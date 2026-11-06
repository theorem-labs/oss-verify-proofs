(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QZDE QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn Q6WR QrPc QYIF QgoP Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q1Ey Qvmy Qawr Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Qvmy.Mq0 Qawr.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Lemma le8_lbw8A : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_C8_of_CB8 : forall segs m a bs, rw_cells segs m a [CB 8 bs] -> rw_cells segs m a [C8 (le_bytes_to_word bs)].
Proof.
intros segs m a bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
split; [split; [cbn; split; exact I |] | exact Hw].
cbn [cells_bytes cbytes app] in *. rewrite le8_lbw8A by exact Hl. exact Hb.
Qed.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetInt64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mq4.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa39f8.

Lemma RTC_GI64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe6a40 (le8 (Z_to_bv 64 0x9cb08)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GI64_STK_A : Z := 96 + PI64_STK_A.

Lemma get_int64_A : jo_get_num_A_stmt HIx 0x9cb08 GI64_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GI64_STK_A, PI64_STK_A in LOS. subst a0 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 96%nat ST.
step. stepz. do 8 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) with (bv_unsigned sp + -96) by (clear - SPA; Z.div_mod_to_equations; lia).
step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
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
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GI64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1') as MU.
change (6434400 - 164) with 6434236 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. stepz. stepz. stepz. step. step.
fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148255159 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }
step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9cbf8)) with (Z_to_bv 64 0x9cbf8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. rewrite ?sxb_zero. step. if_false.
stepz.

lazymatch type of FF1 with rw_cells _ _ _ [?c1; ?c2; ?c3; CB 32 ?jj] =>
apply (rw_cells_split_CB asegs _ Fr [c1; c2; c3] 32 jj [] [8; 8; 16]%nat) in FF1; [| reflexivity]; cbn [mk_CB_cells app] in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
apply rw_cells_C8_of_CB8 in FFe.
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
HEAPAx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md1).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9cd3c) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] mX) as MU.
step. stepz. step. step. stepz. step. if_falsex. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (642428 + 4) with 642432.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 13 step.
evt_done5.
eapply (K _ md5 m5 (bv_unsigned xa1) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FSX | exact FRMX].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (Q1Ey.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
step.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHP mc MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
asan_chk0.
step. rewrite sx32_small by lia. step. step. step.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
step. asan_chkA.
step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
let b1 := eval vm_compute in (match image_bytes asegs 0x10380 8 with Some bs => bs | None => [] end) in
let b2 := eval vm_compute in (match image_bytes asegs 0x10420 8 with Some bs => bs | None => [] end) in
assert (RO1 : ro_cells asegs mc 0x10380 [CB 8 b1]) by (change 8%nat with (length b1); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]);
assert (RO2 : ro_cells asegs mc 0x10420 [CB 8 b2]) by (change 8%nat with (length b2); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]) end end.
step. asan_chkA.
step. step. step. step. step.
if_cases Hc1.
+
step. rewrite ?sxb_zero. step. if_true. step. stepz. step. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+ step. step. step. step.
if_cases Hc2.
*
step. step. step. step. step. step. step.
if_cases Hc3.
--  step. step. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
step. rewrite ?sxb_zero. step. if_false. step. step. stepz. step. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
step. asan_chkA.
step. rewrite sx32_small by lia. step. step.
destruct Hcty as [-> | ->]; if_lit.
+
step. if_lit.
step. asan_chkA. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
step. asan_chkA. step. step.
if_cases Hc7.
* gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 TX) xa1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9cd28) fcx None mc rom))
end end.
{ intros xa1.
step. step. step.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPc ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
evt_done5.
eapply PI64 with (LB := BS ++ LB) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (str := str0) (SA := TX) (R := Fr + 32) (lo := lo);
[ exact HPc | rewrite unsigned_lit by lia; eassumption | exact LO | unfold PI64_STK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity
| reflexivity | reflexivity | exact BY | exact NIN
| exists TB, TBN; split; [apply in_or_app; left; exact INT | lia]
| exact UNS
| exists Fr, 0; split; [exact INF | rewrite fr_size_0; lia]
| exact FFe | exact UNE | clear - HFal; Z.div_mod_to_equations; lia
| cbn [length]; lia
| ].
rewrite ?unsigned_lit by lia.
intros ms3 md3 m3 A3 rv vR eR RS3 VM3 ST3 PD3 HRV RC3 ERR3 HP3. open_ret RS3.

pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
lazymatch type of PD3 with heap_presD _ _ _ ?mb _ =>
assert (HPR3 : heap_pres A4H [(Fr, 32); (sh, 8)] (bv_unsigned sp + -96) mb m3) end.
{ intros a Ha Hc. apply (PD3 a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc |].
right; right. destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr.
+ exists (Fr, fr_size 0 - 8). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; lia].
+ exists (shad A4L Fr, fr_shadow_len 0). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; lia].
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ cbn [hl_client_static A4H] in Hc. unfold a4_client_static in Hc. lia.
+ destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr; lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFa; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSH1; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
change (hl_segs A4H) with asegs in FR, FFa, FSH1.
lazymatch goal with MUc : munch _ m1' ?mc, WMc : wmono asegs m1' ?mc |- _ =>
assert (PDm3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3);
[ eapply heap_presD_trans; [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) |];
eapply heap_presD_weaken; [exact PD3 | lia |];
let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; rewrite app_assoc in Hb; apply in_app_or in Hb; rewrite app_assoc; apply in_or_app;
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]
| clear MUc WMc ] end.
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (XHP3 : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m3 mX -> wmono asegs m3 mX -> mem_inv asegs mX ->
HEAPAx A3 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md3).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP3 LO HT MUX WMX MIX). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6434236, 6434240)] m3) as MU.
unfold A_ERRNO, A_TP in ERR3. change (6434400 - 164) with 6434236 in ERR3.
replace (ret_pc (Z_to_bv 64 642356)) with (Z_to_bv 64 642356) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
step.

destruct HRV as [-> | ->]; if_lit.
+
step. step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
step. asan_chkA.
step. step. step.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_truex. rewrite <- ETX. apply CONT.
+  if_falsex. asan_chkA. step. apply CONT.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetInt64.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QRUw QkMG QG8z Qiiq Ql4f QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeBreakA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_adv_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32) (av : Z),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf ->
0 <= av < 2^64 -> (av = 0 <-> bv_unsigned cb = 0) ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
bv_unsigned cb = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->

(forall m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4',
bv_unsigned cb <> 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' (ts_set_co ts (t_co ts + 1)) b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_LOOP (t_co ts + 1) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) t4' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until av. intros STC INV Hco AVR AVZ Kout Kloop. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK. unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_ADV, APE_OUT, APE_LOOP, shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t. stash PB. stash REST. clear OBJ HPR.
reenterA asegs A4L HIx asegs_wx HP.
step. norm_sx32. step. step. step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (INV' : PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B (ts_set_co ts0 (co + 1)) cb nb pj sv errv);
[ split;
[ unfold PE_CORE_A, ts_set_co; cbn; split; [exact LEN32|]; split; [exact D32|]; split; [lia|]; split; [reflexivity|];
split; [exact TOKc|]; split; [| split; [exact Hpb | split; [| eapply (pe_frameA_blkwrite HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | | exact FR | exact MUc | exact WMc]; apply Forall_cons; [exists tk, 72; cbn [fst snd]; split; [apply in_or_app; left; exact INtk | lia] | apply Forall_nil] ]]];
[ eapply (pbuf_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MUc | exact WMc | exact HW]
| eapply (tstack_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUc | exact WMc | exact HW] ]
| eapply PRW with (ts := ts0) in REST;
[| exact STC | exact MUc | exact WMc | exact MIc | apply pe_wtfA_private; exact HW];
apply (PE_REST_A_set_co HIx GA); [exact REST | cbn [t_co pf_len ts0]; lia] ]
| ];
assert (PBT' : forall b, PBOKat m ts0 b -> PBOKat mc (ts_set_co ts0 (co + 1)) b)
by (intros b PBKb; apply (PBOKat_same mc ts0); [reflexivity | reflexivity |];
eapply (PBOKat_wtqA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PBKb | exact MUc | exact WMc | apply pe_wtfA_wtqA; exact HW])
end end.
clear TOK FR PB TSK MU WM.
destruct (Z.eq_dec av 0) as [Hc0 | Hc1].
- step. if_truex. evt_done5. eapply Kout; [apply AVZ; exact Hc0 | exact INV'].
- step. if_falsex. step. evt_done5. eapply Kloop; [intros E; apply Hc1; apply AVZ; exact E | exact INV' | exact PBT'].
Qed.

Lemma seg_break_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf ->

(forall m' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6',
bv_unsigned cb = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F fc m')) ->

(forall m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4',
bv_unsigned cb <> 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' (ts_set_co ts (t_co ts + 1)) b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_LOOP (t_co ts + 1) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (pf_tk pf + 56)) t4' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV Hco Kout Kloop. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
unfold APE_BREAK, APE_ADV, APE_OUT, APE_LOOP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SLOTS GAP SAVED OBJ HPR LV BUD.
reenterA asegs A4L HIx asegs_wx HP.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step. step. if_falsex.
evt_done5.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
eapply (seg_adv_A (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0);
[exact STC | exact INV0 | exact Hco | lia | tauto | exact Kout | exact Kloop].
Qed.
End PeBreakA.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QrQv.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSEpiG.
Variable HIx : heap_iface_A A4L.

Lemma pe_epilogue_AG :
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (sv : pe_saved) (T : TSet) (lo : Z) (jsl jgap jff jsh : list byte)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
rw_cells asegs m (pf_spf pf) [CB 312 jsl] ->
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) jgap] ->
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) ->
rw_cells asegs m (pa_F pa) [CB 248 jff] ->
rw_cells asegs m (shA (pa_F pa)) [CB 32 jsh] ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) s3 a1 a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 (Z_to_bv 64 (pa_F pa)) s6 s7 (Z_to_bv 64 (pa_F pa)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP GEO SP0 SLOTS GAP SAVED FF FSH ST LO LOS RAE K.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold pe_savedA_cells in SAVED.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & Himg_F & _). rewrite fr_size_2 in Himg_F. cbn [hl_img_lo hl_img_hi A4L A4H hla_base] in Himg_F.
unfold APE_EPI, shA in *. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32); (Ff, Ff + 8)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPA A4L HIx A LBall LM ((Ff, 2) :: FRS) B mc md);
[ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Ff, 2; (split; [exact INF|]);
[ right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; lia
| left; cbn [fst snd]; rewrite ?fr_size_2; lia ]. }
destruct (OBL_FP_PRIVATE HIx _ _ _ _ _ _ _ _ _ HPc INF) as (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr).
rewrite fr_size_2 in FPB. replace (Ff + 256 - 8) with (Ff + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Ff) (k := 2) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPc | exact INF | rewrite fr_size_2; replace (Ff + 256 - 8) with (Ff + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m2 md2 A2 VM2 HP2 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP2. rewrite Z.eqb_refl in HP2.
assert (MUr : munch [(fp, fp + 1)] m1 m2).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m1 m2) by exact Hwv.
assert (MI2 : mem_inv asegs m2).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SAVED; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SLOTS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m1 m2) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; unfold client_addr in FPnc; lia].
change (602972 + 4) with 602976.
clear FF FSH FPC.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. step.
replace (sp0 - 104) with (sp0 + -104) in SAVED by lia.
do 13 step.
step. step.
evt_done5.
assert (ST2 : stk asegs m2 lo sp0).
{ pose proof (stk_release asegs _ _ _ _ ST SLOTS ltac:(lia)) as ST1. rewrite pe_slotsA_size in ST1 || cbn [cells_size csize Nat.add] in ST1.
pose proof (stk_release asegs _ _ _ _ ST1 GAP ltac:(lia)) as STg. cbn [cells_size csize Nat.add] in STg.
rewrite Nat.add_0_r, Z2Nat.id in STg by lia.
replace (spf + Z.of_nat 312 + (sp0 - 104 - (spf + 312))) with (sp0 + -104) in STg by lia.
pose proof (stk_release asegs _ _ _ _ STg SAVED ltac:(lia)) as STs. cbn [cells_size csize Nat.add] in STs.
replace (sp0 + -104 + Z.of_nat 104) with sp0 in STs by lia. exact STs. }
eapply K.
all: lazymatch goal with
| |- model_vm_only _ _ => exact VM2
| |- HEAPA _ _ _ _ _ _ _ _ _ => exact HP2
| |- stk _ _ _ _ => exact ST2
| |- 0 < _ < _ => exact FPR
| |- ~ client_addr _ _ _ _ => exact FPnc
| |- _ \/ _ => exact FPimg
| |- ~ hl_scratch _ _ => exact FPns
| |- forall F' k', _ => intros F' k' Hin'; apply FPfr; right; exact Hin'
| |- munch _ _ _ => eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUr]]; intros z Hz; cbn [outside] in Hz |- *; tauto
| |- wmono _ _ _ => intros z Hz; apply WMr; apply WM; exact Hz
| |- mem_inv _ _ => exact MI2
end.
Qed.

End PeSEpiG.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_ERRST : Z := 0x98060.

Section PeSOfendA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_ofend_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofend ->
t_co ts < pf_len pf ->

(forall m' a0' a1' a2' a3',
bv_unsigned cb = 58 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall a1' a3',
bv_unsigned cb <> 58 ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERRST (t_co ts) gp t0 t1 t2 (Z_to_bv 64 10) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ofend) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Hco Kbreak Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = true).
{ rewrite Hst in Hmode. unfold ST_ofend in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_ofend. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 58) as [C58 | N58].
- step.
if_truex.
step.
asan_chkA.
step.
stepz.
asan_rechkA.
stepz.
step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_ovalue _ _ CObj STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_ovalue; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc _ _ _ _ C58); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step.
if_falsex.
step. step.
asan_rechkA.
step. step.
evt_done5.
subst bse. eapply Kerr; exact N58.
Qed.
End PeSOfendA.
End RC__1.
End Mq3.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QsKa.Mq5 Q1Ey Ql4f.Mq1 QsKa.Mq8 QrQv.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.

Lemma unpoisoned_presx_heap : forall X LST SP m m' s n cA cK,
unpoisoned asegs m A_SB s n -> heap_presx A4H X LST SP m m' ->
In (cA, cK) LST -> cA <= shadow_span_lo A_SB s -> shadow_span_hi A_SB s n <= cA + cK ->
unpoisoned asegs m' A_SB s n.
Proof.
intros X LST SP m m' s n cA cK (Hn & GZ & (v & Hv & Hvr) & WRD) HPR Hin Hlo Hhi.
unfold shadow_span_lo, shadow_span_hi in *.
split; [exact Hn|]. split; [| split].
- intros g Hg. eapply (heap_presx_bytes_at A4H); [exact HPR | exact (GZ g Hg) |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- exists v. split; [| exact Hvr]. eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hv |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- intros w Hw. destruct (WRD w Hw) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hbs |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | rewrite Hlen; cbn; Z.div_mod_to_equations; lia].
Qed.

Lemma unpoisoned_presx_frame : forall X A LB LM FRS B m0 md LBX SP m m' Fs ks b n,
HEAPA A4L HIx A LB LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= b -> b + n <= Fs + fr_size ks - 8 ->
unpoisoned asegs m A_SB b n -> heap_presx A4H X (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
unpoisoned asegs m' A_SB b n.
Proof.
intros X A LB LM FRS B m0 md LBX SP m m' Fs ks b n HP HFs HFa HFk UPS HPR.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
eapply unpoisoned_presx_heap; [exact UPS | exact HPR | apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFs | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow ks) in HFk by lia.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.

Lemma payload_locA_presx : forall X pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m',
HEAPA A4L HIx A LB LM FR B m0 md -> incl FRS FR ->
heap_presx A4H X (LBX ++ LM ++ fr_ivs A4L FR) SP m m' ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) -> (pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros X pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m' HP HinclF HPR [L0 | PL]; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
eapply unpoisoned_presx_frame; [exact HP | exact (HinclF _ HFh) | exact HF1 | exact HF2 | exact UPS | exact HPR].
Qed.

Lemma pe_frameA_presx : forall X pf pa (L : list blk) SP me m cb nb pj sv,
heap_presx A4H X L SP me m -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (pa_F pa, 248) L -> In (shA (pa_F pa), 32) L ->
pe_frameA asegs me pf pa cb nb pj sv -> pe_frameA asegs m pf pa cb nb pj sv.
Proof.
intros X pf pa L SP me m cb nb pj sv HPR HSP GEO InF InS (SL & GP & SV & FF & FSH).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split]]].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact SV | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact FF | right; right]. exists (pa_F pa, 248). split; [exact InF | cbn; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn; lia].
Qed.

Lemma PE_BASE_A_callGx : forall pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m1 md A B LBall errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_presx A4H a4_volatile (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 -> lh_globA m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 LBall2 LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m2 md2 A2 B2 LBall2 errv2.
Proof.
intros pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc STC
(HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) VM12 HPRc LG2 Hincl HP2 ST2 ERR2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_presx a4_volatile pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split]]]].
- eapply payload_presxA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_presx; [exact HPRc | exact LG2 | exact G].
Qed.

Lemma PE_REST_A_callGx : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_presx A4H a4_volatile (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 -> lh_globA m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc STC REST VM12 HPRc LG2 Hincl HP2 LV2 OBJ2 ST2 ERR2 BUD2.
apply PE_REST_A_base in REST as (BASE & _ & _ & _).
apply PE_REST_A_of_base; [| exact LV2 | exact OBJ2 | exact BUD2].
eapply PE_BASE_A_callGx; [exact STC | exact BASE | exact VM12 | exact HPRc | exact LG2 | exact Hincl | exact HP2 | exact ST2 | exact ERR2].
Qed.
End WithIface.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QSHS QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QgoP.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5.

Import QsKa.Mqf.

Import Qvmy Qawr.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Lemma le8_lbw8A : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_C8_of_CB8 : forall segs m a bs, rw_cells segs m a [CB 8 bs] -> rw_cells segs m a [C8 (le_bytes_to_word bs)].
Proof.
intros segs m a bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
split; [split; [cbn; split; exact I |] | exact Hw].
cbn [cells_bytes cbytes app] in *. rewrite le8_lbw8A by exact Hl. exact Hb.
Qed.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetInt64.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mqe.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa6060.

Lemma RTC_GI64PC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe8e40 (le8 (Z_to_bv 64 0x9e4a0)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GI64_STK_A : Z := 96 + PI64_STK_A.

Lemma get_int64_A : jo_get_num_A_stmt HIx 0x9e4a0 GI64_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GI64_STK_A, PI64_STK_A in LOS. subst a0 tp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
unfold A_ERRNO, A_TP in *.
stash ERR.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 96%nat ST.
bstep. bstepz. do 8 bstep.
bstep. bstep.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) with (bv_unsigned sp + -96) by (clear - SPA; Z.div_mod_to_equations; lia).
bstep. bstep. bstep. bstep. bstep. bstep. bstep. bstep.
norm_sx32. bstep. if_false. bstep. bstep.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := BS ++ LB) (LM := LM) (FR := FRS) (B := B);
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
clear SB1 SB2 SB3 UARC.
pose proof (RTC_GI64PC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1') as MU.
change (6444320 - 164) with 6444156 in ERR1.
unfold A_SB in HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
bstep. bstep. bstep. if_truex.
bstepz.
bstep. bstep. bstep. bstep.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
bstep. bstep. bstep. bstepz. bstepz. bstepz. bstep. bstep.
fold sh.
bstepz. bstepz. bstepz. bstepz. bstep. bstepz. bstepz. bstepz. bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (SHE : ro_cells asegs mc 2148256399 [C1 (Z_to_bv 8 0)]) end.
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP1) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X.
eapply bytes_at_transport; [exact X | exact MU |]. cbn [disjoint_from length]. change (Z.of_nat 1) with 1. unfold sh. clear - HFimg HFapp HF0 HFc ACR LO LOS SPR. Z.div_mod_to_equations. lia. }
bstep.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x9e590)) with (Z_to_bv 64 0x9e590) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstepz.

lazymatch type of FF1 with rw_cells _ _ _ [?c1; ?c2; ?c3; CB 32 ?jj] =>
apply (rw_cells_split_CB asegs _ Fr [c1; c2; c3] 32 jj [] [8; 8; 16]%nat) in FF1; [| reflexivity]; cbn [mk_CB_cells app] in FF1 end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
apply rw_cells_C8_of_CB8 in FFe.
assert (XHP : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m1' mX -> wmono asegs m1' mX -> mem_inv asegs mX ->
HEAPAx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md1).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP1 LO HT MUX WMX MIX). }
assert (PD1 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_presD_trans; [| eapply heap_presD_of_pres; [exact HPR1 | lia]].
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) (Fr + 32) HP MU0 WM0); [| lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. exact Hb.
- apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia. }
assert (XPD : forall mb mX, heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mb ->
forall AX mdX, HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mb mdX ->
munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mb mX -> wmono asegs mb mX ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ intros mb mX PDb AX mdX HPb MUX WMX. eapply heap_presD_trans; [exact PDb |].
eapply (fk0_presD HIx); [exact HPb | exact LO | lia | exact MUX | exact WMX]. }

lazymatch type of FR with rw_cells _ _ _ ?frc => lazymatch type of FSH1 with rw_cells _ _ _ ?shc => lazymatch type of FFa with rw_cells _ _ _ ?ffc =>
assert (EPI : forall (mX : word -> option byte) (AX : ASA A4L HIx) (mdX : config) (F1 : bvmap 5 word) (fc1 : bv 32)
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9e6e8) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
clear MU WM MI1 FR FSH1 FFa FFe FFb ST1 ERR1 SHE PCC.
pose proof (wmono_refl asegs mX) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] mX) as MU.
bstep. bstepz. bstep. bstep. bstepz. bstep. if_falsex. bstep. do 8 bstepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ mX mc, WMc : wmono asegs mX mc, MIc : mem_inv asegs mc |- _ =>
pose proof (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HPX LO HT MUc WMc MIc) as HPY;
pose proof (XPD mX mc PDX AX mdX HPX MUc WMc) as PDY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
bstep.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (MUr : munch [(fp, fp + 1)] mq m5) end.
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => assert (WMr : wmono asegs mq m5) by exact Hwv end.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in ERRX; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_TP in FPns; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STX; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (649000 + 4) with 649004.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 13 bstep.
evt_done5.
eapply (K _ md5 m5 (bv_unsigned xa1) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ rewrite Z_to_bv_bv_unsigned. apply ret_statew_intro; [exact FSX | exact FRMX].
+ eapply model_vm_only_trans; [exact VMX | exact VM5].
+ release_frame FRX STX (bv_unsigned sp). exact STX.
+ eapply (heap_pres_of_presD (Fr + 32)).
* eapply heap_presD_weaken; [exact PD5 | lia |]. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
* intros a Hd Hc.
destruct (own_frame_fresh HIx Fr 0 (BS ++ LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; apply in_or_app; right; exact Hb)) as [OFF OFS].
assert (Ho : outside [(Fr + 32, Fr + 40)] a).
{ eapply (QSHS.client_outsideF HIx A1 (BS ++ LB) LM ((Fr, 0) :: FRS) B (LB ++ LM ++ fr_ivs A4L FRS) m1' md1 [(Fr + 32, Fr + 40)] (bv_unsigned sp) HP1); [| lia | | lia | exact Hc].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; apply in_app_or in H; apply in_or_app; destruct H as [H|H]; [left; apply in_or_app; right; exact H | right; exact H] | right; cbn [fr_ivs flat_map app]; right; right; exact H].
- apply Forall_cons; [| apply Forall_nil]. right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia. }
cbn [outside] in Ho. lia.
+ eexists. exact ERRX.
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (jopt_agree asegs A4F BS m m5 s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_presD (Fr + 32)); [exact PD5 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |].
intros a n Hin.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF. rewrite fr_size_0 in DF. lia.
- exact HP5. }
bstep.
destruct s as [shp|].
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1. }
destruct JO as [Hp J].

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m1' mc, WMc : wmono asegs m1' mc, MIc : mem_inv asegs mc |- _ =>
pose proof (XHP mc MUc WMc MIc) as HPc;
assert (AGc : agree_on asegs BS m mc);
[ eapply (agree_of_presD (Fr + 32)); [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb |];
let a := fresh "a" in let n := fresh "n" in let Hin := fresh "Hin" in intros a n Hin;
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF ltac:(apply in_or_app; left; apply in_or_app; left; exact Hin)) as DF; rewrite fr_size_0 in DF; lia
| ] end end.
pose proof (jval_agree asegs A4F shp BS m _ BS p 1 J AGc (incl_refl _)) as Jc.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND0.
assert (ND : List.NoDup (map blk_addr BS)) by exact (nodup_app_l' _ _ (nodup_app_l' _ _ ND0)).
destruct (jval_hdr asegs A4F shp _ BS p 1 Jc ND) as (n & tojs & pb & udel & ud & rest & INp & SZ & N48 & HDR & CLOSE).
assert (INpA : In (p, n) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; exact INpA)) as Hpimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hpimg.
assert (Hp8 : p mod 8 = 0) by (clear - Hpal; Z.div_mod_to_equations; lia).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 0 HPc INpA ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p n 5 HPc INpA ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
if_falsex.
ub_skip.
unfold jhdr_cells in HDR, SZ. cbn [app hl_segs hla_base A4L A4H] in HDR, SZ.
pose proof (jtype_range shp) as JR.
asan_chk0.
bstep. rewrite sx32_small by lia. bstep. bstep. bstep.
destruct shp as [|u| |h|kids|kids]; cbn [jtype] in *; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in *; if_lit.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (b & junk_ & ER & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
bstep. asan_chkA.
bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ => assert (CELLS : exists tojs' udel' ud' bits, rw_cells asegs mc p (jhdr_cells 2 1 tojs' pb_ udel' ud' ++ [C8 bits])) end.
{ destruct u; [destruct Jc as (bits & ud_ & udn & uds & _ & _ & C & _) | destruct Jc as (bits & _ & _ & C)]; do 4 eexists; exact C. }
clear Jc. destruct CELLS as (tojs' & udel' & ud' & bits & CELLS). unfold jhdr_cells in CELLS. cbn [app] in CELLS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ =>
let b1 := eval vm_compute in (match image_bytes asegs 0x10390 8 with Some bs => bs | None => [] end) in
let b2 := eval vm_compute in (match image_bytes asegs 0x10438 8 with Some bs => bs | None => [] end) in
assert (RO1 : ro_cells asegs mc 0x10390 [CB 8 b1]) by (change 8%nat with (length b1); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]);
assert (RO2 : ro_cells asegs mc 0x10438 [CB 8 b2]) by (change 8%nat with (length b2); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]);

let b3 := eval vm_compute in (match image_bytes asegs 0x10478 8 with Some bs => bs | None => [] end) in
assert (RO3 : ro_cells asegs mc 0x10478 [CB 8 b3]) by (change 8%nat with (length b3); apply ro_cells_image; [exact MIc | vm_compute; reflexivity | lia | cbn; lia]) end end.
bstep. asan_chkA.
bstep. bstep. bstep. bstep. bstep.
if_cases Hc1.
+
bstep. rewrite ?sxb_zero. bstep. if_true. bstep. bstepz. bstep. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+ bstep. bstep. bstep. bstep.
if_cases Hc2.
*
bstep. bstep. bstep. bstep. bstep. bstep. bstep.
if_cases Hc3.
--
pose proof (bv_unsigned_in_range 64 bits) as BITR. change (bv_modulus 64) with (2^64) in BITR.
assert (NANOK : forall b : word, bv_ltu (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b) 1))) 1)) (Z_to_bv 64 9218868437227405313) = true ->
fp_is_nan fmt_double (bv_unsigned b) = false).
{ clear. intros b H. pose proof (bv_unsigned_in_range 64 b) as BR. change (bv_modulus 64) with (2^64) in BR.
apply QAzu.Mq1.nan_test_clear; [exact BR|].
rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.bv_ltu_Z in H. apply Z.ltb_lt in H. rewrite (unsigned_lit 9218868437227405313) in H by lia.
rewrite !unsigned_lit_wrap in H. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 in H by lia.
replace ((bv_unsigned b * 2 ^ 1) mod 2 ^ 64 / 2 ^ 1) with (bv_unsigned b mod 2 ^ 63) in H by (clear H; Z.div_mod_to_equations; lia).
rewrite Z.mod_small in H by (clear H; Z.div_mod_to_equations; lia). exact H. }
assert (UBLO : bv_eqb (bword (flt_d (Z_to_bv 64 14114281232179134465) bits)) (Z_to_bv 64 0) = false).
{ unfold flt_d. rewrite (unsigned_lit 14114281232179134465) by lia. change 14114281232179134465 with QAzu.Mq1.B_I64MINU.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_i64_lo (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold flt_d in Hc2. rewrite (unsigned_lit 14114281232179134464) in Hc2 by lia. change 14114281232179134464 with QAzu.Mq1.B_I64MIN in Hc2.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b) in Hc2.
destruct (QAzu.Mq1.flt (bv_unsigned bits) QAzu.Mq1.B_I64MIN); [discriminate | reflexivity]. }
assert (UBHI : bv_eqb (bword (flt_d bits (Z_to_bv 64 4890909195324358656))) (Z_to_bv 64 0) = false).
{ unfold flt_d. rewrite (unsigned_lit 4890909195324358656) by lia. change 4890909195324358656 with QAzu.Mq1.B_I64MAX.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_i64_hi (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold fle_d in Hc1. rewrite (unsigned_lit 4890909195324358656) in Hc1 by lia. change 4890909195324358656 with QAzu.Mq1.B_I64MAX in Hc1.
change (fst (fp_le fmt_double ?a ?b)) with (QAzu.Mq1.fle a b) in Hc1.
destruct (QAzu.Mq1.fle QAzu.Mq1.B_I64MAX (bv_unsigned bits)); [discriminate | reflexivity]. }
bstep. bstep. bstep. bstep. rewrite UBLO; cbv iota.
bstep. bstep. rewrite UBHI; cbv iota.
bstep. bstep. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstepz. bstep. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
bstep. asan_chkA.
bstep. rewrite sx32_small by lia. bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+
bstep. if_lit.
bstep. asan_chkA. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
bstep. asan_chkA. bstep. bstep.
if_cases Hc7.
* gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & Jc). cbn [hl_segs hla_base A4L A4H] in Jc, OPB.
lazymatch type of HPc with HEAPA _ _ _ _ _ _ _ ?mc _ =>
assert (TXT : exists (TX TB TBN len : Z) (str0 rest0 : list byte) (lencell : list cell),
In (TB, TBN) BS /\ TB <= TX /\ TX + Z.of_nat (length str0) + 1 <= TB + TBN /\ ~ In (Z_to_bv 8 0) str0 /\
bytes_at asegs mc TX (str0 ++ [Z_to_bv 8 0]) /\
rw_cells asegs mc (p + 40) (C8 (Z_to_bv 64 len) :: lencell) /\ -2^31 < len < 2^31 /\
((0 <= len /\ TX = p + 48) \/ (len < 0 /\ lencell = [C8 (Z_to_bv 64 TX)])) /\
(exists pn, In (p, pn) BS /\ 56 <= pn)) end.
{ destruct h.
- destruct Jc as (len & pd & pdn & str & junk2 & ER & Hlen & Hstr & Hpdn & C1 & C2).
destruct (first_nul_split2A str junk2) as (str0 & rest0 & E0 & NIN & L0).
exists pd, pd, pdn, len, str0, rest0, [C8 (Z_to_bv 64 pd)].
split; [rewrite EBS, ER; cbn; right; left; reflexivity|]. split; [lia|]. split; [lia|]. split; [exact NIN|].
split. { apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split. { unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1. exact C1. }
split; [lia|]. split; [right; split; [lia | reflexivity]|]. exists 56. split; [rewrite EBS, ER; cbn; left; reflexivity | lia].
- destruct Jc as (len & str & junkS & ER & Hlen & Hstr & C1).
destruct (first_nul_split2A str junkS) as (str0 & rest0 & E0 & NIN & L0).
exists (p + 48), p, (str_objsize len), len, str0, rest0, [CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junkS)].
split; [rewrite EBS, ER; cbn; left; reflexivity|]. split; [lia|]. split; [unfold str_objsize; lia|]. split; [exact NIN|].
unfold jhdr_cells in C1. cbn [app] in C1. apply rw_cells_app with (cs1 := [_;_;_;_;_;_]) in C1 as [_ C1]. cbn [cells_size csize Nat.add] in C1. change (p + Z.of_nat 40) with (p + 40) in C1.
split. { pose proof C1 as C2. apply rw_cells_app with (cs1 := [_]) in C2 as [_ C2]. cbn [cells_size csize Nat.add] in C2.
apply rw_cells_bytes_at in C2. cbn [cells_bytes cbytes app] in C2. rewrite app_nil_r in C2.
change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in C2. replace (p + 40 + 8) with (p + 48) in C2 by lia. eapply bytes_at_cstr_prefix2A; [exact C2 | exact E0]. }
split; [exact C1|]. split; [lia|]. split; [left; split; [lia | reflexivity]|]. exists (str_objsize len). split; [rewrite EBS, ER; cbn; left; reflexivity | unfold str_objsize; lia]. }
clear Jc. destruct TXT as (TX & TB & TBN & len & str0 & rest0 & lencell & INT & TLO & THI & NIN & BY & LENC & Hlen & ALT & (pn & INpn & Hpn)).
assert (INTA : In (TB, TBN) ((BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact INT).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as (_ & _ & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as Htimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HPc INF INTA) as DFT. rewrite fr_size_0 in DFT.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ TB TBN HPc INTA) as APT. cbn [hl_sb A4L] in APT. unfold A_SB in APT.
assert (INpnA : In (p, pn) (BS ++ LB)) by (apply in_or_app; left; exact INpn).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p pn 6 HPc INpnA ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
apply rw_cells_app with (cs1 := [_]) in LENC as [LEN1 LEN2]. cbn [cells_size csize Nat.add] in LEN2. change (p + 40 + Z.of_nat 8) with (p + 40 + 8) in LEN2. replace (p + 40 + 8) with (p + 48) in LEN2 by lia.

lazymatch goal with |- evt _ ?Q (MS ?r ?Fx ?pc ?fcx None ?mc ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify r r';
lazymatch r' with mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
assert (CONT : forall xa1 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 TX) xa1 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9e6d4) fcx None mc rom))
end end.
{ intros xa1.
bstep. bstep. bstep.
pose proof (unpoisoned_of_blk HIx _ _ _ _ _ _ _ TB TBN TX (Z.of_nat (length str0) + 1) HPc ltac:(apply in_or_app; left; exact INT) ltac:(lia) ltac:(lia) ltac:(lia)) as UNS.
lazymatch type of FSH1 with rw_cells _ ?mc _ _ => assert (UNE : unpoisoned asegs mc A_SB (Fr + 32) 8) end.
{ pose proof (rw_cells_bytes_at asegs _ _ _ FSH1) as SHB. cbn [cells_bytes cbytes app] in SHB.
lazymatch type of SHB with bytes_at _ _ _ ?wb => eapply (unpoisoned_gran8 asegs _ A_SB (Fr + 32) wb ltac:(clear - HFal; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(unfold A_SB; lia) eq_refl) end.
- replace (((Fr + 32) / 8 + A_SB) / 8 * 8) with sh by (unfold sh, A_SB; clear - HFal; Z.div_mod_to_equations; lia). exact SHB.
- replace (((Fr + 32) / 8 + A_SB) mod 8) with 4 by (unfold A_SB; clear - HFal; Z.div_mod_to_equations; lia). reflexivity. }
evt_done5.
eapply PI64 with (LB := BS ++ LB) (LM := LM) (FRS := (Fr, 0) :: FRS) (B := B) (str := str0) (SA := TX) (R := Fr + 32) (lo := lo);
[ exact HPc | rewrite unsigned_lit by lia; eassumption | exact LO | unfold PI64_STK_A; rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia
| unfold A_ERRNO, A_TP; eassumption | reflexivity | rewrite unsigned_lit by lia; reflexivity
| reflexivity | reflexivity | exact BY | exact NIN
| exists TB, TBN; split; [apply in_or_app; left; exact INT | lia]
| exact UNS
| exists Fr, 0; split; [exact INF | rewrite fr_size_0; lia]
| exact FFe | exact UNE | clear - HFal; Z.div_mod_to_equations; lia
| cbn [length]; lia
| ].
rewrite ?unsigned_lit by lia.
intros ms3 md3 m3 A3 rv vR eR RS3 VM3 ST3 PD3 HRV RC3 ERR3 HP3. open_ret RS3.

pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
lazymatch type of PD3 with heap_presD _ _ _ ?mb _ =>
assert (HPR3 : heap_pres A4H [(Fr, 32); (sh, 8)] (bv_unsigned sp + -96) mb m3) end.
{ intros a Ha Hc. apply (PD3 a Ha).
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; exact Hc | right; left; exact Hc |].
right; right. destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr.
+ exists (Fr, fr_size 0 - 8). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity | cbn [blk_addr blk_size fst snd]; rewrite fr_size_0; lia].
+ exists (shad A4L Fr, fr_shadow_len 0). split; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; reflexivity | unfold shad; cbn [blk_addr blk_size fst snd hl_sb A4L]; rewrite fr_shadow_len_0; unfold A_SB; fold sh; lia].
- destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ cbn [hl_client_static A4H] in Hc. unfold a4_client_static in Hc. lia.
+ destruct Hb as [<- | [<- | []]]; cbn [blk_addr blk_size fst snd] in Hr; lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FFa; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FSH1; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]].
change (hl_segs A4H) with asegs in FR, FFa, FSH1.
lazymatch goal with MUc : munch _ m1' ?mc, WMc : wmono asegs m1' ?mc |- _ =>
assert (PDm3 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m3);
[ eapply heap_presD_trans; [exact (XPD m1' mc PD1 A1 md1 HP1 MUc WMc) |];
eapply heap_presD_weaken; [exact PD3 | lia |];
let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; rewrite app_assoc in Hb; apply in_app_or in Hb; rewrite app_assoc; apply in_or_app;
destruct Hb as [Hb|Hb]; [left; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb]
| clear MUc WMc ] end.
assert (VM13 : model_vm_only (cfg_model md) (cfg_model md3)) by (eapply model_vm_only_trans; [exact VM1 | exact VM3]).
assert (XHP3 : forall mX, munch [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m3 mX -> wmono asegs m3 mX -> mem_inv asegs mX ->
HEAPAx A3 (BS ++ LB) LM ((Fr, 0) :: FRS) B mX md3).
{ intros mX MUX WMX MIX. exact (fk0_HEAPA HIx _ _ _ _ _ _ _ _ _ _ _ HP3 LO HT MUX WMX MIX). }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (sh, sh + 8); (6444156, 6444160)] m3) as MU.
unfold A_ERRNO, A_TP in ERR3. change (6444320 - 164) with 6444156 in ERR3.
replace (ret_pc (Z_to_bv 64 648928)) with (Z_to_bv 64 648928) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
bstep.

destruct HRV as [-> | ->]; if_lit.
+
bstep. bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
bstep. asan_chkA.
bstep. bstep. bstep.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_truex. rewrite <- ETX. apply CONT.
+  if_falsex. asan_chkA. bstep. apply CONT.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetInt64.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Qhd4 Qwm6.
Import QbFI Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 QrQv.Mq4 Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeBreakA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_break_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf ->

(forall m' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
bv_unsigned cb = 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_OUT gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->

(forall m' gp' t0' a0' a1' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6',
bv_unsigned cb <> 0 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B (ts_set_co ts (t_co ts + 1)) cb nb pj sv errv ->
(forall b, PBOKat m ts b -> PBOKat m' (ts_set_co ts (t_co ts + 1)) b) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_LOOP (t_co ts + 1) gp' t0' a0' a1' (Z_to_bv 64 (pf_tk pf + 36)) a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 2) s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV Hco Kout Kloop. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_OUT, APE_LOOP in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (SBpos : 0 < sb).
{ destruct SBin as [L00 | PL]; [exfalso; cbn [pf_len] in L00; lia|].
destruct PL as [([b0 n0] & Hb0 & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)]; cbn [pf_sb pf_len pa_sp0 blk_addr blk_size fst snd] in *.
- pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b0 n0 HP ltac:(apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb0)) as (_ & _ & Hblo & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (_ & _ & HFlo & _). lia. }
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
assert (INtk' : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LM)) by (apply in_or_app; left; exact INtk).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk') as DFt. rewrite fr_size_2 in DFt.
assert (cs_FF_T : csep Ff 248 tk (Z.of_nat 72)) by (unfold csep; clear - DFt; lia).
assert (cs_T_FF : csep tk 72 Ff (Z.of_nat 248)) by (unfold csep; clear - DFt; lia).
stash DFt. stash Himg_t. stash PB. stash REST. clear GAP SAVED OBJ HPR LV BUD SBin.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_truex.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. if_false.
step. norm_sx32. step. norm_w32. step. if_truex.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. if_false.
stepz.
step. step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
replace (sb + co + 1) with (sb + (co + 1)) by lia.
unstash PB. unstash REST.
assert (HW : Forall (pe_wtfA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl)) [(tk, tk + 72)]) by (apply Forall_cons; [left; cbn; lia | apply Forall_nil]).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
assert (INV' : PE_INV_A HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo mc md A B (ts_set_co ts0 (co + 1)) cb nb pj sv errv);
[ split;
[ unfold PE_CORE_A, ts_set_co; cbn; split; [exact LEN32|]; split; [exact D32|]; split; [lia|]; split; [reflexivity|];
split; [exact TOKc|]; split; [| split; [exact Hpb | split; [| eapply (pe_frameA_blkwrite HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | | exact FR0 | exact MUc | exact WMc]; apply Forall_cons; [exists tk, 72; cbn [fst snd]; split; [apply in_or_app; left; exact INtk | lia] | apply Forall_nil] ]]];
[ eapply (pbuf_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MUc | exact WMc | exact HW]
| eapply (tstack_wtfA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MUc | exact WMc | exact HW] ]
| eapply PRW with (ts := ts0) in REST;
[| exact STC | exact MUc | exact WMc | exact MIc | apply pe_wtfA_private; exact HW];
apply (PE_REST_A_set_co HIx GA); [exact REST | cbn [t_co pf_len ts0]; lia] ]
| ];
assert (PBT' : forall b, PBOKat m ts0 b -> PBOKat mc (ts_set_co ts0 (co + 1)) b)
by (intros b PBKb; apply (PBOKat_same mc ts0); [reflexivity | reflexivity |];
eapply (PBOKat_wtqA HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PBKb | exact MUc | exact WMc | apply pe_wtfA_wtqA; exact HW])
end end.
clear TOK FR0 PB TSK MU WM.
destruct (Z.eq_dec (bv_unsigned cb) 0) as [Hc0 | Hc1].
- step. if_truex. step. evt_done5. eapply Kout; [exact Hc0 | exact INV'].
- step. if_falsex. step. evt_done5. eapply Kloop; [exact Hc1 | exact INV' | exact PBT'].
Qed.
End PeBreakA.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 QrQv.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSEpiGB.
Variable HIx : heap_iface_A A4L.

Lemma pe_epilogue_AG :
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (sv : pe_saved) (T : TSet) (lo : Z) (jsl jgap jff jsh : list byte)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
rw_cells asegs m (pf_spf pf) [CB 312 jsl] ->
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) jgap] ->
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) ->
rw_cells asegs m (pa_F pa) [CB 248 jff] ->
rw_cells asegs m (shA (pa_F pa)) [CB 32 jsh] ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) a0 (Z_to_bv 64 fp) a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI1) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP GEO SP0 SLOTS GAP SAVED FF FSH ST LO LOS RAE K.
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
unfold pe_savedA_cells in SAVED.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as DSF. rewrite fr_size_2 in DSF. cbn [hl_sb A4L] in DSF.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & Himg_F & _). rewrite fr_size_2 in Himg_F. cbn [hl_img_lo hl_img_hi A4L A4H hla_base] in Himg_F.
unfold APE_EPI1, shA in *. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Ff / 8 + 2147450880, Ff / 8 + 2147450880 + 32); (Ff, Ff + 8)] m) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. stepz.
step. step. stepz.
step. if_falsex.
step.
do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc |- _ =>
assert (HPc : HEAPA A4L HIx A LBall LM ((Ff, 2) :: FRS) B mc md);
[ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WMc | exact MIc];
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MUc)
| ] end end.
{ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists Ff, 2; (split; [exact INF|]);
[ right; unfold shad; cbn [fst snd hl_sb A4L]; rewrite ?fr_shadow_len_2; unfold A_SB; lia
| left; cbn [fst snd]; rewrite ?fr_size_2; lia ]. }
destruct (OBL_FP_PRIVATE HIx _ _ _ _ _ _ _ _ _ HPc INF) as (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr).
rewrite fr_size_2 in FPB. replace (Ff + 256 - 8) with (Ff + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Ff) (k := 2) (fp := fp) (rX := Z_to_bv 5 11);
[exact HPc | exact INF | rewrite fr_size_2; replace (Ff + 256 - 8) with (Ff + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m2 md2 A2 VM2 HP2 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP2. rewrite Z.eqb_refl in HP2.
assert (MUr : munch [(fp, fp + 1)] m1 m2).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m1 m2) by exact Hwv.
assert (MI2 : mem_inv asegs m2).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SAVED; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in SLOTS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m1 m2) in GAP; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; unfold client_addr in FPnc; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m1 m2) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; unfold client_addr in FPnc; lia].
change (605392 + 4) with 605396.
clear FF FSH FPC.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.
replace (sp0 - 104) with (sp0 + -104) in SAVED by lia.
do 13 step.
step. step.
evt_done5.
assert (ST2 : stk asegs m2 lo sp0).
{ pose proof (stk_release asegs _ _ _ _ ST SLOTS ltac:(lia)) as ST1. rewrite pe_slotsA_size in ST1 || cbn [cells_size csize Nat.add] in ST1.
pose proof (stk_release asegs _ _ _ _ ST1 GAP ltac:(lia)) as STg. cbn [cells_size csize Nat.add] in STg.
rewrite Nat.add_0_r, Z2Nat.id in STg by lia.
replace (spf + Z.of_nat 312 + (sp0 - 104 - (spf + 312))) with (sp0 + -104) in STg by lia.
pose proof (stk_release asegs _ _ _ _ STg SAVED ltac:(lia)) as STs. cbn [cells_size csize Nat.add] in STs.
replace (sp0 + -104 + Z.of_nat 104) with sp0 in STs by lia. exact STs. }
eapply K.
all: lazymatch goal with
| |- model_vm_only _ _ => exact VM2
| |- HEAPA _ _ _ _ _ _ _ _ _ => exact HP2
| |- stk _ _ _ _ => exact ST2
| |- 0 < _ < _ => exact FPR
| |- ~ client_addr _ _ _ _ => exact FPnc
| |- _ \/ _ => exact FPimg
| |- ~ hl_scratch _ _ => exact FPns
| |- forall F' k', _ => intros F' k' Hin'; apply FPfr; right; exact Hin'
| |- munch _ _ _ => eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUr]]; intros z Hz; cbn [outside] in Hz |- *; tauto
| |- wmono _ _ _ => intros z Hz; apply WMr; apply WM; exact Hz
| |- mem_inv _ _ => exact MI2
end.
Qed.

End PeSEpiGB.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z Qdyh.Mq3.
Import Qhd4 Qwm6.
Import QbFI Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4 Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOfendA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Let PRW := PE_REST_A_private_write HIx GA GA_outside.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Lemma seg_ofend_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ofend ->
t_co ts < pf_len pf ->

(forall m' a1' a4' a5',
bv_unsigned cb = 58 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a1' (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a4' a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall a5',
bv_unsigned cb <> 58 ->
AJ5 A4L HIx A T md
(pe_msO asegs pf pa APE_ERR2 gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 10) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ofend) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INV PBK Hl Hst Hco Kbreak Kerr. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold APE_BREAK, APE_EATBRK, APE_ERR2, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = true).
{ rewrite Hst in Hmode. unfold ST_ofend in Hmode. clear - Hmode SS26.
assert (R : 0 <= tl_ss l <= 26) by lia. enum_z R (tl_ss l); vm_compute in Hmode; split; congruence. }
destruct MODE0 as [-> ->].
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_ofend. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step. step.
change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)).
step.
destruct (Z.eq_dec (bv_unsigned cb) 58) as [C58 | N58].
- step. if_truex.
step.
asan_chkB.
step. step.
stepz.
step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
stepz.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5; subst bse;
destruct (PE_INV_A_lvl_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m mc md A B ts0
cb nb pj sv errv l ST_eatws ST_ovalue _ _ CObj STC INV0 Hl MUc WMc MIc TOKc Lc Hmode ltac:(vm_compute; reflexivity) ltac:(unfold ST_eatws; lia) ltac:(unfold ST_ovalue; lia)
(or_introl eq_refl) ltac:(rewrite Hst; vm_compute; reflexivity)) as [INV3 PBK3];
eapply (Kbreak mc _ _ _ C58); [exact INV3 | exact (PBK3 kP PBK)]
end end.
- step. if_falsex.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step.
evt_done5.
subst bse. eapply Kerr; exact N58.
Qed.
End PeSOfendA.
End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QsKa.Mqe QSHS Ql4f.Mq4 QsKa.Mqh QrQv.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.

Lemma unpoisoned_presx_heap : forall X LST SP m m' s n cA cK,
unpoisoned asegs m A_SB s n -> heap_presx A4H X LST SP m m' ->
In (cA, cK) LST -> cA <= shadow_span_lo A_SB s -> shadow_span_hi A_SB s n <= cA + cK ->
unpoisoned asegs m' A_SB s n.
Proof.
intros X LST SP m m' s n cA cK (Hn & GZ & (v & Hv & Hvr) & WRD) HPR Hin Hlo Hhi.
unfold shadow_span_lo, shadow_span_hi in *.
split; [exact Hn|]. split; [| split].
- intros g Hg. eapply (heap_presx_bytes_at A4H); [exact HPR | exact (GZ g Hg) |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- exists v. split; [| exact Hvr]. eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hv |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- intros w Hw. destruct (WRD w Hw) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
eapply (heap_presx_bytes_at A4H); [exact HPR | exact Hbs |].
eapply client_rangex_block; [exact Hin | Z.div_mod_to_equations; lia | rewrite Hlen; cbn; Z.div_mod_to_equations; lia].
Qed.

Lemma unpoisoned_presx_frame : forall X A LB LM FRS B m0 md LBX SP m m' Fs ks b n,
HEAPA A4L HIx A LB LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= b -> b + n <= Fs + fr_size ks - 8 ->
unpoisoned asegs m A_SB b n -> heap_presx A4H X (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
unpoisoned asegs m' A_SB b n.
Proof.
intros X A LB LM FRS B m0 md LBX SP m m' Fs ks b n HP HFs HFa HFk UPS HPR.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
eapply unpoisoned_presx_heap; [exact UPS | exact HPR | apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFs | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow ks) in HFk by lia.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.

Lemma payload_locA_presx : forall X pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m',
HEAPA A4L HIx A LB LM FR B m0 md -> incl FRS FR ->
heap_presx A4H X (LBX ++ LM ++ fr_ivs A4L FR) SP m m' ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) -> (pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros X pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m' HP HinclF HPR [L0 | PL]; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
eapply unpoisoned_presx_frame; [exact HP | exact (HinclF _ HFh) | exact HF1 | exact HF2 | exact UPS | exact HPR].
Qed.

Lemma pe_frameA_presx : forall X pf pa (L : list blk) SP me m cb nb pj sv,
heap_presx A4H X L SP me m -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (pa_F pa, 248) L -> In (shA (pa_F pa), 32) L ->
pe_frameA asegs me pf pa cb nb pj sv -> pe_frameA asegs m pf pa cb nb pj sv.
Proof.
intros X pf pa L SP me m cb nb pj sv HPR HSP GEO InF InS (SL & GP & SV & FF & FSH).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split]]].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact SV | left; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact FF | right; right]. exists (pa_F pa, 248). split; [exact InF | cbn; lia].
- eapply (heap_presx_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn; lia].
Qed.

Lemma PE_BASE_A_callGx : forall pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m1 md A B LBall errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_presx A4H a4_volatile (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 -> lh_globA m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 LBall2 LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BASE_A HIx GA pf pa LB0 LM FRS payload me lo m2 md2 A2 B2 LBall2 errv2.
Proof.
intros pf pa LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 LBall LBall2 errv errv2 LBc STC
(HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) VM12 HPRc LG2 Hincl HP2 ST2 ERR2.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (Gspf & Gsp0 & Gle & _).
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
assert (SBin2 := payload_locA_presx a4_volatile pf pa LB0 FRS _ _ _ _ _ _ _ LBc _ _ _ HP (incl_tl _ (incl_refl _)) HPRc SBin).
assert (FRI : incl (fr_ivs A4L FRS) (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS))).
{ intros b Hb. apply in_or_app; right. apply in_or_app; right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
split; [| split; [exact PLEN | split; [exact SBin2 | split; [| split]]]].
- eapply payload_presxA; [exact HPRc | intros x Hx; apply in_or_app; left; apply Hincl; exact Hx | exact FRI | | exact STR | exact PLEN | exact SBin]. lia.
- eapply heap_presx_trans; [exact HPR|]. eapply heap_presx_weaken; [exact HPRc | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply Hincl; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb.
- eapply model_vm_only_trans; [exact MDV | exact VM12].
- eapply GA_presx; [exact HPRc | exact LG2 | exact G].
Qed.

Lemma PE_REST_A_callGx : forall pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc,
PE_STATIC_A HIx pf pa lo ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m1 md A B ts errv ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_presx A4H a4_volatile (LBc ++ LM ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 -> lh_globA m2 ->
incl LB0 LBc ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts2) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
(forall i l, nth_error (t_levels ts2) i = Some l -> lvl_cur asegs A4F m2 (t_depth ts2) i l) ->
(if zin (cur_st ts2) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts2) m2 (t_objbs ts2) (t_obj ts2) else t_objbs ts2 = []) ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
PE_BUD pf pa ts2 B2 ->
PE_REST_A HIx GA pf pa q LB0 LM FRS payload me lo m2 md2 A2 B2 ts2 errv2.
Proof.
intros pf pa q LB0 LM FRS payload me lo m1 m2 md md2 A A2 B B2 ts ts2 errv errv2 LBc STC REST VM12 HPRc LG2 Hincl HP2 LV2 OBJ2 ST2 ERR2 BUD2.
apply PE_REST_A_base in REST as (BASE & _ & _ & _).
apply PE_REST_A_of_base; [| exact LV2 | exact OBJ2 | exact BUD2].
eapply PE_BASE_A_callGx; [exact STC | exact BASE | exact VM12 | exact HPRc | exact LG2 | exact Hincl | exact HP2 | exact ST2 | exact ERR2].
Qed.
End WithIface.
End RC__1.
End Mq9.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Notation mem := (word -> option byte) (only parsing).

Definition in_ivs (W : list (Z * Z)) (a : Z) : Prop := exists iv, In iv W /\ fst iv <= a < snd iv.

Definition doranges (Lg : mled) : list (Z * Z) :=
map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas Lg)
++ match ld_brkreg Lg with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.
Definition mng_dyn (Lg : mled) (a : Z) : Prop :=
(exists b l, In (b, l) (ld_groups Lg) /\ b <= a < b + l) \/ (exists r, In r (doranges Lg) /\ fst r <= a < fst r + snd r).

Record mng_sig := MSIG {
mg_heap : PState -> list block -> mem -> Prop;
mg_auxv : mem -> Z -> Prop;
mg_tp : Z;
mg_malloc : Z; mg_free : Z;
mg_stack : Z;
mg_img_lo : Z; mg_data_lo : Z; mg_img_hi : Z;
mg_ctx : Z * Z;
mg_rstat : list (Z * Z);
mg_resv : list (Z * Z);
mg_rtc : list (Z * list byte)
}.

Section WithSig.
Variable segs : list Segment.
Variable S : mng_sig.

Definition mg_wstat : list (Z * Z) := [mg_ctx S; (mg_tp S + -164, mg_tp S + -164 + 4)].

Definition mclient (LB : list block) (SP a : Z) : Prop :=
SP <= a \/ (mg_data_lo S <= a < mg_img_hi S /\ ~ in_ivs mg_wstat a) \/ in_block LB a.
Definition mpres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> mclient LB SP a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).
Definition mrange (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= mg_img_lo S \/ mg_img_hi S <= A).

Definition mmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(LB : list block) (n lo B : Z) (m : mem) (r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv']
/\ mg_auxv S m' B
/\ mpres LB (bv_unsigned sp) m m'
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ mg_heap S s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ mrange A n /\ mg_heap S s' ((p, A, n) :: LB) m' /\ rw_cells segs m' A [CB (Z.to_nat n) junk]
end.

Definition mmalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (n lo B : Z) (errv : word),
mg_heap S s LB m ->
mg_auxv S m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - mg_stack S ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 (mg_tp S) ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM segs (raw_malloc n) s
(mmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (mg_malloc S)) fc None m (seg_rom segs)).

Definition mfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv]
/\ mg_auxv S m' B
/\ mpres (lb_remove p LB) (bv_unsigned sp) m m'
/\ mg_heap S s' (lb_remove p LB) m'.

Definition mfree_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
mg_heap S s LB m -> In (p, A, n) LB ->
mg_auxv S m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - mg_stack S ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 (mg_tp S) ->
a0 = Z_to_bv 64 A ->
implM segs (raw_free p) s
(mfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (mg_free S)) fc None m (seg_rom segs)).

Record mng_laws : Prop := MLAWS {
ml_malloc : mmalloc_stmt;
ml_free : mfree_stmt;

ml_hinv : forall s LB m, mg_heap S s LB m ->
exists st LBa, Permutation LBa LB /\ strip st = ps_m s /\ HINV_from (mg_resv S) rc_secret st (ps_brk s) LBa;

ml_agree : forall s Lg LB m m', mg_heap S s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs (mg_rstat S) a \/ mng_dyn Lg a -> m' (wa a) = m (wa a)) -> mg_heap S s LB m';

ml_agree_blk : forall s Lg LB m m', mg_heap S s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs (mg_rstat S) a \/ mng_dyn Lg a -> ~ in_block LB a -> m' (wa a) = m (wa a)) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview segs m (wa a) <> None -> wview segs m' (wa a) <> None) ->
mg_heap S s LB m';

ml_agree_rt : forall s Lg LB m m', mg_heap S s LB m -> Q9kF.HSIM s Lg LB ->
(forall b l, In (b, l) (ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> in_ivs (mg_rstat S) a \/ mng_dyn Lg a -> ~ in_block LB a ->
~ (exists c, In c (mg_rtc S) /\ fst c <= a < fst c + Z.of_nat (length (snd c))) -> m' (wa a) = m (wa a)) ->
Forall (fun c => bytes_at segs m' (fst c) (snd c) /\ wr_at segs m' (fst c) (Z.of_nat (length (snd c)))) (mg_rtc S) ->
(forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> wview segs m (wa a) <> None -> wview segs m' (wa a) <> None) ->
mg_heap S s LB m';

ml_nodup : forall s LB m, mg_heap S s LB m -> List.NoDup (map blk_id LB);
ml_disjoint : forall s LB m b1 b2, mg_heap S s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1;

ml_ctx_wr : forall s LB m a, mg_heap S s LB m -> fst (mg_ctx S) <= a < snd (mg_ctx S) -> wview segs m (wa a) <> None;

ml_auxv_agree : forall m m' B, mg_auxv S m B ->
(forall a, 0 <= a < 2^64 -> B <= a \/ in_ivs (mg_rstat S) a -> m' (wa a) = m (wa a)) -> mg_auxv S m' B;
ml_auxv_floor : forall m B, mg_auxv S m B -> alloc_ceiling <= B;

ml_auxv_mem : forall m m' B, mg_auxv S m B -> mg_auxv S m' B;

ml_hull : 0x10000 <= mg_img_lo S /\ mg_img_lo S <= mg_data_lo S /\ mg_data_lo S <= mg_img_hi S;
ml_stat_in : Forall (fun iv => mg_data_lo S <= fst iv /\ snd iv <= mg_img_hi S) (mg_rstat S ++ mg_wstat);
ml_stack : 0 <= mg_stack S;

ml_slack : forall s LB m b, mg_heap S s LB m -> In b LB ->
exists junk, bytes_at segs m (blk_addr b + blk_size b) junk /\ Z.of_nat (length junk) = (16 - blk_size b mod 16) mod 16
}.

End WithSig.
End RC__1.
