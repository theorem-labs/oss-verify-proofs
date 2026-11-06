(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn Q6WR QrPc QYIF QgoP Q7UD QXUB Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Q1Ey Qvmy Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn.
Import Q6WR Q6WR.Mq0 QrPc.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Qvmy.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma heap_pres_of_presD : forall D L SP m m',
heap_presD D L SP m m' -> (forall a, D <= a < D + 8 -> ~ client_addr A4H L SP a) -> heap_pres A4H L SP m m'.
Proof. intros D L SP m m' H N a Ha Hc. apply (H a Ha Hc). intros Hd. exact (N a Hd Hc). Qed.

Lemma heap_presD_weaken : forall D L L' SP SP' m m',
heap_presD D L' SP' m m' -> SP' <= SP -> (forall b, In b L -> In b L') -> heap_presD D L SP m m'.
Proof.
intros D L L' SP SP' m m' H HS HL a Ha Hc HD. apply (H a Ha); [| exact HD].
destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b; split; [apply HL; exact Hb | exact Hr]].
Qed.

Lemma agree_of_presD : forall D L SP BS m m',
heap_presD D L SP m m' -> incl BS L -> (forall a n, In (a, n) BS -> D + 8 <= a \/ a + n <= D) -> agree_on asegs BS m m'.
Proof.
intros D L SP BS m m' H Hi Hd a Ha (b & Hb & Hr). apply (H a Ha).
- right; right. exists b. split; [apply Hi; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr. destruct (Hd ba bn Hb); lia.
Qed.

Section FakeK0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma fk0_HEAPA : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (6434236, 6434240)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBall LM ((Fr, 0) :: FRS) B mX md.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk0_presD : forall A LBall LM FRS B m md Fr lo SP D mX,
HEAPAx A LBall LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (6434236, 6434240)] m mX ->
wmono asegs m mX -> heap_presD D (LBall ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBall LM FRS B m md Fr lo SP D mX HP LO HSP MU WM.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 0 LBall LBall LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
assert (SUB1 : forall b, In b (LBall ++ LM ++ fr_ivs A4L FRS) -> In b (LBall ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ SP D HP MU WM SUB1 HSP).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.
End FakeK0.

Section FakeK0b.
Variable HIx : heap_iface_A A4L.

End FakeK0b.

Lemma first_nul_split2A : forall (pre post : list byte),
exists str rest, pre ++ Z_to_bv 8 0 :: post = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ Z_to_bv 8 0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ Z_to_bv 8 0 :: post) = Z_to_bv 8 0 :: (pre ++ Z_to_bv 8 0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ Z_to_bv 8 0 :: post) = b :: (str ++ Z_to_bv 8 0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.
Lemma bytes_at_cstr_prefix2A : forall segs m A (str str0 rest0 tail : list byte),
bytes_at segs m A (str ++ [Z_to_bv 8 0] ++ tail) -> str ++ Z_to_bv 8 0 :: tail = str0 ++ Z_to_bv 8 0 :: rest0 ->
bytes_at segs m A (str0 ++ [Z_to_bv 8 0]).
Proof.
intros segs m A str str0 rest0 tail B E.
change (str ++ [Z_to_bv 8 0] ++ tail) with (str ++ ([Z_to_bv 8 0] ++ tail)) in B. cbn [app] in B. rewrite E in B.
replace (str0 ++ Z_to_bv 8 0 :: rest0) with ((str0 ++ [Z_to_bv 8 0]) ++ rest0) in B by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in B as [B _]. exact B.
Qed.

Definition gi_c1A : list byte := Eval vm_compute in match image_bytes asegs 0x10450 8 with Some bs => bs | None => [] end.
Definition gi_c2A : list byte := Eval vm_compute in match image_bytes asegs 0x103d8 8 with Some bs => bs | None => [] end.
Lemma gi_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x10450 [CB 8 gi_c1A] /\ ro_cells asegs m 0x103d8 [CB 8 gi_c2A].
Proof.
intros m MI. split.
- change 8%nat with (length gi_c1A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
- change 8%nat with (length gi_c2A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetInt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mq4.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa39f8.

Lemma RTC_GIPC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe6a38 (le8 (Z_to_bv 64 0x9c460)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GI_STK_A : Z := 96 + PI64_STK_A.

Lemma get_int_A : jo_get_num_A_stmt HIx 0x9c460 GI_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GI_STK_A, PI64_STK_A in LOS. subst a0 tp.
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
step. stepz. do 9 step.
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
pose proof (RTC_GIPC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
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
stepz.
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
replace (ret_pc (Z_to_bv 64 0x9c558)) with (Z_to_bv 64 0x9c558) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6434400 - 164) with 6434236.
step. step. step. rewrite ?sxb_zero. step. if_false.
stepz.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
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
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6434236 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 xs7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9c724) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
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
change (640868 + 4) with 640872.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 14 step.
evt_done5.
eapply (K _ md5 m5 (bv_swrap 32 (bv_unsigned xa1 + 0)) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ apply ret_statew_intro; [exact FSX | exact FRMX].
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
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. step. step.
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
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ => destruct (gi_roA mc MIc) as [RO1 RO2] end end.
step. asan_chkA.
step. step. step. step. step.
if_cases Hc1.
+
step. step. step. step.
if_cases Hc2.
*
step. step. step. step. step. step. step.
if_cases Hc3.
--  step. step. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
step. rewrite ?sxb_zero. step. if_false. step. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
step. rewrite ?sxb_zero. step. if_true. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
step. rewrite ?sxb_zero. step. if_true. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
step. step. if_lit. step. step. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
step. asan_chkA.
step. asan_chkA.
step. rewrite sx32_small by lia. step. step.
destruct Hcty as [-> | ->]; if_lit.
+
step. step. step.
if_cases Hc5.
*
step. step. step.
if_cases Hc6.
-- gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-- step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
step. step. step.
if_cases Hc7.
* step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* step. step. step. step.
if_cases Hc8.
-- gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-- step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
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
assert (CONT : forall xa2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 TX) xa2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x10 x24 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9c6b8) fcx None mc rom))
end end.
{ intros xa2.
step. step. step. step.

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
replace (ret_pc (Z_to_bv 64 640712)) with (Z_to_bv 64 640712) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
step.

assert (SHE3 : ro_cells asegs m3 2148255159 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6434236 / 8) HP3) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6434236 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6434236 / 8 + 2147450880) with 2148255159 in X. exact X. }
destruct HRV as [-> | ->]; if_lit.
+
step. step.
step. step. step.
if_cases Hc5.
* step. step. step.
if_cases Hc6.
-- gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
-- step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
* step. rewrite ?sxb_zero. step. if_false. step. stepz. step. step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
step. step.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
step. asan_chkA.
step. step. step.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_falsex. step. step. rewrite <- ETX. apply CONT.
+  if_truex. asan_chkA. step. step. apply CONT.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  step. step. if_lit. step. step. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetInt.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvmy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma heap_pres_of_presD : forall D L SP m m',
heap_presD D L SP m m' -> (forall a, D <= a < D + 8 -> ~ client_addr A4H L SP a) -> heap_pres A4H L SP m m'.
Proof. intros D L SP m m' H N a Ha Hc. apply (H a Ha Hc). intros Hd. exact (N a Hd Hc). Qed.

Lemma heap_presD_weaken : forall D L L' SP SP' m m',
heap_presD D L' SP' m m' -> SP' <= SP -> (forall b, In b L -> In b L') -> heap_presD D L SP m m'.
Proof.
intros D L L' SP SP' m m' H HS HL a Ha Hc HD. apply (H a Ha); [| exact HD].
destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [left; lia | right; left; exact Hc | right; right; exists b; split; [apply HL; exact Hb | exact Hr]].
Qed.

Lemma agree_of_presD : forall D L SP BS m m',
heap_presD D L SP m m' -> incl BS L -> (forall a n, In (a, n) BS -> D + 8 <= a \/ a + n <= D) -> agree_on asegs BS m m'.
Proof.
intros D L SP BS m m' H Hi Hd a Ha (b & Hb & Hr). apply (H a Ha).
- right; right. exists b. split; [apply Hi; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr. destruct (Hd ba bn Hb); lia.
Qed.

Section FakeK0.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma fk0_HEAPA : forall A LBall LM FRS B m md Fr lo SP mX,
HEAPAx A LBall LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> SP <= hiA_top A4L HIx ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (6444156, 6444160)] m mX ->
wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LBall LM ((Fr, 0) :: FRS) B mX md.
Proof.
intros A LBall LM FRS B m md Fr lo SP mX HP LO HT MU WM MI.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.

Lemma fk0_presD : forall A LBall LM FRS B m md Fr lo SP D mX,
HEAPAx A LBall LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> alloc_ceiling <= SP ->
munch [(lo, SP); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8); (6444156, 6444160)] m mX ->
wmono asegs m mX -> heap_presD D (LBall ++ LM ++ fr_ivs A4L FRS) SP m mX.
Proof.
intros A LBall LM FRS B m md Fr lo SP D mX HP LO HSP MU WM.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
destruct (own_frame_fresh HIx Fr 0 LBall LBall LM FRS B A m md HP (incl_refl _)) as [OFF OFS].
assert (SUB1 : forall b, In b (LBall ++ LM ++ fr_ivs A4L FRS) -> In b (LBall ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
eapply (presD_private HIx _ _ _ _ _ _ _ _ _ _ SP D HP MU WM SUB1 HSP).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
- left. cbn [fst snd]. lia.
- right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right; left. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
- right; right; left. intros x Hx. cbn [fst snd] in Hx. cbn [hl_scratch A4L A4H hla_base]. unfold A_TP. lia.
Qed.
End FakeK0.

Section FakeK0b.
Variable HIx : heap_iface_A A4L.

End FakeK0b.

Lemma first_nul_split2A : forall (pre post : list byte),
exists str rest, pre ++ Z_to_bv 8 0 :: post = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ Z_to_bv 8 0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ Z_to_bv 8 0 :: post) = Z_to_bv 8 0 :: (pre ++ Z_to_bv 8 0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ Z_to_bv 8 0 :: post) = b :: (str ++ Z_to_bv 8 0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.
Lemma bytes_at_cstr_prefix2A : forall segs m A (str str0 rest0 tail : list byte),
bytes_at segs m A (str ++ [Z_to_bv 8 0] ++ tail) -> str ++ Z_to_bv 8 0 :: tail = str0 ++ Z_to_bv 8 0 :: rest0 ->
bytes_at segs m A (str0 ++ [Z_to_bv 8 0]).
Proof.
intros segs m A str str0 rest0 tail B E.
change (str ++ [Z_to_bv 8 0] ++ tail) with (str ++ ([Z_to_bv 8 0] ++ tail)) in B. cbn [app] in B. rewrite E in B.
replace (str0 ++ Z_to_bv 8 0 :: rest0) with ((str0 ++ [Z_to_bv 8 0]) ++ rest0) in B by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in B as [B _]. exact B.
Qed.

Definition gi_c1A : list byte := Eval vm_compute in match image_bytes asegs 0x10468 8 with Some bs => bs | None => [] end.
Definition gi_c2A : list byte := Eval vm_compute in match image_bytes asegs 0x103e8 8 with Some bs => bs | None => [] end.

Definition gi_c3A : list byte := Eval vm_compute in match image_bytes asegs 0x103f0 8 with Some bs => bs | None => [] end.
Definition gi_c4A : list byte := Eval vm_compute in match image_bytes asegs 0x10368 8 with Some bs => bs | None => [] end.
Lemma gi_roA : forall m, mem_inv asegs m -> ro_cells asegs m 0x10468 [CB 8 gi_c1A] /\ ro_cells asegs m 0x103e8 [CB 8 gi_c2A] /\
ro_cells asegs m 0x103f0 [CB 8 gi_c3A] /\ ro_cells asegs m 0x10368 [CB 8 gi_c4A].
Proof.
intros m MI. split; [| split; [| split]].
- change 8%nat with (length gi_c1A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
- change 8%nat with (length gi_c2A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
- change 8%nat with (length gi_c3A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
- change 8%nat with (length gi_c4A). apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia].
Qed.
Ltac gi_fs_tail := let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn [FSAVED In] in Hk; repeat (destruct Hk as [<- | Hk]); [..| destruct Hk]; rewrite ?freg_get_other by (vm_compute; reflexivity); reflexivity.

Ltac gi_exit EPI XHP XPD PD1 HP1 A1 md1 mb VM1 :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (EPI mc A1 md1);
[ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
| apply XHP; assumption | exact VM1 | eapply (XPD mb mc PD1 A1 md1 HP1); assumption
| first [apply fsaved_refl | gi_fs_tail] | first [intros Hf; exact Hf | intros _; assumption] ] end.
Section AJoGetInt.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis ERRNOL : QlKV.Mqe.errno_location_A_stmt.
Hypothesis PI64 : parse_i64_A_stmt HIx 0xa6060.

Lemma RTC_GIPC : forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m 0xe8e38 (le8 (Z_to_bv 64 0x9dd50)).
Proof.
intros A LB LM FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition GI_STK_A : Z := 96 + PI64_STK_A.

Lemma get_int_A : jo_get_num_A_stmt HIx 0x9dd50 GI_STK_A.
Proof.
unfold jo_get_num_A_stmt. intros until errv. intros (HP & ST & LO & LOS & SPA16 & HT & ERR & TP & RA) JO FRN SPA FRM A0 K.
unfold GI_STK_A, PI64_STK_A in LOS. subst a0 tp.
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
bstep. bstepz. do 10 bstep.
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
pose proof (RTC_GIPC _ _ _ _ _ _ _ HP1) as PCC. apply ro_C8_of_bytes_at in PCC.
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
bstepz.
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
replace (ret_pc (Z_to_bv 64 0x9de4c)) with (Z_to_bv 64 0x9de4c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP. change (6444320 - 164) with 6444156.
bstep. bstep. bstep. rewrite ?sxb_zero. bstep. if_false.
bstepz.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FF1. destruct FF1 as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. replace (Fr + 32 + Z.of_nat 8) with (Fr + 40) in FFb by lia.
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
(eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xt3 xt4 xt5 xt6 : word),
mem_inv asegs mX ->
rw_cells asegs mX (bv_unsigned sp + -96) frc -> rw_cells asegs mX sh shc -> rw_cells asegs mX Fr ffc ->
rw_cells asegs mX 6444156 [C4 eX] -> stk asegs mX lo (bv_unsigned sp + -96) ->
HEAPAx AX (BS ++ LB) LM ((Fr, 0) :: FRS) B mX mdX -> model_vm_only (cfg_model md) (cfg_model mdX) ->
heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX ->
fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
evt asegs (AJ5e A4L HIx AX T mdX)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 Fr) xs3 (Z_to_bv 64 sh) (Z_to_bv 64 Fr) xs6 xs7 xs8 s9 s10 s11 xt3 xt4 xt5 xt6)
F1 (Z_to_bv 64 0x9e03c) fc1 None mX (seg_rom asegs)))
end end end.
{ intros mX AX mdX F1 fc1 eX xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs7 xs8 xt3 xt4 xt5 xt6 MIX FRX FSHX FFX ERRX STX HPX VMX PDX FSX FRMX.
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
change (647292 + 4) with 647296.
clear FFX FSHX FPC.
reenterA asegs A4L HIx asegs_wx HP5.
do 15 bstep.
evt_done5.
eapply (K _ md5 m5 (bv_swrap 32 (bv_unsigned xa1 + 0)) A5).
- assert (PD5 : heap_presD (Fr + 32) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m5).
{ eapply heap_presD_trans; [exact PDY |].
eapply (presD_fp HIx _ _ _ _ _ _ _ _ (Fr + 32) _ (bv_unsigned sp) fp HPY); [| lia | exact FPnc | exact FPfr | exact Hoff | exact Hwv].
intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
split; [| split; [| split; [| split]]].
+ apply ret_statew_intro; [exact FSX | exact FRMX].
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
2:{  destruct JO as [Hp _]. rewrite Hp in *. if_truex. bstep. bstep.
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
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MIc : mem_inv asegs mc |- _ => destruct (gi_roA mc MIc) as (RO1 & RO2 & RO3 & RO4) end end.
bstep. asan_chkA.
bstep. bstep. bstep. bstep. bstep.
if_cases Hc1.
+
bstep. bstep. bstep. bstep.
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
assert (UBLO : bv_eqb (bword (flt_d (bv_extract 0 64 (le_bytes_to_word gi_c3A)) bits)) (Z_to_bv 64 0) = false).
{ unfold flt_d. change (bv_unsigned (bv_extract 0 64 (le_bytes_to_word gi_c3A))) with QAzu.Mq1.B_I32MINU.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_i32_lo (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold flt_d in Hc1. change (bv_unsigned (bv_extract 0 64 (le_bytes_to_word gi_c1A))) with QAzu.Mq1.B_I32MIN in Hc1.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b) in Hc1.
destruct (QAzu.Mq1.flt (bv_unsigned bits) QAzu.Mq1.B_I32MIN); [discriminate | reflexivity]. }
assert (UBHI : bv_eqb (bword (flt_d bits (bv_extract 0 64 (le_bytes_to_word gi_c4A)))) (Z_to_bv 64 0) = false).
{ unfold flt_d. change (bv_unsigned (bv_extract 0 64 (le_bytes_to_word gi_c4A))) with QAzu.Mq1.B_I32MAXU.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b).
rewrite (QAzu.Mq1.ub_i32_hi (bv_unsigned bits) BITR (NANOK bits Hc3)); [reflexivity|].
unfold flt_d in Hc2. change (bv_unsigned (bv_extract 0 64 (le_bytes_to_word gi_c2A))) with QAzu.Mq1.B_I32MAX in Hc2.
change (fst (fp_lt fmt_double ?a ?b)) with (QAzu.Mq1.flt a b) in Hc2.
destruct (QAzu.Mq1.flt QAzu.Mq1.B_I32MAX (bv_unsigned bits)); [discriminate | reflexivity]. }
bstep. bstep. bstep. bstep. rewrite UBLO; cbv iota.
bstep. bstep. bstep. bstep. rewrite UBHI; cbv iota.
bstep. bstep. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
--
bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
*
bstep. rewrite ?sxb_zero. bstep. if_true. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
bstep. rewrite ?sxb_zero. bstep. if_true. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-
bstep. bstep. if_lit. bstep. bstep. if_lit.
destruct Jc as (pb_ & PBS & REST & EBS & OPB & (cty & v & junk_ & ER & Hcty & CELLS)). cbn [hl_segs hla_base A4L A4H] in CELLS. unfold jhdr_cells in CELLS. cbn [app] in CELLS.
assert (INp56 : In (p, 56) (BS ++ LB)) by (apply in_or_app; left; rewrite EBS, ER; cbn; left; reflexivity).
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p 56 6 HPc INp56 ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
bstep. asan_chkA.
bstep. rewrite sx32_small by lia.
bstep. bstep.
destruct Hcty as [-> | ->]; if_lit.
+
asan_chkA. bstep.
bstep. bstep. bstep.
if_cases Hc5.
*
bstep. bstep. bstep.
if_cases Hc6.
-- gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-- bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
+
asan_chkA. bstep.
bstep. bstep. bstep.
if_cases Hc7.
* bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
* bstep. bstep. bstep. bstep.
if_cases Hc8.
-- gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-- bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
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
assert (CONT : forall xa2 : word, evt asegs Q
(MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 TX) xa2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x10 x25 x26 x27 x28 x29 x30 x31) Fx (Z_to_bv 64 0x9dfc0) fcx None mc rom))
end end.
{ intros xa2.
bstep. bstep. bstep. bstep.

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
replace (ret_pc (Z_to_bv 64 647120)) with (Z_to_bv 64 647120) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
reenterA asegs A4L HIx asegs_wx HP3.
bstep.

assert (SHE3 : ro_cells asegs m3 2148256399 [C1 (Z_to_bv 8 0)]).
{ apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (6444156 / 8) HP3) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (6444156 / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
specialize (X ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
change (6444156 / 8 + 2147450880) with 2148256399 in X. exact X. }
destruct HRV as [-> | ->]; if_lit.
+
bstep. bstep. bstep. sh_norm.
replace ((Fr + 32) / 8 + 2147450880) with (sh + 4) by (unfold sh; clear - HFal; Z.div_mod_to_equations; lia).
bstep. bstep. rewrite ?zxb_zero. if_false. bstep.
bstep. bstep. bstep.
if_cases Hc5.
* bstep. bstep. bstep.
if_cases Hc6.
-- gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
-- bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
* bstep. rewrite ?sxb_zero. bstep. if_false. bstep. bstepz. bstep. bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13.
+
bstep. bstep.
gi_exit EPI XHP3 XPD PDm3 HP3 A3 md3 m3 VM13. }
bstep. asan_chkA.
bstep. bstep. bstep.
destruct ALT as [[Hl ETX] | [Hl ->]].
+  if_falsex. bstep. bstep. rewrite <- ETX. apply CONT.
+  if_truex. asan_chkA. bstep. bstep. apply CONT.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
-  bstep. bstep. if_lit. bstep. bstep. if_lit. gi_exit EPI XHP XPD PD1 HP1 A1 md1 m1' VM1.
Qed.
End AJoGetInt.
End RC__1.
