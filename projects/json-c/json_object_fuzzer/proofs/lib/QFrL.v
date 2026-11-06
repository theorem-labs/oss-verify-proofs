(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Ql4f Q9O6 QL3k Q228 QiVi QZ8V QQ2r QtyQ Q1Ey QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 QlKV.Mq6 Ql4f.Mq2 Q228.Mq0 QiVi.Mq1 Qwm6.Mq1 QZ8V.Mq0 QQ2r.Mq0 QtyQ.Mq0 QiVi.Mq0.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem json_escape_str_A_16 : esc_specA_al HIx 16.
Proof.
unfold esc_specA_al. intros until errv. intros D32 HP PB INs Hs1 Hs2 SRC SRCL Hn CAP TXT NEED FL FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
subst a0 a1 a2 a3 tp.
unfold AESCAPE, AESC_STACK in *.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL16 : Z.land fl 16 = 0) by (replace 16 with (Z.land 58 16) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HTLE.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold JHEX_A, A_JHEX_SLOT, A_JHEX in JHX.

pose proof JHX as JHX0. stash JHX0. pose proof SRC as SRC0. stash SRC0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -240, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 240%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -224)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -224 - (bv_unsigned sp + -224) mod 32) with (bv_unsigned sp + -240) by (clear - D32; Z.div_mod_to_equations; lia).
do 11 step.
norm_sx32. step. if_false. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := (pb, PB_SZ) :: (buf, cap) :: LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI1 | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - D32; Z.div_mod_to_equations; lia.
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
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBS; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | cbn; lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBUF; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | cbn; lia | cbn; lia]].
assert (JHX1 : JHEX_A m1') by (eapply JHEX_A_pres; [exact HPR1 | exact JHX]).
clear SB1 SB2 SB3 UARC.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
clear SHB1.
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1'. change (hl_segs A4L) with asegs in MI1'. clear MI1.
assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; right; right; exact Hb)) as [OFF OFS].
assert (HPR01 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
- eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
pose proof (rtc_cell HIx _ _ _ _ _ _ _ 0xe6a70 (le8 (Z_to_bv 64 0xea520)) HP1 ltac:(unfold a4_rt_consts; repeat (first [left; reflexivity | right]))) as GOTH.
apply ro_C8_of_bytes_at in GOTH.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m1') as MU.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz. step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. stepz. stepz. stepz. step. step.
do 4 stepz. step. do 4 stepz.
step.
destruct (Z.eq_dec n 0) as [N0 | NN0].
+ revert SRCL. subst n. intros SRCL. if_lit. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
match goal with H : mem_inv asegs mL |- _ => rename H into MIL end.
match goal with H : stk asegs mL lo _ |- _ => rename H into STL end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FR. destruct FR as [LOCr RESTc]. cbn [cells_size csize Nat.add] in RESTc. change (Z.of_nat 120) with 120 in RESTc.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RESTc. destruct RESTc as [GAPc SAVc]. cbn [cells_size csize Nat.add] in SAVc.
change (Z.of_nat 16) with 16 in SAVc. replace (bv_unsigned sp + -240 + 120 + 16) with (bv_unsigned sp + -104) in SAVc by lia.
pose proof (rw_cells_merge asegs mL _ [] _ [] ltac:(cbn [app]; rewrite app_nil_r; exact LOCr)) as LOCc. cbn [app cells_size csize Nat.add] in LOCc.
change 16%nat with (Z.to_nat 16) in GAPc.
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [] [8%nat; 7%nat; 17%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
assert (HPL : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mL md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MIL].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (HPR0L : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mL).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (INVL : QtyQ.Mq0.esc_inv0 HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB LM FRS B pb lo bpos cap 0 (bv_unsigned sp + -240) 16 Fr 248 A1 0 mL md1).
{ eexists _, _, _, _, _. exists buf, cap, bpos, content, errv1, B.
split; [exact HPL|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold QtyQ.Mq0.escCH0. constructor; [exact LOCc|]. constructor; [exact GAPc|]. constructor; [exact SAVc|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold QtyQ.Mq0.escCH0. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact STL|].
split; [exact HPR0L|]. split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
evt_done5.
eapply (QtyQ.Mq0.esc_epiA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap 0 src T
(bv_unsigned sp + -240) 16 Fr ltac:(right; reflexivity) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia) LO LOS CAP K);
[exact INVL | apply fsaved_refl | intros X; exact X | lia].
+ if_falsex.
stepz. step. step. step. stepz. step. stepz. step.
rewrite (unsigned_lit fl) by lia. rewrite FL16.
step. stepz. step. step. step. step. step.
step. stepz. step. stepz.
step. stepz. step. stepz. step. step. stepz. step. stepz. step. stepz.
step. step. step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
match goal with H : mem_inv asegs mL |- _ => rename H into MIL end.
match goal with H : stk asegs mL lo _ |- _ => rename H into STL end.
unstash JHX0. unstash SRC0.

rewrite (unsigned_lit (pb + 12)), (unsigned_lit (pb + 8)) in FR by lia.
rewrite !Z.shiftr_div_pow2 in FR by lia. change (2^3) with 8 in FR.
replace ((pb + 12) / 8) with (pb / 8 + 1) in FR by (clear - Hal; Z.div_mod_to_equations; lia).
replace ((pb + 8) / 8) with (pb / 8 + 1) in FR by (clear - Hal; Z.div_mod_to_equations; lia).
rewrite land7_mod8 in FR by lia. replace ((pb + 12) mod 8 + 3) with 7 in FR by (clear - Hal; Z.div_mod_to_equations; lia).
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _] _)) in FR. destruct FR as [LOCc RESTc]. cbn [cells_size csize Nat.add] in RESTc.
change (Z.of_nat 120) with 120 in RESTc.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RESTc. destruct RESTc as [GAPc SAVc]. cbn [cells_size csize Nat.add] in SAVc.
change (Z.of_nat 16) with 16 in SAVc. replace (bv_unsigned sp + -240 + 120 + 16) with (bv_unsigned sp + -104) in SAVc by lia.
change 16%nat with (Z.to_nat 16) in GAPc.
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [] [8%nat; 7%nat; 17%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
assert (HPL : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mL md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MIL].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (HPR0L : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mL).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (INVL : esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB LM FRS B pb lo bpos cap n (bv_unsigned sp + -240) 16 Fr 248 A1 0 mL md1).
{ eexists _, _, _, _, _, _. exists buf, cap, bpos, content, errv1, B.
split; [exact HPL|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold escCH. constructor; [exact LOCc|]. constructor; [exact GAPc|]. constructor; [exact SAVc|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold escCH. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact STL|].
split; [exact HPR0L|]. split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
evt_done5.
pose proof (QtyQ.Mq0.esc_loopA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap Sa n sa sk src T
(bv_unsigned sp + -240) 16 Fr ltac:(right; reflexivity) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia)
LO LOS HT CAP TXT NEED JHX0 INs Hs1 Hs2 SRC0 SRCL ltac:(lia) PFRT PFLO OBL_PFRT OBL_PFLO SNP_U K (Z.to_nat n)) as LOOP.
unfold loopKA in LOOP.
eapply (LOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mL md1 A1 0 0 0); [exact INVL | apply fsaved_refl | exact FRM | lia | lia | lia | lia].
Qed.
End Esc.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QKQo QPZI QlCE QhHQ Q5Ki QmZZ QkMG Qu4M QG8z Qdyh Q2Sr QLbz Q6WR QrPc Q30W Qiiq QrQv QGdd QdGy QcmL QV7s QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QRUw.Mq2 QmZZ QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd QdGy.Mq0 QcmL.Mq0 QsKa.Mq8 QrQv.Mq2 QV7s QdGy QQ2r.Mq4 QtyQ.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq4 QdGy.Mq5 QdGy.Mq1.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutM.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis USE : uselocale_A_stmt.
Hypothesis FREEL : freelocale_A_stmt HIx.

Ltac if_vm := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
first [ replace c with true by (vm_compute; reflexivity); cbv iota | replace c with false by (vm_compute; reflexivity); cbv iota ] end.

Lemma seg_out_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (LK : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (cur0 nl : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
tdepth_ok ts -> JOUT (pf_len pf) ts ->
pa_oldloc pa = LC_GLOBAL_A -> In (pa_newloc pa, nl) LM ->
rw_cells asegs me LOCCELL_A [C8 (Z_to_bv 64 cur0)] -> 0 <= cur0 < 2^64 ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
0 <= pa_bslack pa ->
model_vm_only (cfg_model md0) (pf_md pf) ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc (lb_remove (pa_newloc pa) LM) FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 (Z_to_bv 64 (pf_tk pf + 56)) s11 t4 t6 F fc m).
Proof.
intros until fc. intros STC INVW TDOK JO OLDL INNL LOC0 CUR0 S0V RAV BSL VM0 FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct RR as (LRR & MXB & FLB).
assert (RAE : bv_unsigned (pe_ra sv) mod 2 = 0) by (rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity).
pose proof INVW as (CORE & BASE & LVW & BUDW).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof BASE as (HP & ST & ERR & _ & _ & _ & HPR & MDV & G). clear BASE.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
revert STC INVW K. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. subst oldloc. intros STC INVW K.
set (pfx := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (pax := PEFA sp0 Ff LC_GLOBAL_A newloc bsl dsl) in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof alloc_ceiling_range as ACR.
set (LBall := pe_blocksA pfx q LBc ts0 ++ LK) in *.
assert (INtkB : In (tk, 72) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INqB : In (q, 32 * mxd) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (tk, 72) (LBall ++ LM)) by (apply in_or_app; left; exact INtkB).
assert (INq : In (q, 32 * mxd) (LBall ++ LM)) by (apply in_or_app; left; exact INqB).
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as Himg_t.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as APt.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as Himg_q.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as APq.
cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in Himg_t, Himg_q, APt, APq. unfold A_SB in APt, APq.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk) as DFt. rewrite fr_size_2 in DFt.
assert (Htq : tk <> q).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold LBall, pe_blocksA in ND. rewrite !map_app in ND. cbn [map blk_addr fst pfx pf_tk pf_mxd] in ND.
apply NoDup_app_remove_r in ND. apply NoDup_app_remove_r in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

destruct (nth_error levels depth) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
pose proof (TSK depth l Hl) as Ld.
pose proof (LVW depth l Hl) as ([ST26 SS26] & _).

assert (SHT : ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
assert (SHL : ro_cells asegs m ((q + 32 * Z.of_nat depth) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ exact (lvl_shadowAg HIx _ _ _ _ _ _ _ q mxd depth HP INqB ltac:(lia) ltac:(lia) D32). }

assert (LOCcs : forall a, LOCCELL_A <= a < LOCCELL_A + 8 -> hl_client_static A4H a /\ ~ a4_volatile a).
{ intros a Ha. unfold LOCCELL_A, A_TP in Ha. cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
assert (LOCm : rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 cur0)]).
{ eapply (heap_presx_rw_cells A4H); [exact HPR | exact LOC0 | right; left; cbn; intros a Ha; apply LOCcs; lia]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.

reenterA asegs A4L HIx asegs_wx HP.
eapply out_checksAJ; [exact TOK | exact FR | exact Ld | exact SHT | exact SHL
| exact D32 | lia | lia | lia | lia | exact Htal | lia | lia | exact Hqal | exact Hdtq | lia | exact APt | exact APq | exact GEO | lia | exact ST26 | exact SS26 | exact MI |].
intros mc a0' a1' a2' a3' a4' errf HEF TOKc MUc WMc MIc.
assert (MUc72 : munch [(tk, tk + 72)] m mc) by (eapply munch_weaken; [| exact MUc]; intros z Hz; cbn [outside] in Hz |- *; lia).
pose proof (PE_INVW_A_tokw1 HIx GA GA_outside pfx pax q LBc LM FRS payload me lo m mc md A B ts0 LK cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) errf ucs high quote)
STC INVW MUc72 WMc MIc TOKc CO eq_refl) as INVWc.
pose proof (OUTW_of_INVW HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVWc) as OUTWc.
set (tsc := ts_set_x ts0 co (TS isd stpos (Z_to_bv 64 co) errf ucs high quote)) in *.
assert (LOCmc : rw_cells asegs mc LOCCELL_A [C8 (Z_to_bv 64 cur0)]).
{ eapply rw_cells_transport; [exact LOCm | exact MUc | exact WMc |]. unfold LOCCELL_A, A_TP. cbn [disjoint_from cells_size csize Nat.add]. lia. }
pose proof OUTWc as ((_ & _ & _ & _ & _ & _ & _ & _ & FRc) & _).
destruct FRc as (SLc & _). unfold pe_slotsA in SLc. cbn zeta in SLc. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLc. unfold A_SB in SLc.
clear TOK FR Ld SHT SHL LOCm MI TSK PB.

step. step.
eapply evt_cut; [eapply USE; [exact LOCmc | exact CUR0 | unfold LC_GLOBAL_A; lia | reflexivity | eassumption] |].
intros ms1 (m1 & a1x & a2x & a3x & a4x & -> & MU1 & WM1 & MI1 & LOC1).
replace (ret_pc (Z_to_bv 64 0x98148)) with (Z_to_bv 64 0x98148) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA cur0 LC_GLOBAL_A) with GLOBLOC_A in LOC1
by (unfold usl_newA, LC_GLOBAL_A; destruct (Z.eqb_spec (2^64 - 1) 0); [lia|]; rewrite Z.eqb_refl; reflexivity).
pose proof (OUTW_locw HIx GA GA_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC OUTWc MU1 WM1 MI1) as OUTW1.
pose proof OUTW1 as ((_ & _ & _ & _ & _ & _ & _ & _ & FR1) & HP1 & ST1 & ERR1 & _).
destruct FR1 as (SL1 & _). unfold pe_slotsA in SL1. cbn zeta in SL1. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SL1. unfold A_SB in SL1.
clear SLc LOCmc MUc MUc72 WMc MIc TOKc INVWc OUTWc.

step. step.
evt_done5.
eapply (FREEL) with (LB := LBall) (LM := LM) (FRS := (Ff, 2) :: FRS) (d := newloc) (n := nl) (lo := lo) (errv := errv);
[ exact HP1 | exact INNL | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - Gspf; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR1 | reflexivity | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 m2 md2 A2 r2 RS2 VM2 ST2 HPR2 ERR2 HP2. open_ret RS2.
rewrite (unsigned_lit spf) in ST2, HPR2 by lia.
pose proof (OUTW_call HIx GA GA_pres pfx pax q LBc LM (lb_remove newloc LM) FRS me lo m1 m2 md md2 A A2 B B tsc LK cb nb pj sv errv errv
STC OUTW1 (lb_remove_incl newloc LM) VM2 HPR2 HP2 ST2 ERR2 (Z.le_refl _) (Z.le_refl _)) as OUTW2.
assert (LOC2 : rw_cells asegs m2 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact LOC1 | right; left; cbn; intros a Ha; apply LOCcs; lia]. }
clear OUTW1 HP1 ST1 ERR1 SL1 LOC1 MU1 WM1 MI1.
destruct OUTW2 as (CORE2 & _ & _ & _ & HPRX2 & MDV2 & G2 & LVW2 & BB2 & BD2).
destruct CORE2 as (_ & _ & _ & _ & TOK2 & PB2 & _ & TSK2 & FR2).
unfold tsc, ts_set_x, ts0 in TOK2, PB2, TSK2, LVW2, BB2. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pfx pf_tk pf_mxd pf_fl] in TOK2, PB2, TSK2, LVW2, BB2.
assert (SHT2 : ro_cells asegs m2 (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP2 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
pose proof FR2 as (SL2 & _). unfold pe_slotsA in SL2. cbn zeta in SL2. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SL2. unfold A_SB in SL2.
pose proof TOK2 as TOK2c. unfold tok_cells_g in TOK2c. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK2c.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold shA, SB2, SB7, SB8, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. step. rewrite ?sxb_zero. if_vm.
step. rewrite <- (Z_to_bv_bv_unsigned (sx32 errf)).
pose proof (bv_unsigned_in_range 64 (sx32 errf)) as EWR; unfold bv_modulus in EWR; cbn in EWR.
assert (VM02 : model_vm_only (cfg_model md0) (cfg_model md2)).
{ eapply model_vm_only_trans; [exact VM0 | exact MDV2]. }
destruct (Z.eq_dec (bv_unsigned (sx32 errf)) 0) as [E0 | En].
-
rewrite E0. step. if_true.
evt_done5.
eapply (out_success_A HIx GA GA_outside GA_pres PUT pfx pax q pb lo depth levels l pbs objbs LBc LK (lb_remove newloc LM) FRS
(TS isd stpos (Z_to_bv 64 co) errf ucs high quote) cb nb pj sv errv m2 me md2 md0 A2 B T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | exact LEN32 | exact D32 | exact Hl | exact LVW2 | exact TSK2 | exact TOK2 | exact FR2 | exact PB2 | exact Hpb | exact ST2 | exact ERR2 | exact LOC2
| exact HPRX2 | exact S0V | exact RAV | exact VM02
| pose proof (proj1 TDOK depth l Hl) as DL; cbn [t_levels] in DL; pose proof (odep_nonneg (tl_cs l)); lia
| intros s9 Hs9; assert (EE : errf = err) by (destruct HEF as [HE | [HE | [HE | HE]]]; [exact HE | rewrite HE in E0; discriminate E0 | rewrite HE in E0; discriminate E0 | rewrite HE in E0; discriminate E0]);
subst errf; exact (JOUT_level len ts0 l s9 JO E0 Hl Hs9)
| exact G2 | exact BSL | exact BB2 | exact BD2 | exact FS | exact FRM | exact K ].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
unfold LBall, pe_blocksA, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pfx pf_tk pf_mxd]. perm.
-
step. if_falsex. step. step.
evt_done5.
eapply (out_finish_A HIx GA GA_outside pfx pax LBc (objbs ++ LK) (lb_remove newloc LM) FRS me lo _ md2 md0 A2 B [] ((tk, 72) :: (q, 32 * mxd) :: pbs ++ concat (map lvl_blocks levels)) 0
cb nb pj sv errv T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | | left; split; reflexivity | exact FR2 | exact ST2 | exact ERR2 | exact LOC2 | exact HPRX2 | exact VM02 | exact G2 | | exact BD2 | exact RAE | exact FS | exact FRM | exact K ].
+ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
unfold LBall, pe_blocksA, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pfx pf_tk pf_mxd app]. set (CC := concat (map lvl_blocks levels)). perm.
+ exists q, pb, (Z.of_nat depth), pbs, levels, (TS isd stpos (Z_to_bv 64 co) errf ucs high quote).
split; [reflexivity|]. split; [rewrite LEN32; cbn [pfx pf_mxd]; lia|]. split; [cbn [pfx pf_mxd pf_fl]; lia|].
split; [exact TOK2|]. split; [exact PB2|]. split; [exact Hpb|]. split; [exact TSK2|].
split.
* intros i li Hli Hile. destruct (LVW2 i li Hli) as (_ & Ji & Ni & _). split; [exact Ji|].
destruct Ni as [Ni | Ni]; cbn [name_ok] in Ni; [left; exact Ni | right].
destruct Ni as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E].
* intros i li Hli Hlt. destruct (LVW2 i li Hli) as (_ & _ & _ & CL). apply CL. lia.
+ cbn [app length pax pa_bslack]. unfold tstate_blocks in BB2. cbn [t_pbs t_objbs t_levels pax pa_bslack] in BB2. rewrite !length_app in BB2. rewrite length_app.
unfold K_free, K_exit in *. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in *. lia.
Qed.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (fc0 : bv 32) (md0 : config) (cur0 nl : Z).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis OLDL : pa_oldloc pa = LC_GLOBAL_A.
Hypothesis INNL : In (pa_newloc pa, nl) LM.
Hypothesis LOCME : rw_cells asegs me LOCCELL_A [C8 (Z_to_bv 64 cur0)].
Hypothesis CUR0 : 0 <= cur0 < 2^64.
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 (pf_tk pf).
Hypothesis RAV : pe_ra sv = Z_to_bv 64 PE_RA2.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis VM01 : model_vm_only (cfg_model md0) (pf_md pf).
Hypothesis KRET : forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc (lb_remove (pa_newloc pa) LM) FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms'.

Lemma kout_A : KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0.
Proof.
intros ts LK m md A B cb nb pj errv x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 F fc INVW TDK JO FS FRM.
eapply (seg_out_A pf pa q LBc LM FRS payload me lo m md md0 A B ts LK cb nb pj sv errv T cur0 nl) with (F0 := F0) (fc0 := fc0);
[exact STC | exact INVW | exact TDK | exact JO | exact OLDL | exact INNL | exact LOCME | exact CUR0 | exact S0V | exact RAV | exact BSL | exact VM01 | exact FS | intros _; exact FRM | exact KRET].
Qed.
End PeSOutM.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QRUw.Mq2 QmZZ QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv QGdd.Mq0 QdGy.Mq7 QcmL QsKa.Mqh QrQv.Mq4 QV7s.Mq3 QdGy.Mqd QQ2r.Mq8 QtyQ.Mqc.
Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import Q2EX QdGy.Mqb QdGy.Mqc QdGy.Mq8.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutMB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis USE : uselocale_A_stmt.
Hypothesis FREEL : freelocale_A_stmt HIx.

Ltac if_vm := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
first [ replace c with true by (vm_compute; reflexivity); cbv iota | replace c with false by (vm_compute; reflexivity); cbv iota ] end.

Lemma seg_out_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (LK : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (cur0 nl : Z)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
tdepth_ok ts -> JOUT (pf_len pf) ts ->
pa_oldloc pa = LC_GLOBAL_A -> In (pa_newloc pa, nl) LM ->
rw_cells asegs me LOCCELL_A [C8 (Z_to_bv 64 cur0)] -> 0 <= cur0 < 2^64 ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
0 <= pa_bslack pa ->
model_vm_only (cfg_model md0) (pf_md pf) ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc (lb_remove (pa_newloc pa) LM) FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC INVW TDOK JO OLDL INNL LOC0 CUR0 S0V RAV BSL VM0 FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct RR as (LRR & MXB & FLB).
assert (RAE : bv_unsigned (pe_ra sv) mod 2 = 0) by (rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity).
pose proof INVW as (CORE & BASE & LVW & BUDW).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof BASE as (HP & ST & ERR & _ & _ & _ & HPR & MDV & G). clear BASE.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in *. subst choff.
revert STC INVW K. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. subst oldloc. intros STC INVW K.
set (pfx := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (pax := PEFA sp0 Ff LC_GLOBAL_A newloc bsl dsl) in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
pose proof alloc_ceiling_range as ACR.
set (LBall := pe_blocksA pfx q LBc ts0 ++ LK) in *.
assert (INtkB : In (tk, 72) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INqB : In (q, 32 * mxd) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (tk, 72) (LBall ++ LM)) by (apply in_or_app; left; exact INtkB).
assert (INq : In (q, 32 * mxd) (LBall ++ LM)) by (apply in_or_app; left; exact INqB).
assert (INF : In (Ff, 2) ((Ff, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as Himg_t.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as APt.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as Himg_q.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP INq) as APq.
cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in Himg_t, Himg_q, APt, APq. unfold A_SB in APt, APq.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INtk) as DFt. rewrite fr_size_2 in DFt.
assert (Htq : tk <> q).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold LBall, pe_blocksA in ND. rewrite !map_app in ND. cbn [map blk_addr fst pfx pf_tk pf_mxd] in ND.
apply NoDup_app_remove_r in ND. apply NoDup_app_remove_r in ND. apply NoDup_app_remove_l in ND. apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.

destruct (nth_error levels depth) as [l|] eqn:Hl; [| apply nth_error_None in Hl; lia].
pose proof (TSK depth l Hl) as Ld.
pose proof (LVW depth l Hl) as ([ST26 SS26] & _).

assert (SHT : ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
assert (SHL : ro_cells asegs m ((q + 32 * Z.of_nat depth) / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ exact (lvl_shadowAg HIx _ _ _ _ _ _ _ q mxd depth HP INqB ltac:(lia) ltac:(lia) D32). }

assert (LOCcs : forall a, LOCCELL_A <= a < LOCCELL_A + 8 -> hl_client_static A4H a /\ ~ a4_volatile a).
{ intros a Ha. unfold LOCCELL_A, A_TP in Ha. cbn [hl_client_static A4H]. unfold a4_client_static, a4_volatile. lia. }
assert (LOCm : rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 cur0)]).
{ eapply (heap_presx_rw_cells A4H); [exact HPR | exact LOC0 | right; left; cbn; intros a Ha; apply LOCcs; lia]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.

reenterA asegs A4L HIx asegs_wx HP.
eapply out_checksBJ; [exact TOK | exact FR | exact Ld | exact SHT | exact SHL
| exact D32 | lia | lia | lia | lia | exact Htal | lia | lia | exact Hqal | exact Hdtq | lia | exact APt | exact APq | exact GEO | lia | exact ST26 | exact SS26 | exact MI |].
intros mc a0' a1' a2' a3' a4' a5' a6' a7' errf HEF TOKc MUc WMc MIc. unfold pe_msO. cbn [pfx pax pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc].
assert (MUc72 : munch [(tk, tk + 72)] m mc) by (eapply munch_weaken; [| exact MUc]; intros z Hz; cbn [outside] in Hz |- *; lia).
pose proof (PE_INVW_A_tokw1 HIx GA GA_outside pfx pax q LBc LM FRS payload me lo m mc md A B ts0 LK cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) errf ucs high quote)
STC INVW MUc72 WMc MIc TOKc CO eq_refl) as INVWc.
pose proof (OUTW_of_INVW HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INVWc) as OUTWc.
set (tsc := ts_set_x ts0 co (TS isd stpos (Z_to_bv 64 co) errf ucs high quote)) in *.
assert (LOCmc : rw_cells asegs mc LOCCELL_A [C8 (Z_to_bv 64 cur0)]).
{ eapply rw_cells_transport; [exact LOCm | exact MUc | exact WMc |]. unfold LOCCELL_A, A_TP. cbn [disjoint_from cells_size csize Nat.add]. lia. }
pose proof OUTWc as ((_ & _ & _ & _ & _ & _ & _ & _ & FRc) & _).
destruct FRc as (SLc & _). unfold pe_slotsA in SLc. cbn zeta in SLc. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLc. unfold A_SB in SLc.
clear TOK FR Ld SHT SHL LOCm MI TSK PB.

unfold shA, SB2, SB7, SB8, A_SB, A_TP in *. unfold A_SB in *.
step. step.
eapply evt_cut; [eapply USE; [exact LOCmc | exact CUR0 | unfold LC_GLOBAL_A; lia | reflexivity | eassumption] |].
intros ms1 (m1 & a1x & a2x & a3x & a4x & -> & MU1 & WM1 & MI1 & LOC1).
replace (ret_pc (Z_to_bv 64 0x99a04)) with (Z_to_bv 64 0x99a04) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA cur0 LC_GLOBAL_A) with GLOBLOC_A in LOC1
by (unfold usl_newA, LC_GLOBAL_A; destruct (Z.eqb_spec (2^64 - 1) 0); [lia|]; rewrite Z.eqb_refl; reflexivity).
pose proof (OUTW_locw HIx GA GA_loc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC OUTWc MU1 WM1 MI1) as OUTW1.
pose proof OUTW1 as ((_ & _ & _ & _ & _ & _ & _ & _ & FR1) & HP1 & ST1 & ERR1 & _).
destruct FR1 as (SL1 & _). unfold pe_slotsA in SL1. cbn zeta in SL1. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SL1. unfold A_SB in SL1.
clear SLc LOCmc MUc MUc72 WMc MIc TOKc INVWc OUTWc.

step. step.
evt_done5.
eapply (FREEL) with (LB := LBall) (LM := LM) (FRS := (Ff, 2) :: FRS) (d := newloc) (n := nl) (lo := lo) (errv := errv);
[ exact HP1 | exact INNL | rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - Gspf; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR1 | reflexivity | rewrite unsigned_lit by lia; reflexivity | ].
intros ms2 m2 md2 A2 r2 RS2 VM2 ST2 HPR2 ERR2 HP2. open_ret RS2.
rewrite (unsigned_lit spf) in ST2, HPR2 by lia.
pose proof (OUTW_call HIx GA GA_pres pfx pax q LBc LM (lb_remove newloc LM) FRS me lo m1 m2 md md2 A A2 B B tsc LK cb nb pj sv errv errv
STC OUTW1 (lb_remove_incl newloc LM) VM2 HPR2 HP2 ST2 ERR2 (Z.le_refl _) (Z.le_refl _)) as OUTW2.
assert (LOC2 : rw_cells asegs m2 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact LOC1 | right; left; cbn; intros a Ha; apply LOCcs; lia]. }
clear OUTW1 HP1 ST1 ERR1 SL1 LOC1 MU1 WM1 MI1.
destruct OUTW2 as (CORE2 & _ & _ & _ & HPRX2 & MDV2 & G2 & LVW2 & BB2 & BD2).
destruct CORE2 as (_ & _ & _ & _ & TOK2 & PB2 & _ & TSK2 & FR2).
unfold tsc, ts_set_x, ts0 in TOK2, PB2, TSK2, LVW2, BB2. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pfx pf_tk pf_mxd pf_fl] in TOK2, PB2, TSK2, LVW2, BB2.
assert (SHT2 : ro_cells asegs m2 (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP2 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
pose proof FR2 as (SL2 & _). unfold pe_slotsA in SL2. cbn zeta in SL2. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SL2. unfold A_SB in SL2.
pose proof TOK2 as TOK2c. unfold tok_cells_g in TOK2c. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK2c.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
unfold shA, SB2, SB7, SB8, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. rewrite ?sxb_zero. step. step. if_vm.
step. step.
step. step.
rewrite <- (Z_to_bv_bv_unsigned (sx32 errf)).
pose proof (bv_unsigned_in_range 64 (sx32 errf)) as EWR; unfold bv_modulus in EWR; cbn in EWR.
assert (VM02 : model_vm_only (cfg_model md0) (cfg_model md2)).
{ eapply model_vm_only_trans; [exact VM0 | exact MDV2]. }
destruct (Z.eq_dec (bv_unsigned (sx32 errf)) 0) as [E0 | En].
-
rewrite E0. step. if_true.
evt_done5.
eapply (out_success_B HIx GA GA_outside GA_pres PUT pfx pax q pb lo depth levels l pbs objbs LBc LK (lb_remove newloc LM) FRS
(TS isd stpos (Z_to_bv 64 co) errf ucs high quote) cb nb pj sv errv m2 me md2 md0 A2 B T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | exact LEN32 | exact D32 | exact Hl | exact LVW2 | exact TSK2 | exact TOK2 | exact FR2 | exact PB2 | exact Hpb | exact ST2 | exact ERR2 | exact LOC2
| exact HPRX2 | exact S0V | exact RAV | exact VM02
| pose proof (proj1 TDOK depth l Hl) as DL; cbn [t_levels] in DL; pose proof (odep_nonneg (tl_cs l)); lia
| intros sz Hsz; assert (EE : errf = err) by (destruct HEF as [HE | [HE | [HE | HE]]]; [exact HE | rewrite HE in E0; discriminate E0 | rewrite HE in E0; discriminate E0 | rewrite HE in E0; discriminate E0]);
subst errf; exact (JOUT_level len ts0 l sz JO E0 Hl Hsz)
| exact G2 | exact BSL | exact BB2 | exact BD2 | exact FS | exact FRM | exact K ].
eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
unfold LBall, pe_blocksA, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pfx pf_tk pf_mxd]. perm.
-
step. if_falsex. step. step.
evt_done5. unfold APE_EPI1.
eapply (out_finish_B HIx GA GA_outside pfx pax LBc (objbs ++ LK) (lb_remove newloc LM) FRS me lo _ md2 md0 A2 B [] ((tk, 72) :: (q, 32 * mxd) :: pbs ++ concat (map lvl_blocks levels)) 0
cb nb pj sv errv T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | | left; split; reflexivity | exact FR2 | exact ST2 | exact ERR2 | exact LOC2 | exact HPRX2 | exact VM02 | exact G2 | | exact BD2 | exact RAE | exact FS | exact FRM | exact K ].
+ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl].
unfold LBall, pe_blocksA, tstate_blocks, ts0. cbn [t_pbs t_objbs t_levels pfx pf_tk pf_mxd app]. set (CC := concat (map lvl_blocks levels)). perm.
+ exists q, pb, (Z.of_nat depth), pbs, levels, (TS isd stpos (Z_to_bv 64 co) errf ucs high quote).
split; [reflexivity|]. split; [rewrite LEN32; cbn [pfx pf_mxd]; lia|]. split; [cbn [pfx pf_mxd pf_fl]; lia|].
split; [exact TOK2|]. split; [exact PB2|]. split; [exact Hpb|]. split; [exact TSK2|].
split.
* intros i li Hli Hile. destruct (LVW2 i li Hli) as (_ & Ji & Ni & _). split; [exact Ji|].
destruct Ni as [Ni | Ni]; cbn [name_ok] in Ni; [left; exact Ni | right].
destruct Ni as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E].
* intros i li Hli Hlt. destruct (LVW2 i li Hli) as (_ & _ & _ & CL). apply CL. lia.
+ cbn [app length pax pa_bslack]. unfold tstate_blocks in BB2. cbn [t_pbs t_objbs t_levels pax pa_bslack] in BB2. rewrite !length_app in BB2. rewrite length_app.
unfold K_free, K_exit in *. rewrite ?Nat2Z.inj_succ, ?Nat2Z.inj_add in *. lia.
Qed.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (fc0 : bv 32) (md0 : config) (cur0 nl : Z).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Hypothesis OLDL : pa_oldloc pa = LC_GLOBAL_A.
Hypothesis INNL : In (pa_newloc pa, nl) LM.
Hypothesis LOCME : rw_cells asegs me LOCCELL_A [C8 (Z_to_bv 64 cur0)].
Hypothesis CUR0 : 0 <= cur0 < 2^64.
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 (pf_tk pf).
Hypothesis RAV : pe_ra sv = Z_to_bv 64 PE_RA2.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis VM01 : model_vm_only (cfg_model md0) (pf_md pf).
Hypothesis KRET : forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc (lb_remove (pa_newloc pa) LM) FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms'.

Lemma kout_B : KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0.
Proof.
intros ts LK m md A B cb nb pj errv gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc INVW TDK JO FS FRM.
eapply (seg_out_B pf pa q LBc LM FRS payload me lo m md md0 A B ts LK cb nb pj sv errv T cur0 nl) with (F0 := F0) (fc0 := fc0);
[exact STC | exact INVW | exact TDK | exact JO | exact OLDL | exact INNL | exact LOCME | exact CUR0 | exact S0V | exact RAV | exact BSL | exact VM01 | exact FS | intros _; exact FRM | exact KRET].
Qed.
End PeSOutMB.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL3k.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVi.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZ8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZ8V. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiVi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem json_escape_str_A_16 : esc_specA_al HIx 16.
Proof.
unfold esc_specA_al. intros until errv. intros D32 HP PB INs Hs1 Hs2 SRC SRCL Hn CAP TXT NEED FL FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
subst a0 a1 a2 a3 tp.
unfold AESCAPE, AESC_STACK in *.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL16 : Z.land fl 16 = 0) by (replace 16 with (Z.land 58 16) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof alloc_ceiling_range as ACR.
pose proof (hiA_top_le A4L HIx) as HTLE.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold JHEX_A, A_JHEX_SLOT, A_JHEX in JHX.

pose proof JHX as JHX0. stash JHX0. pose proof SRC as SRC0. stash SRC0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -240, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 240%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -224)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -224 - (bv_unsigned sp + -224) mod 32) with (bv_unsigned sp + -240) by (clear - D32; Z.div_mod_to_equations; lia).
do 10 step. stepz.
norm_sx32. step. if_false. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := (pb, PB_SZ) :: (buf, cap) :: LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI1 | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - D32; Z.div_mod_to_equations; lia.
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
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp. unfold A_SB in HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBS; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | cbn; lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in PBUF; [| eapply client_range_block; [apply in_or_app; left; right; left; reflexivity | cbn; lia | cbn; lia]].
assert (JHX1 : JHEX_A m1') by (eapply JHEX_A_pres; [exact HPR1 | exact JHX]).
clear SB1 SB2 SB3 UARC.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
clear SHB1.
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1'. change (hl_segs A4L) with asegs in MI1'. clear MI1.
assert (SUB0 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; left; right; right; exact Hb|]. apply in_app_or in Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb. destruct (SUB0 b Hb) as [H|H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A1 m1' md1 HP1 ltac:(intros b Hb; right; right; exact Hb)) as [OFF OFS].
assert (HPR01 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1').
{ eapply heap_pres_trans.
- eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB0 ltac:(lia)). apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. lia.
- eapply heap_pres_weaken; [exact HPR1 | lia |]. intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; right; exact Hb | apply in_or_app; right; exact Hb]. }
pose proof (rtc_cell HIx _ _ _ _ _ _ _ 0xe8e78 (le8 (Z_to_bv 64 0xec940)) HP1 ltac:(unfold a4_rt_consts; repeat (first [left; reflexivity | right]))) as GOTH.
apply ro_C8_of_bytes_at in GOTH.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(lo, bv_unsigned sp); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m1') as MU.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz. step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step. step. stepz. stepz. stepz. step. step.
do 4 stepz. step. do 3 stepz. stepz. stepz.
step.
destruct (Z.eq_dec n 0) as [N0 | NN0].
+ revert SRCL. subst n. intros SRCL. if_lit. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
match goal with H : mem_inv asegs mL |- _ => rename H into MIL end.
match goal with H : stk asegs mL lo _ |- _ => rename H into STL end.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _] _)) in FR. destruct FR as [LOCr RESTc]. cbn [cells_size csize Nat.add] in RESTc. change (Z.of_nat 120) with 120 in RESTc.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RESTc. destruct RESTc as [GAPc SAVc]. cbn [cells_size csize Nat.add] in SAVc.
change (Z.of_nat 16) with 16 in SAVc. replace (bv_unsigned sp + -240 + 120 + 16) with (bv_unsigned sp + -104) in SAVc by lia.
change 16%nat with (Z.to_nat 16) in GAPc.

lazymatch type of LOCr with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
pose proof (rw_cells_merge asegs mL _ [] [c0; c1; c2] [c3; c4; c5; c6; c7] ltac:(cbn [app]; exact LOCr)) as LOC1;
cbn [app cells_size csize Nat.add] in LOC1;
lazymatch type of LOC1 with rw_cells _ _ _ [?d0; ?d1; ?d2; ?d3; ?d4; ?d5] =>
pose proof (rw_cells_merge asegs mL _ [d0; d1] [d2; d3; d4; d5] [] ltac:(cbn [app]; rewrite ?app_nil_r; exact LOC1)) as LOCc end end.
cbn [app cells_size csize Nat.add] in LOCc.
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [] [8%nat; 7%nat; 17%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
assert (HPL : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mL md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MIL].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (HPR0L : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mL).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (INVL : QtyQ.Mq8.esc_inv0 HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB LM FRS B pb lo bpos cap 0 (bv_unsigned sp + -240) 16 Fr 248 A1 0 mL md1).
{ eexists _, _, _, _, _, _. exists buf, cap, bpos, content, errv1, B.
split; [exact HPL|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold QtyQ.Mq8.escCH0. constructor; [exact LOCc|]. constructor; [exact GAPc|]. constructor; [exact SAVc|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold QtyQ.Mq8.escCH0. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact STL|].
split; [exact HPR0L|]. split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
evt_done5.
eapply (QtyQ.Mq8.esc_epiA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap 0 src T
(bv_unsigned sp + -240) 16 Fr ltac:(right; reflexivity) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia) LO LOS CAP K);
[exact INVL | apply fsaved_refl | intros X; exact X | lia].
+ if_falsex.
stepz. step. step. step. stepz. step. stepz.
step. rewrite (unsigned_lit fl) by lia. rewrite FL16.
step. rewrite ?(unsigned_lit Sa) by lia. rewrite ?(lxor_ones64 Sa) by lia. stepz.
step. rewrite (v_sltiu_0 (Z_to_bv 64 pb) 1) by (rewrite ?(unsigned_lit pb) by lia; lia).
step. rewrite ?(unsigned_lit pb) by lia. rewrite (land7_of_mod16 pb Hal).
step. stepz. step. stepz.
step. rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 Sa)) by (rewrite ?(unsigned_lit 0), ?(unsigned_lit Sa) by lia; lia).
step. step. step.
step. rewrite ?(v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite ?(unsigned_lit 0) by lia; lia).
step. stepz.
step. rewrite ?(unsigned_lit 0) by lia. change (Z.lor 0 0) with 0. stepz.
step. step. step. step. stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mL end.
match goal with H : mem_inv asegs mL |- _ => rename H into MIL end.
match goal with H : stk asegs mL lo _ |- _ => rename H into STL end.
unstash JHX0. unstash SRC0.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _] _)) in FR. destruct FR as [LOCc RESTc]. cbn [cells_size csize Nat.add] in RESTc.
change (Z.of_nat 120) with 120 in RESTc.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RESTc. destruct RESTc as [GAPc SAVc]. cbn [cells_size csize Nat.add] in SAVc.
change (Z.of_nat 16) with 16 in SAVc. replace (bv_unsigned sp + -240 + 120 + 16) with (bv_unsigned sp + -104) in SAVc by lia.
change 16%nat with (Z.to_nat 16) in GAPc.
lazymatch type of LOCc with rw_cells _ _ _ (CB 8 ?jb :: ?rest) =>
assert (JBL : length jb = 8%nat) by (destruct LOCc as [[Hwf _] _]; exact (proj1 Hwf));
eapply (rw_cells_recast_prefix asegs _ _ [CB 8 jb] [C8 (le_bytes_to_word jb)]) in LOCc; [| cbn; tauto | cbn [cells_bytes cbytes app]; rewrite (QtyQ.Mq8.le8_lbw8 jb JBL); reflexivity | reflexivity] end.
cbn [app] in LOCc.
eapply (rw_cells_split_CB asegs _ _ [_; _; _] 32 _ [] [8%nat; 7%nat; 17%nat]) in FF1; [| reflexivity].
cbn [app mk_CB_cells] in FF1.
assert (HPL : HEAPAx A1 ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mL md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | | exact WM | exact MIL].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP1 MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (HPR0L : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mL).
{ eapply heap_pres_trans; [exact HPR01|].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP1 MU WM SUB1 ltac:(lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
+ left. cbn [fst snd]. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
+ right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
assert (INVL : esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md LB LM FRS B pb lo bpos cap Sa n (bv_unsigned sp + -240) 16 Fr 248 A1 0 mL md1).
{ eexists _, _, _, _, _, _. exists buf, cap, bpos, content, errv1, B.
split; [exact HPL|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split. { unfold escCH. constructor; [exact LOCc|]. constructor; [exact GAPc|]. constructor; [exact SAVc|]. constructor; [exact FF1|]. constructor; [exact FSH1 | constructor]. }
split.
{ unfold escCH. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb; cbn [fr_ivs flat_map app]; right; right; exact Hb|].
split; [exact ERR1|]. split; [exact STL|].
split; [exact HPR0L|]. split; [exact VM1|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
evt_done5.
pose proof (QtyQ.Mq8.esc_loopA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb lo bpos cap Sa n sa sk src T
(bv_unsigned sp + -240) 16 Fr ltac:(right; reflexivity) ltac:(lia) ltac:(clear - D32; Z.div_mod_to_equations; lia)
LO LOS HT CAP TXT NEED JHX0 INs Hs1 Hs2 SRC0 SRCL ltac:(lia) PFRT PFLO OBL_PFRT OBL_PFLO SNP_U K (Z.to_nat n)) as LOOP.
unfold loopKA, st_escA in LOOP.

epose proof (LOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mL md1 A1 0 0 0 INVL (fsaved_refl _) FRM ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as LP.
rewrite Z.sub_0_r, Z.add_0_r in LP. exact LP.
Qed.
End Esc.
End RC__1.
