(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QkMG QKQo Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UgLo UC8c UPZI UG8z Udyh Ub4w Ua8x UXfU U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.

Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UPZI.Mq4.
Import QkMG.
Import UG8z Udyh.Mq0 Ub4w.
Import QKQo.
Import Ua8x.Mq4 UXfU.Mq2 U2Sr UPZI.Mq0.
Import QfLs.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeEntry.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.
Hypothesis USE : uselocale_stmt.
Hypothesis ERRNO : errno_location_stmt.
Hypothesis DUP : duplocale_stmt HIx.
Hypothesis NEWL : newlocale_stmt HIx.
Hypothesis FREEL : freelocale_stmt HIx.

Definition PE_ENTRY : Z := 0x21c38.

Local Ltac if_lit b :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota end.

#[using="Type"] Lemma rw_cells_recast_mid : forall segs m A pre mid mid' post,
rw_cells segs m A (pre ++ mid ++ post) ->
cells_wf mid' -> cells_bytes mid' = cells_bytes mid -> cells_size mid' = cells_size mid ->
rw_cells segs m A (pre ++ mid' ++ post).
Proof.
intros segs m A pre mid mid' post H Hwf HB HS.
destruct H as [[Hwf0 HB0] HW0].
apply cells_wf_app in Hwf0 as [H1 H23]. apply cells_wf_app in H23 as [H2 H3].
eapply rw_cells_recast.
- split; [split; [apply cells_wf_app; split; [exact H1| apply cells_wf_app; split; [exact H2 | exact H3]] | exact HB0] | exact HW0].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; assumption.
- rewrite !cells_bytes_app, HB. reflexivity.
- rewrite !cells_size_app, HS. reflexivity.
Qed.

#[using="Type"] Lemma tok_join32 : forall m tk (c0 c1 c2 c3 c4 c5 : cell) rest,
rw_cells rsegs m tk ([c0; c1; c2; c3; c4; c5] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ rest) ->
rw_cells rsegs m tk ([c0; c1; c2; c3; c4; c5] ++ [C8 (Z_to_bv 64 0)] ++ rest).
Proof. intros. eapply rw_cells_recast_mid; [exact H | cbn; auto | vm_compute; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma tok_split32 : forall m tk (c0 c1 c2 c3 c4 c5 : cell) rest,
rw_cells rsegs m tk ([c0; c1; c2; c3; c4; c5] ++ [C8 (Z_to_bv 64 0)] ++ rest) ->
rw_cells rsegs m tk ([c0; c1; c2; c3; c4; c5] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ rest).
Proof. intros. eapply rw_cells_recast_mid; [exact H | cbn; auto | vm_compute; reflexivity | reflexivity]. Qed.

Definition ts_init (mxd : Z) (pb : Z) (pbs : list blk) : tstate :=
TST 0%nat (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)) 0 pb pbs (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0)) 0 None [].

Local Ltac if_any := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
first [ assert_fails (idtac; match c with context [?x] => is_var x end); first [if_lit true | if_lit false]
| if_truex | if_falsex ] end.

#[using="USE ERRNO DUP NEWL FREEL"] Lemma seg_entry :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (TBS LBc : list blk) (tk sb len lenr lo : Z) (payload slack : list byte) (errv : word) (mxd fl : Z),
HEAPx A (TBS ++ LBc) m md ->
tok_fresh_g rsegs mxd fl m TBS tk ->
bytes_at rsegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_ok rsegs m LBc (bv_unsigned sp) sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> jc_glob_P m ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 - 12288 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->
let sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 in

(forall (newl q : Z) (m1 : word -> option byte) (md1 : Model) (A1 : AS S4L HIx) (pb : Z) (pbs : list blk)
(j1 j2 utf : list byte) (errv1 : word)
(x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word),
let pf := PEF tk LC_GLOBAL newl len lenr sb (bv_unsigned sp - 144) md1 mxd fl in
PE_STATIC HIx pf lo ->
PE_INV HIx pf q ((newl, 48) :: LBc) payload m1 lo m1 md1 A1 (ts_init mxd pb pbs) (Z_to_bv 8 1) j1 j2 utf sv errv1 ->
model_vm_only md md1 ->
heap_presx S4L xloc LBc (bv_unsigned sp) m m1 ->
rw_cells rsegs m1 LOCCELL [C8 (Z_to_bv 64 newl)] -> 0 < newl < 2^64 ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP 0 x1' gp' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6' F fc m1) md1) T) ->

(forall ms' md', pe_post_g HIx (PEF tk LC_GLOBAL 0 len lenr sb (bv_unsigned sp - 144) md mxd fl) sv F fc md LBc m lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PE_ENTRY) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until fl. intros HP TF STR PLEN LEN MODE SB0 SBL LOC LCK JCG0 ST LO LOS SPA HT SP63 ERR TP RAE A0 A1 A2 sv Kloop Kret. stash JCG0.
unfold_consts. word_range sp SPR. pose proof (hi_top_hi S4L HIx) as HTH. unfold_consts.

assert (LENROK : 0 <= lenr < 2^64 /\ (lenr = len \/ (lenr = LENW_C /\ 1 <= len))).
{ destruct MODE as [(-> & _) | (-> & _ & (str0 & Ep & _) & _)]; [lia|]. unfold LENW_C. split; [lia | right]. split; [reflexivity|].
subst payload. rewrite length_app in PLEN. cbn [length pf_mxd] in PLEN. lia. }
assert (PLOC : len = 0 \/ (bv_unsigned sp - 144 + PE_FRAME <= sb \/ exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b)).
{ unfold PE_FRAME. destruct MODE as [(_ & [L0 | [SPle | BL]]) | (_ & SPle & _)]; [left; exact L0 | right; left; lia | right; right; exact BL | right; left; lia]. }
destruct TF as (q & pb & pbs & ETBS & MXB & TOK & PB & Hpb & TSK).
subst a0 a1 a2 tp.
assert (INtk : In (tk, 72) (TBS ++ LBc)) by (rewrite ETBS; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (TBS ++ LBc)) by (rewrite ETBS; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q (32 * mxd) HP INq) as Himg_q. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_q.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ ltac:(rewrite ETBS in HP; exact HP)) as Htq.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (tk, tk + 72)] m) as MU.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
stash PB. stash TSK. stash STR. unfold LOCCELL in LOC. unfold LOCALE_LOCK in LCK.
apply rz_evt; [exact MOK|]. unfold PE_ENTRY.
step. carve_frame 144%nat ST.
do 13 step.
step. step. step. step. stepz. stepz. step. step.

eapply evt_cut; [eapply USE; [exact LOC | unfold GLOBLOC; lia | lia | reflexivity | exact MI] |].
intros ms1 (m1 & a1x & a2x & a3x & a4x & -> & MU1 & WM1 & MI1 & LOC1).
replace (ret_pc (Z_to_bv 64 0x21c90)) with (Z_to_bv 64 0x21c90) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_new GLOBLOC 0) with GLOBLOC in LOC1 by reflexivity. unfold LOCCELL in LOC1.
replace (usl_ret GLOBLOC) with LC_GLOBAL by reflexivity.
Local Ltac xport H MU WM := eapply rw_cells_transport in H; [| exact MU | exact WM | unfold LOCCELL; cbn; lia].
xport TOK MU1 WM1. xport FR MU1 WM1. xport LCK MU1 WM1. xport ERR MU1 WM1.
assert (ST1 : stk rsegs m1 lo (bv_unsigned sp + -144)).
{ eapply stk_transport; [exact ST | exact MU1 | exact WM1 |]. intros z Hz. left. unfold LOCCELL. cbn. lia. }
clear ST.

assert (MU01 : munch [(bv_unsigned sp - 144, bv_unsigned sp); (tk, tk + 72); (LOCCELL, LOCCELL + 8)] m m1).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU1]]; intros z Hz; cbn in Hz |- *; clear - Hz; tauto.    }
pose proof (wmono_trans _ _ _ _ WM WM1) as WM01. clear MU WM MU1 WM1 MI.
rename MU01 into MU. rename WM01 into WM.
step. if_any. step. step. step.
first [ ubsan_align Htal | (rewrite ?(unsigned_lit tk) by lia; rewrite (land7_of_mod16 tk Htal); if_any) ]. step.
apply (tok_join32 m1 tk) in TOK. cbn [app pf_mxd] in TOK. stepz. apply (tok_split32 _ tk) in TOK. cbn [app pf_mxd] in TOK.

assert (JOIN : forall (m2' : word -> option byte) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (ja jb jc : list byte),
rw_cells rsegs m2' tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7); C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
wmono rsegs m m2' -> munch [(bv_unsigned sp - 144, bv_unsigned sp); (tk, tk + 72); (LOCCELL, LOCCELL + 8)] m m2' ->
stk rsegs m2' lo (bv_unsigned sp + -144) -> rw_cells rsegs m2' (490496 - 164) [C4 errv] -> rw_cells rsegs m2' 622440 [C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m2' (bv_unsigned sp + -144) [CB 24 ja; C4 (Z_to_bv 64 0); CB 3 jb; C1 (Z_to_bv 8 1); CB 8 jc; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m2' (490496 - 48) [C8 (Z_to_bv 64 GLOBLOC)] -> mem_inv rsegs m2' ->
evt rsegs (RZ rsegs md T)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 490496) xt0 xt1 xt2 (Z_to_bv 64 tk) (Z_to_bv 64 LC_GLOBAL) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
s2 (Z_to_bv 64 lenr) s4 (Z_to_bv 64 sb) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x21d10) fc None m2' (seg_rom rsegs))).
2:{
destruct MODE as [(Elr & _) | (Elr & SPle & (str0 & Ep & NONUL) & SLK & PAD)].
-  subst lenr. step. if_truex. step. if_truex. eapply JOIN; eassumption.
-
subst lenr. replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) in JOIN |- * by (apply bv_eq; reflexivity).
step. if_lit true. step. if_lit false. step. step.
assert (STRZ : bytes_at rsegs m2 (bv_unsigned (Z_to_bv 64 sb)) (str0 ++ Z_to_bv 8 0 :: slack)).
{ rewrite unsigned_lit by lia. unstash STR.
assert (CAT : bytes_at rsegs m sb (payload ++ slack)) by (apply bytes_at_app; split; [exact STR | rewrite PLEN; exact SLK]).
pose proof (bytes_at_bound _ _ _ _ CAT) as CB0. rewrite length_app in CB0.
subst payload. rewrite <- app_assoc in CAT. cbn [app pf_mxd] in CAT.
eapply bytes_at_transport; [exact CAT | exact MU |]. cbn [disjoint_from pf_mxd]. unfold LOCCELL. rewrite !length_app in *. cbn [length pf_mxd] in *. lia. }
assert (PADZ : (- (bv_unsigned (Z_to_bv 64 sb) + Z.of_nat (length str0) + 1)) mod 8 <= Z.of_nat (length slack)).
{ rewrite unsigned_lit by lia. subst payload. rewrite length_app in PLEN. cbn [length pf_mxd] in PLEN.
replace (sb + Z.of_nat (length str0) + 1) with (sb + len) by lia. exact PAD. }
eapply evt_cut; [eapply UgLo.strlen_spec; [exact STRZ | exact NONUL | exact PADZ | exact MI1] |].
intros ms3 (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & _).
replace (ret_pc (Z_to_bv 64 0x21d08)) with (Z_to_bv 64 0x21d08) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (ELEN : Z.of_nat (length str0) = len - 1) by (subst payload; rewrite length_app in PLEN; cbn [length pf_mxd] in PLEN; lia).
rewrite ELEN.
Local Ltac xport3 H MU WM := eapply rw_cells_transport in H; [| exact MU | exact WM | exact I].
xport3 TOK MU3 WM3. xport3 FR MU3 WM3. xport3 LCK MU3 WM3. xport3 ERR MU3 WM3. xport3 LOC1 MU3 WM3.
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -144)) by (eapply stk_transport; [exact ST1 | exact MU3 | exact WM3 | intros z Hz; left; exact I]).
assert (MU03 : munch [(bv_unsigned sp - 144, bv_unsigned sp); (tk, tk + 72); (LOCCELL, LOCCELL + 8)] m m3).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU3]]; intros z Hz; cbn in Hz |- *; clear - Hz; tauto.    }
pose proof (wmono_trans _ _ _ _ WM WM3) as WM03.
step. rewrite (unsigned_lit (len - 1)) by lia.
replace (Z.shiftr (len - 1) 31) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
step. if_lit false.
eapply JOIN; [exact TOK | exact WM03 | exact MU03 | exact ST3 | exact ERR | exact LCK | exact FR | exact LOC1 | exact MI3]. }
clear TOK WM MU ST1 ERR LCK FR LOC1 MI1.
intros m2' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 ja jb jc TOK WM MU ST1 ERR LCK FR LOC1 MI1.
clear m2. rename m2' into m2.
step. step.

assert (LOCcs : forall a, LOCCELL <= a < LOCCELL + 8 -> hl_client_static S4L a /\ ~ s4_volatile a).
{ intros a Ha. unfold LOCCELL in Ha. cbn [hl_client_static S4L pf_mxd]. unfold s4_client_static, s4_volatile. lia. }
apply evt_RZ_done.
assert (HPc : HEAPx A (TBS ++ LBc) m2 md).
{ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI1].
eapply (frame_writes_okx HIx); [exact HP | exact MU | | clia].
apply Forall_cons; [left; cbn [fst snd pf_mxd]; clia|].
apply Forall_cons; [right; left; exists tk, 72; split; [exact INtk | cbn; lia] |].
apply Forall_cons; [right; right; right; cbn [fst snd pf_mxd]; intros z Hz; exact (proj1 (LOCcs z Hz)) | apply Forall_nil]. }

assert (HPRX2 : heap_presx S4L xloc LBc (bv_unsigned sp) m m2).
{ eapply heap_presx_of_munchx; [exact MU | exact WM |].
eapply (client_outsidex HIx xloc); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd pf_mxd]; clia|].
apply Forall_cons; [right; left; exists tk, 72; cbn [fst snd pf_mxd]; split; [exact INtk|]; split; [| lia] |].
{ intros Hin. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite ETBS, map_app in ND. cbn [map app blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. cbn [In app pf_mxd]. right. rewrite ?map_app.
first [ apply in_or_app; right; exact (in_map blk_addr _ _ Hin) | match goal with |- ?g => idtac g end; fail ]. }
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd hl_img_lo hl_img_hi S4L pf_mxd]. intros z Hz. split; [right; exact Hz | unfold LOCCELL in Hz; lia]. }
rename MU into MU0. rename WM into WM0.
unstash TSK. eapply tstack_transport in TSK; [| exact MU0 | exact WM0 | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; unfold LOCCELL; cbn; lia].
eapply DUP; [exact HPc | rewrite unsigned_lit by lia; exact ST1 | clia | rewrite unsigned_lit by lia; cbn [hl_stack S4L pf_mxd]; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia | exact ERR | reflexivity | rewrite unsigned_lit by lia; reflexivity |].
intros ms3 m3 md3 A3 d errv3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs hl_tp S4L pf_mxd] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in HPR3 by lia.

apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LCK; [| right; left; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L pf_mxd] in LCK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LOC1; [| right; left; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L pf_mxd] in LOC1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR3 INq) in TSK; [| cbn [length]; rewrite repeat_length; lia]. cbn [hl_segs S4L pf_mxd] in TSK.
assert (HPRX3 : heap_presx S4L xloc LBc (bv_unsigned sp) m m3).
{ eapply heap_presx_trans; [exact HPRX2|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }

assert (QPB : forall a n, In (a, n) ((q, (32 * mxd)) :: pbs) -> In (a, n) (TBS ++ LBc) /\ a <> tk).
{ intros a n Hin. split.
- rewrite ETBS; cbn. destruct Hin as [E|Hin]; [right; left; exact E | right; right; apply in_or_app; left; exact Hin].
- intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite ETBS in ND. cbn [map app blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. pose proof (in_map blk_addr _ _ Hin) as Hm. cbn [map blk_addr fst pf_mxd] in Hm.
cbn [In pf_mxd]. rewrite map_app. destruct Hm as [E|Hm]; [left; exact E | right; apply in_or_app; left; exact Hm]. }
assert (AG3 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m3).
{ eapply agree_on_trans.
- eapply agree_of_munch; [exact MU0 | exact WM0 |]. intros a n Hin. destruct (QPB a n Hin) as [HinL Hne].
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne).
pose proof (heap_blk_img S4L HIx _ _ _ _ a n HP HinL) as Hi. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hi.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _ & _ & Hhi & _). unfold LOCCELL. cbn. (clear - LO LOS H Hi Hhi; clia).
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros [a n] Hb; exact (proj1 (QPB a n Hb))]. }
destruct OUT3 as [(-> & -> & HP3) | (Hd & (junk3 & BLK3) & HP3)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L pf_mxd] in MI3.
pose proof (munch_refl [(tk, tk + 72)] m3) as MU3. pose proof (wmono_refl rsegs m3) as WM3.
assert (TKnot : ~ In (tk, 72) LBc).
{ intros Hin. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite ETBS, map_app in ND. cbn [map app blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. cbn [In app pf_mxd]. right. rewrite ?map_app.
apply in_or_app; right. exact (in_map blk_addr _ _ Hin). }
reenter MOK3.
step. step. if_false. step.
eapply evt_cut; [eapply ERRNO; reflexivity|]. intros ms4 ->.
replace (ret_pc (Z_to_bv 64 0x21d24)) with (Z_to_bv 64 0x21d24) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof ERR3 as ERRx. replace (490496 - 164) with 490332 in ERRx by reflexivity. unfold ENOMEMv in ERRx.
step. if_any. step. step. if_any.
step. norm_sx32. step. step. if_false. step. step. step. stepz.
clear ERRx.
eapply (pe_epilogue _ _ [CB 24 _; C4 _; CB 3 _; C1 _; CB 8 _] sv); [exact FR | reflexivity | lia | lia | exact RAE |].

apply Kret. unfold pe_post_g, PE_FRAME. cbn [pf_spf pf_tk pe_ra pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pf_md pf_mxd pf_fl].
replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
exists mf, A3, gp, 0, (Z_to_bv 64 12), [], ((tk, 72) :: (q, (32 * mxd)) :: pbs ++ concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)))), [] end.
split; [apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf]|].
split; [exact VM3|].
lazymatch type of FR with rw_cells _ ?mfx _ ?CS =>
set (mf := mfx) in *;
pose proof (stk_release rsegs mf lo (bv_unsigned sp + -144) CS ST3 FR ltac:(lia)) as STx end.
change (Z.of_nat (cells_size _)) with 144 in STx. replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) in STx by lia.
split; [exact STx|]. split; [exact ERR3|]. split; [exact LOC1|].
split.
{ eapply heap_presx_trans; [exact HPRX3|]. eapply heap_presx_of_munchx; [exact MU3 | exact WM3|].
eapply (client_outsidex HIx xloc); [exact HP3 | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. right; left. exists tk, 72. cbn [fst snd pf_mxd]. split; [exact INtk|]. split; [exact TKnot | lia]. }
replace (concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)))) with (@nil blk) by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity). rewrite app_nil_r.
split.
{ assert (HPf : HEAPx A3 (TBS ++ LBc) mf md3).
{ eapply (heap_frame S4L HIx); [exact HP3 | | exact WM3 | exact MI3].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3 MU3). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd pf_mxd].
right; left. exists tk, 72. split; [exact INtk | lia]. }
eapply (heap_perm S4L HIx); [exact HPf | rewrite ETBS; perm]. }
split.
2:{ split; [left; split; reflexivity|].

unstash JCG0.
assert (G2 : jc_glob_P m2).
{ eapply jc_glob_P_munch; [exact JCG0 | exact MU0 | exact WM0 |].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd pf_mxd]; unfold LOCCELL; unfold_consts_goal; lia. }
pose proof (jc_glob_P_pres _ _ _ _ ltac:(eapply heap_pres_weaken; [exact HPR3 | apply Z.le_refl | intros b Hb; exact Hb]) G2) as G3.
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Hitk. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hitk.
eapply jc_glob_P_outside; [exact G3 | exact MU3 | exact WM3 |].
apply Forall_cons; [cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
unstash PB.
exists q, pb, 0, pbs, (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)), (TS (wz 0) (wz 0) (wz 0) (Z_to_bv 64 16) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero, app_nil_r; reflexivity|]. split; [cbn [length]; rewrite repeat_length; lia|]. split; [lia|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
assert (AGp : agree_on rsegs ((q, (32 * mxd)) :: pbs) m mf).
{ eapply agree_on_trans; [| eapply agree_of_munch; [exact MU3 | exact WM3 |]; intros a n Hin;
assert (HinL : In (a, n) (TBS ++ LBc)) by (rewrite ETBS; cbn; destruct Hin as [E|Hin]; [right; left; exact E | right; right; apply in_or_app; left; exact Hin]);
assert (Hne : a <> tk) by (intros ->; pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND; rewrite ETBS in ND; cbn [map app blk_addr fst pf_mxd] in ND;
apply List.NoDup_cons_iff in ND as [Hni _]; apply Hni; pose proof (in_map blk_addr _ _ Hin) as Hm; cbn [map blk_addr fst pf_mxd] in Hm;
cbn [In pf_mxd]; rewrite map_app; destruct Hm as [E|Hm]; [left; exact E | right; apply in_or_app; left; exact Hm]);
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne); pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _); cbn; lia ].
eapply agree_on_trans.
- eapply agree_of_munch; [exact MU0 | exact WM0 |]. intros a n Hin.
assert (HinL : In (a, n) (TBS ++ LBc)).
{ rewrite ETBS; cbn. destruct Hin as [E|Hin]; [right; left; exact E | right; right; apply in_or_app; left; exact Hin]. }
assert (Hne : a <> tk).
{ intros ->. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite ETBS in ND. cbn [map app blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. pose proof (in_map blk_addr _ _ Hin) as Hm. cbn [map blk_addr fst pf_mxd] in Hm.
cbn [In pf_mxd]. rewrite map_app. destruct Hm as [E|Hm]; [left; exact E | right; apply in_or_app; left; exact Hm]. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne).
pose proof (heap_blk_img S4L HIx _ _ _ _ a n HP HinL) as Hi. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hi.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _ & _ & Hhi & _). unfold LOCCELL. cbn. clia.
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity |].
intros b Hb; rewrite ETBS; cbn. destruct Hb as [E|Hb]; [right; left; exact E | right; right; apply in_or_app; left; exact Hb]. }
split; [eapply pbuf_agree; [exact PB | exact AGp | intros b Hb; right; exact Hb]|].
split; [exact Hpb|].
split; [eapply (tstack_transport rsegs); [exact TSK | exact MU3 | exact WM3 | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; cbn; lia]|].
split.
+ intros i li Hli Hile. assert (i = 0%nat) as -> by lia. cbn in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. destruct i as [|i]; [lia|]. change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. apply lvl_zero_clean.
-
assert (INd : In (d, 48) ((d, 48) :: TBS ++ LBc)) by (left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ d 48 HP3 INd) as (_ & Hdal & Hd0 & Hdhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi.
pose proof (heap_blk_img S4L HIx _ _ _ _ d 48 HP3 INd) as Himg_d. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_d.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L pf_mxd] in MI3.
assert (TKnot : ~ In (tk, 72) LBc).
{ intros Hin. pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. rewrite ETBS, map_app in ND. cbn [map app blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. cbn [In app pf_mxd]. right. rewrite ?map_app.
apply in_or_app; right. exact (in_map blk_addr _ _ Hin). }
assert (Dnot : ~ In (d, 48) (TBS ++ LBc)) by (eapply (fresh_not_in S4L HIx); exact HP3).
reenter MOK3.
step. step. if_truex.
step. step. step. step. step.
apply evt_RZ_done.
eapply NEWL; [exact HP3 | exact INd | exact BLK3 | exact LCK | rewrite unsigned_lit by lia; exact ST3 | clia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia | exact ERR3 | reflexivity
| rewrite unsigned_lit by lia; reflexivity |].
intros ms4 m4 r4 junk4 RS4 ST4 HPR4 BLK4 LCK4 ERR4 HP4 R4. open_ret RS4. cbn [hl_segs hl_tp S4L pf_mxd] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST4 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in HPR4 by lia.
rewrite lb_remove_head in HPR4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in LOC1; [| right; left; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L pf_mxd] in LOC1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR4 INq) in TSK; [| cbn [length]; rewrite repeat_length; lia]. cbn [hl_segs S4L pf_mxd] in TSK.
assert (HPRX4 : heap_presx S4L xloc LBc (bv_unsigned sp) m m4).
{ eapply heap_presx_trans; [exact HPRX3|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }
assert (AG4 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m4).
{ eapply agree_on_trans; [exact AG3|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR4 | reflexivity | intros [a n] Hb; exact (proj1 (QPB a n Hb))]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L pf_mxd] in MI4.
reenter MOK4.
destruct R4 as [-> | ->].
+
step. if_truex. step. step.
eapply evt_cut; [eapply USE; [exact LOC1 | unfold GLOBLOC; lia | lia | reflexivity | exact MI4] |].
intros ms5 (m5 & b1x & b2x & b3x & b4x & -> & MU5 & WM5 & MI5 & LOC5).
replace (ret_pc (Z_to_bv 64 0x21d74)) with (Z_to_bv 64 0x21d74) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_new GLOBLOC d) with d in LOC5
by (unfold usl_new, LC_GLOBAL; destruct (Z.eqb_spec d 0); [lia|]; destruct (Z.eqb_spec d (2^64 - 1)); [lia|]; reflexivity).
xport TOK MU5 WM5. xport FR MU5 WM5. xport ERR4 MU5 WM5.
eapply tstack_transport in TSK; [| exact MU5 | exact WM5 | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; unfold LOCCELL; cbn; lia].
assert (ST5 : stk rsegs m5 lo (bv_unsigned sp + -144)).
{ eapply stk_transport; [exact ST4 | exact MU5 | exact WM5 |]. intros z Hz. left. unfold LOCCELL. cbn. lia. }
assert (HPRX5 : heap_presx S4L xloc LBc (bv_unsigned sp) m m5).
{ eapply heap_presx_trans; [exact HPRX4|]. eapply heap_presx_of_munchx; [exact MU5 | exact WM5|].
eapply (client_outsidex HIx xloc); [exact HP4 | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. right; right; right. cbn [fst snd hl_img_lo hl_img_hi S4L pf_mxd]. intros z Hz. split; [right; exact Hz | unfold LOCCELL in Hz; lia]. }
assert (HP5 : HEAPx A3 ((d, 48) :: TBS ++ LBc) m5 md3).
{ eapply (heap_frame S4L HIx); [exact HP4 | | exact WM5 | exact MI5].
eapply (frame_writes_okx HIx); [exact HP4 | exact MU5 | | clia].
apply Forall_cons; [right; right; right; cbn [fst snd pf_mxd]; intros z Hz; exact (proj1 (LOCcs z Hz)) | apply Forall_nil]. }
assert (AG5 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m5).
{ eapply agree_on_trans; [exact AG4|]. eapply agree_of_munch; [exact MU5 | exact WM5 |]. intros a n Hin. destruct (QPB a n Hin) as [HinL Hne].
pose proof (heap_blk_img S4L HIx _ _ _ _ a n HP HinL) as Hi. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hi.
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _). unfold LOCCELL. cbn. lia. }
pose proof MU5 as MU5x. pose proof WM5 as WM5x. stash MU5x. stash WM5x.
clear MU5 WM5 MI4. unfold LOCCELL in LOC5.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m5) as MU6. pose proof (wmono_refl rsegs m5) as WM6.
stepz. step. norm_sx32. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m6 := mc) in * end.
eapply tstack_transport in TSK; [| exact MU6 | exact WM6 | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; cbn; lia].
assert (ST6 : stk rsegs m6 lo (bv_unsigned sp + -144)).
{ first [ exact ST5 | eapply stk_transport; [exact ST5 | exact MU6 | exact WM6 |]; intros z Hz; left; cbn; lia ]. }
assert (AG6 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m6).
{ eapply agree_on_trans; [exact AG5|]. eapply agree_of_munch; [exact MU6 | exact WM6 |]. intros a n Hin. destruct (QPB a n Hin) as [HinL Hne].
pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _ & _ & Hhi & _). cbn. clia. }
assert (HP6 : HEAPx A3 ((d, 48) :: TBS ++ LBc) m6 md3).
{ eapply (heap_frame S4L HIx); [exact HP5 | | exact WM6 | exact MI5].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP5 MU6). apply Forall_cons; [left; cbn [fst snd pf_mxd]; clia | apply Forall_nil]. }
assert (HPRX6 : heap_presx S4L xloc LBc (bv_unsigned sp) m m6).
{ eapply heap_presx_trans; [exact HPRX5|]. eapply heap_presx_of_munchx; [exact MU6 | exact WM6|].
eapply (client_outsidex HIx xloc); [exact HP5 | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [left; cbn [fst snd pf_mxd]; clia | apply Forall_nil]. }
apply evt_RZ_done.
replace (Z_to_bv 64 sb) with (Z_to_bv 64 (sb + 0)) by (f_equal; lia).
unstash PB. unstash STR.
lazymatch type of FR with rw_cells _ _ _ [_; CB 16 ?a; _; CB 3 ?b; _; CB 8 ?c; _; _; _; _; _; _; _; _; _; _; _; _; _] =>
eapply (Kloop d q m6 md3 A3 pb pbs a (Z_to_le_bytes 4 0 ++ b) c errv3) end.
*  unfold PE_STATIC, PE_FRAME, LENR_OK; cbn [pf_spf pf_len pf_lenr pf_sb pf_md pf_mxd pf_fl]. unfold_consts_goal. repeat split; try (clear - LO LOS SPA HT SP63 PLEN LEN SB0 SBL LENROK MXB; lia); try exact I.
all: rewrite <- Zplus_mod_idemp_l, SPA; reflexivity.
*  split.
-- unfold PE_CORE, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [cbn [length]; rewrite repeat_length; lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote Z.of_nat pf_mxd]; exact TOK|].
split; [eapply pbuf_agree; [exact PB | exact AG6 | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|]. split; [exact TSK|]. unfold pe_frame; cbn [pe_s11 pe_s10 pe_s9 pe_s8 pe_s7 pe_s6 pe_s5 pe_s4 pe_s3 pe_s2 pe_s1 pe_s0 pe_ra pf_mxd]. rewrite nbw_zero4, skipn4_zero4. exact FR.
-- unfold PE_REST, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj t_objs t_objbs ts_choff pf_len pf_tk pf_spf pf_sb pf_md pf_mxd pf_fl].
split.
{ eapply (heap_perm S4L HIx); [exact HP6|]. unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_tk pf_md pf_mxd pf_fl].
replace (concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)))) with (@nil blk) by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity). rewrite ETBS. perm. }
split.
{ intros i li Hli. unfold lvl_cur.
destruct i as [|i].
- cbn in Hli. injection Hli as <-. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_reset Nat.ltb Nat.eqb Nat.leb pf_mxd].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|]. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
- change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli. pose proof (nth_error_Some_length Hli) as Hi. rewrite repeat_length in Hi.
apply nth_error_repeat_some in Hli. subst li. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_zero pf_mxd].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|].
replace (S i <? 0)%nat with false by reflexivity. replace (S i =? 0)%nat with false by reflexivity. apply lvl_zero_clean. }
split; [reflexivity|].
split; [exact ST6|]. split; [exact ERR4|].
split.
{ destruct PLOC as [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. apply bytes_at_nil. lia.
- eapply (heap_presx_bytes_at S4L); [exact HPRX6 | exact STR |]. rewrite PLEN. unfold PE_FRAME in PL.
destruct PL as [SPle | (bb & Hbb & Hb1 & Hb2)]; [left; lia | right; right; exists bb; split; [exact Hbb | lia]]. }
split; [exact PLEN|].
split; [unfold payload_loc; cbn [pf_spf pf_sb pf_len pf_mxd]; destruct PLOC as [L0 | [SPle | (bb & Hbb & Hb12)]];
[left; exact L0 | right; left; exact SPle | right; right; exists bb; split; [right; exact Hbb | exact Hb12]]|].
split; [unfold PE_FRAME; apply heap_presx_refl|]. split; [apply model_vm_only_refl|].

unstash JCG0.
assert (G2 : jc_glob_P m2).
{ eapply jc_glob_P_munch; [exact JCG0 | exact MU0 | exact WM0 |].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd pf_mxd]; unfold LOCCELL; unfold_consts_goal; lia. }
pose proof (jc_glob_P_pres _ _ _ _ ltac:(eapply heap_pres_weaken; [exact HPR3 | apply Z.le_refl | intros b Hb; exact Hb]) G2) as G3.
pose proof (jc_glob_P_pres _ _ _ _ HPR4 G3) as G4.
eapply jc_glob_P_munch; [eapply jc_glob_P_munch; [exact G4 | exact MU5x | exact WM5x |] | exact MU6 | exact WM6 |];
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd pf_mxd]; unfold LOCCELL; unfold_consts_goal; lia.
* exact VM3.
* exact HPRX6.
* exact LOC5.
* lia.
+
pose proof (munch_refl [(tk, tk + 72)] m4) as MU7. pose proof (wmono_refl rsegs m4) as WM7.
step. if_false. step. step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m7 := mc) in * end.
assert (HP7 : HEAPx A3 ((d, 48) :: TBS ++ LBc) m7 md3).
{ eapply (heap_frame S4L HIx); [exact HP4 | | exact WM7 | exact MI4].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP4 MU7). apply Forall_cons; [| apply Forall_nil]. cbn [fst snd pf_mxd].
right; left. exists tk, 72. split; [right; exact INtk | lia]. }
assert (ST7 : stk rsegs m7 lo (bv_unsigned sp + -144)).
{ first [ exact ST4 | eapply stk_transport; [exact ST4 | exact MU7 | exact WM7 |]; intros z Hz; left; cbn; lia ]. }
assert (AG7 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m7).
{ eapply agree_on_trans; [exact AG4|]. eapply agree_of_munch; [exact MU7 | exact WM7 |]. intros a n Hin. destruct (QPB a n Hin) as [HinL Hne].
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ a n tk 72 HP HinL INtk Hne). pose proof (heap_blk S4L HIx _ _ _ _ a n HP HinL) as (Hn0 & _). cbn. lia. }
assert (HPRX7 : heap_presx S4L xloc LBc (bv_unsigned sp) m m7).
{ eapply heap_presx_trans; [exact HPRX4|]. eapply heap_presx_of_munchx; [exact MU7 | exact WM7|].
eapply (client_outsidex HIx xloc); [exact HP4 | intros b Hb; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [| apply Forall_nil]. right; left. exists tk, 72. cbn [fst snd pf_mxd]. split; [right; exact INtk|]. split; [exact TKnot | lia]. }
eapply tstack_transport in TSK; [| exact MU7 | exact WM7 | intros j Hj; cbn [length] in Hj; rewrite repeat_length in Hj; cbn; lia].

assert (G7 : jc_glob_P m7).
{ unstash JCG0.
assert (G2 : jc_glob_P m2).
{ eapply jc_glob_P_munch; [exact JCG0 | exact MU0 | exact WM0 |].
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd pf_mxd]; unfold LOCCELL; unfold_consts_goal; lia. }
pose proof (jc_glob_P_pres _ _ _ _ ltac:(eapply heap_pres_weaken; [exact HPR3 | apply Z.le_refl | intros b Hb; exact Hb]) G2) as G3.
pose proof (jc_glob_P_pres _ _ _ _ ltac:(eapply heap_pres_weaken; [exact HPR4 | apply Z.le_refl | intros b Hb; exact Hb]) G3) as G4.
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Hitk. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Hitk.
eapply jc_glob_P_outside; [exact G4 | exact MU7 | exact WM7 |].
apply Forall_cons; [cbn [fst snd pf_mxd]; lia | apply Forall_nil]. }
clear MU7 WM7.
apply evt_RZ_done.
eapply FREEL; [exact HP7 | left; reflexivity | rewrite unsigned_lit by lia; exact ST7 | clia | rewrite unsigned_lit by lia; cbn [hl_stack S4L pf_mxd]; lia
| rewrite unsigned_lit by lia; rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | rewrite unsigned_lit by lia; lia | exact ERR4 | reflexivity
| rewrite unsigned_lit by lia; reflexivity |].
intros ms8 m8 md8 A8 r8 RS8 VM8 ST8 HPR8 ERR8 HP8. open_ret RS8. cbn [hl_segs hl_tp S4L pf_mxd] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST8 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in HPR8 by lia.
rewrite lb_remove_head in HPR8, HP8.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR8) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR8) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR8) in LOC1; [| right; left; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L pf_mxd] in LOC1.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR8 INq) in TSK; [| cbn [length]; rewrite repeat_length; lia]. cbn [hl_segs S4L pf_mxd] in TSK.
pose proof (heap_model_ok _ _ _ _ _ _ HP8) as MOK8.
reenter MOK8.
step. step.
eapply (pe_epilogue _ _ [CB 24 _; C4 _; CB 3 _; C1 _; CB 8 _] sv); [exact FR | reflexivity | lia | lia | exact RAE |].
apply Kret. unfold pe_post_g, PE_FRAME. cbn [pf_spf pf_tk pe_ra pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pf_md pf_mxd pf_fl].
replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
exists m8, A8, gp, 0, errv3, [], ((tk, 72) :: (q, (32 * mxd)) :: pbs ++ concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)))), [].
split; [apply ret_statew_intro; [apply fsaved_refl | intros Hf; exact Hf]|].
split; [eapply model_vm_only_trans; [exact VM3 | exact VM8]|].
lazymatch type of FR with rw_cells _ _ _ ?CS =>
pose proof (stk_release rsegs m8 lo (bv_unsigned sp + -144) CS ST8 FR ltac:(lia)) as STx end.
change (Z.of_nat (cells_size _)) with 144 in STx. replace (bv_unsigned sp + -144 + 144) with (bv_unsigned sp) in STx by lia.
split; [exact STx|]. split; [exact ERR8|]. split; [exact LOC1|].
split.
{ eapply heap_presx_trans; [exact HPRX7|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR8 | lia | intros b Hb; apply in_or_app; right; exact Hb]. }
replace (concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)))) with (@nil blk) by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity). rewrite app_nil_r.
split; [eapply (heap_perm S4L HIx); [exact HP8 | rewrite ETBS; perm]|].
split.
2:{ split; [left; split; reflexivity|].
exact (jc_glob_P_pres _ _ _ _ ltac:(eapply heap_pres_weaken; [exact HPR8 | apply Z.le_refl | intros b Hb; exact Hb]) G7). }
exists q, pb, 0, pbs, (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)), (TS (wz 0) (wz 0) (wz 0) (Z_to_bv 64 16) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero, app_nil_r; reflexivity|]. split; [cbn [length]; rewrite repeat_length; lia|]. split; [lia|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
assert (AG8 : agree_on rsegs ((q, (32 * mxd)) :: pbs) m m8).
{ eapply agree_on_trans; [exact AG7|]. eapply (agree_of_heap_pres rsegs S4L); [exact HPR8 | reflexivity | intros [a n] Hb; exact (proj1 (QPB a n Hb))]. }
unstash PB.
split; [eapply pbuf_agree; [exact PB | exact AG8 | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|]. split; [exact TSK|].
split.
-- intros i li Hli Hile. assert (i = 0%nat) as -> by lia. cbn in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
-- intros i li Hli Hlt. destruct i as [|i]; [lia|]. change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. apply lvl_zero_clean.
Qed.
End PeEntry.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition cur_ss (ts : tstate) : Z :=
match nth_error (t_levels ts) (t_depth ts) with Some l => tl_ss l | None => 0 end.

Definition mbase (pf : pe_fix) (ts : tstate) : nat := (16 * Z.to_nat (pf_len pf - t_co ts))%nat.
Definition mloop (pf : pe_fix) (ts : tstate) : nat := (mbase pf ts + 15)%nat.
Definition mredo (pf : pe_fix) (ts : tstate) : nat := (mbase pf ts + rank (cur_st ts) (cur_ss ts))%nat.
Definition mbrk (pf : pe_fix) (ts : tstate) : nat := mbase pf ts.

#[using="Type"] Lemma rank_le : forall st ss, (rank st ss <= 14)%nat.
Proof. intros st ss. unfold rank, base_rank. repeat (destruct (zin _ _)); destruct (st =? ST_eatws); lia. Qed.

Section PeKont.
Variable HIx : heap_iface S4L.

Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Definition LB0 : list blk := (pf_newl pf, 48) :: LBc.

Definition NUMC (ts : tstate) (m : word -> option byte) : Prop :=
cur_st ts = ST_number -> pbufc rsegs m (t_pbs ts) (t_pb ts) [].

Definition SPV (x : tscal) : Z := bv_unsigned (ts_stpos x) mod 2^32.
Definition SPOK (ts : tstate) (k : Z) : Prop :=
(zin (cur_st ts) [ST_null; ST_boolean; ST_inf] = true -> SPV (t_x ts) <= t_co ts + k) /\
(zin (cur_st ts) [ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = true -> 0 <= bv_unsigned (ts_stpos (t_x ts)) <= 3).

#[using="Type"] Lemma tdepth_ok_same : forall ts ts',
t_levels ts' = t_levels ts -> t_depth ts' = t_depth ts -> t_objs ts' = t_objs ts ->
tdepth_ok ts -> tdepth_ok ts'.
Proof.
intros ts ts' E1 E2 E3 [A B]. unfold tdepth_ok, cur_st in *. rewrite E1, E2, E3. split; [exact A | exact B].
Qed.

#[using="Type"] Lemma tdepth_ok_upd : forall ts l st' ss' cur' cs' cbs' nm' nbs' co' pb' pbs' x' obj' objs' objbs',
tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l ->
odep cs' <= Z.max (odep (tl_cs l)) 1 -> (t_depth ts <= 31)%nat ->
zin st' [ST_array_add; ST_ovadd] = false ->
tdepth_ok (TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' ss' cur' cs' cbs' nm' nbs')) co' pb' pbs' x' obj' objs' objbs').
Proof.
intros ts l st' ss' cur' cs' cbs' nm' nbs' co' pb' pbs' x' obj' objs' objbs' [A B] Hl Hd Hdep Hst.
pose proof (nth_error_Some_length Hl) as LT.
split.
- cbn [t_levels pf_mxd]. intros i li Hi. destruct (Nat.eq_dec i (t_depth ts)) as [->|NE].
+ rewrite nth_error_lupd_eq in Hi by exact LT. injection Hi as <-. cbn [tl_cs pf_mxd]. pose proof (A _ _ Hl). pose proof (odep_nonneg (tl_cs l)). lia.
+ rewrite nth_error_lupd_neq in Hi by (intros E; apply NE; symmetry; exact E). exact (A _ _ Hi).
- unfold cur_st. cbn [t_levels t_depth t_objs pf_mxd]. rewrite nth_error_lupd_eq by exact LT. cbn [tl_st pf_mxd]. rewrite Hst. discriminate.
Qed.

#[using="Type"] Lemma tdepth_ok_absorb : forall ts l st' ss' cur' cs' cbs' nm' nbs' co' pb' pbs' x' obj' objs' objbs',
tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l ->
zin (tl_st l) [ST_array_add; ST_ovadd] = true ->
odep cs' <= Z.max (odep (tl_cs l)) (1 + odep (t_objs ts)) ->
zin st' [ST_array_add; ST_ovadd] = false ->
tdepth_ok (TST (t_depth ts) (lupd (t_levels ts) (t_depth ts) (TL st' ss' cur' cs' cbs' nm' nbs')) co' pb' pbs' x' obj' objs' objbs').
Proof.
intros ts l st' ss' cur' cs' cbs' nm' nbs' co' pb' pbs' x' obj' objs' objbs' [A B] Hl Hst Hdep Hst'.
pose proof (nth_error_Some_length Hl) as LT.
assert (OB : odep (t_objs ts) + Z.of_nat (t_depth ts) <= 31) by (apply B; unfold cur_st; rewrite Hl; exact Hst).
split.
- cbn [t_levels pf_mxd]. intros i li Hi. destruct (Nat.eq_dec i (t_depth ts)) as [->|NE].
+ rewrite nth_error_lupd_eq in Hi by exact LT. injection Hi as <-. cbn [tl_cs pf_mxd]. pose proof (A _ _ Hl). lia.
+ rewrite nth_error_lupd_neq in Hi by (intros E; apply NE; symmetry; exact E). exact (A _ _ Hi).
- unfold cur_st. cbn [t_levels t_depth t_objs pf_mxd]. rewrite nth_error_lupd_eq by exact LT. cbn [tl_st pf_mxd]. rewrite Hst'. discriminate.
Qed.

#[using="Type"] Lemma odep_absorb_arr : forall kids o, odep (Some (Sarr (kids ++ [o]))) <= Z.max (odep (Some (Sarr kids))) (1 + odep o).
Proof. intros kids o. cbn [odep pf_mxd]. rewrite !sdepth_Sarr, okmax_app, okmax_single. pose proof (okmax_nonneg kids). pose proof (odep_nonneg o). lia. Qed.
#[using="Type"] Lemma odep_absorb_obj : forall kids kids' o,
okmax kids' <= Z.max (okmax kids) (odep o) -> odep (Some (Sobj kids')) <= Z.max (odep (Some (Sobj kids))) (1 + odep o).
Proof. intros kids kids' o H. cbn [odep pf_mxd]. rewrite !sdepth_Sobj. pose proof (okmax_nonneg kids). pose proof (okmax_nonneg kids'). pose proof (odep_nonneg o). lia. Qed.

#[using="Type"] Lemma tdepth_ok_push : forall ts l lnew st' ss' co' pb' pbs' x' obj' objs' objbs',
tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l ->
(S (t_depth ts) < length (t_levels ts))%nat -> (length (t_levels ts) <= 32)%nat  ->
tl_cs lnew = None -> zin (tl_st lnew) [ST_array_add; ST_ovadd] = false ->
tdepth_ok (TST (S (t_depth ts))
(lupd (lupd (t_levels ts) (t_depth ts) (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (S (t_depth ts)) lnew)
co' pb' pbs' x' obj' objs' objbs').
Proof.
intros ts l lnew st' ss' co' pb' pbs' x' obj' objs' objbs' [A B] Hl LT2 L32 Hcs Hst.
pose proof (nth_error_Some_length Hl) as LT.
split.
- cbn [t_levels pf_mxd]. intros i li Hi. destruct (Nat.eq_dec i (S (t_depth ts))) as [->|NE].
+ rewrite nth_error_lupd_eq in Hi by (rewrite lupd_length; exact LT2). injection Hi as <-. rewrite Hcs. cbn [odep pf_mxd]. lia.
+ rewrite nth_error_lupd_neq in Hi by (intros E; apply NE; symmetry; exact E). destruct (Nat.eq_dec i (t_depth ts)) as [->|NE2].
* rewrite nth_error_lupd_eq in Hi by exact LT. injection Hi as <-. cbn [tl_cs pf_mxd]. exact (A _ _ Hl).
* rewrite nth_error_lupd_neq in Hi by (intros E; apply NE2; symmetry; exact E). exact (A _ _ Hi).
- unfold cur_st. cbn [t_levels t_depth t_objs pf_mxd]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact LT2). rewrite Hst. discriminate.
Qed.

#[using="Type"] Lemma tdepth_ok_pop : forall ts l dp lp lres co' pb' pbs' x' obj' objbs',
tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l -> t_depth ts = S dp ->
nth_error (t_levels ts) dp = Some lp -> tl_cs lres = None -> (length (t_levels ts) <= 32)%nat  ->
tdepth_ok (TST dp (lupd (t_levels ts) (S dp) lres) co' pb' pbs' x' obj' (tl_cs l) objbs').
Proof.
intros ts l dp lp lres co' pb' pbs' x' obj' objbs' [A B] Hl Hd Hlp Hres L32.
pose proof (nth_error_Some_length Hl) as LT. rewrite Hd in LT.
split.
- cbn [t_levels pf_mxd]. intros i li Hi. destruct (Nat.eq_dec i (S dp)) as [->|NE].
+ rewrite nth_error_lupd_eq in Hi by exact LT. injection Hi as <-. rewrite Hres. cbn [odep pf_mxd]. lia.
+ rewrite nth_error_lupd_neq in Hi by (intros E; apply NE; symmetry; exact E). exact (A _ _ Hi).
- unfold cur_st. cbn [t_levels t_depth t_objs pf_mxd]. rewrite nth_error_lupd_neq by lia. intros _.
pose proof (A _ _ Hl) as H. rewrite Hd in H. lia.
Qed.

Definition KLOOP (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mloop pf ts < n)%nat ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
cur_st ts <> ST_number -> SPOK ts 0 -> tdepth_ok ts ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_LOOP (t_co ts) x1 gp t0 t1 t2 (Z_to_bv 64 (t_co ts)) a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KREDO (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mredo pf ts < n)%nat ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC ts m -> SPOK ts 0 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_REDO (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KBRK (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KBRK2 (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_BREAK2 (t_co ts) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KOUT : Prop :=
forall (ts : tstate) (LK : list blk) (cop : Z) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW HIx pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_OUT cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KERR : Prop :=
forall (ts : tstate) (LK : list blk) (cop : Z) (e : word) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW HIx pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms rsegs pf PE_ERR cop x1 gp t0 t1 t2 e a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KOUT7 : Prop :=
forall (ts : tstate) (LK : list blk) (cop : Z) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW HIx pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf PE_OUT cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

Definition KERR7 : Prop :=
forall (ts : tstate) (LK : list blk) (cop : Z) (e : word) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW HIx pf q LB0 payload me lo m md A ts LK cb j1 j2 utf sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf PE_ERR cop x1 gp t0 t1 t2 e a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.

#[using="Type"] Lemma KOUT_of_7 : KOUT7 -> KOUT.
Proof. intros K7. unfold KOUT. intros. rewrite <- pe_ms7_26. eapply K7; eassumption. Qed.
#[using="Type"] Lemma KERR_of_7 : KERR7 -> KERR.
Proof. intros K7. unfold KERR. intros. rewrite <- pe_ms7_26. eapply K7; eassumption. Qed.

Definition KALL (n : nat) : Prop := KLOOP n /\ KREDO n /\ KBRK n /\ KBRK2 n.

Definition CASE (st : Z) : Prop :=
forall (n : nat) (ts : tstate) (l : tlevel) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = st ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC ts m -> SPOK ts 0 -> tdepth_ok ts ->
bytes_at rsegs me UTF8REP_ADDR utf8rep ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
CSTR_OK pf payload ->
fsaved F0 F -> frm0 fc ->
(mredo pf ts <= n)%nat -> KALL n -> KOUT7 -> KERR7 ->
realizes rsegs (mkCfg (pe_ms rsegs pf (pe_jt st) (t_co ts) x1 gp t0 t1 t2
(Z_to_bv 64 0) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) a3 a4 a5 a6 a7
(Z_to_bv 64 q) s6 s7 s8 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
End PeKont.

End RC__1.
