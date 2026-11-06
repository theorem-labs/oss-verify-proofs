(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtMn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhHQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb4w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzoi.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qyk8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfOM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGEL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGEL.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TokParseP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Hypothesis USE : uselocale_stmt.
Hypothesis ERRNO : errno_location_stmt.
Hypothesis DUP : duplocale_stmt HIx.
Hypothesis NEWL : newlocale_stmt HIx.
Hypothesis FREEL : freelocale_stmt HIx.
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Hypothesis AADD : jo_array_add_P HIx.
Hypothesis SHRINK : jo_array_shrink_P HIx.
Hypothesis OADD : jo_object_add_P HIx.
Hypothesis NEWO : jo_new_object_P HIx.
Hypothesis NEWA : jo_new_array_P HIx.
Hypothesis HC_null : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_null.
Hypothesis HC_bool : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_boolean.
Hypothesis HC_number : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_number.
Hypothesis HC_inf : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_inf.

Ltac mod16 SPA :=
lazymatch type of SPA with ?b mod 16 = 0 =>
lazymatch goal with |- ?x mod 16 = 0 =>
first [ replace x with (b + (-2) * 16) by lia | replace x with b by lia ];
first [ rewrite Z.mod_add by lia; exact SPA | exact SPA ]
end
end.

#[using="Type"] Lemma tokrep_pres : forall LB SP m m' BS tk,
heap_pres S4L LB SP m m' -> incl BS LB -> tokrep rsegs S4F m BS tk -> tokrep rsegs S4F m' BS tk.
Proof.
intros LB SP m m' BS tk HPR Hi (stack & pb & depth & PBS & levels & x & EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
assert (AG : agree_on rsegs BS m m') by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | exact Hi]).
exists stack, pb, depth, PBS, levels, x. split; [exact EBS|]. split; [exact LEN|]. split; [exact Hd|].
split. { eapply (heap_pres_rw_cells S4L); [exact HPR | exact TOK |]. eapply client_range_block; [apply Hi; rewrite EBS; left; reflexivity | lia | unfold tok_cells; cbn; lia]. }
split. { eapply pbuf_agree; [exact PB | exact AG | rewrite EBS; intros b Hb; right; right; apply in_or_app; left; exact Hb]. }
split; [exact Hpb|].
split. { eapply (tstack_pres' S4L); [exact HPR | apply Hi; rewrite EBS; right; left; reflexivity | lia | exact TS]. }
split; [| exact CLEAN].
intros i l Hl Hi'. eapply lvl_ok_agree; [exact (LOK i l Hl Hi') | exact AG |].
rewrite EBS. intros b Hb. right; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks l).
split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb].
Qed.

Local Ltac if_lit b :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota end.

#[using="USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf"] Lemma tokparse_P_main :
forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LBc : list blk) (sp0 sb lo : Z) (str0 slack : list byte) (errv : word),
HEAPx A LBc m md ->
bytes_at rsegs m sb (str0 ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str0 -> Z.of_nat (length str0) < 2^25 ->
bytes_at rsegs m (sb + Z.of_nat (length str0) + 1) slack ->
(- (sb + Z.of_nat (length str0) + 1)) mod 8 <= Z.of_nat (length slack) ->
sp0 <= sb -> sb + Z.of_nat (length str0) + 1 < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m ->
bytes_at rsegs m JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m lo sp0 -> alloc_ceiling <= lo -> lo <= sp0 - TOKPARSE_STK_P ->
sp0 mod 16 = 0 -> sp0 <= hi_top S4L HIx -> 0 <= sp0 <= 2^62 ->
rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
bv_unsigned ra mod 2 = 0 -> frm0 fc ->
(forall ms' md', tokparse_post S4L HIx S4F tokparse_consts_P ra (wz sp0) gp (wz 0x75e70) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LBc lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra (wz sp0) gp (wz 0x75e70) t0 t1 t2 s0 s1 (wz sb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x21768) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv.
intros HP STR NONUL LEN SLK PAD SPle SBL LOC LCK G UTF GOTF ST LO LOS SPA HT SPR ERR RAE FRM K.
unfold TOKPARSE_STK_P in LOS. unfold_consts.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(sp0 - 32, sp0)] m) as MU.
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
pose proof (bytes_at_bound _ _ _ _ SLK) as SL0.

assert (STRk : forall mx, munch [(sp0 - 32, sp0)] m mx ->
bytes_at rsegs mx sb (str0 ++ [Z_to_bv 8 0]) /\ bytes_at rsegs mx (sb + Z.of_nat (length str0) + 1) slack).
{ intros mx MUx. split; (eapply bytes_at_transport; [eassumption | exact MUx |]); cbn; [rewrite length_app; cbn [length]|]; lia. }
clear STR SLK. stash G. stash UTF. stash GOTF.
unfold LOCCELL, LOCALE_LOCK in LOC, LCK. cbn in LOC.
apply rz_evt; [exact MOK|].
step.
carve_frame 32%nat ST.
step. step. step. step. step. step.

apply evt_RZ_done.
eapply (json_tokener_new_cps HIx) with (LB := LBc) (lo := lo);
[ heap_now S4L HIx HP MU WM MI
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; mod16 SPA | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | vm_compute; reflexivity | reflexivity |].
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in ST2, HPR2, ERR2, OUT2. rewrite unsigned_lit in ST2, HPR2 by lia.
replace (ret_pc (wz 0x21784)) with (wz 0x21784) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in LOC; [| right; left; unfold LOCCELL; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L] in LOC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in LCK; [| right; left; unfold LOCALE_LOCK; cbn; unfold s4_client_static; intros; lia]. cbn [hl_segs S4L] in LCK.
unstash G. unstash UTF. unstash GOTF.
lazymatch type of MU with munch _ _ ?mc =>
assert (G1 : jc_glob_P mc) by (eapply jc_glob_P_munch; [exact G | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (UTF1 : bytes_at rsegs mc JA_UTF8REP_P ja_utf8rep) by (eapply bytes_at_transport; [exact UTF | exact MU | cbn; unfold JA_UTF8REP_P; lia]);
assert (GOTF1 : bytes_at rsegs mc JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))))
by (eapply bytes_at_transport; [exact GOTF | exact MU | rewrite length_le8; cbn; unfold JA_GOT_FREE_USERDATA_P; lia]);
destruct (STRk mc MU) as [STR1 SLK1]
end.
pose proof (jc_glob_P_pres _ _ _ _ HPR2 G1) as G2.
assert (UTF2 : bytes_at rsegs m2 JA_UTF8REP_P ja_utf8rep).
{ eapply (heap_pres_bytes_at S4L); [exact HPR2 | exact UTF1 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static. intros; lia. }
assert (GOTF2 : bytes_at rsegs m2 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F)))).
{ eapply (heap_pres_bytes_at S4L); [exact HPR2 | exact GOTF1 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static. intros; lia. }
assert (STR2 : bytes_at rsegs m2 sb (str0 ++ [Z_to_bv 8 0])).
{ eapply (heap_pres_bytes_at S4L); [exact HPR2 | exact STR1 | left; lia]. }
assert (SLK2 : bytes_at rsegs m2 (sb + Z.of_nat (length str0) + 1) slack).
{ eapply (heap_pres_bytes_at S4L); [exact HPR2 | exact SLK1 | left; lia]. }

assert (PX2 : heap_presx S4L ja_xloc_P LBc sp0 m m2).
{ eapply heap_presx_trans.
- eapply heap_presx_of_munchx; [exact MU | exact WM |]. intros a Ha Hc. cbn. split; [| exact I].
destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [lia | cbn in Hc; unfold s4_client_static in Hc; lia |].
destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP Hb) as (_ & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]. }
clear MU WM MI ST G UTF GOTF G1 UTF1 GOTF1 STR1 SLK1 STRk.

assert (EXIT : forall m4 md4 (A4 : AS S4L HIx) F4 fc4 errv4 (RBS LK : list blk) (r4 : Z) (os : option jshape)
(x1 xg y0 y1 y2 xs0 xs1 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) (jk : list byte),
HEAPx A4 (RBS ++ LK ++ LBc) m4 md4 ->
((r4 = 0 /\ RBS = []) \/ (r4 <> 0 /\ exists s, jval rsegs S4F s m4 RBS r4 1 /\ sdepth s <= 32)) ->
heap_presx S4L ja_xloc_P LBc sp0 m m4 -> model_vm_only md md4 -> fsaved F F4 -> frm0 fc4 ->
rw_cells rsegs m4 LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m4 LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m4 ->
bytes_at rsegs m4 JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m4 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m4 lo (sp0 + -32) -> rw_cells rsegs m4 (sp0 + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m4 (0x75e70 - 164) [C4 errv4] ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (sp0 + -32)) xg (wz 0x75e70) y0 y1 y2 xs0 xs1 (wz r4) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (wz 0x217c0) fc4 None m4 (seg_rom rsegs)) md4) T).
{ intros m4 md4 A4 F4 fc4 errv4 RBS LK r4 os x1 xg y0 y1 y2 xs0 xs1 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 jk HP4 RES4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 GOTF4 ST4 FR4 ERR4.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4. pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
apply rz_evt; [exact MOK4|]. do 5 step.
replace (wz (sp0 + -32 + 32)) with (wz sp0) by (f_equal; lia).
apply evt_RZ_done. apply K. unfold tokparse_post. cbn [tpc_X tpc_LOCC tpc_GLOBL tpc_LOCK tpc_UTF8A tpc_GOTA tpc_GOTV tpc_G tokparse_consts_P hl_tp hl_segs S4L].
rewrite (unsigned_lit sp0) by lia.
exists m4, A4, xg, r4, errv4, RBS, LK.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FRM4]|].
split; [exact VM4|].
split. { pose proof (stk_release rsegs m4 lo (sp0 + -32) _ ST4 FR4 ltac:(lia)) as STx. cbn [cells_size csize Nat.add] in STx.
replace (sp0 + -32 + _) with sp0 in STx by lia. exact STx. }
split; [exact ERR4|].
split; [split; [exact LOC4 | split; [exact LCK4 | split; [exact G4 | split; [exact UTF4 | exact GOTF4]]]]|].
split; [exact PX4|]. split; [exact HP4 | exact RES4]. }
destruct OUT2 as [(-> & HP2) | (NZ & BS & TF & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
apply rz_evt; [exact MOK2|]. step. if_lit true.
apply evt_RZ_done.
eapply (EXIT m2 md2 A2 F2 fc2 errv2 [] [] 0 None); [exact HP2 | left; split; reflexivity | exact PX2 | exact VM2 | exact FS2 | exact (FRM2 FRM)
| exact LOC | exact LCK | exact G2 | exact UTF2 | exact GOTF2 | exact ST2 | exact FR | exact ERR2].
-
pose proof TF as (q & pb & PBS & EBS & TOK & _X).
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP2 ltac:(rewrite EBS; left; reflexivity)) as (_ & _ & Hrlo & Hrhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
apply rz_evt; [exact MOK2|]. step. if_falsex. step. step. step. step.
apply evt_RZ_done.
eapply (json_tokener_parse_ex_c_cps HIx (json_object_put_P HIx) USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf) with (TBS := BS) (LBc := LBc) (tk := r) (sb := sb) (str0 := str0) (slack := slack) (lo := lo);
[ exact HP2 | exact TF | exact STR2 | exact NONUL | lia | exact SLK2 | exact PAD | rewrite unsigned_lit by lia; lia | lia
| exact LOC | exact LCK | exact G2 | exact UTF2 | exact GOTF2
| rewrite unsigned_lit by lia; exact ST2 | exact LO | rewrite unsigned_lit by lia; unfold PE_STK; lia
| rewrite unsigned_lit by lia; mod16 SPA | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR2 | reflexivity | vm_compute; reflexivity | exact (FRM2 FRM) | reflexivity | reflexivity
| apply bv_eq; reflexivity |].
intros ms3 md3 PP.
destruct PP as (m3 & A3 & gp3 & r3 & errv3 & RBS & TBS3 & LK & RS3 & VM3 & ST3 & ERR3 & LOC3 & PX3 & HP3 & TOKR3 & RES3 & JG3).
cbn [pf_spf pf_tk pe_ra pe_s0 pe_s1 pe_s2 pe_s3 pe_s4 pe_s5 pe_s6 pe_s7 pe_s8 pe_s9 pe_s10 pe_s11 pf_md hl_segs hl_tp S4L] in RS3, ST3, PX3, TOKR3.
rewrite unsigned_lit in RS3, ST3, PX3 by lia. unfold PE_FRAME in RS3, ST3, PX3.
lazymatch type of ST3 with stk _ _ _ ?e => replace e with (sp0 + -32) in RS3, ST3, PX3 by lia end.
destruct RS3 as (w0 & w1 & w2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & w3 & w4 & w5 & w6 & F3 & fc3 & -> & FS3 & FRM3).
replace (ret_pc (wz 0x21798)) with (wz 0x21798) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
cbn [hl_segs S4L].

assert (PX23 : heap_presx S4L ja_xloc_P LBc sp0 m m3).
{ eapply heap_presx_trans; [exact PX2|]. eapply heap_presx_weaken; [exact PX3 | lia | intros b Hb; exact Hb | intros a Ha; exact Ha]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
assert (LCK3 : rw_cells rsegs m3 LOCALE_LOCK [C4 (wz 0)]).
{ eapply (heap_presx_rw_cells S4L); [exact PX3 | exact LCK |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
assert (UTF3 : bytes_at rsegs m3 JA_UTF8REP_P ja_utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact PX3 | exact UTF2 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
assert (GOTF3 : bytes_at rsegs m3 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F)))).
{ eapply (heap_presx_bytes_at S4L); [exact PX3 | exact GOTF2 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
pose proof (model_vm_only_trans _ _ _ VM2 VM3) as VM03. pose proof (fsaved_trans _ _ _ FS2 FS3) as FS03.
clear PX2 PX3 LCK UTF2 GOTF2 STR2 SLK2.

pose proof TOKR3 as (qq & pb3 & depth3 & PBS3 & levels3 & x3 & EBS3 & LEN3 & Hd3 & TOK3 & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3. pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
unfold tok_cells in TOK3.
apply rz_evt; [exact MOK3|]. step.

assert (FREE : forall m4 md4 (A4 : AS S4L HIx) F4 fc4 (RBS4 : list blk) (r4 : Z)
(x1 xg y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) (jk : list byte),
HEAPx A4 (RBS4 ++ TBS3 ++ LK ++ LBc) m4 md4 ->
((r4 = 0 /\ RBS4 = []) \/ (r4 <> 0 /\ exists s, jval rsegs S4F s m4 RBS4 r4 1 /\ sdepth s <= 32)) ->
tokrep rsegs S4F m4 TBS3 r ->
heap_presx S4L ja_xloc_P LBc sp0 m m4 -> model_vm_only md md4 -> fsaved F F4 -> frm0 fc4 ->
rw_cells rsegs m4 LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m4 LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m4 ->
bytes_at rsegs m4 JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m4 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m4 lo (sp0 + -32) -> rw_cells rsegs m4 (sp0 + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs m4 (0x75e70 - 164) [C4 errv3] ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (sp0 + -32)) xg (wz 0x75e70) y0 y1 y2 (wz r) (wz r4) b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (wz 0x217b4) fc4 None m4 (seg_rom rsegs)) md4) T).
{ intros m4 md4 A4 F4 fc4 RBS4 r4 x1 xg y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 jk HP4 RES4 TOKR4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 GOTF4 ST4 FR4 ERR4.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4. pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
apply rz_evt; [exact MOK4|]. step. step. apply evt_RZ_done.

eapply (json_tokener_free_cps HIx (json_object_put_P HIx)) with (BS := TBS3) (LB := RBS4 ++ LK ++ LBc) (tk := r) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP4 | apply Permutation_app_swap_app] | exact TOKR4 | exact NZ | rewrite unsigned_lit by lia; exact ST4 | exact LO
| rewrite unsigned_lit by lia; unfold put_stk_P; lia
| rewrite unsigned_lit by lia; mod16 SPA
| rewrite unsigned_lit by lia; lia | exact ERR4 | reflexivity | vm_compute; reflexivity | reflexivity |].
intros ms5 md5 (m5 & A5 & r5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (w0' & w1' & w2' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & w3' & w4' & w5' & w6' & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in ST5, HPR5, ERR5, HP5. rewrite unsigned_lit in ST5, HPR5 by lia.
replace (ret_pc (wz 0x217bc)) with (wz 0x217bc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
apply rz_evt; [exact MOK5|]. step. apply evt_RZ_done.
eapply (EXIT m5 md5 A5 F5 fc5 errv3 RBS4 LK r4 None).
+ exact HP5.
+ destruct RES4 as [L | (NZ4 & s & J & D)]; [left; exact L | right]. split; [exact NZ4|]. exists s. split; [| exact D].
eapply jval_agree; [exact J | eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | apply incl_refl].
+ eapply heap_presx_trans; [exact PX4|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb].
+ eapply model_vm_only_trans; [exact VM4 | exact VM5].
+ eapply fsaved_trans; [exact FS4 | exact FS5].
+ exact (FRM5 FRM4).
+ eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact LOC4 |]. right; left. unfold LOCCELL. cbn. unfold s4_client_static. intros; lia.
+ eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact LCK4 |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static. intros; lia.
+ eapply jc_glob_P_pres; [exact HPR5 | exact G4].
+ eapply (heap_pres_bytes_at S4L); [exact HPR5 | exact UTF4 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static. intros; lia.
+ eapply (heap_pres_bytes_at S4L); [exact HPR5 | exact GOTF4 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static. intros; lia.
+ exact ST5.
+ eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact FR4 | left; cbn; lia].
+ exact ERR5. }

step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+
step. apply evt_RZ_done.
eapply (FREE m3 md3 A3 F3 fc3 RBS r3); [exact HP3 | exact RES3 | exact TOKR3 | exact PX23 | exact VM03 | exact FS03 | exact (FRM3 (FRM2 FRM))
| exact LOC3 | exact LCK3 | exact JG3 | exact UTF3 | exact GOTF3 | exact ST3 | exact FR | exact ERR3].
+
destruct RES3 as [[-> ->] | (NZ3 & s & J & D)].
* step. if_lit true. step. step. apply evt_RZ_done.
eapply (FREE m3 md3 A3 F3 fc3 [] 0); [exact HP3 | left; split; reflexivity | exact TOKR3 | exact PX23 | exact VM03 | exact FS03 | exact (FRM3 (FRM2 FRM))
| exact LOC3 | exact LCK3 | exact JG3 | exact UTF3 | exact GOTF3 | exact ST3 | exact FR | exact ERR3].
* assert (RR : 0 < r3 /\ r3 + 48 < 2^64).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND.
destruct (jval_hdr rsegs S4F s m3 RBS r3 1 J ND) as (n & tojs & pb0 & udel & ud & rest & INp & Hn & H48 & _).
pose proof (heap_blk S4L HIx _ _ _ _ r3 n HP3 ltac:(apply in_or_app; left; exact INp)) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
step. if_falsex. step. apply evt_RZ_done.
eapply (json_object_put_P HIx) with (s := Some s) (BS := RBS) (p := r3) (rc := 1) (lo := lo) (LB := TBS3 ++ LK ++ LBc);
[exact HP3 | cbn [put_pre]; split; [exact NZ3 | split; [lia | exact J]] | reflexivity | rewrite unsigned_lit by lia; exact ST3 | exact LO
| rewrite unsigned_lit by lia; unfold put_stk_P; lia
| rewrite unsigned_lit by lia; mod16 SPA
| rewrite unsigned_lit by lia; lia | exact ERR3 | reflexivity | vm_compute; reflexivity |].
intros ms4 md4 (m4 & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OUT4).
destruct RS4 as (w0' & w1' & w2' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & w3' & w4' & w5' & w6' & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in ST4, HPR4, ERR4, OUT4. rewrite unsigned_lit in ST4, HPR4 by lia.
replace (ret_pc (wz 0x217a8)) with (wz 0x217a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HP4 : HEAPx A4 (TBS3 ++ LK ++ LBc) m4 md4).
{ destruct OUT4 as [[_ HP4] | (s' & _ & RC & _)]; [exact HP4 | lia]. }
clear OUT4.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
apply rz_evt; [exact MOK4|]. step. step. apply evt_RZ_done.
eapply (FREE m4 md4 A4 F4 fc4 [] 0).
-- exact HP4.
-- left; split; reflexivity.
-- eapply tokrep_pres; [exact HPR4 | intros b Hb; apply in_or_app; left; exact Hb | exact TOKR3].
-- eapply heap_presx_trans; [exact PX23|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb].
-- eapply model_vm_only_trans; [exact VM03 | exact VM4].
-- eapply fsaved_trans; [exact FS03 | exact FS4].
-- exact (FRM4 (FRM3 (FRM2 FRM))).
-- eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact LOC3 |]. right; left. unfold LOCCELL. cbn. unfold s4_client_static. intros; lia.
-- eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact LCK3 |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static. intros; lia.
-- eapply jc_glob_P_pres; [exact HPR4 | exact JG3].
-- eapply (heap_pres_bytes_at S4L); [exact HPR4 | exact UTF3 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static. intros; lia.
-- eapply (heap_pres_bytes_at S4L); [exact HPR4 | exact GOTF3 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static. intros; lia.
-- exact ST4.
-- eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact FR | left; cbn; lia].
-- exact ERR4.
Qed.

#[using="USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf"] Theorem tokparse_P_cps : tokparse_stmt_P HIx.
Proof.
unfold tokparse_stmt_P, tokparse_stmt. intros until errv.
intros HP STR NONUL LEN SLK PAD SPle SBL (LOC & LCK & G & UTF & GOTF) ST LO LOS SPA HT SP62 ERR TP RAE FRM A0 K.
cbn [tpc_entry tpc_stk tpc_G tpc_X tpc_LOCC tpc_GLOBL tpc_LOCK tpc_UTF8A tpc_GOTA tpc_GOTV tokparse_consts_P hl_tp hl_segs S4L] in *.
subst a0 tp. pose proof (bv_unsigned_in_range 64 sp) as SPR.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply tokparse_P_main; try eassumption; [lia|].
intros ms' md' P. apply K. rewrite Z_to_bv_bv_unsigned in P. exact P.
Qed.
End TokParseP.

End RC__1.
