(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlCE.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhHQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Ki. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uzoi.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uyk8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGEL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGEL.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ul9N.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac Tk1Reset Tk1Free.
Import TopUbTac Tk1Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
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
Let json_tokener_new_cps := UlCE.Mq1.json_tokener_new_cps HIx (Uyk8.json_object_put_P HIx).
Let json_tokener_parse_ex_c_cps := Uzoi.Mq0.json_tokener_parse_ex_c_cps HIx (Uyk8.json_object_put_P HIx) USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf.

Ltac mod16 SPA :=
lazymatch type of SPA with ?b mod 16 = 0 =>
lazymatch goal with |- ?x mod 16 = 0 =>
first [ replace x with (b + (-2) * 16) by lia | replace x with (b + (-3) * 16) by lia | replace x with (b + (-1) * 16) by lia | replace x with b by lia ];
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

#[using="Type"] Lemma tokrep_with_pres : forall LB SP m m' BS tk stack pb depth PBS levels x,
heap_pres S4L LB SP m m' -> incl BS LB -> tokrep_with rsegs S4F m BS tk stack pb depth PBS levels x ->
tokrep_with rsegs S4F m' BS tk stack pb depth PBS levels x.
Proof.
intros LB SP m m' BS tk stack pb depth PBS levels x HPR Hi (EBS & LEN & Hd & TOK & PB & Hpb & TS & LOK & CLEAN).
assert (AG : agree_on rsegs BS m m') by (eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | exact Hi]).
split; [exact EBS|]. split; [exact LEN|]. split; [exact Hd|].
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

#[using="USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf json_tokener_new_cps json_tokener_parse_ex_c_cps"] Lemma tokparse_P_main :
forall (raw gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LBc : list blk) (sp1 sb lo : Z) (str0 slack jw : list byte) (errv : word),
HEAPx A LBc m md ->
bytes_at rsegs m sb (str0 ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str0 -> Z.of_nat (length str0) < 2^25 ->
bytes_at rsegs m (sb + Z.of_nat (length str0) + 1) slack ->
(- (sb + Z.of_nat (length str0) + 1)) mod 8 <= Z.of_nat (length slack) ->
sp1 + 16 <= sb -> sb + Z.of_nat (length str0) + 1 < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m ->
bytes_at rsegs m JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m lo sp1 -> alloc_ceiling <= lo -> lo <= sp1 + 16 - TOKPARSE_STK_P ->
sp1 mod 16 = 0 -> sp1 + 16 <= hi_top S4L HIx -> 0 <= sp1 -> sp1 + 16 <= 2^62 ->
rw_cells rsegs m sp1 [CB 8 jw; C8 raw] -> heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 m -> a1 = wz (sp1 + 4) ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
bv_unsigned raw mod 2 = 0 -> frm0 fc ->
(forall ms' md', tokparse_post S4L HIx S4F tokparse_consts_P raw (wz (sp1 + 16)) gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md LBc lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR (wz 0x21b34) (wz sp1) gp (wz 0x77c00) t0 t1 t2 s0 s1 (wz sb) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x21b40) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv.
intros HP STR NONUL LEN SLK PAD SPle SBL LOC LCK G UTF GOTF ST LO LOS SPA HT SP0 SPR FRW PX0 EA1 ERR RAE FRM K.
subst a1.
pose proof (json_object_put_cps HIx (Ul9N.Mq0.lh_delete_tail_cps2 HIx) MEMMOVE) as PUT.
unfold TOKPARSE_STK_P in LOS. unfold_consts.
apply (rw_cells_split_CB rsegs m sp1 [] 8 jw [C8 raw] [4%nat; 4%nat]) in FRW; [| reflexivity].
cbn [app mk_CB_cells] in FRW.
apply (proj1 (QJjn.rw_cells_app rsegs m sp1 [CB 4 (firstn 4 jw)] [CB 4 (firstn 4 (skipn 4 jw)); C8 raw])) in FRW.
destruct FRW as [FRWa FRWb].
change (sp1 + Z.of_nat (cells_size [CB 4 (firstn 4 jw)])) with (sp1 + 4) in FRWb.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(sp1 - 48, sp1)] m) as MU.
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
pose proof (bytes_at_bound _ _ _ _ SLK) as SL0.

assert (STRk : forall mx, munch [(sp1 - 48, sp1)] m mx ->
bytes_at rsegs mx sb (str0 ++ [Z_to_bv 8 0]) /\ bytes_at rsegs mx (sb + Z.of_nat (length str0) + 1) slack).
{ intros mx MUx. split; (eapply bytes_at_transport; [eassumption | exact MUx |]); cbn; [rewrite length_app; cbn [length]|]; lia. }
clear STR SLK. stash G. stash UTF. stash GOTF. stash FRWa. stash FRWb.
unfold LOCCELL, LOCALE_LOCK in LOC, LCK. cbn in LOC.
apply rz_evt; [exact MOK|].
step.
carve_frame 48%nat ST.
do 9 stepz.
unstash FRWa. unstash FRWb.
lazymatch type of MU with munch _ _ ?mc =>
assert (FRWa' : rw_cells rsegs mc sp1 [CB 4 (firstn 4 jw)]) by (eapply rw_cells_transport; [exact FRWa | exact MU | exact WM | cbn; lia]);
assert (FRWb' : rw_cells rsegs mc (sp1 + 4) [CB 4 (firstn 4 (skipn 4 jw)); C8 raw]) by (eapply rw_cells_transport; [exact FRWb | exact MU | exact WM | cbn; lia]);
clear FRWa FRWb; rename FRWa' into FRWa; rename FRWb' into FRWb
end.

apply evt_RZ_done.
eapply json_tokener_new_cps with (LB := LBc) (lo := lo);
[ heap_now S4L HIx HP MU WM MI
| rewrite unsigned_lit by lia; exact ST | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; mod16 SPA | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | vm_compute; reflexivity | reflexivity |].
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in ST2, HPR2, ERR2, OUT2. rewrite unsigned_lit in ST2, HPR2 by lia.
replace (ret_pc (wz 0x21b68)) with (wz 0x21b68) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRWa; [| left; cbn; lia]. cbn [hl_segs S4L] in FRWa.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRWb; [| left; cbn; lia]. cbn [hl_segs S4L] in FRWb.
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

assert (PX2 : heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 m2).
{ eapply heap_presx_trans; [exact PX0|]. eapply heap_presx_trans.
- eapply heap_presx_of_munchx; [exact MU | exact WM |]. intros a Ha Hc. cbn. split; [| exact I].
destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [lia | cbn in Hc; unfold s4_client_static in Hc; lia |].
destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP Hb) as (_ & _ & _ & Hhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia.
- apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]. }
clear MU WM MI ST G UTF GOTF G1 UTF1 GOTF1 STR1 SLK1 STRk.

assert (EXIT : forall m4 md4 (A4 : AS S4L HIx) F4 fc4 errv4 (RBS LK : list blk) (r4 : Z)
(x1 xg y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) (jv : list byte) (ev : word),
HEAPx A4 (RBS ++ LK ++ LBc) m4 md4 ->
((r4 = 0 /\ RBS = []) \/ (r4 <> 0 /\ exists s, jval rsegs S4F s m4 RBS r4 1 /\ sdepth s <= 32)) ->
heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 m4 -> model_vm_only md md4 -> fsaved F F4 -> frm0 fc4 ->
rw_cells rsegs m4 LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m4 LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m4 ->
bytes_at rsegs m4 JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m4 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m4 lo sp1 -> rw_cells rsegs m4 sp1 [CB 4 jv; C4 ev; C8 raw] ->
rw_cells rsegs m4 (0x77c00 - 164) [C4 errv4] ->
realizes rsegs (mkCfg (MS (mkR x1 (wz sp1) xg (wz 0x77c00) y0 y1 y2 s0 s1 (wz r4) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (wz 0x21b34) fc4 None m4 (seg_rom rsegs)) md4) T).
{ intros m4 md4 A4 F4 fc4 errv4 RBS LK r4 x1 xg y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 jv ev HP4 RES4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 GOTF4 ST4 FR4 ERR4.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4. pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
apply rz_evt; [exact MOK4|]. do 3 step.
apply evt_RZ_done. apply K. unfold tokparse_post. cbn [tpc_X tpc_LOCC tpc_GLOBL tpc_LOCK tpc_UTF8A tpc_GOTA tpc_GOTV tpc_G tokparse_consts_P hl_tp hl_segs S4L].
rewrite (unsigned_lit (sp1 + 16)) by lia.
exists m4, A4, xg, r4, errv4, RBS, LK.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FRM4]|].
split; [exact VM4|].
split. { pose proof (stk_release rsegs m4 lo sp1 _ ST4 FR4 ltac:(lia)) as STx. cbn [cells_size csize Nat.add] in STx.
replace (sp1 + _) with (sp1 + 16) in STx by lia. exact STx. }
split; [exact ERR4|].
split; [split; [exact LOC4 | split; [exact LCK4 | split; [exact G4 | split; [exact UTF4 | exact GOTF4]]]]|].
split; [exact PX4|]. split; [exact HP4 | exact RES4]. }

destruct OUT2 as [(-> & HP2) | (NZ & BS & TF & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [(sp1, sp1 + 16)] m2) as MU.
stash G2. stash UTF2. stash GOTF2. clear STR2 SLK2.
apply rz_evt; [exact MOK2|].
step. if_lit true.
bstep. stepz. step.
do 7 step.
unstash G2. unstash UTF2. unstash GOTF2.
lazymatch type of MU with munch _ _ ?mc =>
assert (PXc : heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 mc)
by (eapply heap_presx_trans; [exact PX2 |]; eapply heap_presx_of_munchx; [exact MU | exact WM |]; intros a Ha Hc; cbn; split; [| exact I];
destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [lia | cbn in Hc; unfold s4_client_static in Hc; lia |];
destruct b as [ba bn]; cbn in Hr; pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP2 Hb) as (_ & _ & _ & Hhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi; lia);
assert (Gc : jc_glob_P mc) by (eapply jc_glob_P_munch; [exact G2 | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (UTFc : bytes_at rsegs mc JA_UTF8REP_P ja_utf8rep) by (eapply bytes_at_transport; [exact UTF2 | exact MU | cbn; unfold JA_UTF8REP_P; lia]);
assert (GOTFc : bytes_at rsegs mc JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))))
by (eapply bytes_at_transport; [exact GOTF2 | exact MU | rewrite length_le8; cbn; unfold JA_GOT_FREE_USERDATA_P; lia]);
assert (HPc : HEAPx A2 LBc mc md2) by (heap_now S4L HIx HP2 MU WM MI2);
pose proof (stk_release rsegs mc lo (sp1 + -48) _ ST2 FR ltac:(lia)) as STc
end.
cbn [cells_size csize Nat.add] in STc. replace (sp1 + -48 + _) with sp1 in STc by lia.
lazymatch type of FRWb with rw_cells _ ?mm _ ?cs =>
pose proof (proj2 (QJjn.rw_cells_app rsegs mm sp1 [CB 4 (firstn 4 jw)] cs) (conj FRWa FRWb)) as FRWj
end.
cbn [app] in FRWj.
try replace (sp1 + -48 + 48) with sp1 by lia.
apply evt_RZ_done.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ ?pcv _ _ _ _) _) _ =>
replace pcv with (wz 0x21b34) by (first [ reflexivity | (symmetry; apply ret_pc_even; [lia | reflexivity]) | (apply bv_eq; vm_compute; reflexivity) ])
end.
eapply (EXIT _ _ A2 _ _ errv2 [] [] 0); [exact HPc | left; split; reflexivity | exact PXc | exact VM2 | exact FS2 | exact (FRM2 FRM)
| exact LOC | exact LCK | exact Gc | exact UTFc | exact GOTFc | exact STc | exact FRWj | exact ERR2].
-
pose proof TF as (q & pb & PBS & EBS & TOK & _X).
pose proof (heap_blk S4L HIx _ _ _ _ r 72 HP2 ltac:(rewrite EBS; left; reflexivity)) as (_ & RAL & Hrlo & Hrhi & _). unfold alloc_ceiling, sp_window_lo, stack_max_size in Hrhi.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.
apply rz_evt; [exact MOK2|]. step. if_falsex. step. step. step. step.
apply evt_RZ_done.
eapply json_tokener_parse_ex_c_cps with (TBS := BS) (LBc := LBc) (tk := r) (sb := sb) (str0 := str0) (slack := slack) (lo := lo);
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
lazymatch type of ST3 with stk _ _ _ ?e => replace e with (sp1 + -48) in RS3, ST3, PX3 by lia end.
destruct RS3 as (w0 & w1 & w2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & w3 & w4 & w5 & w6 & F3 & fc3 & -> & FS3 & FRM3).
replace (ret_pc (wz 0x21b7c)) with (wz 0x21b7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
cbn [hl_segs S4L].

assert (PX23 : heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 m3).
{ eapply heap_presx_trans; [exact PX2|]. eapply heap_presx_weaken; [exact PX3 | lia | intros b Hb; exact Hb | intros a Ha; exact Ha]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in FRWa; [| left; cbn; lia]. cbn [hl_segs S4L] in FRWa.
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in FRWb; [| left; cbn; lia]. cbn [hl_segs S4L] in FRWb.
assert (LCK3 : rw_cells rsegs m3 LOCALE_LOCK [C4 (wz 0)]).
{ eapply (heap_presx_rw_cells S4L); [exact PX3 | exact LCK |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
assert (UTF3 : bytes_at rsegs m3 JA_UTF8REP_P ja_utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact PX3 | exact UTF2 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
assert (GOTF3 : bytes_at rsegs m3 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F)))).
{ eapply (heap_presx_bytes_at S4L); [exact PX3 | exact GOTF2 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static, xloc, ja_xloc_P, s4_volatile, LOCCELL. intros; lia. }
pose proof (model_vm_only_trans _ _ _ VM2 VM3) as VM03. pose proof (fsaved_trans _ _ _ FS2 FS3) as FS03.
clear PX2 PX3 LCK UTF2 GOTF2 STR2 SLK2.

assert (TAIL : forall m4 md4 (A4 : AS S4L HIx) F4 fc4 errv4 (RBS4 : list blk) (r4 : Z) (qt pbt dt : Z) (PBSt : list blk) (lvt : list tlevel) (xt : tscal)
(x1 xg y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 : word) (jk jv : list byte) (ev : word),
HEAPx A4 (RBS4 ++ TBS3 ++ LK ++ LBc) m4 md4 ->
((r4 = 0 /\ RBS4 = []) \/ (r4 <> 0 /\ exists s, jval rsegs S4F s m4 RBS4 r4 1 /\ sdepth s <= 32)) ->
tokrep_with rsegs S4F m4 TBS3 r qt pbt dt PBSt lvt xt ->
heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 m4 -> model_vm_only md md4 -> fsaved F F4 -> frm0 fc4 ->
rw_cells rsegs m4 LOCCELL [C8 (wz GLOBLOC)] -> rw_cells rsegs m4 LOCALE_LOCK [C4 (wz 0)] -> jc_glob_P m4 ->
bytes_at rsegs m4 JA_UTF8REP_P ja_utf8rep -> bytes_at rsegs m4 JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))) ->
stk rsegs m4 lo (sp1 + -48) -> rw_cells rsegs m4 (sp1 + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 (wz 0x21b34)] ->
rw_cells rsegs m4 sp1 [CB 4 jv; C4 ev; C8 raw] ->
rw_cells rsegs m4 (0x77c00 - 164) [C4 errv4] ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (sp1 + -48)) xg (wz 0x77c00) y0 y1 y2 (wz r) (wz dt) b0 b1 b2 b3 b4 b5 b6 b7 (wz r4) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (wz 0x21bd8) fc4 None m4 (seg_rom rsegs)) md4) T).
{ intros m4 md4 A4 F4 fc4 errv4 RBS4 r4 qt pbt dt PBSt lvt xt x1 xg y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 jk jv ev HP4 RES4 TW4 PX4 VM4 FS4 FRM4 LOC4 LCK4 G4 UTF4 GOTF4 ST4 FR4 FRW4 ERR4.
eapply (Tk1Free.tokfree_tail_cps HIx PUT) with (BS := TBS3) (LB := RBS4 ++ LK ++ LBc) (tk := r) (SP := sp1 + -48) (lo := lo);
[ eapply (heap_perm S4L HIx); [exact HP4 | apply Permutation_app_swap_app]
| exact TW4 | exact FR4 | exact ST4 | exact LO | unfold Tk1Reset.RESET_STK, put_stk_P; lia
| mod16 SPA | lia | lia | lia | exact ERR4 | reflexivity |].
intros ms5 md5 (m5 & A5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & HP5).
destruct RS5 as (w0' & w1' & w2' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & w3' & w4' & w5' & w6' & F5 & fc5 & -> & FS5 & FRM5).
cbn [hl_segs hl_tp S4L] in ST5, HPR5, ERR5, HP5. rewrite unsigned_lit in ST5, HPR5 by lia.
replace (ret_pc (wz 0x21b34)) with (wz 0x21b34) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (sp1 + -48 + 48) with sp1 in * by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FRW4; [| left; cbn; lia]. cbn [hl_segs S4L] in FRW4.
eapply (EXIT m5 md5 A5 F5 fc5 errv4 RBS4 LK r4).
- exact HP5.
- destruct RES4 as [L | (NZ4 & s & J & D)]; [left; exact L | right]. split; [exact NZ4|]. exists s. split; [| exact D].
eapply jval_agree; [exact J | eapply (agree_of_heap_pres rsegs S4L); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | apply incl_refl].
- eapply heap_presx_trans; [exact PX4|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb].
- eapply model_vm_only_trans; [exact VM4 | exact VM5].
- eapply fsaved_trans; [exact FS4 | exact FS5].
- exact (FRM5 FRM4).
- eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact LOC4 |]. right; left. unfold LOCCELL. cbn. unfold s4_client_static. intros; lia.
- eapply (heap_pres_rw_cells S4L); [exact HPR5 | exact LCK4 |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static. intros; lia.
- eapply jc_glob_P_pres; [exact HPR5 | exact G4].
- eapply (heap_pres_bytes_at S4L); [exact HPR5 | exact UTF4 |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static. intros; lia.
- eapply (heap_pres_bytes_at S4L); [exact HPR5 | exact GOTF4 |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static. intros; lia.
- exact ST5.
- exact FRW4.
- exact ERR5. }

destruct TOKR3 as (qq & pb3 & depth3 & PBS3 & levels3 & x3 & TW3).
pose proof TW3 as (EBS3 & LEN3 & Hd3 & TOK3 & _).
unfold tok_cells in TOK3.
unfold LOCCELL in LOC3. cbn in LOC3. unfold LOCALE_LOCK in LCK3.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3. pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
pose proof (wmono_refl rsegs m3) as WM. pose proof (munch_refl [(sp1, sp1 + 16)] m3) as MU.
stash JG3. stash UTF3. stash GOTF3. stash TW3.
apply rz_evt; [exact MOK3|].
bstep.
stepz.
unstash JG3. unstash UTF3. unstash GOTF3. unstash TW3.
lazymatch type of MU with munch _ _ ?mc =>
assert (HPRs : heap_pres S4L (RBS ++ TBS3 ++ LK ++ LBc) (sp1 + 16) m3 mc)
by (eapply (heap_pres_of_munch S4L _ (sp1 + 16)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP3 | intros bb Hbb; exact Hbb | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia |];
apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | apply Forall_nil]);
assert (HP3s : HEAPx A3 (RBS ++ TBS3 ++ LK ++ LBc) mc md3) by (heap_now S4L HIx HP3 MU WM MI3);
assert (RESs : (r3 = 0 /\ RBS = []) \/ (r3 <> 0 /\ exists s, jval rsegs S4F s mc RBS r3 1 /\ sdepth s <= 32))
by (destruct RES3 as [L | (NZ3 & s & J & D)]; [left; exact L | right]; split; [exact NZ3|]; exists s; split; [| exact D];
eapply jval_agree; [exact J | eapply (agree_of_heap_pres rsegs S4L); [exact HPRs | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | apply incl_refl]);
assert (PXs : heap_presx S4L ja_xloc_P LBc (sp1 + 16) m0 mc)
by (eapply heap_presx_trans; [exact PX23|]; apply heap_pres_presx; eapply heap_pres_weaken;
[exact HPRs | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb])
end.
pose proof (jc_glob_P_pres _ _ _ _ HPRs JG3) as JGs.
lazymatch type of HPRs with heap_pres _ _ _ _ ?mc =>
assert (UTFs : bytes_at rsegs mc JA_UTF8REP_P ja_utf8rep)
by (eapply (heap_pres_bytes_at S4L); [exact HPRs | exact UTF3 |]; right; left; unfold JA_UTF8REP_P; cbn; unfold s4_client_static; intros; lia);
assert (GOTFs : bytes_at rsegs mc JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))))
by (eapply (heap_pres_bytes_at S4L); [exact HPRs | exact GOTF3 |]; right; left; unfold JA_GOT_FREE_USERDATA_P; rewrite length_le8; cbn; unfold s4_client_static; intros; lia)
end.
pose proof (tokrep_with_pres _ _ _ _ _ _ _ _ _ _ _ _ HPRs ltac:(intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb) TW3) as TWs.
clear TOK3 JG3 UTF3 GOTF3 TW3 RES3 PX23.
pose proof TWs as (_ & _ & _ & TOKs & _). unfold tok_cells in TOKs.
lazymatch type of FRWb with rw_cells _ ?mm _ ?cs =>
pose proof (proj2 (QJjn.rw_cells_app rsegs mm sp1 [CB 4 (firstn 4 jw)] cs) (conj FRWa FRWb)) as FRWj
end.
cbn [app] in FRWj. clear FRWa FRWb.
step. lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c end.
+ step. step. rewrite (sx32_small depth3) by lia. step. if_falsex.
apply evt_RZ_done.
eapply (TAIL _ _ A3 _ _ errv3 RBS r3); [exact HP3s | exact RESs | exact TWs | exact PXs | exact VM03 | exact FS03 | exact (FRM3 (FRM2 FRM))
| exact LOC3 | exact LCK3 | exact JGs | exact UTFs | exact GOTFs | exact ST3 | exact FR | exact FRWj | exact ERR3].
+ destruct RESs as [[-> ->] | (NZ3 & s & J & D)].
* step. if_lit true. step. step. rewrite (sx32_small depth3) by lia. step. if_truex.
apply evt_RZ_done.
eapply (TAIL _ _ A3 _ _ errv3 [] 0); [exact HP3s | left; split; reflexivity | exact TWs | exact PXs | exact VM03 | exact FS03 | exact (FRM3 (FRM2 FRM))
| exact LOC3 | exact LCK3 | exact JGs | exact UTFs | exact GOTFs | exact ST3 | exact FR | exact FRWj | exact ERR3].
* assert (RR : 0 < r3 /\ r3 + 48 < 2^64).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP3s) as ND. rewrite map_app in ND. apply List.NoDup_app_remove_r in ND.
destruct (jval_hdr rsegs S4F s _ RBS r3 1 J ND) as (n & tojs & pb0 & udel & ud & rest & INp & Hn & H48 & _).
pose proof (heap_blk S4L HIx _ _ _ _ r3 n HP3s ltac:(apply in_or_app; left; exact INp)) as (_ & _ & Hlo & Hhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. lia. }
step. if_falsex. step. apply evt_RZ_done.
eapply PUT with (s := Some s) (BS := RBS) (p := r3) (rc := 1) (lo := lo) (LB := TBS3 ++ LK ++ LBc);
[exact HP3s | cbn [put_pre]; split; [exact NZ3 | split; [lia | exact J]] | reflexivity | rewrite unsigned_lit by lia; exact ST3 | exact LO
| rewrite unsigned_lit by lia; unfold put_stk_P; lia
| rewrite unsigned_lit by lia; mod16 SPA
| rewrite unsigned_lit by lia; lia | exact ERR3 | reflexivity | vm_compute; reflexivity |].
intros ms4 md4 (mP & A4 & r4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & OUT4).
destruct RS4 as (w0' & w1' & w2' & q1' & q2' & q3' & q4' & q5' & q6' & q7' & w3' & w4' & w5' & w6' & F4 & fc4 & -> & FS4 & FRM4).
cbn [hl_segs hl_tp S4L] in ST4, HPR4, ERR4, OUT4. rewrite unsigned_lit in ST4, HPR4 by lia.
replace (ret_pc (wz 0x21ba4)) with (wz 0x21ba4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HP4 : HEAPx A4 (TBS3 ++ LK ++ LBc) mP md4).
{ destruct OUT4 as [[_ HP4] | (s' & _ & RC & _)]; [exact HP4 | lia]. }
clear OUT4.
pose proof (tokrep_with_pres _ _ _ _ _ _ _ _ _ _ _ _ HPR4 ltac:(intros b Hb; apply in_or_app; left; exact Hb) TWs) as TW4.
clear TOKs.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FRWj; [| left; cbn; lia]. cbn [hl_segs S4L] in FRWj.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4. pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
pose proof TW4 as (_ & _ & _ & TOK4 & _). unfold tok_cells in TOK4.
cbn [hl_segs S4L].
apply rz_evt; [exact MOK4|]. step. step. rewrite (sx32_small depth3) by lia. step. if_truex.
apply evt_RZ_done.
eapply (TAIL mP md4 A4 F4 fc4 errv3 [] 0).
-- exact HP4.
-- left; split; reflexivity.
-- exact TW4.
-- eapply heap_presx_trans; [exact PXs|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb].
-- eapply model_vm_only_trans; [exact VM03 | exact VM4].
-- eapply fsaved_trans; [exact FS03 | exact FS4].
-- exact (FRM4 (FRM3 (FRM2 FRM))).
-- eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact LOC3 |]. right; left. unfold LOCCELL. cbn. unfold s4_client_static. intros; lia.
-- eapply (heap_pres_rw_cells S4L); [exact HPR4 | exact LCK3 |]. right; left. unfold LOCALE_LOCK. cbn. unfold s4_client_static. intros; lia.
-- eapply jc_glob_P_pres; [exact HPR4 | exact JGs].
-- eapply (heap_pres_bytes_at S4L); [exact HPR4 | exact UTFs |]. right; left. unfold JA_UTF8REP_P. cbn. unfold s4_client_static. intros; lia.
-- eapply (heap_pres_bytes_at S4L); [exact HPR4 | exact GOTFs |]. right; left. unfold JA_GOT_FREE_USERDATA_P. rewrite length_le8. cbn. unfold s4_client_static. intros; lia.
-- exact ST4.
-- exact FR.
-- exact FRWj.
-- exact ERR4.
Qed.

#[using="USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf json_tokener_new_cps json_tokener_parse_ex_c_cps"] Theorem tokparse_P_cps : tokparse_stmt_P HIx.
Proof.
unfold tokparse_stmt_P, tokparse_stmt. intros until errv.
intros HP STR NONUL LEN SLK PAD SPle SBL (LOC & LCK & G & UTF & GOTF) ST LO LOS SPA HT SP62 ERR TP RAE FRM A0 K.
cbn [tpc_entry tpc_stk tpc_G tpc_X tpc_LOCC tpc_GLOBL tpc_LOCK tpc_UTF8A tpc_GOTA tpc_GOTV tokparse_consts_P hl_tp hl_segs S4L] in *.
subst a0 tp. pose proof (bv_unsigned_in_range 64 sp) as SPR.
rewrite <- (Z_to_bv_bv_unsigned sp).
set (sp0 := bv_unsigned sp) in *. assert (Esp : bv_unsigned sp = sp0) by reflexivity. clearbody sp0.
unfold TOKPARSE_STK_P in LOS. unfold_consts. unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(sp0 - 16, sp0)] m) as MU.
pose proof (bytes_at_bound _ _ _ _ STR) as SB0. rewrite length_app in SB0. cbn [length] in SB0.
pose proof (bytes_at_bound _ _ _ _ SLK) as SL0.
assert (STRk : forall mx, munch [(sp0 - 16, sp0)] m mx ->
bytes_at rsegs mx sb (str0 ++ [Z_to_bv 8 0]) /\ bytes_at rsegs mx (sb + Z.of_nat (length str0) + 1) slack).
{ intros mx MUx. split; (eapply bytes_at_transport; [eassumption | exact MUx |]); cbn; [rewrite length_app; cbn [length]|]; lia. }
clear STR SLK. stash G. stash UTF. stash GOTF.
unfold QPZI.LOCCELL, QPZI.LOCALE_LOCK, LOCCELL, LOCALE_LOCK in LOC, LCK. cbn in LOC.
stash LOC. stash LCK. stash ERR.
apply rz_evt; [exact MOK|].
step.
carve_frame 16%nat ST.
do 3 stepz.
unstash G. unstash UTF. unstash GOTF. unstash LOC. unstash LCK. unstash ERR.
lazymatch type of MU with munch _ _ ?mc =>
lazymatch type of LOC with rw_cells _ _ ?aL ?cL =>
assert (LOC1 : rw_cells rsegs mc aL cL) by (eapply rw_cells_transport; [exact LOC | exact MU | exact WM | cbn; lia]) end;
lazymatch type of LCK with rw_cells _ _ ?aK ?cK =>
assert (LCK1 : rw_cells rsegs mc aK cK) by (eapply rw_cells_transport; [exact LCK | exact MU | exact WM | cbn; lia]) end;
lazymatch type of ERR with rw_cells _ _ ?aE ?cE =>
assert (ERR1 : rw_cells rsegs mc aE cE) by (eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn; lia]) end;
clear LOC LCK ERR; rename LOC1 into LOC; rename LCK1 into LCK; rename ERR1 into ERR
end.
lazymatch type of MU with munch _ _ ?mc =>
assert (G1 : jc_glob_P mc) by (eapply jc_glob_P_munch; [exact G | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
assert (UTF1 : bytes_at rsegs mc JA_UTF8REP_P ja_utf8rep) by (eapply bytes_at_transport; [exact UTF | exact MU | cbn; unfold JA_UTF8REP_P; lia]);
assert (GOTF1 : bytes_at rsegs mc JA_GOT_FREE_USERDATA_P (le8 (wz (fn_free_userdata S4F))))
by (eapply bytes_at_transport; [exact GOTF | exact MU | rewrite length_le8; cbn; unfold JA_GOT_FREE_USERDATA_P; lia]);
assert (PX0 : heap_presx S4L ja_xloc_P LBc sp0 m mc)
by (eapply heap_presx_of_munchx; [exact MU | exact WM |]; intros a Ha Hc; cbn; split; [| exact I];
destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [lia | cbn in Hc; unfold s4_client_static in Hc; lia |];
destruct b as [ba bn]; cbn in Hr; pose proof (heap_blk S4L HIx _ _ _ _ ba bn HP Hb) as (_ & _ & _ & Hhi & _); unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi; lia);
assert (HP1 : HEAPx A LBc mc md) by (heap_now S4L HIx HP MU WM MI);
destruct (STRk mc MU) as [STR1 SLK1]
end.
apply evt_RZ_done.
eapply (tokparse_P_main ra gp) with (sp1 := sp0 + -16) (m0 := m) (LBc := LBc) (lo := lo) (str0 := str0) (slack := slack) (errv := errv);
[ exact HP1 | exact STR1 | exact NONUL | exact LEN | exact SLK1 | exact PAD | lia | lia
| exact LOC | exact LCK | exact G1 | exact UTF1 | exact GOTF1
| exact ST | exact LO | unfold TOKPARSE_STK_P; lia | mod16 SPA | lia | lia | lia
| exact FR | replace (sp0 + -16 + 16) with sp0 by lia; exact PX0
| first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?unsigned_lit by lia; lia) | (apply bv_eq; cbn; rewrite ?unsigned_lit by lia; lia) ]
| exact ERR | exact RAE | exact FRM |].
intros ms' md' P. apply K. replace (sp0 + -16 + 16) with sp0 in P by lia. rewrite <- Esp, Z_to_bv_bv_unsigned in P. exact P.
Qed.
End TokParseP.

End RC__1.
