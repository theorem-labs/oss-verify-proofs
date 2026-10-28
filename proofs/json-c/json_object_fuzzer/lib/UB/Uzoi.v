(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QKQo Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM UzWc UfOM UC8c UPZI Uu4M UtMn UG8z Udyh Ub4w ULbz Ua8x U2Sr UMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import UzWc UfOM.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0.
Import UPZI.Mq0 UPZI.Mq4 Uu4M.Mq0 UtMn.
Import QkMG.
Import UG8z Udyh.Mq0 Ub4w.
Import QKQo.
Import ULbz Ua8x.Mq3 U2Sr.
Import QfLs.Mq0.
Import ULbz.Mq0 UMdR.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeTop.
Variable HIx : heap_iface S4L.
Hypothesis PUT : put_stmt_P HIx.
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

Let SEG_ENTRY := ULbz.Mq0.seg_entry HIx USE ERRNO DUP NEWL FREEL.

Let PE_MASTER := UMdR.pe_master HIx PUT USE FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA.

Definition parse_ex_entry : Z := 0x21c38.
Definition PE_STK : Z := 144 + 12288.

#[using="Type"] Lemma pe_post_me : forall pf sv F fc md LBc me m1 lo ms' md',
heap_presx S4L xloc LBc (pf_spf pf + PE_FRAME) me m1 ->
pe_post_g HIx pf sv F fc md LBc m1 lo ms' md' -> pe_post_g HIx pf sv F fc md LBc me lo ms' md'.
Proof.
intros pf sv F fc md LBc me m1 lo ms' md' HX P.
destruct P as (m' & A' & gp & r & errv' & RBS & TBS & LK & RS & VM' & ST & ERR & LOC & HPR & REST).
exists m', A', gp, r, errv', RBS, TBS, LK. split; [exact RS|]. split; [exact VM'|]. split; [exact ST|]. split; [exact ERR|]. split; [exact LOC|].
split; [eapply heap_presx_trans; [exact HX | exact HPR] | exact REST].
Qed.

#[using="PUT USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf SEG_ENTRY PE_MASTER"] Lemma json_tokener_parse_ex_g_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (TBS LBc : list blk) (tk sb len lenr lo : Z) (payload slack : list byte) (errv : word) (mxd fl : Z),
HEAP S4L HIx A (TBS ++ LBc) m md ->
tok_fresh_g rsegs mxd fl m TBS tk ->
bytes_at rsegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_ok rsegs m LBc (bv_unsigned sp) sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> jc_glob_P m ->
bytes_at rsegs m UTF8REP_ADDR utf8rep ->
bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PE_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->
(forall ms' md', pe_post_g HIx (PEF tk LC_GLOBAL 0 len lenr sb (bv_unsigned sp - 144) md mxd fl) (PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc m lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 parse_ex_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until fl. intros HP TF STR PLEN LEN MODE SB0 SBL LOC LCK JCG UTF GOTF ST LO LOS SPA HT SP62 ERR TP RAE FRM A0 A1 A2 K.
unfold PE_STK in LOS.

assert (CSTR : lenr = len \/ nth_error payload (Z.to_nat (len - 1)) = Some (Z_to_bv 8 0)).
{ destruct MODE as [(-> & _) | (_ & _ & (str0 & Ep & _) & _)]; [left; reflexivity | right].
subst payload. rewrite length_app in PLEN. cbn [length pf_mxd] in PLEN.
rewrite nth_error_app2 by lia. replace (Z.to_nat (len - 1) - length str0)%nat with 0%nat by lia. reflexivity. }
assert (CPOS : lenr <> len -> 0 < len).
{ destruct MODE as [(-> & _) | (_ & _ & (str0 & Ep & _) & _)]; [intros NE; exfalso; exact (NE eq_refl) | intros _].
subst payload. rewrite length_app in PLEN. cbn [length pf_mxd] in PLEN. lia. }
eapply SEG_ENTRY;
[exact HP | exact TF | exact STR | exact PLEN | exact LEN | exact MODE | exact SB0 | exact SBL | exact LOC | exact LCK | exact JCG
| exact ST | exact LO | lia | exact SPA | exact HT | exact SP62 | exact ERR | exact TP | exact RAE | exact A0 | exact A1 | exact A2 | | exact K].
cbn zeta. intros newl q m1 md1 A1x pb pbs j1 j2 utf errv1 x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' t3' t4' t5' t6'
STC INV VM1 HPRX LOC1 NEWLR.
set (pf := PEF tk LC_GLOBAL newl len lenr sb (bv_unsigned sp - 144) md1 mxd fl) in *.
set (sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in *.

assert (UTF1 : bytes_at rsegs m1 UTF8REP_ADDR utf8rep).
{ eapply (heap_presx_bytes_at S4L); [exact HPRX | exact UTF |]. right; left. intros a Ha. unfold UTF8REP_ADDR in Ha. cbn in Ha.
cbn. unfold s4_client_static, xloc, s4_volatile, LOCCELL. lia. }
assert (GOTF1 : bytes_at rsegs m1 GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))).
{ eapply (heap_presx_bytes_at S4L); [exact HPRX | exact GOTF |]. right; left. intros a Ha. unfold GOT_free_userdata in Ha. rewrite length_le8 in Ha.
cbn. unfold s4_client_static, xloc, s4_volatile, LOCCELL. lia. }
assert (KRET : forall ms' md', pe_post_g HIx pf sv F fc md LBc m1 lo ms' md' -> realizes rsegs (mkCfg ms' md') T).
{ intros ms' md' P. apply K. eapply pe_post_me; [| exact P]. unfold pf; cbn [pf_spf pf_mxd]. unfold PE_FRAME.
replace (bv_unsigned sp - 144 + 144) with (bv_unsigned sp) by lia. exact HPRX. }
pose proof (PE_MASTER pf q LBc payload m1 lo sv T F fc md
STC eq_refl LOC1 ltac:(unfold pf; cbn [pf_newl pf_mxd]; lia) RAE UTF1 GOTF1 ltac:(unfold CSTR_OK, pf; cbn [pf_lenr pf_len pf_mxd]; exact CSTR) VM1 KRET
(HC_null pf q LBc payload m1 lo sv T F) (HC_bool pf q LBc payload m1 lo sv T F)
(HC_number pf q LBc payload m1 lo sv T F) (HC_inf pf q LBc payload m1 lo sv T F)
(S (16 * Z.to_nat len + 15))) as (KL & _ & _ & _).
eapply (KL (ts_init mxd pb pbs)); [| exact INV | cbv; discriminate | split; intros HH; cbv in HH; discriminate HH | | intros NE; unfold ts_init; cbn [t_co pf_mxd]; unfold pf in NE; cbn [pf_lenr pf_len pf_mxd] in NE; exact (CPOS NE) | apply fsaved_refl | exact FRM].
2:{
split; [| intros HH; cbv in HH; discriminate HH]. unfold ts_init. cbn [t_levels pf_mxd]. intros i l Hi.
pose proof (nth_error_Some_length Hi) as LT. cbn [length pf_mxd] in LT. rewrite repeat_length in LT.
assert (E : tl_cs l = None).
{ destruct i as [|i]; cbn [nth_error pf_mxd] in Hi; [injection Hi as <-; reflexivity|].
apply nth_error_In in Hi. apply (repeat_spec _ lvl_zero l) in Hi. subst l. reflexivity. }
rewrite E. cbn [odep pf_mxd]. pose proof (PE_STATIC_mxd _ _ _ STC) as MX; unfold pf in MX; cbn [pf_mxd pf_fl] in MX. lia. }
unfold mloop, mbase, ts_init. cbn [t_co pf_len pf pf_mxd]. lia.
Qed.

#[using="PUT USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf SEG_ENTRY PE_MASTER"] Lemma json_tokener_parse_ex_gen_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (TBS LBc : list blk) (tk sb len lenr lo : Z) (payload slack : list byte) (errv : word),
HEAP S4L HIx A (TBS ++ LBc) m md ->
tok_fresh rsegs m TBS tk ->
bytes_at rsegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_ok rsegs m LBc (bv_unsigned sp) sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> jc_glob_P m ->
bytes_at rsegs m UTF8REP_ADDR utf8rep ->
bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PE_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->
(forall ms' md', pe_post HIx (PEF tk LC_GLOBAL 0 len lenr sb (bv_unsigned sp - 144) md 32 0) (PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc m lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 parse_ex_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP TF STR PLEN LEN MODE SB0 SBL LOC LCK JCG UTF GOTF ST LO LOS SPA HT SP62 ERR TP RAE FRM A0 A1 A2 K.
eapply json_tokener_parse_ex_g_cps with (mxd := 32) (fl := 0);
[exact HP | apply (proj1 (tok_fresh_g32 rsegs m TBS tk)); exact TF | exact STR | exact PLEN | exact LEN | exact MODE
| exact SB0 | exact SBL | exact LOC | exact LCK | exact JCG | exact UTF | exact GOTF | exact ST | exact LO | exact LOS | exact SPA
| exact HT | exact SP62 | exact ERR | exact TP | exact RAE | exact FRM | exact A0 | exact A1 | exact A2 |].
intros ms' md' P. apply K. eapply pe_post_of_g32; [reflexivity | reflexivity | exact P].
Qed.

#[using="PUT USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf SEG_ENTRY PE_MASTER"] Lemma json_tokener_parse_ex_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (TBS LBc : list blk) (tk sb len lo : Z) (payload : list byte) (errv : word),
HEAP S4L HIx A (TBS ++ LBc) m md ->
tok_fresh rsegs m TBS tk ->
bytes_at rsegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
(len = 0 \/ In (sb, len) LBc) -> 0 <= sb -> sb + len < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> jc_glob_P m ->
bytes_at rsegs m UTF8REP_ADDR utf8rep ->
bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PE_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 len ->
(forall ms' md', pe_post HIx (PEF tk LC_GLOBAL 0 len len sb (bv_unsigned sp - 144) md 32 0) (PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc m lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 parse_ex_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP TF STR PLEN LEN SBin. intros.
eapply json_tokener_parse_ex_gen_cps; [exact HP | exact TF | exact STR | exact PLEN | exact LEN | exact (pe_arg_ok_explicit rsegs m LBc (bv_unsigned sp) sb len payload SBin) | eassumption ..].
Qed.

#[using="PUT USE ERRNO DUP NEWL FREEL MEMMOVE STRDUP AADD SHRINK OADD NEWO NEWA HC_null HC_bool HC_number HC_inf SEG_ENTRY PE_MASTER"] Lemma json_tokener_parse_ex_c_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (TBS LBc : list blk) (tk sb lo : Z) (str0 slack : list byte) (errv : word),
HEAP S4L HIx A (TBS ++ LBc) m md ->
tok_fresh rsegs m TBS tk ->
bytes_at rsegs m sb (str0 ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str0 -> Z.of_nat (length str0) < 2^26 - 1 ->
bytes_at rsegs m (sb + Z.of_nat (length str0) + 1) slack -> (- (sb + Z.of_nat (length str0) + 1)) mod 8 <= Z.of_nat (length slack) ->
bv_unsigned sp <= sb -> sb + Z.of_nat (length str0) + 1 < 2^63 ->
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> jc_glob_P m ->
bytes_at rsegs m UTF8REP_ADDR utf8rep ->
bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PE_STK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx -> bv_unsigned sp <= 2^62 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 (2^64 - 1) ->
(forall ms' md', pe_post HIx (PEF tk LC_GLOBAL 0 (Z.of_nat (length str0) + 1) (2^64 - 1) sb (bv_unsigned sp - 144) md 32 0)
(PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc m lo ms' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 parse_ex_entry) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until errv. intros HP TF STR NONUL LEN SLK PAD SPle SBL. intros.
pose proof (bytes_at_bound _ _ _ _ STR) as B0.
eapply json_tokener_parse_ex_gen_cps with (len := Z.of_nat (length str0) + 1) (slack := slack);
[exact HP | exact TF | exact STR | rewrite length_app; cbn [length pf_mxd]; lia | lia | | lia | lia | eassumption ..].
right. split; [reflexivity|]. split; [exact SPle|]. split; [exists str0; split; [reflexivity | exact NONUL]|].
replace (sb + (Z.of_nat (length str0) + 1)) with (sb + Z.of_nat (length str0) + 1) by lia. split; [exact SLK | exact PAD].
Qed.

End PeTop.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMdR.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Utqc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Utqc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UClN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UClN.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Jo Require JoNewDbl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Import Tk1Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk2 Require Import Tk2Gen.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma strncasecmp_walk_range : forall l r k, -300 <= strncasecmp_walk l r k <= 300.
Proof.
induction l as [|a l IH]; intros [|b r] k; cbn [strncasecmp_walk pf_mxd]; try lia.
- pose proof (lower8_range _ (byte_range8 a)). lia.
- pose proof (lower8_range _ (byte_range8 a)). pose proof (lower8_range _ (byte_range8 b)).
destruct (_ || _)%bool; [lia|]. destruct k; [lia | apply IH].
Qed.
#[using="Type"] Lemma strncasecmp_model_range : forall ls rs n, -300 <= strncasecmp_model ls rs n <= 300.
Proof. intros. unfold strncasecmp_model. destruct (n =? 0); [lia | apply strncasecmp_walk_range]. Qed.
#[using="Type"] Lemma strncmp_walk_range : forall l r k v, strncmp_walk l r k = Some v -> -300 <= v <= 300.
Proof.
induction l as [|a l IH]; intros [|b r] k v H; cbn [strncmp_walk pf_mxd] in H; try discriminate H.
pose proof (byte_range8 a). pose proof (byte_range8 b).
destruct (_ || _)%bool; [injection H as <-; lia|]. destruct k; [injection H as <-; lia | eapply IH; exact H].
Qed.
#[using="Type"] Lemma strncmp_model_range : forall l r n v, strncmp_model l r n = Some v -> -300 <= v <= 300.
Proof. intros l r n v. unfold strncmp_model. destruct (n =? 0); [intros H; injection H as <-; lia | apply strncmp_walk_range]. Qed.
#[using="Type"] Lemma eqb64_0_false : forall v, -300 <= v <= 300 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
intros v Hv Hn. unfold bv_eqb. apply Z.eqb_neq. rewrite (unsigned_lit 0) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. intros E. apply Hn.
destruct (Z.lt_ge_cases v 0); [| rewrite Z.mod_small in E by (cbn; lia); exact E].
replace v with ((v + 2^64) - 1 * 2^64) in E by lia. cbn in E. lia.
Qed.

Section PeNull.
Variable HIx : heap_iface S4L.
Hypothesis MEMMOVE : memmove_stmt.
#[using="MEMMOVE"] Lemma case_null : forall (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte),
CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_null.
Proof.
intros pf q LBc payload me lo sv T F0 utf8rep.
unfold CASE. intros n ts l m md A cb j1 j2 utf errv x1 gp t0 t1 t2 a3 a4 a5 a6 a7 s6 s7 s8 s10 t3 t4 t5 t6 F fc.
change (pe_jt ST_null) with 140044.
intros STC INV Hl Hst Hco Hcb NUM SP TDOK UTF GOTF CSTR FS FRM Mn (KL & KR & KB & KB2) KO7 KE7.
pose proof (KERR_of_7 _ _ _ _ _ _ _ _ _ _ KE7) as KE.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
pose proof CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.

assert (SPB : SPV (t_x ts) <= t_co ts) by (unfold SPOK in SP; pose proof (proj1 SP) as SP1; specialize (SP1 ltac:(unfold cur_st; rewrite Hl, Hst; reflexivity)); lia).
assert (SP0' : 0 <= SPV (t_x ts)) by (unfold SPV; apply Z.mod_pos_bound; lia).
revert INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE SPB SP0'.
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
intros INV NUM SP TDOK Mn KL KR KB KB2 KO7 KE7 KE SPB SP0'.
unfold LB0 in *. cbn [pf_newl pf_mxd] in *.
unfold SPV in SPB, SP0'. cbn [ts_stpos pf_mxd] in SPB, SP0'. set (sp := bv_unsigned stpos mod 2^32) in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_frame in FR. unfold pe_ms. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl]. unfold_consts.

assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs)))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) (proj1 REST) INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 (proj1 REST) INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ (proj1 REST)) as ND. unfold pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_tk pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) (proj1 REST) INtk INq Htq) as Hdtq.
stash Himg_t. clear INtk INq.

pose proof (proj1 (proj2 REST) depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & JO & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. destruct (null_mode _ _ _ SS26 Hmode) as [-> ->].
cbn [name_ok pf_mxd] in NM0. destruct NM0 as [Hn0 Hnbs0].
destruct (tl_cs l) as [s0c|] eqn:Ecs; [exfalso; exact CLS0|]. cbn [jopt pf_mxd] in JO. destruct JO as [Hc0 Hcbs0].
assert (Eobjbs : objbs = []).
{ generalize (proj1 (proj2 (proj2 REST))). unfold cur_st. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
subst objbs. clear LVd CLS0 Hmode.

assert (TDX : forall co' pb' pbs' x' obj' objbs', tdepth_ok (TST depth levels co' pb' pbs' x' obj' objs objbs'))
by (intros; eapply tdepth_ok_same; [reflexivity | reflexivity | reflexivity | exact TDOK]).
clear PB TSK REST CORE.
apply rz_evt; [exact MOK|].
step. step. step. step.
apply evt_RZ_done.
eapply (pe_mapp HIx MEMMOVE (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo m md A
(TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) co 0x2231c (spf + 31) 1 [cb] cb);
[exact STC | exact INV | exact (pe_frame_cbyte _ _ _ _ _ _ _ _ FR) | reflexivity | lia | left; cbn [pf_spf pf_mxd]; unfold PE_FRAME; lia | reflexivity | lia |].
unfold ts_set_pbs; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_oldl pf_newl pf_len pf_sb pf_tk pf_spf pf_md pf_mxd pf_fl].
clear TOK FR MOK INV NUM. clear m.
intros m md1 A1 pbs1 errv1 r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 INV Hr FS1 FRM1.
unfold pe_ms; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl].
assert (FS1' : fsaved F0 F1) by (eapply fsaved_trans; [exact FS | exact FS1]). specialize (FRM1 FRM). clear FS FS1 FRM F fc.
pose proof INV as [CORE REST].
pose proof CORE as (_ & _ & _ & _ & TOK & PB & _ & TSK & FR).
cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj pf_tk pf_spf pf_mxd] in TOK, PB, TSK, FR.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 REST)) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 REST)) as MI. cbn [hl_segs S4L pf_mxd] in MI.
apply rz_evt; [exact MOK|].
destruct Hr as [-> | ->].
2:{
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. if_false. step. step. step. apply evt_RZ_done.
eapply KE; [apply (PE_INV_W HIx); exact INV | apply TDX | exact FS1' | exact FRM1]. }
step. if_true.

unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
step. rewrite (sx32_small_mod stpos) by lia. fold sp.
step. norm_w32.
set (nz := Z.min (sp + 1) 4). set (n3 := Z.min (sp + 1) 3).

assert (PART : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s9x s10x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (sb + co)) s6x s7x s8x s9x s10x (Z_to_bv 64 79040) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x23078) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s9x s10x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof (wmono_refl rsegs mX) as WMX. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] mX) as MUX.
apply rz_evt; [exact MOKX|]. step. step. apply evt_RZ_done.
eapply (KB (TST depth levels co pb pbsX (TS isd (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 co) err ucs high quote) obj objs [])); clear KL KR KB KB2 KO7 KE7 KE.
- unfold mbrk, mredo, mbase in *. unfold cur_st, cur_ss in Mn. cbn [t_co t_levels t_depth pf_len pf_mxd] in *. rewrite Hl, Hst in Mn. unfold rank in Mn. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn. lia.
- eapply (PE_INV_retok HIx _ q _ payload me lo mX _ mdX AX (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
[exact STC | exact INVX | exact MUX | exact WMX | exact MIX | exact TOKX | cbn; lia | reflexivity | exact FRX].
- cbn; lia.
- exact Hcb.
- unfold cur_st; cbn [t_levels t_depth pf_mxd]; rewrite Hl, Hst; discriminate.
- unfold SPOK, SPV; cbn [t_x ts_stpos t_co pf_mxd]. split; [intros _; rewrite spv_lit by lia; lia | unfold cur_st; cbn [t_levels t_depth]; rewrite Hl, Hst; cbn; intros E; discriminate E].
- apply TDX.
- exact FSX.
- exact FRMX. }

assert (FINN : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x s10x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4x (Z_to_bv 64 (sb + co)) s6x s7x s8x s9x s10x (Z_to_bv 64 79040) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x2285c) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x s10x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & STX & ERRX & _).
pose proof (srec_join8 _ _ _ (TSKX depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
pose proof (wmono_refl rsegs mX) as WMX. pose proof (munch_refl [(bse, bse + 32)] mX) as MUX.
stash TSKX. stash STX. stash ERRX. stash HPX. clear RESTX.
apply rz_evt; [exact MOKX|].
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bstz. bst. step. stepz. step.
unstash TSKX. unstash STX. unstash ERRX. unstash HPX.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done.
eapply (KR (TST depth (lupd levels depth (TL ST_eatws ST_finish 0 None [] 0 [])) co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
clear KL KR KB KB2 KO7 KE7 KE.
- unfold mredo, mbase, cur_st, cur_ss in Mn |- *. cbn [t_co t_levels t_depth pf_len pf_mxd] in Mn |- *. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst in Mn.
cbn [tl_st tl_ss pf_mxd]. unfold rank in Mn |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn |- *. lia.
- lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (setcur_inv HIx _ q _ payload me lo mX mX mc mdX mdX AX AX (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) l
cb j1 j2 utf sv errvX errvX [] 0 None bse);
[ exact STC | exact INVX | exact Hl | exact Hc0 | exact Hcbs0 | exact Hn0 | exact Hnbs0 | reflexivity
| apply heap_pres_refl | apply model_vm_only_refl | cbn [app pf_mxd]; exact HPX | exact STX | exact ERRX
| cbn; split; reflexivity | exact Hbse | exact MUX | exact WMX | assumption | exact L5 | eassumption | eassumption ]
end.
- cbn; lia.
- exact Hcb.
- unfold NUMC, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
- unfold SPOK, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; split; intros E; discriminate E.
- eapply (tdepth_ok_upd (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])); [apply TDX | exact Hl | rewrite Ecs; cbn; lia | cbn; lia | reflexivity].
- exact FSX.
- exact FRMX. }

assert (FINNAN : forall mX mdX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x s10x : word) FX fcX,
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX mdX AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
fsaved F0 FX -> frm0 fcX ->
realizes rsegs (mkCfg (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4x (Z_to_bv 64 (sb + co)) s6x s7x s8x s9x s10x (Z_to_bv 64 79040) t3x t4x t5x t6x)
FX (Z_to_bv 64 0x22834) fcX None mX (seg_rom rsegs)) mdX) T).
{ intros mX mdX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x s10x FX fcX INVX FSX FRMX.
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & TSKX & FRX)] RESTX].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX, TSKX. unfold pe_frame in FRX.
pose proof (heap_model_ok _ _ _ _ _ _ (proj1 RESTX)) as MOKX.
pose proof (heap_mem_inv _ _ _ _ _ _ (proj1 RESTX)) as MIX. cbn [hl_segs S4L pf_mxd] in MIX.
pose proof RESTX as (HPX & _ & _ & STX & ERRX & _). cbn [pf_spf pf_mxd] in STX.
pose proof (nan_ro mX MIX) as NANRO.
apply rz_evt; [exact MOKX|].
step. step. step. step.
apply evt_RZ_done.
eapply (JoNewDbl.json_object_new_double_cps HIx) with (LB := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) (lo := lo);
[ exact HPX | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STX | exact ERRX]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
{ unfold dbl_special; rewrite reg_get_set_same_u by (vm_compute; reflexivity); apply Z.leb_le; vm_compute; reflexivity. }
clear TOKX FRX NANRO MOKX.
intros ms2 md2 (m2 & A2 & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (FS2' : fsaved F0 F2) by (eapply fsaved_trans; [exact FSX | eapply fsaved_trans; [apply fsaved_set10 | exact FS2]]).
specialize (FRM2 FRMX).
pose proof INVX as [[_ (_ & _ & _ & TOKX & _ & _ & _ & FRX)] _].
unfold tok_cells, tok_cells_g in TOKX. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_spf pf_mxd] in TOKX, FRX. unfold pe_frame in FRX.
assert (INtk2 : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq2 : In (q, (32 * mxd)) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FRX; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FRX.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOKX; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOKX.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSKX; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSKX.
pose proof (srec_join8 _ _ _ (TSKX depth l Hl)) as Ld. cbn [le4 Z_to_le_bytes app hl_segs S4L pf_mxd] in Ld. rewrite Hc0, Hn0 in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (Hbal : bse mod 16 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).

assert (OUT' : exists A2' NB, HEAP S4L HIx A2' (NB ++ pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])) m2 md2 /\
((r = 0 /\ NB = []) \/ (r <> 0 /\ jval rsegs S4F (Sdouble false) m2 NB r 1))).
{ destruct OUT as [(-> & HP2) | (Hr & NB & J2 & HP2)].
- exists A2, []. split; [exact HP2 | left; split; reflexivity].
- exists A2, NB. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2' & NB & HP2 & OUT).
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L pf_mxd] in MI2.
pose proof (wmono_refl rsegs m2) as WM2. pose proof (munch_refl [(bse, bse + 32)] m2) as MU2.
stash TSKX. stash ST2. stash ERR2. stash HP2.
reenter MOK2.
step. norm_sx32. step.
step. rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
step. replace (q + Z.of_nat depth * 32) with bse by lia.
bstz.
unstash TSKX. unstash ST2. unstash ERR2. unstash HP2.
destruct OUT as [[-> ->] | [Hr J2]].
-
bst. if_false. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse (?c1 :: ?rest) |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [c1] [C4 (Z_to_bv 64 (tl_st l)); C4 (Z_to_bv 64 (tl_ss l))]
rest L8 ltac:(cbn; repeat split) eq_refl eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done. eapply KE; [ | apply TDX | exact FS2' | exact FRM2]. clear KL KR KB KB2 KO7 KE7 KE.
apply (PE_INV_W HIx).
lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (keep_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' _ l cb j1 j2 utf sv errvX errv2 bse);
[ exact STC | exact INVX | exact Hl | exact Hcbs0 | exact Hnbs0 | exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| exact Hbse | exact MU2 | exact WM2 | assumption | unfold srec_cells; rewrite Hc0, Hn0; exact L5 | eassumption | eassumption ]
end.
-
assert (HrR : 0 < r < 2^64).
{ destruct J2 as (pbp & PBS & RB & ENB & OPB & bits & ERB & DS & CELLS).
pose proof (heap_blk S4L HIx _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; rewrite ENB, ERB; left; reflexivity)) as (_ & _ & HB1 & HB2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in HB2. lia. }
bst. if_truex.
step. step. stepz. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with L8 : rw_cells rsegs mc bse _ |- _ =>
pose proof (rw_cells_recast_prefix rsegs mc bse [C8 (Z_to_bv 64 8589934592)] [C4 (Z_to_bv 64 ST_eatws); C4 (Z_to_bv 64 ST_finish)]
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0)] L8 ltac:(cbn; repeat split)
ltac:(apply bytes_eq_by_unsigned; vm_compute; reflexivity) eq_refl) as L5; cbn [app pf_mxd] in L5
end end.
apply evt_RZ_done.
eapply (KR (TST depth (lupd levels depth (TL ST_eatws ST_finish r (Some (Sdouble false)) NB 0 [])) co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []));
clear KL KR KB KB2 KO7 KE7 KE.
+ unfold mredo, mbase, cur_st, cur_ss in Mn |- *. cbn [t_co t_levels t_depth pf_len pf_mxd] in Mn |- *. rewrite nth_error_lupd_eq by lia. rewrite Hl, Hst in Mn.
cbn [tl_st tl_ss pf_mxd]. unfold rank in Mn |- *. cbn -[Nat.mul Nat.add Z.to_nat Z.sub] in Mn |- *. lia.
+ lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
eapply (setcur_inv HIx _ q _ payload me lo mX m2 mc mdX md2 AX A2' (TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) l
cb j1 j2 utf sv errvX errv2 NB r (Some (Sdouble false)) bse);
[ exact STC | exact INVX | exact Hl | exact Hc0 | exact Hcbs0 | exact Hn0 | exact Hnbs0 | reflexivity
| exact HPR2 | exact VM2 | cbn [app pf_mxd] in HP2; exact HP2 | exact ST2 | exact ERR2
| cbn [jres pf_mxd]; split; [exact Hr | exact J2] | exact Hbse | exact MU2 | exact WM2 | assumption | exact L5 | eassumption | eassumption ]
end.
+ cbn; lia.
+ exact Hcb.
+ unfold NUMC, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; intros E; discriminate E.
+ unfold SPOK, cur_st; cbn [t_levels t_depth pf_mxd]; rewrite nth_error_lupd_eq by lia; cbn; split; intros E; discriminate E.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])); [apply TDX | exact Hl | rewrite Ecs; cbn; lia | cbn; lia | reflexivity].
+ exact FS2'.
+ exact FRM2. }

assert (JOIN : evt rsegs (RZ rsegs md1 T) (MS (mkR (Z_to_bv 64 0x2231c) (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl) (Z_to_bv 64 3) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.min (sp + 1) 3)) (Z_to_bv 64 (Z.min (sp + 1) 4)) s8 (Z_to_bv 64 sp) s10 (Z_to_bv 64 PE_JTAB) t3' t4' t5' t6') F1 (Z_to_bv 64 0x22354) fc1 None m (seg_rom rsegs))).
2:{ step. if_truex. step. step.
destruct (Z.lt_ge_cases sp 3) as [Hs3|Hs3].
- step. if_truex. step. step.
destruct (Z.lt_ge_cases sp 2) as [Hs2|Hs2].
+ step. if_truex. replace (Z.min (sp + 1) 4) with (sp + 1) in JOIN by lia. replace (Z.min (sp + 1) 3) with (sp + 1) in JOIN by lia. exact JOIN.
+ step. if_falsex. step. replace (Z.min (sp + 1) 4) with (sp + 1) in JOIN by lia. replace (Z.min (sp + 1) 3) with 3 in JOIN by lia. exact JOIN.
- step. if_falsex. step. step. step. step. if_falsex. step.
replace (Z.min (sp + 1) 4) with 4 in JOIN by lia. replace (Z.min (sp + 1) 3) with 3 in JOIN by lia. exact JOIN. }
subst nz n3. set (nz := Z.min (sp + 1) 4). set (n3 := Z.min (sp + 1) 3).

pose proof (pbuf_cstr m pbs1 pb PB) as (buf & bpos & cap & str & rest & Epbs & Hbpos & Hcap & PBH & BUFS & NIN & Lstr & Lcap).
pose proof REST as (HP & _ & _ & ST & _).
assert (INbuf : In (buf, cap) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
assert (INpb : In (pb, 16) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) (TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs [])))
by (unfold pe_blocks, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & _ & Hbuflo & Hbufhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi, Hpbhi.
replace (str ++ b0 :: rest) with ((str ++ [b0]) ++ rest) in BUFS by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in BUFS. destruct BUFS as [BUFZ _].
clear INbuf INpb HP.

assert (BLK4 : forall mX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (sb + co)) s6x s7x s8x (Z_to_bv 64 sp) s10x (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x22854) fc1 None mX (seg_rom rsegs))).
{ intros mX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x INVX.
step. destruct (Z.eq_dec sp 4) as [E4|N4].
- step. if_falsex. apply evt_RZ_done. eapply FINN; [exact INVX | exact FS1' | exact FRM1].
- step. if_truex. apply evt_RZ_done. eapply PART; [exact INVX | exact FS1' | exact FRM1]. }
assert (BLK3 : forall mX AX pbsX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbsX (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (sb + co)) s6x s7x s8x (Z_to_bv 64 sp) s10x (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x2282c) fc1 None mX (seg_rom rsegs))).
{ intros mX AX pbsX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s6x s7x s8x s10x INVX.
step. destruct (Z.eq_dec sp 3) as [E3|N3].
- step. if_falsex. apply evt_RZ_done. eapply FINNAN; [exact INVX | exact FS1' | exact FRM1].
- step. if_truex. apply evt_RZ_done. eapply PART; [exact INVX | exact FS1' | exact FRM1]. }

assert (NANCMP : forall mX AX errvX (x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s7x s10x : word),
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q ((newl, 48) :: LBc) payload me lo mX md1 AX
(TST depth levels co pb pbs1 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs []) cb j1 j2 utf sv errvX ->
stk rsegs mX lo spf -> bytes_at rsegs mX buf (str ++ [b0]) -> mem_inv rsegs mX ->
evt rsegs (RZ rsegs md1 T) (MS (mkR x1x (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0x t1x t2x (Z_to_bv 64 tk) (Z_to_bv 64 oldl) a0x a1x a2x a3x a4x a5x a6x a7x
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 (sp + 1)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 n3) s7x (Z_to_bv 64 buf) (Z_to_bv 64 sp) s10x (Z_to_bv 64 PE_JTAB) t3x t4x t5x t6x)
F1 (Z_to_bv 64 0x22810) fc1 None mX (seg_rom rsegs))).
{ intros mX AX errvX x1x a0x a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s7x s10x INVe STe BUFZe MIe.
step. step. step. step. step.
pose proof (nan_bytes mX MIe) as NANS. destruct (strncmp_model_cstr nanstr str n3) as [v4 Hv4].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NANS | rewrite unsigned_lit by lia; exact BUFZe | rewrite unsigned_lit by lia; exact Hv4 | exact MIe] |].
intros ms' POST; destruct POST as (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m4' & -> & MUf & WMf & MIf & _ & _).
replace (ret_pc (Z_to_bv 64 0x22824)) with (Z_to_bv 64 0x22824) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ STe MUf WMf I) as STf.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVe MUf WMf MIf ltac:(apply Forall_nil) STf) as INVf.
pose proof (strncmp_model_range _ _ _ _ Hv4) as Rv4.
clear INVe STe BUFZe NANS MIe MUf WMf Hv4.
destruct (Z.eq_dec v4 0) as [Ev4 | Nv4].
{ rewrite Ev4. step. if_true. eapply BLK3; exact INVf. }
step. if_false_by (eqb64_0_false v4 Rv4 Nv4).

step. step. step.
apply evt_RZ_done.
eapply (KE7 _ [] co (Z_to_bv 64 5)); [apply (PE_INV_W HIx); exact INVf | apply TDX | exact FS1' | exact FRM1]. }

step. step. step. step.
lazymatch goal with |- context [zx32 (Z_to_bv 64 ?y)] => change y with fl end.
replace (zx32 (Z_to_bv 64 fl)) with (Z_to_bv 64 fl) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
rewrite (unsigned_lit fl) by lia.
clear TOK FR PB TSK CORE REST MOK.
destruct (land1_cases fl) as [FL1|FL1]; rewrite FL1.
-
step. if_false.
bst.
step. step. step. step.

pose proof (null_bytes m MI) as NULLS.
eapply evt_cut; [eapply strncasecmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZ | exact nonul_null | exact NIN | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | rewrite !unsigned_lit by lia; left; cbn; lia | rewrite !unsigned_lit by lia; left; lia | exact MI] |].
intros ms' POST; destruct POST as (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' & -> & MUc & WMc & MIc & Ea0 & STc & _ & BUFZc).
rewrite ?unsigned_lit in MUc by lia. rewrite ?unsigned_lit in STc by lia. rewrite ?unsigned_lit in BUFZc by lia. rewrite ?unsigned_lit in Ea0 by lia.
replace (ret_pc (Z_to_bv 64 0x2238c)) with (Z_to_bv 64 0x2238c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV MUc WMc MIc ltac:(apply Forall_cons; [cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]) STc) as INVc.
assert (PBHc : rw_cells rsegs m' pb [C8 (Z_to_bv 64 buf); C4 (Z_to_bv 64 bpos); C4 (Z_to_bv 64 cap)]).
{ eapply rw_cells_transport; [exact PBH | exact MUc | exact WMc |]. cbn [disjoint_from cells_size csize Nat.add]. split; [left; lia | exact I]. }
subst a0c. pose proof (strncasecmp_model_range nullstr str nz) as Rv1. set (v1 := strncasecmp_model nullstr str nz) in *.
clear INV ST BUFZ NULLS MI PBH.
destruct (Z.eq_dec v1 0) as [Ev1 | Nv1].
{ rewrite Ev1. step. if_true. eapply BLK4; exact INVc. }
step. if_false_by (eqb64_0_false v1 Rv1 Nv1).
step. step.
bst.
step. step. step. step. step.

pose proof (null_bytes m' MIc) as NULLS. destruct (strncmp_model_cstr nullstr str nz) as [v2 Hv2].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZc | rewrite unsigned_lit by lia; exact Hv2 | exact MIc] |].
intros ms' POST; destruct POST as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m2' & -> & MUd & WMd & MId & _ & BUFZd).
rewrite ?unsigned_lit in BUFZd by lia.
replace (ret_pc (Z_to_bv 64 0x227f0)) with (Z_to_bv 64 0x227f0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ STc MUd WMd I) as STd.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVc MUd WMd MId ltac:(apply Forall_nil) STd) as INVd.
pose proof (strncmp_model_range _ _ _ _ Hv2) as Rv2.
clear INVc STc BUFZc NULLS MIc MUd WMd MUc WMc Hv2 PBHc.
destruct (Z.eq_dec v2 0) as [Ev2 | Nv2].
{ rewrite Ev2. step. if_true. eapply BLK4; exact INVd. }
step. if_false_by (eqb64_0_false v2 Rv2 Nv2).
step. if_false.
step. step. step. step. step.

pose proof (nan_bytes m2' MId) as NANS.
eapply evt_cut; [eapply strncasecmp_spec; [rewrite unsigned_lit by lia; exact NANS | rewrite unsigned_lit by lia; exact BUFZd | exact nonul_nan | exact NIN | rewrite unsigned_lit by lia; exact STd | rewrite unsigned_lit by lia; lia | rewrite !unsigned_lit by lia; left; cbn; lia | rewrite !unsigned_lit by lia; left; lia | exact MId] |].
intros ms' POST; destruct POST as (t0e & t1e & t2e & a0e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m3' & -> & MUe & WMe & MIe & Ea0 & STe & _ & BUFZe).
rewrite ?unsigned_lit in MUe by lia. rewrite ?unsigned_lit in STe by lia. rewrite ?unsigned_lit in BUFZe by lia. rewrite ?unsigned_lit in Ea0 by lia.
replace (ret_pc (Z_to_bv 64 0x2280c)) with (Z_to_bv 64 0x2280c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVd MUe WMe MIe ltac:(apply Forall_cons; [cbn [fst snd pf_spf pf_mxd]; lia | apply Forall_nil]) STe) as INVe.
subst a0e. pose proof (strncasecmp_model_range nanstr str n3) as Rv3. set (v3 := strncasecmp_model nanstr str n3) in *.
clear INVd STd BUFZd NANS MId.
destruct (Z.eq_dec v3 0) as [Ev3 | Nv3].
{ rewrite Ev3. step. if_true. eapply BLK3; exact INVe. }
step. if_false_by (eqb64_0_false v3 Rv3 Nv3).
eapply NANCMP; [exact INVe | exact STe | exact BUFZe | exact MIe].
-
step. if_true.
bst.
step. step. step. step. step.

pose proof (null_bytes m MI) as NULLS. destruct (strncmp_model_cstr nullstr str nz) as [v2 Hv2].
eapply evt_cut; [eapply strncmp_spec; [rewrite unsigned_lit by lia; exact NULLS | rewrite unsigned_lit by lia; exact BUFZ | rewrite unsigned_lit by lia; exact Hv2 | exact MI] |].
intros ms' POST; destruct POST as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m2' & -> & MUd & WMd & MId & _ & BUFZd).
rewrite ?unsigned_lit in BUFZd by lia.
replace (ret_pc (Z_to_bv 64 0x227f0)) with (Z_to_bv 64 0x227f0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (stk_transport_disjoint rsegs [] _ _ _ _ ST MUd WMd I) as STd.
pose proof (PE_INV_stackw HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV MUd WMd MId ltac:(apply Forall_nil) STd) as INVd.
pose proof (strncmp_model_range _ _ _ _ Hv2) as Rv2.
clear INV ST BUFZ NULLS MI MUd WMd Hv2 PBH.
destruct (Z.eq_dec v2 0) as [Ev2 | Nv2].
{ rewrite Ev2. step. if_true. eapply BLK4; exact INVd. }
step. if_false_by (eqb64_0_false v2 Rv2 Nv2).
step. if_true.
eapply NANCMP; [exact INVd | exact STd | exact BUFZd | exact MId].
Qed.
End PeNull.

End RC__1.
