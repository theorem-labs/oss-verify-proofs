(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH Q0Ek Q7UD Qhd4 Qwm6 QgHv Q9O6 QlKV Q228 QiVi QicC QFrL Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek.
Import Q7UD Qhd4 Qwm6.Mq0 QgHv.Mq0 Q9O6.Mq2 QlKV.Mq6 Q228.Mq0 QiVi.Mq0 QicC.Mq0 QFrL.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem json_escape_str_A : esc_specA HIx.
Proof.
apply esc_specA_of_al.
- exact (json_escape_str_A_0 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).
- exact (json_escape_str_A_16 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).
Qed.
End Esc.
End RC__1.
End Mq0.
From Stdlib Require NArith Lia Bool.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QZAi Qx2n QsKa Qw5U QJVP Q6VZ QKvs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QZAi.Mq1 Qx2n.
Import Q7UD Qwm6.Mq0 QsKa.Mq0 Qw5U.Mq3.

Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Module PS := QJVP.Mq0.
Module PT := Q6VZ.Mq0.
Module PH := QKvs.Mq0.
Import ListNotations.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint img_w_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match wview asegs (fun _ => None) (wa A) with Some _ => img_w_b (A + 1) n' | None => false end
end.
Lemma img_w_b_sound : forall n A (m : word -> option byte), img_w_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at asegs m A (Z.of_nat n).
Proof.
intros n A m Hb HA Hhi. split; [exact HA|]. split; [exact Hhi|]. revert A Hb HA Hhi.
induction n as [|n IH]; intros A Hb HA Hhi i Hi; [lia|]. cbn [img_w_b] in Hb.
destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate|]. cbn beta in Ew. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) Hb); lia.
Qed.

Lemma rw_c8_of_bytes : forall (m : word -> option byte) A (v : word),
bytes_at asegs m A (le8 v) -> img_w_b A 8 = true -> rw_cells asegs m A [C8 v].
Proof.
intros m A v B W. pose proof (bytes_at_bound _ _ _ _ B) as Bd. rewrite length_le8 in Bd.
split.
- split; [repeat constructor|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
- apply (img_w_b_sound 8 A m W); lia.
Qed.

Theorem astrtod_total_proof : astrtod_total_stmt.
Proof.
unfold astrtod_total_stmt. intros until ev. intros BY BYT Htxt Hlen Hlt PEC HS ST LO GT SPH Tpos T47 HT PE0 PE47 HPE SEPE GOTG GUA ERR MI FRM Htp Ha0 Ha1.
pose proof (PH.rstrtod_total_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
T PE txt pre post bits used ejunk lo canary ev) as X.
unfold A_TP, A_GOT_GUARD, A_GUARD, ASTRTOD_DEPTH, A_STRTOD in *.
unfold PS.RSTRTOD_DEPTH, PS.RGLOBALS_TOP, PS.RIMG_LO, PS.RATP, PS.RERRNO, PS.RSTRTOD, PS.ssp_cells, PS.got_ssp, PS.ssp_guard in X.
unfold zlength in *. change QTp6.rsegs with asegs in X.
eapply evt_mono; [eapply X; first [assumption | lia | idtac] |].
- split; apply rw_c8_of_bytes; first [assumption | vm_compute; reflexivity].
- intros ms' P. unfold PS.rstrtod_post in P.
destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & ev' & -> & MU & WM & MI' & FR' & FK & FA & ST' & PE' & BY' & SSP' & ERR' & US).
unfold astrtod_post, A_TP. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m', ev'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FR'|]. split; [exact FK|]. split; [exact FA|].
split; [exact ST'|]. split; [exact PE'|]. split; [exact BY'|]. split; [exact ERR'|]. exact US.
Qed.

Theorem scan_total_proofA : scan_total_stmtA.
Proof. exact PH.scan_strtod_h_total_proof. Qed.
End RC__1.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply QWxq_c1 QRjH QHnV QfLs Qtgi QjDH Qsw7 QJjn QRUw QkMG Qu4M QG8z Qdyh QLbz Q2Sr Qa8x Qiiq Q4v2 Qoif Q1Ey Ql4f Q1Y6 QGdd QcmL QrQv QEUF QJZd QW22 QnDr Qmgs QdGy QWrz QV7s QQ2r QtyQ Q8H8 QQPy QFZX Q63E Q6oO Qvmy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3 QLbz.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 QsKa.Mq5 Qoif.Mq0 QlKV.Mq4 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QGdd QcmL.Mq0 QrQv.Mq2 QEUF QJZd.Mq8 QW22.Mq3 QnDr.Mq2 Qmgs QdGy.Mq5 QWrz.Mq1 QV7s QQ2r.Mq2 QtyQ.Mq2 QtyQ.Mq3 Q8H8.Mq0 QQ2r.Mq4 QFrL.Mq1 QQPy.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QsKa.Mq0 QFZX.Mq4 QFZX.Mq3 Q63E.Mq6.
Import Q6oO.Mq0 Q63E.Mq7.
Import Qvmy.Mq0 QW22.Mq0 QV7s.Mq1.
Import QlKV.Mq2 QEUF.Mq1 QnDr.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSTop2.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa39f8.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa3c68.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9c330.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9c9d4.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Lemma ISTRLEN : istrlen_spec_U.
Proof.
unfold istrlen_spec_U. intros until Q. intros UP RT H0 H47 H40 HAPP HLO Ha0 NONUL STR PAD ST LO LOS SPA MI RA K.
apply (astrlen_sound_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a lo s slack Q
UP RT H0 H47 HLO Ha0 NONUL H40); try assumption.
- destruct (Z.le_gt_cases (Z.of_nat (length s)) 63) as [L|G]; [left; exact L| right; apply HAPP; lia].
- intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' _ ST'. exact (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST').
Qed.

Lemma RTC_PEPC : rtc_pepc_stmt HIx.
Proof.
intros A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R. rewrite Forall_forall in R.
refine (R (A_GOT_PEPC, le8 (Z_to_bv 64 A_PE_ENTRY)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts, A_GOT_PEPC, A_PE_ENTRY.
repeat (first [left; reflexivity | right]).
Qed.
Lemma OBL_ERRNO : heapA_errno_stmt HIx.
Proof. intros A LB LM FR B m md HP. exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HP). Qed.

Lemma OBL_SH_ERRNO : sh_errno_stmt HIx.
Proof.
intros A LB LM FR B m md HP.
pose proof (heapA_shadow_img A4L HIx A LB LM FR B m md (A_ERRNO / 8) HP) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (A_ERRNO / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
apply X; vm_compute; discriminate.
Qed.

Definition pe_N0 (len : Z) : nat := (16 * Z.to_nat len + 15)%nat.

Definition pe_A0 (len : Z) : nat := (pe_N0 len + Z.to_nat ((16 * Z.max 0 len + 11008) * len + (2 * (16 * Z.max 0 len + 8192) + 1792)))%nat.

Lemma pe_post_A_me : forall pf pa sv F fc md md1 LBc LM FRS me m1 lo ms' md' A',
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
pe_post_A HIx GA pf pa sv F fc md1 LBc LM FRS m1 lo ms' md' A' -> pe_post_A HIx GA pf pa sv F fc md LBc LM FRS me lo ms' md' A'.
Proof.
intros pf pa sv F fc md md1 LBc LM FRS me m1 lo ms' md' A' HX VM P.
destruct P as (m' & gp & r & errv' & RBS & TBS & LK & B' & RS & VM' & ST & ERR & LOC & HPR & REST).
exists m', gp, r, errv', RBS, TBS, LK, B'. split; [exact RS|]. split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact ST|]. split; [exact ERR|]. split; [exact LOC|].
split; [eapply heap_presx_trans; [exact HX | exact HPR] | exact REST].
Qed.

Theorem json_tokener_parse_ex_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (TBS LBc LM : list blk) (FRS : list frame) (B : bud) (tk sb len lenr lo bsl dsl sp0 : Z) (payload slack : list byte) (errv : word) (mxd q pb : Z) (pbs : list blk),
HEAPA A4L HIx A (TBS ++ LBc) LM FRS B m md ->

TBS = [(tk, 72); (q, 32 * mxd)] ++ pbs -> 1 <= mxd <= 32 ->
rw_cells asegs m tk (tok_cells_g mxd 0 pb 0 q (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) ->
pbuf asegs m pbs pb -> pb <> 0 ->
tstack asegs m q (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)) ->
PBOKat m (ts_init mxd pb pbs) 0 -> pb_capA pbs = 32 ->

bytes_at asegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_okA m LBc FRS sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA m ->
bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
sp = Z_to_bv 64 sp0 ->
stk asegs m lo sp0 -> alloc_ceiling <= lo -> lo <= sp0 - PE_STK_A ->
sp0 mod 32 = 0 -> sp0 + 32 <= hiA_top A4L HIx -> sp0 < 2^62 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->

s0 = Z_to_bv 64 tk -> ra = Z_to_bv 64 PE_RA2 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9eb50) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9bbfc) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94360) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x95f88) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) (UWfp PE_RA2 tk) ->

Z.of_nat (length LM) < 8 -> Z.of_nat (length FRS) + 2 < 4096 -> M2D <= bD B ->
Z.of_nat (pe_A0 len) + PhiPB len 32 + K_free * Z.of_nat (length TBS) + K_exit + bsl <= bB B ->
Z.of_nat (pe_A0 len) + dsl + M2D <= bD B -> 0 <= bsl -> 0 <= dsl ->
(forall ms' md' A', pe_post_A HIx GA (PEF tk 0 0 len lenr sb 0 (cfg_model md) mxd 0) (PEFA sp0 0 0 0 bsl dsl) (PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc LM FRS m lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_PE_ENTRY) fc None m (seg_rom asegs)).
Proof.
intros until pbs. intros HP ETBS MXB TOK PB Hpb TSK PBK CAP STR PLEN LEN MODE SB0 SBL LOC LCK G UTF ESP ST LO LOS SPA HT SP62 ERR TP FRM A0 A1 A2 S0V RAV UWa UWo UWf UWd UWs UWn UWds LMN FRN BM1 BB BD BSL DSL K.

assert (CSTR : lenr = len \/ nth_error payload (Z.to_nat (len - 1)) = Some (Z_to_bv 8 0)).
{ destruct MODE as [_ [-> | (_ & _ & (str0 & Ep & _) & _)]]; [left; reflexivity | right].
subst payload. rewrite length_app in PLEN. cbn [length] in PLEN.
rewrite nth_error_app2 by lia. replace (Z.to_nat (len - 1) - length str0)%nat with 0%nat by lia. reflexivity. }
assert (CPOS : lenr <> len -> 0 < len).
{ destruct MODE as [_ [-> | (_ & L1 & _)]]; [intros NE; exfalso; exact (NE eq_refl) | intros _; lia]. }
assert (INtk : In (tk, 72) ((TBS ++ LBc) ++ LM)) by (apply in_or_app; left; rewrite ETBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof alloc_ceiling_range as ACR.
eapply (seg_entry_A0 HIx GA GA_outside GA_pres GA_loc RTC_PEPC OBL_ERRNO OBL_SH_ERRNO USE ERRNOL DUP NEWL FREEL ISTRLEN) with (bsl := bsl) (dsl := dsl) (sp0 := sp0) (payload := payload) (slack := slack) (q := q) (pb := pb) (pbs := pbs) (len := len) (lenr := lenr) (sb := sb) (tk := tk) (mxd := mxd) (fl := 0);
[ exact HP | exact ETBS | split; [exact MXB | lia] | exact TOK | exact PB | exact Hpb | exact TSK | exact STR | exact PLEN | exact LEN | exact MODE | exact SB0 | exact SBL | exact LOC | exact LCK | exact G
| exact ESP | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SP62 | exact ERR | exact TP | rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity
| exact A0 | exact A1 | exact A2 | exact LMN | exact FRN | exact BM1 | unfold K_ev, PhiPB, K_free, K_exit in *; lia | lia | exact BSL | | exact K ].
cbn zeta. intros newl spf Ff m1 md1 A1x B1 nb pj errv1 gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4' STC INV VM1 HPRX AGP LOC1 NEWLR BB1 BD1.
set (pf := PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd 0) in *.
set (pa := PEFA sp0 Ff LC_GLOBAL_A newl bsl dsl) in *.
set (sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in *.
set (LM1 := (newl, 48) :: LM) in *.

assert (UTF1 : bytes_at asegs m1 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPRX | exact UTF |]. right; left. intros a Ha. unfold UTF8REP_ADDR_A in Ha. cbn in Ha.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia | unfold xlocA, a4_volatile, LOCCELL_A, A_TP; lia]. }

assert (KRET : forall ms' md' A', pe_post_A HIx GA pf pa sv F fc md1 LBc (lb_remove (pa_newloc pa) LM1) FRS m1 lo ms' md' A' -> AJ5 A4L HIx A' T md' ms').
{ intros ms' md' A' P. apply K. unfold LM1, pa in P. cbn [pa_newloc] in P. rewrite lb_remove_head in P.
eapply pe_post_A_eq; [| | | | | | | eapply (pe_post_A_me (PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd 0) (PEFA sp0 Ff LC_GLOBAL_A newl bsl dsl)); [exact HPRX | exact VM1 | exact P]]; reflexivity. }
pose proof (kout_A HIx GA GA_outside GA_pres GA_loc PUT USE FREEL pf pa q LBc LM1 FRS payload m1 lo sv T F fc md1 newl 48
STC eq_refl ltac:(left; reflexivity) LOC1 ltac:(lia) S0V RAV BSL (model_vm_only_refl _) KRET) as KO.
assert (HV : (tk < alloc_ceiling \/ tk mod 8 <> 0 \/ tk <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= tk) /\ 0 <= tk < 2^64).
{ split; [left; lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi; lia]. }
pose proof (pe_kall_S HIx GA GA_outside GA_pres GA_presx GA_lh MAPP SHRINK AADD PUT NEWARR NEWOBJ HD HD_le OADD QFZX.Mq4.istrncmp_sound_U QFZX.Mq3.istrncasecmp_sound_U NEWDBL NEWBOOL NEWSTR PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS pf pa q LBc LM1 FRS payload m1 lo sv T F
FRN STC ltac:(unfold CSTR_OK, pf; cbn [pf_lenr pf_len]; exact CSTR) UTF1 BSL DSL eq_refl tk PE_RA2 S0V RAV HV UWa UWo UWf UWd UWs UWn UWds KO
(S (pe_N0 len))) as (KL & _ & _ & _).
assert (EML : mloop pf (ts_init mxd pb pbs) = pe_N0 len) by (unfold mloop, mbase, ts_init, pe_N0, pf; cbn [t_co pf_len]; f_equal; f_equal; f_equal; lia).
assert (EBL : bloop pf (ts_init mxd pb pbs) = pe_A0 len).
{ unfold bloop, bx, pe_A0. rewrite EML. replace (bres pf (cur_st (ts_init mxd pb pbs)) (cur_ss (ts_init mxd pb pbs))) with (2 * BTOK pf + 1792) by reflexivity.
unfold BRX, BTOK, pf, ts_init; cbn [pf_len t_co]. f_equal. f_equal. lia. }
eapply (KL (ts_init mxd pb pbs)); [rewrite EML; lia | exact INV | cbv; discriminate | intros HH; cbv in HH; discriminate HH | | | | | | apply fsaved_refl | exact FRM].
-
split; [| intros HH; cbv in HH; discriminate HH]. unfold ts_init. cbn [t_levels]. intros i l Hi.
assert (E : tl_cs l = None).
{ destruct i as [|i]; cbn [nth_error] in Hi; [injection Hi as <-; reflexivity|].
apply nth_error_In in Hi. apply (repeat_spec _ lvl_zero l) in Hi. subst l. reflexivity. }
pose proof (nth_error_Some_length Hi) as LT. cbn [length] in LT. rewrite repeat_length in LT.
rewrite E. cbn [odep]. lia.
- intros NE. unfold ts_init; cbn [t_co]. unfold pf in NE; cbn [pf_lenr pf_len] in NE. exact (CPOS NE).
-
assert (E0 : PBS (ts_init mxd pb pbs) = 1) by reflexivity. rewrite E0. exists 0. split; [| split].
+ eapply PBOKat_agree; [exact PBK | exact AGP | unfold ts_init; cbn [t_pbs]; apply incl_refl].
+ cbn [ts_init t_co]. lia.
+ exists 0. split; [| cbv; intros HH; discriminate HH].
unfold jw, ts_init. cbn [t_levels t_depth t_objs t_objbs]. cbn [jwl].
replace (jwl (repeat lvl_zero (Z.to_nat mxd - 1)) 0) with (Some 0) by (destruct (repeat lvl_zero (Z.to_nat mxd - 1)); reflexivity). reflexivity.
-
rewrite EBL. unfold BOK, bneed, ts_init, pf, pa; cbn [t_levels t_depth t_co t_pbs pf_len pa_bslack pa_dslack tstate_blocks t_objbs].
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
rewrite CAP.
split; [| split; [| split; [| split]]].
+ unfold tstate_blocks; cbn [t_pbs t_objbs t_levels]. rewrite ECC, !app_nil_r. cbn [ledger_open phi_open lvl_closed lvl_reset tl_ss tl_st phi_level tl_cs].
rewrite ETBS in BB. cbn [app length] in BB. unfold K_ev in *; cbn [pf_len] in *. unfold PhiPB, K_free, K_exit in *. rewrite ?Nat2Z.inj_succ in BB.
change (phi_open lvl_reset) with 0. replace (ledger_open (repeat lvl_zero (Z.to_nat mxd - 1)) 0) with 0 by (destruct (repeat lvl_zero (Z.to_nat mxd - 1)); reflexivity). lia.
+ lia.
+ unfold PhiPB. lia.
+ unfold pb_inv. lia.
+ intros i l Hi Hl. assert (i = 0%nat) as -> by lia. cbn in Hl. injection Hl as <-.
unfold lvl_disc. change (phi_open lvl_reset) with 0. cbn [lvl_reset tl_cs tl_nbs tl_cbs].
split; [lia|].
split; [intros _ kids HH; discriminate HH|]. split; [intros _ kids HH; discriminate HH | apply Forall_nil].
-  reflexivity.
Qed.
End PeSTop2.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek.
Import QbFI. Import QRBl. Import Qhd4. Import Qwm6.Mq4 QgHv Q9O6.Mq5 QlKV.Mqg Q228.Mq9 QiVi QicC QFrL.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPA A4L HIx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Theorem json_escape_str_A : esc_specA HIx.
Proof.
apply esc_specA_of_al.
- exact (json_escape_str_A_0 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).
- exact (json_escape_str_A_16 HIx OBL_REALLOC_NF PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).
Qed.
End Esc.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS Q9yh Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3 QLbz.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QsKa.Mqe Qoif.Mq4 QlKV.Mqe QSHS Ql4f.Mq4 Q1Y6.Mq4 QGdd.Mq0 QcmL QrQv.Mq4 QEUF.Mq2 QJZd.Mqg QW22.Mq8 QnDr.Mq5 Qmgs.Mq0 QdGy.Mqc QWrz.Mq5 QV7s.Mq3 QQ2r.Mq7 QtyQ.Mq9 QtyQ.Mqa Q8H8 QQ2r.Mq8 QFrL.Mq2 QQPy.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QsKa.Mq9 QFZX QFZX.Mq8 Q63E.Mqg.
Import Q6oO.Mq2 Q63E.Mqh.
Import Qvmy QW22.Mq4 QV7s.Mq5 Q9yh.
Import QlKV.Mq2. Import Q2EX QnDr.Mq6.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSTop2B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.

Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.
Hypothesis NEWDBL : jo_new_double_A_stmt HIx.
Hypothesis NEWBOOL : jo_new_boolean_A_stmt HIx.
Hypothesis NEWSTR : jo_new_string_len_A_stmt HIx.
Hypothesis PARSEI : parse_i64_A_stmt HIx 0xa6060.
Hypothesis PARSEU : parse_i64_A_stmt HIx 0xa62ec.
Hypothesis STRTOD : strtod_A_stmt HIx.
Hypothesis NEWINT : jo_new_int_A_stmt HIx 0x9dbdc.
Hypothesis NEWUINT : jo_new_int_A_stmt HIx 0x9e328.
Hypothesis NEWDBLS : new_double_s_A_stmt HIx.

Lemma ISTRLEN : istrlen_spec_U.
Proof.
unfold istrlen_spec_U. intros until Q. intros UP RT H0 H47 H40 HAPP HLO Ha0 NONUL STR PAD ST LO LOS SPA MI RA K.
apply (astrlen_sound_U ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a lo s slack Q
UP RT H0 H47 HLO Ha0 NONUL H40); try assumption.
- destruct (Z.le_gt_cases (Z.of_nat (length s)) 63) as [L|G]; [left; exact L| right; apply HAPP; lia].
- intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' _ ST'. exact (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST').
Qed.

Lemma RTC_PEPC : rtc_pepc_stmt HIx.
Proof.
intros A LB LM FR B m md HP. pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP) as R. rewrite Forall_forall in R.
refine (R (A_GOT_PEPC, le8 (Z_to_bv 64 A_PE_ENTRY)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts, A_GOT_PEPC, A_PE_ENTRY.
repeat (first [left; reflexivity | right]).
Qed.
Lemma OBL_ERRNO : heapA_errno_stmt HIx.
Proof. intros A LB LM FR B m md HP. exact (heapA_errno A4L HIx _ _ _ _ _ _ _ HP). Qed.

Lemma OBL_SH_ERRNO : sh_errno_stmt HIx.
Proof.
intros A LB LM FR B m md HP.
pose proof (heapA_shadow_img A4L HIx A LB LM FR B m md (A_ERRNO / 8) HP) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) (A_ERRNO / 8) = 0) by (vm_compute; reflexivity). rewrite E in X.
apply X; vm_compute; discriminate.
Qed.

Definition pe_N0 (len : Z) : nat := (16 * Z.to_nat len + 15)%nat.

Definition pe_A0 (len : Z) : nat := (pe_N0 len + Z.to_nat ((16 * Z.max 0 len + 11008) * len + (2 * (16 * Z.max 0 len + 8192) + 1792)))%nat.

Lemma pe_post_A_me : forall pf pa sv F fc md md1 LBc LM FRS me m1 lo ms' md' A',
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
pe_post_A HIx GA pf pa sv F fc md1 LBc LM FRS m1 lo ms' md' A' -> pe_post_A HIx GA pf pa sv F fc md LBc LM FRS me lo ms' md' A'.
Proof.
intros pf pa sv F fc md md1 LBc LM FRS me m1 lo ms' md' A' HX VM P.
destruct P as (m' & gp & r & errv' & RBS & TBS & LK & B' & RS & VM' & ST & ERR & LOC & HPR & REST).
exists m', gp, r, errv', RBS, TBS, LK, B'. split; [exact RS|]. split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [exact ST|]. split; [exact ERR|]. split; [exact LOC|].
split; [eapply heap_presx_trans; [exact HX | exact HPR] | exact REST].
Qed.

Theorem json_tokener_parse_ex_B_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (TBS LBc LM : list blk) (FRS : list frame) (B : bud) (tk sb len lenr lo bsl dsl sp0 : Z) (payload slack : list byte) (errv : word) (mxd q pb : Z) (pbs : list blk),
HEAPA A4L HIx A (TBS ++ LBc) LM FRS B m md ->

TBS = [(tk, 72); (q, 32 * mxd)] ++ pbs -> 1 <= mxd <= 32 ->
rw_cells asegs m tk (tok_cells_g mxd 0 pb 0 q (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) ->
pbuf asegs m pbs pb -> pb <> 0 ->
tstack asegs m q (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)) ->
PBOKat m (ts_init mxd pb pbs) 0 -> pb_capA pbs = 32 ->

bytes_at asegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_okA m LBc FRS sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA m ->
bytes_at asegs m UTF8REP_ADDR_A Qa8x.Mq3.utf8rep ->
sp = Z_to_bv 64 sp0 ->
stk asegs m lo sp0 -> alloc_ceiling <= lo -> lo <= sp0 - PE_STK_A ->
sp0 mod 32 = 16 -> sp0 + 32 <= hiA_top A4L HIx -> sp0 < 2^62 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> frm0 fc ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->

s0 = Z_to_bv 64 tk -> ra = Z_to_bv 64 PE_RA2 ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa0770) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94e48) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_strdup A4L) (Z_to_bv 64 0x975cc) (UWfp PE_RA2 tk) ->
uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f57c) (UWfp PE_RA2 tk) ->

Z.of_nat (length LM) < 8 -> Z.of_nat (length FRS) + 2 < 4096 -> M2D <= bD B ->
Z.of_nat (pe_A0 len) + PhiPB len 32 + K_free * Z.of_nat (length TBS) + K_exit + bsl <= bB B ->
Z.of_nat (pe_A0 len) + dsl + M2D <= bD B -> 0 <= bsl -> 0 <= dsl ->
(forall ms' md' A', pe_post_A HIx GA (PEF tk 0 0 len lenr sb 0 (cfg_model md) mxd 0) (PEFA sp0 0 0 0 bsl dsl) (PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc md LBc LM FRS m lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_PE_ENTRY) fc None m (seg_rom asegs)).
Proof.
intros until pbs. intros HP ETBS MXB TOK PB Hpb TSK PBK CAP STR PLEN LEN MODE SB0 SBL LOC LCK G UTF ESP ST LO LOS SPA HT SP62 ERR TP FRM A0 A1 A2 S0V RAV UWa UWo UWf UWd UWs UWn UWds LMN FRN BM1 BB BD BSL DSL K.

assert (CSTR : lenr = len \/ nth_error payload (Z.to_nat (len - 1)) = Some (Z_to_bv 8 0)).
{ destruct MODE as [_ [-> | (_ & _ & (str0 & Ep & _) & _)]]; [left; reflexivity | right].
subst payload. rewrite length_app in PLEN. cbn [length] in PLEN.
rewrite nth_error_app2 by lia. replace (Z.to_nat (len - 1) - length str0)%nat with 0%nat by lia. reflexivity. }
assert (CPOS : lenr <> len -> 0 < len).
{ destruct MODE as [_ [-> | (_ & L1 & _)]]; [intros NE; exfalso; exact (NE eq_refl) | intros _; lia]. }
assert (INtk : In (tk, 72) ((TBS ++ LBc) ++ LM)) by (apply in_or_app; left; rewrite ETBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & _ & Htlo & Hthi & _).
pose proof alloc_ceiling_range as ACR.
eapply (seg_entry_B0 HIx GA GA_outside GA_pres GA_loc RTC_PEPC OBL_ERRNO OBL_SH_ERRNO USE ERRNOL DUP NEWL FREEL ISTRLEN) with (bsl := bsl) (dsl := dsl) (sp0 := sp0) (payload := payload) (slack := slack) (q := q) (pb := pb) (pbs := pbs) (len := len) (lenr := lenr) (sb := sb) (tk := tk) (mxd := mxd) (fl := 0);
[ exact HP | exact ETBS | split; [exact MXB | lia] | exact TOK | exact PB | exact Hpb | exact TSK | exact STR | exact PLEN | exact LEN | exact MODE | exact SB0 | exact SBL | exact LOC | exact LCK | exact G
| exact ESP | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact SP62 | exact ERR | exact TP | rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity
| exact A0 | exact A1 | exact A2 | exact LMN | exact FRN | exact BM1 | unfold K_ev, PhiPB, K_free, K_exit in *; lia | lia | exact BSL | | exact K ].
cbn zeta. intros newl spf Ff m1 md1 A1x B1 nb pj errv1 gp' t0' a0' a1' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' STC INV VM1 HPRX AGP LOC1 NEWLR BB1 BD1.
set (pf := PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd 0) in *.
set (pa := PEFA sp0 Ff LC_GLOBAL_A newl bsl dsl) in *.
set (sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in *.
set (LM1 := (newl, 48) :: LM) in *.

assert (UTF1 : bytes_at asegs m1 UTF8REP_ADDR_A Qa8x.Mq3.utf8rep).
{ eapply (heap_presx_bytes_at A4H); [exact HPRX | exact UTF |]. right; left. intros a Ha. unfold UTF8REP_ADDR_A in Ha. cbn in Ha.
split; [cbn [hl_client_static A4H]; unfold a4_client_static; lia | unfold xlocA, a4_volatile, LOCCELL_A, A_TP; lia]. }

assert (KRET : forall ms' md' A', pe_post_A HIx GA pf pa sv F fc md1 LBc (lb_remove (pa_newloc pa) LM1) FRS m1 lo ms' md' A' -> AJ5 A4L HIx A' T md' ms').
{ intros ms' md' A' P. apply K. unfold LM1, pa in P. cbn [pa_newloc] in P. rewrite lb_remove_head in P.
eapply pe_post_A_eq; [| | | | | | | eapply (pe_post_A_me (PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd 0) (PEFA sp0 Ff LC_GLOBAL_A newl bsl dsl)); [exact HPRX | exact VM1 | exact P]]; reflexivity. }
pose proof (kout_B HIx GA GA_outside GA_pres GA_loc PUT USE FREEL pf pa q LBc LM1 FRS payload m1 lo sv T F fc md1 newl 48
STC eq_refl ltac:(left; reflexivity) LOC1 ltac:(lia) S0V RAV BSL (model_vm_only_refl _) KRET) as KO.
assert (HV : (tk < alloc_ceiling \/ tk mod 8 <> 0 \/ tk <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= tk) /\ 0 <= tk < 2^64).
{ split; [left; lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi; lia]. }
pose proof (pe_kall_S HIx GA GA_outside GA_pres GA_presx GA_lh MAPP SHRINK AADD PUT NEWARR NEWOBJ HD HD_le OADD QFZX.istrncmp_sound_U QFZX.Mq8.istrncasecmp_sound_U NEWDBL NEWBOOL NEWSTR PARSEI PARSEU STRTOD NEWINT NEWUINT NEWDBLS pf pa q LBc LM1 FRS payload m1 lo sv T F
FRN STC ltac:(unfold CSTR_OK, pf; cbn [pf_lenr pf_len]; exact CSTR) UTF1 BSL DSL eq_refl tk PE_RA2 S0V RAV HV UWa UWo UWf UWd UWs UWn UWds KO
(S (pe_N0 len))) as (KL & _ & _ & _).
assert (EML : mloop pf (ts_init mxd pb pbs) = pe_N0 len) by (unfold mloop, mbase, ts_init, pe_N0, pf; cbn [t_co pf_len]; f_equal; f_equal; f_equal; lia).
assert (EBL : bloop pf (ts_init mxd pb pbs) = pe_A0 len).
{ unfold bloop, bx, pe_A0. rewrite EML. replace (bres pf (cur_st (ts_init mxd pb pbs)) (cur_ss (ts_init mxd pb pbs))) with (2 * BTOK pf + 1792) by reflexivity.
unfold BRX, BTOK, pf, ts_init; cbn [pf_len t_co]. f_equal. f_equal. lia. }
eapply (KL (ts_init mxd pb pbs)); [rewrite EML; lia | exact INV | cbv; discriminate | intros HH; cbv in HH; discriminate HH | | | | | | apply fsaved_refl | exact FRM].
-
split; [| intros HH; cbv in HH; discriminate HH]. unfold ts_init. cbn [t_levels]. intros i l Hi.
assert (E : tl_cs l = None).
{ destruct i as [|i]; cbn [nth_error] in Hi; [injection Hi as <-; reflexivity|].
apply nth_error_In in Hi. apply (repeat_spec _ lvl_zero l) in Hi. subst l. reflexivity. }
pose proof (nth_error_Some_length Hi) as LT. cbn [length] in LT. rewrite repeat_length in LT.
rewrite E. cbn [odep]. lia.
- intros NE. unfold ts_init; cbn [t_co]. unfold pf in NE; cbn [pf_lenr pf_len] in NE. exact (CPOS NE).
-
assert (E0 : PBS (ts_init mxd pb pbs) = 1) by reflexivity. rewrite E0. exists 0. split; [| split].
+ eapply PBOKat_agree; [exact PBK | exact AGP | unfold ts_init; cbn [t_pbs]; apply incl_refl].
+ cbn [ts_init t_co]. lia.
+ exists 0. split; [| cbv; intros HH; discriminate HH].
unfold jw, ts_init. cbn [t_levels t_depth t_objs t_objbs]. cbn [jwl].
replace (jwl (repeat lvl_zero (Z.to_nat mxd - 1)) 0) with (Some 0) by (destruct (repeat lvl_zero (Z.to_nat mxd - 1)); reflexivity). reflexivity.
-
rewrite EBL. unfold BOK, bneed, ts_init, pf, pa; cbn [t_levels t_depth t_co t_pbs pf_len pa_bslack pa_dslack tstate_blocks t_objbs].
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
rewrite CAP.
split; [| split; [| split; [| split]]].
+ unfold tstate_blocks; cbn [t_pbs t_objbs t_levels]. rewrite ECC, !app_nil_r. cbn [ledger_open phi_open lvl_closed lvl_reset tl_ss tl_st phi_level tl_cs].
rewrite ETBS in BB. cbn [app length] in BB. unfold K_ev in *; cbn [pf_len] in *. unfold PhiPB, K_free, K_exit in *. rewrite ?Nat2Z.inj_succ in BB.
change (phi_open lvl_reset) with 0. replace (ledger_open (repeat lvl_zero (Z.to_nat mxd - 1)) 0) with 0 by (destruct (repeat lvl_zero (Z.to_nat mxd - 1)); reflexivity). lia.
+ lia.
+ unfold PhiPB. lia.
+ unfold pb_inv. lia.
+ intros i l Hi Hl. assert (i = 0%nat) as -> by lia. cbn in Hl. injection Hl as <-.
unfold lvl_disc. change (phi_open lvl_reset) with 0. cbn [lvl_reset tl_cs tl_nbs tl_cbs].
split; [lia|].
split; [intros _ kids HH; discriminate HH|]. split; [intros _ kids HH; discriminate HH | apply Forall_nil].
-  reflexivity.
Qed.
End PeSTop2B.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJVP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6VZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKvs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Module PS := QJVP.
Module PT := Q6VZ.
Module PH := QKvs.Mq2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Fixpoint img_w_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| Datatypes.S n' => match wview asegs (fun _ => None) (wa A) with Some _ => img_w_b (A + 1) n' | None => false end
end.
Lemma img_w_b_sound : forall n A (m : word -> option byte), img_w_b A n = true -> 0 <= A -> A + Z.of_nat n <= 2^64 -> wr_at asegs m A (Z.of_nat n).
Proof.
intros n A m Hb HA Hhi. split; [exact HA|]. split; [exact Hhi|]. revert A Hb HA Hhi.
induction n as [|n IH]; intros A Hb HA Hhi i Hi; [lia|]. cbn [img_w_b] in Hb.
destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate|]. cbn beta in Ew. rewrite Ew. discriminate.
- replace (A + i) with ((A + 1) + (i - 1)) by lia. apply (IH (A + 1) Hb); lia.
Qed.

Lemma rw_c8_of_bytes : forall (m : word -> option byte) A (v : word),
bytes_at asegs m A (le8 v) -> img_w_b A 8 = true -> rw_cells asegs m A [C8 v].
Proof.
intros m A v B W. pose proof (bytes_at_bound _ _ _ _ B) as Bd. rewrite length_le8 in Bd.
split.
- split; [repeat constructor|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
- apply (img_w_b_sound 8 A m W); lia.
Qed.

Theorem astrtod_total_proof : astrtod_total_stmt.
Proof.
unfold astrtod_total_stmt. intros until ev. intros BY BYT Htxt Hlen Hlt PEC HS ST LO GT SPH Tpos T47 HT PE0 PE47 HPE SEPE GOTG GUA ERR MI FRM Htp Ha0 Ha1.
pose proof (PH.rstrtod_total_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
T PE txt pre post bits used ejunk lo canary ev) as X.
unfold A_TP, A_GOT_GUARD, A_GUARD, ASTRTOD_DEPTH, A_STRTOD in *.
unfold PS.RSTRTOD_DEPTH, PS.RGLOBALS_TOP, PS.RIMG_LO, PS.RATP, PS.RERRNO, PS.RSTRTOD, PS.ssp_cells, PS.got_ssp, PS.ssp_guard in X.
unfold zlength in *. change QBpX.usegs with asegs in X.
eapply evt_mono; [eapply X; first [assumption | lia | idtac] |].
- split; apply rw_c8_of_bytes; first [assumption | vm_compute; reflexivity].
- intros ms' P. unfold PS.rstrtod_post in P.
destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & ev' & -> & MU & WM & MI' & FR' & FK & FA & ST' & PE' & BY' & SSP' & ERR' & US).
unfold astrtod_post, A_TP. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m', ev'.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact FR'|]. split; [exact FK|]. split; [exact FA|].
split; [exact ST'|]. split; [exact PE'|]. split; [exact BY'|]. split; [exact ERR'|]. exact US.
Qed.

Theorem scan_total_proofA : scan_total_stmtA.
Proof. exact PH.scan_strtod_h_total_proof. Qed.
End RC__1.
