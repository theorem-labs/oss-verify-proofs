(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD Qhd4 QGcC QCKW QS67 QsRG Qnhz QBxa QRjH Q9ox QsV0 Qn1e QMz4 QSpR QXup Lib.GwApply QWxq_c1 Qe4Y QHnV QCcH QfLs Qsw7 QJjn Qwm6 QlKV QsKa Q0TL Qujl QupI QnXa Q2y2 QdM4 QscU QTmr Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4 QGcC.Mq0.
Import QCKW.Mq0 QCKW.Mq2 QS67.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QBxa.Mq0 QRjH Q9ox.Mq2 QsV0 Qn1e QBxa.Mq5 QMz4 Q9ox.Mq0 QSpR.Mq2.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.
Import Qe4Y.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7.
Import Q0TL Qujl QupI.Mq0 QnXa Q2y2 QdM4.Mq1.
Import QscU.Mq1 QTmr.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition hb (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_of (data : list byte) : Z := hb data 0 + 256 * hb data 1.
Definition cfglen_of (data : list byte) : Z := (cfg_of data) mod 32768.
Definition counting_of (data : list byte) : bool := 32768 <=? cfg_of data.
Definition calls_of (data : list byte) : nat :=
match Z.to_nat (cfglen_of data) with O => 1%nat | _ => S (Z.to_nat (hb data 2 mod 4)) end.

Definition TRUN_RET_A : Z := 0x9176c.
Definition HDR_SHORT_A : Z := 0x917b0.
Definition HDR_OVERRUN_A : Z := 0x917cc.

Lemma land_low_high : forall m z0, 0 <= m -> 0 <= z0 < 256 -> Z.land (m * 2^8) z0 = 0.
Proof.
intros m z0 Hm Hz. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [LT|GE].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 z0 n); [apply Bool.andb_false_r| lia|].
destruct (Z.eq_dec z0 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^8)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_low_high : forall m z0, 0 <= m -> 0 <= z0 < 256 -> Z.lor (m * 2^8) z0 = m * 2^8 + z0.
Proof.
intros m z0 Hm Hz. rewrite <- Z.lxor_lor by (apply land_low_high; lia). symmetry. apply Z.add_nocarry_lxor. apply land_low_high; lia.
Qed.

Lemma hdr_cfg_word : forall (b0 b1 : byte),
Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb b1)) 57))) 49))) (bv_unsigned (zxb b0))
= (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768.
Proof.
intros b0 b1. pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in *. cbn in R0, R1.
set (z0 := bv_unsigned b0) in *. set (z1 := bv_unsigned b1) in *.
unfold zxb, sxb. fold z0.
assert (U : bv_unsigned (Z_to_bv 64 (bv_signed b1)) = (if z1 <? 128 then z1 else 2^64 - 256 + z1)).
{ rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap. fold z1. unfold bv_wrap, bv_half_modulus, bv_modulus. cbn -[z1 Z.ltb Z.add Z.sub Z.modulo].
change (2 ^ 8 / 2) with 128. change (2^8) with 256.
destruct (Z.ltb_spec z1 128).
- rewrite (Z.mod_small (z1 + 128) 256) by lia. rewrite Z.mod_small by lia. lia.
- replace ((z1 + 128) mod 256) with (z1 + 128 - 256) by (apply (Zmod_unique _ _ 1); lia).
symmetry. apply (Zmod_unique _ _ (-1)); lia. }
rewrite U. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit z0) by lia.
assert (E : bv_unsigned (Z_to_bv 64 ((if z1 <? 128 then z1 else 2 ^ 64 - 256 + z1) * 2 ^ 57)) = (z1 mod 128) * 2^57).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^7 * 2^57).
rewrite Z.mul_mod_distr_r by lia. f_equal. destruct (Z.ltb_spec z1 128); [reflexivity|].
replace (2^64 - 256 + z1) with (z1 + (2^57 - 2) * 2^7) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite E. replace (z1 mod 128 * 2 ^ 57 / 2 ^ 49) with ((z1 mod 128) * 2^8).
2:{ symmetry. replace (z1 mod 128 * 2^57) with ((z1 mod 128 * 2^8) * 2^49) by lia. apply Z.div_mul. lia. }
pose proof (Z.mod_pos_bound z1 128 ltac:(lia)).
rewrite unsigned_lit by lia. rewrite lor_low_high by lia.
apply (Zmod_unique _ _ (z1 / 128)). { lia. } pose proof (Z.div_mod z1 128 ltac:(lia)). lia.
Qed.

Lemma t_body_cases : forall data fs, (6 <= length data)%nat -> Z.of_nat (length data) < MAX_INPUT ->
t_body data fs =
if (length data <? 6 + Z.to_nat (cfglen_of data))%nat then t_die msg_overrun fs
else match (length data - 6 - Z.to_nat (cfglen_of data))%nat with
| O => t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs)
| S _ => t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs)
end.
Proof.
intros data fs H1 H2. unfold t_body.
replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; lia).
replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
reflexivity.
Qed.

Lemma t_body_ok : forall data fs, (6 + Z.to_nat (cfglen_of data) <= length data)%nat -> Z.of_nat (length data) < MAX_INPUT ->
t_body data fs = t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs).
Proof.
intros data fs H1 H2. rewrite t_body_cases by lia.
replace (length data <? 6 + Z.to_nat (cfglen_of data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
destruct (length data - 6 - Z.to_nat (cfglen_of data))%nat; reflexivity.
Qed.

Lemma zero_lines_split : forall c, (1 <= c)%nat -> zero_lines c = zero_lines 1 ++ zero_lines (Nat.pred c).
Proof. intros [|c] H; [lia|]. reflexivity. Qed.

Lemma byte_signed : forall b : byte, bv_signed b = (if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256).
Proof.
intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[bv_unsigned Z.ltb Z.add Z.sub Z.modulo].
change (2 ^ 8 / 2) with 128. change (2^8) with 256.
destruct (Z.ltb_spec (bv_unsigned b) 128).
- rewrite Z.mod_small by lia. lia.
- replace ((bv_unsigned b + 128) mod 256) with (bv_unsigned b + 128 - 256) by (apply (Zmod_unique _ _ 1); lia). lia.
Qed.

Lemma nth_read {X} : forall (k : nat) (l : list X) (d : X), (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
intros k l d. revert l. induction k as [|k IH]; intros [|x l] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Section Hdr.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Variables (BB_REST BD_REST TR_BB TR_BD : Z).
Variables (BQ_REST BN_REST : Z).
Hypothesis RESTS : TR_BB + 512 <= BB_REST /\ TR_BD <= BD_REST /\ 0 <= TR_BB /\ 0 <= TR_BD.

Hypothesis RESTS6 : 8192 <= BQ_REST /\ 1 <= BN_REST /\ 0 <= BD_REST.

Notation HINVx := (HINV H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST).
Notation TINVx := (TINV HIx argv USP LO fs LM0).

Definition trun_stmt : Prop :=
forall (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) (K : TSet)
(gp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINVx cap buf m md A B ->
6 + cfglen_of data <= Z.of_nat (length data) ->
frm0 fc -> K [] ->
(forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (LK : list blk) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
TINVx 0 buf cap LK m' md' A' B' (zero_lines (Nat.pred (calls_of data))) ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp' (Z_to_bv 64 A_TP) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET_A) fc' None m' (seg_rom asegs))) ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf)
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
a4 a5 a6 a7
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TRUN_A) fc None m (seg_rom asegs)).

Definition leaf_hdr_stmt : Prop :=
forall (pc : Z) (msg : list byte) (cap buf : Z) (A : ASA A4L HIx) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
((pc = HDR_SHORT_A /\ msg = msg_short) \/ (pc = HDR_OVERRUN_A /\ msg = msg_overrun)) ->
drvA_memS argv USP m -> HEAPAx A [(buf, cap)] LM0 [] B m md -> 512 <= bB B ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
(exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))) ->
CFDS fds0 (m_fds (cfg_model md)) -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die msg fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Hypothesis TRUN : trun_stmt.
Hypothesis HLEAF : leaf_hdr_stmt.

Theorem hdr_ok : hdr_stmt H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST.
Proof.
unfold hdr_stmt. intros until fc. intros HI FRM.
destruct HI as [DM HP6 REQ Hcap Hlen (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof RESTS as (RB1 & RB2 & RB0 & RB3). pose proof HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1).

assert (HPL : HEAPAx A [(buf, cap)] LM0 [] (Bud 512 0 0) m md).
{ eapply (heapa5_enter A4L H6); [exact HP6|]. pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof RESTS6 as (R1 & R2 & R3). unfold blink. cbn [bB bD bM]. change (2^30) with 1073741824. lia. }
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
d5_enter.
unfold HDRPT_A. step. step.
destruct (Nat.lt_ge_cases (length data) 6) as [SHORT|LONG].
-
if_truex. evt_done5.
unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
eapply (HLEAF HDR_SHORT_A msg_short); [left; split; reflexivity | exact DM | exact HPL | cbn [bB]; lia | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact FRM].
- if_falsex.

pose proof BLK as [[[WF1 _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].
pose proof (bytes_at_read asegs m buf data 0 1 BA ltac:(lia) ltac:(lia)) as HR0.
pose proof (bytes_at_read asegs m buf data 1 1 BA ltac:(lia) ltac:(lia)) as HR1.
change (Z.to_nat 0) with 0%nat in HR0. change (Z.to_nat 1) with 1%nat in HR1.
rewrite (nth_read 0%nat data (Z_to_bv 8 0)) in HR0 by lia. rewrite (nth_read 1%nat data (Z_to_bv 8 0)) in HR1 by lia.
step. step. step. step. step.
rewrite hdr_cfg_word. fold (hb data 0) (hb data 1). fold (cfg_of data). fold (cfglen_of data).
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
set (cl := cfglen_of data) in *.
assert (LEN64 : Z.of_nat (length data) < 2^26) by lia.
step. step.

destruct (Nat.lt_ge_cases (length data) (6 + Z.to_nat cl)) as [OVR|FIT].
+
if_truex. evt_done5.
rewrite (t_body_cases data fs LONG) by (unfold MAX_INPUT; lia).
replace (length data <? 6 + Z.to_nat (cfglen_of data))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
eapply (HLEAF HDR_OVERRUN_A msg_overrun); [right; split; reflexivity | exact DM | exact HPL | cbn [bB]; lia | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact FRM].
+ if_falsex.
rewrite (t_body_ok data fs) by (unfold MAX_INPUT; lia).

pose proof (bytes_at_read asegs m buf data (2 + cl + 1) 1 BA ltac:(lia) ltac:(lia)) as HP1.
pose proof (bytes_at_read asegs m buf data (2 + cl + 0) 1 BA ltac:(lia) ltac:(lia)) as HP0.
pose proof (bytes_at_read asegs m buf data (2 + cl + 2) 1 BA ltac:(lia) ltac:(lia)) as HP2.
pose proof (bytes_at_read asegs m buf data (2 + cl + 3) 1 BA ltac:(lia) ltac:(lia)) as HP3.
rewrite (nth_read (Z.to_nat (2 + cl + 1)) data (Z_to_bv 8 0)) in HP1 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 0)) data (Z_to_bv 8 0)) in HP0 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 2)) data (Z_to_bv 8 0)) in HP2 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 3)) data (Z_to_bv 8 0)) in HP3 by lia.
step. step. step. step. step. step.
do 9 step. step. step. do 4 step. step.
evt_done5.

rewrite !(unsigned_lit cl) by lia. rewrite !(unsigned_lit (Z.of_nat (length data))) by lia.
replace (Z.of_nat (length data) - cl + -6) with (Z.of_nat (length data) - 6 - cl) by lia.
replace (buf + 2 + cl + 4) with (buf + 6 + cl) by lia.
assert (CALLS1 : (1 <= calls_of data)%nat) by (unfold calls_of; destruct (Z.to_nat (cfglen_of data)); lia).
rewrite (zero_lines_split (calls_of data)) by exact CALLS1.
eapply (aj5_conseq HIx); [| apply t_emit_W_app].
eapply (TRUN cap buf m md A B); [| subst cl; lia | exact FRM | apply t_emit_has_nil |].
{ constructor; [exact DM | exact HP6 | exact REQ | exact Hcap | exact Hlen | exists junk; exact BLK | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact HBUD]. }

intros m' md' A' B' LK F' fc' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' TI.
pose proof (t_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TI) as HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.        unfold TRUN_RET_A.
d5_enter.
unfold sxb. rewrite byte_signed. fold (hb data 1).
pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as R1. unfold bv_modulus in R1. cbn in R1. fold (hb data 1) in R1.
step.

destruct (Z.ltb_spec (hb data 1) 128) as [NC|CNT].
--
if_falsex. step. step. evt_done5.
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 0 buf cap LK m' md' A' B'). exact TI.
--
if_truex. step. step. step.
replace (ret_pc (Z_to_bv 64 595836)) with (Z_to_bv 64 595836 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. step. if_truex. evt_done5.
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 0 buf cap LK m' md' A' B'). exact TI.
Qed.
End Hdr.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGcC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCKW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCKW.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1jK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1jK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfub. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qujl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qujl.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnXa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnXa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOii.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOii.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition hb (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_of (data : list byte) : Z := hb data 0 + 256 * hb data 1.
Definition cfglen_of (data : list byte) : Z := (cfg_of data) mod 32768.
Definition counting_of (data : list byte) : bool := 32768 <=? cfg_of data.
Definition calls_of (data : list byte) : nat :=
match Z.to_nat (cfglen_of data) with O => 1%nat | _ => S (Z.to_nat (hb data 2 mod 4)) end.

Definition TRUN_RET_A : Z := 0x91b44.
Definition HDR_SHORT_A : Z := 0x91b88.
Definition HDR_OVERRUN_A : Z := 0x91ba4.

Lemma land_low_high : forall m z0, 0 <= m -> 0 <= z0 < 256 -> Z.land (m * 2^8) z0 = 0.
Proof.
intros m z0 Hm Hz. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases n 8) as [LT|GE].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 z0 n); [apply Bool.andb_false_r| lia|].
destruct (Z.eq_dec z0 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^8)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_low_high : forall m z0, 0 <= m -> 0 <= z0 < 256 -> Z.lor (m * 2^8) z0 = m * 2^8 + z0.
Proof.
intros m z0 Hm Hz. rewrite <- Z.lxor_lor by (apply land_low_high; lia). symmetry. apply Z.add_nocarry_lxor. apply land_low_high; lia.
Qed.

Lemma hdr_cfg_word : forall (b0 b1 : byte),
Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb b1)) 57))) 49))) (bv_unsigned (zxb b0))
= (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768.
Proof.
intros b0 b1. pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in *. cbn in R0, R1.
set (z0 := bv_unsigned b0) in *. set (z1 := bv_unsigned b1) in *.
unfold zxb, sxb. fold z0.
assert (U : bv_unsigned (Z_to_bv 64 (bv_signed b1)) = (if z1 <? 128 then z1 else 2^64 - 256 + z1)).
{ rewrite Z_to_bv_unsigned. unfold bv_signed, bv_swrap. fold z1. unfold bv_wrap, bv_half_modulus, bv_modulus. cbn -[z1 Z.ltb Z.add Z.sub Z.modulo].
change (2 ^ 8 / 2) with 128. change (2^8) with 256.
destruct (Z.ltb_spec z1 128).
- rewrite (Z.mod_small (z1 + 128) 256) by lia. rewrite Z.mod_small by lia. lia.
- replace ((z1 + 128) mod 256) with (z1 + 128 - 256) by (apply (Zmod_unique _ _ 1); lia).
symmetry. apply (Zmod_unique _ _ (-1)); lia. }
rewrite U. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (unsigned_lit z0) by lia.
assert (E : bv_unsigned (Z_to_bv 64 ((if z1 <? 128 then z1 else 2 ^ 64 - 256 + z1) * 2 ^ 57)) = (z1 mod 128) * 2^57).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^7 * 2^57).
rewrite Z.mul_mod_distr_r by lia. f_equal. destruct (Z.ltb_spec z1 128); [reflexivity|].
replace (2^64 - 256 + z1) with (z1 + (2^57 - 2) * 2^7) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite E. replace (z1 mod 128 * 2 ^ 57 / 2 ^ 49) with ((z1 mod 128) * 2^8).
2:{ symmetry. replace (z1 mod 128 * 2^57) with ((z1 mod 128 * 2^8) * 2^49) by lia. apply Z.div_mul. lia. }
pose proof (Z.mod_pos_bound z1 128 ltac:(lia)).
rewrite unsigned_lit by lia. rewrite lor_low_high by lia.
apply (Zmod_unique _ _ (z1 / 128)). { lia. } pose proof (Z.div_mod z1 128 ltac:(lia)). lia.
Qed.

Lemma t_body_cases : forall data fs, (6 <= length data)%nat -> Z.of_nat (length data) < MAX_INPUT ->
t_body data fs =
if (length data <? 6 + Z.to_nat (cfglen_of data))%nat then t_die msg_overrun fs
else match (length data - 6 - Z.to_nat (cfglen_of data))%nat with
| O => t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs)
| S _ => t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs)
end.
Proof.
intros data fs H1 H2. unfold t_body.
replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; lia).
replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
reflexivity.
Qed.

Lemma t_body_ok : forall data fs, (6 + Z.to_nat (cfglen_of data) <= length data)%nat -> Z.of_nat (length data) < MAX_INPUT ->
t_body data fs = t_emit (W 1 (zero_lines (calls_of data))) (t_exit (exit_code 0) fs).
Proof.
intros data fs H1 H2. rewrite t_body_cases by lia.
replace (length data <? 6 + Z.to_nat (cfglen_of data))%nat with false by (symmetry; apply Nat.ltb_ge; lia).
destruct (length data - 6 - Z.to_nat (cfglen_of data))%nat; reflexivity.
Qed.

Lemma zero_lines_split : forall c, (1 <= c)%nat -> zero_lines c = zero_lines 1 ++ zero_lines (Nat.pred c).
Proof. intros [|c] H; [lia|]. reflexivity. Qed.

Lemma byte_signed : forall b : byte, bv_signed b = (if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256).
Proof.
intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[bv_unsigned Z.ltb Z.add Z.sub Z.modulo].
change (2 ^ 8 / 2) with 128. change (2^8) with 256.
destruct (Z.ltb_spec (bv_unsigned b) 128).
- rewrite Z.mod_small by lia. lia.
- replace ((bv_unsigned b + 128) mod 256) with (bv_unsigned b + 128 - 256) by (apply (Zmod_unique _ _ 1); lia). lia.
Qed.

Lemma nth_read {X} : forall (k : nat) (l : list X) (d : X), (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
intros k l d. revert l. induction k as [|k IH]; intros [|x l] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Section Hdr.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPAx := (HEAPA A4L HIx).
Notation bud6 := QZsi.bud.
Notation Jx := (hiA_J A4L HIx).
Hypothesis SYS : forall (F : FPF) (fc : FPC), @aj_sys F fc asegs Jx.
Notation RZAx A md T := (AJ5 A4L HIx A T md).

Ltac d5_enter := aj5_enter; change (hl_segs A4L) with asegs.

Variable reqA : ASA A4L HIx -> Z.
Hypothesis OBL_FREE_NN : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Hypothesis OBL_CS_WIDE : forall a, cs_wide a -> hl_client_static A4H a.

Variables (argv : list (list byte)) (USP LO : Z) (path data : list byte) (fs : Fs.Fs) (LM0 : list blk).
Variables (fds0 : list (word * FdEntry)).
Notation SP := (USP - 128).
Hypothesis USPF : USP mod 16 = 0 /\ 2^33 <= USP /\ USP <= 2^47.
Hypothesis LOF : alloc_ceiling <= LO /\ LO + 2^22 <= USP - 48.
Hypothesis TOPF : USP <= hiA_top A4L HIx + 160 /\ hiA_bot A4L HIx <= LO.
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Variables (BB_REST BD_REST TR_BB TR_BD : Z).
Variables (BQ_REST BN_REST : Z).
Hypothesis RESTS : TR_BB + 512 <= BB_REST /\ TR_BD <= BD_REST /\ 0 <= TR_BB /\ 0 <= TR_BD.

Hypothesis RESTS6 : 8192 <= BQ_REST /\ 1 <= BN_REST /\ 0 <= BD_REST.

Notation HINVx := (HINV H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST).
Notation TINVx := (TINV HIx argv USP LO fs LM0).

Definition trun_stmt : Prop :=
forall (cap buf : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud6) (K : TSet)
(gp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINVx cap buf m md A B ->
6 + cfglen_of data <= Z.of_nat (length data) ->
frm0 fc -> K [] ->
(forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (LK : list blk) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
TINVx 0 buf cap LK m' md' A' B' (zero_lines (Nat.pred (calls_of data))) ->
RZAx A' md' K
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp' (Z_to_bv 64 A_TP) t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET_A) fc' None m' (seg_rom asegs))) ->
RZAx A md (t_emit (W 1 (zero_lines 1)) K)
(MS (mkR (Z_to_bv 64 TRUN_RET_A) (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf)
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
a4 a5 a6 a7
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TRUN_A) fc None m (seg_rom asegs)).

Definition leaf_hdr_stmt : Prop :=
forall (pc : Z) (msg : list byte) (cap buf : Z) (A : ASA A4L HIx) (B : bud) (m : word -> option byte) (md : config)
(ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
((pc = HDR_SHORT_A /\ msg = msg_short) \/ (pc = HDR_OVERRUN_A /\ msg = msg_overrun)) ->
drvA_memS argv USP m -> HEAPAx A [(buf, cap)] LM0 [] B m md -> 512 <= bB B ->
(exists errv, rw_cells asegs m (A_TP - 164) [C4 errv]) -> stk asegs m LO SP ->
(exists j8 (x7 x6 x5 x4 x3 x2 x1 x0 : word), rw_cells asegs m SP (main_frame j8 x7 x6 x5 x4 x3 x2 x1 x0 (Z_to_bv 64 RA_MAIN))) ->
CFDS fds0 (m_fds (cfg_model md)) -> m_fs (cfg_model md) = fs -> frm0 fc ->
RZAx A md (t_die msg fs)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

Hypothesis TRUN : trun_stmt.
Hypothesis HLEAF : leaf_hdr_stmt.

Theorem hdr_ok : hdr_stmt H6 reqA argv USP LO data fs LM0 fds0 BB_REST BD_REST BQ_REST BN_REST.
Proof.
unfold hdr_stmt. intros until fc. intros HI FRM.
destruct HI as [DM HP6 REQ Hcap Hlen (junk & BLK) (errv & ERR) ST (j8 & x7 & x6 & x5 & x4 & x3 & x2 & x1 & x0 & FR) Hfds Hfs HBUD].
pose proof (hr_view H6 _ _ _ _ _ _ _ HP6) as HP.
pose proof USPF as (U1 & U2 & U3). pose proof LOF as (L1 & L2). pose proof TOPF as (T1 & T2). pose proof RESTS as (RB1 & RB2 & RB0 & RB3). pose proof HBUD as (HQ1 & HB1 & HN1 & HB2 & HM1).

assert (HPL : HEAPAx A [(buf, cap)] LM0 [] (Bud 512 0 0) m md).
{ eapply (heapa5_enter A4L H6); [exact HP6|]. pose proof (QZsi.heapA_budget A4L H6 _ _ _ _ _ _ _ HP6) as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof RESTS6 as (R1 & R2 & R3). unfold blink. cbn [bB bD bM]. change (2^30) with 1073741824. lia. }
rc_lia_prep. unfold alloc_ceiling in L1.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP) as HCK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & _ & Bpos & Bhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; left; reflexivity)) as Bimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Bimg. unfold alloc_ceiling in Bhi.
d5_enter.
unfold HDRPT_A. step. step.
destruct (Nat.lt_ge_cases (length data) 6) as [SHORT|LONG].
-
if_truex. evt_done5.
unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
eapply (HLEAF HDR_SHORT_A msg_short); [left; split; reflexivity | exact DM | exact HPL | cbn [bB]; lia | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact FRM].
- if_falsex.

pose proof BLK as [[[WF1 _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].
pose proof (bytes_at_read asegs m buf data 0 1 BA ltac:(lia) ltac:(lia)) as HR0.
pose proof (bytes_at_read asegs m buf data 1 1 BA ltac:(lia) ltac:(lia)) as HR1.
change (Z.to_nat 0) with 0%nat in HR0. change (Z.to_nat 1) with 1%nat in HR1.
rewrite (nth_read 0%nat data (Z_to_bv 8 0)) in HR0 by lia. rewrite (nth_read 1%nat data (Z_to_bv 8 0)) in HR1 by lia.
step. step. step. step. step.
rewrite hdr_cfg_word. fold (hb data 0) (hb data 1). fold (cfg_of data). fold (cfglen_of data).
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
set (cl := cfglen_of data) in *.
assert (LEN64 : Z.of_nat (length data) < 2^26) by lia.
step. step.

destruct (Nat.lt_ge_cases (length data) (6 + Z.to_nat cl)) as [OVR|FIT].
+
if_truex. evt_done5.
rewrite (t_body_cases data fs LONG) by (unfold MAX_INPUT; lia).
replace (length data <? 6 + Z.to_nat (cfglen_of data))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
eapply (HLEAF HDR_OVERRUN_A msg_overrun); [right; split; reflexivity | exact DM | exact HPL | cbn [bB]; lia | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact FRM].
+ if_falsex.
rewrite (t_body_ok data fs) by (unfold MAX_INPUT; lia).

pose proof (bytes_at_read asegs m buf data (2 + cl + 1) 1 BA ltac:(lia) ltac:(lia)) as HP1.
pose proof (bytes_at_read asegs m buf data (2 + cl + 0) 1 BA ltac:(lia) ltac:(lia)) as HP0.
pose proof (bytes_at_read asegs m buf data (2 + cl + 2) 1 BA ltac:(lia) ltac:(lia)) as HP2.
pose proof (bytes_at_read asegs m buf data (2 + cl + 3) 1 BA ltac:(lia) ltac:(lia)) as HP3.
rewrite (nth_read (Z.to_nat (2 + cl + 1)) data (Z_to_bv 8 0)) in HP1 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 0)) data (Z_to_bv 8 0)) in HP0 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 2)) data (Z_to_bv 8 0)) in HP2 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 3)) data (Z_to_bv 8 0)) in HP3 by lia.
step. step. step. step. step. step.
do 9 step. step. step. do 4 step. step.
evt_done5.

rewrite !(unsigned_lit cl) by lia. rewrite !(unsigned_lit (Z.of_nat (length data))) by lia.
replace (Z.of_nat (length data) - cl + -6) with (Z.of_nat (length data) - 6 - cl) by lia.
replace (buf + 2 + cl + 4) with (buf + 6 + cl) by lia.
assert (CALLS1 : (1 <= calls_of data)%nat) by (unfold calls_of; destruct (Z.to_nat (cfglen_of data)); lia).
rewrite (zero_lines_split (calls_of data)) by exact CALLS1.
eapply (aj5_conseq HIx); [| apply t_emit_W_app].
eapply (TRUN cap buf m md A B); [| subst cl; lia | exact FRM | apply t_emit_has_nil |].
{ constructor; [exact DM | exact HP6 | exact REQ | exact Hcap | exact Hlen | exists junk; exact BLK | exists errv; exact ERR | exact ST
| exists j8, x7, x6, x5, x4, x3, x2, x1, x0; exact FR | exact Hfds | exact Hfs | exact HBUD]. }

intros m' md' A' B' LK F' fc' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' TI.
pose proof (t_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TI) as HP'.
pose proof (heapA_cok A4L HIx _ _ _ _ _ _ _ HP') as HCK'.        unfold TRUN_RET_A.
d5_enter.
unfold sxb. rewrite byte_signed. fold (hb data 1).
pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as R1. unfold bv_modulus in R1. cbn in R1. fold (hb data 1) in R1.
step.

destruct (Z.ltb_spec (hb data 1) 128) as [NC|CNT].
--
if_falsex. step. step. evt_done5.
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 0 buf cap LK m' md' A' B'). exact TI.
--
if_truex. step. step. step.
replace (ret_pc (Z_to_bv 64 596820)) with (Z_to_bv 64 596820 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. step. step. if_truex. evt_done5.
apply (tail_ok HIx SYS reqA OBL_FREE_NN OBL_CS_WIDE argv USP LO fs LM0 USPF LOF TOPF 0 buf cap LK m' md' A' B'). exact TI.
Qed.
End Hdr.
