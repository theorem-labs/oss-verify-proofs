(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq Lib.GwApply Qfw3 Q9A7 QlEo Q5Rg UEQM Qy5Y UKNz Uv2Y UXT6 UotY UGNu QZAi QUZl Qfya QGeV QRjH Q9ox QBxa QSpR QsRG QuJV UFeQ Um90 QHnV Qsw7 QCcH QEpW QbVh QZDE QeZD QqWy QV3E UmAj Uc9I UaOl U4FC Uqqm UDH9 U5Hp UtkK QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq.Mq0 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3.Mq2 Q9A7.Mq1 QlEo.Mq0 QWxq.Mq1 Q5Rg.Mq0 Q5Rg.
Import UEQM.
Import Qy5Y.Mq4.
Import UKNz Uv2Y UXT6 UotY UGNu.
Import QZAi.Mq1 QUZl Qfya QGeV.
Import QRjH Q9ox.Mq2 QBxa.Mq5.

Import QHnV Qsw7.

Import QEpW QWxq QlEo QbVh QZDE.
Import QeZD QqWy QV3E.
Import UmAj Uc9I UaOl.
Import U4FC Uqqm UDH9 U5Hp UtkK UtkK.Mq0.
Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition hb (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition cfg_of (data : list byte) : Z := hb data 0 + 256 * hb data 1.
Definition cfglen_of (data : list byte) : Z := (cfg_of data) mod 32768.
Definition counting_of (data : list byte) : bool := 32768 <=? cfg_of data.
Definition calls_of (data : list byte) : nat :=
match Z.to_nat (cfglen_of data) with O => 1%nat | _ => S (Z.to_nat (hb data 2 mod 4)) end.

Definition TRUN_SYM : Z := 0x20e54.
Definition TRUN_RET : Z := 0x20cf8.

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
Context {AMB : Amb}.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (data : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Variables (fds0 : list (word * FdEntry)).
Hypothesis FD1 : fd_lookup fds0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Notation B := usp0.

Record RPOST (buf cap : Z) (LK : list (Z * Z)) (m : mem) (md : Model) (A : hstate) (pending : list byte) : Prop := MKRP {
rp_dfx   : DFX usp0 pp tid path m;
rp_heap  : HEAPc B A ((buf, cap) :: LK) m md;
rp_errno : exists errv, rw_cells rsegs m RERRNO [C4 errv];
rp_fs    : m_fs md = fs;
rp_out   : STDOUT m md pending;
rp_err   : STDERR m }.

Definition trun_stmt : Prop :=
forall (buf cap : Z) (m : mem) (md : Model) (A : hstate) (Tok Tfail : TSet)
(gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HINV usp0 tid ppw path data fs fds0 cap buf m md A ->
(6 + cfglen_of data <= Z.of_nat (length data)) ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 -> QCcH.frm0 fc -> Tok [] ->
(forall (m' : mem) (md' : Model) (A' : hstate) (LK : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
RPOST buf cap LK m' md' A' (zero_lines (Nat.pred (calls_of data))) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp' tp t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET) fc' None m' (seg_rom rsegs)) md') Tok) ->
(forall (m' : mem) (md' : Model) (A' : hstate) (LK : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32)
(gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
RPOST buf cap LK m' md' A' [] ->
Z.of_nat (length data) - 6 - cfglen_of data > 0 ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp' tp t0' t1' t2'
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 2) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 TRUN_RET) fc' None m' (seg_rom rsegs)) md') Tfail) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (usp0 - 128)) gp tp t0 t1 t2
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf)
(Z_to_bv 64 (buf + 2)) (Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
a4 a5 a6 a7
(Z_to_bv 64 (cfglen_of data)) (Z_to_bv 64 (buf + 6 + cfglen_of data)) (Z_to_bv 64 (Z.of_nat (length data) - 6 - cfglen_of data))
s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TRUN_SYM) fc None m (seg_rom rsegs)) md)
(if (Z.of_nat (length data) - 6 - cfglen_of data =? 0) then t_emit (W 1 (zero_lines 1)) Tok
else (t_emit (W 1 (zero_lines 1)) Tok)   ).

Definition hdr_leaf_stmt : Prop :=
forall (pc : Z) (msg : list byte) (K : TSet) (buf cap : Z) (m : mem) (md : Model) (A : hstate)
(gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word) (F : bvmap 5 word) (fc : bv 32),
((pc = 0x20d3c /\ msg = msg_short) \/ (pc = 0x20d58 /\ msg = msg_overrun)) ->
K [] ->
DF usp0 pp tid path m -> HEAPc B A [(buf, cap)] m md -> (exists errv, rw_cells rsegs m RERRNO [C4 errv]) ->
gp = Z_to_bv 64 0x10800 -> tp = Z_to_bv 64 0x77c00 ->
fd_lookup (m_fds md) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
(forall (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
DFX usp0 pp tid path m' -> HEAPc B A [(buf, cap)] m' md ->
(exists errv, rw_cells rsegs m' RERRNO [C4 errv]) ->
(forall a, 0x66e28 <= a < 0x66f10 -> m' (wa a) = None) ->
UFeQ.Mq0.file_clean m' 0x66d38 (Z_to_bv 64 0x98348) (Z_to_bv 64 0) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 MAIN_FREE_RET) (Z_to_bv 64 (usp0 - 128)) gp tp t0' t1' t2' s0 (Z_to_bv 64 buf) (Z_to_bv 64 buf) a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (Z_to_bv 64 FREE_SYM) fc' None m' (seg_rom rsegs)) md) K) ->
realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (usp0 - 128)) gp tp t0 t1 t2 s0 (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)) md)
(t_emit (W 2 msg) K).

Hypothesis TRUN : trun_stmt.
Hypothesis HLEAF : hdr_leaf_stmt.

#[using="FD2 TRUN HLEAF"] Theorem hdr_ok : hdr_stmt usp0 tid ppw path data fs fds0.
Proof.
unfold hdr_stmt. intros until fc. intros HI Hgp Htp FRM. subst gp tp.
destruct HI as [D HP DSH SH Hcap Hlen (junk & BLK) (errv & ERR) Hfds Hfs HBUD].
pose proof (f_sp _ _ _ _ _ D) as SPB. pose proof (f_ceil _ _ _ _ _ D) as CEIL.
pose proof (heapc_model_ok B _ _ _ _ HP) as MOK. pose proof (heapc_mem_inv B _ _ _ _ HP) as MI.
pose proof (heapc_blk B _ _ _ _ buf cap HP ltac:(left; reflexivity)) as (_ & _ & Bpos & Bhi & _ & Bimg).
unfold alloc_ceiling in Bhi. unfold RIMG_LO, RIMG_HI in Bimg.
word_range ppw PPR.
apply rz_evt; [exact MOK|]. unfold HDRPT.
step. step.
destruct (Nat.lt_ge_cases (length data) 6) as [SHORT|LONG].
-
if_truex. apply evt_RZ_done.
unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite t_die_unfold.
eapply (HLEAF 0x20d3c msg_short); [left; split; reflexivity| apply t_emit_has_nil| exact D| exact HP| exists errv; exact ERR| reflexivity| reflexivity| exact (CFDS_2 _ FD2 _ Hfds)|].
intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' D' HP' ERR' OUTN ERRC.
eapply rz_conseq; [| apply t_emit_W_nil; apply t_emit_has_nil].
apply (tail_ok usp0 tid ppw path fs 2 buf cap [] m' md A []); [| reflexivity].
constructor.
+ exact D'.
+ exact HP'.
+ exact ERR'.
+ exact Hfs.
+ left. split; [reflexivity| exists (wz 0), (wz 0); apply file_clean_pristine; [right; reflexivity| exact OUTN]].
+ right. eexists _, _. exact ERRC.
+ lia.
- if_falsex.

pose proof BLK as [[[WF1 _] BA] _]. cbn [cells_bytes cbytes app] in BA. apply bytes_at_app in BA as [BA _].
pose proof (bytes_at_read rsegs m buf data 0 1 BA ltac:(lia) ltac:(lia)) as HR0.
pose proof (bytes_at_read rsegs m buf data 1 1 BA ltac:(lia) ltac:(lia)) as HR1.
change (Z.to_nat 0) with 0%nat in HR0. change (Z.to_nat 1) with 1%nat in HR1.
rewrite (nth_read 0%nat data (Z_to_bv 8 0)) in HR0 by lia. rewrite (nth_read 1%nat data (Z_to_bv 8 0)) in HR1 by lia.
step. step. step. step. step.
rewrite hdr_cfg_word. fold (hb data 0) (hb data 1). fold (cfg_of data). fold (cfglen_of data).
pose proof (Z.mod_pos_bound (cfg_of data) 32768 ltac:(lia)) as CLR. fold (cfglen_of data) in CLR.
set (cl := cfglen_of data) in *.
assert (LEN64 : Z.of_nat (length data) < 2^26) by lia.
rewrite (t_body_cases data fs LONG) by (unfold MAX_INPUT; lia).
step. step.
destruct (Nat.lt_ge_cases (length data) (6 + Z.to_nat cl)) as [OVR|FIT].
+
if_truex. apply evt_RZ_done.
replace (length data <? 6 + Z.to_nat cl)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite t_die_unfold.
eapply (HLEAF 0x20d58 msg_overrun); [right; split; reflexivity| apply t_emit_has_nil| exact D| exact HP| exists errv; exact ERR| reflexivity| reflexivity| exact (CFDS_2 _ FD2 _ Hfds)|].
intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' D' HP' ERR' OUTN ERRC.
eapply rz_conseq; [| apply t_emit_W_nil; apply t_emit_has_nil].
apply (tail_ok usp0 tid ppw path fs 2 buf cap [] m' md A []); [| reflexivity].
constructor; [exact D'| exact HP'| exact ERR'| exact Hfs| left; split; [reflexivity| exists (wz 0), (wz 0); apply file_clean_pristine; [right; reflexivity| exact OUTN]]| right; eexists _, _; exact ERRC| lia].
+ if_falsex.
replace (length data <? 6 + Z.to_nat cl)%nat with false by (symmetry; apply Nat.ltb_ge; lia).

pose proof (bytes_at_read rsegs m buf data (2 + cl + 1) 1 BA ltac:(lia) ltac:(lia)) as HP1.
pose proof (bytes_at_read rsegs m buf data (2 + cl + 0) 1 BA ltac:(lia) ltac:(lia)) as HP0.
pose proof (bytes_at_read rsegs m buf data (2 + cl + 2) 1 BA ltac:(lia) ltac:(lia)) as HP2.
pose proof (bytes_at_read rsegs m buf data (2 + cl + 3) 1 BA ltac:(lia) ltac:(lia)) as HP3.
rewrite (nth_read (Z.to_nat (2 + cl + 1)) data (Z_to_bv 8 0)) in HP1 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 0)) data (Z_to_bv 8 0)) in HP0 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 2)) data (Z_to_bv 8 0)) in HP2 by lia.
rewrite (nth_read (Z.to_nat (2 + cl + 3)) data (Z_to_bv 8 0)) in HP3 by lia.
step. step. step. step. step. step.
do 9 step. step. step. do 4 step. step.
apply evt_RZ_done.
rewrite (unsigned_lit cl) by lia.
replace (Z.of_nat (length data) + - cl + -6) with (Z.of_nat (length data) - 6 - cl) by lia.
replace (buf + 2 + cl + 4) with (buf + 6 + cl) by lia.
set (Tok := t_emit (W 1 (zero_lines (Nat.pred (calls_of data)))) (t_exit (exit_code 0) fs)).
set (Tfail := t_exit (exit_code (if counting_of data then 0 else 2)) fs).
assert (CALLS1 : (1 <= calls_of data)%nat) by (unfold calls_of; destruct (Z.to_nat (cfglen_of data)); lia).
apply (rz_conseq rsegs _ (if (Z.of_nat (length data) - 6 - cl =? 0) then t_emit (W 1 (zero_lines 1)) Tok else (t_emit (W 1 (zero_lines 1)) Tok)   )).
2:{ subst cl. destruct (Z.eqb_spec (Z.of_nat (length data) - 6 - cfglen_of data) 0) as [E|NE].
- replace (length data - 6 - Z.to_nat (cfglen_of data))%nat with 0%nat by lia.
rewrite (zero_lines_split (calls_of data)) by exact CALLS1. apply t_emit_W_app.
- destruct (length data - 6 - Z.to_nat (cfglen_of data))%nat eqn:EQ; [lia|].
rewrite (zero_lines_split (calls_of data)) by exact CALLS1. apply t_emit_W_app. }
eapply (TRUN buf cap m md A Tok Tfail); [| lia| reflexivity| reflexivity| exact FRM| subst Tok; apply t_emit_has_nil| |].
{ constructor; [exact D| exact HP| exact DSH| exact SH| exact Hcap| exact Hlen| exists junk; exact BLK| exists errv; exact ERR| exact Hfds| exact Hfs| exact HBUD]. }
*
intros m' md' A' LK F' fc' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
destruct RP as [D' HP' ERR' Hfs' OUT' ERR2'].
pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'.
unfold TRUN_RET. apply rz_evt; [exact MOK'|].
unfold sxb. rewrite byte_signed. fold (hb data 1).
pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as R1. unfold bv_modulus in R1. cbn in R1. fold (hb data 1) in R1.
step.
destruct (Z.ltb_spec (hb data 1) 128) as [NC|CNT].
--
if_falsex. step. step. step. step. apply evt_RZ_done.
apply (tail_ok usp0 tid ppw path fs 0 buf cap LK m' md' A'); [| reflexivity].
constructor; auto. lia.
--
if_truex. step. step. step. step. step. step. if_truex. step. step. apply evt_RZ_done.
apply (tail_ok usp0 tid ppw path fs 0 buf cap LK m' md' A'); [| reflexivity].
constructor; auto. lia.
*
intros m' md' A' LK F' fc' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP PLP.
destruct RP as [D' HP' ERR' Hfs' OUT' ERR2'].
pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'.
unfold TRUN_RET. apply rz_evt; [exact MOK'|].
unfold sxb. rewrite byte_signed. fold (hb data 1).
pose proof (bv_unsigned_in_range 8 (nth 1 data (Z_to_bv 8 0))) as R1. unfold bv_modulus in R1. cbn in R1. fold (hb data 1) in R1.
assert (CNTE : counting_of data = (128 <=? hb data 1)).
{ unfold counting_of, cfg_of. pose proof (bv_unsigned_in_range 8 (nth 0 data (Z_to_bv 8 0))) as R0. unfold bv_modulus in R0. cbn in R0. fold (hb data 0) in R0.
destruct (Z.leb_spec 128 (hb data 1)); [apply Z.leb_le; lia| apply Z.leb_gt; lia]. }
step.
destruct (Z.ltb_spec (hb data 1) 128) as [NC|CNT].
-- if_falsex. step. step. step. step. apply evt_RZ_done.
subst Tfail. rewrite CNTE. replace (128 <=? hb data 1) with false by (symmetry; apply Z.leb_gt; lia).
eapply rz_conseq; [| apply t_emit_W_nil; apply t_emit_has_nil].
apply (tail_ok usp0 tid ppw path fs 2 buf cap LK m' md' A'); [| reflexivity].
constructor; auto. lia.
-- if_truex. step. step. step. step. step. step. if_truex. step. step. apply evt_RZ_done.
subst Tfail. rewrite CNTE. replace (128 <=? hb data 1) with true by (symmetry; apply Z.leb_le; lia).
eapply rz_conseq; [| apply t_emit_W_nil; apply t_emit_has_nil].
apply (tail_ok usp0 tid ppw path fs 0 buf cap LK m' md' A'); [| reflexivity].
constructor; auto. lia.
Qed.
End Hdr.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UotY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UotY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGNu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGNu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QwQw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwQw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3dN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3dN.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QV3E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV3E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmAj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmAj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc9I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc9I.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udkw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udkw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaOl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaOl.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4FC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4FC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uqqm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uqqm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Hp. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U56U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U56U. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section AmbE.
Context {AMB : Amb}.

#[using="Type"] Lemma DF_munch_e : forall usp0 pp tid path m m' W,
DF usp0 pp tid path m -> munch W m m' -> wmono rsegs m m' -> stk rsegs m' (usp0 - 8388608) (usp0 - 128) ->
Forall (fun iv => snd iv <= usp0 - 128 /\ (snd iv <= 0x10000 \/ 0x99000 <= fst iv \/ (RERRNO <= fst iv /\ snd iv <= RERRNO + 4)) /\ fst iv <= snd iv) W ->
DF usp0 pp tid path m'.
Proof.
intros usp0 pp tid path m m' W D MU WM ST' FW. destruct D as [SPB STK FRM TID SELF PRS STG PTH PTH8 LOC CEIL].
assert (OUT : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ (RERRNO <= x < RERRNO + 4))) -> outside W x).
{ intros x Hx. unfold RERRNO, RATP in *. clear -FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in FW as [[F1 [F2 F3]] FW]. cbn [fst snd] in *.
split; [lia| apply IH; exact FW]. }
assert (EQ : forall x, (usp0 - 128 <= x \/ (0x10000 <= x < 0x99000 /\ ~ (RERRNO <= x < RERRNO + 4))) -> 0 <= x < 2^64 -> m' (wa x) = m (wa x)).
2: unfold RERRNO, RATP in EQ.
{ intros x Hx Hr. apply MU. unfold wa. rewrite unsigned_lit by lia. apply OUT. exact Hx. }
destruct PTH as (P1 & P2 & P3). destruct TID as [T1 T2].
constructor.
- exact SPB.
- destruct (stk_split rsegs m (usp0 - 8388608) (usp0 - 128) usp0 STK ltac:(lia)) as [_ S2].
apply (stk_merge rsegs m' (usp0 - 8388608) (usp0 - 128) usp0 ST'); [| lia].
eapply stk_transport; [exact S2| exact MU| exact WM|]. intros x Hx. left. apply OUT. lia.
- destruct FRM as [[WF BA] WR]. split; [split; [exact WF|]|].
+ eapply bytes_at_agree; [exact BA|]. intros x Hx. apply EQ; [left; lia|]. rewrite cells_bytes_length in Hx by exact WF. cbn in Hx. lia.
+ destruct WR as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. apply WM. apply W3. exact Hi.
- split; [| exact T2]. eapply bytes_at_agree; [exact T1|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- eapply bytes_at_agree; [exact SELF|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- unfold pris in *. apply Forall_forall. intros [lo hi] IN a Ha. cbn [fst snd] in Ha.
pose proof (proj1 (Forall_forall _ _) PRS _ IN a Ha) as E0. cbn [fst snd] in E0. rewrite <- E0. apply EQ; [right|];
unfold PRIS in IN; cbn in IN; repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]); destruct IN.
- eapply stk_transport; [exact STG| exact MU| exact WM|]. intros x Hx. left. apply OUT. right. unfold RSTAGE, RSTAGE_SZ, RERRNO, RATP in *. lia.
- split; [| lia]. eapply bytes_at_agree; [exact P1|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply EQ; [left; lia| lia].
- destruct PTH8 as (t8 & Q1 & Q2). exists t8. split; [| exact Q2]. eapply bytes_at_agree; [exact Q1|]. intros x Hx. rewrite Q2 in Hx. cbn in Hx. apply EQ; [left; lia| lia].
- eapply bytes_at_agree; [exact LOC|]. intros x Hx. cbn in Hx. apply EQ; [right; lia| lia].
- exact CEIL.
Qed.
End AmbE.

Section ReadDir.
Context {AMB : Amb}.
Variables (usp0 tid : Z) (ppw : word) (path : list byte) (fs : Fs.Fs).
Notation pp := (bv_unsigned ppw).
Variables (fds0 : list (word * FdEntry)).
Hypothesis FD2 : fd_lookup fds0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Hypothesis DOT : path = QBxa.Mq5.dot_path.
Hypothesis LOOM : leaf_oom_stmt usp0 pp tid path.
Hypothesis LERR : leaf_readerr_stmt usp0 pp tid path.
Notation B := usp0.
Notation LO := (usp0 - 8388608).
Notation SP := (usp0 - 128).

#[using="FD2 DOT LOOM LERR"] Theorem read_entry_dir :
read_entry_stmt usp0 tid ppw path (fd_insert fds0 (Z_to_bv 64 3) FdDir) fs (t_opened_dir path fs).
Proof.
unfold read_entry_stmt, t_opened_dir.
intros F fc t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 m md DE HP HBUD Hfds Hfs FRM.
pose proof (DF_of_entry _ _ _ _ _ DE) as D. destruct DE as [SPB STK FRMc ERRC _ _ _ _ _ _ MI _ _ _ _ _ PTH _ _ CEIL].
eapply (heapc_malloc_first B rmalloc_spec
(Z_to_bv 64 0x20bd8) (Z_to_bv 64 SP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77c00)
t0 t1 t2 (Z_to_bv 64 2) s1 (Z_to_bv 64 65536) a1 a2 a3 a4 a5 a6 a7 ppw s3 (Z_to_bv 64 3) (Z_to_bv 64 65536)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6
F fc m md (t_die msg_oom fs) _ A0 [] 65536 LO (wz 0) 0 (DRV_W - FRESHW 0) (DRV_D - FRESHD)%nat HP A0_GSH).
- rewrite A0_hshift. lia.
- lia.
- apply first_req_65536.
- eapply BUD_mono; [exact HBUD| |]. { unfold DRV_W, FRESHW, AMW, PGSZ. cbn. lia. } { unfold DRV_D, FRESHD. lia. }
- unfold DRV_W, FRESHW, AMW, PGSZ. cbn. lia.
- destruct (stk_split rsegs m LO SP usp0 STK ltac:(lia)) as [S1 _]. rewrite unsigned_lit by lia. exact S1.
- unfold alloc_ceiling. lia.
- rewrite unsigned_lit by lia. unfold RMALLOC_STACK. lia.
- rewrite unsigned_lit by lia. lia.
- unfold RATP, RERRNO in *. exact ERRC.
- reflexivity.
- reflexivity.
-
intros ms' m' md' A' errv' RS VM ST' (LB0 & PLB & PRES) ERR' HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES (heapc_mem_inv B _ _ _ _ HP') ST' eq_refl ltac:(lia))).
reenter MOK'. step. if_truex. apply evt_RZ_done.
rewrite <- Hfs, <- (vm_only_fs md md' VM).
eapply LOOM; [exact D'| exact HP'| reflexivity| reflexivity| | right; reflexivity].
rewrite (vm_only_fds md md' VM), Hfds. rewrite Qn1e.fd_lookup_insert_neq by exact neq23. exact FD2.
-
intros ms' m' md' A' r errv' RS VM ST' (LB0 & PLB & PRES) ERR' Hr (junk & BLK) RNG HP' SH' DSH' BUD'.
open_ret RS. pose proof (heapc_model_ok B _ _ _ _ HP') as MOK'. pose proof (heapc_mem_inv B _ _ _ _ HP') as MI'.
rewrite unsigned_lit in ST', PRES by lia.
assert (D' : DF B pp tid path m') by (eapply (DF_alloc B pp tid path m m' LB0 SP LO D PRES MI' ST' eq_refl ltac:(lia))).
destruct RNG as (R1 & R2 & R3 & R4 & R5). unfold alloc_ceiling in R4.
word_range ppw PPR. pose proof stage_bounds as (SB1 & SB2 & SB3 & SB4).

destruct (stk_carve_lo m' RSTAGE (RSTAGE + RSTAGE_SZ) (Z.to_nat 65536) (f_stage _ _ _ _ _ D') ltac:(unfold RSTAGE_SZ; lia)) as [_ (sjunk & DST)].
reenter MOK'. step. if_falsex. step. step. step. step.
step. if_truex. step. step.
step. step. step. if_falsex. step. step. step. step.
apply evt_RZ_done.
eapply (read_dir_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' md' _ RSTAGE 65536 LO errv' MOK' eq_refl);
[reflexivity| reflexivity| rewrite (vm_only_fds md md' VM), Hfds; apply Qn1e.fd_lookup_insert_eq| lia| unfold RSTAGE; lia| unfold RSTAGE; lia| lia| exists sjunk; exact DST
| rewrite unsigned_lit by lia; exact ST'| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; unfold RATP, RERRNO in *; exact ERR'| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI'| reflexivity|].
intros b1 b2 b3 b4 b5 b6 b7 m2. rewrite !unsigned_lit by lia. intros MU2 WM2 MI2 ST2 ERR2.
assert (D2 : DF B pp tid path m2).
{ eapply DF_munch_e; [exact D'| exact MU2| exact WM2| exact ST2|]. constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; unfold RERRNO, RATP; lia| constructor]]. }
pose proof (heapc_model_ok B _ _ _ _ HP') as MOKx.
assert (HP2 : HEAPc B A' [(r, 65536)] m2 md').
{ eapply (heapc_frame B); [exact HP'| | exact WM2| exact MI2]. intros a Ha NCW. apply MU2. unfold wa. rewrite unsigned_lit by lia. cbn.
repeat split; intros [X1 X2]; apply NCW.
- right; left. lia.
- right; right. unfold ralloc_zone, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD, RATP, RDATA_LO, RIMG_HI, RHEX_GOT, RHEX_PTR in *. lia. }
reenter MOKx. step. if_truex. apply evt_RZ_done.
rewrite <- Hfs, <- (vm_only_fs md md' VM).
rewrite <- (Z_to_bv_bv_unsigned ppw).
eapply LERR; [exact D2| exact HP2| exact DOT| reflexivity| reflexivity|].
rewrite (vm_only_fds md md' VM), Hfds. rewrite Qn1e.fd_lookup_insert_neq by exact neq23. exact FD2.
Qed.
End ReadDir.
