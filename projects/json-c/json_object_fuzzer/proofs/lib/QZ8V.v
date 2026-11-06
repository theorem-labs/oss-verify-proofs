(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Ql4f Q9O6 QL3k Q228 QiVi Q1Ey Q4xz QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 QlKV.Mq6 Ql4f.Mq2 Q228.Mq0 QiVi.Mq1 Qwm6.Mq1.

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

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 224 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - AESC_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 6 * n < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 (6 * n) <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis INs : In (sa, sk) LB.
Hypothesis Hs1 : sa <= Sa.
Hypothesis Hs2 : Sa + n <= sa + sk.
Hypothesis SRC0 : bytes_at asegs m0 Sa src.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis Hn : 0 < n < 2^31.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n q d Fr).
Notation st_escx := (st_escA sp gp Sa n q Fr).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac jt_eval :=
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma esc_joinA :
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos + 1 -> 0 <= pos < n -> 0 <= e <= 6 * start ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_JOIN x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until e. intros INV FS FR Hst Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_escA, AESC_JOIN. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
destruct (Z.eq_dec n (pos + 1)) as [E | NE].
- rewrite <- E. rewrite (proj2 (Fs.bv_eqb_eq _ _) eq_refl). fold_mkR.
evt_done5. unfold exitKA in EX. eapply (EX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m md A start e); [exact INV | exact FS | exact FR | lia | lia].
- if_falsex. fold_mkR.
evt_done5. unfold loopKA in IH. eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m md A (pos + 1) start e); [exact INV | exact FS | exact FR | lia | lia | lia | lia].
Qed.

Lemma esc_srcA : forall v A e m md, esc_invx v A e m md -> bytes_at asegs m Sa src.
Proof.
intros v A e m md (j0 & j1 & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & _).
eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC0 |].
eapply client_range_block; [apply in_or_app; left; exact INs | lia | rewrite SRCL; cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma esc_fetchA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z) (c : byte),
esc_invx 248 A e m md -> 0 <= pos < n -> nth_error src (Z.to_nat pos) = Some c ->
(forall a0' a1' a3' : word,
AJ5 A4L HIx A T md (st_escx 0xa0068 x1 t0 t1 t2 a0' a1' a2 a3' a4 a5 a6 a7 (wz (bv_unsigned c)) t3 t4 t5 t6 F' fc' m pos)) ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV Hpos Hc K.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (Q1Ey.payload_byteA _ _ _ _ _ SRC Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct (payload_shadow_of_blk HIx _ _ _ _ _ _ _ sa sk (Sa + pos) HP INsF ltac:(lia)) as (v & SHP & Hv). unfold A_SB in SHP.
unfold st_escA, AESC_LOOP. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
sh_norm.
step. step.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_falsex.
step. change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). fold_mkR.
evt_done5. apply K.
- rewrite (sxb_small v) by lia. if_truex.
step. step.
rewrite (unsigned_lit (Sa + pos)) by lia. rewrite land7_mod8 by lia.
pose proof (Z.mod_pos_bound (Sa + pos) 8 ltac:(lia)) as MB.
if_truex.
step. change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). fold_mkR.
evt_done5. apply K.
Qed.

Lemma esc_iter_regularA :
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
32 <= bv_unsigned c -> bv_unsigned c <> 34 -> bv_unsigned c <> 92 -> bv_unsigned c <> 47 ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc C32 C34 C92 C47 IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a0' a1' a3'.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct (Z.lt_ge_cases 47 (bv_unsigned c)) as [HI|LOW].
- step.
if_truex. step. step. if_falsex. step. step. if_truex. fold_mkR.
evt_done5. eapply esc_joinA; [exact INV | exact FS | exact FR | lia | lia | exact He | exact IH | exact EX].
- assert (E : bv_unsigned c = 32 \/ bv_unsigned c = 33 \/ bv_unsigned c = 35 \/ bv_unsigned c = 36 \/ bv_unsigned c = 37 \/
bv_unsigned c = 38 \/ bv_unsigned c = 39 \/ bv_unsigned c = 40 \/ bv_unsigned c = 41 \/ bv_unsigned c = 42 \/
bv_unsigned c = 43 \/ bv_unsigned c = 44 \/ bv_unsigned c = 45 \/ bv_unsigned c = 46) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; rewrite E.
all: step; if_falsex; step; step; step; if_truex; step; step; if_falsex; step; step; if_truex; fold_mkR.
all: evt_done5; eapply esc_joinA; [exact INV | exact FS | exact FR | lia | lia | exact He | exact IH | exact EX].
Qed.

Lemma esc_appendA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (v e b k : Z) (sbs : list byte),
esc_invx v A e m md ->
bytes_at asegs m b sbs -> Z.of_nat (length sbs) = k -> 0 <= k < 2^31 -> 0 <= b ->
src_locA LB ((Fr, 0) :: FRS) b k -> (0 < k -> unpoisoned asegs m A_SB b k) ->
0 <= e -> e + k <= 6 * n ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
esc_invx v A' (e + k) m' md' -> fsaved F F' -> frm0 fc' -> bytes_at asegs m' b sbs ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz q) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz q) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros until sbs. intros INV SB SBL Hk Hb SRCB UPS He Hek -> Hret Hret2 FS FRM K.
destruct INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := sbs) (e := e);
[ exact INV1 | exact SB | exact SBL | exact Hk | exact Hb | exact SRCB | exact UPS | exact He | exact Hek
| lia | clear - Hq32; Z.div_mod_to_equations; lia | lia | unfold_consts; lia | reflexivity | exact Hret | exact Hret2 | exact FS | exact FRM | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INV' FS' FR' SB'.
apply K; [| exact FS' | exact FR' | exact SB'].
exists j0, j1, gj, j8, sb, j17. exact INV'.
Qed.

Definition esc_jtabA : list byte := Eval vm_compute in match image_bytes asegs 0x2326c 160 with Some bs => bs | None => [] end.
Lemma esc_jtabA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x2326c [CB 160 esc_jtabA].
Proof.
intros m MI. change 160%nat with (length esc_jtabA).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length esc_jtabA)) with 160%Z. lia.
Qed.
Definition esc_litA (cv : Z) : Z :=
match cv with 8 => 0x235a0 | 9 => 0x23600 | 10 => 0x235c0 | 12 => 0x23620 | 13 => 0x235e0 | 34 => 0x23640 | 92 => 0x23660 | 47 => 0x23680 | _ => 0 end.
Definition esc_litbA (cv : Z) : list byte := [b8 92; b8 (match cv with 8 => 98 | 9 => 116 | 10 => 110 | 12 => 102 | 13 => 114 | _ => cv end)].
Lemma esc_lit_okA : forall cv, In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
ro_bytes_b asegs (esc_litA cv) (esc_litbA cv) = true /\ src_ro_chk (esc_litA cv) 2 = true.
Proof. intros cv H. cbn in H. repeat (destruct H as [<- | H]; [split; vm_compute; reflexivity|]). destruct H. Qed.

Lemma esc_special_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e cv : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= pos < n -> 0 <= e <= 6 * pos ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa0094 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz cv) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cv. intros INV FS FR Hpos He Hcv IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (esc_jtabA_ro m MI) as JT.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
destruct (esc_lit_okA cv Hcv) as [LITB LITC].
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (TAIL : forall (u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
AJ5 A4L HIx A T md (MS (mkR (wz 0xa0040) (wz q) gp (wz A_TP) u0 u1 u2 sp (wz q) (wz pb) (wz (esc_litA cv)) (wz 2) b3 b4 b5 b6 b7
(wz 47) (wz n) (wz Sa) (wz cv) (wz 0) (wz pos) (wz pos) (wz (Fr / 8 + 2147450880)) (wz 2147450880) (wz ESC_MASK) u3 u4 u5 u6)
F' (wz AMEMAPPEND) fc' None m (seg_rom asegs))).
{ intros.
eapply esc_appendA with (sbs := esc_litbA cv) (e := e) (v := 248);
[ exact INV | apply Q4xz.rodata_bytes_at; [exact MI | exact LITB | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv]
| reflexivity | lia | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv
| right; right; apply src_globA_of_chk; exact LITC
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; exact LITC | lia]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
pose proof INV' as (j0' & j1' & gj' & j8' & sb' & j17' & INV1').
pose proof INV1' as (buf' & cap' & bpos' & content' & errv' & B' & HP' & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. fold_mkR.
evt_done5. eapply esc_joinA; [exact INV' | exact FS' | exact FR' | lia | lia | lia | exact IH | exact EX]. }
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hcv' := Hcv). cbn in Hcv'.
destruct Hcv' as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; rewrite <- E in *.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 3 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. step. step. if_lit. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 5 step. fold_mkR. evt_done5. apply TAIL.
Qed.

Lemma esc_special_c4A :
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e cv : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa0080 x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 (wz cv) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cv. intros INV FS FR Hst Hpos He Hcv IH EX.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct (Z.lt_ge_cases start pos) as [LT | GE].
-
step. if_falsex.
step. step.
rewrite (unsigned_lit pos), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 248);
[ exact INV
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP | exact INsF | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_special_tailA; [exact INV' | exact FS' | exact FR' | lia | lia | exact Hcv | exact IH | exact EX].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_special_tailA; [exact INV | exact FS | exact FR | lia | lia | exact Hcv | exact IH | exact EX].
Qed.

Lemma esc_iter_specialA :
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
In (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc Hcv IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a0' a1' a3'.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hcv' := Hcv). cbn in Hcv.
destruct Hcv as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; rewrite <- E in *.
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
-  step. if_lit. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
Qed.

Definition esc_apart (a k : Z) : Prop :=
(a + k <= lo \/ q <= a) /\ (a + k <= Fr \/ Fr + 56 <= a) /\ (a + k <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= a).
Definition esc_privW (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= q) \/ (Fr <= fst iv /\ snd iv <= Fr + 56) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 8).
Lemma esc_apart_disjoint : forall W a k, Forall esc_privW W -> esc_apart a k -> disjoint_from W a k.
Proof.
intros W a k HW (H1 & H2 & H3). induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold esc_privW in Hiv. cbn [fst snd] in Hiv. lia.
Qed.

Definition esc_inv_sbx (v : Z) (sbx : list byte) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists j0 j1 gj j8 j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb q d Fr j0 j1 gj j8 sbx j17 v) e m md.
Lemma esc_inv_of_sbx : forall v sbx A e m md, esc_inv_sbx v sbx A e m md -> esc_invx v A e m md.
Proof. intros v sbx A e m md (j0 & j1 & gj & j8 & j17 & H). exists j0, j1, gj, j8, sbx, j17. exact H. Qed.

Lemma esc_inv_privA : forall v v' (A : ASA A4L HIx) e m m' md W j0 j1 gj j8 sb j17 j8' sb' j17',
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb q d Fr j0 j1 gj j8 sb j17 v) e m md ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall esc_privW W ->
rw_cells asegs m' Fr (escFF j8' sb' j17') -> rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') -> stk asegs m' lo q ->
esc_inv_sbx v' sb' A e m' md.
Proof.
intros until j17'. intros INV MU WM MI' HW FF' SH' ST'.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (_ & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> esc_apart a (Z.of_nat (cells_size cs)) -> rw_cells asegs m' a cs).
{ intros a cs H AP. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM | apply esc_apart_disjoint; [exact HW | exact AP]]. }
exists j0, j1, gj, j8', j17'. exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
split.
{ destruct PB as (P1 & P2 & P3 & PBS & PBUF). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
split; [apply TR; [exact PBS | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]
| apply TR; [exact PBUF | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]]. }
unfold escCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 CHm]. apply Forall_cons_iff in CHm as [C3 _].
cbn [fst snd] in C1, C2, C3.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
split.
{ constructor; [cbn [fst snd]; apply TR; [exact C1 | unfold esc_apart, escLoc; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C3 | unfold esc_apart, escSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [exact FSUB|].
split; [apply TR; [exact ERR | unfold esc_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
split; [exact VM|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_inv_shA : forall v v' (A : ASA A4L HIx) e m m' md,
esc_invx v A e m md ->
munch [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') ->
esc_invx v' A e m' md.
Proof.
intros v v' A e m m' md (j0 & j1 & gj & j8 & sb & j17 & INV1) MU WM MI' SH'.
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _ & CHx & _ & _ & _ & STx & _).
unfold escCH in CHx. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx _]. cbn [fst snd] in FFx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
apply (esc_inv_of_sbx v' sb).
eapply (esc_inv_privA v v' A e m m' md _ j0 j1 gj j8 sb j17 j8 sb j17); [exact INV1 | exact MU | exact WM | exact MI' | | | exact SH' | ].
- constructor; [right; right; cbn [fst snd]; lia | constructor].
- eapply (rw_cells_transport asegs _ m m'); [exact FFx | exact MU | exact WM |]. unfold escFF. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I].
change (Z.of_nat (8 + (8 + (8 + (8 + (7 + (17 + 0))))))) with 56. lia.
- eapply (stk_transport_disjoint asegs _ m m'); [exact STx | exact MU | exact WM |]. cbn [disjoint_from]. split; [| exact I]. lia.
Qed.

Definition esc_pbW (buf cap : Z) (iv : Z * Z) : Prop :=
esc_privW iv \/ (pb <= fst iv /\ snd iv <= pb + PB_SZ) \/ (buf <= fst iv /\ snd iv <= buf + cap).
Lemma esc_inv_pbwA : forall v v' (A : ASA A4L HIx) e' m m' md W j0 j1 gj j8 sb j17 j8' sb' j17' buf cap errv B bpos' content',
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B m md ->
Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb q d Fr j0 j1 gj j8 sb j17 v) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> model_vm_only (cfg_model md0) (cfg_model md) ->
cap0 <= cap <= ser_capb cap0 bpos0 (6 * n) -> bB B0 - 64 * (cap - cap0) <= bB B -> bD B0 <= bD B ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall (esc_pbW buf cap) W ->
pbuf_core asegs m' pb buf bpos' cap content' -> bpos0 <= bpos' <= bpos0 + e' ->
rw_cells asegs m' Fr (escFF j8' sb' j17') -> rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') -> stk asegs m' lo q ->
esc_invx v' A e' m' md.
Proof.
intros until content'. intros HP CHm ERR HPR VM Hc HB HD MU WM MI' HW PB' Hb' FF' SH' ST'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as IMpb. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in IMpb.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as IMbuf. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in IMbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> esc_apart a (Z.of_nat (cells_size cs)) ->
(a + Z.of_nat (cells_size cs) <= pb \/ pb + PB_SZ <= a) -> (a + Z.of_nat (cells_size cs) <= buf \/ buf + cap <= a) -> rw_cells asegs m' a cs).
{ intros a cs H (A1 & A2 & A3) A4 A5. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM |].
clear - HW A1 A2 A3 A4 A5. induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in Hiv. lia. }
exists j0, j1, gj, j8', sb', j17'. exists buf, cap, bpos', content', errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [[H | [H | H]] | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia.
- right; left. exists pb, PB_SZ. split; [exact INpbX | lia].
- right; left. exists buf, cap. split; [exact INbufX | lia]. }
split; [exact PB'|].
unfold escCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 CHm]. apply Forall_cons_iff in CHm as [C3 _].
cbn [fst snd] in C1, C2, C3.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
split.
{ constructor; [cbn [fst snd]; apply TR; [exact C1 | unfold esc_apart, escLoc; cbn [cells_size csize Nat.add]; lia | unfold escLoc; cbn [cells_size csize Nat.add]; lia | unfold escLoc; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold esc_apart; cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C3 | unfold esc_apart, escSaved; cbn [cells_size csize Nat.add]; lia | unfold escSaved; cbn [cells_size csize Nat.add]; lia | unfold escSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb0; cbn [fr_ivs flat_map app]; right; right; exact Hb0|].
split; [apply TR; [exact ERR | unfold esc_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia | unfold A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia | unfold A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NIN : forall a k k', In (a, k') [(pb, PB_SZ); (buf, cap)] -> In (a, k) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) -> ~ In (a, k) (LB ++ LM ++ fr_ivs A4L FRS)).
{ intros a k k' Hin HinX Hi. rewrite app_assoc in Hi. apply in_app_or in Hi as [Hi | Hi].
- exact (nodup_prefix_suffix [(pb, PB_SZ); (buf, cap)] (LB ++ LM) a k' k ND Hin Hi).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP HinX _). cbn [fr_ivs flat_map app]. right; right. exact Hi. }
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [[H | [H | H]] | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia.
- right; left. exists pb, PB_SZ. split; [exact INpbX|]. split; [apply (NIN pb PB_SZ PB_SZ); [left; reflexivity | exact INpbX] | lia].
- right; left. exists buf, cap. split; [exact INbufX|]. split; [apply (NIN buf cap cap); [right; left; reflexivity | exact INbufX] | lia]. }
split; [exact VM|]. split; [exact Hb'|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_ctrl_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z),
esc_invx 7 A e m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * (pos + 1) ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa0234 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until e. intros INV FS FR Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _ & CHx & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold escCH in CHx. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in SHx. unfold escSH in SHx.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply esc_joinA; [eapply (esc_inv_shA 7 248 A e m m1 md INV MU WM MI1); exact SHx | exact FS | exact FR | lia | lia | lia | exact IH | exact EX].
Qed.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Lemma esc_ctrl_appA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z) (o : list byte),
esc_inv_sbx 7 (o ++ [b8 0]) A e m md -> length o = 6%nat ->
fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * pos ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa014c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until o. intros INV OL FS FR Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, FFx, SHx. unfold escLoc in LOC. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpb : In (pb, PB_SZ) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (left; reflexivity).
assert (INbuf : In (buf, cap) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; left; reflexivity).
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INpb).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INbuf).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & Hpbal & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & Hbufal & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (NEpb : pb <> buf).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni _]; subst. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb PB_SZ buf cap HP INpbX INbufX NEpb) as DPB.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
shadow_inA A4L HIx HP INpb SHpb.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (SHPR : 2147450880 <= pb / 8 + 2147450880 /\ pb / 8 + 2147450880 + 2 <= 17594333495296) by (clear - Hpb0 Hpbc ACR; Z.div_mod_to_equations; lia).
unfold st_escA. a4l.
reenterA asegs A4L HIx asegs_wx HP.
step. step.
rewrite sxb_zero. step. if_lit.
step. step. rewrite sxb_zero. step. step. step. if_lit.
step. step. step. step. step.
rewrite !sx32_small by lia. rewrite !unsigned_lit by lia. rewrite swrap32_id by lia.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFe, FFb.
change (Z.of_nat 32) with 32 in FFe, FFb.
pose proof (rw_cells_bytes_at asegs _ _ _ FFe) as SBB. cbn [cells_bytes cbytes app] in SBB. rewrite app_nil_r in SBB.
apply bytes_at_app in SBB. destruct SBB as [SBo _].
destruct (sbuf7_shadow_word m _ SHx) as [_ SHB7].
destruct (Z.lt_ge_cases (cap - bpos) 7) as [SLOW | FAST].
-
if_truex.
step. step. step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := o) (e := e) (v := 7);
[ exact (esc_inv_of_sbx _ _ _ _ _ _ INV) | exact SBo | rewrite OL; reflexivity | lia | lia
| right; left; exists Fr, 0; split; [left; reflexivity | rewrite fr_size_0; lia]
| intros _; apply unpoisoned_sbuf7; [exact HFal | lia | unfold A_SB; exact SHB7 | lia]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_ctrl_tailA; [exact INV' | exact FS' | exact FR' | lia | lia | exact IH | exact EX].
-
if_falsex.
destruct (payload_shadow_of_blk HIx _ _ _ _ _ _ _ buf cap (buf + bpos + 6) HP INbuf ltac:(lia)) as (vn & SHN & Hvn). unfold A_SB in SHN.
assert (SHNR : 2147450880 <= (buf + bpos + 6) / 8 + 2147450880 /\ (buf + bpos + 6) / 8 + 2147450880 + 1 <= 17594333495296) by (clear - Hbuf0 Hbufc Hbp Hcap ACR; Z.div_mod_to_equations; lia).
assert (HVN : 0 <= vn < 8) by (destruct Hvn as [-> | [? _]]; lia).
assert (HVM : vn = 0 \/ Z.land (buf + bpos + 6) 7 < vn) by (destruct Hvn as [-> | [? Hm]]; [left; reflexivity | right; rewrite land7_mod8 by lia; exact Hm]).
clear Hvn.
step. asan_chkA.
step. step. step. step. step. fold_mkR.

destruct (rw_cells_CB_cut asegs m buf (Z.to_nat cap) content (Z.to_nat bpos) PBUF ltac:(lia)) as [BPRE BREST].
destruct (rw_cells_CB_cut asegs m _ _ _ 6%nat BREST ltac:(lia)) as [BDST BTL].
destruct (rw_cells_CB_cut asegs m _ _ _ 1%nat BTL ltac:(lia)) as [BNUL BTL2].
rewrite Z2Nat.id in BDST, BNUL, BTL2 by lia. change (Z.of_nat 6) with 6 in BNUL, BTL2. change (Z.of_nat 1) with 1 in BTL2.
clear PBUF BREST BTL.
pose proof ERR as ERR0. stash ERR0. stash BPRE. stash BTL2. stash CHm. stash INV1. stash INV.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, q); (pb + 8, pb + 12); (buf + bpos, buf + bpos + 7)] m) as MU.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m (buf + bpos) (Fr + 32) 6 lo _ o);
rewrite ?unsigned_lit by lia;
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP | exact INbuf | lia | lia | lia]
| intros _; apply unpoisoned_sbuf7; [exact HFal | lia | unfold A_SB; exact SHB7 | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | lia
| exact BDST | exact SBo | rewrite OL; reflexivity
| exact ST | exact LO | lia | clear - Hq32; Z.div_mod_to_equations; lia | exact MI | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BDST2 SBo2 ST2.
clear BDST SBo ST.
transport_after_call asegs m m2 MU2 WM2; try match goal with H : mem_inv asegs m |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 655784)) with (Z_to_bv 64 655784) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. rewrite sxb_zero. step. if_lit.
step. step. step.
rewrite sx32_small by lia. rewrite unsigned_lit by lia. rewrite swrap32_id by lia.

remember (Fr / 8 + 2147450880) as sh eqn:Esh. remember (pb / 8 + 2147450880) as shp eqn:Eshp.
remember ((buf + bpos + 6) / 8 + 2147450880) as shn eqn:Eshn. remember (Z.land (buf + bpos + 6) 7) as mska eqn:Emsk.
assert (MKR : 0 <= mska < 8) by (rewrite Emsk; rewrite land7_mod8 by lia; apply Z.mod_pos_bound; lia).
stash Esh. stash Eshp. stash Eshn. stash Emsk. stash HFal. stash Hq32. stash Hpbal. stash Hbufal.
stepz. step. step. step. sh_norm.
unstash Eshn. replace ((buf + (bpos + 6)) / 8 + 2147450880) with shn by (rewrite Eshn; f_equal; f_equal; lia). clear Eshn.
step. step. fold_mkR.
assert (TAILF : forall a1x a2x : word,
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 655784) (Z_to_bv 64 q) gp (Z_to_bv 64 6434400) z0 z1 z2 sp (Z_to_bv 64 q)
(Z_to_bv 64 (buf + (bpos + 6))) a1x a2x w3 w4 w5 w6 w7 (Z_to_bv 64 47) (Z_to_bv 64 n) (Z_to_bv 64 Sa)
(Z_to_bv 64 pb) (Z_to_bv 64 0) (Z_to_bv 64 pos) (Z_to_bv 64 pos) (Z_to_bv 64 sh) (Z_to_bv 64 2147450880)
(Z_to_bv 64 ESC_MASK) z3 z4 z5 z6)
F' (Z_to_bv 64 655832) fc' None m1 (seg_rom asegs))).
{ intros a1x a2x.
replace (buf + (bpos + 6)) with (buf + bpos + 6) by lia.
stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
match goal with H : mem_inv asegs mf |- _ => rename H into MIf end.
unstash CHm. unstash BPRE. unstash BTL2. unstash ERR0. unstash Esh. subst sh.
assert (BPREf : rw_cells asegs mf buf [CB (Z.to_nat bpos) (firstn (Z.to_nat bpos) content)]).
{ eapply (rw_cells_transport asegs _ m mf); [exact BPRE | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. clear - Hbp Hcap FAST DPB Hbuf0 Hbufc LO ACR. unfold alloc_ceiling in *. lia. }
assert (BTLf : rw_cells asegs mf (buf + bpos + 6 + 1) [CB (Z.to_nat cap - Z.to_nat bpos - 6 - 1) (skipn 1 (skipn 6 (skipn (Z.to_nat bpos) content)))]).
{ eapply (rw_cells_transport asegs _ m mf); [exact BTL2 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r. clear - Hbp Hcap FAST DPB Hbuf0 Hbufc LO ACR. unfold alloc_ceiling in *. lia. }
assert (BNULc : rw_cells asegs mf (buf + bpos + 6) [CB 1 [Z_to_bv 8 0]]).
{ eapply rw_cells_recast; [exact BNUL | cbn; tauto | reflexivity | reflexivity]. }
assert (PBUFf : exists content', Z.of_nat (length content') = cap /\ rw_cells asegs mf buf [CB (Z.to_nat cap) content']).
{ pose proof (rw_cells_CB_join asegs mf buf (Z.to_nat bpos) 6 _ _ BPREf ltac:(rewrite Z2Nat.id by lia; exact BDST2)) as J1.
assert (J2 : rw_cells asegs mf buf [CB (Z.to_nat bpos + 6 + 1) ((firstn (Z.to_nat bpos) content ++ o) ++ [Z_to_bv 8 0])]).
{ apply (rw_cells_CB_join asegs mf buf (Z.to_nat bpos + 6) 1 _ _ J1). replace (buf + Z.of_nat (Z.to_nat bpos + 6)) with (buf + bpos + 6) by (clear - Hbp; lia). exact BNULc. }
assert (J3 : rw_cells asegs mf buf [CB (Z.to_nat bpos + 6 + 1 + (Z.to_nat cap - Z.to_nat bpos - 6 - 1)) (((firstn (Z.to_nat bpos) content ++ o) ++ [Z_to_bv 8 0]) ++ skipn 1 (skipn 6 (skipn (Z.to_nat bpos) content)))]).
{ apply (rw_cells_CB_join asegs mf buf (Z.to_nat bpos + 6 + 1) _ _ _ J2). replace (buf + Z.of_nat (Z.to_nat bpos + 6 + 1)) with (buf + bpos + 6 + 1) by (clear - Hbp; lia). exact BTLf. }
replace (Z.to_nat bpos + 6 + 1 + (Z.to_nat cap - Z.to_nat bpos - 6 - 1))%nat with (Z.to_nat cap) in J3 by (clear - Hbp Hcap FAST; lia).
eexists. split; [| exact J3].
destruct J3 as [[[Hwf _] _] _]. rewrite Hwf. clear - Hcap. lia. }
destruct PBUFf as (content' & Hlen' & PBUFf).
assert (FFf : rw_cells asegs mf Fr (escFF j8 (o ++ [Z_to_bv 8 0]) j17)).
{ unfold escFF. change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 90427); C8 (Z_to_bv 64 654992); CB 8 j8; CB 7 (o ++ [Z_to_bv 8 0]); CB 17 j17]
with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 90427); C8 (Z_to_bv 64 654992); CB 8 j8] ++ ([CB 7 (o ++ [Z_to_bv 8 0])] ++ [CB 17 j17])).
apply rw_cells_app. split; [exact FFa|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
apply rw_cells_app. split; [exact FFe | exact FFb]. }
evt_done5.
eapply esc_ctrl_tailA; [| exact FS | exact FR | lia | | exact IH | exact EX].
- eapply (esc_inv_pbwA 7 7 A (e + 6) m mf md _ j0 j1 gj j8 (o ++ [Z_to_bv 8 0]) j17 j8 (o ++ [Z_to_bv 8 0]) j17 buf cap errv B (bpos + 6) content');
[ exact HP | exact CHm | exact ERR0 | exact HPR | exact VM | exact Hc | exact HB | exact HD | exact MU | exact WM | exact MIf | | | | exact FFf | exact SHx | exact ST2 ].
+ constructor; [left; left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; right; cbn [fst snd]; lia | constructor].
+ split; [lia|]. split; [lia|]. split; [exact Hlen'|]. split; [exact PBS | exact PBUFf].
+ lia.
- lia. }
destruct HVM as [-> | HVM].
+ rewrite sxb_zero. if_lit. fold_mkR. apply TAILF.
+ rewrite (sxb_small vn) by lia. if_truex.
step. rewrite (unsigned_lit (buf + (bpos + 6))) by lia.
unstash Emsk. replace (Z.land (buf + (bpos + 6)) 7) with mska by (rewrite Emsk; f_equal; lia). clear Emsk.
step. if_truex. fold_mkR. apply TAILF.
Qed.

End Esc.
End RC__1.
End Mq0.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrr.
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

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 224 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - AESC_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 6 * n < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 (6 * n) <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis INs : In (sa, sk) LB.
Hypothesis Hs1 : sa <= Sa.
Hypothesis Hs2 : Sa + n <= sa + sk.
Hypothesis SRC0 : bytes_at asegs m0 Sa src.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis Hn : 0 < n < 2^31.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n q d Fr).
Notation st_escx := (st_escA sp gp Sa n q).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.
Ltac jt_eval :=
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma esc_joinA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos + 1 -> 0 <= pos < n -> 0 <= e <= 6 * start ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_JOIN x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until e. intros INV FS FR Hst Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_escA, AESC_JOIN. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step.
replace (n - pos + -1) with (n - (pos + 1)) by lia. replace (Sa + pos + 1) with (Sa + (pos + 1)) by lia.
destruct (Z.eq_dec n (pos + 1)) as [E | NE].
- if_truex. fold_mkR. rewrite <- E.
evt_done5. unfold exitKA in EX. eapply (EX _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m md A start e); [exact INV | exact FS | exact FR | lia | lia].
- if_falsex. fold_mkR.
evt_done5. unfold loopKA in IH. eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m md A (pos + 1) start e); [exact INV | exact FS | exact FR | lia | lia | lia | lia].
Qed.

Lemma esc_srcA : forall v A e m md, esc_invx v A e m md -> bytes_at asegs m Sa src.
Proof.
intros v A e m md (j0 & j1 & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & _).
eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC0 |].
eapply client_range_block; [apply in_or_app; left; exact INs | lia | rewrite SRCL; cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma esc_fetchA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z) (c : byte),
esc_invx 248 A e m md -> 0 <= pos < n -> nth_error src (Z.to_nat pos) = Some c ->
(forall a1' a2' : word,
AJ5 A4L HIx A T md (st_escx 0xa1e38 x1 t0 t1 t2 a0 a1' a2' a3 a4 a5 a6 a7 (wz (bv_unsigned c)) t3 t4 t5 t6 F' fc' m pos)) ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV Hpos Hc K.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (QSHS.payload_byteA _ _ _ _ _ SRC Hc ltac:(lia)) as RDC.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct (payload_shadow_of_blk HIx _ _ _ _ _ _ _ sa sk (Sa + pos) HP INsF ltac:(lia)) as (v & SHP & Hv). unfold A_SB in SHP.
unfold st_escA, AESC_LOOP. a4l. reenterA asegs A4L HIx asegs_wx HP.

step. if_falsex.
step. step. rewrite (v_sltiu_0 (Z_to_bv 64 (Sa + pos)) 1) by (rewrite ?(unsigned_lit (Sa + pos)) by lia; lia).
rewrite ?(unsigned_lit 1), ?(unsigned_lit 0) by lia. change (Z.lxor 1 0) with 1.
step. if_falsex.
step. if_falsex.
step. step.
sh_norm.
step. step.
destruct Hv as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_falsex.
step. step. change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). fold_mkR.
evt_done5. apply K.
- rewrite (sxb_small v) by lia. if_truex.
step. step.
rewrite (unsigned_lit (Sa + pos)) by lia. rewrite land7_mod8 by lia.
pose proof (Z.mod_pos_bound (Sa + pos) 8 ltac:(lia)) as MB.
if_truex.
step. step. change (zxb c) with (Z_to_bv 64 (bv_unsigned c)). fold_mkR.
evt_done5. apply K.
Qed.

Lemma esc_iter_regularA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
32 <= bv_unsigned c -> bv_unsigned c <> 34 -> bv_unsigned c <> 92 -> bv_unsigned c <> 47 ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc C32 C34 C92 C47 IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a1' a2'.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct (Z.lt_ge_cases 47 (bv_unsigned c)) as [HI|LOW].
- step.
if_truex. step. step. if_falsex. step. step. if_truex. fold_mkR.
evt_done5. eapply esc_joinA; [exact INV | exact FS | exact FR | lia | lia | exact He | exact IH | exact EX].
- assert (E : bv_unsigned c = 32 \/ bv_unsigned c = 33 \/ bv_unsigned c = 35 \/ bv_unsigned c = 36 \/ bv_unsigned c = 37 \/
bv_unsigned c = 38 \/ bv_unsigned c = 39 \/ bv_unsigned c = 40 \/ bv_unsigned c = 41 \/ bv_unsigned c = 42 \/
bv_unsigned c = 43 \/ bv_unsigned c = 44 \/ bv_unsigned c = 45 \/ bv_unsigned c = 46) by lia.
destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]; rewrite E.
all: step; if_falsex; step; step; step; if_truex; step; step; if_falsex; step; step; if_truex; fold_mkR.
all: evt_done5; eapply esc_joinA; [exact INV | exact FS | exact FR | lia | lia | exact He | exact IH | exact EX].
Qed.

Lemma esc_appendA :
forall (ret : Z) (x3 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(Fc : bvmap 5 word) (fcc : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (v e b k : Z) (sbs : list byte),
esc_invx v A e m md ->
bytes_at asegs m b sbs -> Z.of_nat (length sbs) = k -> 0 <= k < 2^31 -> 0 <= b ->
src_locA LB ((Fr, 0) :: FRS) b k -> (0 < k -> unpoisoned asegs m A_SB b k) ->
0 <= e -> e + k <= 6 * n ->
x3 = gp -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
fsaved F Fc -> frm0 fcc ->
(forall (A' : ASA A4L HIx) m' md' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) F' fc',
esc_invx v A' (e + k) m' md' -> fsaved F F' -> frm0 fc' -> bytes_at asegs m' b sbs ->
AJ5 A4L HIx A' T md' (MS (mkR (wz ret) (wz q) gp (wz A_TP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6') F' (wz ret) fc' None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md (MS (mkR (wz ret) (wz q) x3 (wz A_TP) t0 t1 t2 x8 x9 (wz pb) (wz b) (wz k) a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) Fc (wz AMEMAPPEND) fcc None m (seg_rom asegs)).
Proof.
intros until sbs. intros INV SB SBL Hk Hb SRCB UPS He Hek -> Hret Hret2 FS FRM K.
destruct INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := sbs) (e := e);
[ exact INV1 | exact SB | exact SBL | exact Hk | exact Hb | exact SRCB | exact UPS | exact He | exact Hek
| lia | clear - Hq32; Z.div_mod_to_equations; lia | lia | unfold_consts; lia | reflexivity | exact Hret | exact Hret2 | exact FS | exact FRM | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INV' FS' FR' SB'.
apply K; [| exact FS' | exact FR' | exact SB'].
exists j0, j1, gj, j8, sb, j17. exact INV'.
Qed.

Definition esc_jtabA : list byte := Eval vm_compute in match image_bytes asegs 0x232cc 160 with Some bs => bs | None => [] end.
Lemma esc_jtabA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x232cc [CB 160 esc_jtabA].
Proof.
intros m MI. change 160%nat with (length esc_jtabA).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length esc_jtabA)) with 160%Z. lia.
Qed.
Definition esc_litA (cv : Z) : Z :=
match cv with 8 => 0x23600 | 9 => 0x23660 | 10 => 0x23620 | 12 => 0x23680 | 13 => 0x23640 | 34 => 0x236a0 | 92 => 0x236c0 | 47 => 0x236e0 | _ => 0 end.
Definition esc_litbA (cv : Z) : list byte := [b8 92; b8 (match cv with 8 => 98 | 9 => 116 | 10 => 110 | 12 => 102 | 13 => 114 | _ => cv end)].
Lemma esc_lit_okA : forall cv, In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
ro_bytes_b asegs (esc_litA cv) (esc_litbA cv) = true /\ src_ro_chk (esc_litA cv) 2 = true.
Proof. intros cv H. cbn in H. repeat (destruct H as [<- | H]; [split; vm_compute; reflexivity|]). destruct H. Qed.

Lemma esc_special_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e cv : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= pos < n -> 0 <= e <= 6 * pos ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa1e74 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 (wz pb) (wz 47) (wz cv) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cv. intros INV FS FR Hpos He Hcv IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (esc_jtabA_ro m MI) as JT.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
destruct (esc_lit_okA cv Hcv) as [LITB LITC].
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (TAIL : forall (u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
AJ5 A4L HIx A T md (MS (mkR (wz 0xa1dec) (wz q) gp (wz A_TP) u0 u1 u2 sp (wz q) (wz pb) (wz (esc_litA cv)) (wz 2) b3 b4 b5 b6 b7
(wz 0) (wz pos) (wz Sa) (wz ESC_MASK) (wz (n - pos)) (wz 1) (wz pos) (wz (Sa + pos)) (wz 2147450880) (wz cv) u3 u4 u5 u6)
F' (wz AMEMAPPEND) fc' None m (seg_rom asegs))).
{ intros.
eapply esc_appendA with (sbs := esc_litbA cv) (e := e) (v := 248);
[ exact INV | apply QUrr.rodata_bytes_at; [exact MI | exact LITB | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv]
| reflexivity | lia | cbn in Hcv; repeat (destruct Hcv as [<- | Hcv]; [cbn; lia|]); destruct Hcv
| right; right; apply src_globA_of_chk; exact LITC
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; exact LITC | lia]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
pose proof INV' as (j0' & j1' & gj' & j8' & sb' & j17' & INV1').
pose proof INV1' as (buf' & cap' & bpos' & content' & errv' & B' & HP' & PB' & CHm' & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
apply Forall_cons_iff in CHm' as [LOC' _]. cbn [fst snd] in LOC'. unfold escLoc in LOC'.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. step. step. fold_mkR.
evt_done5. eapply esc_joinA; [exact INV' | exact FS' | exact FR' | lia | lia | lia | exact IH | exact EX]. }
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hcv' := Hcv). cbn in Hcv'.
destruct Hcv' as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; rewrite <- E in *.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 3 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. step. step. if_lit. do 6 step. fold_mkR. evt_done5. apply TAIL.
-  step. step. step. if_lit. do 5 step. jt_eval. do 4 step. do 5 step. fold_mkR. evt_done5. apply TAIL.
Qed.

Lemma esc_special_c4A :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e cv : Z),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
In cv [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa1e50 x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) (wz cv) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cv. intros INV FS FR Hst Hpos He Hcv IH EX.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
destruct (Z.lt_ge_cases start pos) as [LT | GE].
-
step. if_falsex.
step. step. if_falsex.
step. step.
rewrite (unsigned_lit pos), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 248);
[ exact INV
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP | exact INsF | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
pose proof INV' as (j0' & j1' & gj' & j8' & sb' & j17' & INV1').
pose proof INV1' as (buf' & cap' & bpos' & content' & errv' & B' & HP' & PB' & CHm' & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
apply Forall_cons_iff in CHm' as [LOC' _]. cbn [fst snd] in LOC'. unfold escLoc in LOC'.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. step. fold_mkR.
evt_done5. eapply esc_special_tailA; [exact INV' | exact FS' | exact FR' | lia | lia | exact Hcv | exact IH | exact EX].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_special_tailA; [exact INV | exact FS | exact FR | lia | lia | exact Hcv | exact IH | exact EX].
Qed.

Lemma esc_iter_specialA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
In (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc Hcv IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a1' a2'.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
assert (Hcv' := Hcv). cbn in Hcv.
destruct Hcv as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; rewrite <- E in *.
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
-  step. if_lit. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
- step. if_lit. step. step. step. if_lit. step. if_lit. fold_mkR.
evt_done5. eapply esc_special_c4A; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | cbn; tauto | exact IH | exact EX].
Qed.

Definition esc_apart (a k : Z) : Prop :=
(a + k <= lo \/ q + 8 <= a) /\ (a + k <= Fr \/ Fr + 56 <= a) /\ (a + k <= Fr / 8 + 2147450880 \/ Fr / 8 + 2147450880 + 8 <= a).
Definition esc_privW (iv : Z * Z) : Prop :=
(lo <= fst iv /\ snd iv <= q + 8) \/ (Fr <= fst iv /\ snd iv <= Fr + 56) \/ (Fr / 8 + 2147450880 <= fst iv /\ snd iv <= Fr / 8 + 2147450880 + 8).
Lemma esc_apart_disjoint : forall W a k, Forall esc_privW W -> esc_apart a k -> disjoint_from W a k.
Proof.
intros W a k HW (H1 & H2 & H3). induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold esc_privW in Hiv. cbn [fst snd] in Hiv. lia.
Qed.

Definition esc_inv_sbx (v : Z) (sbx : list byte) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists j0 j1 gj j8 j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb Sa n q d Fr j0 j1 gj j8 sbx j17 v) e m md.
Lemma esc_inv_of_sbx : forall v sbx A e m md, esc_inv_sbx v sbx A e m md -> esc_invx v A e m md.
Proof. intros v sbx A e m md (j0 & j1 & gj & j8 & j17 & H). exists j0, j1, gj, j8, sbx, j17. exact H. Qed.

Lemma esc_inv_privA : forall v v' (A : ASA A4L HIx) e m m' md W j0 j1 gj j8 sb j17 j0' j8' sb' j17',
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb Sa n q d Fr j0 j1 gj j8 sb j17 v) e m md ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall esc_privW W ->
rw_cells asegs m' q [C8 j0'] ->
rw_cells asegs m' Fr (escFF j8' sb' j17') -> rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') -> stk asegs m' lo q ->
esc_inv_sbx v' sb' A e m' md.
Proof.
intros until j17'. intros INV MU WM MI' HW LOCh' FF' SH' ST'.
destruct INV as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (_ & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> esc_apart a (Z.of_nat (cells_size cs)) -> rw_cells asegs m' a cs).
{ intros a cs H AP. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM | apply esc_apart_disjoint; [exact HW | exact AP]]. }
exists j0', j1, gj, j8', j17'. exists buf, cap, bpos, content, errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
split.
{ destruct PB as (P1 & P2 & P3 & PBS & PBUF). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
split; [apply TR; [exact PBS | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]
| apply TR; [exact PBUF | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]]. }
unfold escCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 CHm]. apply Forall_cons_iff in CHm as [C3 _].
cbn [fst snd] in C1, C2, C3.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
split.
{ unfold escLoc in C1.
lazymatch type of C1 with rw_cells _ _ _ (C8 j0 :: ?rest) =>
change (C8 j0 :: rest) with ([C8 j0] ++ rest) in C1; apply (proj1 (rw_cells_app asegs _ _ [_] _)) in C1; destruct C1 as [_ C1t];
cbn [cells_size csize Nat.add] in C1t; change (Z.of_nat 8) with 8 in C1t end.
constructor.
{ cbn [fst snd]. unfold escLoc.
lazymatch goal with |- rw_cells _ _ _ (C8 j0' :: ?rest) => change (C8 j0' :: rest) with ([C8 j0'] ++ rest) end.
apply rw_cells_app. split; [exact LOCh'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
apply TR; [exact C1t | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]. }
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold esc_apart; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C3 | unfold esc_apart, escSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [exact FSUB|].
split; [apply TR; [exact ERR | unfold esc_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [H | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia. }
split; [exact VM|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_inv_shA : forall v v' (A : ASA A4L HIx) e m m' md,
esc_invx v A e m md ->
munch [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') ->
esc_invx v' A e m' md.
Proof.
intros v v' A e m m' md (j0 & j1 & gj & j8 & sb & j17 & INV1) MU WM MI' SH'.
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _ & CHx & _ & _ & _ & STx & _).
unfold escCH in CHx. apply Forall_cons_iff in CHx as [LOCx CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx _]. cbn [fst snd] in LOCx, FFx.
unfold escLoc in LOCx.
lazymatch type of LOCx with rw_cells _ _ _ (C8 j0 :: ?rest) =>
change (C8 j0 :: rest) with ([C8 j0] ++ rest) in LOCx; apply (proj1 (rw_cells_app asegs _ _ [_] _)) in LOCx; destruct LOCx as [LOCh _] end.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
apply (esc_inv_of_sbx v' sb).
eapply (esc_inv_privA v v' A e m m' md _ j0 j1 gj j8 sb j17 j0 j8 sb j17); [exact INV1 | exact MU | exact WM | exact MI' | | | | exact SH' | ].
- constructor; [right; right; cbn [fst snd]; lia | constructor].
- eapply (rw_cells_transport asegs _ m m'); [exact LOCh | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I]. lia.
- eapply (rw_cells_transport asegs _ m m'); [exact FFx | exact MU | exact WM |]. unfold escFF. cbn [disjoint_from cells_size csize Nat.add]. split; [| exact I].
change (Z.of_nat (8 + (8 + (8 + (8 + (7 + (17 + 0))))))) with 56. lia.
- eapply (stk_transport_disjoint asegs _ m m'); [exact STx | exact MU | exact WM |]. cbn [disjoint_from]. split; [| exact I]. lia.
Qed.

Definition esc_pbW (buf cap : Z) (iv : Z * Z) : Prop :=
esc_privW iv \/ (pb <= fst iv /\ snd iv <= pb + PB_SZ) \/ (buf <= fst iv /\ snd iv <= buf + cap).
Lemma esc_inv_pbwA : forall v v' (A : ASA A4L HIx) e' m m' md W j0 j1 gj j8 sb j17 j0' j8' sb' j17' buf cap errv B bpos' content',
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B m md ->
Forall (fun ch => rw_cells asegs m (fst ch) (snd ch)) (escCH ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 pb Sa n q d Fr j0 j1 gj j8 sb j17 v) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> model_vm_only (cfg_model md0) (cfg_model md) ->
cap0 <= cap <= ser_capb cap0 bpos0 (6 * n) -> bB B0 - 64 * (cap - cap0) <= bB B -> bD B0 <= bD B ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' -> Forall (esc_pbW buf cap) W ->
pbuf_core asegs m' pb buf bpos' cap content' -> bpos0 <= bpos' <= bpos0 + e' ->
rw_cells asegs m' q [C8 j0'] ->
rw_cells asegs m' Fr (escFF j8' sb' j17') -> rw_cells asegs m' (Fr / 8 + 2147450880) (escSH v') -> stk asegs m' lo q ->
esc_invx v' A e' m' md.
Proof.
intros until content'. intros HP CHm ERR HPR VM Hc HB HD MU WM MI' HW PB' Hb' LOCh' FF' SH' ST'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as IMpb. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in IMpb.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as IMbuf. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in IMbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (TR : forall a cs, rw_cells asegs m a cs -> esc_apart a (Z.of_nat (cells_size cs)) ->
(a + Z.of_nat (cells_size cs) <= pb \/ pb + PB_SZ <= a) -> (a + Z.of_nat (cells_size cs) <= buf \/ buf + cap <= a) -> rw_cells asegs m' a cs).
{ intros a cs H (A1 & A2 & A3) A4 A5. eapply (rw_cells_transport asegs W m m'); [exact H | exact MU | exact WM |].
clear - HW A1 A2 A3 A4 A5. induction HW as [|[l h] W Hiv _ IH]; cbn [disjoint_from]; [exact I|]. split; [| exact IH].
unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in Hiv. lia. }
exists j0', j1, gj, j8', sb', j17'. exists buf, cap, bpos', content', errv, B.
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [[H | [H | H]] | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia.
- right; left. exists pb, PB_SZ. split; [exact INpbX | lia].
- right; left. exists buf, cap. split; [exact INbufX | lia]. }
split; [exact PB'|].
unfold escCH in CHm |- *.
apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHm as [C2 CHm]. apply Forall_cons_iff in CHm as [C3 _].
cbn [fst snd] in C1, C2, C3.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
split.
{ unfold escLoc in C1.
lazymatch type of C1 with rw_cells _ _ _ (C8 j0 :: ?rest) =>
change (C8 j0 :: rest) with ([C8 j0] ++ rest) in C1; apply (proj1 (rw_cells_app asegs _ _ [_] _)) in C1; destruct C1 as [_ C1t];
cbn [cells_size csize Nat.add] in C1t; change (Z.of_nat 8) with 8 in C1t end.
constructor.
{ cbn [fst snd]. unfold escLoc.
lazymatch goal with |- rw_cells _ _ _ (C8 j0' :: ?rest) => change (C8 j0' :: rest) with ([C8 j0'] ++ rest) end.
apply rw_cells_app. split; [exact LOCh'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
apply TR; [exact C1t | unfold esc_apart; cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]. }
constructor; [cbn [fst snd]; apply TR; [exact C2 | unfold esc_apart; cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; apply TR; [exact C3 | unfold esc_apart, escSaved; cbn [cells_size csize Nat.add]; lia | unfold escSaved; cbn [cells_size csize Nat.add]; lia | unfold escSaved; cbn [cells_size csize Nat.add]; lia]|].
constructor; [cbn [fst snd]; exact FF'|].
constructor; [cbn [fst snd]; exact SH' | constructor]. }
split.
{ constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [left; cbn [fst]; lia|].
constructor; [right; right; exists (Fr, fr_size 0 - 8); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact INF | unfold escFF; cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; rewrite fr_size_0; lia]|].
constructor; [right; right; exists (shad A4L Fr, fr_shadow_len 0); split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact INF | unfold shad, escSH; cbn [blk_addr blk_size fst snd cells_size csize Nat.add hl_sb A4L]; change (fr_shadow_len 0) with 8; unfold A_SB; lia]|].
constructor. }
split; [intros b Hb0; cbn [fr_ivs flat_map app]; right; right; exact Hb0|].
split; [apply TR; [exact ERR | unfold esc_apart, A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia | unfold A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia | unfold A_ERRNO, A_TP; cbn [cells_size csize Nat.add]; lia]|].
split; [exact ST'|].
split.
{ eapply heap_pres_trans; [exact HPR|].
assert (SUB1 : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (NIN : forall a k k', In (a, k') [(pb, PB_SZ); (buf, cap)] -> In (a, k) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) -> ~ In (a, k) (LB ++ LM ++ fr_ivs A4L FRS)).
{ intros a k k' Hin HinX Hi. rewrite app_assoc in Hi. apply in_app_or in Hi as [Hi | Hi].
- exact (nodup_prefix_suffix [(pb, PB_SZ); (buf, cap)] (LB ++ LM) a k' k ND Hin Hi).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP HinX _). cbn [fr_ivs flat_map app]. right; right. exact Hi. }
eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUB1 ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
eapply Forall_impl; [| exact HW]. intros [l h] Hiv. unfold esc_pbW, esc_privW in Hiv. cbn [fst snd] in *.
destruct Hiv as [[H | [H | H]] | [H | H]].
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. lia.
- right; left. exists pb, PB_SZ. split; [exact INpbX|]. split; [apply (NIN pb PB_SZ PB_SZ); [left; reflexivity | exact INpbX] | lia].
- right; left. exists buf, cap. split; [exact INbufX|]. split; [apply (NIN buf cap cap); [right; left; reflexivity | exact INbufX] | lia]. }
split; [exact VM|]. split; [exact Hb'|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_ctrl_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z),
esc_invx 7 A e m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * (pos + 1) ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa20cc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until e. intros INV FS FR Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & _ & CHx & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold escCH in CHx. apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, SHx. unfold escLoc in LOC. unfold escSH in SHx.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step. stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply esc_joinA; [eapply (esc_inv_shA 7 248 A e m m1 md INV MU WM MI1); exact SHx | exact FS | exact FR | lia | lia | lia | exact IH | exact EX].
Qed.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Lemma esc_ctrl_appA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e : Z) (o : list byte),
esc_inv_sbx 7 (o ++ [b8 0]) A e m md -> length o = 6%nat ->
fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * pos ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa1f5c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until o. intros INV OL FS FR Hpos He IH EX.
pose proof INV as (j0 & j1 & gj & j8 & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, FFx, SHx. unfold escLoc in LOC. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpb : In (pb, PB_SZ) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (left; reflexivity).
assert (INbuf : In (buf, cap) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; left; reflexivity).
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INpb).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; exact INbuf).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & Hpbal & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & Hbufal & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (NEpb : pb <> buf).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni _]; subst. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb PB_SZ buf cap HP INpbX INbufX NEpb) as DPB.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
shadow_inA A4L HIx HP INpb SHpb.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (SHPR : 2147450880 <= pb / 8 + 2147450880 /\ pb / 8 + 2147450880 + 2 <= 17594333495296) by (clear - Hpb0 Hpbc ACR; Z.div_mod_to_equations; lia).
unfold st_escA. a4l.
reenterA asegs A4L HIx asegs_wx HP.

step. step. step. if_lit.

step. asan_chkA.

step. step. step. sh_norm. rewrite (div8_add pb 8) by lia. change (8 / 8) with 1.
step. step. rewrite sxb_zero. step. if_lit.

step. rewrite !sx32_small by lia.
step. step. rewrite ?unsigned_lit by lia. rewrite swrap32_id by lia.
step. rewrite (proj2 (Fs.bv_eqb_eq _ _) eq_refl). cbn [negb]. cbv iota.
step. rewrite (unsigned_lit (cap - bpos)) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
step. step.

apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFe, FFb.
change (Z.of_nat 32) with 32 in FFe, FFb.
pose proof (rw_cells_bytes_at asegs _ _ _ FFe) as SBB. cbn [cells_bytes cbytes app] in SBB. rewrite app_nil_r in SBB.
apply bytes_at_app in SBB. destruct SBB as [SBo _].
destruct (sbuf7_shadow_word m _ SHx) as [_ SHB7].
destruct (Z.lt_ge_cases (cap - bpos) 7) as [SLOW | FAST].
-
if_truex.
step. step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := o) (e := e) (v := 7);
[ exact (esc_inv_of_sbx _ _ _ _ _ _ INV) | exact SBo | rewrite OL; reflexivity | lia | lia
| right; left; exists Fr, 0; split; [left; reflexivity | rewrite fr_size_0; lia]
| intros _; apply unpoisoned_sbuf7; [exact HFal | lia | unfold A_SB; exact SHB7 | lia]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.

pose proof INV' as (j0' & j1' & gj' & j8' & sb' & j17' & INV1').
pose proof INV1' as (buf' & cap' & bpos' & content' & errv' & B' & HP' & PB' & CHm' & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
apply Forall_cons_iff in CHm' as [LOC' _]. cbn [fst snd] in LOC'. unfold escLoc in LOC'.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. step. fold_mkR.
evt_done5.
eapply esc_ctrl_tailA; [exact INV' | exact FS' | exact FR' | lia | lia | exact IH | exact EX].
-
if_falsex.
destruct (payload_shadow_of_blk HIx _ _ _ _ _ _ _ buf cap (buf + bpos + 6) HP INbuf ltac:(lia)) as (vn & SHN & Hvn). unfold A_SB in SHN.
assert (SHNR : 2147450880 <= (buf + bpos + 6) / 8 + 2147450880 /\ (buf + bpos + 6) / 8 + 2147450880 + 1 <= 17594333495296) by (clear - Hbuf0 Hbufc Hbp Hcap ACR; Z.div_mod_to_equations; lia).
assert (HVN : 0 <= vn < 8) by (destruct Hvn as [-> | [? _]]; lia).
assert (HVM : vn = 0 \/ Z.land (buf + bpos + 6) 7 < vn) by (destruct Hvn as [-> | [? Hm]]; [left; reflexivity | right; rewrite land7_mod8 by lia; exact Hm]).
clear Hvn.

asan_chkA.

destruct (rw_cells_CB_cut asegs m buf (Z.to_nat cap) content (Z.to_nat bpos) PBUF ltac:(lia)) as [BPRE BREST].
destruct (rw_cells_CB_cut asegs m _ _ _ 6%nat BREST ltac:(lia)) as [BDST BTL].
destruct (rw_cells_CB_cut asegs m _ _ _ 1%nat BTL ltac:(lia)) as [BNUL BTL2].
rewrite Z2Nat.id in BDST, BNUL, BTL2 by lia. change (Z.of_nat 6) with 6 in BNUL, BTL2. change (Z.of_nat 1) with 1 in BTL2.
clear PBUF BREST BTL.
pose proof ERR as ERR0. stash ERR0. stash BPRE. stash BTL2. stash CHm. stash INV1. stash INV.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, q + 8); (pb + 8, pb + 12); (buf + bpos, buf + bpos + 7)] m) as MU.

remember (Fr / 8 + 2147450880) as sh eqn:Esh. remember (pb / 8 + 2147450880) as shp eqn:Eshp.
stash Esh. stash Eshp. stash HFal. stash Hq32. stash Hpbal. stash Hbufal.
stepz.
unstash Eshp.

step. step.
step. step. ub_nzpair buf (buf + bpos). step. if_lit.
step. step. step. step. ub_nowrap (buf + bpos) buf bpos. step. if_lit.

step. step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
match goal with H : stk asegs m1 lo q |- _ => rename H into ST1 end.
heap_nowA_auto A4L HIx HP HP1.
destruct (sbuf7_shadow_word m1 _ SHx) as [_ SHB7].
unstash HFal. unstash Hq32. unstash Esh.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m1 (buf + bpos) (Fr + 32) 6 lo _ o);
rewrite ?unsigned_lit by lia;
[ intros _; eapply (unpoisoned_of_blk HIx); [exact HP1 | exact INbuf | lia | lia | lia]
| intros _; apply unpoisoned_sbuf7; [exact HFal | lia | unfold A_SB; rewrite <- Esh; exact SHB7 | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP1)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | lia
| exact BDST | exact SBo | rewrite OL; reflexivity
| exact ST1 | exact LO | lia | clear - Hq32; Z.div_mod_to_equations; lia | exact MI1 | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BDST2 SBo2 ST2.
clear BDST SBo ST1.
transport_after_call asegs m1 m2 MU2 WM2; try match goal with H : mem_inv asegs m1 |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 663544)) with (Z_to_bv 64 663544) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (pb / 8 + 2147450881) with (shp + 1) by lia.

step. rewrite sxb_zero. step. if_lit.
step. step. step.
rewrite sx32_small by lia. rewrite unsigned_lit by lia. rewrite swrap32_id by lia.
step. if_falsex.
step. rewrite sxb_zero. step. step. step. if_lit.
stash Esh.
stepz.
step. step. rewrite ?zxb_zero. step. if_lit.
step. step.
replace (buf + (bpos + 6)) with (buf + bpos + 6) by lia.
step. step. ub_nzpair buf (buf + bpos + 6). step. if_lit.
step. step. step. step. ub_nowrap (buf + bpos + 6) buf (bpos + 6). step. if_lit.
step. if_falsex.
remember ((buf + bpos + 6) / 8 + 2147450880) as shn eqn:Eshn. remember (Z.land (buf + bpos + 6) 7) as mska eqn:Emsk.
assert (MKR : 0 <= mska < 8) by (rewrite Emsk; rewrite land7_mod8 by lia; apply Z.mod_pos_bound; lia).
stash Eshn. stash Emsk.
step. step. sh_norm.
unstash Eshn. replace ((buf + bpos + 6) / 8 + 2147450880) with shn by (rewrite Eshn; reflexivity).
step. step. fold_mkR.
assert (TAILF : forall a1x a2x : word,
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 663544) (Z_to_bv 64 q) gp (Z_to_bv 64 6444320) z0 z1 z2 sp (Z_to_bv 64 q)
(Z_to_bv 64 (buf + bpos + 6)) a1x a2x (Z_to_bv 64 0) (Z_to_bv 64 0) w5 (Z_to_bv 64 pb) (Z_to_bv 64 47)
(Z_to_bv 64 0) (Z_to_bv 64 pos) (Z_to_bv 64 Sa) (Z_to_bv 64 ESC_MASK) (Z_to_bv 64 (n - pos)) (Z_to_bv 64 1) (Z_to_bv 64 pos)
(Z_to_bv 64 (Sa + pos)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (shp + 1)) z3 z4 z5 z6)
F' (Z_to_bv 64 663660) fc' None m3 (seg_rom asegs))).
{ intros a1x a2x.
stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
match goal with H : mem_inv asegs mf |- _ => rename H into MIf end.
unstash CHm. unstash BPRE. unstash BTL2. unstash ERR0. unstash Esh. subst sh.
assert (BPREf : rw_cells asegs mf buf [CB (Z.to_nat bpos) (firstn (Z.to_nat bpos) content)]).
{ eapply (rw_cells_transport asegs _ m mf); [exact BPRE | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. clear - Hbp Hcap FAST DPB Hbuf0 Hbufc LO ACR LOS Hq Hd. unfold alloc_ceiling in *. lia. }
assert (BTLf : rw_cells asegs mf (buf + bpos + 6 + 1) [CB (Z.to_nat cap - Z.to_nat bpos - 6 - 1) (skipn 1 (skipn 6 (skipn (Z.to_nat bpos) content)))]).
{ eapply (rw_cells_transport asegs _ m mf); [exact BTL2 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r. clear - Hbp Hcap FAST DPB Hbuf0 Hbufc LO ACR LOS Hq Hd. unfold alloc_ceiling in *. lia. }
assert (BNULc : rw_cells asegs mf (buf + bpos + 6) [CB 1 [Z_to_bv 8 0]]).
{ eapply rw_cells_recast; [exact BNUL | cbn; tauto | reflexivity | reflexivity]. }
assert (PBUFf : exists content', Z.of_nat (length content') = cap /\ rw_cells asegs mf buf [CB (Z.to_nat cap) content']).
{ pose proof (rw_cells_CB_join asegs mf buf (Z.to_nat bpos) 6 _ _ BPREf ltac:(rewrite Z2Nat.id by lia; exact BDST2)) as J1.
assert (J2 : rw_cells asegs mf buf [CB (Z.to_nat bpos + 6 + 1) ((firstn (Z.to_nat bpos) content ++ o) ++ [Z_to_bv 8 0])]).
{ apply (rw_cells_CB_join asegs mf buf (Z.to_nat bpos + 6) 1 _ _ J1). replace (buf + Z.of_nat (Z.to_nat bpos + 6)) with (buf + bpos + 6) by (clear - Hbp; lia). exact BNULc. }
assert (J3 : rw_cells asegs mf buf [CB (Z.to_nat bpos + 6 + 1 + (Z.to_nat cap - Z.to_nat bpos - 6 - 1)) (((firstn (Z.to_nat bpos) content ++ o) ++ [Z_to_bv 8 0]) ++ skipn 1 (skipn 6 (skipn (Z.to_nat bpos) content)))]).
{ apply (rw_cells_CB_join asegs mf buf (Z.to_nat bpos + 6 + 1) _ _ _ J2). replace (buf + Z.of_nat (Z.to_nat bpos + 6 + 1)) with (buf + bpos + 6 + 1) by (clear - Hbp; lia). exact BTLf. }
replace (Z.to_nat bpos + 6 + 1 + (Z.to_nat cap - Z.to_nat bpos - 6 - 1))%nat with (Z.to_nat cap) in J3 by (clear - Hbp Hcap FAST; lia).
eexists. split; [| exact J3].
destruct J3 as [[[Hwf _] _] _]. rewrite Hwf. clear - Hcap. lia. }
destruct PBUFf as (content' & Hlen' & PBUFf).
assert (FFf : rw_cells asegs mf Fr (escFF j8 (o ++ [Z_to_bv 8 0]) j17)).
{ unfold escFF.
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] => change [c1; c2; c3; c4; c5; c6] with ([c1; c2; c3; c4] ++ ([c5] ++ [c6])) end.
apply rw_cells_app. split; [exact FFa|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
apply rw_cells_app. split; [exact FFe | exact FFb]. }
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in LOC. destruct LOC as [LOCh _].
evt_done5.
eapply esc_ctrl_tailA; [| exact FS | exact FR | lia | | exact IH | exact EX].
- eapply (esc_inv_pbwA 7 7 A (e + 6) m mf md _ j0 j1 gj j8 (o ++ [Z_to_bv 8 0]) j17 (Z_to_bv 64 shp) j8 (o ++ [Z_to_bv 8 0]) j17 buf cap errv B (bpos + 6) content');
[ exact HP | exact CHm | exact ERR0 | exact HPR | exact VM | exact Hc | exact HB | exact HD | exact MU | exact WM | exact MIf | | | | exact LOCh | exact FFf | exact SHx | exact ST2 ].
+ constructor; [left; left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia|]. constructor; [right; right; cbn [fst snd]; lia | constructor].
+ split; [lia|]. split; [lia|]. split; [exact Hlen'|]. split; [exact PBS | exact PBUFf].
+ lia.
- lia. }
destruct HVM as [-> | HVM].
+ rewrite sxb_zero. if_lit. fold_mkR. apply TAILF.
+ rewrite (sxb_small vn) by lia. if_truex.
step. rewrite (unsigned_lit (buf + bpos + 6)) by lia.
unstash Emsk. replace (Z.land (buf + bpos + 6) 7) with mska by (rewrite Emsk; reflexivity). clear Emsk.
step. if_truex. fold_mkR. apply TAILF.
Qed.

End Esc.
End RC__1.
