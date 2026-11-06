(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QjDH Qsw7 QJjn QRUw Q7UD Qhd4 Qwm6 QlKV QsKa Q9O6 Q228 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QRUw.Mq0.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq2 QsKa Q9O6.Mq2 Q228.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AEsc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition esc_specA_al (d : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(pb buf bpos cap Sa n fl lo sa sk : Z) (src content : list byte) (errv : word),
bv_unsigned sp mod 32 = d ->
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
32 <= cap < 2^30 -> bpos + 6 * n < 2^28 -> ser_need cap bpos (6 * n) <= bB B ->
aflags_ok fl ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AESC_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz pb -> a1 = wz Sa -> a2 = wz n -> a3 = wz fl ->
(forall ms' md' A', ser_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AESCAPE) fc None m (seg_rom asegs)).

Lemma esc_specA_of_al : esc_specA_al 0 -> esc_specA_al 16 -> esc_specA HIx.
Proof.
intros H0 H16. unfold esc_specA. intros until errv. intros HP PB INs Hs1 Hs2 SRC SRCL Hn CAP TXT NEED FL FRSN ST LO LOS SPA.
assert (D32 : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct D32 as [D32 | D32]; [eapply H0 | eapply H16]; eassumption.
Qed.
End AEsc.
End RC__1.
End Mq0.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu Q4v2 QgHv Q1Y6 QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Q228.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition AESC_LOOP : Z := 0xa0050.
Definition AESC_JOIN : Z := 0xa0044.
Definition AESC_EXIT : Z := 0xa02a8.
Definition ESC_MASK : Z := 140754668238592.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).

Definition escLoc (j0 j1 : list byte) : list cell :=
[CB 8 j0; C8 (wz 7); C8 (wz Fr); C8 (wz Fr); C8 (wz (pb / 8 + 1 + 2147450880)); C8 (wz 0x236a0); C8 (wz 0xea520);
C8 (wz (pb + 12)); C8 (wz (pb + 8)); C8 (wz (pb / 8 + 1 + 2147450880)); C8 (wz (Fr + 32)); C8 (wz pb); CB 16 j1; C8 (wz Fr)].
Definition escSaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition escFF (j8 sb j17 : list byte) : list cell := [C8 (wz 1102416563); C8 (wz 0x1613b); C8 (wz 0x9fe90); CB 8 j8; CB 7 sb; CB 17 j17].
Definition escSH (v : Z) : list cell := [C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 v); C1 (b8 243); C1 (b8 243); C1 (b8 243)].

Definition escCH (j0 j1 gj j8 sb j17 : list byte) (v : Z) : list (Z * list cell) :=
[(q, escLoc j0 j1); (q + 120, [CB (Z.to_nat d) gj]); (bv_unsigned sp + -104, escSaved); (Fr, escFF j8 sb j17); (Fr / 8 + 2147450880, escSH v)].

Definition esc_inv (v : Z) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists j0 j1 gj j8 sb j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH j0 j1 gj j8 sb j17 v) e m md.

Definition st_escA (pc : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (pos : Z) : machine_state :=
MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7
(wz 47) (wz n) (wz Sa) x21 (wz 0) (wz pos) (wz pos) (wz (Fr / 8 + 2147450880)) (wz 2147450880) (wz ESC_MASK) t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopKA (k : Z) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z),
esc_inv 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> n - pos = k -> 0 <= e <= 6 * start ->
AJ5 A4L HIx A T md (st_escA AESC_LOOP x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).

Definition exitKA : Prop :=
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (start e : Z),
esc_inv 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= n -> 0 <= e <= 6 * start ->
AJ5 A4L HIx A T md (st_escA AESC_EXIT x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m n).
End Esc.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1 Qfw3_c1 Q4xz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Q228.Mq0 Qwm6.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma u64_of_negA : forall z, -2^64 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2^64.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
symmetry. apply (Z.mod_unique_pos z (2^64) (-1)); lia.
Qed.

Lemma abs_idiom_nonnegA : forall len, 0 <= len < 2^63 ->
Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 len))
(bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) 63))))) -
bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) 63)))
= Z_to_bv 64 len.
Proof.
intros len H. rewrite (signed_lit len) by lia.
rewrite (Z.shiftr_div_pow2 len 63) by lia. rewrite (Z.div_small len (2^63)) by lia.
rewrite (unsigned_lit 0) by lia. rewrite (unsigned_lit len) by lia. rewrite Z.lxor_0_r. rewrite unsigned_lit by lia. f_equal. lia.
Qed.
Lemma abs_idiom_negA : forall len, -2^63 <= len < 0 ->
Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 len))
(bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) 63))))) -
bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 len)) 63)))
= Z_to_bv 64 (- len).
Proof.
intros len H. rewrite (signed_lit len) by lia.
rewrite (Z.shiftr_div_pow2 len 63) by lia.
replace (len / 2 ^ 63) with (-1) by (apply (Z.div_unique len (2^63) (-1) (len + 2^63)); [left; lia | lia]).
change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
rewrite (u64_of_negA len) by lia. rewrite lxor_ones64 by lia.
rewrite unsigned_lit by lia. apply bv_eq. rewrite u64_of_negA by lia. rewrite unsigned_lit by lia. lia.
Qed.

Definition ser_quoteA : list byte := Eval vm_compute in match image_bytes asegs 0x234c0 1 with Some bs => bs | None => [] end.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Lemma blk_granS : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma ser_str_inlineA : ser_specA HIx ASER_STR (Sstr false).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & str & junk & EREST & Hlen0 & SRCL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX.
assert (Z57 : 57 <= str_objsize len) by (unfold str_objsize; lia).
replace (57 <=? str_objsize len) with true in JTX by (symmetry; apply Z.leb_le; exact Z57). injection JTX as <- _.
unfold ASER_STR, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INpL : In (p, str_objsize len) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, str_objsize len) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p (str_objsize len) HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (blk_granS _ _ _ _ _ _ _ p (str_objsize len) 5 HP INp ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof NODE as NODE0. stash NODE0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 step. do 3 step. do 2 step.
asan_chkA.
do 3 step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32. step. if_lit.
do 5 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) A FRS (bv_unsigned sp + -64) [(bv_unsigned sp + -64, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw : 6 * len + 2 <= str_w (str_objsize len)) by (unfold str_w, str_objsize; lia).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
unstash NODE0.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
assert (NODE2 : rw_cells asegs m2 p [C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string A4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INpL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold str_objsize in *. lia. }
assert (INp2 : In (p, str_objsize len) ((pb, PB_SZ) :: (buf2, cap2) :: LB)) by (right; right; exact INpL).
pose proof (blk_granS _ _ _ _ _ _ _ p (str_objsize len) 5 HP2 INp2 ltac:(lia) ltac:(lia)) as SH52.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH52 by lia.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf2 cap2 HP2 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal2 & Hblo2 & Hbhi2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite zxb_zero. step. if_lit.
step. step. step.
if_truex.
step. step. step. rewrite abs_idiom_nonnegA by lia.
step. step. step. fold_mkR.

assert (SRC2 : bytes_at asegs m2 (p + 48) str).
{ apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _] _)) in NODE2. destruct NODE2 as [_ NB]. cbn [cells_size csize Nat.add] in NB. change (Z.of_nat 48) with 48 in NB.
pose proof (rw_cells_bytes_at asegs _ _ _ NB) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. apply bytes_at_app in X. exact (proj1 X). }
evt_done5.
eapply (ser_escapeA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED JHX ESC) with (F := F) (src := str) (e := 0 + 1) (sa := p) (sk := str_objsize len);
[ exact INV2 | exact INpL | lia | unfold str_objsize; lia | exact SRC2 | exact SRCL | lia | lia | lia
| split; [exact Rfl | exact FL58] | exact FRSN | unfold AESC_STACK; lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros A3 m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0 + 1 + 6 * len);
[ exact INV3 | apply rodata_bytes_at; [exact MI3 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP3 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' F4 fc4 INV4 FS4 FR4 _.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & PB4 & CH4 & _ & _ & ERR4 & ST4 & HPR4 & VM4 & Hb4 & Hc4 & HB4 & HD4).
apply Forall_inv in CH4. cbn [fst snd] in CH4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. do 8 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m4, _, errv4, buf4, cap4, bpos4, content4, B4.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FR4]|].
split; [exact VM4|].
split; [release_frame CH4 ST4 (bv_unsigned sp); exact ST4|].
split; [exact HPR4|]. split; [exact ERR4|]. split; [exact HP4|]. split; [exact PB4|].
split; [lia|]. split; [exact Hc4|]. split; lia.
Qed.

Lemma ser_str_heapA : ser_specA HIx ASER_STR (Sstr true).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & pd & pdn & str & junk2 & EREST & Hlen0 & SRCL & Hpdn & NODE & PD). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX.
rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_STR, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INpL : In (p, 56) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
assert (INdL : In (pd, pdn) LB) by (apply INCL; right; left; reflexivity).
assert (INd : In (pd, pdn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INdL).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 56 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; exact INd)) as (_ & Hdal & Hdlo & Hdhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
shadow_inA A4L HIx HP INp SHp.
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof NODE as NODE0. stash NODE0. pose proof PD as PD0. stash PD0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 64%nat ST.
do 9 step. do 3 step. do 2 step.
asan_chkA.
do 3 step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32. step. if_lit.
do 5 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) A FRS (bv_unsigned sp + -64) [(bv_unsigned sp + -64, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw : 6 * len + 2 <= str_w (str_objsize len)) by (unfold str_w, str_objsize; lia).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
unstash NODE0. unstash PD0.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
assert (NODE2 : rw_cells asegs m2 p [C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string A4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INpL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
assert (PD2 : rw_cells asegs m2 pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact PD0 |]. eapply client_range_block; [apply in_or_app; left; exact INdL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
assert (INp2 : In (p, 56) ((pb, PB_SZ) :: (buf2, cap2) :: LB)) by (right; right; exact INpL).
shadow_inA A4L HIx HP2 INp2 SHp2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf2 cap2 HP2 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal2 & Hblo2 & Hbhi2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite zxb_zero. step. if_lit.
step. step. step.
if_falsex.
asan_chkA. step.
step. step. step. rewrite abs_idiom_negA by lia.
step. step. step. fold_mkR.

assert (SRC2 : bytes_at asegs m2 pd str).
{ pose proof (rw_cells_bytes_at asegs _ _ _ PD2) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. apply bytes_at_app in X. exact (proj1 X). }
evt_done5.
eapply (ser_escapeA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED JHX ESC) with (F := F) (src := str) (e := 0 + 1) (sa := pd) (sk := pdn);
[ exact INV2 | exact INdL | lia | lia | exact SRC2 | exact SRCL | lia | lia | lia
| split; [exact Rfl | exact FL58] | exact FRSN | unfold AESC_STACK; lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros A3 m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0 + 1 + 6 * (- len));
[ exact INV3 | apply rodata_bytes_at; [exact MI3 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP3 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -64) with (bv_unsigned sp - 16 * 4) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' F4 fc4 INV4 FS4 FR4 _.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & PB4 & CH4 & _ & _ & ERR4 & ST4 & HPR4 & VM4 & Hb4 & Hc4 & HB4 & HD4).
apply Forall_inv in CH4. cbn [fst snd] in CH4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. do 8 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m4, _, errv4, buf4, cap4, bpos4, content4, B4.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FR4]|].
split; [exact VM4|].
split; [release_frame CH4 ST4 (bv_unsigned sp); exact ST4|].
split; [exact HPR4|]. split; [exact ERR4|]. split; [exact HP4|]. split; [exact PB4|].
split; [lia|]. split; [exact Hc4|]. split; lia.
Qed.
End Ser.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg Lib.SepCache QugP QW22 QJZd QnPO QpNt QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 QugP.Mq1 QW22.Mq2 QlKV.Mq2 QsKa Q9O6 QsKa.Mq4 QJZd.Mq0 Q9O6.Mq2 QL3k.Mq1 Q228.Mq4 Qwm6.Mq1 QnPO.Mq0 QpNt.Mq1.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AGET_STRING_STACK (s : jshape) : Z := 48 + ser_budgetA s.
Definition gsB (w : Z) : Z := pbnew32_costB + 64 * (2 * w + 9).

Section Top.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition get_string_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (s : jshape) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
gsB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).

Lemma get_string_strA : forall (h : bool),
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK (Sstr h)) errv ->
jval asegs A4F (Sstr h) m BS p rc ->
jtx (Sstr h) BS = Some (w, []) ->
0 <= bB B -> 0 <= bD B -> 0 <= w ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F (Sstr h) m' BS' p rc ->
jtx (Sstr h) BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).
Proof.
intros h. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) JV JTX BB0 BD0 Hw0 FRM A0 K.
subst a0 tp.
pose proof JV as JV0. stash JV0.
pose proof (jval_fresh_node asegs A4F _ _ _ _ _ _ JV JTX) as JN.
destruct (jnode_hdrT asegs A4F _ _ _ _ _ _ JN) as (n & udel & ud & cs & rest & ER & Hn & _).
assert (INp : In (p, n) (BS ++ LB)) by (apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 0 HP INp ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 5 HP INp ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
unfold AGET_STRING, AGET_STRING_STACK, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth] in LOS.
word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.

assert (FIN : forall (m1 : word -> option byte) (ms1 : machine_state) (r : word),
munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp) -> rw_cells asegs m1 (6434400 - 164) [C4 errv] ->
ret_statew A4H ra sp gp (Z_to_bv 64 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m1 ms1 ->
AJ5 A4L HIx A T md ms1).
{ intros m1 ms1 r MU1 WM1 MI1 ST1 ERR1 RS1.
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by (heap_nowA A4L HIx HP MU1 WM1 MI1).
eapply (K ms1 md m1 A B r errv BS []); [exact RS1 | apply model_vm_only_refl | exact ST1 | | exact ERR1 | | exact HP1 | | exact JTX | cbn; lia].
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP].
- unfold jo_chargeA, gsB, pbnew32_costB. lia.
- unstash JV0. eapply (jval_agree asegs A4F); [exact JV0 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU1 | exact WM1 |]. intros a0 n0 Hin.
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ _ a0 n0 HP); [apply in_or_app; left; apply in_or_app; left; exact Hin |].
constructor; [cbn [fst]; lia | constructor]. }
destruct h.
-
destruct JN as (len & pd & pdn & str & junk2 & EREST & Hlen0 & SRCL & Hpdn & NODE & PD). unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (En : n = 56) by (rewrite EREST in ER; injection ER as <- _; reflexivity). subst n.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p 56 6 HP INp ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
clear PD.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 step. step. if_falsex.
step. step. step.
asan_chk0.
step. step. step. if_lit.
step. asan_chkA.
step. step. step. if_falsex.
step. step. sh_norm.
replace ((p + 48) / 8 + 2147450880) with (p / 8 + 2147450886) by (clear - Hpal; Z.div_mod_to_equations; lia).
step. step. if_lit.
step. step.
do 5 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (FIN m1); [exact MU | exact WM | exact MI1 | release_frame FR ST (bv_unsigned sp); exact ST | exact ERR |].
apply ret_statew_intro; [apply fsaved_refl | intros X; exact X].
-
destruct JN as (len & str & junk & EREST & Hlen0 & SRCL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (En : n = str_objsize len) by (rewrite EREST in ER; injection ER as <- _; reflexivity). subst n.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _] _)) in NODE. destruct NODE as [NODE _].
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 step. step. if_falsex.
step. step. step.
asan_chk0.
step. step. step. if_lit.
step. asan_chkA.
step. step. step. if_truex.
do 5 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (FIN m1); [exact MU | exact WM | exact MI1 | release_frame FR ST (bv_unsigned sp); exact ST | exact ERR |].
apply ret_statew_intro; [apply fsaved_refl | intros X; exact X].
Qed.

Lemma rest_tl_sepA : forall A PRE L1 LMx FRx Bx m md p n rest a k,
HEAPAx A (PRE ++ ((p, n) :: rest) ++ L1) LMx FRx Bx m md -> 24 <= n -> In (a, k) rest -> a + k <= p + 16 \/ p + 24 <= a.
Proof.
intros A PRE L1 LMx FRx Bx m md p n rest a k HP Hn Hin.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (INa : In (a, k) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; right; exact Hin).
assert (INp : In (p, n) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (NE : p <> a).
{ intros ->. rewrite <- !app_assoc in ND. cbn [app] in ND. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND.
apply in_or_app. right. exact (in_map blk_addr _ (a, k) ltac:(apply in_or_app; left; exact Hin)). }
destruct (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p n a k HP INp INa NE) as [D|D]; lia.
Qed.

Lemma node_write_outside : forall A PRE rest L1 LMx FRx Bx m md p n lo1 hi1,
HEAPAx A (PRE ++ ((p, n) :: rest) ++ L1) LMx FRx Bx m md -> p <= lo1 -> hi1 <= p + n ->
Forall (fun iv : Z * Z => (alloc_ceiling <= fst iv /\ snd iv <= alloc_ceiling)
\/ (exists a k, In (a, k) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx) /\ ~ In (a, k) (L1 ++ LMx ++ fr_ivs A4L FRx) /\ a <= fst iv /\ snd iv <= a + k)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)) [(lo1, hi1)].
Proof.
intros A PRE rest L1 LMx FRx Bx m md p n lo1 hi1 HP Hlo Hhi.
apply Forall_cons; [| apply Forall_nil]. right; left. exists p, n. cbn [fst snd].
assert (INp : In (p, n) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
split; [exact INp|]. split; [| lia].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
rewrite <- !app_assoc in ND. cbn [app] in ND. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND.
intro H. apply in_app_or in H. destruct H as [H|H].
- apply ND. apply in_or_app. right. exact (in_map blk_addr _ (p, n) ltac:(apply in_or_app; right; apply in_or_app; left; exact H)).
- apply in_app_or in H. destruct H as [H|H].
+ apply ND. apply in_or_app. right. exact (in_map blk_addr _ (p, n) ltac:(apply in_or_app; right; apply in_or_app; right; exact H)).
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INp H).
Qed.

Hypothesis SERVAL : SERVALA HIx.

Lemma get_string_nsA : forall (s : jshape), jty s <> JT_STRING ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
gsB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).
Proof.
intros s NSTR. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) JV Hsd JHX JTX Hw27 FRSN BB BD FRM A0 K.
subst a0 tp.
pose proof (jtx_nonneg _ _ _ _ JTX) as Hw0.
pose proof (jval_fresh_node asegs A4F _ _ _ _ _ _ JV JTX) as JN.
destruct (jnode_hdrT asegs A4F _ _ _ _ _ _ JN) as (n & udel & ud & cs & rest & ER & Hn & NODE).
assert (INp : In (p, n) (BS ++ LB)) by (apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 0 HP INp ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP INp ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in NODE. destruct NODE as [NODE _].
pose proof (jty_range s) as JTR.
pose proof (sdepth_nonneg s) as SD0.
pose proof JN as JN0. stash JN0. pose proof JHX as JHX0. stash JHX0. pose proof HP as HP00. stash HP00.
unfold AGET_STRING, AGET_STRING_STACK, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. unfold JT_STRING in NSTR.
word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 step. step. if_falsex.
step. step. step.
asan_chk0.
step. step. step. norm_sx32. if_truex.
step. asan_chkA.
step. step. if_lit.
step. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.

evt_done5.
eapply (printbuf_new32_A_cps HIx) with (u := UWptr) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI1 | apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (clear - SPA; Z.div_mod_to_equations; lia).
all: try eassumption.
1: (unfold gsB, pbnew32_costB in BB |- *; lia).
intros ms4 md4 A4 (m4 & pbr & e4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
cbn [uw_cost] in BD4.
replace (ret_pc (Z_to_bv 64 648988)) with (Z_to_bv 64 648988) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HPR04 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m4).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |]. unstash HP00.
eapply (client_outsideA A4L HIx); [exact HP00 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP00].
- eapply heap_pres_weaken; [exact HPR4 | lia |]. intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb]. }

assert (JN4 : jnode asegs A4F s m4 BS p rc 0).
{ unstash JN0. unstash HP00.
eapply (jnode_agree asegs A4F) with (BS := BS); [ | | apply incl_refl].
- eapply (jnode_agree asegs A4F) with (BS := BS); [exact JN0 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a0 n0 Hin.
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ _ a0 n0 HP00); [apply in_or_app; left; apply in_or_app; left; exact Hin |].
constructor; [cbn [fst]; lia | constructor].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity |]. intros b Hb. apply in_or_app. left. apply in_or_app. left. exact Hb. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in NODE; [| eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]]. a4l.
clear MU WM MI1 ST GOT CELL SH0 SH2 HP.
destruct OUT4 as [(-> & HP4) | (Hpbr & buf & content & PB4 & HP4)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP4 ltac:(apply in_or_app; left; exact INp)) as Himg.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP4 INp ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [(p + 16, p + 24)] m4) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. step. if_lit.
step. stepz. step. step. if_lit.
step. do 5 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
assert (HP4' : HEAPAx A4 ((p, n) :: rest ++ LB) LM FRS B4 m4 md4) by (rewrite ER in HP4; exact HP4).
assert (HP5 : HEAPAx A4 (BS ++ LB) LM FRS B4 m5 md4).
{ rewrite ER. cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP4' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP4' MU); solve_frameW_withA HP4' | exact WM | exact MI5]. }
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m4 m5).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP4' | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia |].
eapply Forall_impl; [| exact (node_write_outside A4 [] rest LB LM FRS B4 m4 md4 p n (p + 16) (p + 24) HP4' ltac:(lia) ltac:(lia))].
intros iv [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]. }
assert (JN5 : jnode asegs A4F s m5 BS p rc 0).
{ eapply (jnode_set_pb asegs A4F); [exact JN4 | exact MU | exact WM | | ].
- apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in NODE. destruct NODE as [_ N2]. cbn [cells_size csize Nat.add] in N2. change (Z.of_nat 16) with 16 in N2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in N2. exact (proj1 N2).
- intros a0 k0 Hin. rewrite ER in Hin. cbn [tl] in Hin.
eapply (rest_tl_sepA A4 [] LB LM FRS B4 m4 md4 p n rest a0 k0); [cbn [app]; exact HP4' | lia | exact Hin]. }
evt_done5.
eapply (K _ md4 m5 A4 B4 _ e4 BS []);
[ apply ret_statew_intro; [exact FS4 | exact FRM4] | exact VM4 | release_frame FR ST4 (bv_unsigned sp); exact ST4
| eapply heap_pres_trans; [exact HPR04 | exact HPR45] | exact ERR4
| unfold jo_chargeA, gsB in *; lia | exact HP5
| apply (proj2 (jval_split asegs A4F _ _ _ _ _)); exists 0, [], BS; split; [rewrite app_nil_r; reflexivity |]; split; [left; split; reflexivity | exact JN5]
| exact JTX | cbn; lia ].
-
rewrite ER in HP4. cbn [app] in HP4.
assert (INp4 : In (p, n) ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB)) by (right; right; left; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP4 ltac:(apply in_or_app; left; exact INp4)) as Himg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pbr 16 HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf 32 HP4 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hfal & Hflo & Hfhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pbr 16 HP4 ltac:(apply in_or_app; left; left; reflexivity)) as Himgb.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf 32 HP4 ltac:(apply in_or_app; left; right; left; reflexivity)) as Himgf.
assert (NEpb : pbr <> p) by (intros ->; eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ p 16 n HP4); apply in_or_app; left; right; left; reflexivity).
assert (NEfb : buf <> p).
{ intros ->. pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP4 (perm_swap (p, 32) (pbr, 16) _) (Permutation_refl LM) (Permutation_refl FRS)) as HPs.
eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ p 32 n HPs). apply in_or_app. left. right. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 p n HP4 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; exact INp4) NEpb) as DJb.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf 32 p n HP4 ltac:(apply in_or_app; left; right; left; reflexivity) ltac:(apply in_or_app; left; exact INp4) NEfb) as DJf.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP4 INp4 ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
pose proof PB4 as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [(p + 16, p + 24)] m4) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. step. if_lit.
step. step. step. step. if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
match goal with H : mem_inv asegs mc |- _ => rename H into MIc end.

assert (HPc : HEAPAx A4 ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) LM FRS B4 mc md4) by (heap_nowA A4L HIx HP4 MU WM MIc).
assert (JNc : jnode asegs A4F s mc BS p rc pbr).
{ eapply (jnode_set_pb asegs A4F); [exact JN4 | exact MU | exact WM | | ].
- apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in NODE. destruct NODE as [_ N2]. cbn [cells_size csize Nat.add] in N2. change (Z.of_nat 16) with 16 in N2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in N2. exact (proj1 N2).
- intros a0 k0 Hin. rewrite ER in Hin. cbn [tl] in Hin.
eapply (rest_tl_sepA A4 [(pbr, 16); (buf, 32)] LB LM FRS B4 m4 md4 p n rest a0 k0); [cbn [app]; exact HP4 | lia | exact Hin]. }
assert (HPR4c : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m4 mc).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP4 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia |].
eapply Forall_impl; [| exact (node_write_outside A4 [(pbr, 16); (buf, 32)] rest LB LM FRS B4 m4 md4 p n (p + 16) (p + 24) HP4 ltac:(lia) ltac:(lia))].
intros iv [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]. }
clear MU WM.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(buf, buf + 1); (pbr + 8, pbr + 12); (bv_unsigned sp + -48 - 16, bv_unsigned sp + -48)] mc) as MU.
step. step. if_lit.
step. step. step. step. fold_mkR.
eapply (printbuf_reset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc md4 A4 _ LM FRS B4 pbr buf 0 32 lo content);
[ exact HPc | exact (conj Hbp (conj Hcap (conj Hlen (conj PBS PBUF)))) | rewrite ?unsigned_lit by lia; exact ST4 | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; reflexivity | ].
intros a1' a2' a3' a4' m6 MU6 WM6 MI6 PB6 ST6.
rewrite ?unsigned_lit in MU6, ST6 by lia.
transport_after_call asegs mc m6 MU6 WM6; try match goal with H : mem_inv asegs mc |- _ => clear H end.
replace (ret_pc (Z_to_bv 64 649036)) with (Z_to_bv 64 649036) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HP6 : HEAPAx A4 ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) LM FRS B4 m6 md4) by (heap_nowA A4L HIx HPc MU WM MI6).
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 1 HP6 INp4 ltac:(lia) ltac:(lia)) as SH1. replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SH1 by lia.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP6 INp4 ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.

assert (JN6 : jnode asegs A4F s m6 BS p rc pbr).
{ eapply (jnode_agree asegs A4F) with (BS := BS); [exact JNc | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a0 n0 Hin. cbn [disjoint_from].
assert (INa : In (a0, n0) (((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) ++ LM)).
{ apply in_or_app. left. right. right. rewrite ER in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right; apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a0 n0 HPc INa) as (_ & _ & _ & Hah & _).
assert (NEa : buf <> a0 /\ pbr <> a0).
{ assert (INm : In a0 (map blk_addr (((p, n) :: rest ++ LB) ++ LM))).
{ refine (in_map blk_addr _ (a0, n0) _). apply in_or_app. left. rewrite ER in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right; apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND. cbn [app map blk_addr fst] in ND.
apply NoDup_cons_iff in ND. destruct ND as [Hn1 ND1]. apply NoDup_cons_iff in ND1. destruct ND1 as [Hn2 _].
split; intros E0; [apply Hn2; rewrite E0; exact INm | apply Hn1; right; rewrite E0; exact INm]. }
destruct NEa as [NE1 NE2].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf 32 a0 n0 HPc ltac:(apply in_or_app; left; right; left; reflexivity) INa NE1) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 a0 n0 HPc ltac:(apply in_or_app; left; left; reflexivity) INa NE2) as D2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
assert (HPRc6 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc m6).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPc | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | ].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, 32. split; [apply in_or_app; left; right; left; reflexivity|]. split; [| lia].
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HPc (perm_swap (buf, 32) (pbr, 16) _) (Permutation_refl LM) (Permutation_refl FRS)) as HPs.
intro H. apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ buf 32 32 HPs); apply in_or_app; left; right; right; apply in_or_app; right; exact H|].
apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ buf 32 32 HPs); apply in_or_app; right; exact H|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; right; left; reflexivity) H).
- right; left. exists pbr, 16. split; [apply in_or_app; left; left; reflexivity|]. split; [| lia].
intro H. apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ pbr 16 16 HPc); apply in_or_app; left; right; right; apply in_or_app; right; exact H|].
apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ pbr 16 16 HPc); apply in_or_app; right; exact H|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; left; reflexivity) H).
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
change ((p, n) :: rest ++ LB) with (((p, n) :: rest) ++ LB) in HP6. rewrite <- ER in HP6.

assert (FINAL : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (ms' : machine_state) (r errv' : word)
(buf' cap' bpos' : Z) (content' : list byte),
ret_statew A4H ra sp gp (Z_to_bv 64 6434400) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md4) (cfg_model md') -> stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -48) m6 m' ->
rw_cells asegs m' (6434400 - 164) [C4 errv'] ->
HEAPAx A' ((pbr, 16) :: (buf', cap') :: BS ++ LB) LM FRS B' m' md' -> pbuf_core asegs m' pbr buf' bpos' cap' content' ->
32 <= cap' <= ser_capb 32 0 w -> bB B4 - 64 * (cap' - 32) <= bB B' -> bD B4 <= bD B' ->
AJ5 A4L HIx A' T md' ms').
{ intros m' md' A' B' ms' r errv' buf' cap' bpos' content' RS' VM' ST' HPR' ERR' HP' PB' Hc' HB' HD'.
eapply (K ms' md' m' A' B' r errv' (BS ++ [(pbr, 16); (buf', cap')]) [(pbr, 16); (buf', cap')]);
[ exact RS' | eapply model_vm_only_trans; [exact VM4 | exact VM'] | exact ST' | | exact ERR' | | | | | cbn; lia ].
- eapply heap_pres_trans; [exact HPR04|]. eapply heap_pres_trans; [exact HPR4c|]. eapply heap_pres_trans; [exact HPRc6|].
eapply heap_pres_weaken; [exact HPR' | lia |]. intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb].
- unfold jo_chargeA, gsB, ser_capb in *. cbn [uw_cost] in *. lia.
- eapply (heapA_perm A4L HIx); [exact HP' | | apply Permutation_refl | apply Permutation_refl].
rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply (Permutation_middle BS LB (buf', cap')) | apply (Permutation_middle BS ((buf', cap') :: LB) (pbr, 16))].
- apply (proj2 (jval_split asegs A4F _ _ _ _ _)). exists pbr, [(pbr, 16); (buf', cap')], BS. split; [reflexivity|]. split.
+ right. split; [lia|]. exists buf', bpos', cap', content'. split; [reflexivity | exact PB'].
+ eapply (jnode_agree asegs A4F) with (BS := BS); [exact JN6 | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR' | reflexivity |]. intros b Hb. apply in_or_app. left. apply in_or_app. left. exact Hb.
- exact (jtx_frame s BS w [] [(pbr, 16); (buf', cap')] JTX). }

assert (KSER : forall ms' md' A',
ser_postA HIx (Z_to_bv 64 649084) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) (Z_to_bv 64 (p + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 (p / 8 + 2147450882)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 F4 fc4 m6 md4 (BS ++ LB) LM FRS B4 pbr 32 0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms').
{ intros ms' md' A' (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS' & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS' as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F' & fc' & -> & FS' & FRM').
a4l. rewrite ?unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 649084)) with (Z_to_bv 64 649084) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR') in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR') in NODE; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; rewrite ER; left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
assert (INp' : In (p, n) ((pbr, 16) :: (buf', cap') :: BS ++ LB)) by (right; right; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP' INp' ltac:(lia) ltac:(lia)) as SH2'. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2' by lia.
pose proof (blk_granS HIx _ _ _ _ _ _ _ pbr 16 0 HP' ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SHpb. rewrite Z.add_0_r in SHpb.
pose proof PB' as (_ & _ & _ & PBS' & _).
clear SH1 SH2 MU WM MI6 ST6 ERR4.
pose proof (wmono_refl asegs m') as WM. pose proof (munch_refl (@nil (Z * Z)) m') as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. if_cases NEG; fold_mkR.
-
step. do 5 step. step. step.
evt_done5.
eapply (FINAL m' md' A' B'); [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS'] | intros X; apply FRM'; apply FRM4; exact X]
| exact VM' | release_frame FR ST' (bv_unsigned sp); exact ST' | exact HPR' | exact ERR' | exact HP' | exact PB' | lia | lia | lia].
- step. step. if_lit.
step. asan_chk0.
step. step. do 5 step. step. step.
evt_done5.
eapply (FINAL m' md' A' B'); [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS'] | intros X; apply FRM'; apply FRM4; exact X]
| exact VM' | release_frame FR ST' (bv_unsigned sp); exact ST' | exact HPR' | exact ERR' | exact HP' | exact PB' | lia | lia | lia]. }

assert (JH6 : JHEX_A m6).
{ unstash JHX0. eapply (JHEX_A_pres (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m6); [| exact JHX0].
eapply heap_pres_trans; [exact HPR04|]. eapply heap_pres_trans; [exact HPR4c | exact HPRc6]. }
assert (TOSER : forall (t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A4 T md4
(MS (mkR (Z_to_bv 64 649084) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0_ t1_ t2_ (Z_to_bv 64 (p + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 p) (Z_to_bv 64 pbr) (Z_to_bv 64 0) (Z_to_bv 64 1) a4_ a5_ a6_ a7_
(Z_to_bv 64 (p / 8 + 2147450882)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F4 (Z_to_bv 64 (afn_of s)) fc4 None m6 (seg_rom asegs))).
{ intros. pose proof (SERVAL s) as SPEC. unfold ser_specA in SPEC.
eapply SPEC with (A := A4) (LB := BS ++ LB) (LM := LM) (FRS := FRS) (B := B4) (buf := buf) (bpos := 0) (cap := 32) (lo := lo)
(content := [Z_to_bv 8 0] ++ skipn 1 content) (errv := e4) (REST := BS) (p := p) (rc := rc) (pb0 := pbr) (pb := pbr) (lv := 0) (fl := 1) (w := w) (Y := []) (R := []);
rewrite ?unsigned_lit by lia.
- exact HP6.
- exact PB6.
- exact JN6.
- intros b Hb. apply in_or_app. left. exact Hb.
- rewrite app_nil_r. exact JTX.
- lia.
- lia.
- unfold ser_need, ser_capb, gsB, pbnew32_costB in *. lia.
- split; [lia | reflexivity].
- lia.
- lia.
- exact FRSN.
- exact ST6.
- unfold alloc_ceiling, sp_window_lo, stack_max_size. exact LO.
- unfold ser_budgetA, ASER_LEVEL, ASER_LEAF. lia.
- clear - SPA. Z.div_mod_to_equations. lia.
- lia.
- exact ERR4.
- exact JH6.
- reflexivity.
- reflexivity.
- apply FRM4. exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- exact KSER. }
step. asan_chkA.
step. step. if_lit. rewrite ?zxb_zero.
step.
unfold afn_of in TOSER.
destruct s as [|[|]| |[|]|kids'|kids'];
try (exfalso; apply NSTR; reflexivity);
(lazymatch type of NODE with context [fn_ofF A4F ?s0] => let fv := eval vm_compute in (fn_ofF A4F s0) in change (fn_ofF A4F s0) with fv in NODE, TOSER end);
step; step; step; step; fold_mkR; evt_done5; apply TOSER.
Qed.
Theorem get_string_A : get_string_A_stmt.
Proof.
unfold get_string_A_stmt. intros until errv. intros PRE JV Hsd JHX JTX Hw FRSN BB BD FRM A0 K.
pose proof (jtx_nonneg _ _ _ _ JTX) as Hw0.
destruct (Z.eq_dec (jty s) JT_STRING) as [ES | NS].
- destruct s as [|u| |h|kids|kids]; try (cbn in ES; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in ES; discriminate ES).
eapply (get_string_strA h); try eassumption.
unfold gsB, pbnew32_costB in BB. lia.
- eapply (get_string_nsA s NS); eassumption.
Qed.
End Top.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Q228.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition AESC_LOOP : Z := 0xa1e0c.
Definition AESC_JOIN : Z := 0xa1df8.
Definition AESC_EXIT : Z := 0xa2154.
Definition ESC_MASK : Z := 140754668238592.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).

Definition escLoc (j0 : word) (j1 : list byte) : list cell :=
[C8 j0; C8 (wz Fr); C8 (wz n); C8 (wz Fr); C8 (wz (pb + 12)); C8 (wz 0); C8 (wz 0xec940);
C8 (wz (pb + 8)); C8 (wz (Fr + 32)); C8 (wz (Fr / 8 + 2147450880)); C8 (wz (18446744073709551615 - Sa)); C8 (wz pb); CB 16 j1; C8 (wz Fr)].
Definition escSaved : list cell := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition escFF (j8 sb j17 : list byte) : list cell := [C8 (wz 1102416563); C8 (wz 0x16294); C8 (wz 0xa1c40); CB 8 j8; CB 7 sb; CB 17 j17].
Definition escSH (v : Z) : list cell := [C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 241); C1 (b8 v); C1 (b8 243); C1 (b8 243); C1 (b8 243)].

Definition escCH (j0 : word) (j1 gj j8 sb j17 : list byte) (v : Z) : list (Z * list cell) :=
[(q, escLoc j0 j1); (q + 120, [CB (Z.to_nat d) gj]); (bv_unsigned sp + -104, escSaved); (Fr, escFF j8 sb j17); (Fr / 8 + 2147450880, escSH v)].

Definition esc_inv (v : Z) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists j0 j1 gj j8 sb j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH j0 j1 gj j8 sb j17 v) e m md.

Definition st_escA (pc : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (pos : Z) : machine_state :=
MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7
(wz 0) (wz pos) (wz Sa) (wz ESC_MASK) (wz (n - pos)) (wz 1) (wz pos) (wz (Sa + pos)) (wz 2147450880) x21 t3 t4 t5 t6)
F' (wz pc) fc' None m (seg_rom asegs).

Definition loopKA (k : Z) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z),
esc_inv 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> n - pos = k -> 0 <= e <= 6 * start ->
AJ5 A4L HIx A T md (st_escA AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).

Definition exitKA : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (start e : Z),
esc_inv 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= n -> 0 <= e <= 6 * start ->
AJ5 A4L HIx A T md (st_escA AESC_EXIT x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m n).
End Esc.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI.  Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QUrr. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 Q228.Mq9. Import Qwm6.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma wz_neg_unsignedS : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof. intros z. apply bv_eq. rewrite !unsigned_lit_wrap. change (2 ^ 64) with 18446744073709551616. rewrite Zminus_mod_idemp_r. f_equal. Qed.

Definition ser_quoteA : list byte := Eval vm_compute in match image_bytes asegs 0x23520 1 with Some bs => bs | None => [] end.

Section Ser.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Hypothesis ESC : esc_specA HIx.

Lemma blk_granS : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma ser_str_inlineA : ser_specA HIx ASER_STR (Sstr false).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & str & junk & EREST & Hlen0 & SRCL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX.
assert (Z57 : 57 <= str_objsize len) by (unfold str_objsize; lia).
replace (57 <=? str_objsize len) with true in JTX by (symmetry; apply Z.leb_le; exact Z57). injection JTX as <- _.
unfold ASER_STR, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INpL : In (p, str_objsize len) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, str_objsize len) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p (str_objsize len) HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (blk_granS _ _ _ _ _ _ _ p (str_objsize len) 5 HP INp ltac:(lia) ltac:(lia)) as SH5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof NODE as NODE0. stash NODE0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex.
step. step. step. ubsan_align Hpal.
do 3 step. step.
asan_chkA.
do 3 step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32. step. if_lit.
do 5 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) A FRS (bv_unsigned sp + -80) [(bv_unsigned sp + -80, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw : 6 * len + 2 <= str_w (str_objsize len)) by (unfold str_w, str_objsize; lia).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
unstash NODE0.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
assert (NODE2 : rw_cells asegs m2 p [C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string A4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INpL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold str_objsize in *. lia. }
assert (INp2 : In (p, str_objsize len) ((pb, PB_SZ) :: (buf2, cap2) :: LB)) by (right; right; exact INpL).
pose proof (blk_granS _ _ _ _ _ _ _ p (str_objsize len) 5 HP2 INp2 ltac:(lia) ltac:(lia)) as SH52.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH52 by lia.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf2 cap2 HP2 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal2 & Hblo2 & Hbhi2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite zxb_zero. step. if_lit.
step. step. step.
if_falsex.
step. if_truex.
step. step. step. step. fold_mkR.

assert (SRC2 : bytes_at asegs m2 (p + 48) str).
{ apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _] _)) in NODE2. destruct NODE2 as [_ NB]. cbn [cells_size csize Nat.add] in NB. change (Z.of_nat 48) with 48 in NB.
pose proof (rw_cells_bytes_at asegs _ _ _ NB) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. apply bytes_at_app in X. exact (proj1 X). }
evt_done5.
eapply (ser_escapeA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED JHX ESC) with (F := F) (src := str) (e := 0 + 1) (sa := p) (sk := str_objsize len);
[ exact INV2 | exact INpL | lia | unfold str_objsize; lia | exact SRC2 | exact SRCL | lia | lia | lia
| split; [exact Rfl | exact FL58] | exact FRSN | unfold AESC_STACK; lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros A3 m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (str_w (str_objsize len)) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0 + 1 + 6 * len);
[ exact INV3 | apply rodata_bytes_at; [exact MI3 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP3 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' F4 fc4 INV4 FS4 FR4 _.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & PB4 & CH4 & _ & _ & ERR4 & ST4 & HPR4 & VM4 & Hb4 & Hc4 & HB4 & HD4).
apply Forall_inv in CH4. cbn [fst snd] in CH4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. if_lit.
step. do 9 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m4, _, errv4, buf4, cap4, bpos4, content4, B4.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FR4]|].
split; [exact VM4|].
split; [release_frame CH4 ST4 (bv_unsigned sp); exact ST4|].
split; [exact HPR4|]. split; [exact ERR4|]. split; [exact HP4|]. split; [exact PB4|].
split; [lia|]. split; [exact Hc4|]. split; lia.
Qed.

Lemma ser_str_heapA : ser_specA HIx ASER_STR (Sstr true).
Proof.
unfold ser_specA. intros until errv. intros HP PB JN INCL JTX CAP TXT NEED FL Hlv Hlvd FRSN ST LO LOS SPA HT ERR JHX TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (len & pd & pdn & str & junk2 & EREST & Hlen0 & SRCL & Hpdn & NODE & PD). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp REST.
cbn [app jtx] in JTX.
rewrite Z.eqb_refl in JTX. injection JTX as <- _.
unfold ASER_STR, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
destruct FL as [Rfl FL58].
assert (FL32 : Z.land fl 32 = 0) by (replace 32 with (Z.land 58 32) by reflexivity; rewrite Z.land_assoc, FL58; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (INpL : In (p, 56) LB) by (apply INCL; left; reflexivity).
assert (INp : In (p, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INpL).
assert (INdL : In (pd, pdn) LB) by (apply INCL; right; left; reflexivity).
assert (INd : In (pd, pdn) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INdL).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 56 HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; exact INd)) as (_ & Hdal & Hdlo & Hdhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
shadow_inA A4L HIx HP INp SHp.
unfold_consts.
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof NODE as NODE0. stash NODE0. pose proof PD as PD0. stash PD0.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex.
step. step. step. ubsan_align Hpal.
do 3 step. step.
asan_chkA.
do 3 step. step. rewrite (unsigned_lit fl) by lia. rewrite FL32. step. if_lit.
do 5 step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
lazymatch type of FR with rw_cells _ _ _ ?frc =>
assert (INV1 : ser_memA HIx sp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) A FRS (bv_unsigned sp + -80) [(bv_unsigned sp + -80, frc)] 0 m1 md) end.
{ exists buf, cap, bpos, content, errv, B.
split; [heap_nowA A4L HIx HP MU WM MI1|].
split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [constructor; [exact FR | constructor]|].
split; [constructor; [left; cbn [fst]; lia | constructor]|].
split; [intros bb Hbb; exact Hbb|].
split; [exact ERR|]. split; [exact ST|].
split. { eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP]. }
split; [apply model_vm_only_refl|].
split; [lia|]. split; [unfold ser_capb; lia|]. split; lia. }
assert (Hw : 6 * len + 2 <= str_w (str_objsize len)) by (unfold str_w, str_objsize; lia).
pose proof INV1 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0);
[ exact INV1 | apply rodata_bytes_at; [exact MI1 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP1 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | apply fsaved_refl | exact FRM | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
unstash NODE0. unstash PD0.
pose proof INV2 as (buf2 & cap2 & bpos2 & content2 & errv2 & B2 & HP2 & PB2 & CH2 & _ & _ & ERR2 & ST2 & HPR2 & VM2 & Hb2 & Hc2 & HB2 & HD2).
apply Forall_inv in CH2. cbn [fst snd] in CH2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs hla_base A4L A4H] in MI2.
assert (NODE2 : rw_cells asegs m2 p [C4 (Z_to_bv 64 JT_STRING); C4 (Z_to_bv 64 rc); C8 (Z_to_bv 64 (fn_str_to_json_string A4F)); C8 (Z_to_bv 64 pb0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 pd)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INpL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
assert (PD2 : rw_cells asegs m2 pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR2 | exact PD0 |]. eapply client_range_block; [apply in_or_app; left; exact INdL | cbn [blk_addr fst]; lia |].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. lia. }
assert (INp2 : In (p, 56) ((pb, PB_SZ) :: (buf2, cap2) :: LB)) by (right; right; exact INpL).
shadow_inA A4L HIx HP2 INp2 SHp2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf2 cap2 HP2 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hbal2 & Hblo2 & Hbhi2 & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi2.
a4l. reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite zxb_zero. step. if_lit.
step. step. step.
if_truex.
asan_chkA. step.
step. if_falsex.
step. step. step. step.
rewrite wz_neg_unsignedS. rewrite (v_slt_0 (Z_to_bv 64 0) (Z_to_bv 64 len)) by (rewrite !signed_lit by lia; lia).
rewrite (v_slti_0 (Z_to_bv 64 (- len)) 0) by (rewrite zsig_lit by lia; lia).
if_lit.
step. step. step. step. fold_mkR.

assert (SRC2 : bytes_at asegs m2 pd str).
{ pose proof (rw_cells_bytes_at asegs _ _ _ PD2) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r in X. apply bytes_at_app in X. exact (proj1 X). }
evt_done5.
eapply (ser_escapeA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED JHX ESC) with (F := F) (src := str) (e := 0 + 1) (sa := pd) (sk := pdn);
[ exact INV2 | exact INdL | lia | lia | exact SRC2 | exact SRCL | lia | lia | lia
| split; [exact Rfl | exact FL58] | exact FRSN | unfold AESC_STACK; lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros A3 m3 md3 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 INV3 FS3 FR3.
pose proof INV3 as (buf3 & cap3 & bpos3 & content3 & errv3 & B3 & HP3 & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs hla_base A4L A4H] in MI3.
a4l. reenterA asegs A4L HIx asegs_wx HP3.
step. step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m md LB LM FRS B pb lo bpos cap (6 * Z.max 0 (pdn - 1) + 50) LO HT CAP TXT NEED OBL_REALLOC_NF) with (F := F) (sb := ser_quoteA) (e := 0 + 1 + 6 * (- len));
[ exact INV3 | apply rodata_bytes_at; [exact MI3 | vm_compute; reflexivity | lia | cbn; lia] | reflexivity | lia | lia
| right; right; apply src_globA_of_chk; vm_compute; reflexivity
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP3 | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| lia | lia | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 16 * 5) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS3 | exact FR3 | ].
intros A4 m4 md4 u0' u1' u2' b0' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' F4 fc4 INV4 FS4 FR4 _.
pose proof INV4 as (buf4 & cap4 & bpos4 & content4 & errv4 & B4 & HP4 & PB4 & CH4 & _ & _ & ERR4 & ST4 & HPR4 & VM4 & Hb4 & Hc4 & HB4 & HD4).
apply Forall_inv in CH4. cbn [fst snd] in CH4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
step. if_lit.
step. do 9 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m4, _, errv4, buf4, cap4, bpos4, content4, B4.
split; [apply ret_statew_intro; [exact FS4 | intros _; exact FR4]|].
split; [exact VM4|].
split; [release_frame CH4 ST4 (bv_unsigned sp); exact ST4|].
split; [exact HPR4|]. split; [exact ERR4|]. split; [exact HP4|]. split; [exact PB4|].
split; [lia|]. split; [exact Hc4|]. split; lia.
Qed.
End Ser.
End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QugP QW22.Mq7. Import QlKV.Mq2 QsKa Q9O6. Import QsKa.Mqd QJZd.Mq9 Q9O6.Mq5 QL3k.Mq4 Q228.Mqc. Import Qwm6.Mq1. Import QnPO.Mq4 QpNt.
Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition AGET_STRING_STACK (s : jshape) : Z := 48 + ser_budgetA s.
Definition gsB (w : Z) : Z := pbnew32_costB + 64 * (2 * w + 9).

Section Top.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition get_string_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (s : jshape) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
gsB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).

Lemma get_string_strA : forall (h : bool),
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK (Sstr h)) errv ->
jval asegs A4F (Sstr h) m BS p rc ->
jtx (Sstr h) BS = Some (w, []) ->
0 <= bB B -> 0 <= bD B -> 0 <= w ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F (Sstr h) m' BS' p rc ->
jtx (Sstr h) BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).
Proof.
intros h. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) JV JTX BB0 BD0 Hw0 FRM A0 K.
subst a0 tp.
pose proof JV as JV0. stash JV0.
pose proof (jval_fresh_node asegs A4F _ _ _ _ _ _ JV JTX) as JN.
destruct (jnode_hdrT asegs A4F _ _ _ _ _ _ JN) as (n & udel & ud & cs & rest & ER & Hn & _).
assert (INp : In (p, n) (BS ++ LB)) by (apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 0 HP INp ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 5 HP INp ltac:(lia) ltac:(lia)) as SH5. replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SH5 by lia.
unfold AGET_STRING, AGET_STRING_STACK, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. cbn [sdepth] in LOS.
word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.

assert (FIN : forall (m1 : word -> option byte) (ms1 : machine_state) (r : word),
munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp) -> rw_cells asegs m1 (6444320 - 164) [C4 errv] ->
ret_statew A4H ra sp gp (Z_to_bv 64 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m1 ms1 ->
AJ5 A4L HIx A T md ms1).
{ intros m1 ms1 r MU1 WM1 MI1 ST1 ERR1 RS1.
assert (HP1 : HEAPAx A (BS ++ LB) LM FRS B m1 md) by (heap_nowA A4L HIx HP MU1 WM1 MI1).
eapply (K ms1 md m1 A B r errv BS []); [exact RS1 | apply model_vm_only_refl | exact ST1 | | exact ERR1 | | exact HP1 | | exact JTX | cbn; lia].
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP].
- unfold jo_chargeA, gsB, pbnew32_costB. lia.
- unstash JV0. eapply (jval_agree asegs A4F); [exact JV0 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU1 | exact WM1 |]. intros a0 n0 Hin.
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ _ a0 n0 HP); [apply in_or_app; left; apply in_or_app; left; exact Hin |].
constructor; [cbn [fst]; lia | constructor]. }
destruct h.
-
destruct JN as (len & pd & pdn & str & junk2 & EREST & Hlen0 & SRCL & Hpdn & NODE & PD). unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (En : n = 56) by (rewrite EREST in ER; injection ER as <- _; reflexivity). subst n.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p 56 6 HP INp ltac:(lia) ltac:(lia)) as SH6. replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SH6 by lia.
clear PD.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. bstep. bstep. if_lit.
bstep. asan_chkA.
bstep. bstep. bstep. if_falsex.
bstep. bstep. sh_norm.
replace ((p + 48) / 8 + 2147450880) with (p / 8 + 2147450886) by (clear - Hpal; Z.div_mod_to_equations; lia).
bstep. bstep. if_lit.
bstep. bstep.
do 5 bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (FIN m1); [exact MU | exact WM | exact MI1 | release_frame FR ST (bv_unsigned sp); exact ST | exact ERR |].
apply ret_statew_intro; [apply fsaved_refl | intros X; exact X].
-
destruct JN as (len & str & junk & EREST & Hlen0 & SRCL & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (En : n = str_objsize len) by (rewrite EREST in ER; injection ER as <- _; reflexivity). subst n.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _; _] _)) in NODE. destruct NODE as [NODE _].
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. bstep. bstep. if_lit.
bstep. asan_chkA.
bstep. bstep. bstep. if_truex.
do 5 bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
evt_done5.
eapply (FIN m1); [exact MU | exact WM | exact MI1 | release_frame FR ST (bv_unsigned sp); exact ST | exact ERR |].
apply ret_statew_intro; [apply fsaved_refl | intros X; exact X].
Qed.

Lemma rest_tl_sepA : forall A PRE L1 LMx FRx Bx m md p n rest a k,
HEAPAx A (PRE ++ ((p, n) :: rest) ++ L1) LMx FRx Bx m md -> 24 <= n -> In (a, k) rest -> a + k <= p + 16 \/ p + 24 <= a.
Proof.
intros A PRE L1 LMx FRx Bx m md p n rest a k HP Hn Hin.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (INa : In (a, k) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; right; exact Hin).
assert (INp : In (p, n) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (NE : p <> a).
{ intros ->. rewrite <- !app_assoc in ND. cbn [app] in ND. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND.
apply in_or_app. right. exact (in_map blk_addr _ (a, k) ltac:(apply in_or_app; left; exact Hin)). }
destruct (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ p n a k HP INp INa NE) as [D|D]; lia.
Qed.

Lemma node_write_outside : forall A PRE rest L1 LMx FRx Bx m md p n lo1 hi1,
HEAPAx A (PRE ++ ((p, n) :: rest) ++ L1) LMx FRx Bx m md -> p <= lo1 -> hi1 <= p + n ->
Forall (fun iv : Z * Z => (alloc_ceiling <= fst iv /\ snd iv <= alloc_ceiling)
\/ (exists a k, In (a, k) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx) /\ ~ In (a, k) (L1 ++ LMx ++ fr_ivs A4L FRx) /\ a <= fst iv /\ snd iv <= a + k)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)) [(lo1, hi1)].
Proof.
intros A PRE rest L1 LMx FRx Bx m md p n lo1 hi1 HP Hlo Hhi.
apply Forall_cons; [| apply Forall_nil]. right; left. exists p, n. cbn [fst snd].
assert (INp : In (p, n) ((PRE ++ ((p, n) :: rest) ++ L1) ++ LMx)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
split; [exact INp|]. split; [| lia].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
rewrite <- !app_assoc in ND. cbn [app] in ND. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND.
intro H. apply in_app_or in H. destruct H as [H|H].
- apply ND. apply in_or_app. right. exact (in_map blk_addr _ (p, n) ltac:(apply in_or_app; right; apply in_or_app; left; exact H)).
- apply in_app_or in H. destruct H as [H|H].
+ apply ND. apply in_or_app. right. exact (in_map blk_addr _ (p, n) ltac:(apply in_or_app; right; apply in_or_app; right; exact H)).
+ exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INp H).
Qed.

Hypothesis SERVAL : SERVALA HIx.

Lemma get_string_nsA : forall (s : jshape), jty s <> JT_STRING ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (p rc lo w : Z) (errv : word),
jo_preA HIx A (BS ++ LB) LM FRS B m md sp tp ra lo (AGET_STRING_STACK s) errv ->
jval asegs A4F s m BS p rc -> sdepth s <= 1000 -> jhex_A m ->
jtx s BS = Some (w, []) -> w < 2^27 ->
Z.of_nat (length FRS) + 1 < 4096 ->
gsB w <= bB B -> 0 <= bD B ->
frm0 fc -> a0 = wz p ->
(forall ms' md' m' (A' : ASA A4L HIx) (B' : bud) (r : word) (errv' : word) (BS' PT' : list blk),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
rw_cells asegs m' A_ERRNO [C4 errv'] ->
jo_chargeA (gsB w) 0 B B' ->
HEAPAx A' (BS' ++ LB) LM FRS B' m' md' -> jval asegs A4F s m' BS' p rc ->
jtx s BS' = Some (w, PT') -> Z.of_nat (length PT') <= 2 ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AGET_STRING) fc None m (seg_rom asegs)).
Proof.
intros s NSTR. intros until errv. intros (HP & ST & LO & LOS & SPA & HT & ERR & TP' & RA) JV Hsd JHX JTX Hw27 FRSN BB BD FRM A0 K.
subst a0 tp.
pose proof (jtx_nonneg _ _ _ _ JTX) as Hw0.
pose proof (jval_fresh_node asegs A4F _ _ _ _ _ _ JV JTX) as JN.
destruct (jnode_hdrT asegs A4F _ _ _ _ _ _ JN) as (n & udel & ud & cs & rest & ER & Hn & NODE).
assert (INp : In (p, n) (BS ++ LB)) by (apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p n HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 0 HP INp ltac:(lia) ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP INp ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _; _] cs)) in NODE. destruct NODE as [NODE _].
pose proof (jty_range s) as JTR.
pose proof (sdepth_nonneg s) as SD0.
pose proof JN as JN0. stash JN0. pose proof JHX as JHX0. stash JHX0. pose proof HP as HP00. stash HP00.
unfold AGET_STRING, AGET_STRING_STACK, ser_budgetA, ASER_LEVEL, ASER_LEAF in *. unfold JT_STRING in NSTR.
word_range sp SPR. unfold_consts.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
pose proof alloc_ceiling_range as ACR.
a4l. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 48%nat ST.
do 6 bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. bstep. bstep. norm_sx32. if_truex.
bstep. asan_chkA.
bstep. bstep. if_lit.
bstep. bstep. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.

evt_done5.
eapply (printbuf_new32_A_cps HIx) with (u := UWptr) (lo := lo);
[ heap_nowA A4L HIx HP MU WM MI1 | apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right] | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [reflexivity | lia].
all: try (clear - SPA; Z.div_mod_to_equations; lia).
all: try eassumption.
1: (unfold gsB, pbnew32_costB in BB |- *; lia).
intros ms4 md4 A4 (m4 & pbr & e4 & B4 & RS4 & VM4 & ST4 & HPR4 & ERR4 & BB4 & BD4 & OUT4).
destruct RS4 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F4 & fc4 & -> & FS4 & FRM4).
a4l. rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HPR4 by lia.
cbn [uw_cost] in BD4.
replace (ret_pc (Z_to_bv 64 656116)) with (Z_to_bv 64 656116) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (HPR04 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m4).
{ eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |]. unstash HP00.
eapply (client_outsideA A4L HIx); [exact HP00 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | solve_clientWA A4L HIx HP00].
- eapply heap_pres_weaken; [exact HPR4 | lia |]. intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb]. }

assert (JN4 : jnode asegs A4F s m4 BS p rc 0).
{ unstash JN0. unstash HP00.
eapply (jnode_agree asegs A4F) with (BS := BS); [ | | apply incl_refl].
- eapply (jnode_agree asegs A4F) with (BS := BS); [exact JN0 | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a0 n0 Hin.
eapply (heapA_blocks_below HIx _ _ _ _ _ _ _ _ a0 n0 HP00); [apply in_or_app; left; apply in_or_app; left; exact Hin |].
constructor; [cbn [fst]; lia | constructor].
- eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity |]. intros b Hb. apply in_or_app. left. apply in_or_app. left. exact Hb. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in NODE; [| eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]]. a4l.
clear MU WM MI1 ST GOT CELL SH0 SH2 HP.
destruct OUT4 as [(-> & HP4) | (Hpbr & buf & content & PB4 & HP4)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP4 ltac:(apply in_or_app; left; exact INp)) as Himg.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP4 INp ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [(p + 16, p + 24)] m4) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
bstep. bstep. if_lit.
bstep. bstepz. bstep. bstep. if_lit.
bstep. do 5 bstep. bstep. bstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
match goal with H : mem_inv asegs m5 |- _ => rename H into MI5 end.
assert (HP4' : HEAPAx A4 ((p, n) :: rest ++ LB) LM FRS B4 m4 md4) by (rewrite ER in HP4; exact HP4).
assert (HP5 : HEAPAx A4 (BS ++ LB) LM FRS B4 m5 md4).
{ rewrite ER. cbn [app]. eapply (heapA_client_frame A4L HIx); [exact HP4' | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP4' MU); solve_frameW_withA HP4' | exact WM | exact MI5]. }
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m4 m5).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP4' | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia |].
eapply Forall_impl; [| exact (node_write_outside A4 [] rest LB LM FRS B4 m4 md4 p n (p + 16) (p + 24) HP4' ltac:(lia) ltac:(lia))].
intros iv [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]. }
assert (JN5 : jnode asegs A4F s m5 BS p rc 0).
{ eapply (jnode_set_pb asegs A4F); [exact JN4 | exact MU | exact WM | | ].
- apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in NODE. destruct NODE as [_ N2]. cbn [cells_size csize Nat.add] in N2. change (Z.of_nat 16) with 16 in N2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in N2. exact (proj1 N2).
- intros a0 k0 Hin. rewrite ER in Hin. cbn [tl] in Hin.
eapply (rest_tl_sepA A4 [] LB LM FRS B4 m4 md4 p n rest a0 k0); [cbn [app]; exact HP4' | lia | exact Hin]. }
evt_done5.
eapply (K _ md4 m5 A4 B4 _ e4 BS []);
[ apply ret_statew_intro; [exact FS4 | exact FRM4] | exact VM4 | release_frame FR ST4 (bv_unsigned sp); exact ST4
| eapply heap_pres_trans; [exact HPR04 | exact HPR45] | exact ERR4
| unfold jo_chargeA, gsB in *; lia | exact HP5
| apply (proj2 (jval_split asegs A4F _ _ _ _ _)); exists 0, [], BS; split; [rewrite app_nil_r; reflexivity |]; split; [left; split; reflexivity | exact JN5]
| exact JTX | cbn; lia ].
-
rewrite ER in HP4. cbn [app] in HP4.
assert (INp4 : In (p, n) ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB)) by (right; right; left; reflexivity).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs hla_base A4L A4H] in MI4.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ p n HP4 ltac:(apply in_or_app; left; exact INp4)) as Himg.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pbr 16 HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf 32 HP4 ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hfal & Hflo & Hfhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pbr 16 HP4 ltac:(apply in_or_app; left; left; reflexivity)) as Himgb.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf 32 HP4 ltac:(apply in_or_app; left; right; left; reflexivity)) as Himgf.
assert (NEpb : pbr <> p) by (intros ->; eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ p 16 n HP4); apply in_or_app; left; right; left; reflexivity).
assert (NEfb : buf <> p).
{ intros ->. pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HP4 (perm_swap (p, 32) (pbr, 16) _) (Permutation_refl LM) (Permutation_refl FRS)) as HPs.
eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ p 32 n HPs). apply in_or_app. left. right. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 p n HP4 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; exact INp4) NEpb) as DJb.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf 32 p n HP4 ltac:(apply in_or_app; left; right; left; reflexivity) ltac:(apply in_or_app; left; exact INp4) NEfb) as DJf.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP4 INp4 ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.
pose proof PB4 as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts.
pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [(p + 16, p + 24)] m4) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP4.
bstep. bstep. if_lit.
bstep. bstep. bstep. bstep. if_falsex.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
match goal with H : mem_inv asegs mc |- _ => rename H into MIc end.

assert (HPc : HEAPAx A4 ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) LM FRS B4 mc md4) by (heap_nowA A4L HIx HP4 MU WM MIc).
assert (JNc : jnode asegs A4F s mc BS p rc pbr).
{ eapply (jnode_set_pb asegs A4F); [exact JN4 | exact MU | exact WM | | ].
- apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in NODE. destruct NODE as [_ N2]. cbn [cells_size csize Nat.add] in N2. change (Z.of_nat 16) with 16 in N2.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in N2. exact (proj1 N2).
- intros a0 k0 Hin. rewrite ER in Hin. cbn [tl] in Hin.
eapply (rest_tl_sepA A4 [(pbr, 16); (buf, 32)] LB LM FRS B4 m4 md4 p n rest a0 k0); [cbn [app]; exact HP4 | lia | exact Hin]. }
assert (HPR4c : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m4 mc).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP4 | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia |].
eapply Forall_impl; [| exact (node_write_outside A4 [(pbr, 16); (buf, 32)] rest LB LM FRS B4 m4 md4 p n (p + 16) (p + 24) HP4 ltac:(lia) ltac:(lia))].
intros iv [H|[H|H]]; [left; lia | right; left; exact H | right; right; exact H]. }
clear MU WM.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(buf, buf + 1); (pbr + 8, pbr + 12); (bv_unsigned sp + -48 - 16, bv_unsigned sp + -48)] mc) as MU.
bstep. bstep. if_lit.
bstep. bstep. bstep. bstep. fold_mkR.
eapply (printbuf_reset_A HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc md4 A4 _ LM FRS B4 pbr buf 0 32 lo content);
[ exact HPc | exact (conj Hbp (conj Hcap (conj Hlen (conj PBS PBUF)))) | rewrite ?unsigned_lit by lia; exact ST4 | exact LO | rewrite ?unsigned_lit by lia; lia
| rewrite ?unsigned_lit by lia; reflexivity | ].
intros a1' a2' a3' a4' m6 MU6 WM6 MI6 PB6 ST6.
rewrite ?unsigned_lit in MU6, ST6 by lia.
transport_after_call asegs mc m6 MU6 WM6; try match goal with H : mem_inv asegs mc |- _ => clear H end.
replace (ret_pc (Z_to_bv 64 656164)) with (Z_to_bv 64 656164) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (HP6 : HEAPAx A4 ((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) LM FRS B4 m6 md4) by (heap_nowA A4L HIx HPc MU WM MI6).
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 1 HP6 INp4 ltac:(lia) ltac:(lia)) as SH1. replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SH1 by lia.
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP6 INp4 ltac:(lia) ltac:(lia)) as SH2. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2 by lia.

assert (JN6 : jnode asegs A4F s m6 BS p rc pbr).
{ eapply (jnode_agree asegs A4F) with (BS := BS); [exact JNc | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a0 n0 Hin. cbn [disjoint_from].
assert (INa : In (a0, n0) (((pbr, 16) :: (buf, 32) :: (p, n) :: rest ++ LB) ++ LM)).
{ apply in_or_app. left. right. right. rewrite ER in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right; apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a0 n0 HPc INa) as (_ & _ & _ & Hah & _).
assert (NEa : buf <> a0 /\ pbr <> a0).
{ assert (INm : In a0 (map blk_addr (((p, n) :: rest ++ LB) ++ LM))).
{ refine (in_map blk_addr _ (a0, n0) _). apply in_or_app. left. rewrite ER in Hin. destruct Hin as [Hin|Hin]; [left; exact Hin | right; apply in_or_app; left; exact Hin]. }
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND. cbn [app map blk_addr fst] in ND.
apply NoDup_cons_iff in ND. destruct ND as [Hn1 ND1]. apply NoDup_cons_iff in ND1. destruct ND1 as [Hn2 _].
split; intros E0; [apply Hn2; rewrite E0; exact INm | apply Hn1; right; rewrite E0; exact INm]. }
destruct NEa as [NE1 NE2].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf 32 a0 n0 HPc ltac:(apply in_or_app; left; right; left; reflexivity) INa NE1) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pbr 16 a0 n0 HPc ltac:(apply in_or_app; left; left; reflexivity) INa NE2) as D2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
assert (HPRc6 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc m6).
{ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HPc | intros bb Hbb; apply in_app_or in Hbb; apply in_or_app; destruct Hbb as [Hbb|Hbb]; [left; right; right; right; apply in_or_app; right; exact Hbb | right; exact Hbb] | lia | ].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd].
- right; left. exists buf, 32. split; [apply in_or_app; left; right; left; reflexivity|]. split; [| lia].
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HPc (perm_swap (buf, 32) (pbr, 16) _) (Permutation_refl LM) (Permutation_refl FRS)) as HPs.
intro H. apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ buf 32 32 HPs); apply in_or_app; left; right; right; apply in_or_app; right; exact H|].
apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ buf 32 32 HPs); apply in_or_app; right; exact H|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; right; left; reflexivity) H).
- right; left. exists pbr, 16. split; [apply in_or_app; left; left; reflexivity|]. split; [| lia].
intro H. apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ pbr 16 16 HPc); apply in_or_app; left; right; right; apply in_or_app; right; exact H|].
apply in_app_or in H. destruct H as [H|H]; [eapply (fresh_not_inA A4L HIx _ _ _ _ _ _ _ pbr 16 16 HPc); apply in_or_app; right; exact H|].
exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HPc ltac:(apply in_or_app; left; left; reflexivity) H).
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia. }
change ((p, n) :: rest ++ LB) with (((p, n) :: rest) ++ LB) in HP6. rewrite <- ER in HP6.

assert (FINAL : forall (m' : word -> option byte) (md' : config) (A' : ASA A4L HIx) (B' : bud) (ms' : machine_state) (r errv' : word)
(buf' cap' bpos' : Z) (content' : list byte),
ret_statew A4H ra sp gp (Z_to_bv 64 6444320) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md4) (cfg_model md') -> stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -48) m6 m' ->
rw_cells asegs m' (6444320 - 164) [C4 errv'] ->
HEAPAx A' ((pbr, 16) :: (buf', cap') :: BS ++ LB) LM FRS B' m' md' -> pbuf_core asegs m' pbr buf' bpos' cap' content' ->
32 <= cap' <= ser_capb 32 0 w -> bB B4 - 64 * (cap' - 32) <= bB B' -> bD B4 <= bD B' ->
AJ5 A4L HIx A' T md' ms').
{ intros m' md' A' B' ms' r errv' buf' cap' bpos' content' RS' VM' ST' HPR' ERR' HP' PB' Hc' HB' HD'.
eapply (K ms' md' m' A' B' r errv' (BS ++ [(pbr, 16); (buf', cap')]) [(pbr, 16); (buf', cap')]);
[ exact RS' | eapply model_vm_only_trans; [exact VM4 | exact VM'] | exact ST' | | exact ERR' | | | | | cbn; lia ].
- eapply heap_pres_trans; [exact HPR04|]. eapply heap_pres_trans; [exact HPR4c|]. eapply heap_pres_trans; [exact HPRc6|].
eapply heap_pres_weaken; [exact HPR' | lia |]. intros bb Hbb. apply in_app_or in Hbb. apply in_or_app. destruct Hbb as [Hbb|Hbb]; [left; apply in_or_app; right; exact Hbb | right; exact Hbb].
- unfold jo_chargeA, gsB, ser_capb in *. cbn [uw_cost] in *. lia.
- eapply (heapA_perm A4L HIx); [exact HP' | | apply Permutation_refl | apply Permutation_refl].
rewrite <- app_assoc. cbn [app].
eapply Permutation_trans; [apply perm_skip; apply (Permutation_middle BS LB (buf', cap')) | apply (Permutation_middle BS ((buf', cap') :: LB) (pbr, 16))].
- apply (proj2 (jval_split asegs A4F _ _ _ _ _)). exists pbr, [(pbr, 16); (buf', cap')], BS. split; [reflexivity|]. split.
+ right. split; [lia|]. exists buf', bpos', cap', content'. split; [reflexivity | exact PB'].
+ eapply (jnode_agree asegs A4F) with (BS := BS); [exact JN6 | | apply incl_refl].
eapply (agree_of_heap_pres asegs A4H); [exact HPR' | reflexivity |]. intros b Hb. apply in_or_app. left. apply in_or_app. left. exact Hb.
- exact (jtx_frame s BS w [] [(pbr, 16); (buf', cap')] JTX). }

assert (KSER : forall ms' md' A',
ser_postA HIx (Z_to_bv 64 656212) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) (Z_to_bv 64 (p + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 (p / 8 + 2147450882)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 F4 fc4 m6 md4 (BS ++ LB) LM FRS B4 pbr 32 0 w lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms').
{ intros ms' md' A' (m' & r & errv' & buf' & cap' & bpos' & content' & B' & RS' & VM' & ST' & HPR' & ERR' & HP' & PB' & Hbp' & Hcap' & HBB' & HBD').
destruct RS' as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & F' & fc' & -> & FS' & FRM').
a4l. rewrite ?unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 656212)) with (Z_to_bv 64 656212) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR') in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR') in NODE; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; rewrite ER; left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
assert (INp' : In (p, n) ((pbr, 16) :: (buf', cap') :: BS ++ LB)) by (right; right; apply in_or_app; left; rewrite ER; left; reflexivity).
pose proof (blk_granS HIx _ _ _ _ _ _ _ p n 2 HP' INp' ltac:(lia) ltac:(lia)) as SH2'. replace (p / 8 + 2147450880 + 2) with (p / 8 + 2147450882) in SH2' by lia.
pose proof (blk_granS HIx _ _ _ _ _ _ _ pbr 16 0 HP' ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SHpb. rewrite Z.add_0_r in SHpb.
pose proof PB' as (_ & _ & _ & PBS' & _).
clear SH1 SH2 MU WM MI6 ST6 ERR4.
pose proof (wmono_refl asegs m') as WM. pose proof (munch_refl (@nil (Z * Z)) m') as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
bstep. if_cases NEG; fold_mkR.
-
bstep. do 5 bstep. bstep. bstep.
evt_done5.
eapply (FINAL m' md' A' B'); [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS'] | intros X; apply FRM'; apply FRM4; exact X]
| exact VM' | release_frame FR ST' (bv_unsigned sp); exact ST' | exact HPR' | exact ERR' | exact HP' | exact PB' | lia | lia | lia].
- bstep. bstep. if_lit.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ pbr 16 HP' ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hpbral & Hpbrlo & Hpbrhi & _).
pose proof alloc_ceiling_range as ACRb.
step. ub_skip. try if_falsex. try ub_skip. asan_chk0.
bstep. bstep. do 5 bstep. bstep. bstep.
evt_done5.
eapply (FINAL m' md' A' B'); [apply ret_statew_intro; [eapply fsaved_trans; [exact FS4 | exact FS'] | intros X; apply FRM'; apply FRM4; exact X]
| exact VM' | release_frame FR ST' (bv_unsigned sp); exact ST' | exact HPR' | exact ERR' | exact HP' | exact PB' | lia | lia | lia]. }

assert (JH6 : JHEX_A m6).
{ unstash JHX0. eapply (JHEX_A_pres (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m6); [| exact JHX0].
eapply heap_pres_trans; [exact HPR04|]. eapply heap_pres_trans; [exact HPR4c | exact HPRc6]. }
assert (TOSER : forall (t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
AJ5 A4L HIx A4 T md4
(MS (mkR (Z_to_bv 64 656212) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6444320) t0_ t1_ t2_ (Z_to_bv 64 (p + 16)) (Z_to_bv 64 2147450880)
(Z_to_bv 64 p) (Z_to_bv 64 pbr) (Z_to_bv 64 0) (Z_to_bv 64 1) a4_ a5_ a6_ a7_
(Z_to_bv 64 (p / 8 + 2147450882)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F4 (Z_to_bv 64 (afn_of s)) fc4 None m6 (seg_rom asegs))).
{ intros. pose proof (SERVAL s) as SPEC. unfold ser_specA in SPEC.
eapply SPEC with (A := A4) (LB := BS ++ LB) (LM := LM) (FRS := FRS) (B := B4) (buf := buf) (bpos := 0) (cap := 32) (lo := lo)
(content := [Z_to_bv 8 0] ++ skipn 1 content) (errv := e4) (REST := BS) (p := p) (rc := rc) (pb0 := pbr) (pb := pbr) (lv := 0) (fl := 1) (w := w) (Y := []) (R := []);
rewrite ?unsigned_lit by lia.
- exact HP6.
- exact PB6.
- exact JN6.
- intros b Hb. apply in_or_app. left. exact Hb.
- rewrite app_nil_r. exact JTX.
- lia.
- lia.
- unfold ser_need, ser_capb, gsB, pbnew32_costB in *. lia.
- split; [lia | reflexivity].
- lia.
- lia.
- exact FRSN.
- exact ST6.
- unfold alloc_ceiling, sp_window_lo, stack_max_size. exact LO.
- unfold ser_budgetA, ASER_LEVEL, ASER_LEAF. lia.
- clear - SPA. Z.div_mod_to_equations. lia.
- lia.
- exact ERR4.
- exact JH6.
- reflexivity.
- reflexivity.
- apply FRM4. exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- exact KSER. }
bstep. asan_chkA.
bstep. bstep. if_lit. rewrite ?zxb_zero.
bstep.
unfold afn_of in TOSER.
destruct s as [|[|]| |[|]|kids'|kids'];
try (exfalso; apply NSTR; reflexivity);
(lazymatch type of NODE with context [fn_ofF A4F ?s0] => let fv := eval vm_compute in (fn_ofF A4F s0) in change (fn_ofF A4F s0) with fv in NODE, TOSER end);
bstep; bstep; bstep; bstep; fold_mkR; evt_done5; apply TOSER.
Qed.
Theorem get_string_A : get_string_A_stmt.
Proof.
unfold get_string_A_stmt. intros until errv. intros PRE JV Hsd JHX JTX Hw FRSN BB BD FRM A0 K.
pose proof (jtx_nonneg _ _ _ _ JTX) as Hw0.
destruct (Z.eq_dec (jty s) JT_STRING) as [ES | NS].
- destruct s as [|u| |h|kids|kids]; try (cbn in ES; unfold JT_BOOLEAN, JT_DOUBLE, JT_INT, JT_STRING, JT_OBJECT, JT_ARRAY in ES; discriminate ES).
eapply (get_string_strA h); try eassumption.
unfold gsB, pbnew32_costB in BB. lia.
- eapply (get_string_nsA s NS); eassumption.
Qed.
End Top.
End RC__1.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mq9.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AEsc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition esc_specA_al (d : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(pb buf bpos cap Sa n fl lo sa sk : Z) (src content : list byte) (errv : word),
bv_unsigned sp mod 32 = d ->
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbuf_core asegs m pb buf bpos cap content ->
In (sa, sk) LB -> sa <= Sa -> Sa + n <= sa + sk ->
bytes_at asegs m Sa src -> Z.of_nat (length src) = n -> 0 <= n < 2^31 ->
32 <= cap < 2^30 -> bpos + 6 * n < 2^28 -> ser_need cap bpos (6 * n) <= bB B ->
aflags_ok fl ->
Z.of_nat (length FRS) + 1 < 4096 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AESC_STACK ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> JHEX_A m ->
tp = wz A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = wz pb -> a1 = wz Sa -> a2 = wz n -> a3 = wz fl ->
(forall ms' md' A', ser_postA HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B pb cap bpos (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz AESCAPE) fc None m (seg_rom asegs)).

Lemma esc_specA_of_al : esc_specA_al 0 -> esc_specA_al 16 -> esc_specA HIx.
Proof.
intros H0 H16. unfold esc_specA. intros until errv. intros HP PB INs Hs1 Hs2 SRC SRCL Hn CAP TXT NEED FL FRSN ST LO LOS SPA.
assert (D32 : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct D32 as [D32 | D32]; [eapply H0 | eapply H16]; eassumption.
Qed.
End AEsc.
End RC__1.
