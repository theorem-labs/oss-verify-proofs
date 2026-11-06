(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Ql4f Q9O6 QL3k Q228 QiVi QZ8V Q1Ey Q4xz QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 QlKV.Mq6 Ql4f.Mq2 Q228.Mq0 QiVi.Mq1 Qwm6.Mq1 QZ8V.Mq0.

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

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n q d Fr).
Notation st_escx := (st_escA sp gp Sa n q Fr).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Local Notation esc_srcA := (QZ8V.Mq0.esc_srcA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src q d Fr INs Hs1 Hs2 SRC0 SRCL).
Local Notation esc_fetchA := (QZ8V.Mq0.esc_fetchA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr INs Hs1 Hs2 SRC0 SRCL).
Local Notation esc_appendA := (QZ8V.Mq0.esc_appendA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED).
Local Notation esc_inv_sbx := (QZ8V.Mq0.esc_inv_sbx HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n q d Fr).
Local Notation esc_inv_privA := (QZ8V.Mq0.esc_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n src q d Fr Hd Hq Hq32 LO LOS HT CAP0).
Local Notation esc_inv_shA := (QZ8V.Mq0.esc_inv_shA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n src q d Fr Hd Hq Hq32 LO LOS HT CAP0).
Local Notation esc_ctrl_appA := (QZ8V.Mq0.esc_ctrl_appA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED Hn).

Definition esc_hexA : list byte := Eval vm_compute in match image_bytes asegs 0x23320 16 with Some bs => bs | None => [] end.
Lemma esc_hex_shadowA : forall A LBx LMx FRx B m md g, HEAPAx A LBx LMx FRx B m md -> g = 18020 \/ g = 18021 ->
ro_cells asegs m (g + 2147450880) [C1 (b8 0)].
Proof.
intros A LBx LMx FRx B m md g HP Hg. apply QsKa.Mq1.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) g = 0) by (destruct Hg as [-> | ->]; vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
apply X; destruct Hg as [-> | ->]; vm_compute; discriminate.
Qed.

Lemma esc_ctrl_hexA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e cz : Z),
esc_invx 7 A e m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * pos -> 0 <= cz < 32 ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa00fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz cz) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cz. intros INV FS FR Hpos He Hcz IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, FFx, SHx. unfold escLoc in LOC. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HTLE. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).

assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
pose proof (ro_C8_of_bytes_at asegs _ _ _ JH) as JHC. unfold A_JHEX_SLOT, A_JHEX in JHC.
assert (HEXB : bytes_at asegs m 0x23320 esc_hexA) by (apply Q4xz.rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
set (hi := Z.shiftr cz 4). set (lo4 := Z.land cz 15).
assert (Hhi : 0 <= hi <= 1).
{ unfold hi. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. clear - Hcz. split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
assert (Hlo4 : 0 <= lo4 <= 15).
{ unfold lo4. replace (Z.land cz 15) with (cz mod 16) by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity). pose proof (Z.mod_pos_bound cz 16 ltac:(lia)). lia. }
destruct (nth_error esc_hexA (Z.to_nat hi)) as [ch1|] eqn:N1; [| apply nth_error_None in N1; cbn [esc_hexA length] in N1; lia].
destruct (nth_error esc_hexA (Z.to_nat lo4)) as [ch2|] eqn:N2; [| apply nth_error_None in N2; cbn [esc_hexA length] in N2; lia].
pose proof (Q1Ey.payload_byteA _ _ _ _ _ HEXB N1 ltac:(lia)) as RD1.
pose proof (Q1Ey.payload_byteA _ _ _ _ _ HEXB N2 ltac:(lia)) as RD2.
pose proof (esc_hex_shadowA _ _ _ _ _ _ _ 18020 HP ltac:(left; reflexivity)) as SHG0.
pose proof (esc_hex_shadowA _ _ _ _ _ _ _ 18021 HP ltac:(right; reflexivity)) as SHG1.
change (18020 + 2147450880) with 2147468900 in SHG0. change (18021 + 2147450880) with 2147468901 in SHG1.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.

assert (SNPK : evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 655692) (Z_to_bv 64 q) gp (Z_to_bv 64 6434400) t0 t1 t2 sp (Z_to_bv 64 q)
(Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 7) (Z_to_bv 64 145056) (Z_to_bv 64 (bv_unsigned ch1)) (Z_to_bv 64 (bv_unsigned ch2)) a5 a6 a7
(Z_to_bv 64 47) (Z_to_bv 64 n) (Z_to_bv 64 Sa) (Z_to_bv 64 cz) (Z_to_bv 64 0) (Z_to_bv 64 pos) (Z_to_bv 64 pos)
(Z_to_bv 64 (Fr / 8 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ESC_MASK) t3 t4 t5 t6)
F' (Z_to_bv 64 326044) fc' None m (seg_rom asegs))).
{ apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFe, FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. change (Fr + 32 + Z.of_nat 7) with (Fr + 32 + 7) in FFb.
assert (SBL : length sb = 7%nat) by (destruct FFe as [[[Hwf _] _] _]; exact Hwf).
destruct (sbuf7_shadow_word m _ SHx) as [SHW7 _].
pose proof (OBL_PFRT _ _ _ _ _ _ _ HP) as RT.
pose proof (bv_unsigned_in_range 8 ch1) as C1R; unfold bv_modulus in C1R; cbn in C1R.
pose proof (bv_unsigned_in_range 8 ch2) as C2R; unfold bv_modulus in C2R; cbn in C2R.
eapply evt_cut.
{ eapply (SNP_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m (Fr + 32) 7 (bv_unsigned ch1) (bv_unsigned ch2) 7%nat sb lo);
[ | reflexivity | exact C1R | reflexivity | exact C2R | reflexivity ].
unfold isnp_pre, SNP_STACK_A. rewrite ?unsigned_lit by lia.
split; [reflexivity|]. split; [reflexivity|]. split; [exact FFe|]. split; [exact RT|].
split; [lia|]. split; [lia|]. split; [exact ST|]. split; [lia|]. split; [unfold alloc_ceiling in OBL_PFLO; lia|]. split; [lia|].
split; [exact MI|]. split; [exact FR|]. split; [left; lia|].
split; [unfold dappJ; destruct HFapp; [left | right]; lia|].
intros k Hk. eapply (rng_okJ_sbuf7 m Fr k HFal); [lia | lia | unfold A_SB; exact SHW7 | lia]. }
intros ms3 (x0 & x1' & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F3 & fc3 & m3 & r & o & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & Hr & Ho & FFe3).
rewrite ?unsigned_lit in MU3, ST3 by lia.
assert (FS3 : fsaved F F3).
{ eapply fsaved_trans; [exact FS|]. intros k Hk. apply FREG3. cbn in Hk. repeat (destruct Hk as [<- | Hk]; [vm_compute; discriminate|]). destruct Hk. }
assert (OL : length o = 6%nat) by (rewrite Ho; reflexivity).
assert (INV3 : esc_inv_sbx 7 (o ++ [b8 0]) A e m3 md).
{ eapply (esc_inv_privA 7 7 A e m m3 md _ j0 j1 gj j8 sb j17 j8 (o ++ [b8 0]) j17); [exact INV1 | exact MU3 | exact WM3 | exact MI3 | | | | exact ST3].
- constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
- unfold escFF. change [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 90427); C8 (Z_to_bv 64 654992); CB 8 j8; CB 7 (o ++ [b8 0]); CB 17 j17]
with ([C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 90427); C8 (Z_to_bv 64 654992); CB 8 j8] ++ ([CB 7 (o ++ [b8 0])] ++ [CB 17 j17])).
apply rw_cells_app. split.
+ eapply (rw_cells_transport asegs _ m m3); [exact FFa | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
+ cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. apply rw_cells_app. split.
* replace (o ++ [b8 0]) with (o ++ Z_to_bv 8 0 :: skipn (S (length o)) sb); [exact FFe3|].
f_equal. f_equal. rewrite OL. apply skipn_all2. rewrite SBL. lia.
* cbn [cells_size csize Nat.add]. change (Fr + 32 + Z.of_nat 7) with (Fr + 32 + 7).
eapply (rw_cells_transport asegs _ m m3); [exact FFb | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
- eapply (rw_cells_transport asegs _ m m3); [exact SHx | exact MU3 | exact WM3 |]. unfold escSH. cbn [disjoint_from cells_size csize Nat.add].
assert (HH : Fr + 64 + 8 <= 2147450880 \/ 17594333495296 <= Fr) by (destruct HFapp as [H|H]; [left; exact H | right; exact H]).
clear - SHR HH LO ACR. revert SHR. generalize (Fr / 8 + 2147450880). intros shv SHR. unfold alloc_ceiling in *. lia. }
replace (ret_pc (Z_to_bv 64 655692)) with (Z_to_bv 64 655692) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply esc_ctrl_appA with (o := o); [exact INV3 | exact OL | exact FS3 | exact FRM3 | exact Hpos | exact He | exact IH | exact EX]. }
step. step. step. step.
rewrite (unsigned_lit cz) by lia. fold hi.
step. step. sh_norm. replace ((144160 + hi) / 8 + 2147450880) with 2147468900 by (clear - Hhi; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. if_lit.
step. rewrite (unsigned_lit cz) by lia. fold lo4. step.
step. step. sh_norm.
destruct (Z.lt_ge_cases lo4 8) as [L8 | G8].
- replace ((144160 + lo4) / 8 + 2147450880) with 2147468900 by (clear - Hlo4 L8; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. change (zxb ch1) with (Z_to_bv 64 (bv_unsigned ch1)). step. if_lit.
step. change (zxb ch2) with (Z_to_bv 64 (bv_unsigned ch2)).
step. step. step. step. fold_mkR. exact SNPK.
- replace ((144160 + lo4) / 8 + 2147450880) with 2147468901 by (clear - Hlo4 G8; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. change (zxb ch1) with (Z_to_bv 64 (bv_unsigned ch1)). step. if_lit.
step. change (zxb ch2) with (Z_to_bv 64 (bv_unsigned ch2)).
step. step. step. step. fold_mkR. exact SNPK.
Qed.

Lemma esc_iter_ctrlA :
forall (x1 t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 (wz start) a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc C32 CN IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a0' a1' a3'.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (cz := bv_unsigned c) in *. clearbody cz.
assert (MB0 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ESC_MASK) ≫ (bv_unsigned (Z_to_bv 64 cz) mod 64)))) 1) = Z_to_bv 64 0).
{ assert (C : cz = 0 \/ cz = 1 \/ cz = 2 \/ cz = 3 \/ cz = 4 \/ cz = 5 \/ cz = 6 \/ cz = 7 \/ cz = 11 \/ cz = 14 \/ cz = 15 \/ cz = 16 \/ cz = 17 \/ cz = 18 \/
cz = 19 \/ cz = 20 \/ cz = 21 \/ cz = 22 \/ cz = 23 \/ cz = 24 \/ cz = 25 \/ cz = 26 \/ cz = 27 \/ cz = 28 \/ cz = 29 \/ cz = 30 \/ cz = 31)
by (cbn in CN; lia).
repeat (destruct C as [-> | C]; [apply bv_eq; vm_compute; reflexivity|]). subst cz. apply bv_eq; vm_compute; reflexivity. }
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, SHx. unfold escLoc in LOC. unfold escSH in SHx.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & _). rewrite fr_size_0 in HFc. unfold alloc_ceiling in HFc.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_falsex. step. step. rewrite MB0. clear MB0.
step. if_lit. step. step. if_falsex. step. step. if_falsex.
step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (INV7 : esc_invx 7 A e m1 md) by (eapply (esc_inv_shA 248 7 A e m m1 md INV MU WM MI1); exact SHx).
destruct (Z.lt_ge_cases start pos) as [LT | GE].
-
step. if_falsex.
step. step.
rewrite (unsigned_lit pos), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. step. fold_mkR.
pose proof (esc_srcA _ _ _ _ _ INV7) as SRC1.
pose proof INV7 as (j0' & j1' & gj' & j8' & sb' & j17' & INV17).
pose proof INV17 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & _).
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 7);
[ exact INV7
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC1 | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP1 | right; right; exact INs | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_ctrl_hexA; [exact INV' | exact FS' | exact FR' | lia | lia | lia | exact IH | exact EX].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_ctrl_hexA; [exact INV7 | exact FS | exact FR | lia | lia | lia | exact IH | exact EX].
Qed.
End Esc.
End RC__1.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QmZZ QPZI QYIF QgoP Qekr QJZd Q2y2 QOmG Q63E Qt1H QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn. Import QPZI.Mq4.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 QsKa.Mq4 QlKV.Mq5 Q9O6.Mq0 Qekr.Mq0 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import Q2y2.
Import QOmG Qw5U.Mq1 Ql4f.Mq0 Q63E.Mq0 Qt1H.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo4.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

Section Ctx.
Variables (sp0 : word) (sp1 lo Fr : Z) (LB0 LM : list blk) (m0 : word -> option byte) (md0 : config) (F0 : bvmap 5 word) (B0 : bud).
Variables (data0 size : Z) (payload : list byte).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp1 - (2^20 - 144).
Hypothesis SPA1 : sp1 mod 32 = 0.
Hypothesis SP10 : sp1 + 32 <= bv_unsigned sp0.
Hypothesis HT : bv_unsigned sp0 + 32 <= hiA_top A4L HIx.
Hypothesis HBOT : hiA_bot A4L HIx <= lo.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DCE : data0 + size <= alloc_ceiling.
Hypothesis INB : size = 0 \/ In (data0, size) LB0.
Hypothesis FRAL : Fr mod 256 = 0.
Hypothesis FRLO : 6574080 <= Fr.
Hypothesis FRHI : Fr + 256 <= alloc_ceiling.
Hypothesis FRAPP : Fr + 256 + 8 <= A_SB \/ A_HMB <= Fr.
Variables (p : Z) (s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.
Variable wtx : Z.
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0.

Notation HINVAc := (HINVA sp0 sp1 lo Fr LB0 LM m0 md0 F0 data0 size).
Notation hstateAc := (hstateA sp0 sp1 Fr p s11).
Notation XT := (xtgt_A (bv_unsigned sp0)).
Let HINVA_callc := HINVA_call HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let OWNc := own_writesA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let GAOc := GA_jo_own HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.
Let FSLc := fslot_evidenceA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP.

#[using="CtxAll"] Lemma HINVA_callD : forall shb m m' md md' (A : ASA A4L HIx) B F F' fc fc' ptr rem data LBh LBx (qv : word),
HINVAc shb m md F fc ptr rem data -> HEAPAx A LBh LM [(Fr, 2)] B m md -> incl LB0 LBx -> incl LBx LBh ->
heap_presxDA (Fr + 224) (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)]) sp1 m m' ->
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> frm0 fc' ->
stk asegs m' lo sp1 -> lh_globA m' -> rw_cells asegs m' (Fr + 224) [C8 qv] ->
HINVAc shb m' md' F' fc' ptr rem data.
Proof.
intros shb m m' md md' A B F F' fc fc' ptr rem data LBh LBx qv
(PX & VM & FS & FRM & LOC & LCK & G & ST & [j8 SL] & FD & [fj FF] & FSH & LSH & BY & L & P0 & P1 & P2) HP Hi Hi2 HPD VM' FS' FRM' ST' LHG' DC'.
pose proof alloc_ceiling_range as ACR.
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
assert (INFR : In (Fr, 248) (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
assert (INSH : In (Fr / 8 + 2147450880, 32) (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)])) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.

assert (NOTD : forall a, client_addrx A4H XT (LB0 ++ LM) (sp1 + 32) a -> ~ (Fr + 224 <= a < Fr + 224 + 8)).
{ intros a [Ha | [[Ha _] | (b & Hb & Hr)]] HD.
- lia.
- pose proof (hl_static_in_img A4L a Ha) as Hi'. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi'. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
assert (Hb' : In (ba, bn) (LBh ++ LM)) by (apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply Hi2; apply Hi; exact Hb | right; exact Hb]).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hb') as DF. rewrite Q1Ey.fr_size_2 in DF. lia. }
assert (EQ : forall a, 0 <= a < 2^64 -> client_addrx A4H (hl_volatile A4H) (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)]) sp1 a -> ~ (Fr + 224 <= a < Fr + 224 + 8) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) by (intros a Ha Hc Hd; exact (HPD a Ha Hc Hd)).
assert (LOCcs : forall a, 6434400 - 48 <= a < 6434400 - 48 + 8 -> hl_client_static A4H a /\ ~ hl_volatile A4H a).
{ intros a Ha. cbn [hl_client_static hl_volatile A4H]. unfold a4_client_static, a4_volatile. lia. }
assert (LCKcs : forall a, 0x6431d0 <= a < 0x6431d0 + 4 -> hl_client_static A4H a /\ ~ hl_volatile A4H a).
{ intros a Ha. cbn [hl_client_static hl_volatile A4H]. unfold a4_client_static, a4_volatile. lia. }
pose proof (rw_cells_bound _ _ _ _ LOC) as LB1. pose proof (rw_cells_bound _ _ _ _ LCK) as LB2. pose proof (rw_cells_bound _ _ _ _ SL) as LB3.
pose proof (rw_cells_bound _ _ _ _ FD) as LB4. pose proof (rw_cells_bound _ _ _ _ FF) as LB5. pose proof (rw_cells_bound _ _ _ _ FSH) as LB6.
cbn [cells_size csize Nat.add] in LB1, LB2, LB3, LB4, LB5. rewrite cells_size_C1, LSH in LB6.
unfold HINVA. split.
{ eapply heap_presx_trans; [exact PX|]. intros a Ha Hc. apply (EQ a Ha); [| exact (NOTD a Hc)].
destruct Hc as [Hc | [[Hc Hx] | (b & Hb & Hr)]]; [left; lia | right; left; split; [exact Hc | intros V; apply Hx; left; exact V] | right; right].
exists b. split; [| exact Hr]. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hi; exact Hb | right; apply in_or_app; left; exact Hb]. }
split; [eapply model_vm_only_trans; [exact VM | exact VM']|]. split; [eapply fsaved_trans; [exact FS | exact FS']|]. split; [exact FRM'|].
split. { eapply rw_cells_pointwiseA; [exact LOC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold T_LOCCELL_A, A_TP in Ha. apply (EQ a); [lia | right; left; apply LOCcs; lia | lia]. }
split. { eapply rw_cells_pointwiseA; [exact LCK|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. unfold T_LOCALE_LOCK_A in Ha. apply (EQ a); [lia | right; left; apply LCKcs; lia | lia]. }
split. { eapply GA_jo_pointwise; [exact G | exact LHG' |]. intros a Ha.
refine (proj1 (EQ a _ _ _)); [lia | right; left; cbn [hl_client_static hl_volatile A4H]; unfold a4_client_static, a4_volatile; lia | lia]. }
split; [exact ST'|].
split. { exists j8. eapply rw_cells_pointwiseA; [exact SL|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | left; lia | lia]. }
split. { eapply rw_cells_pointwiseA; [exact FD|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | left; lia | lia]. }
split.
{ destruct (rw_cells_CB_cut asegs _ _ _ _ 224 FF ltac:(lia)) as [FA FB']. change (Z.of_nat 224) with 224 in FB'. change (248 - 224)%nat with 24%nat in FB'.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 FB' ltac:(lia)) as [_ FB]. change (Z.of_nat 8) with 8 in FB. change (24 - 8)%nat with 16%nat in FB. replace (Fr + 224 + 8) with (Fr + 232) in FB by lia.
assert (FA' : rw_cells asegs m' Fr [CB 224 (firstn 224 fj)]).
{ eapply rw_cells_pointwiseA; [exact FA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 248); split; [exact INFR | cbn; lia] | lia]. }
assert (FBm : rw_cells asegs m' (Fr + 232) [CB 16 (skipn 8 (skipn 224 fj))]).
{ eapply rw_cells_pointwiseA; [exact FB|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (EQ a); [lia | right; right; exists (Fr, 248); split; [exact INFR | cbn; lia] | lia]. }
assert (X1 : rw_cells asegs m' (Fr + 224) ([C8 qv] ++ [CB 16 (skipn 8 (skipn 224 fj))])) by (apply (proj2 (rw_cells_app asegs m' (Fr + 224) _ _)); split; [exact DC' | cbn [cells_size csize Nat.add]; replace (Fr + 224 + Z.of_nat 8) with (Fr + 232) by lia; exact FBm]).
assert (X3 : rw_cells asegs m' Fr ([CB 224 (firstn 224 fj)] ++ ([C8 qv] ++ [CB 16 (skipn 8 (skipn 224 fj))]))) by (apply (proj2 (rw_cells_app asegs m' Fr _ _)); split; [exact FA' | cbn [cells_size csize Nat.add]; change (Z.of_nat 224) with 224; exact X1]).
lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m' Fr ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. exact X3. }
split. { eapply rw_cells_pointwiseA; [exact FSH|]. intros a Ha. rewrite cells_size_C1, LSH in Ha. apply (EQ a); [lia | right; right; exists (Fr / 8 + 2147450880, 32); split; [exact INSH | cbn; lia] | clear - Ha FRAPPu FRLO FRHI ACR; Z.div_mod_to_equations; lia]. }
split; [exact LSH|].
split. { eapply (window_bytesG LB0 data0 size); [exact INB | exact BY | exact L | exact P1 | exact P2 |].
intros a Ha (b & Hb & Hr). apply (EQ a Ha).
- right; right. exists b. split; [apply in_or_app; left; apply Hi; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (in_or_app _ _ _ (or_introl (Hi2 _ (Hi _ Hb))))) as DF. rewrite Q1Ey.fr_size_2 in DF. lia. }
repeat split; assumption.
Qed.
Lemma sp1_16t : sp1 mod 16 = 0.
Proof using SPA1. clear - SPA1. Z.div_mod_to_equations. lia. Qed.

Definition put_any_costB (d : jroot) (DBS : list blk) : Z :=
match d with JRnull => 0 | JRtree _ => 512 * Z.of_nat (length DBS) | _ => JO_PUTX_COSTB_A end.
Definition put_any_costD (d : jroot) : Z := match d with JRdblx _ | JRstrx => JO_PUTX_COSTD_A | _ => 0 end.

#[using="CtxAll CA"] Lemma put_anyA : forall (ret : Z) (d : jroot) (q : Z) m md (A : ASA A4L HIx) B (DBS LBx : list blk)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
0 <= ret < 2^64 -> ret mod 2 = 0 ->
HEAPAx A (DBS ++ LBx) LM [(Fr, 2)] B m md -> jroot_rep A4H A4F d m DBS q ->
stk asegs m lo sp1 ->
put_any_costB d DBS <= bB B -> put_any_costD d <= bD B ->
(forall m' md' (A' : ASA A4L HIx) B' F' fc' (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
model_vm_only (cfg_model md) (cfg_model md') -> fsaved F F' -> (frm0 fc -> frm0 fc') -> stk asegs m' lo sp1 ->
heap_pres A4H (LBx ++ LM ++ fr_ivs A4L [(Fr, 2)]) sp1 m m' -> HEAPAx A' LBx LM [(Fr, 2)] B' m' md' ->
bB B - put_any_costB d DBS <= bB B' -> bD B - put_any_costD d <= bD B' ->
AJ5 A4L HIx A' T md' (hstateAc (Z_to_bv 64 (-1)) (Z_to_bv 64 ret) gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F' ret fc' m')) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) (Z_to_bv 64 ret) gp t0 t1 t2 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F put_entry_A fc m).
Proof.
intros ret d q m md A B DBS LBx gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc Hret Hret2 HP RR ST CBp CDp KQ.
pose proof sp1_16t as SP16. pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP) as (errv & ERR). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR.
unfold hstateA.
assert (TREE : forall s : option jshape, put_pre A4H A4F s m DBS q 1 -> put_costA s 1 DBS <= put_any_costB d DBS -> put_any_costD d = 0 ->
AJ5 A4L HIx A T md
(MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 (Z_to_bv 64 sp1) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 Fr) (Z_to_bv 64 (Fr + 160)) (Z_to_bv 64 p) (Z_to_bv 64 (Fr + 224)) (Z_to_bv 64 (Fr + 96)) (Z_to_bv 64 (Fr / 8 + 2147450880))
(Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-1)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry_A) fc None m (seg_rom asegs))).
{ intros s PRE CLE CD0. pose proof (ca_PUT _ _ _ _ _ _ _ CA) as PU. unfold put_stmt_A, put_stmtA in PU.
eapply PU with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 2)]) (B := B) (s := s) (lo := lo) (rc := 1) (errv := errv);
[ exact HP | exact PRE | reflexivity | rewrite unsigned_lit by lia; exact ST | exact LO
| rewrite unsigned_lit by lia; unfold put_stk_A; lia | rewrite unsigned_lit by lia; exact SP16
| rewrite unsigned_lit by lia; lia | exact ERR | reflexivity | rewrite unsigned_lit by lia; exact Hret2 | lia |].
intros ms' md' A' (m' & r' & B' & RS & VM' & ST' & HPR' & ERR' & CHB & CHD & OUT).
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
destruct OUT as [[_ HP'] | (s' & _ & Hrc & _)]; [| lia].
unfold hstateA in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia]. }
destruct d as [|s|tojs|].
- destruct RR as [-> ->]. apply (TREE None); [split; reflexivity | cbn; lia | reflexivity].
- destruct RR as [Hq J]. apply (TREE (Some s)); [split; [exact Hq|]; split; [lia | exact J] | cbn [put_costA put_any_costB]; change (1 =? 1) with true; cbv iota; lia | reflexivity].
- pose proof (ca_PUTX _ _ _ _ _ _ _ CA) as PX. unfold jo_put_xleaf_A_stmt in PX. cbn [put_any_costB put_any_costD] in CBp, CDp, KQ.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 2)]) (B := B) (r := JRdblx tojs) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_A; lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | exact CBp | exact CDp | reflexivity |].
intros ms' md' m' rv A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] _ ERRx HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold hstateA in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia].
- pose proof (ca_PUTX _ _ _ _ _ _ _ CA) as PX. unfold jo_put_xleaf_A_stmt in PX. cbn [put_any_costB put_any_costD] in CBp, CDp, KQ.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (FRS := [(Fr, 2)]) (B := B) (r := JRstrx) (lo := lo) (errv := errv);
[ split; [exact HP|]; rewrite unsigned_lit by lia;
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_A; lia|]; split; [exact SP16|]; split; [lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | exact CBp | exact CDp | reflexivity |].
intros ms' md' m' rv A' B' (RS & VM' & ST' & HPR' & [errv' ERR']) [CHB CHD] _ ERRx HP'.
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
rewrite unsigned_lit in ST', HPR' by lia.
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
unfold hstateA in KQ. eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact HP' | lia | lia].
Qed.
Notation SINVAc := (SINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p wtx).

Lemma RTC_SCF : forall A LB LM' FR B m md, HEAPAx A LB LM' FR B m md -> bytes_at asegs m 0xe6a68 (le8 (Z_to_bv 64 0x9edbc)).
Proof.
intros A LB LM' FR B m md HP. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
repeat (first [left; reflexivity | right]).
Qed.

Definition SHB3D : list byte := map (Z_to_bv 8)
[0xf1;0xf1;0xf1;0xf1; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0xf8;0xf8;0xf8;0xf2; 0xf2;0xf2;0xf2;0xf2; 0;0;0;0xf2; 0xf2;0xf2;0xf2;0xf2; 0;0xf3;0xf3;0xf3].

Definition KTA (sbf sdf : Z) : Prop :=
forall m' md' (A' : ASA A4L HIx) B' F' fc' LKf (x1 gp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x t3 t4 t5 t6 : word),
heap_presx A4H XT (LB0 ++ LM) (sp1 + 32) m0 m' -> model_vm_only (cfg_model md0) (cfg_model md') -> fsaved F0 F' -> frm0 fc' ->
rw_cells asegs m' T_LOCCELL_A [C8 (Z_to_bv 64 T_GLOBLOC_A)] -> rw_cells asegs m' T_LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA_jo m' ->
stk asegs m' lo sp1 -> (exists j32, rw_cells asegs m' sp1 [CB 32 j32]) ->
HEAPAx A' (LKf ++ LB0) LM [] B' m' md' -> bB B0 - sbf <= bB B' -> bD B0 - sdf <= bD B' ->
AJ5 A4L HIx A' T md'
(MS (mkR x1 (Z_to_bv 64 sp1) gp (Z_to_bv 64 A_TP) t0 t1 t2 sp0 s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x920b0) fc' None m' (seg_rom asegs)).
#[using="CtxAll HINVA_callc OWNc GAOc FSLc CA"] Lemma seg_tailA : forall m md (A : ASA A4L HIx) B F fc ptr rem data r BS LK sb sd (wdc KPC KPR : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVAc SHB3 m md A B F fc ptr rem data r BS LK sb sd ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells asegs m (Fr + 160) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
root_wA r m BS p wdc -> 0 <= wdc < 2^28 ->
0 <= dcB wdc -> 0 <= dcD wdc -> 0 <= KPC -> 0 <= KPR ->
(forall d CBS mX q, copy_ofA r d CBS wdc -> jroot_rep A4H A4F d mX CBS q -> put_any_costB d CBS <= KPC) ->
(forall BSx mX, jroot_rep A4H A4F r mX BSx p -> put_any_costB r BSx <= KPR) ->
sb + dcB wdc + KPC + KPR <= TGT_BB_A_jo -> sd + dcD wdc + 4 <= TGT_BD_A_jo ->
KTA (sb + dcB wdc + KPC + KPR) (sd + dcD wdc + 4) ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-1)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91f34 fc m).
Proof.
intros m md A B F fc ptr rem data r BS LK sb sd wdc KPC KPR x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI (n3 & sj23 & Hn3 & STR3) RWA WDC DCB0 DCD0 KPC0 KPR0 PCC PCR CBT CDT K.
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & [j8 SL] & FD & [fj FF] & FSH & LSH & BY & L & P0 & P1 & P2) & HP & RR & RD & BB & BD & RWm).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (bv_unsigned_in_range 64 sp0) as SP0R. change (bv_modulus 64) with (2^64) in SP0R.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC, LCK. unfold SHB3 in FSH. cbn [map] in FSH.
assert (BYm : bytes_at asegs m ptr data /\ True) by (split; [exact BY | exact I]). clear BY.
pose proof FRAPP as FRAPPu. unfold A_SB, A_HMB in FRAPPu.
pose proof (RTC_SCF _ _ _ _ _ _ _ HP) as SCF. apply QsKa.Mq1.ro_C8_of_bytes_at in SCF.
unfold hstateA, A_TP.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - FRLO FRHI ACR; Z.div_mod_to_equations; lia).
assert (WOK : Forall (own_iv sp1 lo Fr) [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)]).
{ unfold own_iv, sh. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
reenterA asegs A4L HIx asegs_wx HP.
stepz. stepz. step. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
assert (INCL : incl LB0 (BS ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWNc A (BS ++ LK ++ LB0) B m m2 md _ HP INCL MU WM MI2 WOK) as (HP2 & HPX2 & AG2).
assert (RR2 : jroot_rep A4H A4F r m2 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m m2 BS ((BS ++ LK ++ LB0) ++ LM)); [exact RR | exact AG2 | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (GA2 : GA_jo m2) by (exact (GAOc m m2 _ G MU WM WOK)).

assert (RWA2 : root_wA r m2 BS p wdc).
{ destruct r as [|shq|tjq|]; cbn [root_wA] in RWA |- *; try exact RWA.
destruct RWA as (Lx & (lenx & BY40 & LR & LA) & LW). exists Lx. split; [| exact LW]. exists lenx. split; [| split; [exact LR | exact LA]].
eapply (bytes_at_agree asegs _ m m2); [exact BY40 | exact AG2 |].
destruct RR as (Hp0 & pb & PBS & DBS & cap & len' & str' & EBS & _ & Hcap & _).
exists p, (48 + cap). split; [rewrite EBS; apply in_or_app; left; apply in_or_app; left; left; reflexivity|].
rewrite length_le8. cbn. lia. }
assert (UND2 : unpoisoned asegs m2 A_SB (Fr + 224) 8).
{ lazymatch type of FSH with rw_cells _ _ _ ?cs => let l := c1_bytes cs in
exact (FSLc m2 l 28%nat 29%nat FSH eq_refl ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) end. }

pose proof FF as FFv.
lazymatch type of FFv with rw_cells _ _ _ [?c0; ?c1; ?c2] => change [c0; c1; c2] with ([c0] ++ ([c1] ++ [c2])) in FFv end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFv as [_ FFv]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FFv as [DC2 _].
cbn [cells_size csize Nat.add] in DC2. change (Z.of_nat 224) with 224 in DC2.
assert (FJ2 : exists fj2, rw_cells asegs m2 Fr [CB 248 fj2]).
{ pose proof FF as X3. lazymatch type of X3 with rw_cells _ _ _ ?cs => change (rw_cells asegs m2 Fr ([] ++ cs ++ [])) in X3 end.
apply rw_cells_merge in X3. cbn [app] in X3.
lazymatch type of X3 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X3 end. exact X3. }
assert (BY2 : bytes_at asegs m2 ptr data).
{ eapply (window_bytesG (BS ++ LK ++ LB0) data0 size); [destruct INB as [Z0|I1]; [left; exact Z0 | right; apply INCL; exact I1] | exact (proj1 BYm) | exact L | exact P1 | exact P2 |].
intros a Ha (b & Hb & Hr). apply (AG2 a Ha). exists b. split; [apply in_or_app; left; exact Hb | exact Hr]. }
lazymatch goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
assert (HI2 : HINVAc SHB3D m2 md F fc ptr rem data).
{ unfold HINVA. split; [eapply heap_presx_trans; [exact PX | exact HPX2]|]. split; [exact VM|]. split; [exact FS|]. split; [exact FRM|].
split; [exact LOC|]. split; [exact LCK|]. split; [exact GA2|]. split; [exact ST2|]. split; [exists j8; exact SL|]. split; [exact FD|].
split; [exact FJ2|]. split; [exact FSH|]. split; [reflexivity|]. split; [exact BY2|]. repeat split; assumption. }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP2) as (errv2 & ERR2). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR2. unfold A_TP in ERR2.
assert (RD0 : 0 <= rdepth r) by (destruct r as [|s| |]; cbn [rdepth]; [lia | apply Q0Ek.sdepth_nonneg | lia | lia]).
evt_done5.
pose proof (ca_DEEP _ _ _ _ _ _ _ CA) as DC. unfold jo_deep_copy_A_stmt, JO_DEEP_COPY_A, JO_SHALLOW_COPY_A, JO_DEEP_STK0_A, JO_DEEP_STK1_A in DC.
eapply DC with (A := A) (BS := BS) (LB := LK ++ LB0) (FRS := [(Fr, 2)]) (B := B) (lo := lo) (p := p) (D := Fr + 224) (r := r) (errv := errv2) (w := wdc).
- split; [exact HP2|]. rewrite unsigned_lit by lia.
split; [exact ST2|]. split; [exact LO|]. split; [lia|]. split; [exact sp1_16t|]. split; [lia|].
split; [exact ERR2|]. split; [reflexivity | vm_compute; reflexivity].
- rewrite unsigned_lit by lia. exact SPA1.
- exact (proj1 GA2).
- exact RR2.
- exact DC2.
- exists Fr, 2. split; [left; reflexivity|]. rewrite Q1Ey.fr_size_2. lia.
- exact UND2.
- clear - FRAL. Z.div_mod_to_equations. lia.
- cbn [length]. lia.
- exact RWA2.
- lia.
- unfold TGT_BB_A_jo in *. lia.
- unfold TGT_BD_A_jo in *. lia.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
- idtac.
intros ms3 md3 m3 rv3 A3 B3 (RS3 & VM3 & ST3 & HPD3 & [errv3 ERR3]) [CHB3 CHD3] LHG3 RR3 OUT3.
destruct RS3 as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F3 & fc3 & -> & FS3 & FRM3).
rewrite unsigned_lit in ST3, HPD3 by lia.
replace (ret_pc (Z_to_bv 64 0x91f50)) with (Z_to_bv 64 0x91f50 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (STR4 : rw_cells asegs m3 (Fr + 160) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPD3 a); [lia | | lia].
right; right. exists (Fr, 248). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }

assert (OUT : exists (d : jroot) (q : Z) (CBS REM : list blk),
(copy_ofA r d CBS wdc \/ d = JRnull) /\ rw_cells asegs m3 (Fr + 224) [C8 (Z_to_bv 64 q)] /\ jroot_rep A4H A4F d m3 CBS q /\
HEAPAx A3 (CBS ++ BS ++ REM ++ LK ++ LB0) LM [(Fr, 2)] B3 m3 md3).
{ destruct OUT3 as [(_ & d & q & CBS & REM & CO & Hq & DC3 & RRd & HP3) | (_ & REM & DC3 & HP3)].
- exists d, q, CBS, REM. split; [left; exact CO|]. split; [exact DC3|]. split; [exact RRd|].
eapply (heapA_perm A4L HIx); [exact HP3 | | apply Permutation.Permutation_refl | apply Permutation.Permutation_refl].
rewrite !app_assoc. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_tail. apply Permutation.Permutation_app_comm.
- exists JRnull, 0, (@nil blk), REM. split; [right; reflexivity|]. split; [exact DC3|]. split; [split; reflexivity|]. cbn [app]. exact HP3. }
destruct OUT as (d & q & CBS & REM & COd & DC3 & RRd & HP3).
assert (HI3 : HINVAc SHB3D m3 md3 F3 fc3 ptr rem data).
{ eapply (HINVA_callD SHB3D m2 m3 md md3 A B F F3 fc fc3 ptr rem data (BS ++ LK ++ LB0) (LK ++ LB0) (Z_to_bv 64 q));
[ exact HI2 | exact HP2 | intros b Hb; apply in_or_app; right; exact Hb | intros b Hb; apply in_or_app; right; exact Hb
| exact HPD3 | exact VM3 | exact FS3 | exact (FRM3 FRM) | exact ST3 | exact LHG3 | exact DC3 ]. }
clear HI2 HP2 RR2 GA2 UND2 DC2 FJ2 BY2 STR3 MU WM MI2 FF FSH LOC LCK SL FD ST2 ERR2 SCF HPX2 AG2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP3. change (hl_segs A4H) with asegs.
step. step.

evt_done5.
eapply (put_anyA 0x91f58 d q m3 md3 A3 B3 CBS (BS ++ REM ++ LK ++ LB0)); [lia | reflexivity | exact HP3 | exact RRd | exact ST3 | | |].
{ destruct COd as [CO | ->]; [pose proof (PCC d CBS m3 q CO RRd) | cbn [put_any_costB]]; unfold TGT_BB_A_jo in *; lia. }
{ destruct d; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A, TGT_BD_A_jo in *; lia. }
intros m4 md4 Ay4 B4 F4 fc4 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 VM4 FS4 FRM4 ST4 HPR4 HP4 CHB4 CHD4.
assert (HI4 : HINVAc SHB3D m4 md4 F4 fc4 ptr rem data).
{ eapply HINVA_callc; [exact HI3 | exact HPR4 | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb
| exact VM4 | exact FS4 | apply FRM4; exact (proj1 (proj2 (proj2 (proj2 HI3)))) | exact ST4]. }
assert (RR4 : jroot_rep A4H A4F r m4 BS p).
{ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F r m3 m4 BS BS); [exact RR3 | | intros b Hb; exact Hb].
eapply (agree_of_heap_pres asegs A4H); [exact HPR4 | reflexivity | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]. }
assert (STR5 : rw_cells asegs m4 (Fr + 160) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR4|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPR4 a); [lia|].
right; right. exists (Fr, 248). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }
assert (PCD : put_any_costD d <= 2) by (destruct d; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia).
assert (PCB : put_any_costB d CBS <= KPC) by (destruct COd as [CO | ->]; [exact (PCC d CBS m3 q CO RRd) | cbn [put_any_costB]; lia]).
clear HI3 RR3 STR4 RRd HP3 DC3 MI3 MU WM OUT3 HPD3 ERR3 LHG3 ST3.
unfold hstateA, A_TP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4. change (hl_segs A4L) with asegs in MI4.
pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP4. change (hl_segs A4H) with asegs.
step. step.

evt_done5.
eapply (put_anyA 0x91f60 r p m4 md4 Ay4 B4 BS (REM ++ LK ++ LB0)); [lia | reflexivity | exact HP4 | exact RR4 | exact ST4 | | |].
{ pose proof (PCR BS m4 RR4). unfold TGT_BB_A_jo in *. lia. }
{ assert (put_any_costD r <= 2) by (destruct r; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia). unfold TGT_BD_A_jo in *. lia. }
intros m5 md5 Ay5 B5 F5 fc5 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 VM5 FS5 FRM5 ST5 HPR5 HP5 CHB5 CHD5.
assert (HI5 : HINVAc SHB3D m5 md5 F5 fc5 ptr rem data).
{ eapply HINVA_callc; [exact HI4 | exact HPR5 | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb
| exact VM5 | exact FS5 | apply FRM5; exact (proj1 (proj2 (proj2 (proj2 HI4)))) | exact ST5]. }
assert (STR6 : rw_cells asegs m5 (Fr + 160) [C1 (Z_to_bv 8 (2 * n3)); CB 23 sj23]).
{ eapply rw_cells_pointwiseA; [exact STR5|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply (HPR5 a); [lia|].
right; right. exists (Fr, 248). split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity | cbn; lia]. }
assert (PCRB : put_any_costB r BS <= KPR) by (exact (PCR BS m4 RR4)).
assert (PCRD : put_any_costD r <= 2) by (destruct r; cbn [put_any_costD]; unfold JO_PUTX_COSTD_A; lia).

pose proof HI5 as (PX5 & VM5' & FS5' & FRM5' & LOC5 & LCK5 & G5 & _ & [j85 SL5] & FD5 & [fj5 FF5] & FSH5 & _ & _).
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC5, LCK5. unfold SHB3D in FSH5. cbn [map] in FSH5. fold sh in FSH5.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 FF5 ltac:(lia)) as [FM5 _]. clear FF5.
clear HI5 HI4 RR4 STR5 MU WM MI4 HP4.
unfold hstateA, A_TP.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (munch_refl [(lo, sp1 + 32); (Fr, Fr + 248); (sh, sh + 32)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
change (hl_segs A4H) with asegs in *.
reenterA asegs A4L HIx asegs_wx HP5. change (hl_segs A4H) with asegs.
fold sh.
step. stepz.
step. step. rewrite short_flag0A by lia. step. if_true.
do 3 stepz.
step. step. stepz.
step. if_falsex.
step. do 32 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
lazymatch goal with H : mem_inv asegs m6 |- _ => rename H into MI6 end.
assert (INCL5 : incl LB0 (REM ++ LK ++ LB0)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
destruct (OWNc Ay5 (REM ++ LK ++ LB0) B5 m5 m6 md5 _ HP5 INCL5 MU WM MI6 WOK) as (HP6 & HPX6 & AG6).
assert (GA6 : GA_jo m6) by (exact (GAOc m5 m6 _ G5 MU WM WOK)).
assert (INF : In (Fr, 2) [(Fr, 2)]) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP6 INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite Q1Ey.fr_size_2 in FPB. replace (Fr + 256 - 8) with (Fr + 248) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 2) (fp := fp) (rX := Z_to_bv 5 10);
[exact HP6 | exact INF | rewrite Q1Ey.fr_size_2; replace (Fr + 256 - 8) with (Fr + 248) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] m6 m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs m6 m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MI6 y b). rewrite <- Hb. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [Lt|Ge]; [exact Lt | exfalso; apply FPnc; left; exact Ge]).
assert (FPNC0 : forall a, client_addr A4H (LB0 ++ LM) (sp1 + 32) a -> a <> fp).
{ intros a Hc ->. apply FPnc. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]]; [exfalso; lia | right; left; exact Hc | right; right].
exists b. split; [| exact Hr]. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply INCL5; exact Hb | right; exact Hb]. }
assert (HPX7 : heap_presx A4H XT (LB0 ++ LM) (sp1 + 32) m6 m7).
{ eapply (heap_presx_of_munch A4H XT (LB0 ++ LM) (sp1 + 32) [(fp, fp + 1)]); [exact MUr | exact WMr |].
intros a Ha Hc. cbn [outside]. pose proof (FPNC0 a Hc). split; [lia | exact I]. }
assert (FPst : ~ hl_client_static A4H fp) by (intros Hs; apply FPnc; right; left; exact Hs).
cbn [hl_client_static A4H] in FPst. unfold a4_client_static in FPst.
cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg.
apply (rw_cells_transport asegs [(fp, fp + 1)] m6 m7) in LOC5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m6 m7) in LCK5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m6 m7) in SL5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] m6 m7) in FD5; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; lia].
lazymatch goal with H : stk asegs m6 lo sp1 |- _ => rename H into ST6 end.
apply (stk_transport_disjoint asegs [(fp, fp + 1)] m6 m7) in ST6; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
assert (GA7 : GA_jo m7).
{ eapply GA_jo_munch; [exact GA6 | exact MUr | exact WMr |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
change (598056 + 4) with 598060.
clear FM5 FSH5 FPC STR6.
change (hl_segs A4L) with asegs.
reenterA asegs A4L HIx asegs_wx HP7. change (hl_segs A4H) with asegs.
step.
evt_done5.
unfold KTA in K. eapply (K m7 md7 A7 B5 F5 fc5 (REM ++ LK)).
+ eapply heap_presx_trans; [exact PX5 | eapply heap_presx_trans; [exact HPX6 | exact HPX7]].
+ eapply model_vm_only_trans; [exact VM5' | exact VM7].
+ exact FS5'.
+ exact FRM5'.
+ exact LOC5.
+ exact LCK5.
+ exact GA7.
+ exact ST6.
+ lazymatch type of SL5 with rw_cells _ _ _ [?c0; ?c1] => lazymatch type of FD5 with rw_cells _ _ _ [?c2; ?c3] =>
assert (X4 : rw_cells asegs m7 sp1 ([c0; c1] ++ [c2; c3])) by (apply (proj2 (rw_cells_app asegs m7 sp1 _ _)); split; [exact SL5 | cbn [cells_size csize Nat.add]; change (Z.of_nat 16) with 16; exact FD5]) end end.
cbn [app] in X4. lazymatch type of X4 with rw_cells _ _ _ ?cs => change (rw_cells asegs m7 sp1 ([] ++ cs ++ [])) in X4 end.
apply rw_cells_merge in X4. cbn [app] in X4.
lazymatch type of X4 with rw_cells _ _ _ [CB ?n ?b] => exists b; let v := eval vm_compute in n in change n with v in X4 end. exact X4.
+ rewrite <- app_assoc. exact HP7.
+ unfold TGT_BB_A_jo in *. lia.
+ unfold TGT_BD_A_jo in *. lia.
Qed.
End Ctx.
End AHarnJo4.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QkMG Qu4M QG8z Qdyh QLbz Q2Sr QIsM Qiiq QrQv QEUF QdGy QW22 QV7s QYZ0 Qpfz QlAE QMmN QQd3 QQdK QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QrQv.Mq2 QEUF QdGy.Mq2 QW22.Mq3 QdGy.Mq5 QV7s QYZ0.Mq3 QL3k.Mq0 Qpfz Q63E QlAE QlAE.Mq0 QMmN QQd3 QQdK.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq3 Q63E.Mq1 QV7s.Mq0 QnDr.Mq3 Qpfz.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma rank_ge1S : forall st ss, (1 <= rank st ss)%nat.
Proof. intros st ss. unfold rank, base_rank. repeat (destruct (zin _ _)); destruct (st =? ST_eatws); lia. Qed.
Lemma cur_st_lvlS : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st (ts_lvl ts l') = tl_st l'.
Proof. intros ts l l' Hl. unfold cur_st, ts_lvl; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.
Lemma cur_ss_lvlS : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> cur_ss (ts_lvl ts l') = tl_ss l'.
Proof. intros ts l l' Hl. unfold cur_ss, ts_lvl; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.
Lemma cur_st_ofS : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st ts = tl_st l.
Proof. intros ts l H. unfold cur_st. rewrite H. reflexivity. Qed.
Lemma cur_ss_ofS : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_ss ts = tl_ss l.
Proof. intros ts l H. unfold cur_ss. rewrite H. reflexivity. Qed.
Lemma mbase_lvlS : forall pf ts l', mbase pf (ts_lvl ts l') = mbase pf ts.
Proof. reflexivity. Qed.

Lemma PBS_lvl : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> PBS (ts_lvl ts l') = PBSst (tl_st l').
Proof. intros ts l l' Hl. unfold PBS. rewrite (cur_st_lvlS ts l l' Hl). reflexivity. Qed.
Lemma PBS_of : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> PBS ts = PBSst (tl_st l).
Proof. intros ts l Hl. unfold PBS. rewrite (cur_st_ofS ts l Hl). reflexivity. Qed.

Lemma tdepth_ok_lvl : forall ts l st' ss', tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l -> (t_depth ts <= 31)%nat ->
zin st' [ST_array_add; ST_ovadd] = false ->
tdepth_ok (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))).
Proof.
intros ts l st' ss' TD Hl Hd Hz. unfold ts_lvl. eapply tdepth_ok_upd; [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); lia | exact Hd | exact Hz].
Qed.

Lemma cur_st_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_st (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_st l'.
Proof. intros. unfold cur_st; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma cur_ss_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_ss (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_ss l'.
Proof. intros. unfold cur_ss; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma PBS_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
PBS (TST depth (lupd levels depth l') co pb pbs x o os obs) = PBSst (tl_st l').
Proof. intros. unfold PBS. rewrite (cur_st_upd _ _ l) by assumption. reflexivity. Qed.
Lemma NAO_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof.
intros depth levels l l' co pb pbs x o os obs Hl H. unfold NAO. rewrite (cur_st_upd _ _ l) by assumption. unfold EUS, zin in *. cbn [existsb] in *.
destruct (tl_st l' =? ST_array_add); [discriminate H|]. destruct (tl_st l' =? ST_ovadd); [discriminate H|]. destruct (tl_st l' =? ST_escape_unicode); [discriminate H|].
destruct (tl_st l' =? ST_esc_need_escape); [discriminate H|]. destruct (tl_st l' =? ST_esc_need_u); [discriminate H|]. reflexivity.
Qed.

Lemma NAO_upd2 : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = false -> zin (tl_st l') [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false ->
NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof. intros. apply NAO_plain; rewrite (cur_st_upd _ _ l) by assumption; assumption. Qed.

Lemma NAO_upd_eu : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = false -> SPV x = 0 -> UCSV x < 65536 -> NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof. intros. apply NAO_eu; [rewrite (cur_st_upd _ _ l) by assumption; assumption | assumption | assumption]. Qed.
Lemma SPOK_upd_plain : forall depth levels l l' co pb pbs x o os obs k, nth_error levels depth = Some l ->
zin (tl_st l') [ST_null; ST_boolean; ST_inf] = false -> SPOK (TST depth (lupd levels depth l') co pb pbs x o os obs) k.
Proof. intros. unfold SPOK. rewrite (cur_st_upd _ _ l) by assumption. intros HH. rewrite H0 in HH. discriminate HH. Qed.

Section PeSCases1.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_ofend : CASEx ST_ofend.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_ofend_A HIx GA GA_outside pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1); [exact STC | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | exact Hst | exact Hco | |].
-
intros m' a0' a1' a2' a3' C58 INV' PBK'.
change (Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
with (ts_lvl ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) in *.
set (l' := TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_ovalue Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros a1' a3' N58.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 10); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_osep : CASEx ST_osep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_osep_A HIx GA GA_outside pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1); [exact STC | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | exact Hst | exact Hco | |].
-
intros m' ss' a1' a2' a3' Hc INV' PBK'.
change (Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
with (ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) in *.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHA (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ lia.
+ split; [intros E; discriminate E | intros E; exfalso; destruct Hc as [[Hc _] | [Hc _]]; lia].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. subst l'. destruct Hc as [[_ ->] | [_ ->]]; pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ss' Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros a1' a3' N44 N125. unfold pe_msA.
pose proof (KE ts [] 11 m md A B cb nb pj errv) as KEx. unfold pe_msE in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_cstart : CASEx ST_comment_start.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_cstart_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | | |].
-
intros m' md' A' B' st' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hc INV' PBK' BK' FS' FRM'.
assert (Hst' : st' = ST_comment \/ st' = ST_comment_eol) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
eapply (IHB (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs'));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. cbn [tl_st]. destruct Hst' as [-> | ->]; discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; destruct Hst' as [-> | ->]; pbs_norm; pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
-
intros m' md' A' B' st' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hc INV' FS' FRM'.
assert (Hst' : st' = ST_comment \/ st' = ST_comment_eol) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
pose proof (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO
(ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) [] m' md' A' B' cb nb pj errv') as KEM.
unfold pe_msO in KEM. unfold pe_msA. eapply KEM; [apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
-
intros a1' a3' N42 N47. unfold pe_msA.
pose proof (KE ts [] 13 m md A B cb nb pj errv) as KEx. unfold pe_msE in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_cend : CASEx ST_comment_end.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_cend_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | |].
- intros m' md' A' B' st' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hc INV' PBK' BK' FS' FRM'.
assert (Hst' : st' = ST_eatws \/ st' = ST_comment) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
eapply (IHB (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. cbn [tl_st]. destruct Hst' as [-> | ->]; discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; destruct Hst' as [-> | ->]; pbs_norm; pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
- intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmemb_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_asep : CASEx ST_array_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_asep_A HIx GA GA_outside GA_pres SHRINK pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (bredo pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | | |].
-
intros m' ss' a1' a2' a3' Hc INV' PBK'.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHA (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ lia.
+ split; [intros E; discriminate E | intros E; exfalso; destruct Hc as [Hc _]; lia].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. subst l'. destruct Hc as [_ ->]; pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ss' Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| try (subst l'; destruct Hc as [_ ->]); bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| try (subst l'; destruct Hc as [_ ->]); bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a1' a2' a3' N44 N93. unfold pe_msA.
pose proof (KE ts [] 8 m md A B cb nb pj errv) as KEx. unfold pe_msE in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_aadd : CASEx ST_array_add.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst, (Qdyh.Mq0.lvl_mode_aadd (tl_ss l)) in Hmode. injection Hmode as <- <-.
assert (Hcs : exists kids, tl_cs l = Some (Sarr kids)) by (destruct (tl_cs l) as [s0|]; [destruct s0; cbn in CLS0; try contradiction; eexists; reflexivity | cbn in CLS0; contradiction]).
destruct Hcs as [kids Hcs].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 1280 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 1280)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (OBJV : pj_obj pj = Z_to_bv 64 (t_obj ts)) by (apply (proj1 OW); rewrite Est, Hst; reflexivity).
eapply (seg_aadd_A HIx GA GA_outside GA_pres AADD pf pa q LBc LM FRS payload me lo m md A B ts l kids cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 1280)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact OBJV | exact Hl | exact Hst | exact Hcs | |].
-
intros m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' INV' PBK' BK' JX' FS' FRM'.
assert (OBN : t_objs ts = None -> t_objbs ts = []).
{ pose proof INV as [_ (_ & _ & OBJ9 & _)]. rewrite Est, Hst in OBJ9. cbn in OBJ9. intros E9. rewrite E9 in OBJ9. exact (proj2 OBJ9). }
eapply (IHR (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl_obj in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, Hst in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_eatws ST_array_sep) with 2%nat. change (rank ST_array_add (tl_ss l)) with 3%nat in M. lia.
+ intros E. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_absorb (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Hst; reflexivity | cbn [t_objs]; rewrite Hcs; apply odep_absorb_arr | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_add _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 6 Hl);
[reflexivity | reflexivity | rewrite ?Hst; reflexivity | reflexivity | exact PBK | exact PBK' | lia | jl_dead
| intros w0 b Lw0 Eb; exact (lw_aadd l kids objs objbs cbs' _ _ w0 b Hcs Lw0 Eb OBN JX') | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, Hst by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co].
change (rank ST_eatws ST_array_sep) with 2%nat. change (rank ST_array_add (tl_ss l)) with 3%nat. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_comment : CASEx ST_comment.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_comment_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_comment_end (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmemc_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_set_co ts co') []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_ceol : CASEx ST_comment_eol.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_ceol_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmemc_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_set_co ts co') []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_ofs : CASEx ST_ofs.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
replace (pe_jtA ST_ofs) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_ofs_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1);
[exact STC | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | left; exact Hst | exact Hco | | |].
-
intros m' a0' a1' a2' a3' a4' C125 INV' PBK'.
set (l' := TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_finish Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros _. reflexivity.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' a0' a1' a2' a3' a4' Hq INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (tx_quote (t_x ts) cb)) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs (tx_quote x cb) obj objs objbs) B _ l ST_ofield (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co (tx_quote x cb)); [cbn [t_co]; lia | exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL. reflexivity.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a1' a2' a3' a4' N34 N39 N125.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 9); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_ofs2 : CASEx ST_ofs_after_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
replace (pe_jtA ST_ofs_after_sep) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_ofs_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1);
[exact STC | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | right; exact Hst | exact Hco | | |].
-
intros m' a0' a1' a2' a3' a4' C125 INV' PBK'.
set (l' := TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_finish Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros _. reflexivity.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' a0' a1' a2' a3' a4' Hq INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (tx_quote (t_x ts) cb)) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs (tx_quote x cb) obj objs objbs) B _ l ST_ofield (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co (tx_quote x cb)); [cbn [t_co]; lia | exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL. reflexivity.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a1' a2' a3' a4' N34 N39 N125.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 9); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.
End PeSCases1.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq6 QYZ0.Mq3 Q63E QMmN QV7s QMgr.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq5.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STC : PE_STATIC_A HIx pf pa lo.
Notation KOUTx := (KOUT_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0).
Hypothesis KO : KOUTx.

Local Ltac open_w STCx INVW :=
pose proof STCx as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
pose proof INVW as (CORE & BASE & _ & _);
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & _ & _ & _ & FR);
pose proof (proj1 BASE) as HP; clear BASE.

Lemma kerrst_of_kout_O :
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s10 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_ERRST x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s5 s7 s10 s11 t4 t6 F fc m).
Proof.
intros ts LK e m md A B cb nb pj errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s10 s11 t4 t6 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRST. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
stepz.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.

Lemma kerrlit_of_kout :
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 < e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md
(Q1Y6.Mq2.pe_msE pf pa APE_ERRLIT x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (pf_tk pf / 8 + 2147450882)) s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
intros ts LK e m md A B cb nb pj errv x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc INVW TD He FS FRM.
pose proof STC as STC'. open_w STC' INVW.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
revert STC' INVW KO. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC' INVW KO'.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(tk, tk + 72)] m) as MU.
pose proof (KO' (ts_set_err ts0 (Z_to_bv 64 e)) LK) as KOx. unfold pe_msO, APE_OUT in KOx. cbn [pf_tk pf_spf pa_sp0 pa_F] in KOx. clear KO'.
unfold pe_msA, pe_msO, pe_msE, APE_ERRLIT. cbn [pf_tk pf_spf pf_sb pf_lenr pa_sp0 pa_F]. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t.
reenterA asegs A4L HIx asegs_wx HP.
step.
stepz.
do 3 step.
step.
step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m mc, WMc : wmono asegs m mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _ |- _ =>
evt_done5;
pose proof (PE_INVW_A_tokw1 HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LBc LM FRS payload me lo m mc md A B ts0 LK
cb nb pj sv errv co (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) STC' INVW MUc WMc MIc TOKc ltac:(cbn [pf_len]; lia) eq_refl) as INV3
end end.
eapply KOx; [exact INV3 | apply tdepth_ok_set_err; exact TD | apply JOUT_set_err; lia | exact FS | exact FRM].
Qed.
End WithIface.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo QlCE QhHQ Q5Ki QGdd QcmL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd QdGy.Mq0 QcmL.Mq0 QsKa.Mq8 QrQv.Mq2 QV7s QdGy.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Hypothesis USE : uselocale_A_stmt.
Hypothesis FREEL : freelocale_A_stmt HIx.

Lemma frame_writes_okFS : forall A LB LM FR B m m' md W,
HEAPA A4L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top A4L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (forall x, fst iv <= x < snd iv -> hl_client_static A4H x)) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr A4H (LB ++ LM) alloc_ceiling a -> ~ hl_scratch A4L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns Hnf.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1. intros Hin.
destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | [(F & k & HF & HFr) | Hcs]]]].
- apply Hnc. left. lia.
- apply Hnc. right; right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
- apply Hnf. exists F, k. split; [exact HF|]. destruct HFr as [HFr | HFr]; [left | right]; lia.
- apply Hnc. right; left. exact (Hcs a Hin).
Qed.

Lemma own_frame_freshG : forall F0 (LBall LB0 LM : list blk) FRS B A m md,
HEAPA A4L HIx A LBall LM ((F0, 2) :: FRS) B m md -> incl LB0 LBall ->
~ In (F0, fr_size 2 - 8) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (shad A4L F0, fr_shadow_len 2) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros F0 LBall LB0 LM FRS B A m md HP Hincl.
assert (INF : In (F0, 2) ((F0, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBall ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hincl; exact Hb | right; exact Hb]. }
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- exact (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_frame _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
pose proof (fr_shadow_len_bnd kg Hkg). unfold fr_size in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK. lia.
- exact (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_shadow _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
rewrite (fr_size_shadow kg) in EK by lia. pose proof (fr_shadow_len_bnd kg Hkg).
unfold fr_shadow_len at 1 in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK.
assert (8 <= fr_shadow_len kg) by (unfold fr_shadow_len; pose proof (Z.pow_pos_nonneg 2 kg); lia). lia.
+ injection E as EG _. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
assert (HF8 : F0 mod 8 = 0) by (unfold fr_size in HFal; cbn in HFal; Z.div_mod_to_equations; lia).
assert (HG8 : G mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kg)); [| apply Z.mod_divide; [pose proof (fr_size_pos kg); lia | exact HGal]].
exists (fr_shadow_len kg). rewrite (fr_size_shadow kg) by lia. lia. }
apply Hni. replace F0 with G; [exact (in_map fr_base _ _ HG)|]. unfold shad in EG. Z.div_mod_to_equations. lia.
Qed.

Lemma tokrep_g_agree : forall mxd fl m m' BS tk,
tokrep_g asegs A4F mxd fl m BS tk -> agree_on asegs BS m m' -> tokrep_g asegs A4F mxd fl m' BS tk.
Proof.
intros mxd fl m m' BS tk (stack & pb & depth & PBS & levels & x & EBS & LEN & RNG & TOK & PB & Hpb & TSK & LOK & LCL) AG.
exists stack, pb, depth, PBS, levels, x.
split; [exact EBS|]. split; [exact LEN|]. split; [exact RNG|].
split. { eapply (rw_cells_agree asegs); [exact TOK | exact AG |]. exists tk, 72. split; [rewrite EBS; left; reflexivity | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. rewrite EBS. right; right. apply in_or_app; left; exact Hb. }
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AG |]. exists stack, (32 * mxd). split; [rewrite EBS; right; left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl). lia. }
split; [| exact LCL].
intros i l Hl Hi. eapply (lvl_ok_agree asegs A4F); [exact (LOK i l Hl Hi) | exact AG |].
intros b Hb. rewrite EBS. right; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb].
Qed.

Definition pe_epilogue_A2_stmt : Prop :=
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (T : TSet) (lo : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) s3 a1 a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 (Z_to_bv 64 (pa_F pa)) s6 s7 (Z_to_bv 64 (pa_F pa)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI) fc None m (seg_rom asegs)).
Lemma EPI2 : pe_epilogue_A2_stmt.
Proof. exact (pe_epilogue_A HIx). Qed.

Lemma out_finish_A :
forall (pf : pe_fix) (pa : pe_fixA) (LBc LK LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (RBS TBS : list blk) (r : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPA A4L HIx A (RBS ++ TBS ++ LK ++ LBc) LM ((pa_F pa, 2) :: FRS) B m md ->
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m TBS (pf_tk pf) ->
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
model_vm_only (cfg_model md0) (cfg_model md) ->
GA m ->
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B -> pa_dslack pa <= bD B ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 r) s4 (Z_to_bv 64 (pa_F pa)) s6 s7 (Z_to_bv 64 (pa_F pa)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC HP TR RET FR ST ERR LOC HPRX VM G BB BD RAE FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (LBall := RBS ++ TBS ++ LK ++ LBc) in *.
eapply EPI2; [exact HP | exact GEO | exact SP0 | exact FR | exact ST | exact LO | exact LOS | exact RAE |].
intros m' md' A' fp VM' HP' ST' FPR FPnc FPimg FPns FPfr MU WM MI.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in FPimg.

assert (DJ : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] a n).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _). cbn [disjoint_from]. split; [| split; [| split; [| exact I]]].
- pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as X. rewrite fr_size_2 in X. lia.
- destruct (Z_le_gt_dec (fp + 1) a); [lia|]. destruct (Z_le_gt_dec (a + n) fp); [lia|]. exfalso. apply FPnc. right; right. exists (a, n). split; [exact Hin | cbn [blk_addr blk_size fst snd]; lia]. }
assert (AG : agree_on asegs (LBall ++ LM) m m').
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. exact (DJ a n Hin). }
apply K. unfold pe_post_A.
exists m', gp, r, errv, RBS, TBS, LK, B.
split; [apply ret_statew_intro; [exact FS | exact FRM]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [exact ST'|].
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6434400 - 164 <= fp < 6434400 - 160)) by (intros X; apply FPns; cbn [hl_scratch A4H]; unfold A_TP; lia). lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MU | exact WM |]. unfold LOCCELL_A, A_TP, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6434400 - 48 <= fp < 6434400 - 40)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc.
assert (O12 : outside [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8)] a).
{ destruct (own_frame_freshG (pa_F pa) LBall LBc LM FRS B A m md HP ltac:(unfold LBall; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as [OFF OFS].
eapply (client_outsideF HIx _ LBall LM ((pa_F pa, 2) :: FRS) _ (LBc ++ LM ++ fr_ivs A4L FRS) _ _ _ (pa_sp0 pa) HP); [ | lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists (pa_F pa), 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]).
+ right. unfold shad, shA; cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_2. unfold A_SB. lia.
+ left. cbn [fst snd]. rewrite fr_size_2. lia. }
cbn [outside] in O12 |- *. destruct O12 as (O1 & O2 & _). split; [exact O1|]. split; [exact O2|]. split; [| exact I].
intros Hfp. assert (a = fp) by lia. subst a. destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr Gf kg HG) as [N1 N2].
+ apply N1. lia.
+ apply N2. exact Hbr. }
split; [exact HP'|].
split. { eapply tokrep_g_agree; [exact TR|]. eapply agree_on_incl; [exact AG|]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; right. apply in_or_app; left. exact Hb. }
split. { destruct RET as [R0 | (Rn & s & J & SD)]; [left; exact R0 | right]. split; [exact Rn|]. exists s. split; [| exact SD].
eapply (jval_agree asegs A4F); [exact J | exact AG |]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; left. exact Hb. }
split. { eapply GA_outside; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; unfold shA, A_SB; lia. }
split; [exact BB | exact BD].
Qed.

Definition PE_OUTW_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (LK : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts ++ LK) LM ((pa_F pa, 2) :: FRS) B m md /\
stk asegs m lo (pf_spf pf) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
heap_presx A4H xlocA (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m /\
model_vm_only (pf_md pf) (cfg_model md) /\
GA m /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_weakA m (t_depth ts) i l) /\
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B /\ pa_dslack pa <= bD B.

Lemma OUTW_of_INVW : forall pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv,
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m md A B ts LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv (CORE & (HP & ST & ERR & _ & _ & _ & HPR & MDV & G) & LVW & BB & BD).
split; [exact CORE|]. split; [exact HP|]. split; [exact ST|]. split; [exact ERR|].
split; [eapply heap_presx_weaken; [exact HPR | lia | intros b Hb; exact Hb | intros a Xa; left; exact Xa]|].
split; [exact MDV|]. split; [exact G|]. split; [exact LVW|]. split; [exact BB | exact BD].
Qed.

Lemma lvl_weakA_agree : forall BS m m' depth i l, lvl_weakA m depth i l -> agree_on asegs BS m m' -> incl (lvl_blocks l) BS -> lvl_weakA m' depth i l.
Proof.
intros BS m m' depth i l (R & J & N & C) AG Hi. split; [exact R|]. split.
- eapply (jopt_agree asegs A4F); [exact J | exact AG | intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; left; exact Hb].
- split; [| exact C]. destruct N as [N|N]; [left|right]; (eapply (name_ok_agree asegs); [exact N | exact AG |]; intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; right; exact Hb).
Qed.

Lemma lvl_blocks_in_tstate : forall ts i l, nth_error (t_levels ts) i = Some l -> incl (lvl_blocks l) (tstate_blocks ts).
Proof.
intros ts i l Hl b Hb. unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | exact Hb].
Qed.

Lemma OUTW_locw : forall pf pa q LB0 LM FRS me lo m m1 md A B ts LK cb nb pj sv errv,
PE_STATIC_A HIx pf pa lo ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m md A B ts LK cb nb pj sv errv ->
munch [(LOCCELL_A, LOCCELL_A + 8)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m1 md A B ts LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS me lo m m1 md A B ts LK cb nb pj sv errv STC (CORE & HP & ST & ERR & HPRX & MDV & G & LVW & BUD) MU WM MI.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (LBall := pe_blocksA pf q LB0 ts ++ LK) in *.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
assert (LOCR : LOCCELL_A = 6434352) by reflexivity.
assert (BIMG : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(LOCCELL_A, LOCCELL_A + 8)] a n).
{ intros a n Hin. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Hi. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. cbn [disjoint_from]. split; [lia | exact I]. }
assert (AG : agree_on asegs (LBall ++ LM) m m1) by (eapply (agree_of_munch asegs); [exact MU | exact WM | exact BIMG]).
assert (INtk : In (pf_tk pf, 72) (LBall ++ LM)) by (apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (LBall ++ LM)) by (apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INts : incl (tstate_blocks ts) (LBall ++ LM)) by (intros b Hb; apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; left; exact Hb).
split.
{ split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split. { eapply (rw_cells_agree asegs); [exact TOK | exact AG |]. exists (pf_tk pf), 72. split; [exact INtk | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. apply INts. unfold tstate_blocks. apply in_or_app; left. exact Hb. }
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AG |]. exists q, (32 * pf_mxd pf). split; [exact INq|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl). lia. }
destruct FR as (SL & GP & SV & FF & FSH).
split; [| split; [| split; [| split]]].
- eapply rw_cells_transport; [exact SL | exact MU | exact WM |]. rewrite pe_slotsA_size. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact GP | exact MU | exact WM |]. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact SV | exact MU | exact WM |]. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact FF | exact MU | exact WM |]. unfold ff_cellsA. cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I].
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. unfold ffsh_cells, FSH0, shA, A_SB. cbn [cells_size csize Nat.add map length disjoint_from]. split; [right; lia | exact I]. }
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI]. eapply (frame_writes_okFS _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_nil]. right; right; right; right. cbn [fst snd]. intros x Hx. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
split. { eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. left. cbn [outside]. split; [lia | exact I]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO. cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I]. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I].
intros Hin. destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- lia.
- apply Hx. right. exact Hin.
- assert (OUTI : blk_addr b + blk_size b <= 65536 \/ 6574080 <= blk_addr b).
{ apply in_app_or in Hb as [Hb | Hb].
- destruct b as [ba bn]. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb)) as Hi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H blk_addr blk_size fst snd] in Hi |- *. exact Hi.
- apply in_app_or in Hb as [Hb | Hb].
+ destruct b as [ba bn]. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; right; exact Hb)) as Hi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H blk_addr blk_size fst snd] in Hi |- *. exact Hi.
+ apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd].
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _ & HG0 & _). right. unfold shad. cbn [hl_sb A4L]. unfold A_SB. Z.div_mod_to_equations. lia. }
lia. }
split; [exact MDV|].
split; [exact (GA_loc _ _ G MU WM)|].
split; [| exact BUD].
intros i l Hl. eapply lvl_weakA_agree; [exact (LVW i l Hl) | exact AG |]. intros b Hb. apply INts. exact (lvl_blocks_in_tstate ts i l Hl b Hb).
Qed.

Lemma lb_remove_incl : forall p (LB : list blk), incl (lb_remove p LB) LB.
Proof.
induction LB as [|[a n] LB IH]; intros b Hb; [exact Hb|]. cbn [lb_remove blk_addr fst] in Hb.
destruct (Z.eqb a p); [right; exact Hb|]. destruct Hb as [Hb | Hb]; [left; exact Hb | right; apply IH; exact Hb].
Qed.

Lemma OUTW_call : forall pf pa q LB0 LM LM' FRS me lo m1 m2 md md2 A A2 B B2 ts LK cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m1 md A B ts LK cb nb pj sv errv ->
incl LM' LM ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H ((pe_blocksA pf q LB0 ts ++ LK) ++ LM' ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts ++ LK) LM' ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
bB B <= bB B2 -> bD B <= bD B2 ->
PE_OUTW_A pf pa q LB0 LM' FRS me lo m2 md2 A2 B2 ts LK cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM LM' FRS me lo m1 m2 md md2 A A2 B B2 ts LK cb nb pj sv errv errv2 STC (CORE & HP & ST & ERR & HPRX & MDV & G & LVW & BB & BD) HLM VM HPR HP2 ST2 ERR2 HB HD.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (LBall := pe_blocksA pf q LB0 ts ++ LK) in *.
assert (INtk : In (pf_tk pf, 72) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INts : incl (tstate_blocks ts) LBall) by (intros b Hb; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; left; exact Hb).
assert (AG : agree_on asegs LBall m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. exact Hb. }
split.
{ split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact TOK |]. eapply client_range_block; [apply in_or_app; left; exact INtk | lia | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. apply INts. unfold tstate_blocks. apply in_or_app; left. exact Hb. }
split; [exact Hpb|].
split. { eapply (tstack_pres_g A4H); [exact HPR | apply in_or_app; left; exact INq | exact LEN32 | exact TSK]. }
eapply (pe_frameA_pres pf pa _ _ _ _ _ _ _ _ HPR); [lia | exact GEO | | | exact FR].
- apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity.
- apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; reflexivity. }
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
split.
{ eapply heap_presx_trans; [eapply heap_presx_weaken; [exact HPRX | lia | | intros a Xa; exact Xa] |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply HLM; exact Hb | apply in_or_app; right; exact Hb].
- eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [eapply model_vm_only_trans; [exact MDV | exact VM]|].
split; [eapply GA_pres; [exact HPR | exact G]|].
split; [| split; lia].
intros i l Hl. eapply lvl_weakA_agree; [exact (LVW i l Hl) | exact AG |]. intros b Hb. apply INts. exact (lvl_blocks_in_tstate ts i l Hl b Hb).
Qed.
End PeSOutA.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x Qoif Qeia QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2 Qdyh.Mq0 Qu4M.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QYZ0.Mq3 QlKV.Mq7 QsKa.Mq5 Qoif.Mq0 Qeia.Mq0 QYZ0.Mq4 QWrz.Mq0 QdGy.Mq6 Q63E.Mq2 Qt1H.Mq3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOvaddA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma seg_ovadd_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat) (v2 ra2 : Z)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
pj_obj pj = Z_to_bv 64 (t_obj ts) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovadd ->
tl_cs l = Some (Sobj kids) ->
frm0 fc -> Z.of_nat (length FRS) + 2 < 4096 ->

pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94360) (UWfp ra2 v2) ->

(forall m' md' A' B' cbs' kids' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
Z.of_nat (length kids') <= Z.of_nat (length kids) + 1 ->
okmax kids' <= Z.max (okmax kids) (odep (t_objs ts)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) cb nb pj sv errv' ->
PBOK m' (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) kP ->
BOK pf pa (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) B' nB ->
(forall w wv nm nn, tl_nbs l = [(nm, nn)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
exists w', jtx (Sobj kids') cbs' = Some (w', []) /\ w' <= w + key_w nn + wv) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' md' A' B' LK errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts LK cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' (Z_to_bv 64 (pf_tk pf + 56)) s11' t4' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ovadd) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK OBJW Hl Hst Hcs FRM FRN S0V RAV HV UWK Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_ERRST, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = true).
{ rewrite Hst, (Qdyh.Mq0.lvl_mode_ovadd (tl_ss l)) in Hmode. injection Hmode as <- <-. split; reflexivity. }
destruct MODE0 as (-> & ->). cbn [name_ok] in NM0. destruct NM0 as (Hn0 & nn & ks & Hnbs0 & Hnn & CSTR0).
destruct pj as [pj0 pj8 pj16 pjobj pj288 pj304 pjgap pjfhd pjf1 pjf2]. cbn [pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj_gap pj_fhd pj_f1 pj_f2] in *. subst pjobj.
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ3c SEPQ3q SEPQ3t.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_ovadd. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkA.
step.
asan_chkA.
step. step. step.
step.
evt_done5. subst bse.
eapply (pe_oadd_c HIx GA GA_presx GA_lh HD HD_le OADD (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb _ sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Hcs | exact FRM | exact FRN | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT FS2 FRM2.
clear TOK SLOTS FF SHT SHQ SHQ4 SHQ2 SHQ3 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq HbseR Hb8.
destruct OUT as [(-> & cbs2 & kids2 & INV2 & PBK2 & LENK & DEPK & BK2 & JX2) | (-> & LK & INVW2)].
- set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) in *.
set (TS2 := ts_lvl_obj ts0 l2 0 None []) in *.
assert (Hd : (depth < length levels)%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Hl2 : nth_error (t_levels TS2) (t_depth TS2) = Some l2) by (unfold TS2, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd).
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & _). clear REST2.
unfold TS2, ts_lvl_obj, ts0 in TOK, TSK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; exact Hd)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPQ3c SEPQ3q SEPQ3t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t2. stash Himg_q2. stash TSK. stash INV2.
reenterA asegs A4L HIx asegs_wx HP.
step. step.
if_true.
step.
asan_rechkA.
asan_rechkM 1.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
step.
step.

evt_done5. unstash INV2.
pose proof (PE_NWIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md2 A2 B2 TS2 cb nb _ sv errv2 l2 INV2 Hl2 eq_refl) as WIN0.
cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs l2] in WIN0. rewrite Hnbs0 in WIN0.
set (ln := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) []) in *.
set (TSn := ts_lvl TS2 ln) in *.
assert (COST : 512 <= bB B2).
{ pose proof (BK2 (tl_st l) (tl_ss l) 0 None ltac:(right; rewrite Hst; reflexivity)) as BKx.
fold l2 TS2 in BKx. eapply (BOK_blk_512 _ _ _ _ _ (tl_name l, nn) BKx BSL). unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l2). split; [apply in_map; eapply nth_error_In; exact Hl2 | unfold lvl_blocks; apply in_or_app; right; cbn [tl_nbs l2]; rewrite Hnbs0; left; reflexivity]. }
eapply (pe_free_name_n HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md2 A2 B2 TSn cb nb _ sv errv2 T (co + kP) v2 ra2 (tl_name l) nn);
[exact STC | exact WIN0 | unfold TSn; apply (PBOKat_same m2 TS2); [reflexivity | reflexivity | exact PBK2] | exact COST | exact S0V | exact RAV | exact HV
| exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros m3 md3 A3 r3 v0 v1 v2' v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 WIN3 PBK3.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ3 SHT7 SHT2 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi WIN0 INV2 PBK2 COST.
pose proof WIN3 as (COREx & BASEx & _). destruct COREx as (_ & _ & _ & _ & TOK & _ & _ & TSK3 & FR3). pose proof (proj1 BASEx) as HP. clear BASEx.
unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR3 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q3.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m3) as WM.
assert (Hln : nth_error (t_levels TSn) (t_depth TSn) = Some ln) by (unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite lupd_length; exact Hd).
pose proof (TSK3 depth ln Hln) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, ln in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPQ3c SEPQ3q SEPQ3t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t3. stash Himg_q3. stash WIN3. stash TSK3. stash FR3.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
step.
asan_rechkA.
asan_rechkM 6.
clear SHT7 SHT2.
step.
norm_sx32.
step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia.
rewrite Z.shiftl_mul_pow2 by lia.
change (2 ^ 5) with 32.
step.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
clear SHQ3.
stepz.
step.
asan_chkA.
step.
stepz.
asan_chkA.
stepz.
step.

set (lf := TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids2)) cbs2 0 []).
unstash WIN3. unstash TSK3. unstash FR3.
assert (Hlen3 : length (t_levels TSn) = Z.to_nat mxd) by (unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb (PEJA pj0 pj8 pj16 (Z_to_bv 64 obj) pj288 pj304 pjgap pjfhd pjf1 pjf2) sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS (charge B2 512 0) A3 m3 mc md3 lo [(bse, bse + 32)] cb nb _ sv); [exact STC | exact HP | exact INqL | exact FR3 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels TSn) (t_depth TSn) lf))
by (rewrite Hbse in MUc, Lc; eapply (tstack_put asegs m3 mc q (t_levels TSn) depth lf []);
[exact TSK3 | rewrite Hlen3; lia | exact MUc | exact WMc | intros; exact I | exact Lc]);
destruct (PE_NWIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 (charge B2 512 0) TSn []
cb nb _ sv errv2 [(bse, bse + 32)] ln lf cb nb _ STC WIN3 Hln MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lf, ST_eatws; cbn [tl_st]; lia) ltac:(unfold lf, ST_osep; cbn [tl_ss]; lia) eq_refl eq_refl eq_refl eq_refl) as (WIN4 & PBT4 & _)
end end.
set (TSf := ts_lvl TSn lf) in *.
assert (Hlf : nth_error (t_levels TSf) (t_depth TSf) = Some lf) by (unfold TSf, TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite !lupd_length; exact Hd).
assert (ETS : ts_lvl TSf lf = ts_lvl_obj ts0 lf 0 None []).
{ unfold TSf, TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite !lupd_lupdS. reflexivity. }
assert (BK4 : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl_obj ts0 lf 0 None []) (charge B2 512 0) nB).
{ pose proof (BK2 (tl_st l) (tl_ss l) 0 None ltac:(right; rewrite Hst; reflexivity)) as BKx. fold l2 TS2 in BKx.
pose proof (BOK_name_free (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) TS2 B2 (charge B2 512 0) nB l2 (tl_name l, nn) ST_eatws ST_osep 0 BKx Hl2 ltac:(cbn [tl_nbs l2]; exact Hnbs0)
ltac:(intros CL; exfalso; rewrite (lvl_closed_open_st l2) in CL; [discriminate CL | cbn [tl_st l2]; rewrite Hst; reflexivity])
ltac:(cbn; lia) ltac:(cbn; lia)) as BKy.
cbn [tl_cur tl_cs tl_cbs l2] in BKy. unfold TS2, ts_lvl, ts_lvl_obj, ts0 in BKy |- *. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in BKy |- *.
rewrite lupd_lupdS in BKy. exact BKy. }
pose proof (PE_NWIN_close HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md3 A3 (charge B2 512 0) TSf [] cb nb _ sv errv2 lf CObj false WIN4 Hlf
ltac:(vm_compute; reflexivity) I ltac:(cbn [name_ok tl_name tl_nbs lf]; split; reflexivity) ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name lf]; fold lf; rewrite ETS; exact (BOK_weak _ _ _ _ _ BK4))) as INV5.
cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name lf] in INV5. fold lf in INV5. rewrite ETS in INV5.
pose proof (PE_INV_A_set_obj HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ obj objs INV5 eq_refl
ltac:(rewrite (cur_st_lvl_obj ts0 l _ _ _ _ Hl); exact I)) as INV6.
pose proof (PBT4 _ PBK3) as P4.
eapply (Kredo _ md3 A3 (charge B2 512 0) cbs2 kids2 errv2); [exact LENK | exact DEPK | exact INV6 | eapply (PBOKat_same _ TSf); [reflexivity | reflexivity | exact P4] | | exact JX2 | exact FS2 | exact FRM2].
exact (BOK_obj_irrel _ _ _ _ _ _ _ _ _ _ BK4).
- clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INVW2 as (CORE2 & BASE2 & _).
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FR).
pose proof (proj1 BASE2) as HP. clear BASE2.
unfold ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2.
reenterA asegs A4L HIx asegs_wx HP.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step. step.
if_false.
step.
step.
asan_rechkM 2.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 LK errv2); [exact INVW2 | exact FS2 | exact FRM2].
Qed.
End PeSOvaddA.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY Qkko QlmN QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QsKa.Mq8 QrQv.Mq2 QEUF QdGy.Mq2 QfHY.Mq0 Qkko QlmN QlmN.Mq1 QVob.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma seg_sesc_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode ST_escape_unicode (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m')) ->

(forall m' a0' a1' a2' a3' a4',
bv_unsigned cb = 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts))))
(TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts))))
(TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0' a1' a2' a3' a4' a5 a6 a7 (Z_to_bv 64 (Z.of_nat (t_depth ts)))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F fc m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(Q1Y6.Mq2.pe_msE pf pa APE_ERR2 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) s5' (Z_to_bv 64 (pf_tk pf + 36)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 (pa_F pa))
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pf_sb pf + t_co ts)) t3' t4' t5' t6' F' fc' m')) ->

(forall a1' a3' a4',
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_ERR2 (t_co ts) gp t0 t1 t2 (Z_to_bv 64 12) a1'
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3' a4' a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_string_escape) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) (Z_to_bv 64 (pa_F pa + 64)) F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE HMODE10 Hzss Kbreak Kbrku Kerr16 Kerr12.
eapply (sesc_dispatch_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. intros a3' a4'.
destruct (pe_jt3A_cases (bv_unsigned cb)) as [[E C] | [[E C] | [[E C] | E]]]; rewrite E.
- eapply (sesc_quote_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
- eapply (sesc_u_A HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP);
[exact STC | exact INV | exact PBK | exact Hl | exact Hst | exact HMODE10 |].
intros m' a0' a1' a2' a3x a4x INV' PBK'. eapply (Kbrku m'); [exact C | exact INV' | exact PBK'].
- eapply (sesc_hash_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (bv_unsigned cb)); [exact STC | exact INV | exact C |].
intros a0' a1'.
destruct C as [C | [C | [C | [C | C]]]]; rewrite C; cbn [pe_jt4A].
+ eapply (sesc_lit_b_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_f_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_n_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_r_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_t_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
- eapply (sesc_default_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. apply Kerr12.
Qed.
End PeSSescA.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QSHS Qc5u QAzu Q6vt Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QrQv.Mq4 QEUF.Mq2 QdGy.Mq9 QW22.Mq8 QdGy.Mqc QV7s.Mq3 QYZ0.Mq8 QL3k.Mq3 Qpfz.Mq3 Q63E.Mqa QlAE.Mq2 QlAE.Mq1 QMmN.Mq0 QQd3.Mq0 QQdK.Mq0.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import Q2EX QdGy.Mqa Q63E.Mqb QV7s.Mq4 QnDr.Mq6 Qpfz.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma rank_ge1S : forall st ss, (1 <= rank st ss)%nat.
Proof. intros st ss. unfold rank, base_rank. repeat (destruct (zin _ _)); destruct (st =? ST_eatws); lia. Qed.
Lemma cur_st_lvlS : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st (ts_lvl ts l') = tl_st l'.
Proof. intros ts l l' Hl. unfold cur_st, ts_lvl; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.
Lemma cur_ss_lvlS : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> cur_ss (ts_lvl ts l') = tl_ss l'.
Proof. intros ts l l' Hl. unfold cur_ss, ts_lvl; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; rewrite Hl; discriminate). reflexivity. Qed.
Lemma cur_st_ofS : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_st ts = tl_st l.
Proof. intros ts l H. unfold cur_st. rewrite H. reflexivity. Qed.
Lemma cur_ss_ofS : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> cur_ss ts = tl_ss l.
Proof. intros ts l H. unfold cur_ss. rewrite H. reflexivity. Qed.
Lemma mbase_lvlS : forall pf ts l', mbase pf (ts_lvl ts l') = mbase pf ts.
Proof. reflexivity. Qed.

Lemma PBS_lvl : forall ts l l', nth_error (t_levels ts) (t_depth ts) = Some l -> PBS (ts_lvl ts l') = PBSst (tl_st l').
Proof. intros ts l l' Hl. unfold PBS. rewrite (cur_st_lvlS ts l l' Hl). reflexivity. Qed.
Lemma PBS_of : forall ts l, nth_error (t_levels ts) (t_depth ts) = Some l -> PBS ts = PBSst (tl_st l).
Proof. intros ts l Hl. unfold PBS. rewrite (cur_st_ofS ts l Hl). reflexivity. Qed.

Lemma tdepth_ok_lvl : forall ts l st' ss', tdepth_ok ts -> nth_error (t_levels ts) (t_depth ts) = Some l -> (t_depth ts <= 31)%nat ->
zin st' [ST_array_add; ST_ovadd] = false ->
tdepth_ok (ts_lvl ts (TL st' ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))).
Proof.
intros ts l st' ss' TD Hl Hd Hz. unfold ts_lvl. eapply tdepth_ok_upd; [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); lia | exact Hd | exact Hz].
Qed.

Lemma cur_st_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_st (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_st l'.
Proof. intros. unfold cur_st; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma cur_ss_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l -> cur_ss (TST depth (lupd levels depth l') co pb pbs x o os obs) = tl_ss l'.
Proof. intros. unfold cur_ss; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (apply nth_error_Some; congruence). reflexivity. Qed.
Lemma PBS_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
PBS (TST depth (lupd levels depth l') co pb pbs x o os obs) = PBSst (tl_st l').
Proof. intros. unfold PBS. rewrite (cur_st_upd _ _ l) by assumption. reflexivity. Qed.
Lemma NAO_upd : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false -> NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof.
intros depth levels l l' co pb pbs x o os obs Hl H. unfold NAO. rewrite (cur_st_upd _ _ l) by assumption. unfold EUS, zin in *. cbn [existsb] in *.
destruct (tl_st l' =? ST_array_add); [discriminate H|]. destruct (tl_st l' =? ST_ovadd); [discriminate H|]. destruct (tl_st l' =? ST_escape_unicode); [discriminate H|].
destruct (tl_st l' =? ST_esc_need_escape); [discriminate H|]. destruct (tl_st l' =? ST_esc_need_u); [discriminate H|]. reflexivity.
Qed.

Lemma NAO_upd2 : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = false -> zin (tl_st l') [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false ->
NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof. intros. apply NAO_plain; rewrite (cur_st_upd _ _ l) by assumption; assumption. Qed.

Lemma NAO_upd_eu : forall depth levels l l' co pb pbs x o os obs, nth_error levels depth = Some l ->
zin (tl_st l') [ST_array_add; ST_ovadd] = false -> SPV x = 0 -> UCSV x < 65536 -> NAO (TST depth (lupd levels depth l') co pb pbs x o os obs).
Proof. intros. apply NAO_eu; [rewrite (cur_st_upd _ _ l) by assumption; assumption | assumption | assumption]. Qed.
Lemma SPOK_upd_plain : forall depth levels l l' co pb pbs x o os obs k, nth_error levels depth = Some l ->
zin (tl_st l') [ST_null; ST_boolean; ST_inf] = false -> SPOK (TST depth (lupd levels depth l') co pb pbs x o os obs) k.
Proof. intros. unfold SPOK. rewrite (cur_st_upd _ _ l) by assumption. intros HH. rewrite H0 in HH. discriminate HH. Qed.

Section PeSCases1B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis AADD : jo_array_add_A2J HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_ofend : CASEx ST_ofend.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_ofend_A HIx GA GA_outside pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1); [exact STC | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | exact Hst | exact Hco | |].
-
intros m' a1' a4' a5' C58 INV' PBK'.
change (Qdyh.Mq3.ts_set_level ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
with (ts_lvl ts (TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) in *.
set (l' := TL ST_eatws ST_ovalue (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_ovalue Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros a5' N58.
unfold pe_msO.
pose proof (KE ts [] 10 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_osep : CASEx ST_osep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_osep_A HIx GA GA_outside pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1); [exact STC | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | exact Hst | exact Hco | |].
-
intros m' ss' a1' a4' a5' Hc INV' PBK'.
change (Qdyh.Mq4.ts_set_level ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)))
with (ts_lvl ts (TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) in *.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. subst l'. destruct Hc as [[_ ->] | [_ ->]]; pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ss' Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros a5' N44 N125.
unfold pe_msO, pe_msX.
pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 11 m md A B cb nb pj errv) as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_ofs : CASEx ST_ofs.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
replace (pe_jtA ST_ofs) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_ofs_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1);
[exact STC | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | left; exact Hst | exact Hco | | |].
-
intros m' a1' a4' C125 INV' PBK'.
set (l' := TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_finish Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros _. reflexivity.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' a0' a1' a2' a3' a4' a6' Hq INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (tx_quote (t_x ts) cb)) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs (tx_quote x cb) obj objs objbs) B _ l ST_ofield (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co (tx_quote x cb)); [cbn [t_co]; lia | exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL. reflexivity.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a1' N34 N39 N125.
unfold pe_msO.
pose proof (KE ts [] 9 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_ofs2 : CASEx ST_ofs_after_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
replace (pe_jtA ST_ofs_after_sep) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_ofs_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1);
[exact STC | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact Hl | right; exact Hst | exact Hco | | |].
-
intros m' a1' a4' C125 INV' PBK'.
set (l' := TL ST_eatws ST_finish (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ST_finish Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros _. reflexivity.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' a0' a1' a2' a3' a4' a6' Hq INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (tx_quote (t_x ts) cb)) (TL ST_ofield (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs (tx_quote x cb) obj objs objbs) B _ l ST_ofield (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co (tx_quote x cb)); [cbn [t_co]; lia | exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL. reflexivity.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a1' N34 N39 N125.
unfold pe_msO.
pose proof (KE ts [] 9 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_cstart : CASEx ST_comment_start.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_cstart_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | | |].
-
intros m' md' A' B' st' pbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' Hc INV' PBK' BK' FS' FRM'.
assert (Hst' : st' = ST_comment \/ st' = ST_comment_eol) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
eapply (IHB (ts_pbs (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs'));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. cbn [tl_st]. destruct Hst' as [-> | ->]; discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; destruct Hst' as [-> | ->]; pbs_norm; pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
-
intros m' md' A' B' st' errv' t0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' Hc INV' FS' FRM'.
assert (Hst' : st' = ST_comment \/ st' = ST_comment_eol) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
pose proof (KE (ts_lvl ts (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) [] 16 m' md' A' B' cb nb pj errv') as KEM.
unfold pe_msE, pe_msO in KEM. unfold pe_msO. eapply KEM; [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
-
intros a4' N42 N47.
unfold pe_msO, pe_msX.
pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 13 m md A B cb nb pj errv) as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_cend : CASEx ST_comment_end.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_cend_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | |].
- intros m' md' A' B' st' pbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' Hc INV' PBK' BK' FS' FRM'.
assert (Hst' : st' = ST_eatws \/ st' = ST_comment) by (destruct Hc as [[_ E] | [_ E]]; [left | right]; exact E).
eapply (IHB (ts_lvl (ts_pbs ts pbs') (TL st' (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. cbn [tl_st]. destruct Hst' as [-> | ->]; discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | destruct Hst' as [-> | ->]; reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; destruct Hst' as [-> | ->]; pbs_norm; pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | cbn [tl_st]; destruct Hst' as [-> | ->]; reflexivity].
-
intros m' md' A' B' errv' x1' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 16 m' md' A' B' cb nb pj errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | exact TD | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_asep : CASEx ST_array_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
eapply (seg_asep_A HIx GA GA_outside GA_pres SHRINK pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (bredo pf ts));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | exact Hco | | |].
-
intros m' ss' a1' a4' a5' Hc INV' PBK'.
set (l' := TL ST_eatws ss' (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ rewrite (PBS_lvl ts l l' Hl); cbn [tl_st]; pbs_norm. subst l'. destruct Hc as [_ ->]; pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_eatws ss' Hl); [| exact BK]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| try (subst l'; destruct Hc as [_ ->]); bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. rewrite Hst in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Hst, CL in Hmode. vm_compute in Hmode. discriminate Hmode.
+ unfold NAO. rewrite (cur_st_lvlS ts l l' Hl). reflexivity.
-
intros m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| try (subst l'; destruct Hc as [_ ->]); bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros a2' a5' N44 N93.
unfold pe_msO, pe_msX.
pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 8 m md A B cb nb pj errv) as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_aadd : CASEx ST_array_add.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & _).
rewrite Hst, (Qdyh.Mq0.lvl_mode_aadd (tl_ss l)) in Hmode. injection Hmode as <- <-.
assert (Hcs : exists kids, tl_cs l = Some (Sarr kids)) by (destruct (tl_cs l) as [s0|]; [destruct s0; cbn in CLS0; try contradiction; eexists; reflexivity | cbn in CLS0; contradiction]).
destruct Hcs as [kids Hcs].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 1280 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 1280)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (OBJV : pj_obj pj = Z_to_bv 64 (t_obj ts)) by (apply (proj1 OW); rewrite Est, Hst; reflexivity).
eapply (seg_aadd_A HIx GA GA_outside GA_pres AADD pf pa q LBc LM FRS payload me lo m md A B ts l kids cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 1280)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact OBJV | exact Hl | exact Hst | exact Hcs | |].
-
intros m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INV' PBK' BK' JX' FS' FRM'.
assert (OBN : t_objs ts = None -> t_objbs ts = []).
{ pose proof INV as [_ (_ & _ & OBJ9 & _)]. rewrite Est, Hst in OBJ9. cbn in OBJ9. intros E9. rewrite E9 in OBJ9. exact (proj2 OBJ9). }
eapply (IHR (ts_lvl_obj ts (TL ST_eatws ST_array_sep (tl_cur l) (Some (Sarr (kids ++ [t_objs ts]))) cbs' (tl_name l) (tl_nbs l)) (t_obj ts) (t_objs ts) []));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl_obj in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, Hst in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_eatws ST_array_sep) with 2%nat. change (rank ST_array_add (tl_ss l)) with 3%nat in M. lia.
+ intros E. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_absorb (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Hst; reflexivity | cbn [t_objs]; rewrite Hcs; apply odep_absorb_arr | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_add _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 6 Hl);
[reflexivity | reflexivity | rewrite ?Hst; reflexivity | reflexivity | exact PBK | exact PBK' | lia | jl_dead
| intros w0 b Lw0 Eb; exact (lw_aadd l kids objs objbs cbs' _ _ w0 b Hcs Lw0 Eb OBN JX') | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, Hst by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co].
change (rank ST_eatws ST_array_sep) with 2%nat. change (rank ST_array_add (tl_ss l)) with 3%nat. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_comment : CASEx ST_comment.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_comment_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_comment_end (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_set_co ts co') [] 16 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma case_ceol : CASEx ST_comment_eol.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof INV as [(LEN32 & D32 & _) _]; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_ceol_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | |].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs (ts_set_co ts co') pbs') (TL ST_eatws (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pbs' e co' cb' errv' gp' t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (kerrmem2_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO _ []);
[apply (PE_INV_A_W HIx GA); exact INV' | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_set_co ts co') [] 16 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.
End PeSCases1B.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv QGdd.Mq0 QdGy.Mq7 QcmL QsKa.Mqh QrQv.Mq4 QV7s.Mq3 QdGy.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Hypothesis USE : uselocale_A_stmt.
Hypothesis FREEL : freelocale_A_stmt HIx.

Lemma frame_writes_okFS : forall A LB LM FR B m m' md W,
HEAPA A4L HIx A LB LM FR B m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top A4L HIx)
\/ (exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (forall x, fst iv <= x < snd iv -> hl_client_static A4H x)) W ->
forall a, 0 <= a < 2^64 -> ~ client_addr A4H (LB ++ LM) alloc_ceiling a -> ~ hl_scratch A4L a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a).
Proof.
intros A LB LM FR B m m' md W HP MU HW a Ha Hnc Hns Hnf.
apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1. intros Hin.
destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | [(F & k & HF & HFr) | Hcs]]]].
- apply Hnc. left. lia.
- apply Hnc. right; right. exists (b, n). split; [exact Hb | cbn; lia].
- exact (Hns (Hsc a Hin)).
- apply Hnf. exists F, k. split; [exact HF|]. destruct HFr as [HFr | HFr]; [left | right]; lia.
- apply Hnc. right; left. exact (Hcs a Hin).
Qed.

Lemma own_frame_freshG : forall F0 (LBall LB0 LM : list blk) FRS B A m md,
HEAPA A4L HIx A LBall LM ((F0, 2) :: FRS) B m md -> incl LB0 LBall ->
~ In (F0, fr_size 2 - 8) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (shad A4L F0, fr_shadow_len 2) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros F0 LBall LB0 LM FRS B A m md HP Hincl.
assert (INF : In (F0, 2) ((F0, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (LBall ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; apply Hincl; exact Hb | right; exact Hb]. }
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- exact (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_frame _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
pose proof (fr_shadow_len_bnd kg Hkg). unfold fr_size in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK. lia.
- exact (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_shadow _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
rewrite (fr_size_shadow kg) in EK by lia. pose proof (fr_shadow_len_bnd kg Hkg).
unfold fr_shadow_len at 1 in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK.
assert (8 <= fr_shadow_len kg) by (unfold fr_shadow_len; pose proof (Z.pow_pos_nonneg 2 kg); lia). lia.
+ injection E as EG _. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
assert (HF8 : F0 mod 8 = 0) by (unfold fr_size in HFal; cbn in HFal; Z.div_mod_to_equations; lia).
assert (HG8 : G mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kg)); [| apply Z.mod_divide; [pose proof (fr_size_pos kg); lia | exact HGal]].
exists (fr_shadow_len kg). rewrite (fr_size_shadow kg) by lia. lia. }
apply Hni. replace F0 with G; [exact (in_map fr_base _ _ HG)|]. unfold shad in EG. Z.div_mod_to_equations. lia.
Qed.

Lemma tokrep_g_agree : forall mxd fl m m' BS tk,
tokrep_g asegs A4F mxd fl m BS tk -> agree_on asegs BS m m' -> tokrep_g asegs A4F mxd fl m' BS tk.
Proof.
intros mxd fl m m' BS tk (stack & pb & depth & PBS & levels & x & EBS & LEN & RNG & TOK & PB & Hpb & TSK & LOK & LCL) AG.
exists stack, pb, depth, PBS, levels, x.
split; [exact EBS|]. split; [exact LEN|]. split; [exact RNG|].
split. { eapply (rw_cells_agree asegs); [exact TOK | exact AG |]. exists tk, 72. split; [rewrite EBS; left; reflexivity | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. rewrite EBS. right; right. apply in_or_app; left; exact Hb. }
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AG |]. exists stack, (32 * mxd). split; [rewrite EBS; right; left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl). lia. }
split; [| exact LCL].
intros i l Hl Hi. eapply (lvl_ok_agree asegs A4F); [exact (LOK i l Hl Hi) | exact AG |].
intros b Hb. rewrite EBS. right; right. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | unfold lvl_blocks; apply in_or_app; left; exact Hb].
Qed.

Definition pe_epilogue_A2_stmt : Prop :=
forall (pf : pe_fix) (pa : pe_fixA) (LBall LM : list blk) (FRS : list frame) (B : bud)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (T : TSet) (lo : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md ->
pe_geomA pf pa -> 0 <= pf_spf pf < 2^62 ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) -> alloc_ceiling <= lo -> lo <= pf_spf pf - 12288 ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
(forall m' md' (A' : ASA A4L HIx) (fp : Z),
model_vm_only (cfg_model md) (cfg_model md') ->
HEAPA A4L HIx A' LBall LM FRS B m' md' ->
stk asegs m' lo (pa_sp0 pa) ->
0 < fp < 2^64 -> ~ client_addr A4H (LBall ++ LM) alloc_ceiling fp -> (fp < hl_img_lo A4H \/ hl_img_hi A4H <= fp) ->
~ hl_scratch A4H fp ->
(forall F' k', In (F', k') FRS -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
munch [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] m m' ->
wmono asegs m m' -> mem_inv asegs m' ->
AJ5 A4L HIx A' T md'
(MS (mkR (pe_ra sv) (Z_to_bv 64 (pa_sp0 pa)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (pe_s0 sv) (pe_s1 sv) a0 (Z_to_bv 64 fp) a2 a3 a4 a5 a6 a7
(pe_s2 sv) (pe_s3 sv) (pe_s4 sv) (pe_s5 sv) (pe_s6 sv) (pe_s7 sv) (pe_s8 sv) (pe_s9 sv) (pe_s10 sv) (pe_s11 sv) t3 t4 t5 t6)
F (ret_pc (pe_ra sv)) fc None m' (seg_rom asegs))) ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI1) fc None m (seg_rom asegs)).
Lemma EPI2 : pe_epilogue_A2_stmt.
Proof. exact (pe_epilogue_A HIx). Qed.

Lemma out_finish_B :
forall (pf : pe_fix) (pa : pe_fixA) (LBc LK LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (RBS TBS : list blk) (r : Z)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPA A4L HIx A (RBS ++ TBS ++ LK ++ LBc) LM ((pa_F pa, 2) :: FRS) B m md ->
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m TBS (pf_tk pf) ->
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) ->
pe_frameA asegs m pf pa cb nb pj sv ->
stk asegs m lo (pf_spf pf) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
model_vm_only (cfg_model md0) (cfg_model md) ->
GA m ->
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B -> pa_dslack pa <= bD B ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI1) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC HP TR RET FR ST ERR LOC HPRX VM G BB BD RAE FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (LBall := RBS ++ TBS ++ LK ++ LBc) in *.
eapply EPI2; [exact HP | exact GEO | exact SP0 | exact FR | exact ST | exact LO | exact LOS | exact RAE |].
intros m' md' A' fp VM' HP' ST' FPR FPnc FPimg FPns FPfr MU WM MI.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in FPimg.

assert (DJ : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] a n).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _). cbn [disjoint_from]. split; [| split; [| split; [| exact I]]].
- pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as X. rewrite fr_size_2 in X. lia.
- destruct (Z_le_gt_dec (fp + 1) a); [lia|]. destruct (Z_le_gt_dec (a + n) fp); [lia|]. exfalso. apply FPnc. right; right. exists (a, n). split; [exact Hin | cbn [blk_addr blk_size fst snd]; lia]. }
assert (AG : agree_on asegs (LBall ++ LM) m m').
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. exact (DJ a n Hin). }
apply K. unfold pe_post_A.
exists m', gp, r, errv, RBS, TBS, LK, B.
split; [apply ret_statew_intro; [exact FS | exact FRM]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [exact ST'|].
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 164 <= fp < 6444320 - 160)) by (intros X; apply FPns; cbn [hl_scratch A4H]; unfold A_TP; lia). lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MU | exact WM |]. unfold LOCCELL_A, A_TP, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 48 <= fp < 6444320 - 40)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc.
assert (O12 : outside [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8)] a).
{ destruct (own_frame_freshG (pa_F pa) LBall LBc LM FRS B A m md HP ltac:(unfold LBall; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as [OFF OFS].
eapply (client_outsideF HIx _ LBall LM ((pa_F pa, 2) :: FRS) _ (LBc ++ LM ++ fr_ivs A4L FRS) _ _ _ (pa_sp0 pa) HP); [ | lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists (pa_F pa), 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]).
+ right. unfold shad, shA; cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_2. unfold A_SB. lia.
+ left. cbn [fst snd]. rewrite fr_size_2. lia. }
cbn [outside] in O12 |- *. destruct O12 as (O1 & O2 & _). split; [exact O1|]. split; [exact O2|]. split; [| exact I].
intros Hfp. assert (a = fp) by lia. subst a. destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr Gf kg HG) as [N1 N2].
+ apply N1. lia.
+ apply N2. exact Hbr. }
split; [exact HP'|].
split. { eapply tokrep_g_agree; [exact TR|]. eapply agree_on_incl; [exact AG|]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; right. apply in_or_app; left. exact Hb. }
split. { destruct RET as [R0 | (Rn & s & J & SD)]; [left; exact R0 | right]. split; [exact Rn|]. exists s. split; [| exact SD].
eapply (jval_agree asegs A4F); [exact J | exact AG |]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; left. exact Hb. }
split. { eapply GA_outside; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; unfold shA, A_SB; lia. }
split; [exact BB | exact BD].
Qed.

Definition PE_OUTW_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (LK : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts ++ LK) LM ((pa_F pa, 2) :: FRS) B m md /\
stk asegs m lo (pf_spf pf) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
heap_presx A4H xlocA (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m /\
model_vm_only (pf_md pf) (cfg_model md) /\
GA m /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_weakA m (t_depth ts) i l) /\
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B /\ pa_dslack pa <= bD B.

Lemma OUTW_of_INVW : forall pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv,
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m md A B ts LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m md A B ts LK cb nb pj sv errv (CORE & (HP & ST & ERR & _ & _ & _ & HPR & MDV & G) & LVW & BB & BD).
split; [exact CORE|]. split; [exact HP|]. split; [exact ST|]. split; [exact ERR|].
split; [eapply heap_presx_weaken; [exact HPR | lia | intros b Hb; exact Hb | intros a Xa; left; exact Xa]|].
split; [exact MDV|]. split; [exact G|]. split; [exact LVW|]. split; [exact BB | exact BD].
Qed.

Lemma lvl_weakA_agree : forall BS m m' depth i l, lvl_weakA m depth i l -> agree_on asegs BS m m' -> incl (lvl_blocks l) BS -> lvl_weakA m' depth i l.
Proof.
intros BS m m' depth i l (R & J & N & C) AG Hi. split; [exact R|]. split.
- eapply (jopt_agree asegs A4F); [exact J | exact AG | intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; left; exact Hb].
- split; [| exact C]. destruct N as [N|N]; [left|right]; (eapply (name_ok_agree asegs); [exact N | exact AG |]; intros b Hb; apply Hi; unfold lvl_blocks; apply in_or_app; right; exact Hb).
Qed.

Lemma lvl_blocks_in_tstate : forall ts i l, nth_error (t_levels ts) i = Some l -> incl (lvl_blocks l) (tstate_blocks ts).
Proof.
intros ts i l Hl b Hb. unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [apply in_map; eapply nth_error_In; exact Hl | exact Hb].
Qed.

Lemma OUTW_locw : forall pf pa q LB0 LM FRS me lo m m1 md A B ts LK cb nb pj sv errv,
PE_STATIC_A HIx pf pa lo ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m md A B ts LK cb nb pj sv errv ->
munch [(LOCCELL_A, LOCCELL_A + 8)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m1 md A B ts LK cb nb pj sv errv.
Proof.
intros pf pa q LB0 LM FRS me lo m m1 md A B ts LK cb nb pj sv errv STC (CORE & HP & ST & ERR & HPRX & MDV & G & LVW & BUD) MU WM MI.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (LBall := pe_blocksA pf q LB0 ts ++ LK) in *.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
assert (LOCR : LOCCELL_A = 6444272) by reflexivity.
assert (BIMG : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(LOCCELL_A, LOCCELL_A + 8)] a n).
{ intros a n Hin. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Hi. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. cbn [disjoint_from]. split; [lia | exact I]. }
assert (AG : agree_on asegs (LBall ++ LM) m m1) by (eapply (agree_of_munch asegs); [exact MU | exact WM | exact BIMG]).
assert (INtk : In (pf_tk pf, 72) (LBall ++ LM)) by (apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (LBall ++ LM)) by (apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INts : incl (tstate_blocks ts) (LBall ++ LM)) by (intros b Hb; apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; left; exact Hb).
split.
{ split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split. { eapply (rw_cells_agree asegs); [exact TOK | exact AG |]. exists (pf_tk pf), 72. split; [exact INtk | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. apply INts. unfold tstate_blocks. apply in_or_app; left. exact Hb. }
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AG |]. exists q, (32 * pf_mxd pf). split; [exact INq|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl). lia. }
destruct FR as (SL & GP & SV & FF & FSH).
split; [| split; [| split; [| split]]].
- eapply rw_cells_transport; [exact SL | exact MU | exact WM |]. rewrite pe_slotsA_size. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact GP | exact MU | exact WM |]. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact SV | exact MU | exact WM |]. cbn [disjoint_from]. split; [right; lia | exact I].
- eapply rw_cells_transport; [exact FF | exact MU | exact WM |]. unfold ff_cellsA. cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I].
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. unfold ffsh_cells, FSH0, shA, A_SB. cbn [cells_size csize Nat.add map length disjoint_from]. split; [right; lia | exact I]. }
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI]. eapply (frame_writes_okFS _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_nil]. right; right; right; right. cbn [fst snd]. intros x Hx. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
split. { eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. left. cbn [outside]. split; [lia | exact I]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO. cbn [cells_size csize Nat.add disjoint_from]. split; [lia | exact I]. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. intros a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I].
intros Hin. destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- lia.
- apply Hx. right. exact Hin.
- assert (OUTI : blk_addr b + blk_size b <= 65536 \/ 6582272 <= blk_addr b).
{ apply in_app_or in Hb as [Hb | Hb].
- destruct b as [ba bn]. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb)) as Hi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H blk_addr blk_size fst snd] in Hi |- *. exact Hi.
- apply in_app_or in Hb as [Hb | Hb].
+ destruct b as [ba bn]. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; right; exact Hb)) as Hi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H blk_addr blk_size fst snd] in Hi |- *. exact Hi.
+ apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd].
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _ & HG0 & _). right. unfold shad. cbn [hl_sb A4L]. unfold A_SB. Z.div_mod_to_equations. lia. }
lia. }
split; [exact MDV|].
split; [exact (GA_loc _ _ G MU WM)|].
split; [| exact BUD].
intros i l Hl. eapply lvl_weakA_agree; [exact (LVW i l Hl) | exact AG |]. intros b Hb. apply INts. exact (lvl_blocks_in_tstate ts i l Hl b Hb).
Qed.

Lemma lb_remove_incl : forall p (LB : list blk), incl (lb_remove p LB) LB.
Proof.
induction LB as [|[a n] LB IH]; intros b Hb; [exact Hb|]. cbn [lb_remove blk_addr fst] in Hb.
destruct (Z.eqb a p); [right; exact Hb|]. destruct Hb as [Hb | Hb]; [left; exact Hb | right; apply IH; exact Hb].
Qed.

Lemma OUTW_call : forall pf pa q LB0 LM LM' FRS me lo m1 m2 md md2 A A2 B B2 ts LK cb nb pj sv errv errv2,
PE_STATIC_A HIx pf pa lo ->
PE_OUTW_A pf pa q LB0 LM FRS me lo m1 md A B ts LK cb nb pj sv errv ->
incl LM' LM ->
model_vm_only (cfg_model md) (cfg_model md2) ->
heap_pres A4H ((pe_blocksA pf q LB0 ts ++ LK) ++ LM' ++ fr_ivs A4L ((pa_F pa, 2) :: FRS)) (pf_spf pf) m1 m2 ->
HEAPA A4L HIx A2 (pe_blocksA pf q LB0 ts ++ LK) LM' ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv2] ->
bB B <= bB B2 -> bD B <= bD B2 ->
PE_OUTW_A pf pa q LB0 LM' FRS me lo m2 md2 A2 B2 ts LK cb nb pj sv errv2.
Proof.
intros pf pa q LB0 LM LM' FRS me lo m1 m2 md md2 A A2 B B2 ts LK cb nb pj sv errv errv2 STC (CORE & HP & ST & ERR & HPRX & MDV & G & LVW & BB & BD) HLM VM HPR HP2 ST2 ERR2 HB HD.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
set (LBall := pe_blocksA pf q LB0 ts ++ LK) in *.
assert (INtk : In (pf_tk pf, 72) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) LBall) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
assert (INts : incl (tstate_blocks ts) LBall) by (intros b Hb; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; left; exact Hb).
assert (AG : agree_on asegs LBall m1 m2).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPR | reflexivity |]. intros b Hb. apply in_or_app; left. exact Hb. }
split.
{ split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|].
split. { eapply (heap_pres_rw_cells A4H); [exact HPR | exact TOK |]. eapply client_range_block; [apply in_or_app; left; exact INtk | lia | cbn; lia]. }
split. { eapply (pbuf_agree asegs); [exact PB | exact AG |]. intros b Hb. apply INts. unfold tstate_blocks. apply in_or_app; left. exact Hb. }
split; [exact Hpb|].
split. { eapply (tstack_pres_g A4H); [exact HPR | apply in_or_app; left; exact INq | exact LEN32 | exact TSK]. }
eapply (pe_frameA_pres pf pa _ _ _ _ _ _ _ _ HPR); [lia | exact GEO | | | exact FR].
- apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity.
- apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; reflexivity. }
split; [exact HP2|]. split; [exact ST2|]. split; [exact ERR2|].
split.
{ eapply heap_presx_trans; [eapply heap_presx_weaken; [exact HPRX | lia | | intros a Xa; exact Xa] |].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply HLM; exact Hb | apply in_or_app; right; exact Hb].
- eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
split; [eapply model_vm_only_trans; [exact MDV | exact VM]|].
split; [eapply GA_pres; [exact HPR | exact G]|].
split; [| split; lia].
intros i l Hl. eapply lvl_weakA_agree; [exact (LVW i l Hl) | exact AG |]. intros b Hb. apply INts. exact (lvl_blocks_in_tstate ts i l Hl b Hb).
Qed.
End PeSOutB.
End RC__1.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0 Qdyh.Mq3 Qdyh.Mq4 QIsM.Mq2 Qa8x.Mq2 Qdyh.Mq0 Qu4M.Mq0.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QYZ0.Mq8 QlKV.Mqh QsKa.Mqe Qoif.Mq4 Qeia.Mq6 QYZ0.Mq9 QWrz.Mq3 QdGy.Mqe Q63E.Mqc Qt1H.Mq5.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import QEUF.Mq3.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOvaddB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.

Ltac pe_openA STC INV :=
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & RR & LENR); pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk);
destruct INV as [CORE REST];
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR);
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).

Ltac shq_facts HP INq INtk q mxd tk dz j SH SEPc SEPq SEPt :=
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd dz j HP INq ltac:(lia) ltac:(lia)) as SH;
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) q (32 * mxd) HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INq))) as (SEPc & SEPq & _);
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (32 * mxd) (4 * dz + j) tk 72 HP INq ltac:(lia) (in_or_app _ _ _ (or_introl INtk))) as (_ & SEPt & _);
cbn [hl_sb A4L] in SEPc, SEPq, SEPt.

Lemma seg_ovadd_B :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel) (kids : list (option jshape))
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat) (v2 ra2 : Z)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> BOK pf pa ts B (S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + nB)) ->
pj_obj pj = Z_to_bv 64 (t_obj ts) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_ovadd ->
tl_cs l = Some (Sobj kids) ->
frm0 fc -> Z.of_nat (length FRS) + 2 < 4096 ->

pe_s0 sv = Z_to_bv 64 v2 -> pe_ra sv = Z_to_bv 64 ra2 ->
(v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64 ->
uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94e48) (UWfp ra2 v2) ->

(forall m' md' A' B' cbs' kids' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
Z.of_nat (length kids') <= Z.of_nat (length kids) + 1 ->
okmax kids' <= Z.max (okmax kids) (odep (t_objs ts)) ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) cb nb pj sv errv' ->
PBOK m' (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) kP ->
BOK pf pa (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []) B' nB ->
(forall w wv nm nn, tl_nbs l = [(nm, nn)] -> jtx (Sobj kids) (tl_cbs l) = Some (w, []) -> jtx_opt (t_objs ts) (t_objbs ts) = Some (wv, []) ->
exists w', jtx (Sobj kids') cbs' = Some (w', []) /\ w' <= w + key_w nn + wv) ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' md' A' B' LK errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc',
PE_INVW_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts LK cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msO asegs pf pa APE_ERRMEM gp t0' t1' t2' (Z_to_bv 64 (pf_tk pf + 36)) a1' a2' a3' a4' a5' a6' a7' s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3' t4' t5' t6' F' fc' m')) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_ovadd) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK BK OBJW Hl Hst Hcs FRM FRN S0V RAV HV UWK Kredo Kerr16. pose proof INV as INV0. pe_openA STC INV.
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR as FR0. unfold pe_frameA in FR. destruct FR as (SLOTS & GAP & SAVED & FF & FSH).
unfold pe_slotsA in SLOTS. cbn zeta in SLOTS. unfold ff_cellsA in FF.
unfold pe_msA, pe_msO in *.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in *.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (tok_shadowA HIx _ _ _ _ _ _ _ _ HP INtk) as SHT.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m) as WM.
pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
pose proof (TSK depth l Hl) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
pose proof (stack_shadowA HIx _ _ _ _ _ _ _ q mxd (Z.of_nat depth) 0 HP INq ltac:(lia) ltac:(lia)) as SHQ.
replace (q / 8 + 4 * Z.of_nat depth + 0 + A_SB) with (q / 8 + 4 * Z.of_nat depth + A_SB) in SHQ by lia.
assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (SHQ4 : ro_cells asegs m (bse / 8 + A_SB) [C1 (Z_to_bv 8 0)]).
{ replace (bse / 8) with (q / 8 + 4 * Z.of_nat depth) by (subst bse; rewrite div8_add_mul32 by lia; lia). exact SHQ. }
pose proof (munch_refl [(bse, bse + 32)] m) as MU.
pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 2 SHQ2 SEPQ2c SEPQ2q SEPQ2t.
replace (q / 8 + 4 * (Z.of_nat depth) + 2 + A_SB) with (bse / 8 + 2147450882) in SHQ2 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 2) = bse / 8 + 2147450882) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ2c, SEPQ2q, SEPQ2t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
unfold APE_BREAK, APE_REDO, APE_OUT, APE_ERRMEM, APE_JTAB in *. unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (MODE0 : c0 = CObj /\ hn0 = true).
{ rewrite Hst, (Qdyh.Mq0.lvl_mode_ovadd (tl_ss l)) in Hmode. injection Hmode as <- <-. split; reflexivity. }
destruct MODE0 as (-> & ->). cbn [name_ok] in NM0. destruct NM0 as (Hn0 & nn & ks & Hnbs0 & Hnn & CSTR0).
destruct pj as [pj0 pj8 pj16 pjobj pj288 pj304 pjgap pjfhd pjf1 pjf2]. cbn [pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pj_gap pj_fhd pj_f1 pj_f2] in *. subst pjobj.
clear Hdtq SEPQ2c SEPQ2q SEPQ2t SEPQ3c SEPQ3q SEPQ3t.
stash Himg_t. stash Himg_q. clear PB REST TSK HP LV OBJ HPR BUD GAP SAVED FSH.
reenterA asegs A4L HIx asegs_wx HP. rewrite Hst. unfold ST_ovadd. cbn [pe_jtA].
replace (q + 32 * Z.of_nat depth) with bse by lia.
step.
asan_chkB.
step.
asan_chkB.
do 4 step.
step.
evt_done5. subst bse.
eapply (pe_oadd_c HIx GA GA_presx GA_lh HD HD_le OADD (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m md A B ts0 l kids cb nb _ sv errv T kP nB);
[exact STC | exact BSL | exact INV0 | exact PBK | exact BK | exact Hl | exact Hst | exact Hcs | exact FRM | exact FRN | rewrite unsigned_lit by lia; reflexivity |].
intros m2 md2 A2 B2 errv2 r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 F2 fc2 OUT FS2 FRM2.
clear TOK SLOTS FF SHT SHQ SHQ4 SHQ2 SHQ3 Ld MU WM MI Htal Htlo Hthi Hqal Hqlo Hqhi Hqtk INtk INq HbseR Hb8.
destruct OUT as [(-> & cbs2 & kids2 & INV2 & PBK2 & LENK & DEPK & BK2 & JX2) | (-> & LK & INVW2)].
- set (l2 := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) (tl_nbs l)) in *.
set (TS2 := ts_lvl_obj ts0 l2 0 None []) in *.
assert (Hd : (depth < length levels)%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
assert (Hl2 : nth_error (t_levels TS2) (t_depth TS2) = Some l2) by (unfold TS2, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; exact Hd).
clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INV2 as INV2'. destruct INV2' as [CORE2 REST2].
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & TSK & FR).
pose proof REST2 as (HP & _). clear REST2.
unfold TS2, ts_lvl_obj, ts0 in TOK, TSK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK, TSK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 TS2)) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
pose proof (TSK depth l2 ltac:(apply nth_error_lupd_eq; exact Hd)) as Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld. unfold srec_cells in Ld. cbn [tl_st tl_ss tl_cur tl_name l2] in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] m2) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
clear SEPQ3c SEPQ3q SEPQ3t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (subst bse; lia). assert (Hb8 : bse mod 8 = 0) by (subst bse; clear - Hqal; Z.div_mod_to_equations; lia).
stash Himg_t2. stash Himg_q2. stash TSK. stash INV2.
reenterA asegs A4L HIx asegs_wx HP.
step. if_true.
step. step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero. do 2 step. step. if_true.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
step. step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
step.
step.

evt_done5. unstash INV2.
pose proof (PE_NWIN_open HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md2 A2 B2 TS2 cb nb _ sv errv2 l2 INV2 Hl2 eq_refl) as WIN0.
cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name tl_nbs l2] in WIN0. rewrite Hnbs0 in WIN0.
set (ln := TL (tl_st l) (tl_ss l) (tl_cur l) (Some (Sobj kids2)) cbs2 (tl_name l) []) in *.
set (TSn := ts_lvl TS2 ln) in *.
assert (COST : 512 <= bB B2).
{ pose proof (BK2 (tl_st l) (tl_ss l) 0 None ltac:(right; rewrite Hst; reflexivity)) as BKx.
fold l2 TS2 in BKx. eapply (BOK_blk_512 _ _ _ _ _ (tl_name l, nn) BKx BSL). unfold tstate_blocks. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l2). split; [apply in_map; eapply nth_error_In; exact Hl2 | unfold lvl_blocks; apply in_or_app; right; cbn [tl_nbs l2]; rewrite Hnbs0; left; reflexivity]. }
eapply (pe_free_name_n HIx GA GA_pres (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m2 md2 A2 B2 TSn cb nb _ sv errv2 T (co + kP) v2 ra2 (tl_name l) nn);
[exact STC | exact WIN0 | unfold TSn; apply (PBOKat_same m2 TS2); [reflexivity | reflexivity | exact PBK2] | exact COST | exact S0V | exact RAV | exact HV
| exact UWK | rewrite unsigned_lit by lia; reflexivity |].
intros m3 md3 A3 r3 v0 v1 v2' v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 WIN3 PBK3.
cbn [pf_spf] in *. unfold A_TP in *.
clear TOK SLOTS Ld SHQ3 SHT7 SHT2 MU WM MI HP INtk INq Htal Htlo Hthi Hqal Hqlo Hqhi WIN0 INV2 PBK2 COST.
pose proof WIN3 as (COREx & BASEx & _). destruct COREx as (_ & _ & _ & _ & TOK & _ & _ & TSK3 & FR3). pose proof (proj1 BASEx) as HP. clear BASEx.
unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
pose proof FR3 as (SLOTS & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []))) by (unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * mxd) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []))) by (unfold pe_blocksA; apply in_or_app; right; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t3.
blk_factsA A4L HIx HP q (32 * mxd) Hqal Hqlo Hqhi Himg_q3.
pose proof (q_ne_tkA HIx _ _ _ _ _ _ _ _ _ _ HP) as Hqtk. cbn [pf_tk] in Hqtk.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tk 72 q (32 * mxd) HP (in_or_app _ LM _ (or_introl INtk)) (in_or_app _ LM _ (or_introl INq)) ltac:(congruence)) as Hdtq.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m3) as WM.
assert (Hln : nth_error (t_levels TSn) (t_depth TSn) = Some ln) by (unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite lupd_length; exact Hd).
pose proof (TSK3 depth ln Hln) as Ld. rewrite <- Hbse in Ld. unfold srec_cells, ln in Ld. cbn [tl_st tl_ss tl_cur tl_name] in Ld.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 0 SHQ0 SEPQ0c SEPQ0q SEPQ0t.
replace (q / 8 + 4 * (Z.of_nat depth) + 0 + A_SB) with (bse / 8 + 2147450880) in SHQ0 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 0) = bse / 8 + 2147450880) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ0c, SEPQ0q, SEPQ0t. clear EQx.
shq_facts HP INq INtk q mxd tk (Z.of_nat depth) 3 SHQ3 SEPQ3c SEPQ3q SEPQ3t.
replace (q / 8 + 4 * (Z.of_nat depth) + 3 + A_SB) with (bse / 8 + 2147450883) in SHQ3 by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia).
assert (EQx : q / 8 + A_SB + (4 * (Z.of_nat depth) + 3) = bse / 8 + 2147450883) by (rewrite Hbse, div8_add_mul32 by lia; unfold A_SB; lia). rewrite EQx in SEPQ3c, SEPQ3q, SEPQ3t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 7 HP INtk ltac:(lia)) as SHT7.
replace (tk / 8 + 7 + A_SB) with (tk / 8 + 2147450887) in SHT7 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT7c & SEPT7q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 7 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT7t & _).
cbn [hl_sb A4L] in SEPT7c, SEPT7q, SEPT7t. assert (EQx : tk / 8 + A_SB + 7 = tk / 8 + 2147450887) by (unfold A_SB; lia). rewrite EQx in SEPT7c, SEPT7q, SEPT7t. clear EQx.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 2 HP INtk ltac:(lia)) as SHT2.
replace (tk / 8 + 2 + A_SB) with (tk / 8 + 2147450882) in SHT2 by (unfold A_SB; lia).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 q (32 * mxd) HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INq))) as (SEPT2c & SEPT2q & _).
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ tk 72 2 tk 72 HP INtk ltac:(lia) (in_or_app _ LM _ (or_introl INtk))) as (_ & SEPT2t & _).
cbn [hl_sb A4L] in SEPT2c, SEPT2q, SEPT2t. assert (EQx : tk / 8 + A_SB + 2 = tk / 8 + 2147450882) by (unfold A_SB; lia). rewrite EQx in SEPT2c, SEPT2q, SEPT2t. clear EQx.
pose proof (munch_refl [(bse, bse + 32)] m3) as MU.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
assert (cs_tk_L : csep tk 72 bse (Z.of_nat 32)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_L_tk : csep bse 32 tk (Z.of_nat 72)) by (unfold csep; clear - Hdtq HbseR; lia).
assert (cs_Q0_L : csep (bse / 8 + 2147450880) 1 bse (Z.of_nat 32)) by (unfold csep; clear - SEPQ0q HbseR; lia).
clear Hdtq SEPQ0c SEPQ0q SEPQ0t SEPQ3c SEPQ3q SEPQ3t SEPT7c SEPT7q SEPT7t SEPT2c SEPT2q SEPT2t.
stash Himg_t3. stash Himg_q3. stash WIN3. stash TSK3. stash FR3.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
reenterA asegs A4L HIx asegs_wx HP.
step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_true.
step. step. rewrite ?sxb_zero, ?zxb_zero. do 3 step. step. if_true.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
do 3 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_truex.
step. ub_land Hb8. step. ub_if_lit.
clear SHT7 SHT2.
step.
asan_chkB.
clear SHQ3.
stepz.
step. if_truex.
step.
asan_chkB.
step.
stepz.
asan_chkB.
stepz.
step.

set (lf := TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids2)) cbs2 0 []).
unstash WIN3. unstash TSK3. unstash FR3.
assert (Hlen3 : length (t_levels TSn) = Z.to_nat mxd) by (unfold TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; rewrite !lupd_length; exact LEN32).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m3 mc, WMc : wmono asegs m3 mc, MIc : mem_inv asegs mc, TOKc : rw_cells asegs mc tk _, Lc : rw_cells asegs mc bse _ |- _ =>
evt_done5;
assert (INqL : Forall (fun iv => exists a n, In (a, n) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 (tsF TSn []) ++ LM) /\ a <= fst iv /\ snd iv <= a + n) [(bse, bse + 32)])
by (apply Forall_cons; [exists q, (32 * mxd); cbn [fst snd]; split; [apply in_or_app; left; exact INq | lia] | apply Forall_nil]);
assert (FRc : pe_frameA asegs mc (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) cb nb (PEJA pj0 pj8 pj16 (Z_to_bv 64 obj) pj288 pj304 pjgap pjfhd pjf1 pjf2) sv)
by (eapply (pe_frameA_blkwriteG HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) _ LM FRS (charge B2 512 0) A3 m3 mc md3 lo [(bse, bse + 32)] cb nb _ sv); [exact STC | exact HP | exact INqL | exact FR3 | exact MUc | exact WMc]);
assert (TSKc : tstack asegs mc q (lupd (t_levels TSn) (t_depth TSn) lf))
by (rewrite Hbse in MUc, Lc; eapply (tstack_put asegs m3 mc q (t_levels TSn) depth lf []);
[exact TSK3 | rewrite Hlen3; lia | exact MUc | exact WMc | intros; exact I | exact Lc]);
destruct (PE_NWIN_write HIx GA GA_outside (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo m3 mc md3 A3 (charge B2 512 0) TSn []
cb nb _ sv errv2 [(bse, bse + 32)] ln lf cb nb _ STC WIN3 Hln MUc WMc MIc
ltac:(apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia | apply Forall_nil])
TOKc TSKc FRc ltac:(unfold lf, ST_eatws; cbn [tl_st]; lia) ltac:(unfold lf, ST_osep; cbn [tl_ss]; lia) eq_refl eq_refl eq_refl eq_refl) as (WIN4 & PBT4 & _)
end end.
set (TSf := ts_lvl TSn lf) in *.
assert (Hlf : nth_error (t_levels TSf) (t_depth TSf) = Some lf) by (unfold TSf, TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth]; apply nth_error_lupd_eq; rewrite !lupd_length; exact Hd).
assert (ETS : ts_lvl TSf lf = ts_lvl_obj ts0 lf 0 None []).
{ unfold TSf, TSn, TS2, ts_lvl, ts_lvl_obj, ts0; cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs]. rewrite !lupd_lupdS. reflexivity. }
assert (BK4 : BOK (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) (ts_lvl_obj ts0 lf 0 None []) (charge B2 512 0) nB).
{ pose proof (BK2 (tl_st l) (tl_ss l) 0 None ltac:(right; rewrite Hst; reflexivity)) as BKx. fold l2 TS2 in BKx.
pose proof (BOK_name_free (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) TS2 B2 (charge B2 512 0) nB l2 (tl_name l, nn) ST_eatws ST_osep 0 BKx Hl2 ltac:(cbn [tl_nbs l2]; exact Hnbs0)
ltac:(intros CL; exfalso; rewrite (lvl_closed_open_st l2) in CL; [discriminate CL | cbn [tl_st l2]; rewrite Hst; reflexivity])
ltac:(cbn; lia) ltac:(cbn; lia)) as BKy.
cbn [tl_cur tl_cs tl_cbs l2] in BKy. unfold TS2, ts_lvl, ts_lvl_obj, ts0 in BKy |- *. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in BKy |- *.
rewrite lupd_lupdS in BKy. exact BKy. }
pose proof (PE_NWIN_close HIx GA (PEF tk oldl newl len lenr sb spf pmd mxd fl) (PEFA sp0 Ff oldloc newloc bsl dsl) q LB0 LM FRS payload me lo _ md3 A3 (charge B2 512 0) TSf [] cb nb _ sv errv2 lf CObj false WIN4 Hlf
ltac:(vm_compute; reflexivity) I ltac:(cbn [name_ok tl_name tl_nbs lf]; split; reflexivity) ltac:(reflexivity)
ltac:(cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name lf]; fold lf; rewrite ETS; exact (BOK_weak _ _ _ _ _ BK4))) as INV5.
cbn [tl_st tl_ss tl_cur tl_cs tl_cbs tl_name lf] in INV5. fold lf in INV5. rewrite ETS in INV5.
pose proof (PE_INV_A_set_obj HIx GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ obj objs INV5 eq_refl
ltac:(rewrite (cur_st_lvl_obj ts0 l _ _ _ _ Hl); exact I)) as INV6.
pose proof (PBT4 _ PBK3) as P4.
eapply (Kredo _ md3 A3 (charge B2 512 0) cbs2 kids2 errv2); [exact LENK | exact DEPK | exact INV6 | eapply (PBOKat_same _ TSf); [reflexivity | reflexivity | exact P4] | | exact JX2 | exact FS2 | exact FRM2].
exact (BOK_obj_irrel _ _ _ _ _ _ _ _ _ _ BK4).
- clear INV0 PBK BK.
cbn [pf_spf] in *. unfold A_TP in *.
pose proof INVW2 as (CORE2 & BASE2 & _).
destruct CORE2 as (_ & _ & _ & _ & TOK & _ & _ & _ & FR).
pose proof (proj1 BASE2) as HP. clear BASE2.
unfold ts0 in TOK. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd pf_fl] in TOK.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
unfold pe_frameA in FR. destruct FR as (SLOTS & _ & _ & _ & _). unfold pe_slotsA in SLOTS. cbn zeta in SLOTS.
cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS.
assert (INtk : In (tk, 72) (pe_blocksA (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0 ++ LK)) by (apply in_or_app; left; unfold pe_blocksA; apply in_or_app; right; left; reflexivity).
blk_factsA A4L HIx HP tk 72 Htal Htlo Hthi Himg_t2.
pose proof (tok_granA HIx _ _ _ _ _ _ _ tk 4 HP INtk ltac:(lia)) as SHT4.
replace (tk / 8 + 4 + A_SB) with (tk / 8 + SB4) in SHT4 by (unfold SB4, A_SB; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (wmono_refl asegs m2) as WM.
unfold shA in *. a4l. unfold SB2, SB4, SB7, SB8 in *.
stash Himg_t2.
reenterA asegs A4L HIx asegs_wx HP.
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
step.
if_false.
step.
step.
step. rewrite ?sxb_zero, ?zxb_zero. do 2 step. step. if_true.
evt_done5.
eapply (Kerr16 m2 md2 A2 B2 LK errv2); [exact INVW2 | exact FS2 | exact FRM2].
Qed.
End PeSOvaddB.
End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import QG8z Qdyh.Mq0.
Import Qhd4 Qwm6.
Import QbFI.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QSHS Ql4f.Mq4 Q1Y6.Mq4 QsKa.Mqh QrQv.Mq4 QEUF.Mq2 QdGy.Mq9 QfHY Qkko.Mq3 QlmN.Mq3 QlmN.Mq4 QVob.Mq1.
Import Qc5u QAzu.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSSescA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.

Lemma seg_sesc_A :
forall (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (l : tlevel)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) (T : TSet) (kP : Z) (nB : nat)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo -> 0 <= pa_bslack pa ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv -> PBOK m ts kP -> kP + 1 <= 1 -> BOK pf pa ts B (S nB) ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_string_escape ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode (tl_ss l) (tl_ss l) = Some (c, hn)) ->
(forall c hn, lvl_mode (tl_st l) (tl_ss l) = Some (c, hn) -> lvl_mode ST_escape_unicode (tl_ss l) = Some (c, hn)) ->
zin (tl_ss l) [ST_array_add; ST_ovadd] = false ->

(forall m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B'
(ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (kP + 1) ->
BOK pf pa (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' nB ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' (Z_to_bv 64 2) s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall m' a0' a1' a3' a4' a5' a6',
bv_unsigned cb = 117 ->
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md A B
(ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts))))
(TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv ->
PBOK m' (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts))))
(TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) kP ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0' a1' (Z_to_bv 64 0) a3' a4' a5' a6' a7 s3 (Z_to_bv 64 2) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m')) ->

(forall m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc',
PE_INV_A HIx GA pf pa q LB0 LM FRS payload me lo m' md' A' B' ts cb nb pj sv errv' ->
fsaved F F' -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msX asegs pf pa APE_ERR3 x1' gp' t0' t1' t2' (Z_to_bv 64 16) a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m')) ->

(forall a5' a6',
AJ5 A4L HIx A T md
(pe_msX asegs pf pa APE_ERR3 (Z_to_bv 64 (pf_tk pf / 8 + SB2)) gp t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (pf_tk pf + 32)) (Z_to_bv 64 12) (Z_to_bv 64 (bv_unsigned cb)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5' a6' a7 s3 (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m)) ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA ST_string_escape) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
Proof.
intros until fc. intros STC BSL INV PBK HkP BK Hl Hst HMODE HMODE10 Hzss Kbreak Kbrku Kerr16 Kerr12.
eapply (sesc_dispatch_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. intros a5' a6'.
destruct (pe_jt3A_cases (bv_unsigned cb)) as [[E C] | [[E C] | [[E C] | E]]]; rewrite E.
- eapply (sesc_quote_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
- eapply (sesc_u_A HIx GA GA_outside pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP);
[exact STC | exact INV | exact PBK | exact Hl | exact Hst | exact HMODE10 |].
intros m' b0 b1 b3 b4 b6 INV' PBK'. eapply (Kbrku m'); [exact C | exact INV' | exact PBK'].
- eapply (sesc_hash_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T (bv_unsigned cb)); [exact STC | exact INV | exact C |].
intros a0' a1'.
destruct C as [C | [C | [C | [C | C]]]]; rewrite C; cbn [pe_jt4A].
+ eapply (sesc_lit_b_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_f_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_n_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_r_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
+ eapply (sesc_lit_t_A HIx GA GA_outside GA_pres MAPP pf pa q LB0 LM FRS payload me lo m md A B ts l cb nb pj sv errv T kP nB);
[exact STC | exact BSL | exact INV | exact PBK | exact HkP | exact BK | exact Hl | exact Hst | exact HMODE | exact Hzss | exact Kbreak | exact Kerr16].
- eapply (sesc_default_A HIx GA pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. apply Kerr12.
Qed.
End PeSSescA.
End RC__1.
End Mqa.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZ8V.
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

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n q d Fr).
Notation st_escx := (st_escA sp gp Sa n q).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Local Notation esc_srcA := (QZ8V.esc_srcA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src q d Fr INs Hs1 Hs2 SRC0 SRCL).
Local Notation esc_fetchA := (QZ8V.esc_fetchA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr INs Hs1 Hs2 SRC0 SRCL Hn).
Local Notation esc_appendA := (QZ8V.esc_appendA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED).
Local Notation esc_inv_sbx := (QZ8V.esc_inv_sbx HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n q d Fr).
Local Notation esc_inv_privA := (QZ8V.esc_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src q d Fr Hd Hq Hq32 LO LOS HT CAP0).
Local Notation esc_inv_shA := (QZ8V.esc_inv_shA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src q d Fr Hd Hq Hq32 LO LOS HT CAP0).
Local Notation esc_ctrl_appA := (QZ8V.esc_ctrl_appA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED Hn).

Definition esc_hexA : list byte := Eval vm_compute in match image_bytes asegs 0x23380 16 with Some bs => bs | None => [] end.
Lemma esc_hex_shadowA : forall A LBx LMx FRx B m md g, HEAPAx A LBx LMx FRx B m md -> g = 18032 \/ g = 18033 ->
ro_cells asegs m (g + 2147450880) [C1 (b8 0)].
Proof.
intros A LBx LMx FRx B m md g HP Hg. apply QsKa.Mqa.ro_C1_of_bytes_at.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP) as X.
assert (E : img_shadow_val (hl_reg_globals A4L) g = 0) by (destruct Hg as [-> | ->]; vm_compute; reflexivity). rewrite E in X.
cbn [hl_sb A4L hl_img_lo hl_img_hi hla_base A4H] in X. unfold A_SB in X.
apply X; destruct Hg as [-> | ->]; vm_compute; discriminate.
Qed.

Lemma esc_ctrl_hexA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos e cz : Z),
esc_invx 7 A e m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n -> 0 <= e <= 6 * pos -> 0 <= cz < 32 ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx 0xa1ee8 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz cz) t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until cz. intros INV FS FR Hpos He Hcz IH EX.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [FFx CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, FFx, SHx. unfold escLoc in LOC. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HTLE. unfold AESC_STACK in LOS. unfold usp in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).

assert (JH : JHEX_A m) by (eapply JHEX_A_pres; [exact HPR | exact JHEX0]).
pose proof (ro_C8_of_bytes_at asegs _ _ _ JH) as JHC. unfold A_JHEX_SLOT, A_JHEX in JHC.
assert (HEXB : bytes_at asegs m 0x23380 esc_hexA) by (apply QUrr.rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
set (hi := Z.shiftr cz 4). set (lo4 := Z.land cz 15).
assert (Hhi : 0 <= hi <= 1).
{ unfold hi. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. clear - Hcz. split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
assert (Hlo4 : 0 <= lo4 <= 15).
{ unfold lo4. replace (Z.land cz 15) with (cz mod 16) by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity). pose proof (Z.mod_pos_bound cz 16 ltac:(lia)). lia. }
destruct (nth_error esc_hexA (Z.to_nat hi)) as [ch1|] eqn:N1; [| apply nth_error_None in N1; cbn [esc_hexA length] in N1; lia].
destruct (nth_error esc_hexA (Z.to_nat lo4)) as [ch2|] eqn:N2; [| apply nth_error_None in N2; cbn [esc_hexA length] in N2; lia].
pose proof (QSHS.payload_byteA _ _ _ _ _ HEXB N1 ltac:(lia)) as RD1.
pose proof (QSHS.payload_byteA _ _ _ _ _ HEXB N2 ltac:(lia)) as RD2.
pose proof (esc_hex_shadowA _ _ _ _ _ _ _ 18032 HP ltac:(left; reflexivity)) as SHG0.
pose proof (esc_hex_shadowA _ _ _ _ _ _ _ 18033 HP ltac:(right; reflexivity)) as SHG1.
change (18032 + 2147450880) with 2147468912 in SHG0. change (18033 + 2147450880) with 2147468913 in SHG1.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.

assert (SNPK : evt asegs (AJ5e A4L HIx A T md)
(MS (mkR (Z_to_bv 64 663388) (Z_to_bv 64 q) gp (Z_to_bv 64 6444320) t0 t1 t2 sp (Z_to_bv 64 q)
(Z_to_bv 64 (Fr + 32)) (Z_to_bv 64 7) (Z_to_bv 64 145152) (Z_to_bv 64 (bv_unsigned ch1)) (Z_to_bv 64 (bv_unsigned ch2)) a5 a6 a7
(Z_to_bv 64 0) (Z_to_bv 64 pos) (Z_to_bv 64 Sa) (Z_to_bv 64 ESC_MASK) (Z_to_bv 64 (n - pos)) (Z_to_bv 64 1) (Z_to_bv 64 pos)
(Z_to_bv 64 (Sa + pos)) (Z_to_bv 64 2147450880) (Z_to_bv 64 cz) t3 t4 t5 t6)
F' (Z_to_bv 64 327028) fc' None m (seg_rom asegs))).
{ apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFe FFb]. cbn [cells_size csize Nat.add] in FFe, FFb.
change (Z.of_nat 32) with 32 in FFe, FFb. change (Fr + 32 + Z.of_nat 7) with (Fr + 32 + 7) in FFb.
assert (SBL : length sb = 7%nat) by (destruct FFe as [[[Hwf _] _] _]; exact Hwf).
destruct (sbuf7_shadow_word m _ SHx) as [SHW7 _].
pose proof (OBL_PFRT _ _ _ _ _ _ _ HP) as RT.
pose proof (bv_unsigned_in_range 8 ch1) as C1R; unfold bv_modulus in C1R; cbn in C1R.
pose proof (bv_unsigned_in_range 8 ch2) as C2R; unfold bv_modulus in C2R; cbn in C2R.
eapply evt_cut.
{ eapply (SNP_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m (Fr + 32) 7 (bv_unsigned ch1) (bv_unsigned ch2) 7%nat sb lo);
[ | reflexivity | exact C1R | reflexivity | exact C2R | reflexivity ].
unfold isnp_pre, SNP_STACK_A. rewrite ?unsigned_lit by lia.
split; [reflexivity|]. split; [reflexivity|]. split; [exact FFe|]. split; [exact RT|].
split; [lia|]. split; [lia|]. split; [exact ST|]. split; [lia|]. split; [unfold alloc_ceiling in OBL_PFLO; lia|]. split; [lia|].
split; [exact MI|]. split; [exact FR|]. split; [left; lia|].
split; [unfold dappJ; destruct HFapp; [left | right]; lia|].
intros k Hk. eapply (rng_okJ_sbuf7 m Fr k HFal); [lia | lia | unfold A_SB; exact SHW7 | lia]. }
intros ms3 (x0 & x1' & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F3 & fc3 & m3 & r & o & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & Hr & Ho & FFe3).
rewrite ?unsigned_lit in MU3, ST3 by lia.
assert (FS3 : fsaved F F3).
{ eapply fsaved_trans; [exact FS|]. intros k Hk. apply FREG3. cbn in Hk. repeat (destruct Hk as [<- | Hk]; [vm_compute; discriminate|]). destruct Hk. }
assert (OL : length o = 6%nat) by (rewrite Ho; reflexivity).
assert (INV3 : esc_inv_sbx 7 (o ++ [b8 0]) A e m3 md).
{ unfold escLoc in LOC.
lazymatch type of LOC with rw_cells _ _ _ (C8 j0 :: ?rest) =>
change (C8 j0 :: rest) with ([C8 j0] ++ rest) in LOC; apply (proj1 (rw_cells_app asegs _ _ [_] _)) in LOC; destruct LOC as [LOCh LOCt];
cbn [cells_size csize Nat.add] in LOCt; change (Z.of_nat 8) with 8 in LOCt end.
eapply (esc_inv_privA 7 7 A e m m3 md _ j0 j1 gj j8 sb j17 j0 j8 (o ++ [b8 0]) j17); [exact INV1 | exact MU3 | exact WM3 | exact MI3 | | | | | exact ST3].
- constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
- eapply (rw_cells_transport asegs _ m m3); [exact LOCh | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
- unfold escFF.
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] => change [c1; c2; c3; c4; c5; c6] with ([c1; c2; c3; c4] ++ ([c5] ++ [c6])) end.
apply rw_cells_app. split.
+ eapply (rw_cells_transport asegs _ m m3); [exact FFa | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
+ cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. apply rw_cells_app. split.
* replace (o ++ [b8 0]) with (o ++ Z_to_bv 8 0 :: skipn (S (length o)) sb); [exact FFe3|].
f_equal. f_equal. rewrite OL. apply skipn_all2. rewrite SBL. lia.
* cbn [cells_size csize Nat.add]. change (Fr + 32 + Z.of_nat 7) with (Fr + 32 + 7).
eapply (rw_cells_transport asegs _ m m3); [exact FFb | exact MU3 | exact WM3 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
- eapply (rw_cells_transport asegs _ m m3); [exact SHx | exact MU3 | exact WM3 |]. unfold escSH. cbn [disjoint_from cells_size csize Nat.add].
assert (HH : Fr + 64 + 8 <= 2147450880 \/ 17594333495296 <= Fr) by (destruct HFapp as [H|H]; [left; exact H | right; exact H]).
clear - SHR HH LO ACR. revert SHR. generalize (Fr / 8 + 2147450880). intros shv SHR. unfold alloc_ceiling in *. lia. }
replace (ret_pc (Z_to_bv 64 663388)) with (Z_to_bv 64 663388) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
eapply esc_ctrl_appA with (o := o); [exact INV3 | exact OL | exact FS3 | exact FRM3 | exact Hpos | exact He | exact IH | exact EX]. }

step. step. step. step.
rewrite (unsigned_lit cz) by lia. fold hi.

step. if_falsex.
step. step. ub_nzpair 144256 (144256 + hi). step. rewrite ?(unsigned_lit 1), ?(unsigned_lit 0) by lia. change (Z.lxor 1 0) with 1. step. if_lit. step. if_lit.
step. rewrite (unsigned_lit cz) by lia. fold lo4.
step. step. if_falsex.

step. step. sh_norm. replace ((144256 + hi) / 8 + 2147450880) with 2147468912 by (clear - Hhi; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. if_lit.

step.
step. step. sh_norm.
destruct (Z.lt_ge_cases lo4 8) as [L8 | G8].
- replace ((144256 + lo4) / 8 + 2147450880) with 2147468912 by (clear - Hlo4 L8; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. change (zxb ch1) with (Z_to_bv 64 (bv_unsigned ch1)). step. if_lit.
step. change (zxb ch2) with (Z_to_bv 64 (bv_unsigned ch2)).
step. step. step. step. step. fold_mkR. exact SNPK.
- replace ((144256 + lo4) / 8 + 2147450880) with 2147468913 by (clear - Hlo4 G8; Z.div_mod_to_equations; lia).
step. rewrite sxb_zero. step. change (zxb ch1) with (Z_to_bv 64 (bv_unsigned ch1)). step. if_lit.
step. change (zxb ch2) with (Z_to_bv 64 (bv_unsigned ch2)).
step. step. step. step. step. fold_mkR. exact SNPK.
Qed.

Lemma esc_iter_ctrlA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 x21 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (md : config)
(A : ASA A4L HIx) (pos start e : Z) (c : byte),
esc_invx 248 A e m md -> fsaved F F' -> frm0 fc' ->
0 <= start <= pos -> pos < n -> 0 <= e <= 6 * start ->
nth_error src (Z.to_nat pos) = Some c ->
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
loopKx (n - pos - 1) -> exitKx ->
AJ5 A4L HIx A T md (st_escx AESC_LOOP x1 t0 t1 t2 a0 a1 a2 a3 a4 (wz start) (wz pb) (wz 47) x21 t3 t4 t5 t6 F' fc' m pos).
Proof.
intros until c. intros INV FS FR Hst Hpos He Hc C32 CN IH EX.
eapply esc_fetchA; [exact INV | lia | exact Hc |]. intros a1' a2'.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
set (cz := bv_unsigned c) in *. clearbody cz.
assert (MB0 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 ESC_MASK) ≫ (bv_unsigned (Z_to_bv 64 cz) mod 64)))) 1) = Z_to_bv 64 0).
{ assert (C : cz = 0 \/ cz = 1 \/ cz = 2 \/ cz = 3 \/ cz = 4 \/ cz = 5 \/ cz = 6 \/ cz = 7 \/ cz = 11 \/ cz = 14 \/ cz = 15 \/ cz = 16 \/ cz = 17 \/ cz = 18 \/
cz = 19 \/ cz = 20 \/ cz = 21 \/ cz = 22 \/ cz = 23 \/ cz = 24 \/ cz = 25 \/ cz = 26 \/ cz = 27 \/ cz = 28 \/ cz = 29 \/ cz = 30 \/ cz = 31)
by (cbn in CN; lia).
repeat (destruct C as [-> | C]; [apply bv_eq; vm_compute; reflexivity|]). subst cz. apply bv_eq; vm_compute; reflexivity. }
pose proof CHm as CHx. unfold escCH in CHx.
apply Forall_cons_iff in CHx as [LOC CHx]. apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [_ CHx].
apply Forall_cons_iff in CHx as [_ CHx]. apply Forall_cons_iff in CHx as [SHx _]. cbn [fst snd] in LOC, SHx. unfold escLoc in LOC. unfold escSH in SHx.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & HF0 & HFc & _). rewrite fr_size_0 in HFc. unfold alloc_ceiling in HFc.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)] m) as MU.
unfold st_escA. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. if_falsex. step. step. rewrite MB0. clear MB0.
step. if_lit. step. step. if_falsex. step. step. if_falsex.
step. step. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (INV7 : esc_invx 7 A e m1 md) by (eapply (esc_inv_shA 248 7 A e m m1 md INV MU WM MI1); exact SHx).
pose proof (esc_srcA _ _ _ _ _ INV7) as SRC1.
pose proof INV7 as (j0' & j1' & gj' & j8' & sb' & j17' & INV17).
pose proof INV17 as (buf1 & cap1 & bpos1 & content1 & errv1 & B1 & HP1 & PB1 & CHm1 & _).
try clear LOC. apply Forall_cons_iff in CHm1 as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
destruct (Z.lt_ge_cases start pos) as [LT | GE].
-
step. if_falsex.
step. step. if_falsex.
step. step.
rewrite (unsigned_lit pos), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 7);
[ exact INV7
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC1 | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP1 | right; right; exact INs | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_ctrl_hexA; [exact INV' | exact FS' | exact FR' | lia | lia | lia | exact IH | exact EX].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_ctrl_hexA; [exact INV7 | exact FS | exact FR | lia | lia | lia | exact IH | exact EX].
Qed.
End Esc.
End RC__1.
