(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Ql4f Q4xz Q9O6 QL3k Q228 QJZd QfHY Q1Ey QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 Q4xz QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 Ql4f.Mq2 Qwm6.Mq1 Q228.Mq6 Q228.Mq5 QJZd.Mq6 QfHY.Mq3 QfHY.Mq2.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition DBL_NAN : list byte := map (Z_to_bv 8) [78; 97; 78; 0].

Lemma dbl_ff_join : forall m Fr j8 jr (k : nat) txt bufb,
rw_cells asegs m Fr [C8 (wz 1102416563); C8 (wz 0x19d61); C8 (wz 0x9d3bc); CB 8 j8] ->
rw_cells asegs m (Fr + 32) [CB k txt] -> rw_cells asegs m (Fr + 32 + Z.of_nat k) [CB (128 - k) (skipn k bufb)] ->
rw_cells asegs m (Fr + 32 + 128) [CB 88 jr] -> (k <= 128)%nat ->
rw_cells asegs m Fr (dblFF j8 (txt ++ skipn k bufb) jr).
Proof.
intros m Fr j8 jr k txt bufb H1 H2 H3 H4 Hk.
pose proof (rw_cells_CB_join asegs m (Fr + 32) k (128 - k) _ _ H2 H3) as J.
replace (k + (128 - k))%nat with 128%nat in J by lia.
unfold dblFF.
change [C8 (wz 1102416563); C8 (wz 0x19d61); C8 (wz 0x9d3bc); CB 8 j8; CB 128 (txt ++ skipn k bufb); CB 88 jr]
with ([C8 (wz 1102416563); C8 (wz 0x19d61); C8 (wz 0x9d3bc); CB 8 j8] ++ ([CB 128 (txt ++ skipn k bufb)] ++ [CB 88 jr])).
apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
apply rw_cells_app. split; [exact J|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 128) with 128. exact H4.
Qed.

Lemma dbl_shw : forall m sh t8, rw_cells asegs m sh (dblSH 0 t8) -> bytes_at asegs m sh DBUF_SHW.
Proof.
intros m sh t8 SHx. unfold dblSH in SHx. pose proof (rw_cells_bytes_at asegs _ _ _ SHx) as Y. cbn [cells_bytes cbytes app] in Y.
change (Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: t8 ++ []) with (DBUF_SHW ++ (t8 ++ [])) in Y.
apply bytes_at_app in Y. exact (proj1 Y).
Qed.

Definition DBL_INF : list byte := Eval vm_compute in lit_bytesA 0x23740 9.
Definition DBL_NINF : list byte := Eval vm_compute in lit_bytesA 0x23760 10.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 9 < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 9 <= bB B0.
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 9 lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).
Local Notation dbl_epiA := (QfHY.Mq2.dbl_epiA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb lo bpos0 cap0 T q d Fr Hd Hq Hq32 LO LOS K).

Lemma dbl_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x24 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (bufb : list byte) (len : Z),
dbl_invx 0 A 0 bufb m md -> 0 < len <= 9 -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7 (wz Fr) (wz pb) (wz (Fr + 32)) x21 x22 (wz len) x24 (wz (Fr / 8 + 2147450880)) (wz Fr) x27 t3 t4 t5 t6)
F' (wz 0x9d580) fc' None m (seg_rom asegs)).
Proof.
intros until len. intros INV Hlen FS FR.
destruct INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
rewrite fr_size_2 in HFal, HFc.

assert (BUFB : bytes_at asegs m (Fr + 32) bufb).
{ unfold dblFF in FFx. apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [_ X]. cbn [cells_size csize Nat.add] in X. change (Z.of_nat 32) with 32 in X.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in X. destruct X as [X _]. pose proof (rw_cells_bytes_at asegs _ _ _ X) as Y. cbn [cells_bytes cbytes app] in Y. rewrite app_nil_r in Y. exact Y. }
assert (BL : length bufb = 128%nat).
{ unfold dblFF in FFx. destruct FFx as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. tauto. }
assert (SRC : bytes_at asegs m (Fr + 32) (firstn (Z.to_nat len) bufb)).
{ rewrite <- (firstn_skipn (Z.to_nat len) bufb) in BUFB. apply bytes_at_app in BUFB. exact (proj1 BUFB). }
assert (SHW : bytes_at asegs m (Fr / 8 + A_SB) DBUF_SHW).
{ unfold dblSH in SHx. pose proof (rw_cells_bytes_at asegs _ _ _ SHx) as Y. cbn [cells_bytes cbytes app] in Y.
change (Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: t8 ++ []) with (DBUF_SHW ++ (t8 ++ [])) in Y.
apply bytes_at_app in Y. unfold A_SB. exact (proj1 Y). }
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl (@nil (Z * Z)) m) as MU.
clear LOC SAV FFx SHx.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_truex.
step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 9 LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := firstn (Z.to_nat len) bufb) (e := 0);
[ exact INV1 | exact SRC | rewrite length_firstn, BL; lia | lia | lia
| right; left; exists Fr, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros Hk; apply unpoisoned_dbuf; [exact HFal | lia | exact SHW | lia]
| lia | lia | lia | clear - Hq32; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply dbl_epiA with (e := 0 + len) (bufb := bufb); [exists LOCc, j8, jr, t8; split; [exact HLOC | exact INV2] | exact FS2 | intros _; exact FR2 | lia].
Qed.

Variables (p rc pb0 fl : Z) (bits : word).
Hypothesis INp : In (p, 48) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string A4F) pb0 0 0 ++ [C8 bits]).
Hypothesis SPEC : dbl_special bits.

Lemma dbl_armsA :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (bufb : list byte),
dbl_invx 0 A 0 bufb m md -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) (wz (p + 40)) a1 a2 a3 a4 a5 a6 a7 (wz Fr) (wz pb) (wz p) (wz fl) (wz 0) x23 x24 (wz (Fr / 8 + 2147450880)) (wz Fr) (wz 2147450880) t3 t4 t5 t6)
F' (wz 0x9d54c) fc' None m (seg_rom asegs)).
Proof.
intros until bufb. intros INV FS FR.
pose proof INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (NODE : rw_cells asegs m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string A4F) pb0 0 0 ++ [C8 bits])).
{ eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (INpF : In (p, 48) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpF) as (_ & Hpal & Hplo & Hphi & _).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 bits) as BR. unfold bv_modulus in BR. cbn in BR.
unfold dbl_special in SPEC.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
rewrite fr_size_2 in HFal, HFc.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_2 in HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpF) as DFp. rewrite fr_size_2 in DFp.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.

pose proof (dbl_shw _ _ _ SHx) as SHW.
unfold dblFF in FFx. unfold dblSH in SHx.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe. change (Z.of_nat 32) with 32 in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFb FFr]. cbn [cells_size csize Nat.add] in FFr. change (Z.of_nat 128) with 128 in FFr.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, q); (Fr + 32, Fr + 42)] m) as MU.
clear LOC SAV. stash INV. stash INV1. stash HFal. stash Hq32. stash PB.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. step. step. step. step. step.
step.
destruct (Z.eq_dec (bv_unsigned bits mod 2^63) 0x7FF0000000000000) as [INFb|NAN].
-
rewrite abs63z_ltu by lia. replace (bv_unsigned bits mod 2 ^ 63 <? 9218868437227405313) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
rewrite (abs63z_lit bits _ INFb).
step. if_lit.
destruct (inf_bits bits INFb) as [E|E].
+ rewrite E.
step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 9218868437227405312)) with true by (vm_compute; reflexivity).
change (bword true) with (Z_to_bv 64 1).
step. if_lit.
step. step. step. step. step. fold_mkR.
destruct (rw_cells_CB_cut asegs m _ _ _ 9%nat FFb ltac:(lia)) as [BD BT]. change (Z.of_nat 9) with 9 in BT. clear FFb.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc0 m (Fr + 32) 145216 9 lo _ DBL_INF);
rewrite ?unsigned_lit by lia;
[ intros _; apply unpoisoned_dbuf; [unstash HFal; exact HFal | lia | unstash Esh; subst sh; unfold A_SB; exact SHW | lia]
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | left; lia
| exact BD | apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity] | reflexivity
| exact ST | exact LO | lia | unstash Hq32; clear - Hq32; Z.div_mod_to_equations; lia | exact MI | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BD2 SRC2 ST2.
clear BD ST SHW.
transport_after_call asegs m m2 MU2 WM2; try match goal with H : mem_inv asegs m |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 644776)) with (Z_to_bv 64 644776) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. fold_mkR.
pose proof (dbl_ff_join m2 Fr j8 jr 9 DBL_INF bufb FFa BD2 BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_INF ++ skipn 9 bufb) (len := 8); [ | lia | fsaved_tmp | exact FRM].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m m2 md _ bufb);
[ exact INV | exact MU | exact WM | exact MI2 | | exact FFf | exact SHx | exact ST2 ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
+ rewrite E.
step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 18442240474082181120)) with false by (vm_compute; reflexivity).
change (bword false) with (Z_to_bv 64 0).
step. if_lit.
step. step. step. step. step. fold_mkR.
destruct (rw_cells_CB_cut asegs m _ _ _ 10%nat FFb ltac:(lia)) as [BD BT]. change (Z.of_nat 10) with 10 in BT. clear FFb.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc0 m (Fr + 32) 145248 10 lo _ DBL_NINF);
rewrite ?unsigned_lit by lia;
[ intros _; apply unpoisoned_dbuf; [unstash HFal; exact HFal | lia | unstash Esh; subst sh; unfold A_SB; exact SHW | lia]
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | left; lia
| exact BD | apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity] | reflexivity
| exact ST | exact LO | lia | unstash Hq32; clear - Hq32; Z.div_mod_to_equations; lia | exact MI | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BD2 SRC2 ST2.
clear BD ST SHW.
transport_after_call asegs m m2 MU2 WM2; try match goal with H : mem_inv asegs m |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 645108)) with (Z_to_bv 64 645108) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. fold_mkR.
pose proof (dbl_ff_join m2 Fr j8 jr 10 DBL_NINF bufb FFa BD2 BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_NINF ++ skipn 10 bufb) (len := 9); [ | lia | fsaved_tmp | exact FRM].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m m2 md _ bufb);
[ exact INV | exact MU | exact WM | exact MI2 | | exact FFf | exact SHx | exact ST2 ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
-
rewrite abs63z_ltu by lia. replace (bv_unsigned bits mod 2 ^ 63 <? 9218868437227405313) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
destruct (rw_cells_CB_cut asegs m _ _ _ 4%nat FFb ltac:(lia)) as [B4 BT]. change (Z.of_nat 4) with 4 in BT. clear FFb.
step. step. stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
match goal with H : mem_inv asegs mf |- _ => rename H into MIf end.
assert (B4c : rw_cells asegs mf (Fr + 32) [CB 4 DBL_NAN]).
{ eapply rw_cells_recast; [exact B4 | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes]. f_equal. symmetry. apply Qfw3_c1.le4_lit_of_mod32; [reflexivity | vm_compute; reflexivity]. }
pose proof (dbl_ff_join mf Fr j8 jr 4 DBL_NAN bufb FFa B4c BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_NAN ++ skipn 4 bufb) (len := 3); [ | lia | fsaved_tmp | exact FR].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m mf md _ bufb);
[ exact INV | exact MU | exact WM | exact MIf | | exact FFf | exact SHx | exact ST ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
Qed.
End Dbl.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB.  From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUrr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL3k.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL3k.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q228.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q228.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfHY.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfHY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfHY.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).

Definition DBL_NAN : list byte := map (Z_to_bv 8) [78; 97; 78; 0].

Lemma dbl_ff_join : forall m Fr j8 jr (k : nat) txt bufb,
rw_cells asegs m Fr [C8 (wz 1102416563); C8 (wz 0x19e77); C8 (wz 0x9ee14); CB 8 j8] ->
rw_cells asegs m (Fr + 32) [CB k txt] -> rw_cells asegs m (Fr + 32 + Z.of_nat k) [CB (128 - k) (skipn k bufb)] ->
rw_cells asegs m (Fr + 32 + 128) [CB 88 jr] -> (k <= 128)%nat ->
rw_cells asegs m Fr (dblFF j8 (txt ++ skipn k bufb) jr).
Proof.
intros m Fr j8 jr k txt bufb H1 H2 H3 H4 Hk.
pose proof (rw_cells_CB_join asegs m (Fr + 32) k (128 - k) _ _ H2 H3) as J.
replace (k + (128 - k))%nat with 128%nat in J by lia.
unfold dblFF.
change [C8 (wz 1102416563); C8 (wz 0x19e77); C8 (wz 0x9ee14); CB 8 j8; CB 128 (txt ++ skipn k bufb); CB 88 jr]
with ([C8 (wz 1102416563); C8 (wz 0x19e77); C8 (wz 0x9ee14); CB 8 j8] ++ ([CB 128 (txt ++ skipn k bufb)] ++ [CB 88 jr])).
apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
apply rw_cells_app. split; [exact J|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 128) with 128. exact H4.
Qed.

Lemma dbl_shw : forall m sh t8, rw_cells asegs m sh (dblSH 0 t8) -> bytes_at asegs m sh DBUF_SHW.
Proof.
intros m sh t8 SHx. unfold dblSH in SHx. pose proof (rw_cells_bytes_at asegs _ _ _ SHx) as Y. cbn [cells_bytes cbytes app] in Y.
change (Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: t8 ++ []) with (DBUF_SHW ++ (t8 ++ [])) in Y.
apply bytes_at_app in Y. exact (proj1 Y).
Qed.

Definition DBL_INF : list byte := Eval vm_compute in lit_bytesA 0x237a0 9.
Definition DBL_NINF : list byte := Eval vm_compute in lit_bytesA 0x237c0 10.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Dbl.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 : Z) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 128 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - ADBL_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 9 < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 9 <= bB B0.
Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 9 lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Notation dbl_invx := (dbl_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr).
Local Notation dbl_epiA := (QfHY.Mq6.dbl_epiA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb lo bpos0 cap0 T q d Fr Hd Hq Hq32 LO LOS K).

Lemma dbl_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (bufb : list byte) (len : Z),
dbl_invx 0 A 0 bufb m md -> 0 < len <= 9 -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7 (wz Fr) (wz pb) (wz (Fr + 32)) (wz len) x22 x23 x24 (wz (Fr / 8 + 2147450880)) (wz Fr) x27 t3 t4 t5 t6)
F' (wz 0x9efb4) fc' None m (seg_rom asegs)).
Proof.
intros until len. intros INV Hlen FS FR.
destruct INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
rewrite fr_size_2 in HFal, HFc.

assert (BUFB : bytes_at asegs m (Fr + 32) bufb).
{ unfold dblFF in FFx. apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [_ X]. cbn [cells_size csize Nat.add] in X. change (Z.of_nat 32) with 32 in X.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in X. destruct X as [X _]. pose proof (rw_cells_bytes_at asegs _ _ _ X) as Y. cbn [cells_bytes cbytes app] in Y. rewrite app_nil_r in Y. exact Y. }
assert (BL : length bufb = 128%nat).
{ unfold dblFF in FFx. destruct FFx as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. tauto. }
assert (SRC : bytes_at asegs m (Fr + 32) (firstn (Z.to_nat len) bufb)).
{ rewrite <- (firstn_skipn (Z.to_nat len) bufb) in BUFB. apply bytes_at_app in BUFB. exact (proj1 BUFB). }
assert (SHW : bytes_at asegs m (Fr / 8 + A_SB) DBUF_SHW).
{ unfold dblSH in SHx. pose proof (rw_cells_bytes_at asegs _ _ _ SHx) as Y. cbn [cells_bytes cbytes app] in Y.
change (Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 241 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: Z_to_bv 8 243 :: t8 ++ []) with (DBUF_SHW ++ (t8 ++ [])) in Y.
apply bytes_at_app in Y. unfold A_SB. exact (proj1 Y). }
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl (@nil (Z * Z)) m) as MU.
clear LOC SAV FFx SHx.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. if_truex.
step. step. step. step. fold_mkR.
evt_done5.
eapply (ser_appendA HIx sp gp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 9 LO HT CAP0 TXT NEED OBL_REALLOC_NF) with (F := F) (sb := firstn (Z.to_nat len) bufb) (e := 0);
[ exact INV1 | exact SRC | rewrite length_firstn, BL; lia | lia | lia
| right; left; exists Fr, 2; split; [left; reflexivity | rewrite fr_size_2; lia]
| intros Hk; apply unpoisoned_dbuf; [exact HFal | lia | exact SHW | lia]
| lia | lia | lia | clear - Hq32; Z.div_mod_to_equations; lia | lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A2 m2 md2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 INV2 FS2 FR2 _.
eapply dbl_epiA with (e := 0 + len) (bufb := bufb); [exists LOCc, j8, jr, t8; split; [exact HLOC | exact INV2] | exact FS2 | intros _; exact FR2 | lia].
Qed.

Variables (p rc pb0 fl : Z) (bits : word).
Hypothesis INp : In (p, 48) LB.
Hypothesis NODE0 : rw_cells asegs m0 p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string A4F) pb0 0 0 ++ [C8 bits]).
Hypothesis SPEC : dbl_special bits.

Lemma dbl_armsA :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x24 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (bufb : list byte),
dbl_invx 0 A 0 bufb m md -> fsaved F F' -> frm0 fc' ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) (wz (p + 40)) a1 a2 a3 a4 a5 a6 a7 (wz Fr) (wz pb) (wz p) x21 (wz fl) (wz 0) x24 (wz (Fr / 8 + 2147450880)) (wz Fr) (wz 2147450880) t3 t4 t5 t6)
F' (wz 0x9ef80) fc' None m (seg_rom asegs)).
Proof.
intros until bufb. intros INV FS FR.
pose proof INV as (LOCc & j8 & jr & t8 & HLOC & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
assert (NODE : rw_cells asegs m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string A4F) pb0 0 0 ++ [C8 bits])).
{ eapply (heap_pres_rw_cells A4H); [exact HPR | exact NODE0 |]. eapply client_range_block; [apply in_or_app; left; exact INp | lia | cbn; lia]. }
unfold jhdr_cells in NODE. cbn [app] in NODE.
assert (INpF : In (p, 48) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; right; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p 48 HP INpF) as (_ & Hpal & Hplo & Hphi & _).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (bv_unsigned_in_range 64 bits) as BR. unfold bv_modulus in BR. cbn in BR.
unfold dbl_special in SPEC.
pose proof alloc_ceiling_range as ACR. unfold ADBL_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
rewrite fr_size_2 in HFal, HFc.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. rewrite fr_size_2 in HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpF) as DFp. rewrite fr_size_2 in DFp.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 32 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
unfold dblCH in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, SAV, FFx, SHx.

pose proof (dbl_shw _ _ _ SHx) as SHW.
unfold dblFF in FFx. unfold dblSH in SHx.
apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _] _)) in FFx. destruct FFx as [FFa FFe]. cbn [cells_size csize Nat.add] in FFe. change (Z.of_nat 32) with 32 in FFe.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FFe. destruct FFe as [FFb FFr]. cbn [cells_size csize Nat.add] in FFr. change (Z.of_nat 128) with 128 in FFr.
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, q); (Fr + 32, Fr + 42)] m) as MU.
clear LOC SAV. stash INV. stash INV1. stash HFal. stash Hq32. stash PB.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. step. step. step. step. step.
step.
destruct (Z.eq_dec (bv_unsigned bits mod 2^63) 0x7FF0000000000000) as [INFb|NAN].
-
rewrite abs63z_ltu by lia. replace (bv_unsigned bits mod 2 ^ 63 <? 9218868437227405313) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
rewrite (abs63z_lit bits _ INFb).
step. if_lit.
destruct (inf_bits bits INFb) as [E|E].
+ rewrite E.
step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 9218868437227405312)) with true by (vm_compute; reflexivity).
change (bword true) with (Z_to_bv 64 1).
step. if_lit.
step. step. step. step. step. fold_mkR.
destruct (rw_cells_CB_cut asegs m _ _ _ 9%nat FFb ltac:(lia)) as [BD BT]. change (Z.of_nat 9) with 9 in BT. clear FFb.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc0 m (Fr + 32) 145312 9 lo _ DBL_INF);
rewrite ?unsigned_lit by lia;
[ intros _; apply unpoisoned_dbuf; [unstash HFal; exact HFal | lia | unstash Esh; subst sh; unfold A_SB; exact SHW | lia]
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | left; lia
| exact BD | apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity] | reflexivity
| exact ST | exact LO | lia | unstash Hq32; clear - Hq32; Z.div_mod_to_equations; lia | exact MI | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BD2 SRC2 ST2.
clear BD ST SHW.
transport_after_call asegs m m2 MU2 WM2; try match goal with H : mem_inv asegs m |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 651480)) with (Z_to_bv 64 651480) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. fold_mkR.
pose proof (dbl_ff_join m2 Fr j8 jr 9 DBL_INF bufb FFa BD2 BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_INF ++ skipn 9 bufb) (len := 8); [ | lia | fsaved_tmp | exact FRM].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m m2 md _ bufb);
[ exact INV | exact MU | exact WM | exact MI2 | | exact FFf | exact SHx | exact ST2 ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
+ rewrite E.
step. step.
replace (flt_d (Z_to_bv 64 0) (Z_to_bv 64 18442240474082181120)) with false by (vm_compute; reflexivity).
change (bword false) with (Z_to_bv 64 0).
step. if_lit.
step. step. step. step. step. fold_mkR.
destruct (rw_cells_CB_cut asegs m _ _ _ 10%nat FFb ltac:(lia)) as [BD BT]. change (Z.of_nat 10) with 10 in BT. clear FFb.
eapply (amemcpy_U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc0 m (Fr + 32) 145344 10 lo _ DBL_NINF);
rewrite ?unsigned_lit by lia;
[ intros _; apply unpoisoned_dbuf; [unstash HFal; exact HFal | lia | unstash Esh; subst sh; unfold A_SB; exact SHW | lia]
| intros _; eapply (unpoisoned_of_glob HIx); [exact HP | apply src_globA_of_chk; vm_compute; reflexivity | lia]
| exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP)
| lia | lia | lia | lia | left; lia | left; lia | reflexivity | reflexivity | reflexivity | lia | left; lia | left; lia
| exact BD | apply rodata_bytes_at; [exact MI | vm_compute; reflexivity | lia | apply Z.leb_le; vm_compute; reflexivity] | reflexivity
| exact ST | exact LO | lia | unstash Hq32; clear - Hq32; Z.div_mod_to_equations; lia | exact MI | reflexivity | ].
intros z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 m2 MU2 WM2 MI2 BD2 SRC2 ST2.
clear BD ST SHW.
transport_after_call asegs m m2 MU2 WM2; try match goal with H : mem_inv asegs m |- _ => clear H end.
clear MU2 WM2.
replace (ret_pc (Z_to_bv 64 651812)) with (Z_to_bv 64 651812) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. step. fold_mkR.
pose proof (dbl_ff_join m2 Fr j8 jr 10 DBL_NINF bufb FFa BD2 BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_NINF ++ skipn 10 bufb) (len := 9); [ | lia | fsaved_tmp | exact FRM].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m m2 md _ bufb);
[ exact INV | exact MU | exact WM | exact MI2 | | exact FFf | exact SHx | exact ST2 ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
-
rewrite abs63z_ltu by lia. replace (bv_unsigned bits mod 2 ^ 63 <? 9218868437227405313) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
destruct (rw_cells_CB_cut asegs m _ _ _ 4%nat FFb ltac:(lia)) as [B4 BT]. change (Z.of_nat 4) with 4 in BT. clear FFb.
step. step. stepz. step. fold_mkR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
match goal with H : mem_inv asegs mf |- _ => rename H into MIf end.
assert (B4c : rw_cells asegs mf (Fr + 32) [CB 4 DBL_NAN]).
{ eapply rw_cells_recast; [exact B4 | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes]. f_equal. symmetry. apply Qfw3_c1.le4_lit_of_mod32; [reflexivity | vm_compute; reflexivity]. }
pose proof (dbl_ff_join mf Fr j8 jr 4 DBL_NAN bufb FFa B4c BT FFr ltac:(lia)) as FFf.
unstash INV. unstash Esh. subst sh. fold (dblSH 0 t8) in SHx.
evt_done5.
eapply dbl_tailA with (bufb := DBL_NAN ++ skipn 4 bufb) (len := 3); [ | lia | fsaved_tmp | exact FR].
eapply (dbl_inv_privA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 q d Fr Hd Hq LO LOS HT 0 0 A 0 m mf md _ bufb);
[ exact INV | exact MU | exact WM | exact MIf | | exact FFf | exact SHx | exact ST ].
constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; cbn [fst snd]; lia | constructor].
Qed.
End Dbl.
End RC__1.
