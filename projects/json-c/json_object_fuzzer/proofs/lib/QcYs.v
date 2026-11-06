(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Q6sh QQwg QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QTVW QpY2 QOJv Q9Ho QqLk QnRU QMSY QkfD QpME QkJ4 QRfV QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY QkfD.
Import QpME.Mq1 QkJ4.
Import QRfV.Mq0.
Import QpME.Mq1 QkJ4.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma msz_eq : msz = ssz + 4095 - (ssz + 4095) mod 4096 + 4096.
Proof. subst msz ssz. unfold sec_map_size, sec_size, round_up, kPage. Z.div_mod_to_equations. lia. Qed.

Lemma alloc_shadow_sec : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (idx : word) (j1 j2 : list byte) (Q : machine_state -> Prop),
let up := A + 8 * ngran n' in
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m mb [C8 (wz mb); C8 (wz msz); C8 (wz ssz); C8 idx] ->
rw_cells asegs m (SH AB) [CB (Z.to_nat 256) j1] ->
rw_cells asegs m (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) j2] ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + (AB + sz - up) / 8)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (SH AB) [CB (Z.to_nat 256) (fas 256)] ->
rw_cells asegs m1 (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) (fas ((AB + sz - up) / 8))] ->
evt asegs Q (MS (mkR (wz 0x3f500) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz sz) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz up) (wz obj) (wz 0) (wz (A + n' + 7)) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f500) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f414) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f424) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros up RT MI ST CEIL LO HDRS.
pose proof sgeomS as (Grz & Gn' & GN & _ & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & _ & TD & _).
pose proof msz_eq as ME.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (Gn1 : 1 <= n') by lia.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHu : SH up = SH AB + 256 + ngran n') by (subst up A; rewrite SHa; unfold SH, A_SHADOW_OFS; subst AB; clear - MBP Grz NG2; Z.div_mod_to_equations; lia).
assert (UPB : AB + 2048 + n' <= up /\ up + 2048 <= AB + sz /\ (AB + sz - up) mod 8 = 0 /\ up mod 8 = 0).
{ assert (RU : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
subst up A sz AB. split; [(first [ clear - RU SHu SHa RU8 NG3 PK GK GndE GM1 Gssz GN Gn' Grz MBK msz ssz nd n' rz mb n RE BAND; lia | lia ])|]. split; [(first [ clear - RU SHu SHa RU8 NG3 PK GK GndE GM1 Gssz GN Gn' Grz MBK msz ssz nd n' rz mb n RE BAND; lia | lia ])| split; [clear - Gmsz Grz NG2 MBP; Z.div_mod_to_equations; lia| clear - MBP Grz GA16; Z.div_mod_to_equations; lia]]. }
destruct UPB as (UP1 & UP2 & UP3 & UP4).

remember ((AB + sz - up) / 8) as k2 eqn:EK2.
assert (K2 : 8 * k2 = AB + sz - up /\ 256 <= k2) by (subst k2; clear - UP2 UP3; Z.div_mod_to_equations; lia).
assert (SHe : SH (AB + sz) = SH up + k2) by (rewrite SHu, SHa; unfold SH, A_SHADOW_OFS; subst AB; clear - MBP Grz NG2 K2 UP1; Z.div_mod_to_equations; lia).
assert (MBH : 0x645000 <= mb) by (clear - GK GN Gnd1 Gssz GM1; lia).
assert (SHB : 0x80000000 <= SH AB /\ SH AB + 256 + ngran n' + k2 <= SH band_lo) by (rewrite SHa, (SH_eq band_lo); subst AB sz; clear - MBH GC K2 UP1 UP2 Gn1 Grz NG2; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.

assert (MK1 : Z.land 4095 AB = 0).
{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. subst AB. clear - MBP. Z.div_mod_to_equations. lia. }
assert (MK2 : Z.land (ssz + 4095) 18446744073709547520 = sz) by (rewrite land_pagemask by (first [ clear - MBH UP2 RU8 NG3 PK Gssz Gnd2 Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ]); (first [ clear - MBH SHe K2 EK2 k2 UP2 SHu SHa RU8 NG3 ME PK GM1 Gssz Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ])).
assert (MK3 : Z.land (A + n' + 7) 18446744073709551608 = up).
{ rewrite land_mask8 by (first [ clear - MBH UP2 RU8 NG3 PC PK GC Gssz Gnd1 GN Gn' Grz up AVP MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ]). subst up. rewrite NG1. unfold round_up. clear - GA16 Gn1 Grz GK. Z.div_mod_to_equations. lia. }

clear Gmsz GA16 SHa ME NG1 EK2.
intros SHD1 SHD2 CONT.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + k2)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
rtc RT 24%nat K24. rtc RT 25%nat K25. unfold A_INSTANCE in *. unfold prim_lo in GP, PK, PC.
step. if_true.
step.

assert (TAIL : forall (a1v : word),
evt asegs Q (MS (mkR (wz 0x3f414) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') (wz (al_space_beg (ae_L RE))) a1v a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz 967832) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f480) fc None m (seg_rom asegs))).
{ intros a1v.
step.
clear K24 K25.
stp.
step.
rewrite (unsigned_lit AB), MK1 by lia.
step. if_false.
stp. step. if_false.
step.
rewrite (unsigned_lit AB) by lia. replace (AB - 4096) with mb by lia.
step.
clear HDRS.
step.
rewrite ?(unsigned_lit ssz) by lia.
stp.
step.
rewrite (unsigned_lit (ssz + 4095)), ?(Z.land_comm 18446744073709547520), MK2 by lia.
step.
step.
step.
rewrite (unsigned_lit (A + n' + 7)), MK3 by lia.
step.
rewrite (unsigned_lit A), (unsigned_lit AB) by lia. replace (A - AB) with 2048 by lia.
stp. step.
step.
call_sp_ch (poison_shadow_spec_lh RE X) ltac:(fun PO => change (2048 / 8) with 256 in PO; clear SHD1 ST);
[exact RT| exact RL| assumption| exact ST| exact CEIL'| lia
| subst AB; clear - MBP; Z.div_mod_to_equations; lia| reflexivity| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - MBH SHe K2 k2 UP2 SHu RU8 NG3 GC GK GM1 Gssz Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])| lia| left; lia| exact SHD1|].
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH AB) _ |- _ => rename H into RT1; rename H2 into FA1 end.
step. step.
rewrite ?(unsigned_lit AB), ?(unsigned_lit up) by lia.
replace (AB - up + sz) with (8 * k2) by lia.
stp. step.
assert (D8 : 8 * k2 / 8 = k2) by (rewrite Z.mul_comm; apply Z.div_mul; lia). rewrite <- D8 in SHD2.
step.
call_sp_ch (poison_shadow_spec_lh RE X) ltac:(fun PO => rewrite ?D8 in PO; clear SHD2 ST1);
[exact RT1| exact RL| assumption| exact ST1| exact CEIL'| lia
| exact UP4| rewrite Z.mul_comm; apply Z.mod_mul; lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - D8 MBH SHe K2 k2 UP2 SHu RU8 NG3 GC GK GM2 GM1 Gssz Gnd2 Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])| lia| left; lia| exact SHD2|].
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH up) _ |- _ => rename H into RT2; rename H2 into FA2 end.
clear D8.
replace (8 * k2) with (AB + sz - up) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST2| exact RT2| | ].
- unfold fas, fa_byte. exact FA1.
- unfold fas, fa_byte. exact FA2. }

destruct GP as [LOW|HIGH].
- step. unfold_cond; cond_unsig; if_true.
apply TAIL.
- step. unfold_cond; cond_unsig; if_false.
stp. stp. step.
step. unfold_cond; cond_unsig; if_true.
apply TAIL.
Qed.
End S.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLxt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QMSY QkfD.
Import QLxt QpME.Mq1 QkJ4 QRfV.
Import QRfV.Mq0.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_stats_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2904, rl_T X + 2904 + 8)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 -> RStats RE X m1 ->
evt asegs Q (MS (mkR (wz 0x3f5b8) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f5f8) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f5b4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RS MI ST CEIL LO CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
remember (rl_T X + 2904) as MBS eqn:EMBS.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); [exact RT| exact RL| assumption| exact ST| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm |- _ => rename H into RT1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.

pose proof RS as (HJ & ERR & OOM).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (HJ1 : hjunk mm (rl_T X + 2800) (rl_T X + 3168)) by (eapply hjunk_wmono; [exact HJ| exact WM]) end.
destruct (hjunk_split _ _ (rl_T X + 2824) _ HJ1 ltac:(lia)) as [HJa HJb].
replace (rl_T X + 2824) with (rl_T X + 2800 + 24) in HJa by lia. destruct (hjunk_C8x3 RE 0 0 _ _ HJa) as (w1 & w2 & w3 & STA).
destruct (hjunk_split _ _ MBS _ HJb ltac:(lia)) as [_ HJc]. destruct (hjunk_split _ _ (MBS + 8) _ HJc ltac:(lia)) as [HJd _].
destruct (hjunk_C8 _ _ HJd) as (w4 & STB). clear HJ1 HJa HJb HJc HJd.
step. step. step.
step. step.
stp. stp.
step. step.
step. step. step.
step. ifz.
rewrite EMBS in STB.
step. step. step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| |].
- eapply RTconst_munch; [exact RT1| exact MUh| exact WMh|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor].
- destruct ERR as [e ERR]. destruct OOM as [b OOM]. unfold A_ERRNO in ERR.
split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exists e; unfold A_ERRNO| exists b];
(eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]).
Qed.

Lemma alloc_fill_sec : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj cf : Z) (fj : list byte) (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) -> 0 <= cf <= 1 ->
hjunk m A (AB + sz) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(A, A + Z.min n' 4096)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
hjunk m1 A (AB + sz) -> (cf = 0 -> m1 = m) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f748) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f5b8) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f5f8) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR CF HJU CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (mn := Z.min n' 4096) in *. assert (MN : 1 <= mn <= n' /\ mn <= 4096) by lia.
pose proof (munch_refl [(A, A + mn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_frame in FR.
step.
step.
destruct (Z.eq_dec cf 0) as [CF0|CF1].
- subst cf. if_lit. step.  eapply CONT; [exact MU| exact WM| exact MI| exact ST| exact RT| exact FR| exact HJU| intros _; reflexivity].
- ifz.
rtc RT 19%nat K19. rtc RT 12%nat K12. rtc RT 23%nat K23.
step. step.
stp.
step. if_lit.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => ms1 = MS (@bvmap_set 5 word 12 (wz mn) R) FF (wz 0x3f730) fcc rv mm ro))
end.
{ step. destruct (Z.ltb_spec n' 4096) as [LT|GE]; ifz.
- apply evt_done. simp_regs. replace mn with n' by lia. reflexivity.
- step. apply evt_done. simp_regs. replace mn with 4096 by lia. reflexivity. }
intros ms1 ->. simp_regs.
step. step.
step.
stp.
step.
destruct (hjunk_split _ _ (A + mn) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (A + mn) with (A + Z.of_nat (Z.to_nat mn)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & UC2).
replace (ret_pc (wz 259912)) with (wz 259912) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
eapply CONT; [exact MU2| exact WM2| exact MI2| | | | | intros E0; exfalso; exact (CF1 E0)].
+ eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn [disjoint_from]; lia].
+ eapply RTconst_munch; [exact RT| exact MU2| exact WM2|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia| constructor].
+ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
+ eapply hjunk_merge; [| eapply hjunk_wmono; [exact HJ2| exact WM2]].
replace (A + mn) with (A + Z.of_nat (cells_size [CB (Z.to_nat mn) (repeat (b8 (190 mod 256)) (Z.to_nat mn))])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact UC2| lia].
Qed.

Lemma alloc_fin_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (idw g1 g2 : word)
(Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2]) ->
(forall m1 (u0 u1 u2 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) -> RTconst RE X m1 ->
rw_cells asegs m1 (A + -16) [C1 (b8 2); C1 (b8 (hb1f b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m1 AB [C8 (wz kMagic); C8 (wz (A + -16))]) ->
evt asegs Q (MS (mkR rav sp gp (wz A_TP) u0 u1 u2 v0 v1 (wz A) u4 u5 u6 u7 u10 u11 u12
v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 u14 u15 u16 u17)
F (ret_pc rav) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f748) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR MG CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (hb1_facts b1) as [HB1 HBF].
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia| constructor]. }
unfold alloc_frame in FR.

Local Ltac fin_head RT MI HDR b1 :=
step; call0 (lsan_disabled_spec RE X); [exact RT| exact MI|]; subst_words;
step;
stp; stp;
step;
rewrite zxb_b8, (Z.mod_small (hb1 b1) 256), (unsigned_lit (hb1 b1)) by lia; change (Z.land (hb1 b1) 243) with (hb1f b1);
step;
rewrite (unsigned_lit (hb1f b1)), Z.lor_0_r by lia;
stp;
step;
rewrite (unsigned_lit (hb1f b1)) in HDR by lia;
step;
stf;
change (bv_unsigned (wz 2)) with 2 in HDR;
step.

Local Ltac fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR MG :=
let RTc := fresh "RTc" in let RT1 := fresh "RT1" in let ST1 := fresh "ST1" in
step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RTc : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]) end;
call_sp_ch (run_malloc_hooks_spec RE X) ltac:(fun _ => idtac); [exact RTc| exact RL| assumption| exact ST| exact CEIL'| lia|];
match goal with H : stk asegs _ _ _ |- _ => rename H into ST1 end;
match goal with H : RTconst RE X _, H' : mem_inv asegs ?mm |- _ => lazymatch type of H with RTconst _ _ mm => rename H into RT1 end end;
step; do 13 step; step;
release_frame FR ST1 (bv_unsigned sp);
step;
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact RT1| exact HDR| MG].

- specialize (MG ltac:(lia)).
fin_head RT MI HDR b1.
ifz.
step. step. ifz.
step. step.
step.
step.
stf.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros _; exact MG).
Qed.
End S.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QpY2.Mq1 QkfD QkJ4.
Import QRfV.Mq0.
Import QlES.
Import QpME.Mq4. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QsGW.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac Qu1d.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation zeros k := (repeat (b8 0) (Z.to_nat k)).

Lemma zsplit : forall m a N k, rw_cells asegs m a [CB (Z.to_nat N) (zeros N)] -> 0 <= k <= N ->
rw_cells asegs m a [CB (Z.to_nat k) (zeros k)] /\ rw_cells asegs m (a + k) [CB (Z.to_nat (N - k)) (zeros (N - k))].
Proof.
intros m a N k H Hk.
assert (H' : rw_cells asegs m a ([CB (Z.to_nat k) (zeros k)] ++ [CB (Z.to_nat (N - k)) (zeros (N - k))])).
{ eapply rw_cells_recast'; [exact H| cbn; rewrite !repeat_length; lia|].
cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. lia. }
apply (proj1 (rw_cells_app asegs m a _ _)) in H'. cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'.
replace (a + Z.of_nat (Z.to_nat k)) with (a + k) in H' by lia. exact H'.
Qed.

Lemma zeros_hdr : forall m a, rw_cells asegs m a [CB (Z.to_nat 16) (zeros 16)] ->
rw_cells asegs m a [C1 (b8 0); C1 (b8 0); C2 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast'; [exact H| cbn; tauto| reflexivity]. Qed.

Lemma zeros_C8x2 : forall m a, rw_cells asegs m a [CB (Z.to_nat 16) (zeros 16)] -> rw_cells asegs m a [C8 (wz 0); C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast'; [exact H| cbn; tauto| reflexivity]. Qed.

Lemma zeros_hjunk : forall m a N, rw_cells asegs m a [CB (Z.to_nat N) (zeros N)] -> 0 <= N -> 0x645000 <= a -> hjunk m a (a + N).
Proof.
intros m a N H HN Ha. replace (a + N) with (a + Z.of_nat (cells_size [CB (Z.to_nat N) (zeros N)])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact H| exact Ha].
Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Variables (n mb : Z).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sec_pieces : forall m,
let up := A + 8 * ngran n' in
rw_cells asegs m AB [CB (Z.to_nat sz) (zeros sz)] ->
hjunk m (SH AB) (SH (AB + ssz)) ->
rw_cells asegs m (SH (AB + ssz)) [CB (Z.to_nat ((sz - ssz) / 8)) (fas ((sz - ssz) / 8))] ->
exists (j1 j j2 : list byte) (pb : byte),
rw_cells asegs m AB [C8 (wz 0); C8 (wz 0)]
/\ hjunk m (AB + 16) (A + -16)
/\ rw_cells asegs m (A + -16) [C1 (b8 0); C1 (b8 0); C2 (wz 0); C4 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m A [CB (Z.to_nat n) (zeros n)]
/\ hjunk m (A + n) (AB + sz)
/\ rw_cells asegs m (SH AB) [CB (Z.to_nat 256) j1]
/\ rw_cells asegs m (SH A) [CB (Z.to_nat (8 * (n' / 8) / 8)) j]
/\ (n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb])
/\ rw_cells asegs m (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) j2].
Proof.
intros m up BODY HJ FAS.
pose proof (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP) as (Grz & Gn' & GN & _ & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & _).
fold rz n' nd ssz msz AB A in Grz, Gn', Gnd1, Gnd2, Gssz, Gmsz, GM1, GM2, GndE, GA16, GC.
assert (MB6 : 0x645000 <= mb) by (clear - MBK GM1 Gssz Gnd1 GN; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
assert (RU : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - GN Gn'; Z.div_mod_to_equations; lia).
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH A = SH AB + 256) by (subst A; rewrite Grz, <- (SH_plus8 AB 256); reflexivity).
assert (SHu : SH up = SH A + ngran n') by (subst up; rewrite <- SH_plus8; reflexivity).
assert (SHs : SH (AB + ssz) = SH up + 256).
{ replace (AB + ssz) with (up + 8 * 256) by (subst up A; rewrite Gssz, GndE, Grz, <- RU, NG3; lia). rewrite SH_plus8. reflexivity. }
assert (K2 : (AB + sz - up) / 8 = 256 + (sz - ssz) / 8 /\ 0 <= (sz - ssz) / 8).
{ subst up A sz. clear - Gmsz GM1 GM2 NG2 Gssz GndE RU NG3 Grz. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q RU NG3 GndE GM1 Gmsz r1 Gssz Grz AB msz ssz nd n' rz mb n; lia | lia ]). }
destruct K2 as [K2 K3].
assert (SB : 0x645000 <= SH AB) by (rewrite SHa; subst AB; rewrite ?KHI_eq in MBK; clear - MBK; Z.div_mod_to_equations; lia).

destruct (zsplit m AB sz 16 BODY ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z1 R1]. pose proof (zeros_C8x2 _ _ Z1) as MG.
destruct (zsplit m (AB + 16) (sz - 16) (rz - 32) R1 ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z2 R2]. pose proof (zeros_hjunk _ _ _ Z2 ltac:((first [ clear - MB6 Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ])) ltac:(rewrite ?KHI_eq in MBK; (first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as HJm.
replace (AB + 16 + (rz - 32)) with (A + -16) in HJm, R2 by (subst A; lia).
destruct (zsplit m (A + -16) (sz - 16 - (rz - 32)) 16 R2 ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z3 R3]. pose proof (zeros_hdr _ _ Z3) as HDR.
replace (A + -16 + 16) with A in R3 by lia.
destruct (zsplit m A (sz - 16 - (rz - 32) - 16) n R3 ltac:((first [ clear - SHu N8 RU RU8 NG3 MB6 GndE GM1 Gssz GN Gn' Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [UZ R4].
pose proof (zeros_hjunk _ _ _ R4 ltac:((first [ clear - SHu N8 RU RU8 NG3 MB6 GndE GM1 Gssz GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])) ltac:(rewrite ?KHI_eq in MBK; (first [ clear - MB6 GN Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ]))) as HJU.
replace (A + n + (sz - 16 - (rz - 32) - 16 - n)) with (AB + sz) in HJU by (subst A; lia).

destruct (hjunk_split _ _ (SH A) _ HJ ltac:(rewrite SHs, SHu, SHA; lia)) as [HJ1 HJr].
replace (SH A) with (SH AB + Z.of_nat (Z.to_nat 256)) in HJ1 by (first [ clear - SHA MB6 Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ]). destruct (hjunk_cells _ _ _ HJ1) as [j1 SHD1].
destruct (hjunk_split _ _ (SH A + n' / 8) _ HJr ltac:(rewrite SHs, SHu, NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia)) as [HJ2 HJr2].
replace (SH A + n' / 8) with (SH A + Z.of_nat (Z.to_nat (8 * (n' / 8) / 8))) in HJ2 by (rewrite D8; clear - N8; lia).    destruct (hjunk_cells _ _ _ HJ2) as [j PZ].
destruct (hjunk_split _ _ (SH up) _ HJr2 ltac:(rewrite SHs, SHu, NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia)) as [HJ3 HJ4].
assert (PB : exists pb : byte, n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]).
{ destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- exists (b8 0). intros NE. exfalso. exact (NE Z0).
- replace (SH up) with (SH A + n' / 8 + Z.of_nat 1%nat) in HJ3 by (rewrite SHu, NG1; unfold round_up; clear - N8 NZ; Z.div_mod_to_equations; lia).
destruct (hjunk_cells _ _ _ HJ3) as [pbs PB1].
assert (L1 : length pbs = 1%nat) by (destruct PB1 as [[[WF _] _] _]; cbn in WF; lia). destruct pbs as [|pb [|]]; [cbn in L1; clear - L1; lia| | cbn in L1; clear - L1; lia].
exists pb. intros _. eapply rw_cells_recast'; [exact PB1| cbn; tauto| reflexivity]. }
destruct PB as [pb PB].
assert (HJt : hjunk m (SH up) (SH up + Z.of_nat (Z.to_nat ((AB + sz - up) / 8)))).
{ eapply hjunk_merge; [exact HJ4|]. rewrite SHs.
replace (SH up + Z.of_nat (Z.to_nat ((AB + sz - up) / 8))) with (SH up + 256 + Z.of_nat (cells_size [CB (Z.to_nat ((sz - ssz) / 8)) (fas ((sz - ssz) / 8))])) by (cbn [cells_size csize Nat.add]; rewrite K2; clear - K3; lia).
eapply cells_hjunk; [rewrite <- SHs; exact FAS| (first [ clear - SHu SHA SHa NG2 NG1 up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ])]. }
destruct (hjunk_cells _ _ _ HJt) as [j2 SHD2].
exists j1, j, j2, pb. repeat (split; [assumption|]). exact SHD2.
Qed.
End S.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ QmP7 QYyZ Qu3b QsDw QcfN QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QTVW.Mq3 QOJv.Mq4 QNQk.Mq2 Q9Ho.Mq2 QqLk QnRU.Mqa QmP7.Mq0 QpY2.Mq1 Q9Ho.Mq1 QYyZ.Mq0 QnRU.Mq0 QOJv.Mq5 Qu3b.Mq2 QYyZ.Mq5 QYyZ.Mq3 QpME.Mq1 QkJ4.
Import QsDw.Mq0.
Import QcfN.Mq1.
Import QlES.
Import QVo2.

Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma bst_assemble88 : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 88 j0] ->
rw_cells asegs m (obj + 104) [CB 1952 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 88%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1952%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 88 j0] ++ [CB 1952 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 88 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Definition cicpt_W (bp T : Z) : list (Z * Z) := [(bp - 2144 - 144, bp); (T + 3168, T + 3169)].

Lemma calloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo cnt sz : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 : word) (tsz : Z) (q : list word) (rest junk8 junk8b : list byte),
munch (cicpt_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp - 2144) ->
rw_cells asegs m' (bp - 2144) [CB 8 junk8b] ->
rw_cells asegs m' (bp - 2136) (unw_obj (bp - 2136) tsz q rest bp) -> length q = 5%nat ->
1 <= tsz <= 30 ->
rw_cells asegs m' (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR (wz 0x63814) (wz (bp + -2144)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz sz) (wz cnt) (wz sz) (wz (bp + -2136)) u3 u4 u5 u6 u7
(wz cnt) (wz 0x637a4) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_calloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x632cc) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL TU MI ST CEIL LO BPR UNW Hcnt Hsz CONT.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof (QSsj.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (cicpt_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold cicpt_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 9 step.
step.
step.
carve_frame 112%nat ST.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT2.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1952 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -72) in FRb by (cbn; lia) end.
apply (proj1 (rw_cells_app asegs _ _ [CB 8 _] _)) in FR0 as [J8 FR0].
lazymatch type of FR0 with rw_cells _ _ ?a _ => replace a with (bp + -2136) in FR0 by (cbn; lia) end.
replace (bp + -2032) with (bp + -2136 + 104) in FRa by lia.
replace (bp + -2120) with (bp + -2136 + 16) in FR0 by lia.
destruct (bst_assemble88 _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
step.
call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
destruct POST as (tsz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
clear URD FRc RT4.
step. step. step. step.
step.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) => lazymatch type of J8 with rw_cells _ _ _ [CB 8 ?j8b] =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ tsz q rest' j8 j8b); [exact MU| exact WM| assumption| exact ST2| exact J8| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2] end end.
Qed.
End S.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QV3O QjgW QpF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0 QjgW.
Import QpME.Mq8 QpF1.
Import QRfV.Mq3.
Import QpME.Mq8 QpF1.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma msz_eq : msz = ssz + 4095 - (ssz + 4095) mod 4096 + 4096.
Proof. subst msz ssz. unfold sec_map_size, sec_size, round_up, kPage. Z.div_mod_to_equations. lia. Qed.

Lemma alloc_shadow_sec : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (idx : word) (j1 j2 : list byte) (Q : machine_state -> Prop),
let up := A + 8 * ngran n' in
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m mb [C8 (wz mb); C8 (wz msz); C8 (wz ssz); C8 idx] ->
rw_cells asegs m (SH AB) [CB (Z.to_nat 256) j1] ->
rw_cells asegs m (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) j2] ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + (AB + sz - up) / 8)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (SH AB) [CB (Z.to_nat 256) (fas 256)] ->
rw_cells asegs m1 (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) (fas ((AB + sz - up) / 8))] ->
evt asegs Q (MS (mkR (wz 0x3f72c) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 (wz sz) (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz up) (wz obj) (wz 0) (wz (A + n' + 7)) (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f72c) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f640) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz A_INSTANCE) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f650) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros up RT MI ST CEIL LO HDRS.
pose proof sgeomS as (Grz & Gn' & GN & _ & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & _ & TD & _).
pose proof msz_eq as ME.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
assert (Gn1 : 1 <= n') by lia.
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHu : SH up = SH AB + 256 + ngran n') by (subst up A; rewrite SHa; unfold SH, A_SHADOW_OFS; subst AB; clear - MBP Grz NG2; Z.div_mod_to_equations; lia).
assert (UPB : AB + 2048 + n' <= up /\ up + 2048 <= AB + sz /\ (AB + sz - up) mod 8 = 0 /\ up mod 8 = 0).
{ assert (RU : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
subst up A sz AB. split; [(first [ clear - RU SHu SHa RU8 NG3 PK GK GndE GM1 Gssz GN Gn' Grz MBK msz ssz nd n' rz mb n RE BAND; lia | lia ])|]. split; [(first [ clear - RU SHu SHa RU8 NG3 PK GK GndE GM1 Gssz GN Gn' Grz MBK msz ssz nd n' rz mb n RE BAND; lia | lia ])| split; [clear - Gmsz Grz NG2 MBP; Z.div_mod_to_equations; lia| clear - MBP Grz GA16; Z.div_mod_to_equations; lia]]. }
destruct UPB as (UP1 & UP2 & UP3 & UP4).

remember ((AB + sz - up) / 8) as k2 eqn:EK2.
assert (K2 : 8 * k2 = AB + sz - up /\ 256 <= k2) by (subst k2; clear - UP2 UP3; Z.div_mod_to_equations; lia).
assert (SHe : SH (AB + sz) = SH up + k2) by (rewrite SHu, SHa; unfold SH, A_SHADOW_OFS; subst AB; clear - MBP Grz NG2 K2 UP1; Z.div_mod_to_equations; lia).
assert (MBH : 0x647000 <= mb) by (clear - GK GN Gnd1 Gssz GM1; lia).
assert (SHB : 0x80000000 <= SH AB /\ SH AB + 256 + ngran n' + k2 <= SH band_lo) by (rewrite SHa, (SH_eq band_lo); subst AB sz; clear - MBH GC K2 UP1 UP2 Gn1 Grz NG2; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD0.

assert (MK1 : Z.land 4095 AB = 0).
{ rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. subst AB. clear - MBP. Z.div_mod_to_equations. lia. }
assert (MK2 : Z.land (ssz + 4095) 18446744073709547520 = sz) by (rewrite land_pagemask by (first [ clear - MBH UP2 RU8 NG3 PK Gssz Gnd2 Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ]); (first [ clear - MBH SHe K2 EK2 k2 UP2 SHu SHa RU8 NG3 ME PK GM1 Gssz Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ])).
assert (MK3 : Z.land (A + n' + 7) 18446744073709551608 = up).
{ rewrite land_mask8 by (first [ clear - MBH UP2 RU8 NG3 PC PK GC Gssz Gnd1 GN Gn' Grz up AVP MBK sz A AB msz ssz nd n' rz mb n RE BAND; lia | lia ]). subst up. rewrite NG1. unfold round_up. clear - GA16 Gn1 Grz GK. Z.div_mod_to_equations. lia. }

clear Gmsz GA16 SHa ME NG1 EK2.
intros SHD1 SHD2 CONT.
pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp - 128); (SH AB, SH AB + 256); (SH up, SH up + k2)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
rtc RT 24%nat K24. rtc RT 25%nat K25. unfold A_INSTANCE in *. unfold prim_lo in GP, PK, PC.
step. if_true.
step.

assert (TAIL : forall (a1v : word),
evt asegs Q (MS (mkR (wz 0x3f640) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 0) (wz n') (wz (al_space_beg (ae_L RE))) a1v a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) (wz 977752) (wz obj) (wz 0) (wz (A + n')) (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f6ac) fc None m (seg_rom asegs))).
{ intros a1v.
step.
clear K24 K25.
stp.
step.
rewrite (unsigned_lit AB), MK1 by lia.
step. if_false.
stp. step. if_false.
step.
rewrite (unsigned_lit AB) by lia. replace (AB - 4096) with mb by lia.
step.
clear HDRS.
step.
rewrite ?(unsigned_lit ssz) by lia.
stp.
step.
rewrite (unsigned_lit (ssz + 4095)), ?(Z.land_comm 18446744073709547520), MK2 by lia.
step.
step.
step.
rewrite (unsigned_lit (A + n' + 7)), MK3 by lia.
step.
rewrite (unsigned_lit A), (unsigned_lit AB) by lia. replace (A - AB) with 2048 by lia.
stp. step.
step.
call_sp_ch (poison_shadow_spec_lh RE X) ltac:(fun PO => change (2048 / 8) with 256 in PO; clear SHD1 ST);
[exact RT| exact RL| assumption| exact ST| exact CEIL'| lia
| subst AB; clear - MBP; Z.div_mod_to_equations; lia| reflexivity| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - MBH SHe K2 k2 UP2 SHu RU8 NG3 GC GK GM1 Gssz Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])| lia| left; lia| exact SHD1|].
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH AB) _ |- _ => rename H into RT1; rename H2 into FA1 end.
step. step.
rewrite ?(unsigned_lit AB), ?(unsigned_lit up) by lia.
replace (AB - up + sz) with (8 * k2) by lia.
stp. step.
assert (D8 : 8 * k2 / 8 = k2) by (rewrite Z.mul_comm; apply Z.div_mul; lia). rewrite <- D8 in SHD2.
step.
call_sp_ch (poison_shadow_spec_lh RE X) ltac:(fun PO => rewrite ?D8 in PO; clear SHD2 ST1);
[exact RT1| exact RL| assumption| exact ST1| exact CEIL'| lia
| exact UP4| rewrite Z.mul_comm; apply Z.mod_mul; lia| lia| rewrite ?KHI_eq; change (2^47) with 140737488355328; (first [ clear - D8 MBH SHe K2 k2 UP2 SHu RU8 NG3 GC GK GM2 GM1 Gssz Gnd2 Gnd1 GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])| lia| left; lia| exact SHD2|].
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
match goal with H : RTconst RE X ?mm, H2 : rw_cells asegs ?mm (SH up) _ |- _ => rename H into RT2; rename H2 into FA2 end.
clear D8.
replace (8 * k2) with (AB + sz - up) by lia.
eapply CONT; [exact MU| exact WM| assumption| exact ST2| exact RT2| | ].
- unfold fas, fa_byte. exact FA1.
- unfold fas, fa_byte. exact FA2. }

destruct GP as [LOW|HIGH].
- step. unfold_cond; cond_unsig; if_true.
apply TAIL.
- step. unfold_cond; cond_unsig; if_false.
stp. stp. step.
step. unfold_cond; cond_unsig; if_true.
apply TAIL.
Qed.
End S.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QMSY.Mq0 QjgW.
Import QLxt.Mq0 QpME.Mq8 QpF1 QRfV.Mq2.
Import QRfV.Mq3.
Import QlES.
Import ListNotations. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Variables (n mb : Z) (gp : word).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sgeomS : rz = 2048 /\ n' = n /\ 64513 <= n <= 2^26 /\ nd mod 8 = 0 /\ n + 2048 <= nd /\ nd < n + 2056 /\ ssz = nd + 2048
/\ msz mod 4096 = 0 /\ ssz + 4096 <= msz /\ msz < ssz + 8192 /\ nd = 2048 + round_up n 8
/\ A mod 16 = 0 /\ appr_lia mb msz /\ mb + msz <= band_lo
/\ (mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb) /\ 0x10007fff8000 <= prim_lo RE /\ prim_lo RE + 2^37 + 0x1000 <= band_lo
/\ appr_lia (rl_T X) 4096 /\ rl_T X + 4096 <= band_lo /\ rl_T X mod 4096 = 0
/\ (mb + msz <= rl_T X \/ rl_T X + 4096 <= mb)
/\ appr_lia (rl_ctx X) 65536 /\ rl_ctx X + 65536 <= band_lo
/\ (mb + msz <= rl_ctx X \/ rl_ctx X + 65536 <= mb)
/\ appr_lia (rl_dn X) 0x100000 /\ rl_dn X + 0x100000 <= band_lo
/\ (mb + msz <= rl_dn X \/ rl_dn X + 0x100000 <= mb)
/\ appr_lia (rl_ssb X) 0x800000 /\ rl_ssb X + 0x800000 <= band_lo
/\ (mb + msz <= rl_ssb X \/ rl_ssb X + 0x800000 <= mb).
Proof. exact (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP). Qed.

Lemma alloc_stats_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (Q : machine_state -> Prop),
RTconst RE X m -> RStats RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
(forall m1 (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (rl_T X + 2904, rl_T X + 2904 + 8)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 -> RStats RE X m1 ->
evt asegs Q (MS (mkR (wz 0x3f7e4) (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f824) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f7e0) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RS MI ST CEIL LO CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
remember (rl_T X + 2904) as MBS eqn:EMBS.
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 128); (rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
step. call_sp_ch (get_thread_stats_spec RE X) ltac:(fun _ => idtac); [exact RT| exact RL| assumption| exact ST| exact CEIL'| lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST end.
match goal with H : RTconst RE X ?mm |- _ => rename H into RT1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(rl_T X + 2800, rl_T X + 2824); (MBS, MBS + 8)] mm) as MUh; pose proof (wmono_refl asegs mm) as WMh end.

pose proof RS as (HJ & ERR & OOM).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (HJ1 : hjunk mm (rl_T X + 2800) (rl_T X + 3168)) by (eapply hjunk_wmono; [exact HJ| exact WM]) end.
destruct (hjunk_split _ _ (rl_T X + 2824) _ HJ1 ltac:(lia)) as [HJa HJb].
replace (rl_T X + 2824) with (rl_T X + 2800 + 24) in HJa by lia. destruct (hjunk_C8x3 RE 0 0 _ _ HJa) as (w1 & w2 & w3 & STA).
destruct (hjunk_split _ _ MBS _ HJb ltac:(lia)) as [_ HJc]. destruct (hjunk_split _ _ (MBS + 8) _ HJc ltac:(lia)) as [HJd _].
destruct (hjunk_C8 _ _ HJd) as (w4 & STB). clear HJ1 HJa HJb HJc HJd.
step. step. step.
step. step.
stp. stp.
step. step.
step. step. step.
step. ifz.
rewrite EMBS in STB.
step. step. step.
eapply CONT; [exact MU| exact WM| assumption| exact ST| |].
- eapply RTconst_munch; [exact RT1| exact MUh| exact WMh|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor].
- destruct ERR as [e ERR]. destruct OOM as [b OOM]. unfold A_ERRNO in ERR.
split; [eapply hjunk_wmono; [exact HJ| exact WM]|].
split; [exists e; unfold A_ERRNO| exists b];
(eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia]).
Qed.

Lemma alloc_fill_sec : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj cf : Z) (fj : list byte) (v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) -> 0 <= cf <= 1 ->
hjunk m A (AB + sz) ->
(forall m1 (u u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(A, A + Z.min n' 4096)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp + -128) -> RTconst RE X m1 ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj (wz cf) v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
hjunk m1 A (AB + sz) -> (cf = 0 -> m1 = m) ->
evt asegs Q (MS (mkR u (wz (bv_unsigned sp + -128)) gp (wz A_TP) u0 u1 u2 s0v (wz n') u3 u4 u5 u6 u7 u10 u11 u12
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) u14 u15 u16 u17)
F (wz 0x3f974) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR (wz 0x3f7e4) (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f824) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR CF HJU CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (mn := Z.min n' 4096) in *. assert (MN : 1 <= mn <= n' /\ mn <= 4096) by lia.
pose proof (munch_refl [(A, A + mn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold alloc_frame in FR.
step.
step.
destruct (Z.eq_dec cf 0) as [CF0|CF1].
- subst cf. if_lit. step.  eapply CONT; [exact MU| exact WM| exact MI| exact ST| exact RT| exact FR| exact HJU| intros _; reflexivity].
- ifz.
rtc RT 19%nat K19. rtc RT 12%nat K12. rtc RT 23%nat K23.
step. step.
stp.
step. if_lit.
step.

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => ms1 = MS (@bvmap_set 5 word 12 (wz mn) R) FF (wz 0x3f95c) fcc rv mm ro))
end.
{ step. destruct (Z.ltb_spec n' 4096) as [LT|GE]; ifz.
- apply evt_done. simp_regs. replace mn with n' by lia. reflexivity.
- step. apply evt_done. simp_regs. replace mn with 4096 by lia. reflexivity. }
intros ms1 ->. simp_regs.
step. step.
step.
stp.
step.
destruct (hjunk_split _ _ (A + mn) _ HJU ltac:(lia)) as [HJ1 HJ2].
replace (A + mn) with (A + Z.of_nat (Z.to_nat mn)) in HJ1 by lia. destruct (hjunk_cells _ _ _ HJ1) as [junk UC].
step.
eapply evt_cut; [eapply memset_spec; [rewrite !unsigned_lit by lia; exact UC| assumption]|].
intros ms' PO. unfold memset_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & MU2 & WM2 & MI2 & UC2).
replace (ret_pc (wz 260468)) with (wz 260468) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
eapply CONT; [exact MU2| exact WM2| exact MI2| | | | | intros E0; exfalso; exact (CF1 E0)].
+ eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn [disjoint_from]; lia].
+ eapply RTconst_munch; [exact RT| exact MU2| exact WM2|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia| constructor].
+ eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
+ eapply hjunk_merge; [| eapply hjunk_wmono; [exact HJ2| exact WM2]].
replace (A + mn) with (A + Z.of_nat (cells_size [CB (Z.to_nat mn) (repeat (b8 (190 mod 256)) (Z.to_nat mn))])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact UC2| lia].
Qed.

Lemma alloc_fin_sec : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (s0v s6v s9v : word) (sp : word) (F : bvmap 5 word) fc m lo
(obj : Z) (fj : list byte) (canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav : word) (b0 b1 : byte) (idw g1 g2 : word)
(Q : machine_state -> Prop),
RTconst RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 816 ->
rw_cells asegs m (bv_unsigned sp + -128) (alloc_frame fj canfill v11 v10 v9 v8 v7 v6 v5 v4 v3 v2 v1 v0 rav) ->
rw_cells asegs m (A + -16) [C1 b0; C1 (b8 (hb1 b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m AB [C8 g1; C8 g2]) ->
(forall m1 (u0 u1 u2 u4 u5 u6 u7 u10 u11 u12 u14 u15 u16 u17 : word),
munch [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m m1 ->
wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) -> RTconst RE X m1 ->
rw_cells asegs m1 (A + -16) [C1 (b8 2); C1 (b8 (hb1f b1)); C2 (wz 0); C4 (wz n'); C8 idw] ->
(16 < rz -> rw_cells asegs m1 AB [C8 (wz kMagic); C8 (wz (A + -16))]) ->
evt asegs Q (MS (mkR rav sp gp (wz A_TP) u0 u1 u2 v0 v1 (wz A) u4 u5 u6 u7 u10 u11 u12
v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 u14 u15 u16 u17)
F (ret_pc rav) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 s0v (wz n') a0 a1 a2 a3 a4 a5 a6 a7
(wz AB) (wz ssz) (wz A) (wz (A + -16)) s6v (wz obj) (wz 0) s9v (wz (rl_T X)) (wz 1) t3 t4 t5 t6)
F (wz 0x3f974) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT MI ST CEIL LO FR HDR MG CONT.
pose proof sgeomS as (Grz & Gn' & GN & Gnd8 & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & GP & PK & PC & TK' & TB & TA & TD & _).
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (hb1_facts b1) as [HB1 HBF].
pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (FWrt : Forall (rt_avoid RE X) [(bv_unsigned sp - 160, bv_unsigned sp); (AB, AB + 16); (A + -16, A)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia|].
constructor; [apply (rt_avoid_sec RE X n mb RL Hn HP MBP MBK MBC AVO AVP); try unfold A in *; unfold AB, sz, msz, ssz, nd, rz in *; lia| constructor]. }
unfold alloc_frame in FR.

Local Ltac fin_head RT MI HDR b1 :=
step; call0 (lsan_disabled_spec RE X); [exact RT| exact MI|]; subst_words;
step;
stp; stp;
step;
rewrite zxb_b8, (Z.mod_small (hb1 b1) 256), (unsigned_lit (hb1 b1)) by lia; change (Z.land (hb1 b1) 243) with (hb1f b1);
step;
rewrite (unsigned_lit (hb1f b1)), Z.lor_0_r by lia;
stp;
step;
rewrite (unsigned_lit (hb1f b1)) in HDR by lia;
step;
stf;
change (bv_unsigned (wz 2)) with 2 in HDR;
step.

Local Ltac fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR MG :=
let RTc := fresh "RTc" in let RT1 := fresh "RT1" in let ST1 := fresh "ST1" in
step; step; step;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RTc : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact FWrt]) end;
call_sp_ch (run_malloc_hooks_spec RE X) ltac:(fun _ => idtac); [exact RTc| exact RL| assumption| exact ST| exact CEIL'| lia|];
match goal with H : stk asegs _ _ _ |- _ => rename H into ST1 end;
match goal with H : RTconst RE X _, H' : mem_inv asegs ?mm |- _ => lazymatch type of H with RTconst _ _ mm => rename H into RT1 end end;
step; do 13 step; step;
release_frame FR ST1 (bv_unsigned sp);
step;
eapply CONT; [exact MU| exact WM| assumption| exact ST1| exact RT1| exact HDR| MG].

- specialize (MG ltac:(lia)).
fin_head RT MI HDR b1.
ifz.
step. step. ifz.
step. step.
step.
step.
stf.
fin_tail sp RT MU WM FWrt ST CEIL' FR CONT HDR ltac:(intros _; exact MG).
Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QpY2.Mqb QjgW QpF1.
Import QRfV.Mq3.
Import QlES.
Import QpME. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Local Ltac lia ::= lia_fast. Local Ltac mkr__lia_0 := lia_fast.
Local Ltac Q0z1.transport_lia ::= tslia_fast. Local Ltac mkr__transport_lia_1 := tslia_fast.
Local Ltac QbcP_c1.if_lit ::= if_lit_fast. Local Ltac mkr__if_lit_2 := if_lit_fast.
Local Ltac QN4c.sfp_cheap ::= sfp_fast. Local Ltac mkr__sfp_cheap_3 := sfp_fast.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation zeros k := (repeat (b8 0) (Z.to_nat k)).

Lemma zsplit : forall m a N k, rw_cells asegs m a [CB (Z.to_nat N) (zeros N)] -> 0 <= k <= N ->
rw_cells asegs m a [CB (Z.to_nat k) (zeros k)] /\ rw_cells asegs m (a + k) [CB (Z.to_nat (N - k)) (zeros (N - k))].
Proof.
intros m a N k H Hk.
assert (H' : rw_cells asegs m a ([CB (Z.to_nat k) (zeros k)] ++ [CB (Z.to_nat (N - k)) (zeros (N - k))])).
{ eapply rw_cells_recast'; [exact H| cbn; rewrite !repeat_length; lia|].
cbn [cells_bytes cbytes app]. rewrite !app_nil_r, <- repeat_app. f_equal. lia. }
apply (proj1 (rw_cells_app asegs m a _ _)) in H'. cbn [cells_size csize Nat.add] in H'. rewrite Nat.add_0_r in H'.
replace (a + Z.of_nat (Z.to_nat k)) with (a + k) in H' by lia. exact H'.
Qed.

Lemma zeros_hdr : forall m a, rw_cells asegs m a [CB (Z.to_nat 16) (zeros 16)] ->
rw_cells asegs m a [C1 (b8 0); C1 (b8 0); C2 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast'; [exact H| cbn; tauto| reflexivity]. Qed.

Lemma zeros_C8x2 : forall m a, rw_cells asegs m a [CB (Z.to_nat 16) (zeros 16)] -> rw_cells asegs m a [C8 (wz 0); C8 (wz 0)].
Proof. intros m a H. eapply rw_cells_recast'; [exact H| cbn; tauto| reflexivity]. Qed.

Lemma zeros_hjunk : forall m a N, rw_cells asegs m a [CB (Z.to_nat N) (zeros N)] -> 0 <= N -> 0x647000 <= a -> hjunk m a (a + N).
Proof.
intros m a N H HN Ha. replace (a + N) with (a + Z.of_nat (cells_size [CB (Z.to_nat N) (zeros N)])) by (cbn [cells_size csize Nat.add]; lia).
eapply cells_hjunk; [exact H| exact Ha].
Qed.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Variables (n mb : Z).
Let rz := rz_size n.
Let n' := used_size n.
Let nd := needed n.
Let ssz := sec_size n.
Let msz := sec_map_size n.
Let AB := mb + 4096.
Let A := AB + rz.
Let sz := msz - 4096.
Hypothesis RL : rlay_ok RE X.
Hypothesis Hn : 0 <= n <= 2^26.
Hypothesis HP : from_primary n = false.
Hypothesis MBP : mb mod 4096 = 0.
Hypothesis MBK : appr_lia mb msz.
Hypothesis MBC : mb + msz <= band_lo.
Hypothesis AVO : forall o, In o (rlay_objs RE X) -> mb + msz <= fst o \/ fst o + snd o <= mb.
Hypothesis AVP : mb + msz <= prim_lo RE \/ prim_lo RE + (2^37 + 0x1000) <= mb.
Set Default Proof Using "RL Hn HP MBP MBK MBC AVO AVP".

Lemma sec_pieces : forall m,
let up := A + 8 * ngran n' in
rw_cells asegs m AB [CB (Z.to_nat sz) (zeros sz)] ->
hjunk m (SH AB) (SH (AB + ssz)) ->
rw_cells asegs m (SH (AB + ssz)) [CB (Z.to_nat ((sz - ssz) / 8)) (fas ((sz - ssz) / 8))] ->
exists (j1 j j2 : list byte) (pb : byte),
rw_cells asegs m AB [C8 (wz 0); C8 (wz 0)]
/\ hjunk m (AB + 16) (A + -16)
/\ rw_cells asegs m (A + -16) [C1 (b8 0); C1 (b8 0); C2 (wz 0); C4 (wz 0); C8 (wz 0)]
/\ rw_cells asegs m A [CB (Z.to_nat n) (zeros n)]
/\ hjunk m (A + n) (AB + sz)
/\ rw_cells asegs m (SH AB) [CB (Z.to_nat 256) j1]
/\ rw_cells asegs m (SH A) [CB (Z.to_nat (8 * (n' / 8) / 8)) j]
/\ (n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb])
/\ rw_cells asegs m (SH up) [CB (Z.to_nat ((AB + sz - up) / 8)) j2].
Proof.
intros m up BODY HJ FAS.
pose proof (sgeom RE X n mb RL Hn HP MBP MBK MBC AVO AVP) as (Grz & Gn' & GN & _ & Gnd1 & Gnd2 & Gssz & Gmsz & GM1 & GM2 & GndE & GA16 & GK & GC & _).
fold rz n' nd ssz msz AB A in Grz, Gn', Gnd1, Gnd2, Gssz, Gmsz, GM1, GM2, GndE, GA16, GC.
assert (MB6 : 0x647000 <= mb) by (clear - MBK GM1 Gssz Gnd1 GN; lia).
pose proof (ngran_eq n' ltac:(lia)) as (NG1 & NG2 & NG3). pose proof (round_up_8 n' ltac:(lia)) as [RU8 _].
assert (RU : round_up n' 8 = round_up n 8) by (rewrite Gn'; reflexivity).
assert (N8 : 0 <= n' / 8 /\ 0 <= n' mod 8 < 8 /\ n' = 8 * (n' / 8) + n' mod 8) by (clear - GN Gn'; Z.div_mod_to_equations; lia).
assert (D8 : 8 * (n' / 8) / 8 = n' / 8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
assert (SHa : SH AB = AB / 8 + 0x7fff8000) by reflexivity.
assert (SHA : SH A = SH AB + 256) by (subst A; rewrite Grz, <- (SH_plus8 AB 256); reflexivity).
assert (SHu : SH up = SH A + ngran n') by (subst up; rewrite <- SH_plus8; reflexivity).
assert (SHs : SH (AB + ssz) = SH up + 256).
{ replace (AB + ssz) with (up + 8 * 256) by (subst up A; rewrite Gssz, GndE, Grz, <- RU, NG3; lia). rewrite SH_plus8. reflexivity. }
assert (K2 : (AB + sz - up) / 8 = 256 + (sz - ssz) / 8 /\ 0 <= (sz - ssz) / 8).
{ subst up A sz. clear - Gmsz GM1 GM2 NG2 Gssz GndE RU NG3 Grz. Z.div_mod_to_equations. (first [ clear - H9 q1 H5 H4 r0 q0 H0 H r q RU NG3 GndE GM1 Gmsz r1 Gssz Grz AB msz ssz nd n' rz mb n; lia | lia ]). }
destruct K2 as [K2 K3].
assert (SB : 0x647000 <= SH AB) by (rewrite SHa; subst AB; rewrite ?KHI_eq in MBK; clear - MBK; Z.div_mod_to_equations; lia).

destruct (zsplit m AB sz 16 BODY ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z1 R1]. pose proof (zeros_C8x2 _ _ Z1) as MG.
destruct (zsplit m (AB + 16) (sz - 16) (rz - 32) R1 ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z2 R2]. pose proof (zeros_hjunk _ _ _ Z2 ltac:((first [ clear - MB6 Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ])) ltac:(rewrite ?KHI_eq in MBK; (first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as HJm.
replace (AB + 16 + (rz - 32)) with (A + -16) in HJm, R2 by (subst A; lia).
destruct (zsplit m (A + -16) (sz - 16 - (rz - 32)) 16 R2 ltac:((first [ clear - MB6 GM1 Gssz Gnd1 Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [Z3 R3]. pose proof (zeros_hdr _ _ Z3) as HDR.
replace (A + -16 + 16) with A in R3 by lia.
destruct (zsplit m A (sz - 16 - (rz - 32) - 16) n R3 ltac:((first [ clear - SHu N8 RU RU8 NG3 MB6 GndE GM1 Gssz GN Gn' Grz up MBK Hn sz A AB msz ssz nd n' rz mb n BAND; lia | lia ]))) as [UZ R4].
pose proof (zeros_hjunk _ _ _ R4 ltac:((first [ clear - SHu N8 RU RU8 NG3 MB6 GndE GM1 Gssz GN Gn' Grz up MBK sz A AB msz ssz nd n' rz mb n BAND; lia | lia ])) ltac:(rewrite ?KHI_eq in MBK; (first [ clear - MB6 GN Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ]))) as HJU.
replace (A + n + (sz - 16 - (rz - 32) - 16 - n)) with (AB + sz) in HJU by (subst A; lia).

destruct (hjunk_split _ _ (SH A) _ HJ ltac:(rewrite SHs, SHu, SHA; lia)) as [HJ1 HJr].
replace (SH A) with (SH AB + Z.of_nat (Z.to_nat 256)) in HJ1 by (first [ clear - SHA MB6 Grz up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ]). destruct (hjunk_cells _ _ _ HJ1) as [j1 SHD1].
destruct (hjunk_split _ _ (SH A + n' / 8) _ HJr ltac:(rewrite SHs, SHu, NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia)) as [HJ2 HJr2].
replace (SH A + n' / 8) with (SH A + Z.of_nat (Z.to_nat (8 * (n' / 8) / 8))) in HJ2 by (rewrite D8; clear - N8; lia).    destruct (hjunk_cells _ _ _ HJ2) as [j PZ].
destruct (hjunk_split _ _ (SH up) _ HJr2 ltac:(rewrite SHs, SHu, NG1; unfold round_up; clear - N8; Z.div_mod_to_equations; lia)) as [HJ3 HJ4].
assert (PB : exists pb : byte, n' mod 8 <> 0 -> rw_cells asegs m (SH A + n' / 8) [C1 pb]).
{ destruct (Z.eq_dec (n' mod 8) 0) as [Z0|NZ].
- exists (b8 0). intros NE. exfalso. exact (NE Z0).
- replace (SH up) with (SH A + n' / 8 + Z.of_nat 1%nat) in HJ3 by (rewrite SHu, NG1; unfold round_up; clear - N8 NZ; Z.div_mod_to_equations; lia).
destruct (hjunk_cells _ _ _ HJ3) as [pbs PB1].
assert (L1 : length pbs = 1%nat) by (destruct PB1 as [[[WF _] _] _]; cbn in WF; lia). destruct pbs as [|pb [|]]; [cbn in L1; clear - L1; lia| | cbn in L1; clear - L1; lia].
exists pb. intros _. eapply rw_cells_recast'; [exact PB1| cbn; tauto| reflexivity]. }
destruct PB as [pb PB].
assert (HJt : hjunk m (SH up) (SH up + Z.of_nat (Z.to_nat ((AB + sz - up) / 8)))).
{ eapply hjunk_merge; [exact HJ4|]. rewrite SHs.
replace (SH up + Z.of_nat (Z.to_nat ((AB + sz - up) / 8))) with (SH up + 256 + Z.of_nat (cells_size [CB (Z.to_nat ((sz - ssz) / 8)) (fas ((sz - ssz) / 8))])) by (cbn [cells_size csize Nat.add]; rewrite K2; clear - K3; lia).
eapply cells_hjunk; [rewrite <- SHs; exact FAS| (first [ clear - SHu SHA SHa NG2 NG1 up MBK sz A AB msz ssz n' rz mb n BAND; lia | lia ])]. }
destruct (hjunk_cells _ _ _ HJt) as [j2 SHD2].
exists j1, j, j2, pb. repeat (split; [assumption|]). exact SHD2.
Qed.
End S.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr QvDJ.Mq2.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QYyZ.Mqc QYyZ.Mqa QpME.Mq8 QpF1.
Import QsDw.Mq1.
Import QcfN.Mq4.
Import QlES.
Import QVo2.Mq2.

Import ListNotations.
Import Qc6I.Exc. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma bst_assemble88 : forall m obj (j0 j1 : list byte) (bpw : word),
rw_cells asegs m obj [C8 (wz (obj + 16)); C8 (wz 0); CB 88 j0] ->
rw_cells asegs m (obj + 104) [CB 1952 j1; C8 bpw] ->
exists (q0 q1 q2 q3 q4 : word) (rest : list byte),
rw_cells asegs m obj (unw_obj obj 0 [q0; q1; q2; q3; q4] rest (bv_unsigned bpw)).
Proof.
intros m obj j0 j1 bpw H0 H1.
assert (L0 : length j0 = 88%nat) by (destruct H0 as [[WF _] _]; cbn in WF; tauto).
assert (L1 : length j1 = 1952%nat) by (destruct H1 as [[WF _] _]; cbn in WF; tauto).
assert (H : rw_cells asegs m obj ([C8 (wz (obj + 16)); C8 (wz 0); CB 88 j0] ++ [CB 1952 j1; C8 bpw])).
{ apply (proj2 (rw_cells_app asegs m obj _ _)). cbn [cells_size csize Nat.add]. split; [exact H0| exact H1]. }
do 40 (let b := fresh "y" in destruct j0 as [|b j0]; [cbn in L0; lia|]). cbn in L0.
match type of H with context [CB 88 (?y0 :: ?y1 :: ?y2 :: ?y3 :: ?y4 :: ?y5 :: ?y6 :: ?y7 :: ?z0 :: ?z1 :: ?z2 :: ?z3 :: ?z4 :: ?z5 :: ?z6 :: ?z7 ::
?u0 :: ?u1 :: ?u2 :: ?u3 :: ?u4 :: ?u5 :: ?u6 :: ?u7 :: ?v0 :: ?v1 :: ?v2 :: ?v3 :: ?v4 :: ?v5 :: ?v6 :: ?v7 ::
?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: j0)] =>
exists (wz (bytes_le_to_Z [y0; y1; y2; y3; y4; y5; y6; y7])), (wz (bytes_le_to_Z [z0; z1; z2; z3; z4; z5; z6; z7])),
(wz (bytes_le_to_Z [u0; u1; u2; u3; u4; u5; u6; u7])), (wz (bytes_le_to_Z [v0; v1; v2; v3; v4; v5; v6; v7])),
(wz (bytes_le_to_Z [x0; x1; x2; x3; x4; x5; x6; x7])), (j0 ++ j1)
end.
eapply rw_cells_recast'; [exact H| |].
- unfold unw_obj. cbn. rewrite length_app. lia.
- unfold unw_obj. cbn [map app cells_bytes cbytes]. rewrite Z_to_bv_bv_unsigned.
rewrite (le8_split32 0) by lia. rewrite !le8_of_bytes by reflexivity.
cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Let atn := at_nodeA L asegs.

Definition cicpt_W (bp T : Z) : list (Z * Z) := [(bp - 2144 - 144, bp); (T + 3168, T + 3169)].

Lemma calloc_icpt_pre : forall (ra : word) (bp : Z) (gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo cnt sz : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> rw_cells asegs m (rl_T X + 3168) [C1 (b8 0)] -> mem_inv asegs m ->
stk asegs m lo bp -> band_lo <= lo -> lo <= bp - CALLOC_STACK -> 0 <= bp < 2^64 ->
unw_readable asegs RE m bp ->
0 <= cnt < 2^64 -> 0 <= sz < 2^64 ->
(forall m' (u0 u1 u2 u3 u4 u5 u6 u7 u10 u11 u12 u13 : word) (tsz : Z) (q : list word) (rest junk8 junk8b : list byte),
munch (cicpt_W bp (rl_T X)) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bp - 2144) ->
rw_cells asegs m' (bp - 2144) [CB 8 junk8b] ->
rw_cells asegs m' (bp - 2136) (unw_obj (bp - 2136) tsz q rest bp) -> length q = 5%nat ->
1 <= tsz <= 30 ->
rw_cells asegs m' (bp + -72) [CB 8 junk8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
RTconst RE X m' -> rw_cells asegs m' (rl_T X + 3168) [C1 (b8 0)] ->
evt asegs Q (MS (mkR (wz 0x63bec) (wz (bp + -2144)) gp (wz A_TP) u0 u1 u2 (wz bp) (wz sz) (wz cnt) (wz sz) (wz (bp + -2136)) u3 u4 u5 u6 u7
(wz cnt) (wz 0x63b7c) (wz 1) (wz (bp + -2136)) (wz (bp + -89)) s7 s8 s9 s10 s11 u10 u11 u12 u13)
F (wz asan_calloc_entry) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz bp) gp (wz A_TP) t0 t1 t2 s0 s1 (wz cnt) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x636a4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL TU MI ST CEIL LO BPR UNW Hcnt Hsz CONT.
pose proof CEIL as CEIL'. idtac. unfold CALLOC_STACK, ALLOC_STACK in LO.
pose proof (QKBN.rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB. idtac. rewrite ?KHI_eq in TK.
pose proof (munch_refl (cicpt_W bp (rl_T X)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold cicpt_W in MU.
assert (RTW : Forall (rt_avoid RE X) [(bp - 2144 - 144, bp); (rl_T X + 3168, rl_T X + 3169)]).
{ constructor; [apply rt_avoid_stack; [exact RL| lia]|]. constructor; [apply rt_avoid_Thigh; [exact RL| lia| lia]| constructor]. }
unfold A_INSTANCE in *.
step.
carve_frame 2032%nat ST.
do 9 step.
step.
step.
carve_frame 112%nat ST.
step. step. step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT1 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end.
call_ch (try_asan_init_spec RE X) ltac:(fun PO => rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT1| exact RL| assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL'| rewrite unsigned_lit by lia; lia|].
subst_words. match goal with H : stk asegs _ lo _ |- _ => try rename H into ST1 end.
match goal with H : RTconst RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RT2 end. clear RT1.
step. if_lit.
step. step. step. step. step.
stf.
step.
stf.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT3 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT2.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
stp. step. if_lit.
step. call0 (get_current_pc_spec); []. subst_words.
rtc RT3 19%nat K19. rtc RT3 15%nat K15.
step. step.
stp.
step.
step. call0 (malloc_ctx_size_spec RE X); [exact RT3| assumption|]. subst_words.
step. stp. stp.
step.
rewrite (unsigned_lit bp), and_all_ones by lia.
stp.
step.
step. if_lit.
step. step. step. step. stp. step.

apply (proj1 (rw_cells_app asegs _ _ [CB 1952 _; C8 (wz bp)] _)) in FR as [FRa FRb].
lazymatch type of FRb with rw_cells _ _ ?a _ => replace a with (bp + -72) in FRb by (cbn; lia) end.
apply (proj1 (rw_cells_app asegs _ _ [CB 8 _] _)) in FR0 as [J8 FR0].
lazymatch type of FR0 with rw_cells _ _ ?a _ => replace a with (bp + -2136) in FR0 by (cbn; lia) end.
replace (bp + -2032) with (bp + -2136 + 104) in FRa by lia.
replace (bp + -2120) with (bp + -2136 + 16) in FR0 by lia.
destruct (bst_assemble88 _ _ _ _ _ FR0 FRa) as (q0 & q1 & q2 & q3 & q4 & rest & OBJ). rewrite (unsigned_lit bp) in OBJ by lia. clear FR0 FRa.
pose proof FRb as FRc. apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _)) in FRc as [_ FRc].
lazymatch type of FRc with rw_cells _ _ ?a _ => replace a with (bp - 16) in FRc by (cbn; lia) end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (RT4 : RTconst RE X mc) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| exact RTW]) end. clear RT3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => assert (URD : unw_readable asegs RE mc (bp - 16)) end.
{ eapply (unw_readable_prologue RE _ m _ bp s0 ra); [exact MU| intros z Hz; cbn [outside]; lia| exact FRc| exact UNW]. }
step.
call_ch (unwind_impl_spec RE X) ltac:(fun PO => unfold unwind_stack in PO; rewrite !(unsigned_lit (bp + -2144)) in PO by lia);
[exact RT4| exact RL| assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold unwind_stack; lia
| exact OBJ| exact TU| exact URD| lia| rewrite unsigned_lit by lia; lia| lia| lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST2 end.
destruct POST as (tsz & q & rest' & OBJ2 & LQ & TU2 & SZR & RT5).
clear URD FRc RT4.
step. step. step. step.
step.
lazymatch type of FRb with rw_cells _ _ _ (CB 8 ?j8 :: _) => lazymatch type of J8 with rw_cells _ _ _ [CB 8 ?j8b] =>
eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ tsz q rest' j8 j8b); [exact MU| exact WM| assumption| exact ST2| exact J8| exact OBJ2| exact LQ| exact SZR| exact FRb| exact RT5| exact TU2] end end.
Qed.
End S.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI QDpG_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QOJv.Mqa QOJv.Mqb QnRU.Mqi QVo2.Mq3.
Import QpY2.Mqc.
Import QteI.Mqg QRfV.Mq4 QteI.Mqh QDpG_c1.Mq2.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma frame_stack_only : forall a G m m1 lo hi cl v,
munch [(lo, hi)] m m1 -> wmono asegs m m1 -> rlay_ok RE X -> band_lo <= lo ->
(RTconst RE X m -> RTconst RE X m1) /\ (RStats RE X m -> RStats RE X m1) /\ (RPrimL a G RE X m cl v -> RPrimL a G RE X m1 cl v).
Proof.
intros a G m m1 lo hi cl v MU WM RL CEIL.
split; [| split].
- intros RT. eapply RTconst_munch; [exact RT| exact MU| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| exact CEIL]| constructor].
- intros RS. eapply RStats_munch; [exact RS| exact MU| exact WM|]. constructor; [| constructor].
st_avoid_solve.
- intros RP. eapply RPrimL_stack; [exact RP| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; exact CEIL| constructor].
Qed.

Lemma populate_spec : forall ra sp gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c req lo v : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
1 <= c <= 30 -> 0 <= req <= 8 ->
aimplT atn (populate (ae_L RE) a c req) s
(pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user (cls a c)) lo m v)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 2768)) (wz c) (wz (ri_addr RE c)) (wz req) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz populate_entry) fc None m (seg_rom asegs)).
Proof.
intros until v; intros RT RL RS RP MI ST CEIL LO Hc Hreq.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & _ & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
unfold populate. replace (req * class_size c) with (class_size c * req) by lia.
eapply aimplT_evt.
{ eapply (populate_A RE X); try eassumption; lia. }
intros ms1 (a5' & a6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1). clear RI.
destruct (frame_stack_only a G m m1 _ _ c v MU1 WM1 RL ltac:(idtac; lia)) as (HRT & HRS & HRP).
specialize (HRT RT). specialize (HRS RS). specialize (HRP RP).
assert (MU1' : munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user (cls a c))) m m1).
{ eapply munch_weaken; [| exact MU1]. unfold pop_W, POPULATE_STACK. sub_fp_solve. }
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE].
-
eapply aimplT_bind.
{ apply (populate_B L RE X ra sp gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5' a6' a7 t3 t4 t5 t6 F fc m m1 s a G c req lo v);
try eassumption; unfold POPULATE_STACK; lia. }
intros [ok a1] s' ms' [-> POST]. cbn [fst snd] in POST. destruct ok; cbn [negb].
+ destruct POST as (EQA & x1 & u0 & u1 & u2 & x9 & v1 & v2 & v4 & v5 & v6 & v7 & x19 & x22 & u3 & u4 & u5 & u6 & m2
& -> & MU2 & WM2 & MI2 & ST2 & FR2 & RT2 & RS2 & RP2).
rewrite <- EQA in MU2 |- *.
eapply aimplT_mono; [apply (populate_C L RE X x1 u0 u1 u2 x9 v1 v2 v4 v5 v6 v7 x19 x22 u3 u4 u5 u6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
F fc m m2 s a1 G c lo v); try eassumption; unfold POPULATE_STACK; lia|].
cbn beta. intros r s' ms' [_ H]. exact H.
+ destruct POST as [-> POST]. apply aimplT_ret. apply evt_done. exact POST.
-
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\
ms' = MS (mkR ra (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user (cls a c))) (wz req) a5' a6' a7
(wz (reg_beg (ae_L RE) c)) (wz (c_alloc_user (cls a c) + class_size c * req)) (wz (c_mapped_user (cls a c))) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x44798) fc None m1 (seg_rom asegs)).
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb].
eapply aimplT_mono; [apply (populate_C L RE X ra t0 t1 t2 (wz (rl_T X + 2768)) (wz (c * 4294967296)) (wz c) (wz req) a5' a6' a7
(wz (c_alloc_user (cls a c) + class_size c * req)) s6 t3 t4 t5 t6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
F fc m m1 s a G c lo v); try eassumption; unfold POPULATE_STACK; lia|].
cbn beta. intros r s' ms' [_ H]. exact H.
Qed.
End S.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDpG_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDpG_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma frame_stack_only : forall a G m m1 lo hi cl v,
munch [(lo, hi)] m m1 -> wmono asegs m m1 -> rlay_ok RE X -> band_lo <= lo ->
(RTconst RE X m -> RTconst RE X m1) /\ (RStats RE X m -> RStats RE X m1) /\ (RPrimL a G RE X m cl v -> RPrimL a G RE X m1 cl v).
Proof.
intros a G m m1 lo hi cl v MU WM RL CEIL.
split; [| split].
- intros RT. eapply RTconst_munch; [exact RT| exact MU| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| exact CEIL]| constructor].
- intros RS. eapply RStats_munch; [exact RS| exact MU| exact WM|]. constructor; [| constructor].
st_avoid_solve.
- intros RP. eapply RPrimL_stack; [exact RP| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; exact CEIL| constructor].
Qed.

Lemma populate_spec : forall ra sp gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (c req lo v : Z),
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrimL a G RE X m c v -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
1 <= c <= 30 -> 0 <= req <= 8 ->
aimplT atn (populate (ae_L RE) a c req) s
(pop_post RE X ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s G c (c_alloc_user (cls a c)) lo m v)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 2768)) (wz c) (wz (ri_addr RE c)) (wz req) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz populate_entry) fc None m (seg_rom asegs)).
Proof.
intros until v; intros RT RL RS RP MI ST CEIL LO Hc Hreq.
pose proof CEIL as CEIL'. idtac. unfold POPULATE_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.

destruct (RPrimL_open _ _ _ _ _ _ _ RP) as (K & HJS & GNE & HCall & _ & HC). apply class_repL_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & _ & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
unfold populate. replace (req * class_size c) with (class_size c * req) by lia.
eapply aimplT_evt.
{ eapply (populate_A RE X); try eassumption; lia. }
intros ms1 (a5' & a6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1). clear RI.
destruct (frame_stack_only a G m m1 _ _ c v MU1 WM1 RL ltac:(idtac; lia)) as (HRT & HRS & HRP).
specialize (HRT RT). specialize (HRS RS). specialize (HRP RP).
assert (MU1' : munch (pop_W RE X (bv_unsigned sp) c (c_alloc_user (cls a c))) m m1).
{ eapply munch_weaken; [| exact MU1]. unfold pop_W, POPULATE_STACK. sub_fp_solve. }
destruct (Z.ltb_spec (c_mapped_user (cls a c)) (c_alloc_user (cls a c) + class_size c * req)) as [LT|GE].
-
eapply aimplT_bind.
{ apply (populate_B L RE X ra sp gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a5' a6' a7 t3 t4 t5 t6 F fc m m1 s a G c req lo v);
try eassumption; unfold POPULATE_STACK; lia. }
intros [ok a1] s' ms' [-> POST]. cbn [fst snd] in POST. destruct ok; cbn [negb].
+ destruct POST as (EQA & x1 & u0 & u1 & u2 & x9 & v1 & v2 & v4 & v5 & v6 & v7 & x19 & x22 & u3 & u4 & u5 & u6 & m2
& -> & MU2 & WM2 & MI2 & ST2 & FR2 & RT2 & RS2 & RP2).
rewrite <- EQA in MU2 |- *.
eapply aimplT_mono; [apply (populate_C L RE X x1 u0 u1 u2 x9 v1 v2 v4 v5 v6 v7 x19 x22 u3 u4 u5 u6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
F fc m m2 s a1 G c lo v); try eassumption; unfold POPULATE_STACK; lia|].
cbn beta. intros r s' ms' [_ H]. exact H.
+ destruct POST as [-> POST]. apply aimplT_ret. apply evt_done. exact POST.
-
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\
ms' = MS (mkR ra (wz (bv_unsigned sp + -64)) gp (wz A_TP) t0 t1 t2 (wz (ri_addr RE c)) (wz (rl_T X + 2768))
(wz A_INSTANCE) (wz (c * 4294967296)) (wz c) (wz (c_alloc_user (cls a c))) (wz req) a5' a6' a7
(wz (reg_beg (ae_L RE) c)) (wz (c_alloc_user (cls a c) + class_size c * req)) (wz (c_mapped_user (cls a c))) (wz (class_size c))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x4456c) fc None m1 (seg_rom asegs)).
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb].
eapply aimplT_mono; [apply (populate_C L RE X ra t0 t1 t2 (wz (rl_T X + 2768)) (wz (c * 4294967296)) (wz c) (wz req) a5' a6' a7
(wz (c_alloc_user (cls a c) + class_size c * req)) s6 t3 t4 t5 t6 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
F fc m m1 s a G c lo v); try eassumption; unfold POPULATE_STACK; lia|].
cbn beta. intros r s' ms' [_ H]. exact H.
Qed.
End S.
