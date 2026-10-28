(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat FmtFp.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_memset F_memcpy F_memchr F_strnlen Stdio_kit F_syscalls StdioFiles.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_pop_arg.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import Printf_model Printf_mlib.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import Printf_zfacts F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import F_printf_core_common.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import StoreFast.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".
Section PrintfCore.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^47)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.
Hypothesis HA : (A + zlength fmt <= 118784)%Z.
Hypothesis SEP_F : ((121784 <= Fp /\ Fp + 232 <= 324000) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((324008 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.
Local Notation W := (F_printf_core_common.W Fp B BS q lo AP).
Local Notation hi_cells := (F_printf_core_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (F_printf_core_common.lo_cells AP nla nlt).
Local Notation fmt_rng := (F_printf_core_common.fmt_rng fmt HF).
Local Notation implM_eq_ms := (F_printf_core_common.implM_eq_ms (St:=St)).
Local Notation sink_store := (F_printf_core_common.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (F_printf_core_common.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation S_FLAGS := (F_printf_core_common.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (F_printf_core_common.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (F_printf_core_common.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (F_printf_core_common.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (F_printf_core_common.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (F_printf_core_common.tregs Fp q gp tp A).
Notation sfx := (sfx fmt).
Notation SPv := (Z_to_bv 64 (q + -544)).
Ltac hush := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;
repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.
Lemma L_DIR : S_DIR.
Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX).
destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.
assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evt usegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x17b48) fc None m (seg_rom usegs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 else k2)%Z);
[exact FI' | exact LOW' | lia | | ]).
{ destruct PX as [(N46 & Hp & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
- right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp.
destruct PX as [(N46 & Hpq & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- rewrite Hxp. cbn [Z.b2z].
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d); [exact FI' | zl | rewrite <- Ec2; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1)%Z); [zl | rewrite Hrest, Es2b; reflexivity | replace (k2 + 1 - 1)%Z with k2 by lia; rewrite <- Ec2, Ht; reflexivity | lia | lia | lia]).
- rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK.
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1 + Z.of_nat n3 + 1)%Z); [zl | exact Erest | replace (k2 + 1 + Z.of_nat n3 + 1 - 1)%Z with (k2 + 1 + Z.of_nat n3)%Z by lia; symmetry; exact Et | lia | lia | lia]). }
assert (FL34 : forall (a3 a4 a5 : word), evt usegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x17ab8) fc None m (seg_rom usegs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.
assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }
rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
- zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
Qed.
End PrintfCore.
