(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_su_errb.v (commit eb934de95d13, blob 1eeb1794d82c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 3 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); preset's YA02.SINV0 takes the segment list first, as in A/AD1d.v:61. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1g AD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d YI04 YI00 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Definition ERRB_OBJ : Z := 0xaa728.
Definition ERRB_OBJ_LEN : Z := 56.

Definition EXH_OFF : Z := 68.

Definition RINFO_ZERO : kentry := KZero (SA AD1g.eSp1 137439019008) (ELit 4096).

Definition su_errb_check (ch : acs) : bool :=
(kn_img ch ERRB_OBJ ERRB_OBJ_LEN && kn_mem RINFO_ZERO ch)%bool.
Lemma su_errb_check_all : forallb su_errb_check HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma errb_obj_rom_zero : forall k, (k < 56)%nat ->
seg_rom tfibsegs (Z_to_bv 64 (ERRB_OBJ + Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof.
intros k Hk.
do 56 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation m1 := (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL).
#[local] Notation u := (uE E).
Let CHK : su_errb_check ch = true := proj1 (forallb_forall _ _) su_errb_check_all ch (HS_tfib_In h ch Hch).
Let MRm1 := AD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.

Theorem errb_obj_zero_start : val_mem tfibsegs m1 ERRB_OBJ 56 0.
Proof.
pose proof CHK as H. unfold su_errb_check in H. apply andb_prop in H as [Kimg _].
intros k Hk.
unfold kn_img in Kimg. apply existsb_exists in Kimg as (K & HK & HKb).
destruct K as [| | |lo hi| | | | | |]; try discriminate HKb. apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
unfold ERRB_OBJ, ERRB_OBJ_LEN in *.
pose proof (Hnone (0xaa728 + Z.of_nat k) ltac:(lia)) as X.
pose proof (errb_obj_rom_zero k Hk) as Hs. unfold ERRB_OBJ in Hs.
assert (Hb : mbyte TSEGS MR (0xaa728 + Z.of_nat k) = Some (Z_to_bv 8 0)) by (unfold mbyte; rewrite X; exact Hs).
change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb).
f_equal. f_equal. unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Theorem exh_bytes_zero_start : forall c, 1 <= c <= 31 ->
val_mem tfibsegs m1 (ly_space (AD1g.ly0 ch E model) + kRegionInfoOff + 128 * c + EXH_OFF) 1 0.
Proof.
intros c Hc.
pose proof CHK as H. unfold su_errb_check in H. apply andb_prop in H as [_ Kzero].
pose proof (AD1g.uSp sp rdraw brk inp h ch E R FULL model Hch HC) as (S1 & _).
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (ho_zero_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ Kzero (128 * c + 68)) as Z0.
unfold elenZ, estart in Z0. cbn [a_base a_off edenot] in Z0. rewrite u64_lit in Z0 by lia.
try fold (u AD1g.eSp1) in Z0.
specialize (Z0 ltac:(lia)).
cbn [AD1g.ly0 ly_space]. rewrite S1. unfold kRegionInfoOff, EXH_OFF.
replace (u AD1g.eSp1 + 65536 + 2 ^ 37 + 128 * c + 68) with (u AD1g.eSp1 + 137439019008 + (128 * c + 68)) by lia.
change tfibsegs with TSEGS. unfold mbyte. rewrite (AD2i.MR_m1 sp rdraw inp ch E FULL model _ _ Z0).
all: f_equal; f_equal; unfold YO0f.le_byte; rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia); reflexivity.
Qed.
End e.
End c.
