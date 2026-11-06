(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Ops StackInit InitLib OblsLib CertSound DrvShape DrvLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require StrReg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AsanDrun.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib CertS DrvShape DrvLib.
Open Scope Z_scope.
Unset Lia Cache.

Section PB.
Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).

Let MP := AsanDrun.MP inp.
Let PB := AsanDrun.PB inp sp rnd.
Let file := AsanDrun.file inp.
Let p1 := AsanDrun.p1 inp.

Lemma MP_fds : forall mo f, MP mo -> MP (with_fds f mo).
Proof. intros mo f H. exact H. Qed.
Lemma HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.
Proof. exact (AsanDrun.MP_stable inp). Qed.

Lemma MP_file : fs_lookup (in_fs inp) p1 <> None -> forall mo, MP mo -> fs_lookup (m_fs mo) p1 = Some file.
Proof.
  intros EX mo H. unfold MP, AsanDrun.MP in H. rewrite H. unfold file, AsanDrun.file, AsanDrun.fs0.
  fold p1. destruct (fs_lookup (in_fs inp) p1) as [f|]; [reflexivity| exfalso; apply EX; reflexivity].
Qed.

Lemma PB_file : forall b, PB b -> b 4%uint63 = file.
Proof. intros b H. unfold PB, AsanDrun.PB in H. rewrite H. reflexivity. Qed.
Lemma PB_size : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (Ops.fsize file).
Proof. intros b H. unfold PB, AsanDrun.PB in H. rewrite H. reflexivity. Qed.

Lemma PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).
Proof.
  intros E H i Hi. unfold PB, AsanDrun.PB in H.
  assert (E4 : eb E 4%uint63 = file) by (rewrite H; reflexivity).
  assert (E5 : eb E 5%uint63 = payload file) by (rewrite H; reflexivity).
  assert (E13 : eb E 13%uint63 = LE8 (Z.max 0 (fsize file - 6 - cfg_len file))) by (rewrite H; reflexivity).
  assert (E14 : eb E 14%uint63 = LE8 (6 + cfg_len file)) by (rewrite H; reflexivity).
  pose proof (Z.mod_pos_bound (cfgw file) 32768 ltac:(lia)) as CB. unfold fsize in *.
  assert (R13 : 0 <= Z.max 0 (Z.min (Z.of_nat (length file)) (2 ^ 62) - 6 - cfg_len file) < 2 ^ 64) by (unfold cfg_len; lia).
  assert (R14 : 0 <= 6 + cfg_len file < 2 ^ 64) by (unfold cfg_len; lia).
  unfold CtrM.B13, CtrM.B14 in *. change wzero with (wp 0%uint63) in *.
  rewrite (OL.den_param8_u E 13%uint63 _ E13 R13) in Hi. rewrite (OL.den_param8_u E 14%uint63 _ E14 R14).
  rewrite E4, E5. unfold payload. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63)) /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.
Proof.
  intros E H. unfold PB, AsanDrun.PB in H.
  assert (E12 : eb E 12%uint63 = SI.strarea (in_argv inp) (in_envp inp)) by (rewrite H; reflexivity).
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea (in_argv inp) (in_envp inp))))) by (rewrite H; reflexivity).
  pose proof (SI.BSB_top AImg.a_phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hfit) as T. rewrite SI.length_BSB in T.
  pose proof (SI.length_strarea (in_argv inp) (in_envp inp)) as L. pose proof (SI.SP_lo sp Hsp) as LO.
  rewrite E12. split; [| apply SI.strarea_len8].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). apply (OL.den_param8_u E 15%uint63 _ E15). unfold SI.raw_len, SI.SP in *. lia.
Qed.

Lemma PB_str : forall b, PB b -> forall j js, StrReg.legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Proof.
  intros b H j js LS. unfold PB, AsanDrun.PB in H.
  assert (NZ : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun x : byte => bv_unsigned x <> 0) s).
  { intros s N. apply Forall_forall. intros x Hx E0. apply N. replace (Z_to_bv 8 0) with x; [exact Hx|].
    apply bv_eq. rewrite E0. reflexivity. }
  destruct LS as [[-> ->]|[-> ->]].
  - exists (AsanDrun.a0 inp). rewrite H. split; [reflexivity|]. split; [| split; [reflexivity| exact (AsanDrun.a0_len inp Hva)]].
    apply NZ. destruct Hva as (_ & _ & _ & HZ & _). exact (proj1 (Forall_forall _ _) HZ _ (AsanDrun.a0_In inp Hva)).
  - exists (AsanDrun.p1 inp). rewrite H. split; [reflexivity|]. split; [| split; [reflexivity| exact (AsanDrun.p1_len inp Hva)]].
    apply NZ. exact (AsanDrun.p1_nz inp Hva).
Qed.
End PB.

Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Notation.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsM.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.StackInit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.InitLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.OblsLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.CertSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.DrvShape OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.DrvLib.
Import AsanDrun.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val St Ops CtrLib CertS DrvShape DrvLib.
Open Scope Z_scope.
Unset Lia Cache.

Section PB.
Variable inp : ProcInput.
Variables (sp : word) (rnd : EntryDraw).
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).

Let MP := AsanDrun.TwinB.MP inp.
Let PB := AsanDrun.TwinB.PB inp sp rnd.
Let file := AsanDrun.TwinB.file inp.
Let p1 := AsanDrun.TwinB.p1 inp.

Lemma MP_fds : forall mo f, MP mo -> MP (with_fds f mo).
Proof. intros mo f H. exact H. Qed.
Lemma HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.
Proof. exact (AsanDrun.TwinB.MP_stable inp). Qed.

Lemma MP_file : fs_lookup (in_fs inp) p1 <> None -> forall mo, MP mo -> fs_lookup (m_fs mo) p1 = Some file.
Proof.
  intros EX mo H. unfold MP, AsanDrun.TwinB.MP in H. rewrite H. unfold file, AsanDrun.TwinB.file, AsanDrun.TwinB.fs0.
  fold p1. destruct (fs_lookup (in_fs inp) p1) as [f|]; [reflexivity| exfalso; apply EX; reflexivity].
Qed.

Lemma PB_file : forall b, PB b -> b 4%uint63 = file.
Proof. intros b H. unfold PB, AsanDrun.TwinB.PB in H. rewrite H. reflexivity. Qed.
Lemma PB_size : forall b, PB b -> b 11%uint63 = Z_to_le_bytes 8 (Ops.fsize file).
Proof. intros b H. unfold PB, AsanDrun.TwinB.PB in H. rewrite H. reflexivity. Qed.

Lemma PB5 : forall E, PB (eb E) -> forall i, 0 <= i < bv_unsigned (den E CtrM.B13) ->
  nth (Z.to_nat (bv_unsigned (den E CtrM.B14) + i)) (eb E 4%uint63) (Z_to_bv 8 0) = nth (Z.to_nat i) (eb E 5%uint63) (Z_to_bv 8 0).
Proof.
  intros E H i Hi. unfold PB, AsanDrun.TwinB.PB in H.
  assert (E4 : eb E 4%uint63 = file) by (rewrite H; reflexivity).
  assert (E5 : eb E 5%uint63 = payload file) by (rewrite H; reflexivity).
  assert (E13 : eb E 13%uint63 = LE8 (Z.max 0 (fsize file - 6 - cfg_len file))) by (rewrite H; reflexivity).
  assert (E14 : eb E 14%uint63 = LE8 (6 + cfg_len file)) by (rewrite H; reflexivity).
  pose proof (Z.mod_pos_bound (cfgw file) 32768 ltac:(lia)) as CB. unfold fsize in *.
  assert (R13 : 0 <= Z.max 0 (Z.min (Z.of_nat (length file)) (2 ^ 62) - 6 - cfg_len file) < 2 ^ 64) by (unfold cfg_len; lia).
  assert (R14 : 0 <= 6 + cfg_len file < 2 ^ 64) by (unfold cfg_len; lia).
  unfold CtrM.B13, CtrM.B14 in *. change wzero with (wp 0%uint63) in *.
  rewrite (OL.den_param8_u E 13%uint63 _ E13 R13) in Hi. rewrite (OL.den_param8_u E 14%uint63 _ E14 R14).
  rewrite E4, E5. unfold payload. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma PB12 : forall E, PB (eb E) -> bv_unsigned (den E (CtrA.SZ 15%uint63)) = Z.of_nat (length (eb E 12%uint63)) /\ Z.of_nat (length (eb E 12%uint63)) mod 8 = 0.
Proof.
  intros E H. unfold PB, AsanDrun.TwinB.PB in H.
  assert (E12 : eb E 12%uint63 = SI.strarea (in_argv inp) (in_envp inp)) by (rewrite H; reflexivity).
  assert (E15 : eb E 15%uint63 = LE8 (Z.of_nat (length (SI.strarea (in_argv inp) (in_envp inp))))) by (rewrite H; reflexivity).
  pose proof (SI.BSB_top BImg.b_phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd Hfit) as T. rewrite SI.length_BSB in T.
  pose proof (SI.length_strarea (in_argv inp) (in_envp inp)) as L. pose proof (SI.SP_lo sp Hsp) as LO.
  rewrite E12. split; [| apply SI.strarea_len8].
  unfold CtrA.SZ. change wzero with (wp 0%uint63). apply (OL.den_param8_u E 15%uint63 _ E15). unfold SI.raw_len, SI.SP in *. lia.
Qed.

Lemma PB_str : forall b, PB b -> forall j js, StrReg.TwinB.legal_str j js ->
  exists s : list byte, b j = s ++ [Z_to_bv 8 0] /\ Forall (fun x : byte => bv_unsigned x <> 0) s
    /\ b js = Z_to_le_bytes 8 (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) <= 131071.
Proof.
  intros b H j js LS. unfold PB, AsanDrun.TwinB.PB in H.
  assert (NZ : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun x : byte => bv_unsigned x <> 0) s).
  { intros s N. apply Forall_forall. intros x Hx E0. apply N. replace (Z_to_bv 8 0) with x; [exact Hx|].
    apply bv_eq. rewrite E0. reflexivity. }
  destruct LS as [[-> ->]|[-> ->]].
  - exists (AsanDrun.TwinB.a0 inp). rewrite H. split; [reflexivity|]. split; [| split; [reflexivity| exact (AsanDrun.TwinB.a0_len inp Hva)]].
    apply NZ. destruct Hva as (_ & _ & _ & HZ & _). exact (proj1 (Forall_forall _ _) HZ _ (AsanDrun.TwinB.a0_In inp Hva)).
  - exists (AsanDrun.TwinB.p1 inp). rewrite H. split; [reflexivity|]. split; [| split; [reflexivity| exact (AsanDrun.TwinB.p1_len inp Hva)]].
    apply NZ. exact (AsanDrun.TwinB.p1_nz inp Hva).
Qed.
End PB.
End TwinB.
