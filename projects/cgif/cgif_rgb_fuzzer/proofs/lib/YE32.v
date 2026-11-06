(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YB1u YE3h YF9i YF9j YE3r YE3s YE33 YE3u YE3t YE3y YE31 YFa1 YE2z YE3c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YE08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_exit : Z := 0x9284c.
Definition TRB_TPX : Z := 0x5de210.
Definition F_STDIN : Z := 0xa7a20.
Definition X1_PC : Z := 0x70830.
Definition X2_PC : Z := 0x88d70.
Definition X3_PC : Z := 0x308e4.
Definition XW1 (a : Z) : Prop := False.
Definition XW2 (a : Z) : Prop := (0xa7bc0 <= a < 0xa7bc8) \/ (0xa8b30 <= a < 0xa8b38) \/
(0x7fffc1d8 <= a < 0x7fffc1dc) \/ (0x7fffc1e0 <= a < 0x7fffc1e4) \/ (0x8000cf68 <= a < 0x8000cf78).
Definition XW3 (a : Z) : Prop := a = 0xa7c10.
Definition XTRUE (W : world trbsegs) (m : word -> option byte) : Prop := True.
Definition X3PRE (W : world trbsegs) (m : word -> option byte) : Prop :=
val_mem trbsegs (mrestrict (w_H W) m) 0xa3220 8 0x92730 /\ val_mem trbsegs (mrestrict (w_H W) m) 0xa3228 8 0.
Definition ex_consts : list (Z * N * Z) :=
[(0xa3f30, 8%N, 0xa2ce8); (0xa3f38, 8%N, 0xa2cd8); (0xa2cd8, 8%N, 0x88d70); (0xa2ce0, 8%N, 0x308e4);
(0xa3220, 8%N, 0x92730); (0xa3228, 8%N, 0);
(0xa7928, 8%N, F_STDERR); (0xa7a18, 8%N, F_STDOUT); (0xa7b08, 8%N, F_STDIN);
(0x5fe260, 1%N, 0); (0x5fe264, 4%N, 0); (0x5fe268, 4%N, 2); (0x5fe270, 8%N, 0x5fe278); (0x5fe278, 8%N, 0);
(0x5fe280, 8%N, 0x927f8); (0x5fe288, 8%N, 0x927f8); (0x5fe380, 8%N, 0x70830); (0x5fe388, 8%N, 0x811f8); (0x5dd8d4, 1%N, 0);
(0x5fe480, 4%N, 0); (0x5fe4a3, 1%N, 0); (0x5fe900, 4%N, 0); (0x5fe908, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition ex_consts1 : list (Z * N * Z) :=
[(0xa3f30, 8%N, 0xa2ce8); (0xa3f38, 8%N, 0xa2cd8); (0xa2cd8, 8%N, 0x88d70); (0xa2ce0, 8%N, 0x308e4);
(0xa3220, 8%N, 0x92730); (0xa3228, 8%N, 0);
(0xa7928, 8%N, F_STDERR); (0xa7a18, 8%N, F_STDOUT); (0xa7b08, 8%N, F_STDIN);
(0x5fe260, 1%N, 0); (0x5fe264, 4%N, 0); (0x5fe268, 4%N, 1); (0x5fe270, 8%N, 0x5fe278); (0x5fe278, 8%N, 0);
(0x5fe280, 8%N, 0x927f8); (0x5fe380, 8%N, 0x70830); (0x5dd8d4, 1%N, 0);
(0x5fe480, 4%N, 0); (0x5fe4a3, 1%N, 0); (0x5fe900, 4%N, 0); (0x5fe908, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition cells_are (l : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (a, n, v) => val_mem trbsegs m a (N.to_nat n) v end) l.
Definition ex_cell_range (tp a : Z) : Prop :=
vo_file a \/ vf_file a \/ (F_STDIN <= a < F_STDIN + FILE_SZ) \/
(A_canary <= a < A_canary + 8) \/ (0xa3f30 <= a < 0xa3f40) \/ (0xa2cd8 <= a < 0xa2ce8) \/ (0xa3220 <= a < 0xa3230) \/
(0xa7928 <= a < 0xa7930) \/ (0xa7a18 <= a < 0xa7a20) \/ (0xa7b08 <= a < 0xa7b10) \/
(0x5fe260 <= a < 0x5fe390) \/ (0x5dd8d4 <= a < 0x5dd8d5) \/ (0x5fe480 <= a < 0x5fe484) \/ (0x5fe4a3 <= a < 0x5fe4a4) \/ (0x5fe900 <= a < 0x5fe910) \/
(tp - 168 <= a < tp - 164).
Section S.
Variable B : asyms.
Hypothesis TL : TrbSyms B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis HB : TrbSyms B.
Hypothesis X1 : xret_realizes trbsegs B X1_PC XW1 XTRUE.
Hypothesis X2 : xret_realizes_noar trbsegs B X2_PC XW2 XTRUE.
Hypothesis X3 : xret_realizes trbsegs B X3_PC XW3 X3PRE.
Theorem trb_exit_pristine : forall ly S (W : world trbsegs) regs mem md code tid cval sew,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trbsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trbsegs (w_H W) (w_A W) md ->
srealizes trbsegs (cfg_at trbsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_pristine (imgk := YF00.K_trb)) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_trb)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_pristine (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_pristine (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Theorem trb_exit_pristine1 : forall ly S (W : world trbsegs) regs mem md code tid cval sew,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRB_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem trbsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trbsegs (w_H W) (w_A W) md ->
srealizes trbsegs (cfg_at trbsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_pristine1 (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Theorem trb_exit_empty : forall ly S (W : world trbsegs) regs mem md code tid cval sew,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trbsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trbsegs (w_H W) (w_A W) md ->
srealizes trbsegs (cfg_at trbsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_empty (imgk := YF00.K_trb)) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_trb)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_empty (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_empty (imgk := YF00.K_trb)); eassumption ] ]. Qed.
Theorem trb_exit_flush : forall ly S (W : world trbsegs) regs mem md code tid cval sew wp (pend : list byte) ch,
ecall_pre trbsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRB_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trbsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trbsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trbsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trbsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> wp = STDOUT_BUFA + Z.of_nat (length pend) -> (0 < length pend)%nat -> wp <= STDOUT_BUFA + STDOUT_BSZ ->
(forall i, (i < length pend)%nat -> aview trbsegs (w_H W) mem (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))) ->
fdchan (Z_to_bv 64 1) ch md ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trbsegs (w_H W) (w_A W) md ->
srealizes trbsegs (cfg_at trbsegs A_exit regs mem md) (t_emit (map (WriteEv ch) pend) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof. first [ exact (YE08.tfx_exit_flush (imgk := YF00.K_trb)) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_trb)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_flush (imgk := YF00.K_trb)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_flush (imgk := YF00.K_trb)); eassumption ] ]. Qed.
End S.
End b.
