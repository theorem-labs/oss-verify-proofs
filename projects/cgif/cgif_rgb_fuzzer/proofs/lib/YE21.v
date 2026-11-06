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
YB0z YE2g YF8z YF90 YE2q YE2r YE22 YE2t YE2s YE2x YE20 YF9g YE1y YE2b.
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
Definition A_exit : Z := 0x91800.
Definition TRA_TPX : Z := 0x5dd150.
Definition F_STDIN : Z := 0xa6930.
Definition X1_PC : Z := 0x7056c.
Definition X2_PC : Z := 0x88344.
Definition X3_PC : Z := 0x30794.
Definition XW1 (a : Z) : Prop := False.
Definition XW2 (a : Z) : Prop := (0xa6b00 <= a < 0xa6b08) \/ (0xa7a70 <= a < 0xa7a78) \/
(0x7fffc1d8 <= a < 0x7fffc1dc) \/ (0x7fffc1e0 <= a < 0x7fffc1e4) \/ (0x8000cd4a <= a < 0x8000cd5a).
Definition XW3 (a : Z) : Prop := a = 0xa6b50.
Definition XTRUE (W : world trasegs) (m : word -> option byte) : Prop := True.
Definition X3PRE (W : world trasegs) (m : word -> option byte) : Prop :=
val_mem trasegs (mrestrict (w_H W) m) 0xa2130 8 0x916e4 /\ val_mem trasegs (mrestrict (w_H W) m) 0xa2138 8 0.
Definition ex_consts : list (Z * N * Z) :=
[(0xa2e40, 8%N, 0xa1bf8); (0xa2e48, 8%N, 0xa1be8); (0xa1be8, 8%N, 0x88344); (0xa1bf0, 8%N, 0x30794);
(0xa2130, 8%N, 0x916e4); (0xa2138, 8%N, 0);
(0xa6838, 8%N, F_STDERR); (0xa6928, 8%N, F_STDOUT); (0xa6a18, 8%N, F_STDIN);
(0x5fd1a0, 1%N, 0); (0x5fd1a4, 4%N, 0); (0x5fd1a8, 4%N, 2); (0x5fd1b0, 8%N, 0x5fd1b8); (0x5fd1b8, 8%N, 0);
(0x5fd1c0, 8%N, 0x917ac); (0x5fd1c8, 8%N, 0x917ac); (0x5fd2c0, 8%N, 0x7056c); (0x5fd2c8, 8%N, 0x80f34); (0x5dc814, 1%N, 0);
(0x5fd3c0, 4%N, 0); (0x5fd3e3, 1%N, 0); (0x5fd840, 4%N, 0); (0x5fd848, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition ex_consts1 : list (Z * N * Z) :=
[(0xa2e40, 8%N, 0xa1bf8); (0xa2e48, 8%N, 0xa1be8); (0xa1be8, 8%N, 0x88344); (0xa1bf0, 8%N, 0x30794);
(0xa2130, 8%N, 0x916e4); (0xa2138, 8%N, 0);
(0xa6838, 8%N, F_STDERR); (0xa6928, 8%N, F_STDOUT); (0xa6a18, 8%N, F_STDIN);
(0x5fd1a0, 1%N, 0); (0x5fd1a4, 4%N, 0); (0x5fd1a8, 4%N, 1); (0x5fd1b0, 8%N, 0x5fd1b8); (0x5fd1b8, 8%N, 0);
(0x5fd1c0, 8%N, 0x917ac); (0x5fd2c0, 8%N, 0x7056c); (0x5dc814, 1%N, 0);
(0x5fd3c0, 4%N, 0); (0x5fd3e3, 1%N, 0); (0x5fd840, 4%N, 0); (0x5fd848, 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition cells_are (l : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (a, n, v) => val_mem trasegs m a (N.to_nat n) v end) l.
Definition ex_cell_range (tp a : Z) : Prop :=
vo_file a \/ vf_file a \/ (F_STDIN <= a < F_STDIN + FILE_SZ) \/
(A_canary <= a < A_canary + 8) \/ (0xa2e40 <= a < 0xa2e50) \/ (0xa1be8 <= a < 0xa1bf8) \/ (0xa2130 <= a < 0xa2140) \/
(0xa6838 <= a < 0xa6840) \/ (0xa6928 <= a < 0xa6930) \/ (0xa6a18 <= a < 0xa6a20) \/
(0x5fd1a0 <= a < 0x5fd2d0) \/ (0x5dc814 <= a < 0x5dc815) \/ (0x5fd3c0 <= a < 0x5fd3c4) \/ (0x5fd3e3 <= a < 0x5fd3e4) \/ (0x5fd840 <= a < 0x5fd850) \/
(tp - 168 <= a < tp - 164).
Section S.
Variable B : asyms.
Hypothesis TL : TraSyms B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis HB : TraSyms B.
Hypothesis X1 : xret_realizes trasegs B X1_PC XW1 XTRUE.
Hypothesis X2 : xret_realizes_noar trasegs B X2_PC XW2 XTRUE.
Hypothesis X3 : xret_realizes trasegs B X3_PC XW3 X3PRE.
Theorem tra_exit_pristine : forall ly S (W : world trasegs) regs mem md code tid cval sew,
ecall_pre trasegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRA_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trasegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trasegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trasegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trasegs (w_H W) (w_A W) md ->
srealizes trasegs (cfg_at trasegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_pristine (imgk := YF00.K_tra)) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine (imgk := YF00.K_tra)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_pristine (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_pristine (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Theorem tra_exit_pristine1 : forall ly S (W : world trasegs) regs mem md code tid cval sew,
ecall_pre trasegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRA_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem trasegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trasegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trasegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trasegs (w_H W) (w_A W) md ->
srealizes trasegs (cfg_at trasegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_pristine1 (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Theorem tra_exit_empty : forall ly S (W : world trasegs) regs mem md code tid cval sew,
ecall_pre trasegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRA_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trasegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trasegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trasegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trasegs (w_H W) (w_A W) md ->
srealizes trasegs (cfg_at trasegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof. first [ exact (YE08.tfx_exit_empty (imgk := YF00.K_tra)) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_empty (imgk := YF00.K_tra)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_empty (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_empty (imgk := YF00.K_tra)); eassumption ] ]. Qed.
Theorem tra_exit_flush : forall ly S (W : world trasegs) regs mem md code tid cval sew wp (pend : list byte) ch,
ecall_pre trasegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TRA_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem trasegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem trasegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem trasegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem trasegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> wp = STDOUT_BUFA + Z.of_nat (length pend) -> (0 < length pend)%nat -> wp <= STDOUT_BUFA + STDOUT_BSZ ->
(forall i, (i < length pend)%nat -> aview trasegs (w_H W) mem (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))) ->
fdchan (Z_to_bv 64 1) ch md ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI trasegs (w_H W) (w_A W) md ->
srealizes trasegs (cfg_at trasegs A_exit regs mem md) (t_emit (map (WriteEv ch) pend) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof. first [ exact (YE08.tfx_exit_flush (imgk := YF00.K_tra)) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL LAWS HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X1) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL LAWS HB X1 X2) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS HB X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL LAWS HB X1 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL LAWS X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL LAWS HB X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B TL X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL LAWS X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) B HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) TL HB X1 X2 X3) | exact ((YE08.tfx_exit_flush (imgk := YF00.K_tra)) LAWS HB X1 X2 X3) | solve [ eapply (YE08.tfx_exit_flush (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YE08.tfx_exit_flush (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End S.
End b.
