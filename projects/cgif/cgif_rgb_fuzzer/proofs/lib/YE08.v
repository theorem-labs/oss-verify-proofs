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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8v YE1o YE1p YE07 YE09 YE1s YE1r YE1w YE06 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Notation tfxtbl_x := tfxmusl_tbl (only parsing).
Notation tfxtbl_x_ok := tfxmusl_tbl_ok (only parsing).
Definition A_exit {imgk : img} : Z := (0x91800 + D_104c).
Definition TFX_TPX {imgk : img} : Z := (0x5dd150 + D_10c0).
Definition F_STDIN {imgk : img} : Z := (0xa6930 + D_10f0).
Definition X1_PC {imgk : img} : Z := (0x7056c + D_2c4).  Definition X1_RA {imgk : img} : Z := (0x9169c + D_104c).  Definition OSP_X1 : Z := -64.
Definition X2_PC {imgk : img} : Z := (0x88344 + D_a2c). Definition X3_PC {imgk : img} : Z := (0x30794 + D_150).   Definition X23_RA {imgk : img} : Z := (0x917e4 + D_104c). Definition OSP_X23 : Z := -48.
Definition XW1 (a : Z) : Prop := False.
Definition XW2 {imgk : img} (a : Z) : Prop := ((0xa6b00 + D_10c0) <= a < (0xa6b08 + D_10c0)) \/ ((0xa7a70 + D_10c0) <= a < (0xa7a78 + D_10c0)) \/
(0x7fffc1d8 <= a < 0x7fffc1dc) \/ (0x7fffc1e0 <= a < 0x7fffc1e4) \/ ((0x8000cd4a + D_21e) <= a < (0x8000cd5a + D_21e)).
Definition XW3 {imgk : img} (a : Z) : Prop := a = (0xa6b50 + D_10c0).
Definition XTRUE {imgk : img} (W : world tfxsegs) (m : word -> option byte) : Prop := True.
Definition X3PRE {imgk : img} (W : world tfxsegs) (m : word -> option byte) : Prop :=
val_mem tfxsegs (mrestrict (w_H W) m) (0xa2130 + D_10f0) 8 (0x916e4 + D_104c) /\ val_mem tfxsegs (mrestrict (w_H W) m) (0xa2138 + D_10f0) 8 0.
Definition ex_consts {imgk : img} : list (Z * N * Z) :=
[((0xa2e40 + D_10f0), 8%N, (0xa1bf8 + D_10f0)); ((0xa2e48 + D_10f0), 8%N, (0xa1be8 + D_10f0)); ((0xa1be8 + D_10f0), 8%N, (0x88344 + D_a2c)); ((0xa1bf0 + D_10f0), 8%N, (0x30794 + D_150));
((0xa2130 + D_10f0), 8%N, (0x916e4 + D_104c)); ((0xa2138 + D_10f0), 8%N, 0);
((0xa6838 + D_10f0), 8%N, F_STDERR); ((0xa6928 + D_10f0), 8%N, F_STDOUT); ((0xa6a18 + D_10f0), 8%N, F_STDIN);
((0x5fd1a0 + D_10c0), 1%N, 0); ((0x5fd1a4 + D_10c0), 4%N, 0); ((0x5fd1a8 + D_10c0), 4%N, 2); ((0x5fd1b0 + D_10c0), 8%N, (0x5fd1b8 + D_10c0)); ((0x5fd1b8 + D_10c0), 8%N, 0);
((0x5fd1c0 + D_10c0), 8%N, (0x917ac + D_104c)); ((0x5fd1c8 + D_10c0), 8%N, (0x917ac + D_104c)); ((0x5fd2c0 + D_10c0), 8%N, (0x7056c + D_2c4)); ((0x5fd2c8 + D_10c0), 8%N, (0x80f34 + D_2c4)); ((0x5dc814 + D_10c0), 1%N, 0);
((0x5fd3c0 + D_10c0), 4%N, 0); ((0x5fd3e3 + D_10c0), 1%N, 0); ((0x5fd840 + D_10c0), 4%N, 0); ((0x5fd848 + D_10c0), 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition ex_consts1 {imgk : img} : list (Z * N * Z) :=
[((0xa2e40 + D_10f0), 8%N, (0xa1bf8 + D_10f0)); ((0xa2e48 + D_10f0), 8%N, (0xa1be8 + D_10f0)); ((0xa1be8 + D_10f0), 8%N, (0x88344 + D_a2c)); ((0xa1bf0 + D_10f0), 8%N, (0x30794 + D_150));
((0xa2130 + D_10f0), 8%N, (0x916e4 + D_104c)); ((0xa2138 + D_10f0), 8%N, 0);
((0xa6838 + D_10f0), 8%N, F_STDERR); ((0xa6928 + D_10f0), 8%N, F_STDOUT); ((0xa6a18 + D_10f0), 8%N, F_STDIN);
((0x5fd1a0 + D_10c0), 1%N, 0); ((0x5fd1a4 + D_10c0), 4%N, 0); ((0x5fd1a8 + D_10c0), 4%N, 1); ((0x5fd1b0 + D_10c0), 8%N, (0x5fd1b8 + D_10c0)); ((0x5fd1b8 + D_10c0), 8%N, 0);
((0x5fd1c0 + D_10c0), 8%N, (0x917ac + D_104c)); ((0x5fd2c0 + D_10c0), 8%N, (0x7056c + D_2c4)); ((0x5dc814 + D_10c0), 1%N, 0);
((0x5fd3c0 + D_10c0), 4%N, 0); ((0x5fd3e3 + D_10c0), 1%N, 0); ((0x5fd840 + D_10c0), 4%N, 0); ((0x5fd848 + D_10c0), 8%N, 0);
(F_STDIN + 8, 8%N, 0); (F_STDIN + 16, 8%N, 0); (F_STDIN + 40, 8%N, 0); (F_STDIN + 56, 8%N, 0); (F_STDIN + 140, 4%N, 0xffffffff);
(F_STDERR + 8, 8%N, 0); (F_STDERR + 16, 8%N, 0); (F_STDERR + 140, 4%N, 0xffffffff)].
Definition cells_are {imgk : img} (l : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (a, n, v) => val_mem tfxsegs m a (N.to_nat n) v end) l.
Definition ex_cell_range {imgk : img} (tp a : Z) : Prop :=
vo_file a \/ vf_file a \/ (F_STDIN <= a < F_STDIN + FILE_SZ) \/
(A_canary <= a < A_canary + 8) \/ ((0xa2e40 + D_10f0) <= a < (0xa2e50 + D_10f0)) \/ ((0xa1be8 + D_10f0) <= a < (0xa1bf8 + D_10f0)) \/ ((0xa2130 + D_10f0) <= a < (0xa2140 + D_10f0)) \/
((0xa6838 + D_10f0) <= a < (0xa6840 + D_10f0)) \/ ((0xa6928 + D_10f0) <= a < (0xa6930 + D_10f0)) \/ ((0xa6a18 + D_10f0) <= a < (0xa6a20 + D_10f0)) \/
((0x5fd1a0 + D_10c0) <= a < (0x5fd2d0 + D_10c0)) \/ ((0x5dc814 + D_10c0) <= a < (0x5dc815 + D_10c0)) \/ ((0x5fd3c0 + D_10c0) <= a < (0x5fd3c4 + D_10c0)) \/ ((0x5fd3e3 + D_10c0) <= a < (0x5fd3e4 + D_10c0)) \/ ((0x5fd840 + D_10c0) <= a < (0x5fd850 + D_10c0)) \/
(tp - 168 <= a < tp - 164).
Definition cellr (a : Z) (n : N) (v : sv) (w : bool) : YQ0b.region :=
YQ0b.mkRegion None a (a + Z.of_N n) a (if w then a + Z.of_N n else a) [YQ0b.mkChunk a (CVal n v)].
Definition ex_regions {imgk : img} (fo : list YQ0b.chunk) : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YQ0b.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fo;
YQ0b.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ)
[YQ0b.mkChunk (F_STDERR + 8) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDERR + 16) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDERR + 40) (CVal 8 (SOff 35 0)); YQ0b.mkChunk (F_STDERR + 56) (CVal 8 (SOff 35 0));
YQ0b.mkChunk (F_STDERR + 140) (CVal 4 (SLit 0xffffffff))];
YQ0b.mkRegion None F_STDIN (F_STDIN + FILE_SZ) F_STDIN F_STDIN
[YQ0b.mkChunk (F_STDIN + 8) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDIN + 16) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDIN + 40) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDIN + 56) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDIN + 140) (CVal 4 (SLit 0xffffffff))];
cellr A_GOT_canary 8 (SLit A_canary) false;
cellr A_canary 8 (SOff 33 0) false;
YQ0b.mkRegion None (0xa2e40 + D_10f0) (0xa2e50 + D_10f0) (0xa2e40 + D_10f0) (0xa2e40 + D_10f0) [YQ0b.mkChunk (0xa2e40 + D_10f0) (CVal 8 (SLit (0xa1bf8 + D_10f0))); YQ0b.mkChunk (0xa2e48 + D_10f0) (CVal 8 (SLit (0xa1be8 + D_10f0)))];
YQ0b.mkRegion None (0xa1be8 + D_10f0) (0xa1bf8 + D_10f0) (0xa1be8 + D_10f0) (0xa1be8 + D_10f0) [YQ0b.mkChunk (0xa1be8 + D_10f0) (CVal 8 (SLit (0x88344 + D_a2c))); YQ0b.mkChunk (0xa1bf0 + D_10f0) (CVal 8 (SLit (0x30794 + D_150)))];
YQ0b.mkRegion None (0xa2130 + D_10f0) (0xa2140 + D_10f0) (0xa2130 + D_10f0) (0xa2130 + D_10f0) [YQ0b.mkChunk (0xa2130 + D_10f0) (CVal 8 (SLit (0x916e4 + D_104c))); YQ0b.mkChunk (0xa2138 + D_10f0) (CVal 8 (SLit 0))];
cellr (0xa6838 + D_10f0) 8 (SLit F_STDERR) false;
cellr (0xa6928 + D_10f0) 8 (SLit F_STDOUT) false;
cellr (0xa6a18 + D_10f0) 8 (SLit F_STDIN) false;
YQ0b.mkRegion None (0x5fd1a0 + D_10c0) (0x5fd2d0 + D_10c0) (0x5fd1a0 + D_10c0) (0x5fd2d0 + D_10c0)
[YQ0b.mkChunk (0x5fd1a0 + D_10c0) (CVal 1 (SLit 0)); YQ0b.mkChunk (0x5fd1a4 + D_10c0) (CVal 4 (SLit 0)); YQ0b.mkChunk (0x5fd1a8 + D_10c0) (CVal 4 (SLit 2));
YQ0b.mkChunk (0x5fd1b0 + D_10c0) (CVal 8 (SLit (0x5fd1b8 + D_10c0))); YQ0b.mkChunk (0x5fd1b8 + D_10c0) (CVal 8 (SLit 0));
YQ0b.mkChunk (0x5fd1c0 + D_10c0) (CVal 8 (SLit (0x917ac + D_104c))); YQ0b.mkChunk (0x5fd1c8 + D_10c0) (CVal 8 (SLit (0x917ac + D_104c)));
YQ0b.mkChunk (0x5fd2c0 + D_10c0) (CVal 8 (SLit (0x7056c + D_2c4))); YQ0b.mkChunk (0x5fd2c8 + D_10c0) (CVal 8 (SLit (0x80f34 + D_2c4)))];
cellr (0x5fd3c0 + D_10c0) 4 (SLit 0) true;
cellr (0x5fd3e3 + D_10c0) 1 (SLit 0) false;
cellr (0x5dc814 + D_10c0) 1 (SLit 0) false;
YQ0b.mkRegion None (0x5fd840 + D_10c0) (0x5fd850 + D_10c0) (0x5fd840 + D_10c0) (0x5fd840 + D_10c0) [YQ0b.mkChunk (0x5fd840 + D_10c0) (CVal 4 (SLit 0)); YQ0b.mkChunk (0x5fd848 + D_10c0) (CVal 8 (SLit 0))];
YQ0b.mkRegion (Some 4%nat) (-168) (-164) (-168) (-168) [YQ0b.mkChunk (-168) (CVal 4 (SOff 32 0))] ].
Definition ex_regions1 {imgk : img} (fo : list YQ0b.chunk) : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- VF_STK) 0 (- VF_STK) 0 [];
YQ0b.mkRegion None F_STDOUT (F_STDOUT + FILE_SZ) F_STDOUT (F_STDOUT + FILE_SZ) fo;
YQ0b.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ)
[YQ0b.mkChunk (F_STDERR + 8) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDERR + 16) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDERR + 40) (CVal 8 (SOff 35 0)); YQ0b.mkChunk (F_STDERR + 56) (CVal 8 (SOff 35 0));
YQ0b.mkChunk (F_STDERR + 140) (CVal 4 (SLit 0xffffffff))];
YQ0b.mkRegion None F_STDIN (F_STDIN + FILE_SZ) F_STDIN F_STDIN
[YQ0b.mkChunk (F_STDIN + 8) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDIN + 16) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDIN + 40) (CVal 8 (SLit 0)); YQ0b.mkChunk (F_STDIN + 56) (CVal 8 (SLit 0));
YQ0b.mkChunk (F_STDIN + 140) (CVal 4 (SLit 0xffffffff))];
cellr A_GOT_canary 8 (SLit A_canary) false;
cellr A_canary 8 (SOff 33 0) false;
YQ0b.mkRegion None (0xa2e40 + D_10f0) (0xa2e50 + D_10f0) (0xa2e40 + D_10f0) (0xa2e40 + D_10f0) [YQ0b.mkChunk (0xa2e40 + D_10f0) (CVal 8 (SLit (0xa1bf8 + D_10f0))); YQ0b.mkChunk (0xa2e48 + D_10f0) (CVal 8 (SLit (0xa1be8 + D_10f0)))];
YQ0b.mkRegion None (0xa1be8 + D_10f0) (0xa1bf8 + D_10f0) (0xa1be8 + D_10f0) (0xa1be8 + D_10f0) [YQ0b.mkChunk (0xa1be8 + D_10f0) (CVal 8 (SLit (0x88344 + D_a2c))); YQ0b.mkChunk (0xa1bf0 + D_10f0) (CVal 8 (SLit (0x30794 + D_150)))];
YQ0b.mkRegion None (0xa2130 + D_10f0) (0xa2140 + D_10f0) (0xa2130 + D_10f0) (0xa2130 + D_10f0) [YQ0b.mkChunk (0xa2130 + D_10f0) (CVal 8 (SLit (0x916e4 + D_104c))); YQ0b.mkChunk (0xa2138 + D_10f0) (CVal 8 (SLit 0))];
cellr (0xa6838 + D_10f0) 8 (SLit F_STDERR) false;
cellr (0xa6928 + D_10f0) 8 (SLit F_STDOUT) false;
cellr (0xa6a18 + D_10f0) 8 (SLit F_STDIN) false;
YQ0b.mkRegion None (0x5fd1a0 + D_10c0) (0x5fd2d0 + D_10c0) (0x5fd1a0 + D_10c0) (0x5fd2d0 + D_10c0)
[YQ0b.mkChunk (0x5fd1a0 + D_10c0) (CVal 1 (SLit 0)); YQ0b.mkChunk (0x5fd1a4 + D_10c0) (CVal 4 (SLit 0)); YQ0b.mkChunk (0x5fd1a8 + D_10c0) (CVal 4 (SLit 1));
YQ0b.mkChunk (0x5fd1b0 + D_10c0) (CVal 8 (SLit (0x5fd1b8 + D_10c0))); YQ0b.mkChunk (0x5fd1b8 + D_10c0) (CVal 8 (SLit 0));
YQ0b.mkChunk (0x5fd1c0 + D_10c0) (CVal 8 (SLit (0x917ac + D_104c)));
YQ0b.mkChunk (0x5fd2c0 + D_10c0) (CVal 8 (SLit (0x7056c + D_2c4)))];
cellr (0x5fd3c0 + D_10c0) 4 (SLit 0) true;
cellr (0x5fd3e3 + D_10c0) 1 (SLit 0) false;
cellr (0x5dc814 + D_10c0) 1 (SLit 0) false;
YQ0b.mkRegion None (0x5fd840 + D_10c0) (0x5fd850 + D_10c0) (0x5fd840 + D_10c0) (0x5fd840 + D_10c0) [YQ0b.mkChunk (0x5fd840 + D_10c0) (CVal 4 (SLit 0)); YQ0b.mkChunk (0x5fd848 + D_10c0) (CVal 8 (SLit 0))];
YQ0b.mkRegion (Some 4%nat) (-168) (-164) (-168) (-168) [YQ0b.mkChunk (-168) (CVal 4 (SOff 32 0))] ].
Definition ex_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition ex_factsF {imgk : img} : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (34%nat, mkAF (STDOUT_BUFA + 1) (STDOUT_BUFA + STDOUT_BSZ) 0) ] [] [].
Definition ss_exP {imgk : img} : sstate := mkSS A_exit sr_atoms (ex_regions (fo_chunks stdout_fields0)) None ex_facts0.
Definition ss_exP1 {imgk : img} : sstate := mkSS A_exit sr_atoms (ex_regions1 (fo_chunks stdout_fields0)) None ex_facts0.
Definition ss_exE {imgk : img} : sstate := mkSS A_exit sr_atoms (ex_regions (YQ0b.mkChunk (F_STDOUT + 40) (CVal 8 (SLit STDOUT_BUFA)) :: fo_chunks stdout_fields1)) None ex_facts0.
Definition ss_exF {imgk : img} : sstate := mkSS A_exit sr_atoms (ex_regions (YQ0b.mkChunk (F_STDOUT + 40) (CVal 8 (SOff 34 0)) :: fo_chunks stdout_fields1)) None ex_factsF.
Definition exm {imgk : img} (a : Z) : Prop := vo_file a \/ vf_file a \/ ((0x5fd1a0 + D_10c0) <= a < (0x5fd2d0 + D_10c0)) \/ ((0x5fd3c0 + D_10c0) <= a < (0x5fd3c4 + D_10c0)).
Lemma exm_img_bytes_ok1 {imgk : img} : zallb (img_byte_ok tfxsegs) (0x5fd1a0 + D_10c0) (Z.to_nat 0x130) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma exm_img_bytes_ok2 {imgk : img} : zallb (img_byte_ok tfxsegs) (0x5fd3c0 + D_10c0) 4%nat = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma exm_img {imgk : img} : forall a, exm a -> img_byte_ok tfxsegs a = true.
Proof.
intros a [H|[H|[H|H]]].
- unfold vo_file in H. img_exact (zallb_sound _ _ _ a stdout_img_bytes_ok ltac:(img_try (unfold FILE_SZ in *; img_lia))).
- unfold vf_file in H. img_exact (zallb_sound _ _ _ a stderr_img_bytes_ok ltac:(img_try (unfold FILE_SZ in *; img_lia))).
- img_exact (zallb_sound _ _ _ a exm_img_bytes_ok1 ltac:(img_lia)).
- img_exact (zallb_sound _ _ _ a exm_img_bytes_ok2 ltac:(img_lia)).
Qed.
Lemma exm_dec {imgk : img} : forall a, exm a \/ ~ exm a.
Proof. intros a. unfold exm, vo_file, vf_file. img_lia. Qed.
Definition exw_ok {imgk : img} (t : option nat * Z * Z) : bool :=
band_winb t || win_eqb t (None, F_STDOUT, F_STDOUT + FILE_SZ) || win_eqb t (None, F_STDERR, F_STDERR + FILE_SZ)
|| win_eqb t (None, (0x5fd1a0 + D_10c0), (0x5fd2d0 + D_10c0)) || win_eqb t (None, (0x5fd3c0 + D_10c0), (0x5fd3c4 + D_10c0)) || (snd t <=? snd (fst t)).
Definition ex_windows_ok {imgk : img} (ss : sstate) : bool := forallb exw_ok (windows (ss_mem ss)).
Lemma ex_windows_sound {imgk : img} : forall E ss sp0 a,
ex_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ exm a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold ex_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). unfold exw_ok in Hb.
repeat (apply orb_prop in Hb as [Hb|Hb]).
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. (subst lo; cbv beta).
cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm, vo_file. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm, vf_file. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm. img_lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm. img_lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. img_lia.
Qed.
Section VX. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (sp0 : Z) (mem0 : word -> option byte) (md0 : Model).
Variable mut : Z -> Prop.
Hypothesis Hmut_img : forall a, mut a -> img_byte_ok tfxsegs a = true.
Hypothesis Hmut_dec : forall a, mut a \/ ~ mut a.
Hypothesis HFown : forall a, mut a -> ~ aowned B ly S a.
Variable xs : Z -> Prop.
Hypothesis Hstk : ly_stk_lo ly + VF_STK <= sp0.
Hypothesis Htop : sp0 <= ly_stk_hi ly.
Definition VX (mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly S W mem md /\ same_but_materialized md0 md /\
(forall a, vf_band sp0 a -> apresent (w_H W) mem a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> ~ xs a -> aview tfxsegs (w_H W) mem a = aview tfxsegs (w_H W) mem0 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ mut a -> ~ xs a -> apresent (w_H W) mem0 a -> apresent (w_H W) mem a).
Lemma VX_init : AR tfxsegs B ly S W mem0 md0 -> (forall a, vf_band sp0 a -> apresent (w_H W) mem0 a) -> VX mem0 md0.
Proof.
intros HAR Hp. split; [img_try (img_exact HAR)|]. split; [img_try (img_apply same_but_materialized_refl)|]. split; [img_try (img_exact Hp)|].
split; [img_try (intros; img_refl) | img_try (intros a _ _ _ Ha; img_exact Ha)].
Qed.
Lemma VX_run : forall mem md memB mat,
VX mem md ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> memB x = mem x) ->
(forall x : word, ~ vf_band sp0 (bv_unsigned x) -> ~ mut (bv_unsigned x) -> mrestrict (w_H W) memB x = mrestrict (w_H W) mem x) ->
(forall a, vf_band sp0 a -> apresent (w_H W) memB a) ->
VX memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros mem md memB mat (HAR & Hsbm & Hpb & Hfr & Hpm) HF HFr HpbB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (HVF : VF_STK = 9104) by img_refl.
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ mut a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a).
{ intros a Hr H1 H2. img_apply aview_eq_of. img_apply HFr; rewrite unsigned_lit_small by img_lia; assumption. }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
split; [|img_try (split; [|split; [img_exact HpbB | split]])].
- img_apply (al_frame _ _ LAWS ly S W mem md memB _ HAR).
+ intros a Hr Hown. img_apply AVB; [img_try (img_exact Hr) | |].
* intros Hb. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold vf_band in Hb; img_lia)) Hown).
* intros Hf. img_exact (HFown a Hf Hown).
+ assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) memB a <> None).
{ intros a Hr Hv.
assert (CASE : vf_band sp0 a \/ mut a \/ (~ vf_band sp0 a /\ ~ mut a)).
{ destruct (Hmut_dec a) as [Hm|Hm]; [img_try (right; left; img_exact Hm)|]. assert (D : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)). tauto. }
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* img_apply aview_some_of_apresent. img_apply HpbB. img_exact Hin.
* unfold aview, mbyte. destruct (mrestrict (w_H W) memB (Z_to_bv 64 a)) as [b|]; [img_try (cbn; discriminate)|].
pose proof (Hmut_img a Hin) as Hb.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfxsegs (Z_to_bv 64 a)); [img_try (cbn; discriminate) | img_try (discriminate Hb)].
* rewrite AVB; assumption. }
intros a Hv. rewrite (aview_mod _ memB a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
+ img_apply MF. + img_apply MF. + img_apply MF.
+ intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.     destruct (Hmut_dec a) as [Hmt|Hmt].
* exfalso. pose proof (Hmut_img a Hmt) as Hb. unfold img_byte_ok, img_byte in Hb. rewrite (seg_rom_none_band a Ha) in Hb. discriminate Hb.
* assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin|Hout]; [img_try (exfalso; destruct (Hpb a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh)|].
rewrite HF; [img_refl | |]; rewrite unsigned_lit_small by (img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)); assumption.
- eapply same_but_materialized_trans; [img_try (img_exact Hsbm) | img_try (img_apply with_vm_backing_same)].
- intros a Hr H1 H2 H3. rewrite AVB by assumption. img_apply Hfr; assumption.
- intros a Hr Hf Hx Hp.
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin | Hout]; [img_try (img_apply HpbB; img_exact Hin)|].
destruct (Hpm a Hr Hf Hx Hp) as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite HF; [img_try (img_exact Hb)| |]; rewrite unsigned_lit_small by img_lia; assumption.
Qed.
Lemma VX_splice : forall mem md memB mdB (Sx : Z -> Prop),
VX mem md ->
AR tfxsegs B ly S W memB mdB -> same_but_materialized md mdB ->
(forall a, Sx a -> vf_band sp0 a \/ mut a \/ xs a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Sx a -> aview tfxsegs (w_H W) memB a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> (vf_band sp0 a \/ ~ Sx a) -> apresent (w_H W) mem a -> apresent (w_H W) memB a) ->
VX memB mdB.
Proof.
intros mem md memB mdB Sx (HAR & Hsbm & Hpb & Hfr & Hpm) HARB HsbmB HSx HfrB HpmB.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HVF : VF_STK = 9104) by img_refl.
split; [img_try (img_exact HARB)|]. split; [img_try (eapply same_but_materialized_trans; [img_exact Hsbm | img_exact HsbmB])|].
split; [img_try (intros a Ha; img_apply HpmB; [unfold vf_band in Ha; img_lia | left; img_exact Ha | img_apply Hpb; img_exact Ha])|]. split.
- intros a Hr H1 H2 H3. rewrite HfrB; [img_try (img_apply Hfr; assumption) | img_try (img_exact Hr) | img_try (intros Hs; destruct (HSx a Hs) as [Hb|[Hm|Hx]]; [img_exact (H1 Hb) | img_exact (H2 Hm) | img_exact (H3 Hx)])].
- intros a Hr Hf Hx Hp. img_apply HpmB; [img_try (img_exact Hr) | | img_try (img_apply Hpm; assumption)].
assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (img_try (unfold vf_band; img_lia)).
destruct CASE as [Hin | Hout]; [img_try (left; img_exact Hin) | img_try (right)]. intros Hs. destruct (HSx a Hs) as [Hb|[Hm|Hx']]; tauto.
Qed.
End VX.
Definition ex_rest {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => ((tl (ex_regions []))))).
Lemma ex_rest_ok {imgk : img} : forall E (rest : smem) tp,
skeleton rest = skeleton ex_rest -> bv_unsigned (ew E 4) = tp -> 168 <= tp -> tp <= 2 ^ 43 ->
forall r, In r rest -> exists bz, base_val E (YQ0b.r_base r) = bz /\ 0 <= bz + YQ0b.r_lo r /\ bz + YQ0b.r_hi r <= 2 ^ 43.
Proof.
intros E rest tp Hsk H4 Htp1 Htp2 r Hr. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi].
repeat (destruct Hin as [Hq|Hin]; [img_try (symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val]; rewrite ?H4; eexists; split; [img_refl|];
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; img_lia) |]).
destruct Hin.
Qed.
Lemma wseg_writable {imgk : img} : forall (m : word -> option byte) lo n a,
wseg_ok tfxsegs (Z_to_bv 64 lo) (Z.to_nat n) = true -> 0 <= lo -> lo + n <= 2 ^ 47 -> 0 <= n -> lo <= a < lo + n -> writable_at tfxsegs m a.
Proof.
intros m lo n a Hz Hlo Hhi Hn Ha. unfold writable_at.
img_apply (store_ok_all tfxsegs m (Z.to_nat n) (Z_to_bv 64 lo));
[img_try (rewrite unsigned_lit_small by img_lia; rewrite Z2Nat.id by img_lia; img_lia)
| img_try (img_apply store_ok_wseg; img_exact Hz)
| img_try (rewrite !unsigned_lit_small by img_lia; rewrite Z2Nat.id by img_lia; img_lia)].
Qed.
Lemma wz_stdout {imgk : img} : wseg_ok tfxsegs (Z_to_bv 64 F_STDOUT) (Z.to_nat FILE_SZ) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma wz_stderr {imgk : img} : wseg_ok tfxsegs (Z_to_bv 64 F_STDERR) (Z.to_nat FILE_SZ) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma wz_atexit {imgk : img} : wseg_ok tfxsegs (Z_to_bv 64 (0x5fd1a0 + D_10c0)) (Z.to_nat 0x130) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma wz_exitlock {imgk : img} : wseg_ok tfxsegs (Z_to_bv 64 (0x5fd3c0 + D_10c0)) (Z.to_nat 4) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma ex_rest_w {imgk : img} : forall E (rest : smem), skeleton rest = skeleton ex_rest ->
forall r a (m : word -> option byte), In r rest ->
base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> writable_at tfxsegs m a.
Proof.
intros E rest Hsk r a m Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Ha.
repeat (destruct Hin as [Hq|Hin]; [img_try (symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val] in Ha;
first [ img_apply (wseg_writable m F_STDOUT FILE_SZ a wz_stdout); unfold F_STDOUT, FILE_SZ in *; img_lia
| img_apply (wseg_writable m F_STDERR FILE_SZ a wz_stderr); unfold F_STDERR, FILE_SZ in *; img_lia
| img_apply (wseg_writable m (0x5fd1a0 + D_10c0) 0x130 a wz_atexit); img_lia
| img_apply (wseg_writable m (0x5fd3c0 + D_10c0) 4 a wz_exitlock); img_lia
| exfalso; unfold F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *; img_lia ]) |]).
destruct Hin.
Qed.
Lemma ex_rest_range {imgk : img} : forall E (rest : smem) tp,
skeleton rest = skeleton ex_rest -> bv_unsigned (ew E 4) = tp ->
forall r a, In r rest -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
(is_canary_region r = true /\ A_GOT_canary <= a < A_GOT_canary + 8) \/ ex_cell_range tp a.
Proof.
intros E rest tp Hsk H4 r a Hr Ha. pose proof (In_skel rest r Hr) as Hin. rewrite Hsk in Hin.
unfold ex_rest, skeleton in Hin. cbn in Hin. destruct r as [b lo hi wlo whi cs]. unfold skel in Hin. cbn in Hin.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Ha. unfold ex_cell_range, vo_file, vf_file.
repeat (destruct Hin as [Hq|Hin]; [img_try (symmetry in Hq; injection Hq; intros; (subst; cbv beta); cbn [base_val] in Ha; rewrite ?H4 in Ha;
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary in *;
first [ left; split; [(try img_inst; img_case; vm_compute); img_refl | img_lia] | right; img_lia ]) |]).
destruct Hin.
Qed.
Lemma ex_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_runN tfxsegs tfxtbl_x FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tfxtbl_x tfxtbl_x_ok Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Lemma srz_sym_exit {imgk : img} : forall (W : world tfxsegs) E ss ms model (c : word),
AI tfxsegs (w_H W) (w_A W) model ->
st_ok_ecall tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
sr_get (ss_regs ss) 17 = SLit 94 -> sv_denot E (sr_get (ss_regs ss) 10) = c -> bv_unsigned c < 256 ->
srealizes tfxsegs (mkCfg ms model) (t_exit c (m_fs model)).
Proof.
intros W E ss ms model c HAI HS Hrv H17 H10 Hc.
destruct (st_ok_ecall_shape_r tfxsegs (w_H W) E ss ms HS Hrv) as (regs & mem & -> & Hregs & Hmem & HG).
img_apply (srz_exit_small_lazy tfxsegs regs _ mem (seg_rom tfxsegs) model c (AI_halted _ _ _ _ HAI)).
- rewrite (Hregs 17%bv), H17. right. img_refl.
- rewrite (Hregs 10%bv). img_exact H10.
- img_exact Hc.
Qed.
Lemma m_fs_wvb : forall l mat md, m_fs (with_vm_backing l mat md) = m_fs md.
Proof. intros l mat md. destruct md; img_refl. Qed.
Lemma rdn_of_aview {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte),
(forall i, (i < length bs)%nat -> aview tfxsegs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs 0%bv))) ->
rdn tfxsegs (mrestrict H m) (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros H m a bs Hb. img_apply (proj2 (rdn_mbytes tfxsegs _ (length bs) a bs)). split; [img_refl|].
intros i Hi. destruct (aview_mbyte H m _ _ (Hb i Hi)) as (b & Hmb & Hbv). rewrite Hmb.
symmetry. rewrite (nth_error_nth' bs 0%bv Hi). f_equal. img_apply bv_eq. symmetry. img_exact Hbv.
Qed.
Lemma beq0_sext32_false : forall E n v, bv_unsigned (ew E n) = v -> 0 < v < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SLit 0)) (sv_denot E (SExt true 32 (SOff n 0))) = false.
Proof.
intros E n v Hv Hr. rewrite branch_eq_U, U_SLit, U_SExt, U_off by (img_try (rewrite Hv; unfold M64; img_lia)).
rewrite Hv, Z.add_0_r. img_change (zcanon 0) with 0.
img_change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v) by img_lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. img_change (2 ^ Z.of_N 32) with (2 ^ 32).
replace ((v + 2 ^ 32 ÷ 2) mod 2 ^ 32 - 2 ^ 32 ÷ 2) with v.
2:{ img_change (2 ^ 32 ÷ 2) with (2 ^ 31). rewrite Z.mod_small; img_lia. }
rewrite zcanon_id by (img_try (unfold M64; img_lia)). img_apply Z.eqb_neq. img_lia.
Qed.
Local Ltac WSEG := first
[ img_apply (wseg_writable _ (682048 + D_10f0) 232); [img_try (img_exact wz_stdout) | img_lia | img_lia | img_lia | img_lia]
| img_apply (wseg_writable _ (681808 + D_10f0) 232); [img_try (img_exact wz_stderr) | img_lia | img_lia | img_lia | img_lia]
| img_apply (wseg_writable _ (0x5fd1a0 + D_10c0) 0x130); [img_try (img_exact wz_atexit) | img_lia | img_lia | img_lia | img_lia]
| img_apply (wseg_writable _ (0x5fd3c0 + D_10c0) 4); [img_try (img_exact wz_exitlock) | img_lia | img_lia | img_lia | img_lia] ].
Local Ltac CELL := (eapply (chunk_ok_val tfxsegs _ _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)]).
Definition xP_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL ss_exP)))).
Definition xP_st1c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond xP_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0)))))).
Definition xP_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP_st1c)))).
Definition xP_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 36 xP_st2 X1_RA OSP_X1 0 []))).
Definition xP_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP_af2)))).
Definition xP_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 52 xP_st3 X23_RA OSP_X23 0 []))).
Definition xP_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP_af3)))).
Definition xP_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 68 xP_st4 X23_RA OSP_X23 0 []))).
Definition xP_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP_af4)))).
Definition xP_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP_st2)))).
Definition xP_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP_st2)))).
Definition xP_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP_st3)))).
Definition xP_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP_st3)))).
Definition xP_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP_st4)))).
Definition xP_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP_st4)))).
Lemma xP_run1 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL ss_exP = (xP_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP_run2 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP_st1c = (xP_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP_run3 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP_af2 = (xP_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP_run4 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP_af3 = (xP_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP_run5 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP_af4 = (xP_st5, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition xP1_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL ss_exP1)))).
Definition xP1_st1c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond xP1_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0)))))).
Definition xP1_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP1_st1c)))).
Definition xP1_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 36 xP1_st2 X1_RA OSP_X1 0 []))).
Definition xP1_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP1_af2)))).
Definition xP1_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 52 xP1_st3 X23_RA OSP_X23 0 []))).
Definition xP1_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP1_af3)))).
Definition xP1_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 68 xP1_st4 X23_RA OSP_X23 0 []))).
Definition xP1_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xP1_af4)))).
Definition xP1_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP1_st2)))).
Definition xP1_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP1_st2)))).
Definition xP1_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP1_st3)))).
Definition xP1_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP1_st3)))).
Definition xP1_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xP1_st4)))).
Definition xP1_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xP1_st4)))).
Lemma xP1_run1 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL ss_exP1 = (xP1_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP1_run2 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP1_st1c = (xP1_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP1_run3 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP1_af2 = (xP1_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP1_run4 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP1_af3 = (xP1_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xP1_run5 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xP1_af4 = (xP1_st5, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition xE_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL ss_exE)))).
Definition xE_st1c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond xE_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0)))))).
Definition xE_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xE_st1c)))).
Definition xE_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 36 xE_st2 X1_RA OSP_X1 0 []))).
Definition xE_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xE_af2)))).
Definition xE_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 52 xE_st3 X23_RA OSP_X23 0 []))).
Definition xE_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xE_af3)))).
Definition xE_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 68 xE_st4 X23_RA OSP_X23 0 []))).
Definition xE_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xE_af4)))).
Definition xE_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xE_st2)))).
Definition xE_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xE_st2)))).
Definition xE_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xE_st3)))).
Definition xE_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xE_st3)))).
Definition xE_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xE_st4)))).
Definition xE_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xE_st4)))).
Lemma xE_run1 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL ss_exE = (xE_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xE_run2 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xE_st1c = (xE_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xE_run3 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xE_af2 = (xE_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xE_run4 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xE_af3 = (xE_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xE_run5 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xE_af4 = (xE_st5, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition xF_st1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL ss_exF)))).
Definition xF_st1c {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (YQ09.add_cond xF_st1 (mkAC BC_NE (SLit 0) (SExt true 32 (SOff 32 0)))))).
Definition xF_st2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xF_st1c)))).
Definition xF_af2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 36 xF_st2 X1_RA OSP_X1 0 []))).
Definition xF_st3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xF_af2)))).
Definition xF_af3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 52 xF_st3 X23_RA OSP_X23 0 []))).
Definition xF_st4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xF_af3)))).
Definition xF_af4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (vf_after_icpt 68 xF_st4 X23_RA OSP_X23 0 []))).
Definition xF_st5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xF_af4)))).
Definition xF_r02 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xF_st2)))).
Definition xF_rest2 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xF_st2)))).
Definition xF_r03 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xF_st3)))).
Definition xF_rest3 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xF_st3)))).
Definition xF_r04 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => (hd img_ro_region (ss_mem xF_st4)))).
Definition xF_rest4 {imgk : img} : smem := ltac:(img_eval_last (fun imgk : img => (tl (ss_mem xF_st4)))).
Lemma xF_run1 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL ss_exF = (xF_st1, RS_stopped (SR_branch BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xF_run2 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xF_st1c = (xF_st2, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xF_run3 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xF_af2 = (xF_st3, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xF_run4 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xF_af3 = (xF_st4, RS_stopped SR_fetch). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma xF_run5 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xF_af4 = (xF_st5, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition xF_af5 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after xF_st5 0 (-144) 84))).
Definition xF_st6 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxtbl_x FUEL xF_af5)))).
Lemma xF_run6 {imgk : img} : sym_runN tfxsegs tfxtbl_x FUEL xF_af5 = (xF_st6, RS_ecall). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Local Ltac GEO := unfold STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary, OSP_X1, OSP_X23, XW1, XW2, XW3, TFX_TPX in *; img_lia.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis HB : TfxSyms B.
Hypothesis X1 : xret_realizes tfxsegs B X1_PC XW1 XTRUE.
Hypothesis X2 : xret_realizes_noar tfxsegs B X2_PC XW2 XTRUE.
Hypothesis X3 : xret_realizes tfxsegs B X3_PC XW3 X3PRE.
Lemma ex_entryP : forall (W : world tfxsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exP
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HF.
rewrite restrict_mkst_fx. unfold ss_exP.
assert (HVF : VF_STK = 9104) by img_refl.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFX_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E4 : bv_unsigned (ew E 4) = TFX_TPX) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; img_apply unsigned_lit_small; unfold TFX_TPX; img_lia)). unfold TFX_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (E34 : ew E 34 = Z_to_bv 64 (6281312 + D_10c0)) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 2))).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 3))).
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
unfold fo_chunks, stdout_fields0. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ sew); [img_try (cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)] ].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia) |].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hgot)].
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [img_try (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E4. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ (6148432 + D_10c0) (-168) 4 _ tid); [img_try (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
img_exact Htid.
- img_apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; img_lia.
Qed.
Lemma ex_entryP1 : forall (W : world tfxsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFX_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exP1
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HF.
rewrite restrict_mkst_fx. unfold ss_exP1.
assert (HVF : VF_STK = 9104) by img_refl.
unfold cells_are, ex_consts1 in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold stdout_pristine, ofile_is, stdout_fields0 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFX_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E4 : bv_unsigned (ew E 4) = TFX_TPX) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; img_apply unsigned_lit_small; unfold TFX_TPX; img_lia)). unfold TFX_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (E34 : ew E 34 = Z_to_bv 64 (6281312 + D_10c0)) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 2))).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 3))).
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- unfold ex_regions1. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
unfold fo_chunks, stdout_fields0. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ sew); [img_try (cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)] ].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia) |].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hgot)].
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [img_try (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E4. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ (6148432 + D_10c0) (-168) 4 _ tid); [img_try (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
img_exact Htid.
- img_apply pairwise_disjoint_of_extents. unfold ex_regions1, cellr, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; img_lia.
Qed.
Lemma ex_entryE : forall (W : world tfxsegs) regs mem tid cval sew,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) ss_exE
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem tid cval sew Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr [HF Hwp].
rewrite restrict_mkst_fx. unfold ss_exE.
assert (HVF : VF_STK = 9104) by img_refl.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFX_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E4 : bv_unsigned (ew E 4) = TFX_TPX) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; img_apply unsigned_lit_small; unfold TFX_TPX; img_lia)). unfold TFX_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (E34 : ew E 34 = Z_to_bv 64 (6281312 + D_10c0)) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 2))).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 3))).
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 (6281312 + D_10c0); Z_to_bv 64 sew]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
unfold fo_chunks, stdout_fields1. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ (6281312 + D_10c0)); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hwp)]. }
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ sew); [img_try (cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)] ].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia) |].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hgot)].
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [img_try (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E4. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ (6148432 + D_10c0) (-168) 4 _ tid); [img_try (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
img_exact Htid.
- img_apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [ex_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; img_lia.
Qed.
Lemma ex_entryF : forall (W : world tfxsegs) regs mem tid cval sew wp,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - VF_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 4 = w64 (as_tp B) -> as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA + 1 <= wp <= STDOUT_BUFA + STDOUT_BSZ ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) ss_exF
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_exit) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem tid cval sew wp Hsp1 Hsp2 Hal Hpres H4 HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr [HF Hwp] Hwpr.
rewrite restrict_mkst_fx. unfold ss_exF.
assert (HVF : VF_STK = 9104) by img_refl.
unfold cells_are, ex_consts in HC.
repeat match type of HC with Forall _ (_ :: _) =>
let h := fresh "HCc" in pose proof (Forall_inv HC) as h; cbn beta iota in h; apply Forall_inv_tail in HC end.
unfold ofile_is, stdout_fields1 in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
unfold F_STDOUT, F_STDERR, F_STDIN, STDOUT_BUFA, STDOUT_BSZ, A_GOT_canary, A_canary in *. rewrite HTP in Htid. unfold TFX_TPX in Htid.
set (E := Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E4 : bv_unsigned (ew E 4) = TFX_TPX) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), H4, HTP; img_apply unsigned_lit_small; unfold TFX_TPX; img_lia)). unfold TFX_TPX in E4.
assert (E32 : ew E 32 = Z_to_bv 64 tid) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (E33 : ew E 33 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 1))).
assert (E34 : ew E 34 = Z_to_bv 64 wp) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 2))).
assert (E35 : ew E 35 = Z_to_bv 64 sew) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 3))).
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- unfold ex_regions. unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- VF_STK)); [img_try (img_exact E2) | img_lia | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. img_lia.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
unfold fo_chunks, stdout_fields1. unfold F_STDOUT, STDOUT_BUFA, STDOUT_BSZ. cbn [map Z.add].
img_apply Forall_cons.
{ eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ wp); [| img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hwp)].
cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |].
repeat img_apply Forall_cons; try img_apply Forall_nil;
first [ CELL | eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ sew); [img_try (cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; assumption)] ].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia) |].
repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hgot)].
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [img_try (cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; WSEG) |]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|]. repeat img_apply Forall_cons; try img_apply Forall_nil; CELL.
+   unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E4. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ (6148432 + D_10c0) (-168) 4 _ tid); [img_try (cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) | img_try (img_zside) | img_try (img_zside) |].
img_exact Htid.
- img_apply pairwise_disjoint_of_extents. unfold ex_regions, cellr, img_ro_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2, E4.
unfold F_STDOUT, F_STDERR, F_STDIN, FILE_SZ, A_GOT_canary, A_canary.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [ex_factsF f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E34, (unsigned_lit_small wp) by img_lia.
img_change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r. unfold STDOUT_BUFA, STDOUT_BSZ in *. repeat split; img_lia.
Qed.
Theorem tfx_exit_pristine : forall ly S (W : world tfxsegs) regs mem md code tid cval sew,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfxsegs (w_H W) (w_A W) md ->
srealizes tfxsegs (cfg_at tfxsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl. assert (HFE : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl. assert (HFI : F_STDIN = (682288 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (667152 + D_10f0)) by img_refl. assert (HCA : A_canary = (6279568 + D_10c0)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. img_apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [img_try (left; img_exact H) | img_try (right; left; img_exact H) | img_lia | img_lia]. }
unfold cfg_at. img_change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryP W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (img_try (rewrite G4_0; img_apply unsigned_lit_small; rewrite HTP; unfold TFX_TPX; img_lia)).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (img_try (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); img_exact Ha0)).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; img_lia)).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; unfold wp; GEO)).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 ss_exP xP_st1 _ _ _ HS0 xP_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exP sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exP sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xP_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfxsegs E0 xP_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(img_try (img_apply (beq0_sext32_false E0 32 tid A32_0); img_lia))) as HS1c.
img_change (YQ09.add_cond xP_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xP_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 xP_st1c xP_st2 _ _ _ HS1c xP_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (ex_windows_sound E0 xP_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (ex_windows_sound E0 xP_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xP_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xP_st2 ms2 _ ly S sp0 xP_r02 xP_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold X1_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E0 xP_rest2 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_0 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E0 xP_rest2 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW1; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO))
(ex_rest_w E0 xP_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(img_try (img_exact I))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 36 xP_st2 X1_RA OSP_X1 0 []) with xP_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- img_exact VX2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X1 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm2'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact U4_0)).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A10_0)).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A34_0)).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E1 xP_af2 xP_st3 _ _ _ HS2' xP_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (ex_windows_sound E1 xP_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (ex_windows_sound E1 xP_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E1 xP_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xP_st3) _ _ _ Hmem3); (try img_inst; img_case; vm_compute); img_refl). }
clear Hmem3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xP_st3 ms3 _ ly S sp0 xP_r03 xP_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E1 xP_rest3 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_1 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E1 xP_rest3 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW3; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO))
(ex_rest_w E1 xP_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(img_try (img_exact X3P))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 52 xP_st3 X23_RA OSP_X23 0 []) with xP_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- img_exact VX3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X23 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm3'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact U4_1)).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A10_1)).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A34_1)).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E2 xP_af3 xP_st4 _ _ _ HS3' xP_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (ex_windows_sound E2 xP_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (ex_windows_sound E2 xP_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E2 xP_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xP_st4 ms4 _ ly S sp0 xP_r04 xP_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E2 xP_rest4 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_2 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E2 xP_rest4 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW2; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO))
(ex_rest_w E2 xP_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(img_try (img_exact I))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
img_change (vf_after_icpt 68 xP_st4 X23_RA OSP_X23 0 []) with xP_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact U4_2)).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A10_2)).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A34_2)).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E3 xP_af4 xP_st5 _ _ _ HS4' xP_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
img_apply (srz_sym_exit W E3 xP_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| img_try (rewrite unsigned_lit_small by img_lia; img_lia)].
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by img_lia. img_refl.
Qed.
Theorem tfx_exit_pristine1 : forall ly S (W : world tfxsegs) regs mem md code tid cval sew,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFX_TPX ->
cells_are ex_consts1 (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfxsegs (w_H W) (w_A W) md ->
srealizes tfxsegs (cfg_at tfxsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl. assert (HFE : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl. assert (HFI : F_STDIN = (682288 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (667152 + D_10f0)) by img_refl. assert (HCA : A_canary = (6279568 + D_10c0)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. img_apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [img_try (left; img_exact H) | img_try (right; left; img_exact H) | img_lia | img_lia]. }
unfold cfg_at. img_change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryP1 W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (img_try (rewrite G4_0; img_apply unsigned_lit_small; rewrite HTP; unfold TFX_TPX; img_lia)).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (img_try (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); img_exact Ha0)).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; img_lia)).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; unfold wp; GEO)).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 ss_exP1 xP1_st1 _ _ _ HS0 xP1_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exP1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exP1 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xP1_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfxsegs E0 xP1_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(img_try (img_apply (beq0_sext32_false E0 32 tid A32_0); img_lia))) as HS1c.
img_change (YQ09.add_cond xP1_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xP1_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 xP1_st1c xP1_st2 _ _ _ HS1c xP1_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (ex_windows_sound E0 xP1_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (ex_windows_sound E0 xP1_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xP1_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xP1_st2 ms2 _ ly S sp0 xP1_r02 xP1_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold X1_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E0 xP1_rest2 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_0 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E0 xP1_rest2 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW1; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO))
(ex_rest_w E0 xP1_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(img_try (img_exact I))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 36 xP1_st2 X1_RA OSP_X1 0 []) with xP1_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- img_exact VX2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X1 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm2'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact U4_0)).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A10_0)).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A34_0)).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E1 xP1_af2 xP1_st3 _ _ _ HS2' xP1_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (ex_windows_sound E1 xP1_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (ex_windows_sound E1 xP1_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E1 xP1_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xP1_st3) _ _ _ Hmem3); (try img_inst; img_case; vm_compute); img_refl). }
clear Hmem3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xP1_st3 ms3 _ ly S sp0 xP1_r03 xP1_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E1 xP1_rest3 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_1 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E1 xP1_rest3 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW3; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO))
(ex_rest_w E1 xP1_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(img_try (img_exact X3P))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 52 xP1_st3 X23_RA OSP_X23 0 []) with xP1_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- img_exact VX3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X23 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm3'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact U4_1)).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A10_1)).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A34_1)).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E2 xP1_af3 xP1_st4 _ _ _ HS3' xP1_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (ex_windows_sound E2 xP1_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (ex_windows_sound E2 xP1_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E2 xP1_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xP1_st4 ms4 _ ly S sp0 xP1_r04 xP1_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E2 xP1_rest4 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_2 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E2 xP1_rest4 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW2; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO))
(ex_rest_w E2 xP1_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(img_try (img_exact I))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
img_change (vf_after_icpt 68 xP1_st4 X23_RA OSP_X23 0 []) with xP1_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact U4_2)).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A10_2)).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A34_2)).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E3 xP1_af4 xP1_st5 _ _ _ HS4' xP1_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
img_apply (srz_sym_exit W E3 xP1_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| img_try (rewrite unsigned_lit_small by img_lia; img_lia)].
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by img_lia. img_refl.
Qed.
Theorem tfx_exit_empty : forall ly S (W : world tfxsegs) regs mem md code tid cval sew,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem) ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfxsegs (w_H W) (w_A W) md ->
srealizes tfxsegs (cfg_at tfxsegs A_exit regs mem md) (t_exit (Z_to_bv 64 code) (m_fs md)).
Proof.
intros ly S W regs mem md code tid cval sew HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl. assert (HFE : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl. assert (HFI : F_STDIN = (682288 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (667152 + D_10f0)) by img_refl. assert (HCA : A_canary = (6279568 + D_10c0)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. img_apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [img_try (left; img_exact H) | img_try (right; left; img_exact H) | img_lia | img_lia]. }
unfold cfg_at. img_change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryE W regs mem tid cval sew Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 STDOUT_BUFA; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (img_try (rewrite G4_0; img_apply unsigned_lit_small; rewrite HTP; unfold TFX_TPX; img_lia)).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (img_try (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); img_exact Ha0)).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; img_lia)).
pose (wp := STDOUT_BUFA). assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; unfold wp; GEO)).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 ss_exE xE_st1 _ _ _ HS0 xE_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exE sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exE sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xE_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfxsegs E0 xE_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(img_try (img_apply (beq0_sext32_false E0 32 tid A32_0); img_lia))) as HS1c.
img_change (YQ09.add_cond xE_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xE_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 xE_st1c xE_st2 _ _ _ HS1c xE_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (ex_windows_sound E0 xE_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (ex_windows_sound E0 xE_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xE_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
clear VX1 HF2 HFr2.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xE_st2 ms2 _ ly S sp0 xE_r02 xE_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold X1_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E0 xE_rest2 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_0 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E0 xE_rest2 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW1; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO))
(ex_rest_w E0 xE_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(img_try (img_exact I))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 36 xE_st2 X1_RA OSP_X1 0 []) with xE_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- img_exact VX2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X1 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm2'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact U4_0)).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A10_0)).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A34_0)).
clear HE1 HS2 VX2.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E1 xE_af2 xE_st3 _ _ _ HS2' xE_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (ex_windows_sound E1 xE_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (ex_windows_sound E1 xE_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E1 xE_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xE_st3) _ _ _ Hmem3); (try img_inst; img_case; vm_compute); img_refl). }
clear Hmem3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xE_st3 ms3 _ ly S sp0 xE_r03 xE_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E1 xE_rest3 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_1 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E1 xE_rest3 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW3; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO))
(ex_rest_w E1 xE_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(img_try (img_exact X3P))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 52 xE_st3 X23_RA OSP_X23 0 []) with xE_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- img_exact VX3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X23 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm3'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact U4_1)).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A10_1)).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A34_1)).
clear HE2 HS3 VX3.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E2 xE_af3 xE_st4 _ _ _ HS3' xE_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (ex_windows_sound E2 xE_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (ex_windows_sound E2 xE_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E2 xE_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
clear VX3' HF4 HFr4.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xE_st4 ms4 _ ly S sp0 xE_r04 xE_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E2 xE_rest4 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_2 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E2 xE_rest4 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW2; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO))
(ex_rest_w E2 xE_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(img_try (img_exact I))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
img_change (vf_after_icpt 68 xE_st4 X23_RA OSP_X23 0 []) with xE_af4 in HS4'.
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact U4_2)).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A10_2)).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A34_2)).
clear HE3 HS4 VX4.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E3 xE_af4 xE_st5 _ _ _ HS4' xE_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
clear HF5 HFr5.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat5 md).
img_apply (srz_sym_exit W E3 xE_st5 ms5 _ (Z_to_bv 64 code) HAI5 HS5 eq_refl eq_refl); [| img_try (rewrite unsigned_lit_small by img_lia; img_lia)].
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_3, unsigned_lit_small by img_lia. img_refl.
Qed.
Theorem tfx_exit_flush : forall ly S (W : world tfxsegs) regs mem md code tid cval sew wp (pend : list byte) ch,
ecall_pre tfxsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 code -> 0 <= code < 256 ->
as_tp B = TFX_TPX ->
cells_are ex_consts (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (as_tp B - 168) 4 tid -> 0 < tid < 2 ^ 31 ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 40) 8 sew -> val_mem tfxsegs (mrestrict (w_H W) mem) (F_STDERR + 56) 8 sew -> 0 <= sew < 2 ^ 64 ->
stdout_mid wp (mrestrict (w_H W) mem) -> wp = STDOUT_BUFA + Z.of_nat (length pend) -> (0 < length pend)%nat -> wp <= STDOUT_BUFA + STDOUT_BSZ ->
(forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) mem (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))) ->
fdchan (Z_to_bv 64 1) ch md ->
(forall a, ex_cell_range (as_tp B) a -> ~ aowned B ly S a) ->
(forall a, STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
AI tfxsegs (w_H W) (w_A W) md ->
srealizes tfxsegs (cfg_at tfxsegs A_exit regs mem md) (t_emit (map (WriteEv ch) pend) (t_exit (Z_to_bv 64 code) (m_fs md))).
Proof.
intros ly S W regs mem md code tid cval sew wp pend ch HPRE Hsp44 Hstk Hpres Ha0 Hcode HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO Hwp Hpend Hwphi HPEND Hch HXown HBown HAI0.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by img_refl. assert (HVF : VF_STK = 9104) by img_refl.
assert (HFF : F_STDOUT = (682048 + D_10f0)) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl. assert (HFE : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HBF : STDOUT_BUFA = (6281312 + D_10c0)) by img_refl. assert (HBS : STDOUT_BSZ = 1024) by img_refl. assert (HFI : F_STDIN = (682288 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (667152 + D_10f0)) by img_refl. assert (HCA : A_canary = (6279568 + D_10c0)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (sp0 := spZ regs) in *.
assert (Hsp47 : sp0 <= 2 ^ 47) by img_lia.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm a -> ~ aowned B ly S a).
{ intros a Ha. img_apply HXown. unfold exm in Ha. unfold ex_cell_range. destruct Ha as [H|[H|[H|H]]]; [img_try (left; img_exact H) | img_try (right; left; img_exact H) | img_lia | img_lia]. }
unfold cfg_at. img_change (w64 A_exit) with (Z_to_bv 64 A_exit).
pose proof (ex_entryF W regs mem tid cval sew wp Hsp44 Hsp47 Hal16 ltac:(img_try (intros a Ha; img_apply Hpres; img_exact Ha)) Htp HTP HC Htid Htidr Hgot Hcan Hcv Hew1 Hew2 Hewr HFO ltac:(img_lia)) as HS0.
set (EL := [Z_to_bv 64 tid; Z_to_bv 64 cval; Z_to_bv 64 wp; Z_to_bv 64 sew]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (img_try (intros i r Hi; rewrite HE0; img_exact (ew_Ereg_nat regs _ i r Hi))).
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (img_try (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); img_refl)).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (img_try (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); img_exact Hgp)).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (img_try (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); img_exact Htp)).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B) by (img_try (rewrite G4_0; img_apply unsigned_lit_small; rewrite HTP; unfold TFX_TPX; img_lia)).
assert (A10_0 : ew E0 10 = Z_to_bv 64 code) by (img_try (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); img_exact Ha0)).
assert (A32_0 : bv_unsigned (ew E0 32) = tid) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 0) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; img_lia)).
assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (img_try (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; img_apply unsigned_lit_small; GEO)).
clear HE0 EE.
pose proof (VX_init B ly S W sp0 mem md exm XS HAR Hpres) as VX0.
pose proof HPEND as PEND0.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 ss_exF xF_st1 _ _ _ HS0 xF_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VX1 : VX B ly S W sp0 mem md exm XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF1. intros Hin. destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr1. intros Hin. destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xF_st1 ms1 sp0 HS1 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
assert (PEND1 : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms1) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND0 i Hi). img_apply aview_eq_of. img_apply HFr1. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E0 ss_exF sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO)]. }
clear VX0 HF1 HFr1 PEND0.
pose proof (st_ok_add_cond_neg tfxsegs E0 xF_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
ltac:(img_try (img_apply (beq0_sext32_false E0 32 tid A32_0); img_lia))) as HS1c.
img_change (YQ09.add_cond xF_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with xF_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E0 xF_st1c xF_st2 _ _ _ HS1c xF_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VX2 : VX B ly S W sp0 mem md exm XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF2. intros Hin. destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr2. intros Hin. destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E0 xF_st2 ms2 sp0 HS2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 ltac:(img_lia)). }
assert (PEND2 : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms2) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND1 i Hi). img_apply aview_eq_of. img_apply HFr2. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E0 xF_st1c sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp0 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO)]. }
clear VX1 HF2 HFr2 PEND1.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 xF_st2 ms2 _ ly S sp0 xF_r02 xF_rest2 36 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold OSP_X1; img_lia)) ltac:(img_try (unfold X1_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E0 xF_rest2 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_0 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E0 xF_rest2 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_0 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW1; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO))
(ex_rest_w E0 xF_rest2 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(img_try (img_exact I))) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
img_change (vf_after_icpt 36 xF_st2 X1_RA OSP_X1 0 []) with xF_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
- img_exact VX2.
- img_exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X1 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr2'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm2'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
assert (PEND2' : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms2') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND2 i Hi). img_apply Hfr2'; [img_try (GEO) | img_try (unfold OSP_X1; GEO) | img_try (img_apply HBown; GEO) | img_try (unfold XW1; GEO)]. }
remember (havoc E0 36 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 36)%nat -> ew E1 j = ew E0 j) by (img_try (intros j Hj; rewrite HE1; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact Usp0)).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G3_0)).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact G4_0)).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact U4_0)).
assert (A10_1 : ew E1 10 = Z_to_bv 64 code) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A10_0)).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (img_try (rewrite OLD1 by ((img_case; cbv); img_lia); img_exact A34_0)).
clear HE1 HS2 VX2 PEND2.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E1 xF_af2 xF_st3 _ _ _ HS2' xF_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VX3 : VX B ly S W sp0 mem md exm XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF3. intros Hin. destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr3. intros Hin. destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E1 xF_st3 ms3 sp0 HS3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 ltac:(img_lia)). }
assert (PEND3 : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms3) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND2' i Hi). img_apply aview_eq_of. img_apply HFr3. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E1 xF_af2 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp1 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO)]. }
clear VX2' HF3 HFr3 PEND2'.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _). cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem xF_st3) _ _ _ Hmem3); (try img_inst; img_case; vm_compute); img_refl). }
clear Hmem3.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 xF_st3 ms3 _ ly S sp0 xF_r03 xF_rest3 52 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E1 xF_rest3 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_1 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E1 xF_rest3 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_1 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW3; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO))
(ex_rest_w E1 xF_rest3 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(img_try (img_exact X3P))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
img_change (vf_after_icpt 52 xF_st3 X23_RA OSP_X23 0 []) with xF_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
- img_exact VX3.
- img_exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). img_apply with_vm_backing_same.
- intros a [Ha|[Ha|Ha]]; [img_try (left; unfold vf_band, OSP_X23 in *; img_lia) | img_try (right; right; unfold XS; tauto) | img_try (right; right; unfold XS; tauto)].
- intros a Hr Hna. img_apply Hfr3'; [img_try (img_exact Hr) | img_try (intros H'; img_apply Hna; left; img_exact H') | img_try (intros H'; img_apply Hna; right; left; img_exact H') | img_try (intros H'; img_apply Hna; right; right; img_exact H')].
- intros a Hr Hba. img_apply Hpm3'; [img_try (img_exact Hr)|]. destruct Hba as [Hb|Hns]; [img_try (intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO) | img_try (intros Hx; img_apply Hns; right; right; img_exact Hx)]. }
assert (PEND3' : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms3') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND3 i Hi). img_apply Hfr3'; [img_try (GEO) | img_try (unfold OSP_X23; GEO) | img_try (img_apply HBown; GEO) | img_try (unfold XW3; GEO)]. }
remember (havoc E1 52 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 52)%nat -> ew E2 j = ew E1 j) by (img_try (intros j Hj; rewrite HE2; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact Usp1)).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G3_1)).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact G4_1)).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact U4_1)).
assert (A10_2 : ew E2 10 = Z_to_bv 64 code) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A10_1)).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (img_try (rewrite OLD2 by ((img_case; cbv); img_lia); img_exact A34_1)).
clear HE2 HS3 VX3 PEND3.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E2 xF_af3 xF_st4 _ _ _ HS3' xF_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VX4 : VX B ly S W sp0 mem md exm XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm exm_img exm_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
rewrite ?wvb_wvb in VR. img_apply VR.
- intros x Hx1 Hx2. img_apply HF4. intros Hin. destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- intros x Hx1 Hx2. img_apply HFr4. intros Hin. destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (img_exact (Hx1 Hw)) | img_try (img_exact (Hx2 Hw))].
- img_apply (vf_band_present W E2 xF_st4 ms4 sp0 HS4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 ltac:(img_lia)). }
assert (PEND4 : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms4) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND3' i Hi). img_apply aview_eq_of. img_apply HFr4. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E2 xF_af3 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp2 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO)]. }
clear VX3' HF4 HFr4 PEND3'.
eapply (SRr_srealizes tfxsegs W _ _ _
(vf_icpt_xcall_noar B X2_PC XW2 XTRUE X2 W E2 xF_st4 ms4 _ ly S sp0 xF_r04 xF_rest4 68 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))
ltac:(img_refl) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold OSP_X23; img_lia)) ltac:(img_try (unfold X23_RA; img_lia)) ltac:(img_refl)
(ex_rest_ok E2 xF_rest4 (as_tp B) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) U4_2 ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)) ltac:(img_try (rewrite HTP; unfold TFX_TPX; img_lia)))
ltac:(img_try (intros r a Hr Ha; destruct (ex_rest_range E2 xF_rest4 (as_tp B) ltac:((try img_inst; img_case; vm_compute); img_refl) U4_2 r a Hr Ha) as [[HcanR Hcr]|Hcr];
[ split; [img_try (left; img_exact HcanR) | img_try (unfold XW2; unfold A_GOT_canary in Hcr; GEO)]
| split; [img_try (right; img_apply HXown; img_exact Hcr) | img_try (unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO)] ]))
ltac:(img_try (intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO))
(ex_rest_w E2 xF_rest4 ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(img_try (img_exact I))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4'). cbn [cfg_model] in HAI4'.
rewrite wvb_wvb in HAI4' |- *.
img_change (vf_after_icpt 68 xF_st4 X23_RA OSP_X23 0 []) with xF_af4 in HS4'.
assert (PEND4' : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms4') (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND4 i Hi). img_apply Hfr4'; [img_try (GEO) | img_try (unfold OSP_X23; GEO) | img_try (img_apply HBown; GEO) | img_try (unfold XW2; GEO)]. }
remember (havoc E2 68 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 68)%nat -> ew E3 j = ew E2 j) by (img_try (intros j Hj; rewrite HE3; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact Usp2)).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G3_2)).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact G4_2)).
assert (U4_3 : bv_unsigned (ew E3 4) = as_tp B) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact U4_2)).
assert (A10_3 : ew E3 10 = Z_to_bv 64 code) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A10_2)).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (img_try (rewrite OLD3 by ((img_case; cbv); img_lia); img_exact A34_2)).
clear HE3 HS4 VX4 PEND4.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E3 xF_af4 xF_st5 _ _ _ HS4' xF_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (PEND5 : forall i, (i < length pend)%nat -> aview tfxsegs (w_H W) (ms_mem ms5) (STDOUT_BUFA + Z.of_nat i) = Some (bv_unsigned (nth i pend 0%bv))).
{ intros i Hi. rewrite <- (PEND4' i Hi). img_apply aview_eq_of. img_apply HFr5. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (ex_windows_sound E3 xF_af4 sp0 _ ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl)) Usp3 Hin) as [Hw|Hw]; [img_try (unfold vf_band in Hw; GEO) | img_try (unfold exm, vo_file, vf_file, F_STDOUT, F_STDERR, FILE_SZ in Hw; GEO)]. }
clear HF5 HFr5 PEND4'.
pose proof HS5 as HSc5. destruct HSc5 as (_ & _ & _ & _ & _ & _ & Hregs5 & Hmem5 & HG5). cbn [restrict ms_mem] in Hmem5.
pose proof (lit_buf_sound tfxsegs E3 (mrestrict (w_H W) (ms_mem ms5)) (ss_mem xF_st5) (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem5
ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))) as Hfdrd. cbn [sv_denot] in Hfdrd.
replace (map (WriteEv ch) pend) with (map (WriteEv ch) (pend ++ [])) by (img_try (rewrite app_nil_r; img_refl)).
eapply (srz_sym_stdio_writev2 W E3 xF_st5 ms5 _ (Z_to_bv 64 1) ch 0 2 (-144) F_STDOUT _ (SLit STDOUT_BUFA) (SOff 34 (- STDOUT_BUFA)) (SLit 0) (SLit 0)
pend [] (map (Z_to_bv 8) [1; 0; 0; 0]) 84 _ HAI5 HS5 eq_refl eq_refl eq_refl).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val, U_off, U_SLit by (img_try (rewrite A34_3; unfold M64; GEO)). rewrite A34_3. rewrite (zcanon_id _) by (img_try (unfold M64; GEO)).
rewrite (proj2 (Z.eqb_neq _ _)) by GEO. img_refl.
- match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite iovcnt_val', U_off, U_SLit by (img_try (rewrite A34_3; unfold M64; GEO)). rewrite A34_3. rewrite (zcanon_id _) by (img_try (unfold M64; GEO)).
rewrite (proj2 (Z.eqb_neq _ _)) by GEO. img_refl.
- img_refl.
- img_refl.
- img_refl.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
rewrite !U_off, U_SLit by (img_try (rewrite ?A34_3; unfold M64; GEO)). img_change (zcanon 0) with 0. img_lia.
- match goal with |- U _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-   rewrite word_to_nat_U, U_off by (img_try (rewrite A34_3; unfold M64; GEO)). cbn [sv_denot]. rewrite A34_3.
replace (Z.to_nat (wp + - STDOUT_BUFA)) with (length pend) by img_lia. img_exact (rdn_of_aview (w_H W) (ms_mem ms5) STDOUT_BUFA pend PEND5).
- img_refl.
- rewrite U_off, U_SLit by (img_try (rewrite A34_3; unfold M64; GEO)). rewrite A34_3. img_change (zcanon 0) with 0. GEO.
- rewrite U_off, U_SLit by (img_try (rewrite A34_3; unfold M64; GEO)). rewrite A34_3. rewrite (zcanon_id _) by (img_try (unfold M64; GEO)). GEO.
- rewrite U_off, U_SLit, Usp3 by (img_try (rewrite A34_3; unfold M64; GEO)). rewrite A34_3. rewrite (zcanon_id _) by (img_try (unfold M64; GEO)). GEO.
- rewrite !U_SLit. img_change (zcanon 0) with 0. img_lia.
- rewrite !U_SLit, Usp3. img_change (zcanon 0) with 0. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDOUT. img_lia.
- unfold F_STDOUT. img_lia.
- rewrite Usp3. unfold F_STDOUT. img_lia.
- rewrite Usp3. img_lia.
- rewrite Usp3. img_lia.
- img_case; vm_compute. all: img_refl.
- intros ms5' ws5 mat5' HS5' HF5' HFr5' HAI5'. rewrite ?wvb_wvb in HAI5' |- *.
img_change (wl_after xF_st5 0 (-144) 84) with xF_af5 in HS5'.
remember (havoc E3 84 ws5) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 84)%nat -> ew E4 j = ew E3 j) by (img_try (intros j Hj; rewrite HE4; img_apply ew_havoc_old; img_exact Hj)).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact Usp3)).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G3_3)).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact G4_3)).
assert (U4_4 : bv_unsigned (ew E4 4) = as_tp B) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact U4_3)).
assert (A10_4 : ew E4 10 = Z_to_bv 64 code) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact A10_3)).
assert (A34_4 : bv_unsigned (ew E4 34) = wp) by (img_try (rewrite OLD4 by ((img_case; cbv); img_lia); img_exact A34_3)).
clear HE4 HS5 Hfdrd Hregs5 Hmem5 HG5 HF5' HFr5' PEND5.
eapply (SRr_srealizes tfxsegs W _ _ _ (ex_phase W E4 xF_af5 xF_st6 _ _ _ HS5' xF_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
rewrite <- (m_fs_wvb (m_vm_lazy md) mat6 md).
img_apply (srz_sym_exit W E4 xF_st6 ms6 _ (Z_to_bv 64 code) HAI6 HS6 eq_refl eq_refl); [| img_try (rewrite unsigned_lit_small by img_lia; img_lia)].
match goal with |- sv_denot _ ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
cbn [sv_denot]. rewrite Z.add_0_r, A10_4, unsigned_lit_small by img_lia. img_refl.
Qed.
End S.
End d.
