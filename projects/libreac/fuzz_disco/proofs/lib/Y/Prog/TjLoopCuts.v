(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 163 of its 193 lines of code are new or changed and 515 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Definition ss_tjM : sstate :=
(mkSS 24008
[SLit 0; SOff 760 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 761 0; SOff 762 0; SOff 763 0; SOff 2 0; SOff 60 0; SOff 764 0; SOff 765 0; SOff 766 0; SOff 767 0; SOff 768 0; SOff 769 0; SOff 770 0; SOff 771 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 772 0; SOff 32 0; SOff 733 0; SOff 773 0; SOff 774 0; SOff 775 0; SOff 776 0; SOff 777 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjR : sstate :=
(mkSS 24132
[SLit 0; SOff 780 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 781 0; SOff 782 0; SOff 783 0; SOff 2 0; SOff 60 0; SOff 784 0; SOff 785 0; SOff 786 0; SOff 787 0; SOff 788 0; SOff 789 0; SOff 790 0; SOff 791 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 792 0; SOff 32 0; SOff 793 0; SOff 794 0; SOff 795 0; SOff 796 0; SOff 797 0; SOff 798 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjU : sstate :=
(mkSS 24344
[SLit 0; SOff 800 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 801 0; SOff 802 0; SOff 803 0; SOff 2 0; SOff 60 0; SOff 804 0; SOff 805 0; SOff 806 0; SOff 807 0; SOff 808 0; SOff 809 0; SOff 810 0; SOff 811 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 812 0; SOff 32 0; SOff 813 0; SOff 814 0; SOff 815 0; SOff 816 0; SOff 817 0; SOff 818 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjK : sstate :=
(mkSS 24460
[SLit 0; SOff 820 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 821 0; SOff 822 0; SOff 823 0; SOff 2 0; SOff 60 0; SOff 824 0; SOff 825 0; SOff 826 0; SOff 827 0; SOff 828 0; SOff 829 0; SOff 830 0; SOff 831 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 740 13; SOff 32 0; SOff 833 0; SOff 832 0; SOff 835 0; SOff 836 0; SOff 837 0; SOff 838 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 24 (CVal 8 (SOff 740 14)); YP09.mkChunk 32 (CVal 8 (SOff 834 0)); YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition ss_tjT : sstate :=
(mkSS 24608
[SLit 0; SOff 840 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 841 0; SOff 842 0; SOff 843 0; SOff 2 0; SOff 60 0; SOff 844 0; SOff 845 0; SOff 846 0; SOff 847 0; SOff 848 0; SOff 849 0; SOff 850 0; SOff 851 0; SOff 516 0; SOff 721 0; SOff 13 0; SOff 12 0; SOff 529 0; SOff 740 0; SOff 853 0; SOff 32 0; SOff 852 0; SOff 854 0; SOff 855 0; SOff 856 0; SOff 857 0; SOff 858 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 40 (CVal 8 (SOff 281 0)); YP09.mkChunk 48 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 56 (CVal 8 (SOff 516 160)); YP09.mkChunk 64 (CVal 8 (SOff 516 32)); YP09.mkChunk 72 (CVal 8 (SOff 10 384)); YP09.mkChunk 80 (CVal 8 (SOff 516 0)); YP09.mkChunk 88 (CVal 8 (SOff 516 96)); YP09.mkChunk 96 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 104 (CVal 8 (SOff 282 0)); YP09.mkChunk 112 (CVal 8 (SOff 10 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 0)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit 18446744073709551615))); YP09.mkChunk 136 (CVal 8 (SOff 722 0)); YP09.mkChunk 144 (CVal 8 (SOff 741 0)); YP09.mkChunk 152 (CVal 8 (SLit 1))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition tj_e (cx : tjcx) (i : Z) : entry := reac_disco_table_json_c.tj_entry (c_T cx) i.
Definition tj_age (cx : tjcx) (i : Z) : Z := age_of (c_now cx) (disco_table_c.last_of (c_T cx) i).
Definition tj_after4 (cx : tjcx) (i : Z) : list Z :=
P5 (tj_e cx i) ++ P6 (c_now cx) (tj_e cx i) ++ tj_lemmas.tj_rest (c_T cx) (c_now cx) (i + 1).
Definition tj_after2 (cx : tjcx) (i : Z) : list Z :=
P3 reac_disco_table_json_c.box_tok (tj_e cx i) ++ P4 reac_disco_table_json_c.box_tok (tj_e cx i) ++ tj_after4 cx i.
Definition tj_after1 (cx : tjcx) (i : Z) : list Z := P2 (tj_e cx i) ++ tj_after2 cx i.
Section h.
Variable B : asyms.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Definition tj_lbody (i : Z) (cx : tjcx) (E : env) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
(ms3 : machine_state) : Prop :=
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
tj_keep B cx W3 (ms_mem ms3) /\ 3 <= c_cap cx /\
0 <= i < disco_table_c.n_of (c_T cx) /\
ew E 721 = w64 (48 * i) /\ ew E 722 = w64 i /\
ew E 740 = w64 (c_t cx + 48 * i) /\ ew E 741 = w64 (tj_age cx i).
Definition tj_wrote (cx : tjcx) (W3 : world SEGS) (ms3 : machine_state) (acc rest : list Z) : Prop :=
Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) = acc ++ rest /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ [0]).
Definition tj_split (E : env) (n1 n2 : nat) (acc : list Z) : Prop :=
exists o1 o2 : Z, ew E n1 = w64 o1 /\ ew E n2 = w64 o2 /\ 0 <= o1 /\ 0 <= o2 /\ o1 + o2 = Z.of_nat (length acc).
Definition INV_tjM (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody i cx E ly3 S3 W3 ms3 /\
exists acc : list Z, tj_split E 733 764 acc /\ tj_wrote cx W3 ms3 acc (tj_after1 cx i).
Definition INV_tjR (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody i cx E ly3 S3 W3 ms3 /\
exists acc : list Z, tj_split E 793 784 acc /\ tj_wrote cx W3 ms3 acc (tj_after2 cx i).
Definition INV_tjU (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody i cx E ly3 S3 W3 ms3 /\
model_of reac_disco_table_json_c.box_tok (tj_e cx i) = (s_unknown, s_0x0) /\
exists acc : list Z, ew E 813 = w64 (Z.of_nat (length acc)) /\ tj_wrote cx W3 ms3 acc (tj_after2 cx i).
Definition INV_tjK (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody i cx E ly3 S3 W3 ms3 /\
ew E 834 = w64 (SB + (c_t cx + 48 * i + 13) / 8) /\ ew E 832 = w64 (SB + (c_t cx + 48 * i + 14) / 8) /\
(exists tok : list Z,
model_of reac_disco_table_json_c.box_tok (tj_e cx i) =
(tok, dec (e_decl_in (tj_e cx i)) ++ [120] ++ dec (e_decl_out (tj_e cx i))) /\
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (tj_F cx + 96) (tok ++ [0]) /\
range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (tj_F cx + 96) (Z.of_nat (length tok) + 1) /\
shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms3)) (tj_F cx + 96) (Z.of_nat (length tok) + 1)) /\
exists acc : list Z, ew E 833 = w64 (Z.of_nat (length acc)) /\ tj_wrote cx W3 ms3 acc (tj_after2 cx i).
Definition INV_tjT (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 0 /\ tj_lbody i cx E ly3 S3 W3 ms3 /\
exists acc : list Z, ew E 852 = w64 (Z.of_nat (length acc)) /\ tj_wrote cx W3 ms3 acc (tj_after4 cx i).
Definition tj_fromM (i : Z) : Prop := tj_from0 B IMG ss_tjM (INV_tjM i).
Definition tj_fromR (i : Z) : Prop := tj_from0 B IMG ss_tjR (INV_tjR i).
Definition tj_fromU (i : Z) : Prop := tj_from0 B IMG ss_tjU (INV_tjU i).
Definition tj_fromK (i : Z) : Prop := tj_from0 B IMG ss_tjK (INV_tjK i).
Definition tj_fromT (i : Z) : Prop := tj_from0 B IMG ss_tjT (INV_tjT i).
Definition tj_seg_mac : Prop :=
forall i, tj_fromX B IMG -> tj_fromM i -> tj_fromL B IMG i.
Definition tj_seg_role : Prop :=
forall i, tj_fromX B IMG -> tj_fromR i -> tj_fromM i.
Definition tj_seg_box : Prop :=
forall i, tj_fromU i -> tj_fromK i -> tj_fromR i.
Definition tj_seg_unk : Prop :=
forall i, tj_fromX B IMG -> tj_fromT i -> tj_fromU i.
Definition tj_seg_tok : Prop :=
forall i, tj_fromX B IMG -> tj_fromT i -> tj_fromK i.
Definition tj_seg_tail : Prop :=
forall i, tj_fromX B IMG -> tj_fromC B IMG -> tj_fromL B IMG (i + 1) -> tj_fromT i.
End h.
End f.
End d.
