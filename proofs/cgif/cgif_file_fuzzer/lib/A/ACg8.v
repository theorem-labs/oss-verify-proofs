(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC87.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_bX_rec Usp E32u Hing HTS hd Bhd Hfb Hfq :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
first
[
unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; unfold ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
|
unfold FPn; lazymatch type of E32u with _ = ?g => exists (g + 88, g + 92) end;
split; [left; reflexivity | cbn [fst snd]; lia] ]
| ]
| |- awr_ok _ (YP09.mkRegion (Some hd) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bhd with _ = ?p =>
eapply awr_ok_cons_block with (n := hd) (m := FRAME_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bhd | exact Hfb | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size FRAME_SIZE) with 40; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPb; apply (proj2 (YI04.inFP_app _ _ _)); left; unfold ablocks_fp;
exists (p, p + req_size FRAME_SIZE); split;
[ apply (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) _ (p, FRAME_SIZE)); exact Hfq
| cbn [fst snd]; change (req_size FRAME_SIZE) with 40; lia ]
| ] end
end
| fail 1 "awr_b: no rule for the head region" ];
awr_bX_rec Usp E32u Hing HTS hd Bhd Hfb Hfq
end.
Ltac awr_bX Usp E32u Hing HTS hd Bhd Hfb Hfq :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_bX_rec Usp E32u Hing HTS hd Bhd Hfb Hfq.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition xs_BX (ih ho : Z) (hd : nat) : sstate :=
add_atom (add_atom (add_atom
(mkSS AF_B (ss_regs (xs_B ih ho hd)) (af_hdr hd :: ss_mem (xs_B ih ho hd)) None (ss_facts (xs_B ih ho hd)))
hd hfactA) 71 (mkAF 0 4294967295 0)) 72 (mkAF 0 65535 0).
Definition xs_L0 (ih ho : Z) (hd : nat) : sstate :=
(mkSS AF_LOOP
[SLit 0; SOff 644 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 32 88; shq 32 88; SOff 649 0; SOff 650 0; SOff 651 0; SOff 652 0; SOff 653 0; SOff 46 0; SOff 654 0; SOff 655 0; SOff 32 0; SOff 657 0; SOff 648 0; shq 32 ho; SOff 38 0; SOff 32 ho; SLit ih; SOff 658 0; SOff 658 0; SOff 657 0; SOff 656 0; SOff 659 0; SOff 660 0; SOff 661 0]
[{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -216; YP09.c_val := CVal 8 (SAlu ALU_ADD (SOff 72 0) (SExt false 16 (SOff 51 0))) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff hd 24) |};
{| c_off := -208; YP09.c_val := CVal 8 (shq hd 24) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff hd 0) |};
{| c_off := -120; YP09.c_val := CVal 8 (SOff 46 0) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 46 24) |};
{| c_off := -152; YP09.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 32 92) |};
{| c_off := -192; YP09.c_val := CVal 8 (shq 32 92) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 46 16) |};
{| c_off := -144; YP09.c_val := CVal 8 (shq 46 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (shq 32 40) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |};
{| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |};
{| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |};
{| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |};
{| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |};
{| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |};
{| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(72%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(71%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(hd,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(2%nat,
{|
af_lo := 70368744177664;
af_hi := 140737488355328;
af_al2 := 4
|});
(32%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(38%nat,
{| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 3
|})];
f_conds := [];
f_alias := []
|}).
Definition xs_SM (ih ho : Z) (hd : nat) : sstate :=
(mkSS AF_SAME
[SLit 0; SOff 644 0; SOff 2 (-224); SOff 3 0; SOff 4 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 32 88; shq 32 88; SOff 648 0; SOff 649 0; SOff 650 0; SOff 651 0; SOff 652 0; SOff 653 0; SOff 654 0; SOff 655 0; SOff 32 0; SOff 656 0; SOff 657 0; shq 32 ho; SOff 38 0; SOff 32 ho; SLit ih; SOff 658 0; SOff 659 0; SOff 660 0; SOff 661 0; SOff 662 0; SOff 663 0; SOff 664 0]
[{|
r_base := Some hd;
r_lo := 0;
r_hi := 40;
r_wlo := 24;
r_whi := 24;
r_chunks :=
[{| c_off := 8; YP09.c_val := CVal 8 (SOff 70 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 71 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 72 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -224;
r_hi := -104;
r_wlo := -224;
r_whi := -104;
r_chunks :=
[{| c_off := -216; YP09.c_val := CVal 8 (SAlu ALU_ADD (SOff 72 0) (SExt false 16 (SOff 51 0))) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff hd 24) |};
{| c_off := -208; YP09.c_val := CVal 8 (shq hd 24) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff hd 0) |};
{| c_off := -120; YP09.c_val := CVal 8 (SOff 46 0) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 46 24) |};
{| c_off := -152; YP09.c_val := CVal 8 (SLit ho) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 32 92) |};
{| c_off := -192; YP09.c_val := CVal 8 (shq 32 92) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 67 0) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 46 16) |};
{| c_off := -144; YP09.c_val := CVal 8 (shq 46 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SOff 32 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (shq 32 40) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 38 0) |}] |};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 88;
r_whi := 92;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |};
{| c_off := 24; YP09.c_val := CVal 8 (SOff 39 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 40 0) |};
{| c_off := 44; YP09.c_val := CVal 4 (SOff 41 0) |};
{| c_off := 48; YP09.c_val := CVal 2 (SOff 42 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 43 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 54; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 72; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit pf) |};
{| c_off := 88; YP09.c_val := CVal 4 (SOff 37 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit ih) |}]
|};
{|
r_base := Some 46%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 47 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 48 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 49 0) |};
{| c_off := 20; YP09.c_val := CVal 4 (SOff 50 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 51 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 52 0) |};
{| c_off := 28; YP09.c_val := CVal 1 (SOff 53 0) |}]
|}]
None
{|
f_atoms :=
[(72%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(71%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(hd,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(2%nat,
{|
af_lo := 70368744177664;
af_hi := 140737488355328;
af_al2 := 4
|});
(32%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 4
|});
(38%nat,
{| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(46%nat,
{|
af_lo := 4096;
af_hi := 140737479966720;
af_al2 := 3
|})];
f_conds := [];
f_alias := []
|}).
Section h.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation cmpq G attr gen delay ctrans nlp lpal img HD := (fun pq : Z * Z => negb (YO07.cmp_pixel G (YI0b.af_nf G attr gen delay ctrans nlp lpal img) HD (fst pq) (snd pq))).
Definition af_preBX (B : asyms) ly S W (regs : bvmap 5 word) mem md (g cfp : Z) (s : cgif_st) (N fattr : Z) (ms1 : machine_state) md1 : Prop :=
ajournal SEGS B TADDFRAME_STK (spZ regs) (FPn g) ly S W mem md [] ly S W (ms_mem ms1) md1 0 /\
af_side (mrestrict (w_H W) (ms_mem ms1)) g s /\
(forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) (ms_mem ms1)) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)) /\
(cg_cur s = 0 \/ cg_cur s = R_PENDING) /\
(Z.land fattr 1 <> 0 \/ Z.land (cg_attr s) 4 = 0) /\
(cg_ihead s = 1 \/ cg_ihead s = 2).
Definition af_xl (s : cgif_st) (fattr fgen delay nlp tidx : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (HD : YO07.frame) (kk : Z) : Prop :=
cgif_live gs /\ gsF = YI0b.af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs /\
qslot gs (Z.to_nat (cg_ihead s)) = Some HD /\
YI0b.af_merged (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG gs =
(if forallb (cmpq (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG HD) (combine IMG (YO07.f_img HD))
then Some (YO07.q_set gs (YO07.s_ihead gs) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))) else None) /\
forallb (cmpq (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG HD) (combine (firstn (Z.to_nat kk) IMG) (firstn (Z.to_nat kk) (YO07.f_img HD))) = true.
Definition af_xsm (s : cgif_st) (delay : Z) (gs gsF : YO07.gif_st) (HD : YO07.frame) : Prop :=
cgif_live gs /\ qslot gs (Z.to_nat (cg_ihead s)) = Some HD /\ delay + YO07.f_delay HD <= 65535 /\
gsF = YO07.q_set gs (YO07.s_ihead gs) (Some (YO07.set_delay HD (delay + YO07.f_delay HD))).
Definition AF_SM_stmtX (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (HD : YO07.frame),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preBX B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (xs_SM (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
af_xsm s delay gs gsF HD ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_L_stmtX (B : asyms) : Prop :=
forall (n : nat) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (kk : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (HD : YO07.frame),
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preBX B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (xs_L0 (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
ew E 657 = Z_to_bv 64 (img + kk) -> ew E 658 = Z_to_bv 64 (fr_img f + kk) -> ew E 648 = Z_to_bv 64 (Z.of_nat n) ->
0 <= kk -> kk + Z.of_nat n = N -> (1 <= n)%nat ->
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_Li_stmtX (B : asyms) (ihv : Z) : Prop :=
forall (n : nat) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (kk : Z) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st) (HD : YO07.frame),
cg_ihead s = ihv ->
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preBX B ly S W regs mem md g cfp s N fattr ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (xs_L0 (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)) ->
ew E 657 = Z_to_bv 64 (img + kk) -> ew E 658 = Z_to_bv 64 (fr_img f + kk) -> ew E 648 = Z_to_bv 64 (Z.of_nat n) ->
0 <= kk -> kk + Z.of_nat n = N -> (1 <= n)%nat ->
af_xl s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF HD kk ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
Definition AF_Bi_stmtX (B : asyms) (ihv : Z) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E : env) (ms1 : machine_state) md1 (f : frame_st) (GPAL IMG LPAL : list Z) (gs gsF : YO07.gif_st),
cg_ihead s = ihv ->
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E ->
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E (xs_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E (mrestrict (w_H W) (ms_mem ms1)) ->
af_xok s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF ->
SRr SEGS W (mkCfg ms1 md1) (af_postX K MT XN B ly S W regs mem md g s N img fattr lpa nlp rest GPAL gs gsF EV_ADDFRAME).
End h.
Section l.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Lemma af_pre_of_BX : forall ly S W regs mem md g cfp s N lpal img fattr fgen delay nlp tidx f E ms1 md1,
af_preBX B ly S W regs mem md g cfp s N fattr ms1 md1 -> af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E ->
af_preX B ly S W regs mem md g cfp s N fattr E ms1 md1.
Proof. intros * (H1 & H2 & H3 & H4 & H5 & H6) (_ & E67 & _). repeat (split; [assumption|]). exact H6. Qed.
Lemma af_B_extX : forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest (E0 : env) (ms1 : machine_state) md1 (f : frame_st) GPAL IMG LPAL gs,
af_cxX K MT XN B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest GPAL IMG LPAL gs ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E0 ->
af_preX B ly S W regs mem md g cfp s N fattr E0 ms1 md1 ->
nth (Z.to_nat (cg_ihead s)) (cg_frames s) None = Some f ->
st_ok_pi SEGS VAL E0 (xs_B (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) ->
sh_ok SEGS Bxa af_SH E0 (mrestrict (w_H W) (ms_mem ms1)) ->
let E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)] in
af_EB regs g s cfp lpal img fattr fgen delay nlp tidx f E /\ af_preBX B ly S W regs mem md g cfp s N fattr ms1 md1 /\
st_ok_pi SEGS VAL E (xs_BX (cg_ihead s) (8 * cg_ihead s) (33 + Z.to_nat (cg_ihead s))) (restrict (w_H W) ms1) /\
sh_ok SEGS Bxa (af_SHB (33 + Z.to_nat (cg_ihead s))) E (mrestrict (w_H W) (ms_mem ms1)).
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f GPAL IMG LPAL gs CX HE0 HPX Hn HS SHOK.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67_0 & Hih).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (HFS : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (HfIn : In (Some f) (cg_frames s)) by (rewrite <- Hn; apply nth_In; rewrite (proj1 HWF); destruct Hih as [-> | ->]; cbn; lia).
pose proof (proj2 HSD f HfIn) as HOBf.
pose proof (af_B_blocks B LAWS ly S W mem md g cfp s N img fattr lpa nlp rest f HAR HPerm HFO HfIn) as (_ & _ & Hfb & Hfq & _ & _ & _ & _ & _ & Dgh & Dch).
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR1 Hfb) as (Hh16 & Hh4096 & Hhceil & Hhh_ia & HhP & _). pose proof (proj1 Hhh_ia) as Hhh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR1 Hfb) as Hhh_img.
change (req_size FRAME_SIZE) with 40 in Hhceil, Hhh, HhP, Hhh_img.
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) (fr_img f) HOBf eq_refl eq_refl) as [Vhimg Rhimg].
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) (fr_attr f) HOBf eq_refl eq_refl) as [Vhattr Rhattr].
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) (fr_delay f) HOBf eq_refl eq_refl) as [Vhdel Rhdel].
cbn [snd N.to_nat] in Vhimg, Rhimg, Vhattr, Rhattr, Vhdel, Rhdel.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rhimg. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rhattr. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rhdel.
pose proof (st_ok_pi_havoc_hi 70 E0 _ _ [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)] HS ltac:(destruct Hih as [Q|Q]; rewrite Q; vm_compute; reflexivity)) as HS1.
clear HS. rename HS1 into HS. cbv zeta.
set (E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)]) in *. try (let Hx := fresh "HEIo" in rename HEI into Hx). assert (HEI : img_env VAL A_LIM E) by hei_prove.
assert (OLD : forall n, (n < 70)%nat -> ew E n = ew E0 n) by (intros n Hn0; subst E; apply YN3v.ew_havoc_old; clear - Hn0; lia).
assert (E70 : ew E 70 = Z_to_bv 64 (fr_img f)) by (subst E; change 70%nat with (70 + 0)%nat; rewrite (YN3v.ew_havoc_new E0 70 _ 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (E71 : ew E 71 = Z_to_bv 64 (fr_attr f)) by (subst E; change 71%nat with (70 + 1)%nat; rewrite (YN3v.ew_havoc_new E0 70 _ 1 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (E72 : ew E 72 = Z_to_bv 64 (fr_delay f)) by (subst E; change 72%nat with (70 + 2)%nat; rewrite (YN3v.ew_havoc_new E0 70 _ 2 (Z_to_bv 64 0)) by (cbn; lia); reflexivity).
assert (HE : af_E regs g s cfp lpal img fattr fgen delay nlp tidx E) by (subst E; apply af_E_havoc; [exact HE0 | clear; lia | clear; cbv; lia]).
assert (E67 : ew E 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD by (clear - PBASE PBLO; lia); exact E67_0).
assert (HAE0 : env_agree 70 E0 E) by (subst E; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
pose proof (sh_ok_agree SEGS Bxa af_SH 70 E0 E _ HAE0 eq_refl SHOK) as SHOK1. clear SHOK.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & _).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
split; [split; [exact HE | split; [exact E67 | split; [exact E70 | split; [exact E71 | exact E72]]]]|].
split; [split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | exact Hih]]]]]|].
assert (Bhd : bv_unsigned (ew E (33 + Z.to_nat (cg_ihead s))) = fr_ptr f).
{ destruct Hih as [Q|Q]; rewrite Q in Hn |- *; [change (33 + Z.to_nat 1)%nat with 34%nat; rewrite E34 | change (33 + Z.to_nat 2)%nat with 35%nat; rewrite E35];
[change (Z.to_nat 1) with 1%nat in Hn | change (Z.to_nat 2) with 2%nat in Hn]; rewrite Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia. }
split.
- unfold xs_BX.
apply st_ok_pi_add_fact; [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E72, unsigned_lit_small by (clear - Rhdel; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rhdel; lia].
apply st_ok_pi_add_fact; [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E71, unsigned_lit_small by (clear - Rhattr; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Rhattr; lia].
apply st_ok_pi_add_fact; [| unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bhd; change (2 ^ 4) with 16; clear - Hh4096 Hhh Hhceil Hh16 C1 C3 C4; lia].
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
change (mkSS AF_B _ _ None _) with (mkSS (ss_pc ssx) (ss_regs ssx) (af_hdr (33 + Z.to_nat (cg_ihead s)) :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx)) | st_ok _ _ ?ssx _ =>
change (mkSS AF_B _ _ None _) with (mkSS (ss_pc ssx) (ss_regs ssx) (af_hdr (33 + Z.to_nat (cg_ihead s)) :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx))  end.
apply (st_ok_pi_add_region E _ _ (af_hdr (33 + Z.to_nat (cg_ihead s))) HS eq_refl).
+ unfold region_ok, af_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
rewrite Bhd. split; [clear - Hh4096 Hhceil C1; lia|]. split; [clear - Hh4096 Hhceil C1; lia|].
split; [intros o Ho; exfalso; clear - Ho; lia|].
constructor; [eapply (chunk_ok_val SEGS E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhimg]|].
constructor; [eapply (chunk_ok_val SEGS E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E71, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhattr]|].
constructor; [eapply (chunk_ok_val SEGS E _ (fr_ptr f)); [cbn [sv_denot]; rewrite E72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vhdel]|].
constructor.
+ destruct Hih as [Q|Q]; rewrite Q in Bhd |- *;
[change (33 + Z.to_nat 1)%nat with 34%nat in Bhd |- * | change (33 + Z.to_nat 2)%nat with 35%nat in Bhd |- *];
(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bhd, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgh Dch Hh4096 Hhh Hhh_img Hhceil Hcfp HZg Hceil Hslo HTS C1 C3 C4 Hob241 Hob253; unfold off_img in Hhh_img; repeat split; lia).
- unfold sh_ok, af_SHB. apply Forall_app. split; [exact SHOK1|]. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS ly S W (ms_mem ms1) md1 E Bxa (33 + Z.to_nat (cg_ihead s)) (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE HAR1 Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bhd.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia.
Qed.
Lemma af_xmtr00 : forall S N, af_xnums MT XN -> 1 <= N <= 100000000 -> af_xmtr MT XN S S N 0 0.
Proof.
intros S N (HXM & HXN & HXMN) HN. pose proof (HXM N HN) as BM. pose proof (HXN N HN) as BN. pose proof (HXMN N HN) as BMN. pose proof (mo_free_nonneg MT MLAW) as Hf0.
pose proof (mo_malloc_nonneg MT MLAW 40 ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW N ltac:(lia)). pose proof (mo_malloc_nonneg MT MLAW 196605 ltac:(lia)).
exists 0. split; [lia|]. split; [exact (mle_start MT S MLAW)|]. split; lia.
Qed.
Lemma af_xsm_ret : forall (m : word -> option byte) md s N (k : nat) f d' delay GPAL gs gsF HD,
cgif_relA SEGS K m md s pf N GPAL gs -> cgif_wf s N -> cg_ihead s = Z.of_nat k -> (k < 3)%nat ->
nth k (cg_frames s) None = Some f -> af_xsm s delay gs gsF HD -> d' = delay + fr_delay f ->
cgif_relA SEGS K m md (upd_frame s k (set_fr_delay f d')) pf N GPAL gsF /\ af_xout gs gsF N.
Proof.
intros m md s N k f d' delay GPAL gs gsF HD XR Hwf Hih Hk Hn (XLV & Hq & Hfd & XGF) Hd.
rewrite Hih, Nat2Z.id in Hq.
apply (proj1 (cgif_relA_split SEGS K m md s pf N GPAL gs)) in XR as ((XCUR & XOCC) & XS & XL).
pose proof (proj1 (af_xlive_iff SEGS m s N GPAL gs) (XL XLV)) as [XH XSL]. pose proof XH as (_ & _ & XHih & _).
pose proof (proj1 Hwf) as Hlen. pose proof Hwf as (_ & HW1 & HH1 & HN & _).
assert (Eih : YO07.s_ihead gs = Z.of_nat k) by (rewrite <- XHih; exact Hih).
rewrite Eih in XGF. rewrite XGF.
pose proof (q_set_fields gs (Z.of_nat k) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))) as (Ecur & _ & Eout & _).
split; [| unfold af_xout, FRAME_OUT; rewrite Eout; clear - HW1 HH1 HN; nia].
apply (proj2 (cgif_relA_split SEGS K m md _ pf N GPAL _)).
split; [split; [rewrite Ecur; exact XCUR | exact (cgif_occ_upd s gs k _ _ Hk Hlen XOCC)]|].
split; [rewrite Eout; exact XS|].
intros _. apply (proj2 (af_xlive_iff SEGS m _ N GPAL _)). split; [exact (af_xhdr_upd SEGS m s GPAL gs k _ _ XH)|].
apply (af_xslots_upd SEGS m s N gs k _ _ (fun _ => True) Hk Hlen); [exact (af_xslots_mono SEGS m s N gs _ _ (fun j _ => I) XSL)|].
intros _. pose proof (XSL k Hk I) as R. rewrite Hn, Hq in R. cbn [oframe_relbA] in R.
destruct R as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
unfold frame_relbA. cbn [set_fr_delay fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal YO07.set_delay YO07.f_attr YO07.f_gen YO07.f_delay YO07.f_nlp YO07.f_ctrans YO07.f_disp YO07.f_trans YO07.f_img YO07.f_lpal].
split; [exact A1|]. split; [exact A2|]. split; [rewrite Hd, A3; reflexivity|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9 | exact A10].
Qed.
End l.
End e.
End c.
Ltac af_B_namesX LAWS CX HEB HPB Hn :=
lazymatch type of CX with af_cxX _ _ _ ?B ?ly ?S ?W ?regs ?mem ?md ?ch ?g ?cfp ?s ?N ?lpal ?lpa ?img ?fattr ?fgen ?delay ?nlp ?tidx ?rest ?GPAL ?IMG ?LPAL ?gs =>
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ ?f ?E =>
pose proof HPB as (HJ & HSD & HGK & Hcur & HnoTab & Hih);
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive);
pose proof (proj2 CX) as (_ & Hpfr & XREL0 & _ & XIMG0 & XIMGL & XLPAL0 & _);
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (HTS : TADDFRAME_STK = 17664) by reflexivity; assert (HFS : FRAME_SIZE = 40) by reflexivity; assert (HES : ESTACK = 4096) by reflexivity;
set (sp0 := spZ regs) in *;
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity);
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _); pose proof (proj1 Hgh_ia) as Hgh;
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hing) as Hgh_img;
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img;
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA);
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Hf4096 & Hfceil & Hfhigh);
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img;
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia);
pose proof (in_app_sub _ _ cfp 32 Hfhigh ltac:(clear - Hflo; lia) ltac:(clear; lia) ltac:(clear - Hfhi; lia)) as Hcfp_ia;
pose proof (proj1 HWF) as Hlen;
assert (HfIn : In (Some f) (cg_frames s)) by (rewrite <- Hn; apply nth_In; rewrite Hlen; destruct Hih as [-> | ->]; cbn; lia);
pose proof (af_B_blocks B LAWS ly S W mem md g cfp s N img fattr lpa nlp rest f HAR HPerm HFO HfIn) as (Himg & Hfimg & Hfb & Hfq & Dig & Dfg & Dic & Dfc & Dif & Dgh & Dch);
pose proof (af_B_blocks2 B LAWS ly S W mem md g s N img fattr lpa nlp rest f HAR HPerm HfIn) as [Dih Dfh];
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfb) as (Hh16 & Hh4096 & Hhceil & Hhh_ia & _); pose proof (proj1 Hhh_ia) as Hhh;
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hfb) as Hhh_img;
change (req_size FRAME_SIZE) with 40 in Hhceil, Hhh, Hhh_img;
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N HAR Himg) as (_ & Hi4096 & Hiceil & Hih0_ia & _); pose proof (proj1 Hih0_ia) as Hih0;
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Himg) as Hih0_img;
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N HAR Hfimg) as (_ & Hfi4096 & Hficeil & Hfih0_ia & _); pose proof (proj1 Hfih0_ia) as Hfih0;
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hfimg) as Hfih0_img;
pose proof HWF as (_ & HW1 & HH1 & HNWH & HNmax & _);
assert (HN1 : 1 <= N <= 100000000) by (clear - HW1 HH1 HNWH HNmax; nia);
pose proof (req_size_pos N ltac:(clear - HN1; lia)) as [_ HrN];
pose proof (obj_at_nth _ _ _ _ _ 7 (48, 2%N) (cg_W s) (proj1 HT) eq_refl eq_refl) as [_ RW];
pose proof (obj_at_nth _ _ _ _ _ 8 (50, 2%N) (cg_H s) (proj1 HT) eq_refl eq_refl) as [_ RH];
cbn [snd] in RW, RH; change (2 ^ (8 * Z.of_N 2)) with 65536 in RW, RH;
pose proof (obj_at_nth _ _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]; cbn [snd] in Rcur;
change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rcur;
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf];
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity])
end end.
