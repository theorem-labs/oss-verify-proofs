(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkc YCj4 YC8g YCjr YCj1 YCj0 YCja.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Record flcx := mkFLCX {
c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_ch : list (Z * Z * Z);
c_g : Z; c_s : cgif_st; c_N : Z; c_i : nat; c_f : frame_st; c_rest : list (Z * Z);
c_fpos : Z; c_sp1 : Z;
c_wfn : Z; c_hw : Z; c_uar : Z;
c_E0 : env }.
Definition fl_FP (cx : flcx) : list (Z * Z) := [(fr_ptr (c_f cx) + 20, fr_ptr (c_f cx) + 24); (cg_raw (c_s cx) + 40, cg_raw (c_s cx) + 44)].
Definition fl_base (B : asyms) (CTX : list (list Z)) (wfn hw : Z) (cx : flcx) : Prop :=
afn_pre SEGS B TFLUSH_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
In (raZ (c_regs cx) :: spine (c_ch cx)) CTX /\ Z.of_nat (length (frames (c_S cx))) <= 7 /\ spZ (c_regs cx) + 32 <= ly_top (c_ly cx) /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
getr (c_regs cx) 10 = w64 (c_g cx) /\
tcgif_at SEGS (c_wfn cx) (c_hw cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx) (c_s cx) /\ cgif_wf (c_s cx) (c_N cx) /\
(c_i cx = 1%nat \/ c_i cx = 2%nat) /\ nth_error (cg_frames (c_s cx)) (c_i cx) = Some (Some (c_f cx)) /\
getr (c_regs cx) 11 = w64 (fr_ptr (c_f cx)) /\
getr (c_regs cx) 12 = w64 (frame_ptr (nth (c_i cx - 1) (cg_frames (c_s cx)) None)) /\
Permutation (ablocks B (c_ly cx) (c_S cx)) (cgif_blocks (c_g cx) (c_s cx) (c_N cx) ++ c_rest cx) /\
st_nev (c_S cx) + EV_FLUSH <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_FLUSH <= LIVE_MAX /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -352) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 28)%nat -> ew (c_E0 cx) (32 + j) = nth j (fl_extra (c_hw cx) (c_s cx) (c_f cx) (c_uar cx)) (Z_to_bv 64 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
c_wfn cx = wfn /\ c_hw cx = hw /\ c_uar cx = as_uar_cell B.
Definition fl_F (cx : flcx) : Z := frame_addr (c_ly cx) 1 (c_fpos cx).
Definition fl_FL (cx : flcx) : Z := flag_addr (c_ly cx) 1 (c_fpos cx).
Definition fl_E (cx : flcx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
(forall j, (1 <= j < 28)%nat -> ew E (32 + j) = nth j (fl_extra (c_hw cx) (c_s cx) (c_f cx) (c_uar cx)) (Z_to_bv 64 0)) /\
ew E 60 = Z_to_bv 64 (c_sp1 cx) /\ ew E 516 = Z_to_bv 64 (fl_F cx) /\ ew E 528 = Z_to_bv 64 (fl_FL cx) /\ ew E 529 = Z_to_bv 64 (SB + fl_F cx / 8) /\
img_env VAL A_LIM E.
Definition fl_post (B : asyms) (cx : flcx) : world SEGS -> config -> Prop :=
apost_base SEGS B TFLUSH_STK (fl_FP cx) (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) EV_FLUSH
(fun ly' S' W' regs' mem' md' => exists r gen' rwcur' : Z,
getr regs' 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
tcgif_at SEGS (c_wfn cx) (c_hw cx) (mrestrict (w_H W') mem') (c_g cx) (flush_upd (c_s cx) (c_i cx) gen' rwcur') /\ cgif_wf (flush_upd (c_s cx) (c_i cx) gen' rwcur') (c_N cx) /\
Permutation (ablocks B ly' S') (cgif_blocks (c_g cx) (c_s cx) (c_N cx) ++ c_rest cx)).
Definition fl_from (B : asyms) (CTX : list (list Z)) (wfn hw : Z) (ss : sstate)
(INV : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : flcx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
fl_base B CTX wfn hw cx -> fl_E cx E ->
ajournal SEGS B TFLUSH_STK (spZ (c_regs cx)) (fl_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (1, c_fpos cx) :: frames (c_S cx) ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (fl_post B cx).
Definition INV_0 (B : asyms) (kmax : Z) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= kmax /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Definition clr4 (x : Z) : Z := x - x mod 4.
Definition clr2 (x : Z) : Z := x - x mod 2.
Definition fl_isfirst (cx : flcx) : bool := frame_ptr (nth (c_i cx - 1) (cg_frames (c_s cx)) None) =? 0.
Definition fl_hasalpha (cx : flcx) : bool := negb ((Z.land (cg_attr (c_s cx)) 8 =? 0) && (Z.land (fr_attr (c_f cx)) 2 =? 0)).
Definition fl_settr (cx : flcx) : bool := negb (Z.land (fr_attr (c_f cx)) 4 =? 0).
Definition fl_uselct (cx : flcx) : bool := negb (Z.land (fr_attr (c_f cx)) 1 =? 0).
Definition fl_gen1 (cx : flcx) : Z := if fl_isfirst cx || fl_hasalpha cx then clr4 (fr_gen (c_f cx)) else fr_gen (c_f cx).
Definition fl_gen2 (cx : flcx) : Z := if fl_settr cx then clr2 (fl_gen1 cx) else fl_gen1 cx.
Definition fl_npal (cx : flcx) : Z := if fl_uselct cx then fr_nlp (c_f cx) else cg_ngp (c_s cx).
Definition fl_gen3 (cx : flcx) : Z := if fl_npal cx =? 256 then clr2 (fl_gen2 cx) else fl_gen2 cx.
Lemma clr4_range : forall x, 0 <= x -> 0 <= clr4 x <= x. Proof. intros x Hx. unfold clr4. pose proof (Z.mod_pos_bound x 4 ltac:(lia)). pose proof (Z.mod_le x 4 Hx ltac:(lia)). lia. Qed.
Lemma clr2_range : forall x, 0 <= x -> 0 <= clr2 x <= x. Proof. intros x Hx. unfold clr2. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). pose proof (Z.mod_le x 2 Hx ltac:(lia)). lia. Qed.
Definition ss_B : sstate :=
(mkSS 6992
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 513 0; SOff 514 0; SOff 515 0; SOff 2 0; SOff 60 0; SLit 0; SOff 246 0; SOff 240 6660; SOff 529 0; SOff 516 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 18 0; SOff 19 0; SOff 20 0;
SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 524 0; SOff 32 0; SOff 526 0; SOff 527 0]
[{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 16;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 53 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ra_deads_B2 : list (bv 5) := [10; 11; 13]%bv.
Definition ss_B2_0 : sstate :=
(mkSS 7296
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 11 16; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0;
SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 12 0) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))) (SLit 1);
SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)); SOff 52 0; SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8); SAlu ALU_AND (SOff 52 0) (SLit 4); SOff 10 0; SOff 11 0;
SOff 12 0; SOff 18 0; SOff 41 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 40 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SOff 527 0]
[{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 184; YP09.c_val := CVal 8 (SOff 58 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |};
{| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 591 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |})];
f_conds :=
[{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SOff 52 0) (SLit 4); ac_b := SLit 0 |};
{|
ac_c := BC_EQ; ac_a := SAlu ALU_AND (SAlu ALU_OR (SAlu ALU_SLTU (SOff 12 0) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))) (SLit 1); ac_b := SLit 0
|}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_B2 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs ss_B2_0 592 [10; 11; 13]%nat) (f_atoms (ss_facts ss_B2_0) ++ [(591%nat, mkAF 0 4294967295 0)])).
Definition INV_B2 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
exists gen, ew E 591 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32 /\
(frame_ptr (nth (c_i cx - 1) (cg_frames (c_s cx)) None) = 0 -> gen mod 4 = 0).
Definition ra_deads_B3 : list (bv 5) := [10; 11; 13; 20]%bv.
Definition ss_B3_0 : sstate :=
(mkSS 7384
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 11 16; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SLit 256; SLit 0; SOff 52 0; SOff 594 0; SAlu ALU_AND (SOff 52 0) (SLit 4);
SOff 10 0; SOff 11 0; SOff 12 0; SOff 18 0; SOff 41 0; SOff 42 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 40 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SOff 527 0]
[{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 58 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (591%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SOff 42 0; ac_b := SLit 256 |}; {| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SOff 52 0) (SLit 1); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_B3 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs ss_B3_0 622 [10; 11; 13; 20]%nat)
(filter (fun p => negb (Nat.eqb (fst p) 591)) (f_atoms (ss_facts ss_B3_0)) ++ [(621%nat, mkAF 0 4294967295 0); (625%nat, mkAF 0 65535 0)])).
Definition INV_B3 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32 /\
(frame_ptr (nth (c_i cx - 1) (cg_frames (c_s cx)) None) = 0 -> gen mod 4 = 0)) /\
ew E 625 = Z_to_bv 64 (fl_npal cx).
Lemma fl_E_havoc : forall cx E N vs, (530 <= N)%nat -> fl_E cx E -> fl_E cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & EX & E60 & E516 & E528 & E529 & HEI). unfold fl_E. rewrite !ew_havoc_old by lia.
split; [|split; [|split; [exact E60 | split; [exact E516 | split; [exact E528 | split; [exact E529 | apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]]]]]]].
- intros n Hn. rewrite !ew_havoc_old by lia. apply AG. exact Hn.
- intros j Hj. rewrite !ew_havoc_old by lia. apply EX. exact Hj.
Qed.
Lemma INV_0_havoc : forall B kmax cx E N vs k ly3 S3 W3 ms3 md3,
INV_0 B kmax cx E k ly3 S3 W3 ms3 md3 -> INV_0 B kmax cx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
End b.
End a.
