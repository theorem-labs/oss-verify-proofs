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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACja.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj0 ACj6.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Record flxx := mkFLXX { x_path : Z; x_pf : Z; x_Sg : list Z; x_GPAL : list Z; x_cur : YO07.frame; x_bef : option YO07.frame }.
Definition fl_FP0 (cx : flcx) : list (Z * Z) := [(fr_ptr (c_f cx) + 20, fr_ptr (c_f cx) + 24)].
Definition fl_FPX (cx : flcx) (xx : flxx) : list (Z * Z) :=
(fr_ptr (c_f cx) + 20, fr_ptr (c_f cx) + 24) :: (cg_raw (c_s cx) + 40, cg_raw (c_s cx) + 44) :: asink_fp (x_pf xx).
Definition fl_tmpblkX (B : asyms) (cx : flcx) (pt n : Z) (ly3 : alayout) (S3 : astate) : Prop :=
(4096 <= pt /\ zone2 pt n) /\ pt + n <= alloc_ceiling /\ pt mod 16 = 0 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)] /\
(forall blc lyq ownq i, In (pt, n) blc -> 0 <= i < n ->
awr_byte TFLUSH_STK (spZ (c_regs cx)) (fl_FP0 cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (pt + i)) /\
aftok (fl_FP0 cx) (ablocks B (c_ly cx) (c_S cx)) (pt, n).
Section c.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Definition fl_baseX (B : asyms) (CTX : list (list Z)) (wfn : Z) (cx : flcx) (xx : flxx) : Prop :=
afn_pre SEGS B TFLUSH_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
In (raZ (c_regs cx) :: spine (c_ch cx)) CTX /\ Z.of_nat (length (frames (c_S cx))) <= 7 /\ spZ (c_regs cx) + 32 <= ly_top (c_ly cx) /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
getr (c_regs cx) 10 = w64 (c_g cx) /\
xcgif_at SEGS (c_wfn cx) (x_path xx) (c_hw cx) (x_pf xx) (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_g cx) (c_s cx) /\ cgif_wf (c_s cx) (c_N cx) /\
(c_i cx = 1%nat \/ c_i cx = 2%nat) /\ nth_error (cg_frames (c_s cx)) (c_i cx) = Some (Some (c_f cx)) /\
getr (c_regs cx) 11 = w64 (fr_ptr (c_f cx)) /\
getr (c_regs cx) 12 = w64 (frame_ptr (nth (c_i cx - 1) (cg_frames (c_s cx)) None)) /\
Permutation (ablocks B (c_ly cx) (c_S cx)) (cgif_blocks (c_g cx) (c_s cx) (c_N cx) ++ c_rest cx) /\
st_nev (c_S cx) + EV_FLUSH <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_FLUSH <= LIVE_MAX /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -384) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
(forall j, (j < 28)%nat -> ew (c_E0 cx) (32 + j) = nth j (fl_extraX (x_path xx) (c_hw cx) (x_pf xx) (c_s cx) (c_f cx) (c_uar cx)) (Z_to_bv 64 0)) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
c_wfn cx = wfn /\ 0 <= c_hw cx < 2 ^ 64 /\ c_uar cx = as_uar_cell B /\
x_pf xx <> 0 /\ In (x_pf xx, FILE_BLOCK) (c_rest cx) /\
asink_at SEGS K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) (x_pf xx) (x_Sg xx) /\
Z.of_nat (length (x_Sg xx)) + FRAME_OUT (c_N cx) <= SINK_MAX /\
(Z.land (cg_attr (c_s cx)) 4 = 0 -> garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (cg_pal (c_s cx)) (x_GPAL xx) /\ Z.of_nat (length (x_GPAL xx)) = 3 * cg_ngp (c_s cx)) /\
frame_relbA SEGS true (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_N cx) (c_f cx) (x_cur xx) /\
oframe_relbA SEGS false (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_N cx) (nth (c_i cx - 1) (cg_frames (c_s cx)) None) (x_bef xx) /\
rw_attr (c_s cx) = raw_attr_of (cg_attr (c_s cx)) /\
mo_ok MT (c_S cx) (xm_flush XN (c_N cx)).
Definition fl_EX (cx : flcx) (xx : flxx) (E : env) : Prop :=
(forall n, (n < 33)%nat -> ew E n = ew (c_E0 cx) n) /\
(forall j, (1 <= j < 28)%nat -> ew E (32 + j) = nth j (fl_extraX (x_path xx) (c_hw cx) (x_pf xx) (c_s cx) (c_f cx) (c_uar cx)) (Z_to_bv 64 0)) /\
ew E 60 = Z_to_bv 64 (c_sp1 cx) /\ ew E 516 = Z_to_bv 64 (fl_F cx) /\ ew E 528 = Z_to_bv 64 (fl_FL cx) /\ ew E 529 = Z_to_bv 64 (SB + fl_F cx / 8) /\
img_env VAL A_LIM E.
Definition fl_postX (B : asyms) (cx : flcx) (xx : flxx) : world SEGS -> config -> Prop :=
apost_base SEGS B TFLUSH_STK (fl_FPX cx xx) (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) EV_FLUSH
(fun ly' S' W' regs' mem' md' => exists r rwcur' : Z,
getr regs' 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
xcgif_at SEGS (c_wfn cx) (x_path xx) (c_hw cx) (x_pf xx) (mrestrict (w_H W') mem') (c_g cx)
(flush_upd (c_s cx) (c_i cx) (YI0f.fl_gen3 (gcfg_of (c_s cx) (x_GPAL xx)) (x_cur xx) (x_bef xx)) rwcur') /\
cgif_wf (flush_upd (c_s cx) (c_i cx) (YI0f.fl_gen3 (gcfg_of (c_s cx) (x_GPAL xx)) (x_cur xx) (x_bef xx)) rwcur') (c_N cx) /\
Permutation (ablocks B ly' S') (cgif_blocks (c_g cx) (c_s cx) (c_N cx) ++ c_rest cx) /\
(exists code bytes,
YO07.flush_frame (gcfg_of (c_s cx) (x_GPAL xx)) (rc_int (rw_cur (c_s cx))) (x_cur xx) (x_bef xx) = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
asink_at SEGS K (mrestrict (w_H W') mem') md' (x_pf xx) (x_Sg xx ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT (c_N cx)) /\
mo_le MT (c_S cx) S' (xn_flush XN (c_N cx))).
Definition fl_fromX0 (B : asyms) (CTX : list (list Z)) (wfn : Z) (ss : sstate)
(INV : flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : flcx) (xx : flxx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
fl_baseX B CTX wfn cx xx -> fl_EX cx xx E ->
ajournal SEGS B TFLUSH_STK (spZ (c_regs cx)) (fl_FP0 cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (2, c_fpos cx) :: frames (c_S cx) ->
INV cx xx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (fl_postX B cx xx).
Definition fl_fromX1 (B : asyms) (CTX : list (list Z)) (wfn : Z) (ss : sstate)
(INV : flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : flcx) (xx : flxx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
fl_baseX B CTX wfn cx xx -> fl_EX cx xx E ->
ajournal SEGS B TFLUSH_STK (spZ (c_regs cx)) (fl_FPX cx xx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (2, c_fpos cx) :: frames (c_S cx) ->
INV cx xx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (fl_postX B cx xx).
Definition INV_0X (B : asyms) (kmax : Z) : flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_0 B kmax cx E k ly3 S3 W3 ms3 md3 /\ mo_le MT (c_S cx) S3 0.
Definition INV_B2X (B : asyms) : flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_B2 B cx E k ly3 S3 W3 ms3 md3 /\ ew E 591 = Z_to_bv 64 (ACj6.fl_gen2 cx) /\ mo_le MT (c_S cx) S3 0.
Definition INV_B3X (B : asyms) : flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_B3 B cx E k ly3 S3 W3 ms3 md3 /\ ew E 621 = Z_to_bv 64 (ACj6.fl_gen3 cx) /\ mo_le MT (c_S cx) S3 0.
Lemma fl_EX_havoc : forall cx xx E N vs, (530 <= N)%nat -> fl_EX cx xx E -> fl_EX cx xx (havoc E N vs).
Proof.
intros cx xx E N vs HN (AG & EX & E60 & E516 & E528 & E529 & HEI). unfold fl_EX. rewrite !ew_havoc_old by lia.
split; [|split; [|split; [exact E60 | split; [exact E516 | split; [exact E528 | split; [exact E529 | apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]]]]]]].
- intros n Hn. rewrite !ew_havoc_old by lia. apply AG. exact Hn.
- intros j Hj. rewrite !ew_havoc_old by lia. apply EX. exact Hj.
Qed.
Lemma fl_EX_E : forall cx xx E, fl_EX cx xx E -> fl_E cx E \/ True.
Proof. intros; right; exact I. Qed.
Lemma INV_0X_havoc : forall B kmax cx xx E N vs k ly3 S3 W3 ms3 md3,
INV_0X B kmax cx xx E k ly3 S3 W3 ms3 md3 -> INV_0X B kmax cx xx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
End c.
End b.
End a.
