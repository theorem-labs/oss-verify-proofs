(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bs X1c2 X1bn X1cc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ri.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gj X1fl X1ei X1ea X1fr X1gg X1eo.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1en.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof : fwritex_stderr_stmt.
Proof.
unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
destruct st as [buf st].
first [ sf_destruct 11%nat SINK as flags mode tail rest FC FL32 FL8 BUF LEN BHI BGLO | sf_fb; destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO) ]. cbn [fst] in FC, BUF, LEN.
unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ in *.
change X1ff.rsegs with rsegs in *.
destruct SSP as [GOT GUARD]. change X1fd.rsegs with rsegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
assert (LSB : length (zb bs) = length bs) by apply zb_length.
pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
unfold zlength in *.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).

pose proof BUF as BUF0.
assert (BT : B + 80 <= TASK_SIZE) by exact (wr_at_below _ _ _ _ MI (proj2 BUF) ltac:(cbn; lia)).
apply (rw_cells_split_CB rsegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
cbn [mk_CB_cells app] in BUF.
rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
apply (proj1 (X1en.rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
unfold implM, OUT_stderr.
destruct (80 - zlength buf <? zlength bs) eqn:CMP.
-
pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
eapply impl_evt.
{ eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
cbv beta. intros ms1 PO.
first [ sf_destruct 17%nat PO as t0' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 -> MU1 WM1 MI1 ST1 | sf_fb; destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1) ].
unfold file_cells in FC.
transport_after_call rsegs m m1 MU1 WM1.
unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
eapply impl_ebind.
{ eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 250128) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
(wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
try reflexivity.
- exact FC.
- apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
- exact SRC.
- lia.
- exact ST1.
- unfold STDIO_WRITE_DEPTH. lia.
- lia.
- split; [exact GOT | exact GUARD].
- exact MI1.
- lia. - lia.
- unfold got_ssp. lia.
- unfold ssp_guard. lia.
- lia. - lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- lia.
- unfold zlength. lia.
- right. unfold zlength. lia.
- unfold zlength. lia.
- unfold zlength in *. lia.
- intros ->. unfold zlength in *. cbn [length] in *. lia. }
cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
first [ sf_destruct 23%nat PO as t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 -> MU2 WM2 MI2 ST2 FC2 SSP2 -> | sf_fb; destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->) ].
unfold STDIO_WRITE_DEPTH in MU2.
apply impl_ret_ok. cbn [fst snd]. apply evt_done.

pose proof (rw_cells_transport rsegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
pose proof (bytes_at_transport rsegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
unfold out_post, SR. sf_eexists 16%nat. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
split.
{
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((zb buf ++ rest)) | ] | sf_fb; exists flags, mode, tail, (zb buf ++ rest) ]. cbn [fst].
split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
split; [exact BUF2|]. split; [| split; [exact BHI| exact BGLO]].
unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
split; [exact SSP2 | exact SRC2].
-
pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
apply impl_ret_ok. cbn [fst snd].
unfold file_cells in FC.
eapply evt_mono.
{ eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
(Fp := 250128) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
[ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
[exact ST | exact MI].
}
cbv beta. intros ms' PO.
first [ sf_destruct 23%nat PO as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MU2 WM2 MI2 ST2 FC2 DST2 SRC2 | sf_fb; destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2) ].
unfold out_post, SR. sf_eexists 16%nat.
split. { reflexivity. }
split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
assert (GOT2 : rw_cells rsegs m2 245968 [C8 (Z_to_bv 64 448184)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells rsegs m2 448184 [C8 canary]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells rsegs m2 B [CB (length buf) (zb buf)]).
{ eapply (rw_cells_transport rsegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact ((skipn (length (zb bs)) rest)) | ] | sf_fb; exists flags, mode, tail, (skipn (length (zb bs)) rest) ]. cbn [fst].
split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
assert (J : rw_cells rsegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
{ cbn [app]. apply (proj2 (X1en.rw_cells_app rsegs _ _ [_] _)); split; [exact BUFa2|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
split; [| split; [exact BHI| exact BGLO]].
unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed.
