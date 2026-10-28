(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (IQ OLD NEW lo : Z) (m0 : mem).
Hypothesis AO : apart IQ 40 OLD 40.
Hypothesis AN : apart IQ 40 NEW 40.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + LSPI_DEPTH <= bv_unsigned sp.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis SP63 : bv_unsigned sp < 2 ^ 63.
Hypothesis AOS : apart OLD 40 lo (bv_unsigned sp - lo).
Hypothesis ANS : apart NEW 40 lo (bv_unsigned sp - lo).
Hypothesis AQS : apart IQ 40 lo (bv_unsigned sp - lo).
Hypothesis O0 : 0 < OLD.
Hypothesis O4 : OLD mod 4 = 0.
Hypothesis N0 : 0 < NEW.
Hypothesis N4 : NEW mod 4 = 0.
Hypothesis Q0 : 0 < IQ.
Hypothesis Q4 : IQ mod 4 = 0.
Local Notation usp := (bv_unsigned sp).
Local Notation W := [(lo, usp); (IQ, IQ + 40)].
Local Notation FRAME := [C8 s3; C8 s2; C8 s1; C8 s0].
Local Notation POST := (lsp_interpolate_post IQ lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).

Ltac margin_exit FR ST DONE PREV CUR MU WM MI FRM :=
let C1 := fresh "C1" in let C2 := fresh "C2" in
do 6 zstep; release_frame FR ST (bv_unsigned sp);
chunk_snoc DONE PREV; rewrite f32_snoc in DONE; chunk_uncons CUR as C1; chunk_snoc DONE C1; rewrite f32_snoc in DONE;
chunk_uncons CUR as C2; chunk_snoc DONE C2; rewrite f32_snoc in DONE;
apply evt_done; unfold lsp_interpolate_post;
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact FRM|]; split; [exact ST|];
split; [exact DONE|]; rewrite !length_app; cbn [length]; lia.

Ltac margin_next IH q done pw rest FR ST DONE PREV CUR MU WM MI FRM :=
let C1 := fresh "C1" in
chunk_snoc DONE PREV; rewrite f32_snoc in DONE; chunk_uncons CUR as C1; replace q with (q + 4 + -4) in C1 by lia;
eapply (IH (done ++ [pw]) rest (q + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact DONE | exact C1 | exact CUR ].

#[using="LOW GLO SP63 AQS Q0 Q4"] Lemma margin_loop : forall (k : nat) (done rest : list word) (q off : Z) (pw cw nw : word)
(t0 t1 t2 xs0 xs1 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 7)%nat ->
q = IQ + 4 + 4 * Z.of_nat (length done) -> off = 4 + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -32) -> rw_cells rsegs m (usp + -32) FRAME ->
rw_cells rsegs m IQ (f32 done) -> rw_cells rsegs m (q + -4) (f32 [pw]) -> rw_cells rsegs m q (f32 (cw :: nw :: rest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 36) (Z_to_bv 64 (18446744073709551615 - IQ))
(Z_to_bv 64 q) (Z_to_bv 64 off) a4 a5 a6 a7
xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x28080) fc None m (seg_rom rsegs)).
Proof.
clear AO AN AOS ANS O0 O4 N0 N4.
unfold apart in AQS. unfold LSPI_DEPTH in LOW. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros done rest q off pw cw nw t0 t1 t2 xs0 xs1 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 G fc m
LR LD Hq Hoff FRM MI MU WM ST FR DONE PREV CUR.
-
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
destruct rest; [|cbn in LR; lia]. cbn [length] in LD, BC.
rewrite !f32_cons in CUR. rewrite f32_cons, f32_nil in PREV.
zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep.
if_cases B1.
+ zstep. zstep. if_false_z. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_false_x. margin_exit FR ST DONE PREV CUR MU WM MI FRM.
* zstep. zstep. zstep. zstep. zstep. zstep. if_false_x. margin_exit FR ST DONE PREV CUR MU WM MI FRM.
+ zstep. zstep. zstep. zstep. if_false_z. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_false_x. margin_exit FR ST DONE PREV CUR MU WM MI FRM.
* zstep. zstep. zstep. zstep. zstep. zstep. if_false_x. margin_exit FR ST DONE PREV CUR MU WM MI FRM.
-
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
destruct rest as [|nw' rest]; [cbn in LR; lia|]. cbn [length] in LD, LR, BC.
rewrite !f32_cons in CUR. rewrite f32_cons, f32_nil in PREV.
zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep.
if_cases B1.
+ zstep. zstep. if_false_z. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_true_x. margin_next IH q done pw rest FR ST DONE PREV CUR MU WM MI FRM.
* zstep. zstep. zstep. zstep. zstep. zstep. if_true_x. margin_next IH q done pw rest FR ST DONE PREV CUR MU WM MI FRM.
+ zstep. zstep. zstep. zstep. if_false_z. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_true_x. margin_next IH q done pw rest FR ST DONE PREV CUR MU WM MI FRM.
* zstep. zstep. zstep. zstep. zstep. zstep. if_true_x. margin_next IH q done pw rest FR ST DONE PREV CUR MU WM MI FRM.
Qed.

#[using="LOW GLO SP63 AQS Q0 Q4"] Lemma tail2 : forall (qs : list word) (xa3 t0 t1 t2 xs0 xs1 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -32) -> rw_cells rsegs m (usp + -32) FRAME ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 36) (Z_to_bv 64 9) (Z_to_bv 64 IQ) xa3 a4 a5 a6 a7
xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x28064) fc None m (seg_rom rsegs)).
Proof.
clear AO AN AOS ANS O0 O4 N0 N4.
unfold apart in AQS. unfold LSPI_DEPTH in LOW. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LQ FRM MI MU WM ST FR X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 qs]]]; try (cbn in LQ; lia). cbn [length] in LQ.
rewrite !f32_cons in X.
zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep.
chunk_uncons X as C0. rewrite zb_lxor_ones by lia.
eapply (margin_loop (length qs) [] qs (IQ + 4) 4);
[ reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR
| apply rw_cells_nil; lia
| replace (IQ + 4 + -4) with IQ by lia; exact C0
| exact X ].
Qed.

#[using="LOW GLO SP63 AQS Q0 Q4"] Lemma tail1 : forall (qs : list word) (xa0 xa1 t0 t1 t2 xs0 xs1 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -32) -> rw_cells rsegs m (usp + -32) FRAME ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 xs0 xs1 xa0 xa1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) a4 a5 a6 a7
xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x28014) fc None m (seg_rom rsegs)).
Proof.
clear AO AN AOS ANS O0 O4 N0 N4.
unfold apart in AQS. unfold LSPI_DEPTH in LOW. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LQ FRM MI MU WM ST FR X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|qx qs]]]]]]]]]]]; try (cbn in LQ; lia).
rewrite !f32_cons, f32_nil in X.
zstep. zstep. if_false_z. zstep. zstep. zstep. if_false_z. zstep. zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
if_cases B.
eapply (tail2 [q0; q1; q2; q3; q4; q5; q6; q7; q8; q9]); [ reflexivity | exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | rewrite !f32_cons, f32_nil; exact X ].
- zstep. zstep.
eapply (tail2 [q0; q1; q2; q3; q4; q5; q6; q7; q8; _]); [ reflexivity | exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | rewrite !f32_cons, f32_nil; exact X ].
Qed.

#[using="LOW GLO SP63 AQS Q0 Q4"] Lemma tail0 : forall (qs : list word) (xa0 xa1 t0 t1 t2 xs0 xs1 a4 a5 a7 xs2 xs3 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -32) -> rw_cells rsegs m (usp + -32) FRAME ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 xs0 xs1 xa0 xa1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) a4 a5 (Z_to_bv 64 0) a7
xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x27ffc) fc None m (seg_rom rsegs)).
Proof.
clear AO AN AOS ANS O0 O4 N0 N4.
unfold apart in AQS. unfold LSPI_DEPTH in LOW. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LQ FRM MI MU WM ST FR X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. cbn [length] in LQ.
rewrite f32_cons in X.
zstep. if_false_z. zstep. if_false_z. zstep. zstep. zstep. if_cases B.
eapply (tail1 (q0 :: qs)); [ cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | rewrite f32_cons; exact X ].
- zstep.
eapply (tail1 (_ :: qs)); [ cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | rewrite f32_cons; exact X ].
Qed.

Ltac interp_checks :=
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z;
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z;
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_z.

#[using="AO AN LOW GLO SP63 AOS ANS AQS O0 O4 N0 N4 Q0 Q4"] Lemma interp_loop : forall (k : nat) (done qrest orest nrest : list word) (qi qo qn : Z) (qw ow nw : word)
(t3v xs3 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qrest = k -> length orest = k -> length nrest = k -> (length done + k = 9)%nat ->
qi = IQ + 4 * Z.of_nat (length done) -> qo = OLD + 4 * Z.of_nat (length done) -> qn = NEW + 4 * Z.of_nat (length done) ->
t3v = Z_to_bv 64 (Z.of_nat (S k)) ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -32) -> rw_cells rsegs m (usp + -32) FRAME ->
rw_cells rsegs m IQ (f32 done) -> rw_cells rsegs m qi (f32 (qw :: qrest)) ->
rw_cells rsegs m qo (f32 (ow :: orest)) -> rw_cells rsegs m qn (f32 (nw :: nrest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -32)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 qi) (Z_to_bv 64 qn)
(Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1)
(Z_to_bv 64 qo) xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3v (Z_to_bv 64 qo) (Z_to_bv 64 qn) (Z_to_bv 64 qi))
G (Z_to_bv 64 0x27f8c) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AO, AN, AOS, ANS, AQS. unfold LSPI_DEPTH in LOW. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros done qrest orest nrest qi qo qn qw ow nw t3v xs3 G fc m
LQ LO LN LD Hqi Hqo Hqn Ht3 FRM MI MU WM ST FR DONE X O N; subst t3v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32 in BO; cbn [length] in BO;
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32 in BN; cbn [length] in BN;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
- destruct qrest; [|cbn in LQ; lia]. destruct orest; [|cbn in LO; lia]. destruct nrest; [|cbn in LN; lia]. cbn [length] in LD.
rewrite f32_cons, f32_nil in X. rewrite f32_cons, f32_nil in O. rewrite f32_cons, f32_nil in N.
interp_checks. do 13 zstep. if_false_x.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
eapply (tail0 (done ++ [_])); [ rewrite length_app; cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact DONE ].
- destruct qrest as [|qw' qrest]; [cbn in LQ; lia|]. destruct orest as [|ow' orest]; [cbn in LO; lia|]. destruct nrest as [|nw' nrest]; [cbn in LN; lia|].
cbn [length] in LQ, LO, LN, LD, BX, BO, BN.
rewrite !f32_cons in X. rewrite !f32_cons in O. rewrite !f32_cons in N.
interp_checks. do 13 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1. rewrite f32_snoc in DONE.
chunk_uncons O as O1. chunk_uncons N as N1.
eapply (IH (done ++ [_]) qrest orest nrest (qi + 4) (qo + 4) (qn + 4));
[ lia | lia | lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| f_equal; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact DONE | exact X | exact O | exact N ].
Qed.
End S.

Lemma lsp_interpolate_proof : lsp_interpolate_stmt.
Proof.
intros OLD NEW IQ sub lo os ns qs. intros until m. intros O LO N LN X LQ AO AN SUB -> -> -> -> -> -> MI FRM
ST LOW GLO SP63 AOS ANS AQS O0 O4 N0 N4 Q0 Q4.
pose proof AO as AO'. pose proof AN as AN'. unfold apart in AO', AN'.
pose proof AOS as AOS'. pose proof ANS as ANS'. pose proof AQS as AQS'. unfold apart in AOS', ANS', AQS'.
pose proof LOW as LOW'. unfold LSPI_DEPTH in LOW'. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO'.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32, LO in BO.
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32, LN in BN.
pose proof (munch_refl [(lo, bv_unsigned sp); (IQ, IQ + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. destruct os as [|o0 os]; [cbn in LO; lia|]. destruct ns as [|n0 ns]; [cbn in LN; lia|].
cbn [length] in LQ, LO, LN.
carve_frame 32%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 4%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w0 [|w1 [|w2 [|w3 [|? ?]]]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
zstep. zstep. zstep. zstep. zstep. zstep.
zstep. if_false_x.
do 25 zstep. cond_prep. rewrite Q4.
eapply (interp_loop IQ OLD NEW lo m AO AN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
LOW GLO SP63 AOS ANS AQS O0 O4 N0 N4 Q0 Q4 9%nat [] qs os ns IQ OLD NEW);
[ lia | lia | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; lia | reflexivity
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | apply rw_cells_nil; lia | exact X | exact O | exact N ].
Qed.
