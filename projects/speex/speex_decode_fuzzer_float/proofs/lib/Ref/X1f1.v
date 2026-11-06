(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (IQ OLD NEW : Z) (m0 : mem).
Hypothesis AO : apart IQ 40 OLD 40.
Hypothesis AN : apart IQ 40 NEW 40.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Local Notation POST := (lsp_interpolate_post IQ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).

#[using="Type"] Lemma margin_loop : forall (k : nat) (done rest : list word) (q : Z) (pw cw nw : word)
(t0 t1 t2 xa1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 7)%nat ->
q = IQ + 4 + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch [(IQ, IQ + 40)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m IQ (f32 done) -> rw_cells rsegs m (q + -4) (f32 [pw]) -> rw_cells rsegs m q (f32 (cw :: nw :: rest)) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) xa1 (Z_to_bv 64 (IQ + 36)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x239d0) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros done rest q pw cw nw t0 t1 t2 xa1 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m
LR LD Hq FRM MI MU WM DONE PREV CUR.
-
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
destruct rest; [|cbn in LR; lia]. cbn [length] in LD, BC.
rewrite !f32_cons in CUR. rewrite f32_cons, f32_nil in PREV.
zstep. zstep. zstep. zstep. zstep.
if_cases B1.
+ zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_false_x. zstep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
chunk_uncons CUR as C2. chunk_snoc DONE C2. rewrite f32_snoc in DONE.
apply evt_done; unfold lsp_interpolate_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact DONE|]. rewrite !length_app; cbn [length]; lia.
* zstep. zstep. zstep. zstep. zstep. zstep. if_false_x. zstep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
chunk_uncons CUR as C2. chunk_snoc DONE C2. rewrite f32_snoc in DONE.
apply evt_done; unfold lsp_interpolate_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact DONE|]. rewrite !length_app; cbn [length]; lia.
+ zstep. zstep. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_false_x. zstep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
chunk_uncons CUR as C2. chunk_snoc DONE C2. rewrite f32_snoc in DONE.
apply evt_done; unfold lsp_interpolate_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact DONE|]. rewrite !length_app; cbn [length]; lia.
* zstep. zstep. zstep. zstep. zstep. zstep. if_false_x. zstep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
chunk_uncons CUR as C2. chunk_snoc DONE C2. rewrite f32_snoc in DONE.
apply evt_done; unfold lsp_interpolate_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact DONE|]. rewrite !length_app; cbn [length]; lia.
-
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
destruct rest as [|nw' rest]; [cbn in LR; lia|]. cbn [length] in LD, LR, BC.
rewrite !f32_cons in CUR. rewrite f32_cons, f32_nil in PREV.
zstep. zstep. zstep. zstep. zstep.
if_cases B1.
+ zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_true_x.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. replace q with (q + 4 + -4) in C1 by lia.
eapply (IH (done ++ [pw]) rest (q + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact DONE | exact C1 | exact CUR ].
* zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. replace q with (q + 4 + -4) in C1 by lia.
eapply (IH (done ++ [pw]) rest (q + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact DONE | exact C1 | exact CUR ].
+ zstep. zstep. zstep. zstep. zstep. zstep. if_cases B2.
* zstep. zstep. if_true_x.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. replace q with (q + 4 + -4) in C1 by lia.
eapply (IH (done ++ [pw]) rest (q + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact DONE | exact C1 | exact CUR ].
* zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE. chunk_uncons CUR as C1. replace q with (q + 4 + -4) in C1 by lia.
eapply (IH (done ++ [pw]) rest (q + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact DONE | exact C1 | exact CUR ].
Qed.

#[using="Type"] Lemma tail2 : forall (qs : list word) (xa0 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch [(IQ, IQ + 40)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 (Z_to_bv 64 9) (Z_to_bv 64 IQ) (Z_to_bv 64 10) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x239ac) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros LQ FRM MI MU WM X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 qs]]]; try (cbn in LQ; lia). cbn [length] in LQ.
rewrite !f32_cons in X.
zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
chunk_uncons X as C0.
eapply (margin_loop (length qs) [] qs (IQ + 4));
[ reflexivity | cbn [length]; lia | cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM
| apply rw_cells_nil; lia
| replace (IQ + 4 + -4) with IQ by lia; exact C0
| exact X ].
Qed.

#[using="Type"] Lemma tail1 : forall (qs : list word) (xa0 xa1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch [(IQ, IQ + 40)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x23978) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros LQ FRM MI MU WM X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|qx qs]]]]]]]]]]]; try (cbn in LQ; lia).
rewrite !f32_cons, f32_nil in X.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
if_cases B.
eapply (tail2 [q0; q1; q2; q3; q4; q5; q6; q7; q8; q9]); [ reflexivity | exact FRM | exact MI | exact MU | exact WM | rewrite !f32_cons, f32_nil; exact X ].
- zstep. zstep.
eapply (tail2 [q0; q1; q2; q3; q4; q5; q6; q7; q8; _]); [ reflexivity | exact FRM | exact MI | exact MU | exact WM | rewrite !f32_cons, f32_nil; exact X ].
Qed.

#[using="Type"] Lemma tail0 : forall (qs : list word) (xa0 xa1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qs = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch [(IQ, IQ + 40)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m IQ (f32 qs) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 (Z_to_bv 64 IQ) (Z_to_bv 64 10) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x23968) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros LQ FRM MI MU WM X.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. cbn [length] in LQ.
rewrite f32_cons in X.
zstep. zstep. zstep. if_cases B.
eapply (tail1 (q0 :: qs)); [ cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | rewrite f32_cons; exact X ].
- zstep.
eapply (tail1 (_ :: qs)); [ cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | rewrite f32_cons; exact X ].
Qed.

#[using="AO AN"] Lemma interp_loop : forall (k : nat) (done qrest orest nrest : list word) (qi qo qn : Z) (qw ow nw : word)
(t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length qrest = k -> length orest = k -> length nrest = k -> (length done + k = 9)%nat ->
qi = IQ + 4 * Z.of_nat (length done) -> qo = OLD + 4 * Z.of_nat (length done) -> qn = NEW + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch [(IQ, IQ + 40)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m IQ (f32 done) -> rw_cells rsegs m qi (f32 (qw :: qrest)) ->
rw_cells rsegs m qo (f32 (ow :: orest)) -> rw_cells rsegs m qn (f32 (nw :: nrest)) ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 qo) (Z_to_bv 64 qn) (Z_to_bv 64 IQ) (Z_to_bv 64 10) (Z_to_bv 64 (IQ + 40)) (Z_to_bv 64 qi) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x23944) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AO, AN.
induction k as [|k IH]; intros done qrest orest nrest qi qo qn qw ow nw t0 t1 t2 a6 a7 t3 t4 t5 t6 G fc m
LQ LO LN LD Hqi Hqo Hqn FRM MI MU WM DONE X O N;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32 in BO; cbn [length] in BO;
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32 in BN; cbn [length] in BN;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
- destruct qrest; [|cbn in LQ; lia]. destruct orest; [|cbn in LO; lia]. destruct nrest; [|cbn in LN; lia]. cbn [length] in LD.
rewrite f32_cons, f32_nil in X. rewrite f32_cons, f32_nil in O. rewrite f32_cons, f32_nil in N.
do 9 zstep. if_false_x.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
eapply (tail0 (done ++ [_])); [ rewrite length_app; cbn [length]; lia | exact FRM | exact MI | exact MU | exact WM | exact DONE ].
- destruct qrest as [|qw' qrest]; [cbn in LQ; lia|]. destruct orest as [|ow' orest]; [cbn in LO; lia|]. destruct nrest as [|nw' nrest]; [cbn in LN; lia|].
cbn [length] in LQ, LO, LN, LD, BX, BO, BN.
rewrite !f32_cons in X. rewrite !f32_cons in O. rewrite !f32_cons in N.
do 9 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1. rewrite f32_snoc in DONE.
chunk_uncons O as O1. chunk_uncons N as N1.
eapply (IH (done ++ [_]) qrest orest nrest (qi + 4) (qo + 4) (qn + 4));
[ lia | lia | lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact DONE | exact X | exact O | exact N ].
Qed.
End S.

Lemma lsp_interpolate_proof : lsp_interpolate_stmt.
Proof.
intros OLD NEW IQ sub os ns qs. intros until m. intros O LO N LN X LQ AO AN SUB -> -> -> -> -> -> MI FRM.
pose proof AO as AO'. pose proof AN as AN'. unfold apart in AO', AN'.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32, LO in BO.
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32, LN in BN.
pose proof (munch_refl [(IQ, IQ + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct qs as [|q0 qs]; [cbn in LQ; lia|]. destruct os as [|o0 os]; [cbn in LO; lia|]. destruct ns as [|n0 ns]; [cbn in LN; lia|].
cbn [length] in LQ, LO, LN.
zstep. if_false_x.
do 10 zstep.
eapply (interp_loop IQ OLD NEW m AO AN ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 9%nat [] qs os ns IQ OLD NEW);
[ lia | lia | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | apply rw_cells_nil; lia | exact X | exact O | exact N ].
Qed.
