(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mr X1ms X1mh.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Section Seg.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X). Local Notation canary := (x_canary X). Local Notation st := (x_st X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).
Local Notation mo := (sbd_mode (x_s X)).

Ltac close_ctxE EFS MU := unfold sbctx, sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; rewrite ?EFS; repeat match goal with |- _ /\ _ => split end; first [close_goal MU | congruence].

Definition isv_post (PS PD : Z) (fr : sframe) (n : nat) (ss : list word)
(xra xsp t0 t1 t2 xs0 xs1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (m' : mem) (dws : list word) (c0 c1 c2 c3 c4 c5 c6 c7 : word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 c0 c1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x2f92c) fc None m' (seg_rom rsegs)
/\ munch [(PD, PD + 8 * Z.of_nat n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = (2 * n)%nat /\ rw_cells rsegs m' PS (f32 ss) /\ length ss = n
/\ rw_cells rsegs m' (bv_unsigned xs0 + -384) (sframe_cells fr).

#[using="Type"] Lemma isv_loop : forall (PS PD K : Z) (fr : sframe) (n : nat)
(xra xsp t0 t1 t2 xs0 xs1 a1v a2v a3v a4v a7v s2 s3 s4 s5 s6 s10 s11 t3 t4 t5 t6 : word) (mN : mem)
srest rest sdone done (q r : Z) (a0v a5v a6v : word) F fc m,
(length sdone + length srest = n)%nat -> length done = (2 * length sdone)%nat -> length rest = (2 * length srest)%nat -> (1 <= length srest)%nat ->
q = PD + 8 * Z.of_nat (length sdone) -> r = PS + 4 * Z.of_nat (length sdone) -> a0v = Z_to_bv 64 (4 * Z.of_nat (length sdone)) ->
a5v = Z_to_bv 64 q -> a6v = Z_to_bv 64 q ->
0 < PD -> PD mod 4 = 0 -> PD + 8 * Z.of_nat n < 2^64 -> 0 <= PS -> PS + 4 * Z.of_nat n < 2^64 ->
4 * Z.of_nat n <= K < 2^32 -> 384 <= bv_unsigned xs0 ->
f_216 fr = Z_to_bv 64 4294967296 ->
apart PD (8 * Z.of_nat n) PS (4 * Z.of_nat n) ->
apart PD (8 * Z.of_nat n) (bv_unsigned xs0 + -384) (Z.of_nat (cells_size (sframe_cells fr))) ->
a1v = Z_to_bv 64 (18446744073709551615 - PS) -> a2v = Z_to_bv 64 1 -> a3v = Z_to_bv 64 1 -> a4v = Z_to_bv 64 (4 * Z.of_nat n) ->
mem_inv rsegs m -> munch [(PD, PD + 8 * Z.of_nat n)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m (bv_unsigned xs0 + -384) (sframe_cells fr) ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m q (f32 rest) ->
rw_cells rsegs m PS (f32 sdone) -> rw_cells rsegs m r (f32 srest) ->
evt rsegs (isv_post PS PD fr n (sdone ++ srest) xra xsp t0 t1 t2 xs0 xs1 s2 s3 s4 s5 s6
(Z_to_bv 64 K) (Z_to_bv 64 PS) (Z_to_bv 64 PD) s10 s11 t3 t4 t5 t6 fc mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0v a1v a2v a3v a4v a5v a6v a7v
s2 s3 s4 s5 s6 (Z_to_bv 64 K) (Z_to_bv 64 PS) (Z_to_bv 64 PD) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2f8ec) fc None m (seg_rom rsegs)).
Proof.
intros PS PD K fr n xra xsp t0 t1 t2 xs0 xs1 a1v a2v a3v a4v a7v s2 s3 s4 s5 s6 s10 s11 t3 t4 t5 t6 mN srest.
revert a1v a2v a3v a4v a7v.
induction srest as [|x srest IHs]; intros a1v a2v a3v a4v a7v rest sdone done q r a0v a5v a6v F fc m LN Ld Lr L1 Hq Hr Ha0 Ha5 Ha6 P0 P4 P64 S0 S64 HK SP0 F216 AP APF
-> -> -> -> MI MU WM FRM DONE YR SDONE XR; [cbn in L1; lia|]. subst a0v a5v a6v q r.
destruct rest as [|y1 [|y2 rest']]; try (cbn in Lr; lia). cbn [length] in LN, Ld, Lr, L1.
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX.
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS.
unfold apart in AP, APF. unfold sframe_cells in APF, FRM. cbn [cells_size csize Nat.add] in APF.
rewrite !f32_cons in XR. rewrite !f32_cons in YR.
destruct srest as [|x' srest'].
- destruct rest' as [|? ?]; [| cbn in Lr; lia]. rewrite f32_nil in XR, YR. cbn [length] in *.
remember (PD + 8 * Z.of_nat (length sdone)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. if_false_z. zstep. rewrite F216. zstep. if_false_z. zstep. if_false_z.
zstep. zstep. zstep. if_false_z. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length sdone)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. zstep. zstep. if_false_x.
subst qq rr.
unfold isv_post, sframe_cells.
chunk_snoc SDONE XR. apply f32_snoc1' in SDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. chunk_snoc DONE YR. rewrite <- app_assoc in DONE. cbn [app] in DONE.
lazymatch type of DONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in DONE by (rewrite f32_app; reflexivity) end.
finish.
all: try exact DONE.
all: try (rewrite length_app; cbn [length]; lia).
- destruct rest' as [|y3 [|y4 rest'']]; try (cbn in Lr; lia). cbn [length] in *.
remember (PD + 8 * Z.of_nat (length sdone)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. if_false_z. zstep. rewrite F216. zstep. if_false_z. zstep. if_false_z.
zstep. zstep. zstep. if_false_z. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length sdone)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
subst qq rr.
chunk_uncons XR as X1. chunk_snoc SDONE X1. apply f32_snoc1' in SDONE.
chunk_uncons YR as Y1. chunk_uncons YR as Y2. chunk_snoc DONE Y1. chunk_snoc DONE Y2. rewrite <- app_assoc in DONE. cbn [app] in DONE.
lazymatch type of DONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in DONE by (rewrite f32_app; reflexivity) end.
replace (sdone ++ x :: x' :: srest') with ((sdone ++ [x]) ++ x' :: srest') by (rewrite <- app_assoc; reflexivity).
lazymatch type of DONE with rw_cells _ _ _ (f32 (_ ++ [?u; ?v])) =>
eapply (IHs _ _ _ _ _ (y3 :: y4 :: rest'') (sdone ++ [x]) (done ++ [u; v]) (PD + 8 * Z.of_nat (length (sdone ++ [x]))) (PS + 4 * Z.of_nat (length (sdone ++ [x])))) end.
all: try (f_equal; rewrite ?length_app; cbn [length]; lia).
all: try eassumption.
all: try (unfold sframe_cells; exact FRM).
all: try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
all: try (unfold apart, sframe_cells; rewrite ?length_app; cbn [length cells_size csize Nat.add] in *; lia).
all: try (rewrite ?length_app; cbn [length]; rewrite ?f32_cons; first [exact_at XR | exact_at YR]).
Qed.

Definition cp1_post (SB PS PD : Z) (s : sbd_state bptr) (aa : sb_addrs) (OUTv : Z) (n : nat) (ss : list word)
(xra xsp t0 t1 t2 xs0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (m' : mem) (dws : list word) (c0 c2 c3 c4 c5 c6 c7 : word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 (Z_to_bv 64 SB) c0 a1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x2f9ac) fc None m' (seg_rom rsegs)
/\ munch [(PD, PD + 4 * Z.of_nat n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = n /\ rw_cells rsegs m' PS (f32 ss) /\ length ss = n
/\ rw_cells rsegs m' (SB + 40) (sbp_ptrs s aa OUTv).

#[using="Type"] Lemma cp1_loop : forall (SB PS PD K OUTv : Z) (s : sbd_state bptr) (aa : sb_addrs) (n : nat)
(xra xsp t0 t1 t2 xs0 a1 a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word) (mN : mem)
rest srest sdone done (q r : Z) (a0v : word) F fc m,
(length done + length rest = n)%nat -> length srest = length rest -> length sdone = length done -> (1 <= length rest)%nat ->
q = PD + 4 * Z.of_nat (length done) -> r = PS + 4 * Z.of_nat (length done) -> a0v = Z_to_bv 64 (4 * Z.of_nat (length done)) ->
PD = a_exc aa -> 0 < PD -> PD mod 4 = 0 -> PD + 4 * Z.of_nat n < 2^64 -> 0 <= PS -> PS + 4 * Z.of_nat n < 2^64 ->
4 * Z.of_nat n <= K < 2^64 -> 0 <= SB -> SB + 40 + Z.of_nat (cells_size (sbp_ptrs s aa OUTv)) <= 2^64 ->
apart PD (4 * Z.of_nat n) PS (4 * Z.of_nat n) ->
apart PD (4 * Z.of_nat n) (SB + 40) (Z.of_nat (cells_size (sbp_ptrs s aa OUTv))) ->
a2v = Z_to_bv 64 (18446744073709551615 - PS) -> a3v = Z_to_bv 64 (4 * Z.of_nat n) ->
mem_inv rsegs m -> munch [(PD, PD + 4 * Z.of_nat n)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m (SB + 40) (sbp_ptrs s aa OUTv) ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m q (f32 rest) ->
rw_cells rsegs m PS (f32 sdone) -> rw_cells rsegs m r (f32 srest) ->
evt rsegs (cp1_post SB PS PD s aa OUTv n (sdone ++ srest) xra xsp t0 t1 t2 xs0 a1 s2 s3 s4 s5 s6
(Z_to_bv 64 K) (Z_to_bv 64 PS) s9 s10 s11 t3 t4 t5 t6 fc mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 (Z_to_bv 64 SB) a0v a1 a2v a3v a4v a5v a6v a7v
s2 s3 s4 s5 s6 (Z_to_bv 64 K) (Z_to_bv 64 PS) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2f964) fc None m (seg_rom rsegs)).
Proof.
intros SB PS PD K OUTv s aa n xra xsp t0 t1 t2 xs0 a1 a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 mN rest.
revert a4v a5v a6v a7v.
induction rest as [|y rest IHr]; intros a4v a5v a6v a7v srest sdone done q r a0v F fc m LN Ls Lsd L1 Hq Hr Ha0 HPD P0 P4 P64 S0 S64 HK SB0 SB64 AP APS
-> -> MI MU WM PTRS DONE YR SDONE XR; [cbn in L1; lia|]. subst a0v q r.
destruct srest as [|x srest']; [cbn in Ls; lia|]. cbn [length] in LN, Ls, L1.
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX.
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS.
unfold apart in AP, APS. unfold sbp_ptrs in APS, SB64, PTRS. cbn [cells_size csize Nat.add] in APS, SB64. rewrite !f32_cons in XR. rewrite !f32_cons in YR.
assert (AL : (4 * Z.of_nat (length done) + PD) mod 4 = 0) by (rewrite Z.add_comm, Z.add_mod, P4 by lia; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
subst PD.
destruct rest as [|y' rest'].
- destruct srest'; [| cbn in Ls; lia]. rewrite f32_nil in XR, YR. cbn [length] in *.
zstep. if_false_z. zstep. if_false_z. zstep. zstep.
remember (a_exc aa + 4 * Z.of_nat (length done)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. zstep. zstep. zstep. if_false_z.
zstep. if_false_z. zstep. zstep. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length done)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. if_false_x.
subst qq rr.
unfold cp1_post.
chunk_snoc SDONE XR. apply f32_snoc1' in SDONE.
chunk_snoc DONE YR. apply f32_snoc1' in DONE.
finish.
all: try exact DONE.
all: try (rewrite length_app; cbn [length]; lia).
- destruct srest' as [|x' srest'']; [cbn in Ls; lia|]. cbn [length] in *.
zstep. if_false_z. zstep. if_false_z. zstep. zstep.
remember (a_exc aa + 4 * Z.of_nat (length done)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. zstep. zstep. zstep. if_false_z.
zstep. if_false_z. zstep. zstep. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length done)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. if_true_x.
subst qq rr.
chunk_uncons XR as X1. chunk_snoc SDONE X1. apply f32_snoc1' in SDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. apply f32_snoc1' in DONE.
replace (sdone ++ x :: x' :: srest'') with ((sdone ++ [x]) ++ x' :: srest'') by (rewrite <- app_assoc; reflexivity).
lazymatch type of DONE with rw_cells _ _ _ (f32 (_ ++ [?v])) =>
eapply (IHr _ _ _ _ (x' :: srest'') (sdone ++ [x]) (done ++ [v]) (a_exc aa + 4 * Z.of_nat (length (done ++ [v]))) (PS + 4 * Z.of_nat (length (done ++ [v])))) end.
all: try (f_equal; rewrite ?length_app; cbn [length]; lia).
all: try eassumption.
all: try (unfold sbp_ptrs; exact PTRS).
all: try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
all: try (unfold apart, sbp_ptrs; rewrite ?length_app; cbn [length cells_size csize Nat.add] in *; lia).
all: try (rewrite ?length_app; cbn [length]; rewrite ?f32_cons; first [exact_at XR | exact_at YR]).
Qed.

Definition cp2_post (SB PS PD : Z) (s : sbd_state bptr) (aa : sb_addrs) (OUTv : Z) (n : nat) (ss : list word)
(xra xsp t0 t1 t2 xs0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (m' : mem) (dws : list word) (c0 c2 c3 c4 c5 c6 c7 : word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 (Z_to_bv 64 SB) c0 a1 c2 c3 c4 c5 c6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x2fa04) fc None m' (seg_rom rsegs)
/\ munch [(PD, PD + 4 * Z.of_nat n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = n /\ rw_cells rsegs m' PS (f32 ss) /\ length ss = n
/\ rw_cells rsegs m' (SB + 40) (sbp_ptrs s aa OUTv).

#[using="Type"] Lemma cp2_loop : forall (SB PS PD K OUTv : Z) (s : sbd_state bptr) (aa : sb_addrs) (n : nat)
(xra xsp t1 t2 xs0 a1 a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word) (mN : mem)
rest srest sdone done (q r : Z) (a0v : word) F fc m,
(length done + length rest = n)%nat -> length srest = length rest -> length sdone = length done -> (1 <= length rest)%nat ->
q = PD + 4 * Z.of_nat (length done) -> r = PS + 4 * Z.of_nat (length done) -> a0v = Z_to_bv 64 (4 * Z.of_nat (length done)) ->
PD = a_iq aa -> 0 < PD -> PD mod 4 = 0 -> PD + 4 * Z.of_nat n < 2^64 -> 0 <= PS -> PS + 4 * Z.of_nat n < 2^64 ->
4 * Z.of_nat n <= K < 2^64 -> 0 <= SB -> SB + 40 + Z.of_nat (cells_size (sbp_ptrs s aa OUTv)) <= 2^64 ->
apart PD (4 * Z.of_nat n) PS (4 * Z.of_nat n) ->
apart PD (4 * Z.of_nat n) (SB + 40) (Z.of_nat (cells_size (sbp_ptrs s aa OUTv))) ->
a2v = Z_to_bv 64 (4 * Z.of_nat n) ->
mem_inv rsegs m -> munch [(PD, PD + 4 * Z.of_nat n)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m (SB + 40) (sbp_ptrs s aa OUTv) ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m q (f32 rest) ->
rw_cells rsegs m PS (f32 sdone) -> rw_cells rsegs m r (f32 srest) ->
evt rsegs (cp2_post SB PS PD s aa OUTv n (sdone ++ srest) xra xsp (Z_to_bv 64 K) t1 t2 xs0 a1 s2 s3 s4 s5
(Z_to_bv 64 (18446744073709551615 - PS)) s7 s8 s9 (Z_to_bv 64 PS) s11 t3 t4 t5 t6 fc mN)
(MS (mkR xra xsp gp tp (Z_to_bv 64 K) t1 t2 xs0 (Z_to_bv 64 SB) a0v a1 a2v a3v a4v a5v a6v a7v
s2 s3 s4 s5 (Z_to_bv 64 (18446744073709551615 - PS)) s7 s8 s9 (Z_to_bv 64 PS) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2f9bc) fc None m (seg_rom rsegs)).
Proof.
intros SB PS PD K OUTv s aa n xra xsp t1 t2 xs0 a1 a2v a3v a4v a5v a6v a7v s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 mN rest.
revert a3v a4v a5v a6v a7v.
induction rest as [|y rest IHr]; intros a3v a4v a5v a6v a7v srest sdone done q r a0v F fc m LN Ls Lsd L1 Hq Hr Ha0 HPD P0 P4 P64 S0 S64 HK SB0 SB64 AP APS
-> MI MU WM PTRS DONE YR SDONE XR; [cbn in L1; lia|]. subst a0v q r.
destruct srest as [|x srest']; [cbn in Ls; lia|]. cbn [length] in LN, Ls, L1.
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX.
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS.
unfold apart in AP, APS. unfold sbp_ptrs in APS, SB64, PTRS. cbn [cells_size csize Nat.add] in APS, SB64. rewrite !f32_cons in XR. rewrite !f32_cons in YR.
assert (AL : (4 * Z.of_nat (length done) + PD) mod 4 = 0) by (rewrite Z.add_comm, Z.add_mod, P4 by lia; rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
subst PD.
destruct rest as [|y' rest'].
- destruct srest'; [| cbn in Ls; lia]. rewrite f32_nil in XR, YR. cbn [length] in *.
zstep. if_false_z. zstep. if_false_z. zstep. zstep.
remember (a_iq aa + 4 * Z.of_nat (length done)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. zstep. zstep. zstep. if_false_z.
zstep. if_false_z. zstep. zstep. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length done)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. if_false_x.
subst qq rr.
unfold cp2_post.
chunk_snoc SDONE XR. apply f32_snoc1' in SDONE.
chunk_snoc DONE YR. apply f32_snoc1' in DONE.
finish.
all: try exact DONE.
all: try (rewrite length_app; cbn [length]; lia).
- destruct srest' as [|x' srest'']; [cbn in Ls; lia|]. cbn [length] in *.
zstep. if_false_z. zstep. if_false_z. zstep. zstep.
remember (a_iq aa + 4 * Z.of_nat (length done)) as qq eqn:Hqq in *.
zstep. if_false_z. zstep. zstep. zstep. zstep. if_false_z.
zstep. if_false_z. zstep. zstep. zstep. if_false_z.
zstep. remember (PS + 4 * Z.of_nat (length done)) as rr eqn:Hrr in *.
zstep. zstep. zstep. zstep. if_true_x.
subst qq rr.
chunk_uncons XR as X1. chunk_snoc SDONE X1. apply f32_snoc1' in SDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. apply f32_snoc1' in DONE.
replace (sdone ++ x :: x' :: srest'') with ((sdone ++ [x]) ++ x' :: srest'') by (rewrite <- app_assoc; reflexivity).
lazymatch type of DONE with rw_cells _ _ _ (f32 (_ ++ [?v])) =>
eapply (IHr _ _ _ _ _ (x' :: srest'') (sdone ++ [x]) (done ++ [v]) (a_iq aa + 4 * Z.of_nat (length (done ++ [v]))) (PS + 4 * Z.of_nat (length (done ++ [v])))) end.
all: try (f_equal; rewrite ?length_app; cbn [length]; lia).
all: try eassumption.
all: try (unfold sbp_ptrs; exact PTRS).
all: try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
all: try (unfold apart, sbp_ptrs; rewrite ?length_app; cbn [length cells_size csize Nat.add] in *; lia).
all: try (rewrite ?length_app; cbn [length]; rewrite ?f32_cons; first [exact_at XR | exact_at YR]).
Qed.

Definition at_T (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -512)) gp tp (Z_to_bv 64 OUT) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2fab8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -512) /\ frame_at X m fr
/\ f_0 fr = Z_to_bv 64 (usp + -384) /\ f_144 fr = Z_to_bv 64 (18446744073709551615 - (usp + -448)) /\ f_152 fr = Z_to_bv 64 32
/\ f_176 fr = Z_to_bv 64 (usp + -448) /\ f_184 fr = Z_to_bv 64 0 /\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -512) (f32 vak) /\ length vak = 8%nat.

Definition QL3 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => (sub < 3 /\ at_L X low dtx s1 r (sub + 1) b ms) \/ (sub = 3 /\ at_T low dtx s1 b ms).

#[using="RCEIL k IH"] Lemma sbL3_40 : FS = 40 -> forall low dtx s1 r sub b ms, at_L2_40 X low dtx s1 r sub b ms -> evt rsegs (QL3 low dtx s1 r sub b) ms.
Proof.
intros EFS low dtx s1 r sub b ms AT.
first [ sf_destruct 46%nat AT as Fx fc m kk xra xa0 xs2 xs3 xs4 xs9 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F136e F168e F192e F200e SAT Hsub Exs9 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs2 & xs3 & xs4 & xs9 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F136e & F168e & F192e & F200e & SAT & Hsub & Exs9 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 25%nat sfP_ as F0e F8e F16e F24e F32e F40e F56e F64e F72e F80e F88e F96e F104e F112e F120e F128e F144e F152e F160e F176e F184e F208e F216e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F56e & F64e & F72e & F80e & F88e & F96e & F104e & F112e & F120e & F128e & F144e & F152e & F160e & F176e & F184e & F208e & F216e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
pose proof (ih_range _ _ IH) as RNG.
assert (RBA : 0 < a_exc a /\ a_exc a mod 16 = 0 /\ 0 < a_iq a /\ a_iq a mod 16 = 0 /\ 0 < a_msp a /\ a_msp a mod 16 = 0 /\ 0 < a_er a /\ a_er a mod 16 = 0).
{ pose proof (RNG (sbd_excBuf s0, a_exc a, 4 * FS) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R3.
pose proof (RNG (sbd_interp_qlpc s0, a_iq a, 32) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R5.
pose proof (RNG (sbd_exc_rms s0, a_er a, 16) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R7.
pose proof (RNG (sbd_mem_sp s0, a_msp a, 64) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R8.
unfold rblock_range in R3, R5, R7, R8. cbn [blk_addr blk_size fst snd] in R3, R5, R7, R8. lia. }
destruct RBA as (Pexc & Aexc & Piq & Aiq & Pmsp & Amsp & Per & Aer).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-672) ltac:(lia)) as USP672.
pose proof (USPk _ _ IH (-512) ltac:(lia)) as USP512.
pose proof (ih_isave _ _ IH) as KK. rewrite EFS in KK.

zstep. unfold sb_isave_ptr. rewrite Eis.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(OUT, OUT + 8000)] mm) as MUJ; pose proof (wmono_refl rsegs mm) as WMJ end.
lazymatch type of MUJ with munch _ ?MMM _ =>
lazymatch goal with |- evt _ _ (MS (mkR ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 _ _ _ _ _ _ _ _ ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30) _ _ ?fc0 _ _ _) =>
eapply (evt_cut rsegs (fun ms1 => exists (Fx1 : bvmap 5 word) (m1 : mem) (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word) (ows1 : list word),
ms1 = MS (mkR r0 r1 r2 r3 r4 r5 r6 r7 r8 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 r17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30)
Fx1 (Z_to_bv 64 0x2f92c) fc0 None m1 (seg_rom rsegs)
/\ mem_inv rsegs m1 /\ munch [(OUT, OUT + 8000)] MMM m1 /\ wmono rsegs MMM m1
/\ rw_cells rsegs m1 OUT (f32 ows1) /\ length ows1 = 2000%nat)) end end.
{ destruct (sbd_innov_save s0) as [kk0|] eqn:EISV.
- subst kk0. subst xs9. change (OUT + 4 * (8 * 40)) with (OUT + 1280).
zstep. if_false_x.
zstep. zstep. rewrite Efs, (sx32_lit 40) by lia. rewrite (lts_zero_lit 40) by lia. if_false_x.
do 9 zstep. rewrite ?zb_lxor_ones by lia.
pose proof (ih_out4 _ _ IH) as O4.
pose proof (f32_split rsegs _ _ ows (Z.to_nat (320 + 80 * sub)) ltac:(rewrite Lows; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (320 + 80 * sub)) ows) 80%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XO2a XO3]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub)) + 4 * Z.of_nat 80%nat) with (OUT + 1280 + 320 * sub + 320) in XO3 by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 1280 + 320 * sub) in XO2a by lia.
set (owsA := firstn (Z.to_nat (320 + 80 * sub)) ows) in *.
assert (LA : Z.of_nat (length owsA) = 320 + 80 * sub) by (subst owsA; rewrite length_firstn, Lows; lia).
set (owsB := firstn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows)) in *.
assert (LB : length owsB = 80%nat) by (subst owsB; rewrite length_firstn, length_skipn, Lows; lia).
set (owsC := skipn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows)) in *.
assert (LC : Z.of_nat (length owsC) = 2000 - 80 - (320 + 80 * sub)) by (subst owsC; rewrite !length_skipn, Lows; lia).
clearbody owsA owsB owsC. clear XO.
assert (ISV4 : (OUT + 1280 + 320 * sub) mod 4 = 0) by (Z.to_euclidean_division_equations; lia).
replace (0 <? OUT + 1280 + 320 * sub) with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.land (OUT + 1280 + 320 * sub) 3) with 0 by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact ISV4).
remember (OUT + 1280 + 320 * sub) as ISV eqn:EISVA.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (isv_loop (usp + -672) ISV 160 fr 40%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc vexc owsB [] [] ISV (usp + -672));
[ cbn [length]; lia | reflexivity | rewrite LB, Lvexc; reflexivity | lia
| cbn [length]; lia | cbn [length]; lia | reflexivity | reflexivity | reflexivity
| subst ISV; lia | exact ISV4 | subst ISV; lia | lia | lia | lia | lia | exact F216e
| subst ISV; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite cells_size_sframe; subst ISV; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | apply munch_refl | apply wmono_refl
| unfold sframe_cells; exact FL
| rewrite f32_nil; apply rw_cells_nil; subst ISV; lia | exact_at XO2a
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC | ] end.

cbv beta. try clear XO2a. clear LB. name_post. try rename STc into ST. try rename FRMc into FRM.
cbn [app] in *.
match goal with H : rw_cells _ _ ISV (f32 ?w), L : length ?w = _ |- _ => rename H into XO2; rename L into LB2; rename w into owsB2 end.
subst ISV.
pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(replace (OUT + 4 * Z.of_nat (length owsA)) with (OUT + 1280 + 320 * sub) by lia; exact XO2)) as XO12.
pose proof (f32_join rsegs _ _ _ _ XO12 ltac:(rewrite length_app, LB2; replace (OUT + 4 * Z.of_nat (length owsA + (2 * 40%nat))) with (OUT + 1280 + 320 * sub + 320) by lia; exact XO3)) as XO.
clear XO1 XO12 XO2 XO3.
assert (LowsN : length ((owsA ++ owsB2) ++ owsC) = 2000%nat) by (rewrite !length_app, LB2; lia).
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, ((owsA ++ owsB2) ++ owsC).
split; [reflexivity|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO| exact LowsN].
- zstep. if_true_x.
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, ows.
split; [reflexivity|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO| exact Lows]. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 16%nat sfH_ as Fx1 m1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ows1 -> MI1 MUJ' WMJ' XO1 Lows1 | sf_fb; destruct sfH_ as (Fx1 & m1 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ows1 & -> & MI1 & MUJ' & WMJ' & XO1 & Lows1) ].
clear XO Lows. lazymatch type of MUJ' with munch _ ?ma ?mb => transport_after_call rsegs ma mb MUJ' WMJ' end.
clear MUJ' WMJ' MUJ WMJ. try clear MI. rename MI1 into MI. rename XO1 into XO. rename Lows1 into Lows. rename ows1 into ows'.


pose proof (ih_out4 _ _ IH) as O4.
zstep. rewrite Efs, (sx32_lit 40) by lia. zstep. rewrite Ilpc1, (sx32_lit 8) by lia.
zstep. zstep. zstep. zstep. rewrite F168e. zstep. rewrite F184e. zstep.
pose proof (f32_split rsegs _ _ ows' (Z.to_nat (160 + 40 * sub)) ltac:(rewrite Lows; lia) XO) as [XA XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (160 + 40 * sub)) ows') 40%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [YS XC]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (160 + 40 * sub)) + 4 * Z.of_nat 40%nat) with (OUT + 640 + 160 * sub + 160) in XC by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (160 + 40 * sub))) with (OUT + 640 + 160 * sub) in YS by lia.
set (oA := firstn (Z.to_nat (160 + 40 * sub)) ows') in *.
assert (LoA : Z.of_nat (length oA) = 160 + 40 * sub) by (subst oA; rewrite length_firstn, Lows; lia).
set (ys := firstn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows')) in *.
assert (Lys : length ys = 40%nat) by (subst ys; rewrite length_firstn, length_skipn, Lows; lia).
set (oC := skipn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows')) in *.
assert (LoC : Z.of_nat (length oC) = 2000 - 40 - (160 + 40 * sub)) by (subst oC; rewrite !length_skipn, Lows; lia).
clearbody oA ys oC. clear XO Lows.
pose proof (f32_split rsegs _ _ (sj_msp j) 8%nat ltac:(rewrite Lmsp; lia) BMSP) as [BM1 BM2]. clear BMSP.
replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in BM2 by lia.
assert (LM1 : length (firstn 8 (sj_msp j)) = 8%nat) by (rewrite length_firstn, Lmsp; reflexivity).
assert (LM2 : length (skipn 8 (sj_msp j)) = 8%nat) by (rewrite length_skipn, Lmsp; reflexivity).
remember (OUT + 640 + 160 * sub) as PY eqn:EPY.
call ((h_iir _ (ih_hyps _ _ IH)) (a_exc a) (a_iq a) PY (a_msp a) 40 lo (sj_exc j) (sj_iq j) ys (firstn 8 (sj_msp j)) (Z_to_bv 64 0));
[ exact BEXC | lia | exact BIQ | exact Liq | exact BM1 | exact LM1
| right; split; [subst PY; unfold apart; lia | split; [exact YS | exact Lys]] | lia
| subst PY; unfold apart; lia | subst PY; unfold apart; lia
| unfold apart; pose proof (lay_IQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia | unfold apart; slia
| lia | Z.to_euclidean_division_equations; lia
| lia | Z.to_euclidean_division_equations; lia
| subst PY; lia | subst PY; Z.to_euclidean_division_equations; lia
| lia | Z.to_euclidean_division_equations; lia
| rewrite USP672; exact ST | rewrite USP672; unfold IIR_DEPTH; lia | unfold NB_GLOBALS_TOP in *; lia | rewrite USP672; lia
| rewrite USP672; unfold apart; lia
| subst PY; rewrite USP672; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP672; unfold apart; lia | rewrite USP672; unfold apart; lia
| reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ].

cbv beta delta [callR]. clear FRM. try clear YS; try clear Lys; try clear BM1; try clear LM1. name_post. rename FRMc into FRM. try rename STc into ST.
rewrite USP672 in ST.
match goal with H : rw_cells _ _ PY (f32 ?w), L : length ?w = _ |- _ => rename H into YS; rename L into Lys; rename w into ys2 end.
match goal with H : rw_cells _ _ (a_msp a) (f32 ?w), L : length ?w = _ |- _ => rename H into BM1; rename L into LM1; rename w into msp1 end.
change (Z.to_nat 40) with 40%nat in Lys.
subst PY.
pose proof (f32_join rsegs _ _ _ _ XA ltac:(replace (OUT + 4 * Z.of_nat (length oA)) with (OUT + 640 + 160 * sub) by lia; exact YS)) as XAY.
pose proof (f32_join rsegs _ _ _ _ XAY ltac:(rewrite length_app, Lys; replace (OUT + 4 * Z.of_nat (length oA + 40%nat)) with (OUT + 640 + 160 * sub + 160) by lia; exact XC)) as XO.
clear XA XAY YS XC.
assert (Lows : length ((oA ++ ys2) ++ oC) = 2000%nat) by (rewrite !length_app, Lys; lia).
set (ows2 := (oA ++ ys2) ++ oC) in *. clearbody ows2.
pose proof (f32_join rsegs _ _ _ _ BM1 ltac:(rewrite LM1; replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) by lia; exact BM2)) as BMSP. clear BM1 BM2.
assert (Lmsp' : length (msp1 ++ skipn 8 (sj_msp j)) = 16%nat) by (rewrite length_app, LM1, LM2; reflexivity).
set (mspN := msp1 ++ skipn 8 (sj_msp j)) in *. clearbody mspN.

zstep. rewrite F64e. zstep. rewrite Efs, (sx32_lit 40) by lia. zstep. rewrite (lts_zero_lit 40) by lia. if_false_x.
zstep. zstep. zstep. rewrite ?zb_lxor_ones by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (cp1_loop S (usp + -672) (a_exc a) 160 OUT s1 a 40%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (sj_exc j) vexc [] [] (a_exc a) (usp + -672));
[ cbn [length]; lia | lia | reflexivity | lia
| cbn [length]; lia | cbn [length]; lia | reflexivity
| reflexivity | lia | Z.to_euclidean_division_equations; lia | lia | lia | lia
| lia | lia | rewrite cells_size_sbp_ptrs; lia
| unfold apart; lia
| rewrite cells_size_sbp_ptrs; unfold apart; slia
| reflexivity | reflexivity
| exact MI | apply munch_refl | apply wmono_refl
| unfold sbp_ptrs; exact P2
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at BEXC
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC | ] end.

cbv beta. try clear BEXC; try clear VEXC. name_post. try rename STc into ST. try rename FRMc into FRM. cbn [app] in *.
match goal with H : rw_cells _ _ (a_exc a) (f32 ?w), L : length ?w = _ |- _ => rename H into BEXC; rename L into LexcN; rename w into excN end.
match goal with H : rw_cells _ _ (usp + -672) (f32 vexc) |- _ => rename H into VEXC end.

zstep. rewrite Ilpc1, (sx32_lit 8) by lia. zstep. rewrite (lts_zero_lit 8) by lia. if_false_x.
zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (cp2_loop S (usp + -512) (a_iq a) 32 OUT s1 a 8%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (sj_iq j) vak [] [] (a_iq a) (usp + -512));
[ cbn [length]; lia | rewrite Lvak, Liq; reflexivity | reflexivity | rewrite Liq; lia
| cbn [length]; lia | cbn [length]; lia | reflexivity
| reflexivity | lia | Z.to_euclidean_division_equations; lia | lia | lia | lia
| lia | lia | rewrite cells_size_sbp_ptrs; lia
| unfold apart; lia
| rewrite cells_size_sbp_ptrs; unfold apart; slia
| reflexivity
| exact MI | apply munch_refl | apply wmono_refl
| first [ assumption | unfold sbp_ptrs; exact P2 ]
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at BIQ
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VAK | ] end.
cbv beta. try clear BIQ; try clear VAK. name_post. try rename STc into ST. try rename FRMc into FRM. cbn [app] in *.
match goal with H : rw_cells _ _ (a_iq a) (f32 ?w), L : length ?w = _ |- _ => rename H into BIQ; rename L into LiqN; rename w into iqN end.
match goal with H : rw_cells _ _ (usp + -512) (f32 vak) |- _ => rename H into VAK end.

zstep. zstep.
call ((h_rms _ (ih_hyps _ _ IH)) (a_exc a) 40 excN); [exact BEXC | rewrite LexcN; reflexivity | lia | lia | Z.to_euclidean_division_equations; lia | reflexivity | reflexivity | exact MI | exact FRM | ].
cbv beta delta [callR]. clear FRM. try clear BEXC; try clear LexcN. name_post. rename FRMc into FRM. try rename STc into ST.
match goal with H : rw_cells _ _ (a_exc a) (f32 ?w), L : length ?w = _ |- _ => rename H into BEXC; rename L into LexcN; rename w into excM end.
change (Z.to_nat 40) with 40%nat in LexcN.

zstep. rewrite F128e. zstep. zstep. rewrite F192e. zstep. zstep. zstep. zstep.
if_false_z.
zstep. if_false_z.
zstep. if_false_z.
zstep. zstep.
assert (ER4 : (a_er a + sub * 4) mod 4 = 0) by (Z.to_euclidean_division_equations; lia).
replace (Z.land (a_er a + sub * 4) 3) with 0 by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact ER4).
if_false_z.
pose proof (f32_split rsegs _ _ (sj_er j) (Z.to_nat sub) ltac:(rewrite Ler; lia) BER) as [QER1 QER2]. clear BER.
replace (a_er a + 4 * Z.of_nat (Z.to_nat sub)) with (a_er a + sub * 4) in QER2 by lia.
assert (LER1 : Z.of_nat (length (firstn (Z.to_nat sub) (sj_er j))) = sub) by (rewrite length_firstn, Ler; lia).
destruct (skipn (Z.to_nat sub) (sj_er j)) as [|er0 errest] eqn:EERR.
{ exfalso. pose proof (f_equal (@length _) EERR) as LL. rewrite length_skipn, Ler in LL. cbn in LL. lia. }
assert (LERR : Z.of_nat (length errest) = 3 - sub).
{ pose proof (f_equal (@length _) EERR) as LL. rewrite length_skipn, Ler in LL. cbn in LL. lia. }
clear EERR. set (erdone := firstn (Z.to_nat sub) (sj_er j)) in *. clearbody erdone.
remember (a_er a + sub * 4) as ERA eqn:EERA.
pose proof (rw_cells_bound _ _ _ _ QER2) as BQER2. rewrite cells_size_f32 in BQER2. cbn [length] in BQER2. rewrite f32_cons in QER2.
lstep.
lazymatch type of QER2 with rw_cells _ _ _ (C4 ?v :: f32 errest) =>
rewrite <- (f32_cons v errest) in QER2;
pose proof (f32_join rsegs _ _ _ _ QER1 ltac:(replace (a_er a + 4 * Z.of_nat (length erdone)) with ERA by lia; exact QER2)) as BER end.
lazymatch type of BER with rw_cells _ _ _ (f32 ?erl) => set (ernew := erl) in BER end.
assert (Ler' : length ernew = 4%nat) by (subst ernew; rewrite length_app; cbn [length]; lia). clearbody ernew.
clear QER1 QER2.
zstep. if_false_z.
subst ERA.

zstep. rewrite F136e. zstep. rewrite F200e. zstep. rewrite F56e. zstep. if_false_z.
zstep. rewrite Inb1, (sx32_lit 4) by lia. zstep. rewrite Inb1, (sx32_lit 4) by lia.
zstep. zstep. zstep. zstep. rewrite F200e. zstep. zstep. zstep.
pose proof (f32_as_blob _ _ _ 40%nat VEXC Lvexc) as INB. clear VEXC. change (Z.to_nat (4 * Z.of_nat 40%nat)) with 160%nat in INB.
release_frame INB ST (usp + -512).

destruct (Z.eq_dec sub 3) as [E3 | NE3].
-
rewrite (lts_ge_false' (sub + 1) 4) by lia. zstep.
apply evt_done. right. split; [exact E3|]. unfold at_T.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _, _, _, _, _, _.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) excM (sj_oq j) iqN mspN (sj_pg j) ernew).
exists ows2, stb, fr. first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
repeat match goal with |- _ /\ _ => split end; first [ assumption | lia ].
-
rewrite (lts_true' (sub + 1) 4) by lia.
apply evt_done. left. split; [lia|]. unfold at_L.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _, _, _.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) excM (sj_oq j) iqN mspN (sj_pg j) ernew).
exists ows2, stb, fr. first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
repeat match goal with |- _ /\ _ => split end; first [ assumption | lia ].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
