(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STEREO_DEPTH : Z := 48.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition stereo_handler_post (A D : Z) b (STEREO lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (sws' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep rsegs m' A D (stereo_handler_bits b) /\ bits_ok (stereo_handler_bits b).
Definition stereo_handler_stmt : Prop :=
forall (A D : Z) b (ST STEREO lo : Z) (sws : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b ->
rw_cells rsegs m STEREO (f32 sws) -> length sws = 2%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + STEREO_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
apart STEREO 8 lo (bv_unsigned sp - lo) ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart STEREO 8 A BITS_SIZEOF -> apart STEREO 8 D (sb_buf_size b) ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 ST -> a2 = Z_to_bv 64 STEREO ->
mem_inv rsegs m -> frm0 fc ->
0 < STEREO -> STEREO mod 4 = 0 ->
evt rsegs (stereo_handler_post A D b STEREO lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_std_stereo_request_handler) fc None m (seg_rom rsegs)).

Hypothesis HEXP : @exp_stmt.

Definition exp_postZ (lo q : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (k : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (callR ra (Z_to_bv 64 q) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv k) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, q)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo q.
#[using="HEXP"] Lemma exp_specZ : forall (lo q : Z)
(ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk rsegs m lo q -> lo + EXP_DEPTH <= q -> 0 <= q < 2^64 -> mem_inv rsegs m -> frm0 fc ->
evt rsegs (exp_postZ lo q ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_exp) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros STK LO Hq MI FRM.
pose proof (HEXP lo ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m) as H.
unfold exp_post in H. rewrite !unsigned_lit64 in H by lia. apply H; assumption.
Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.

Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].

#[using="Type"] Lemma stereo_tail : forall (A D : Z) (b b3 : bits_st ptr) (STEREO lo tmp : Z) (w0 w1 : word) (rj : list byte) (bs : list byte)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(rav x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 s2v : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m0 m1 : mem),
0 <= tmp < 4 ->
length rj = 16%nat -> rw_cells rsegs m1 A (bits_cells D b3 rj) -> u8arr rsegs m1 D bs -> sb_data b3 = map bv_unsigned bs -> bits_side A D b3 ->
bits_ok b3 ->
rw_cells rsegs m1 STEREO (f32 [w0; w1]) ->
rw_cells rsegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
stk rsegs m1 lo (bv_unsigned sp + -32) -> lo + STEREO_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
apart STEREO 8 lo (bv_unsigned sp - lo) -> apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart STEREO 8 A BITS_SIZEOF -> apart STEREO 8 D (sb_buf_size b) ->
munch [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
b3 = stereo_handler_bits b ->
evt rsegs (stereo_handler_post A D b STEREO lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0)
(MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x1 x2 x3 (Z_to_bv 64 STEREO) (Z_to_bv 64 A) (Z_to_bv 64 tmp) x4 x5 x6 x7 x8 x9 x10
s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 x11 x12 x13 x14)
F1 (Z_to_bv 64 0x1d2fc) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros Htmp Lrj OBJ DAT Hbs SIDE OK3 SW FR STK LO GLO AS1 AS2 AS3 AS4 AS5 MU WM MI FRM ->.
unfold STEREO_DEPTH, NB_GLOBALS_TOP, apart in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
unfold bits_cells in OBJ.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (rw_cells_bound _ _ _ _ SW) as GS. cbn [cells_size csize Nat.add length f32 map] in GS.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (BSZ : sb_buf_size (stereo_handler_bits b) = sb_buf_size b) by (unfold stereo_handler_bits; rewrite !ub_size; reflexivity).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK3 as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
rewrite f32_cons, f32_cons, f32_nil in SW.
assert (CASES : tmp = 0 \/ tmp = 1 \/ tmp = 2 \/ tmp = 3) by lia.
destruct CASES as [-> |[-> |[-> | ->]]].
all: zstep; zstep; ntk.
all: zstep; zstep; zstep; zstep; zstep; ntk.
all: do 5 zstep.
all: do 5 zstep; release_frame FR STK (bv_unsigned sp); zstep.
all: apply evt_done; unfold stereo_handler_post;
eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 3%nat; eexists [_; _];
split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact FRM|]; split; [exact STK|];
split; [rewrite f32_cons, f32_cons, f32_nil; exact SW|]; split; [reflexivity|];
split; [| exact OK3];
(split; [exists rj; split; [exact Lrj| unfold bits_cells; exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]).
Qed.

Ltac stereo_rest A D b STEREO lo rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK1 SN0 SM4 :=
zstep; zstep; zstep;
let R1 := fresh "REP" in
rebits R1 A D (ub b 1) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1;
zstep; (call (speex_bits_unpack_unsigned_spec A D (ub b 1) 5); [exact R1 | exact OK1 | lia | eassumption |]);
clear R1; try rename MI0 into MI; rewrite (unpack_eta (ub b 1) 5) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub (ub b 1) 5) |- _ =>
destruct H as ((rj2 & Lrj2 & OBJ2) & (bs2 & DAT2 & Hbs2) & SIDE2); unfold bits_cells in OBJ2 end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv (ub b 1) 5) |- _ => subst v end;
let OK2 := fresh "OK2" in let Hv2 := fresh "Hv2" in let Hbs2' := fresh "Hbs2'" in let Lbs2 := fresh "Lbs2" in
pose proof (speex_bits_unpack_unsigned_ok (ub b 1) 5 _ _ OK1 ltac:(lia) (unpack_eta (ub b 1) 5)) as sfP_; sf_curry 6%nat sfP_; intros OK2 Hv2 _ _ Hbs2' _; sf_clear sfP_; sf_fix_order;
lazymatch goal with Hbs2 : sb_data (ub (ub b 1) 5) = map bv_unsigned ?bs2 |- _ =>
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size b)
by (let X := fresh in pose proof OK2 as X; unfold bits_ok in X; rewrite Hbs2, zlength_map_unsigned in X; lia) end;
zstep; ntk;
zstep; rewrite land3_mod4, SM4;
zstep; ntk;
zstep; try (replace (Z.b2z (0 <? 1)) with 1 by reflexivity); try (replace (Z.b2z (1 <? 1)) with 0 by reflexivity);
do 5 zstep;
do 3 zstep;
zstep; (call (exp_specZ lo); [eassumption | unfold EXP_DEPTH; lia | lia | eassumption | eassumption |]); try rename MI0 into MI;
unfold callR;
lazymatch goal with H : rw_cells _ _ STEREO _ |- _ => rewrite f32_cons, f32_cons, f32_nil in H end;
zstep; zstep;
lazymatch goal with OBJ2 : rw_cells _ _ A _, DAT2 : u8arr _ _ D ?bs2 |- _ =>
lazymatch goal with Lrj2 : length ?rj2 = 16%nat, Hbs2 : sb_data _ = map bv_unsigned bs2, SIDE2 : bits_side A D (ub (ub b 1) 5) |- _ =>
let R2 := fresh "REP" in
rebits R2 A D (ub (ub b 1) 5) rj2 Lrj2 OBJ2 bs2 DAT2 Hbs2 SIDE2;
zstep; zstep; zstep; (call (speex_bits_unpack_unsigned_spec A D (ub (ub b 1) 5) 2); [exact R2 | eassumption | lia | eassumption |]);
clear R2 end end;
try rename MI0 into MI; rewrite (unpack_eta (ub (ub b 1) 5) 2) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub (ub (ub b 1) 5) 2) |- _ =>
destruct H as ((rj3 & Lrj3 & OBJ3) & (bs3 & DAT3 & Hbs3) & SIDE3) end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv (ub (ub b 1) 5) 2) |- _ => subst v end;
lazymatch goal with OK2 : bits_ok (ub (ub b 1) 5) |- _ =>
pose proof (speex_bits_unpack_unsigned_ok (ub (ub b 1) 5) 2 _ _ OK2 ltac:(lia) (unpack_eta (ub (ub b 1) 5) 2)) as sfP_; sf_curry 6%nat sfP_; intros OK3 Hv3 _ _ Hbs3' _; sf_clear sfP_; sf_fix_order end;
eapply (stereo_tail A D b (ub (ub (ub b 1) 5) 2) STEREO lo (uv (ub (ub b 1) 5) 2));
try eassumption; try reflexivity; try lia;
rewrite ?f32_cons, ?f32_nil; try eassumption.

#[using="HEXP"] Lemma stereo_handler_proof : stereo_handler_stmt.
Proof.
unfold stereo_handler_stmt. intros until m. intros REP OK SW LSW STK LO GLO AS1 AS2 AS3 AS4 AS5 -> -> -> MI FRM SN0 SM4.
unfold STEREO_DEPTH, NB_GLOBALS_TOP, apart in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
destruct sws as [|w0 [|w1 [|? ?]]]; try (cbn in LSW; lia). clear LSW.
pose proof (rw_cells_bound _ _ _ _ SW) as GS. cbn [cells_size csize Nat.add length f32 map] in GS.
pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold A_speex_std_stereo_request_handler.
carve_frame 32%nat STK.
do 8 zstep.
rebits REP A D b rj Lrj OBJ bs DAT Hbs SIDE.

zstep. call (speex_bits_unpack_unsigned_spec A D b 1); [exact REP | exact OK | lia | exact MI |].
clear REP. try rename MI0 into MI. rewrite (unpack_eta b 1) in *. cbn [fst snd] in *.
match goal with H : bits_rep _ _ _ _ (ub b 1) |- _ => destruct H as ((rj1 & Lrj1 & OBJ1) & (bs1 & DAT1 & Hbs1) & SIDE1) end.
unfold bits_cells in OBJ1.
match goal with H : ?v = Z_to_bv 64 (uv b 1) |- _ => subst v end.
pose proof (speex_bits_unpack_unsigned_ok b 1 _ _ OK ltac:(lia) (unpack_eta b 1)) as sfP_; first [ sf_destruct 6%nat sfP_ as OK1 Hv1 _ _ Hbs1' _ | sf_fb; destruct sfP_ as (OK1 & Hv1 & _ & _ & Hbs1' & _) ].
assert (Lbs1 : Z.of_nat (length bs1) = sb_buf_size b).
{ pose proof OK1 as X. unfold bits_ok in X. rewrite Hbs1, zlength_map_unsigned in X. lia. }

assert (CV : uv b 1 = 0 \/ uv b 1 = 1) by lia.
destruct CV as [EV|EV]; rewrite EV.
- stereo_rest A D b STEREO lo rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK1 SN0 SM4.
- stereo_rest A D b STEREO lo rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK1 SN0 SM4.
Qed.
End F.
