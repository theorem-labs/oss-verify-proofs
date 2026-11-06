(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09e.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition A_noise_codebook_unquant : Z := 0xb29a8.

Definition noise_cb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(usp lo inn seedp : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (is' : list word) (seed' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(inn, inn + 160); (seedp, seedp + 4); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ rw_cells bsegs m' inn (f32 is') /\ length is' = 40%nat /\ rw_cells bsegs m' seedp [C4 seed'].

Section NC.
Variables (inn seedp usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis OBI : aobj bsegs m inn 160.
Hypothesis OBS : aobj bsegs m seedp 4.
Hypothesis I4 : inn mod 4 = 0.
Hypothesis S4 : seedp mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ISH : inn + 160 <= SH_LO \/ SH_HI <= inn.
Hypothesis SSH : seedp + 4 <= SH_LO \/ SH_HI <= seedp.
Hypothesis IAP : inn + 160 <= lo \/ usp <= inn.
Hypothesis SAP : seedp + 4 <= lo \/ usp <= seedp.
Hypothesis ISA : inn + 160 <= seedp \/ seedp + 4 <= inn.
Local Notation POST := (noise_cb_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo inn seedp m).
Local Notation W := [(inn, inn + 160); (seedp, seedp + 4); (usp + -16, usp)].

Lemma noise_loop : forall (rest dn : list word) (x sd : word) (kz off : Z) (seed0 : word) (j0 : list byte) (wa1 wa2 wt4 t5 t6 : word) F0 fc m1,
wa1 = Z_to_bv 64 (inn + off) -> wa2 = Z_to_bv 64 kz -> wt4 = Z_to_bv 64 (inn + off) -> 0 < inn ->
Z.of_nat (length dn) + Z.of_nat (S (length rest)) = 40 ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -16) -> rw_cells bsegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m1 inn (f32 dn) -> rw_cells bsegs m1 (inn + off) (f32 (x :: rest)) -> rw_cells bsegs m1 seedp [C4 seed0] ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1664525) (Z_to_bv 64 1013904223) (Z_to_bv 64 1) s0 s1
(Z_to_bv 64 inn) wa1 wa2 sd (Z_to_bv 64 (Z.shiftr seedp 3 + SHB)) (Z_to_bv 64 seedp) (Z_to_bv 64 SHB) (Z_to_bv 64 1)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1065353216) wt4 t5 t6)
F0 (Z_to_bv 64 0xb2a24) fc None m1 (seg_rom bsegs)).
Proof using OBI OBS I4 S4 LO SPH IAP SAP ISA ISH SSH.
induction rest as [|x' rest IH]; intros dn x sd kz off seed0 j0 wa1 wa2 wt4 t5 t6 F0 fc m1 E1 E2 E4 IPOS HL Hkz Hoff FRM MU OF WM MI ST FR DONE X SD;
subst wa1 wa2 wt4;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof OBI as (OI0 & OI1 & _); pose proof OBS as (OS0 & OS1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons, ?f32_nil in X.
- bato 0xb2a4c. astep. chk_merge OBI 4.
bato 0xb2a80. astep. try sh_if.
bato 0xb2aa0. astep. chk_merge OBS 4.
bato 0xb2aa8. astep. release_frame FR ST usp. astep. astep.
unfold noise_cb_post. finish.
+ chunk_snoc DONE X. f32_fold_snoc DONE. exact DONE.
+ rewrite length_app. cbn [length] in *. lia.
+ eassumption.
- bato 0xb2a4c. astep. chk_merge OBI 4.
bato 0xb2a80. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (inn + off + 4) with (inn + (off + 4)) in * by lia.
rewrite <- f32_cons in X. f32_fold_snoc DONE.
eapply (IH _ x' _ (Z.of_nat (S (length rest))) (off + 4)); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Lemma noise_cb_walk : forall (is0 : list word) (seed0 : word) (t0 t1 t2 a1 a3 a4 a6 a7 t3 t4 t5 t6 : word) F fc,
rw_cells bsegs m inn (f32 is0) -> length is0 = 40%nat -> rw_cells bsegs m seedp [C4 seed0] -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= inn -> (seedp + 4 <= 0x10000 \/ IMG_TOP_B <= seedp) -> 0 < seedp ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 inn) a1 (Z_to_bv 64 40) a3 a4 (Z_to_bv 64 seedp) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_noise_codebook_unquant) fc None m (seg_rom bsegs)).

Proof.
intros is0 seed0 t0 t1 t2 a1 a3 a4 a6 a7 t3 t4 t5 t6 F fc X LX SD FRM ST ITOP STOP SPOS (G1 & G2 & _) MI.
unfold A_noise_codebook_unquant, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof ISH as ISH'. unfold SH_LO, SH_HI in ISH'.
pose proof SSH as SSH'. unfold SH_LO, SH_HI in SSH'. unfold IMG_TOP_B in ITOP, STOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LX in BX.
pose proof ST as (STa & STb & _).
pose proof OBI as (OI0 & OI1 & _). pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xb29d8. astep. chk_merge OBS 4.
bato 0xb2a24. bnorm. bdec.
destruct is0 as [|x0 rest]; [cbn [length] in LX; lia|].
replace inn with (inn + 0) in X at 1 by lia.
eapply (noise_loop rest [] x0 _ 40 0); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End NC.
