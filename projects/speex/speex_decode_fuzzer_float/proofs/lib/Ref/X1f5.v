(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.
Lemma f32_snoc4 l a b c d : (((f32 l ++ [C4 a]) ++ [C4 b]) ++ [C4 c]) ++ [C4 d] = f32 (l ++ [a; b; c; d]).
Proof. rewrite <- !app_assoc. cbn [app]. rewrite f32_app, !f32_cons, f32_nil. reflexivity. Qed.

Section Inner.
Context {RCEIL : RunCeiling}.

Variables (usp j : Z) (m0 : mem).
Variables gp tp t0 t1 t2 sp s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xa5 xs2 xs3 : word.

Definition inner_post : machine_state -> Prop :=
fun ms' => exists (G' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws' : list word),
ms' = MS (mkR (Z_to_bv 64 145204) (Z_to_bv 64 (usp + -176)) gp tp t0 t1 t2 sp (Z_to_bv 64 8)
(Z_to_bv 64 j) (Z_to_bv 64 (usp + -172)) (Z_to_bv 64 2) (Z_to_bv 64 9) (Z_to_bv 64 (usp + -84))
(Z_to_bv 64 (usp + -84)) (Z_to_bv 64 (usp + -140)) (Z_to_bv 64 (usp + -84))
xs2 xs3 (Z_to_bv 64 (usp + -148)) (Z_to_bv 64 17179869184) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0x238b4) fc' None m' (seg_rom rsegs)
/\ munch [(usp + -144, usp + -80)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' (usp + -144) (f32 ws') /\ length ws' = 18%nat.

#[using="Type"] Lemma inner_loop : forall (k : nat) (wdone wrest xrest : list word) (q xq : Z) (n1 n2 n3 n4 x0 x1 : word)
(xa5 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length wrest = (4 * k + 2)%nat -> length xrest = (2 * k)%nat -> (length wdone + 4 * k = 12)%nat ->
q = usp + -148 + 4 * Z.of_nat (length wdone) -> xq = usp + -172 + 2 * Z.of_nat (length wdone) ->
usp + -144 < 2 ^ 64 -> 4240 <= usp ->
frm0 fc -> mem_inv rsegs m -> munch [(usp + -144, usp + -80)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (usp + -144) (f32 wdone) -> rw_cells rsegs m (q + 4) (f32 (n1 :: n2 :: n3 :: n4 :: wrest)) ->
rw_cells rsegs m (xq + -4) (f32 (x0 :: x1 :: xrest)) ->
evt rsegs inner_post
(MS (mkR (Z_to_bv 64 145204) (Z_to_bv 64 (usp + -176)) gp tp t0 t1 t2 sp (Z_to_bv 64 8)
(Z_to_bv 64 j) (Z_to_bv 64 (usp + -172)) (Z_to_bv 64 2) (Z_to_bv 64 9) (Z_to_bv 64 (usp + -84))
xa5 (Z_to_bv 64 xq) (Z_to_bv 64 q)
xs2 xs3 (Z_to_bv 64 (usp + -148)) (Z_to_bv 64 17179869184) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x2385c) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros wdone wrest xrest q xq n1 n2 n3 n4 x0 x1 xa5' G fc m
LW LX LD Hq Hxq TOP BOT FRM MI MU WM WD WC XC;
pose proof (rw_cells_bound _ _ _ _ WC) as BW; rewrite cells_size_f32 in BW; cbn [length] in BW;
pose proof (rw_cells_bound _ _ _ _ XC) as BXC; rewrite cells_size_f32 in BXC; cbn [length] in BXC;
pose proof (rw_cells_bound _ _ _ _ WD) as BD; rewrite cells_size_f32 in BD.
-
destruct wrest as [|e0 [|e1 [|? ?]]]; try (cbn in LW; lia). destruct xrest; [|cbn in LX; lia]. cbn [length] in LD.
rewrite !f32_cons, f32_nil in WC. rewrite !f32_cons, f32_nil in XC.
do 22 zstep. if_false_x.
chunk_uncons WC as R1. chunk_uncons WC as R2. chunk_uncons WC as R3. chunk_uncons WC as R4.
chunk_snoc WD R1. chunk_snoc WD R2. chunk_snoc WD R3. chunk_snoc WD R4. rewrite f32_snoc4 in WD.
chunk_uncons WC as R5. chunk_snoc WD R5. rewrite f32_snoc in WD. chunk_uncons WC as R6. chunk_snoc WD R6. rewrite f32_snoc in WD.
replace (q + 16) with (usp + -84) by lia. replace (xq + 8) with (usp + -140) by lia.
apply evt_done; unfold inner_post.
sf_eexists 4%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact WD|]. rewrite !length_app; cbn [length]; lia.
- destruct wrest as [|n1' [|n2' [|n3' [|n4' wrest]]]]; try (cbn in LW; lia).
destruct xrest as [|x0' [|x1' xrest]]; try (cbn in LX; lia). cbn [length] in LW, LX, LD, BW, BXC.
rewrite !f32_cons in WC. rewrite !f32_cons in XC.
do 22 zstep. if_true_x.
chunk_uncons WC as R1. chunk_uncons WC as R2. chunk_uncons WC as R3. chunk_uncons WC as R4.
chunk_snoc WD R1. chunk_snoc WD R2. chunk_snoc WD R3. chunk_snoc WD R4. rewrite f32_snoc4 in WD.
chunk_uncons XC as X1. chunk_uncons XC as X2.
match type of WC with rw_cells _ _ ?a _ => replace a with (q + 16 + 4) in WC by lia end.
match type of XC with rw_cells _ _ ?a _ => replace a with (xq + 8 + -4) in XC by lia end.
eapply (IH (wdone ++ [_; _; _; _]) wrest xrest (q + 16) (xq + 8));
[ lia | lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact TOP | exact BOT
| exact FRM | exact MI | exact MU | exact WM | exact WD
| exact WC | exact XC ].
Qed.
End Inner.
