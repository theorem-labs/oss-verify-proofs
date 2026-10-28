(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.
Lemma f32_snoc4 l a b c d : (((f32 l ++ [C4 a]) ++ [C4 b]) ++ [C4 c]) ++ [C4 d] = f32 (l ++ [a; b; c; d]).
Proof. rewrite <- !app_assoc. cbn [app]. rewrite f32_app, !f32_cons, f32_nil. reflexivity. Qed.

Section Inner.
Context {RCEIL : RunCeiling}.

Variables (usp j : Z) (m0 : mem).
Variables ra gp tp sp xa1 s9 s10 s11 : word.

Definition inner_post : machine_state -> Prop :=
fun ms' => exists (G' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws' : list word) (xs3 xs4 xs5 xs6 xs7 xs8 : word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -224)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (-4)) (Z_to_bv 64 5) sp (Z_to_bv 64 2147483647)
(Z_to_bv 64 j) xa1 (Z_to_bv 64 10) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -176)) (Z_to_bv 64 (usp + -224))
(Z_to_bv 64 (18446744073709551615 - (usp + -224))) (Z_to_bv 64 (18446744073709551615 - (usp + -176)))
(Z_to_bv 64 80) xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 (-8)) (Z_to_bv 64 80) (Z_to_bv 64 8589934592) (Z_to_bv 64 1))
G' (Z_to_bv 64 0x27e40) fc' None m' (seg_rom rsegs)
/\ munch [(usp + -176, usp + -96)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' (usp + -176) (f32 ws') /\ length ws' = 22%nat.

Local Ltac il_body q xq o2 o3 :=
zstep; if_false_x; zstep; if_false_x;
zstep; replace (usp + -176 + o2) with q by lia;
zstep; if_false_x; zstep; zstep; if_false_x; zstep; zstep; if_false_x;
zstep; if_false_x; zstep; zstep; if_false_x; zstep; zstep; if_false_x; zstep; if_false_x;
zstep; replace (usp + -224 + o3) with xq by lia;
do 21 zstep.

#[using="Type"] Lemma inner_loop : forall (k : nat) (wdone wrest xrest : list word) (q xq o2 o3 o5 : Z) (n1 n2 n3 n4 x0 x1 : word)
(xs4 xs6 xs7 xs8 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length wrest = (4 * k + 2)%nat -> length xrest = (2 * k)%nat -> (length wdone + 4 * k = 16)%nat ->
q = usp + -176 + 4 * Z.of_nat (length wdone) -> xq = usp + -220 + 2 * Z.of_nat (length wdone) ->
o2 = 4 * Z.of_nat (length wdone) -> o3 = 2 * Z.of_nat (length wdone) + 4 -> 2 * o5 = Z.of_nat (length wdone) ->
usp + -88 < 2 ^ 64 -> 4272 <= usp ->
frm0 fc -> mem_inv rsegs m -> munch [(usp + -176, usp + -96)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m (usp + -176) (f32 wdone) -> rw_cells rsegs m q (f32 (n1 :: n2 :: n3 :: n4 :: wrest)) ->
rw_cells rsegs m (xq + -4) (f32 (x0 :: x1 :: xrest)) ->
evt rsegs inner_post
(MS (mkR ra (Z_to_bv 64 (usp + -224)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (-4)) (Z_to_bv 64 5) sp (Z_to_bv 64 2147483647)
(Z_to_bv 64 j) xa1 (Z_to_bv 64 10) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -176)) (Z_to_bv 64 (usp + -224))
(Z_to_bv 64 (18446744073709551615 - (usp + -224))) (Z_to_bv 64 (18446744073709551615 - (usp + -176)))
(Z_to_bv 64 o2) (Z_to_bv 64 o3) xs4 (Z_to_bv 64 o5) xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 (-8)) (Z_to_bv 64 80) (Z_to_bv 64 8589934592) (Z_to_bv 64 1))
G (Z_to_bv 64 0x27db0) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros wdone wrest xrest q xq o2 o3 o5 n1 n2 n3 n4 x0 x1 xs4 xs6 xs7 xs8 G fc m
LW LX LD Hq Hxq Ho2 Ho3 Ho5 TOP BOT FRM MI MU WM WD WC XC;
pose proof (rw_cells_bound _ _ _ _ WC) as BW; rewrite cells_size_f32 in BW; cbn [length] in BW;
pose proof (rw_cells_bound _ _ _ _ XC) as BXC; rewrite cells_size_f32 in BXC; cbn [length] in BXC;
pose proof (rw_cells_bound _ _ _ _ WD) as BD; rewrite cells_size_f32 in BD.
-
destruct wrest as [|e0 [|e1 [|? ?]]]; try (cbn in LW; lia). destruct xrest; [|cbn in LX; lia]. cbn [length] in LD.
rewrite !f32_cons, f32_nil in WC. rewrite !f32_cons, f32_nil in XC.
il_body q xq o2 o3. if_false_x.
chunk_uncons WC as R1. chunk_uncons WC as R2. chunk_uncons WC as R3. chunk_uncons WC as R4.
chunk_snoc WD R1. chunk_snoc WD R2. chunk_snoc WD R3. chunk_snoc WD R4. rewrite f32_snoc4 in WD.
chunk_uncons WC as R5. chunk_snoc WD R5. rewrite f32_snoc in WD. chunk_uncons WC as R6. chunk_snoc WD R6. rewrite f32_snoc in WD.
replace (o2 + 16) with 80 by lia.
apply evt_done; unfold inner_post.
sf_eexists 10%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|].
split; [exact WD|]. rewrite !length_app; cbn [length]; lia.
- destruct wrest as [|n1' [|n2' [|n3' [|n4' wrest]]]]; try (cbn in LW; lia).
destruct xrest as [|x0' [|x1' xrest]]; try (cbn in LX; lia). cbn [length] in LW, LX, LD, BW, BXC.
rewrite !f32_cons in WC. rewrite !f32_cons in XC.
il_body q xq o2 o3. if_true_x.
chunk_uncons WC as R1. chunk_uncons WC as R2. chunk_uncons WC as R3. chunk_uncons WC as R4.
chunk_snoc WD R1. chunk_snoc WD R2. chunk_snoc WD R3. chunk_snoc WD R4. rewrite f32_snoc4 in WD.
chunk_uncons XC as X1. chunk_uncons XC as X2.
match type of WC with rw_cells _ _ ?a _ => replace a with (q + 16) in WC by lia end.
match type of XC with rw_cells _ _ ?a _ => replace a with (xq + 8 + -4) in XC by lia end.
eapply (IH (wdone ++ [_; _; _; _]) wrest xrest (q + 16) (xq + 8) (o2 + 16) (o3 + 8) (o5 + 2));
[ lia | lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact TOP | exact BOT
| exact FRM | exact MI | exact MU | exact WM | exact WD
| exact WC | exact XC ].
Qed.
End Inner.
