(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_h_model.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma upd_app_mid : forall {X} (l1 : list X) (x v : X) (l2 : list X), upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|a l1 IH]; intros x v l2; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Section Tail.
Hypothesis U32R : prod_u32r_stmt.
Variables (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : fmem) (SP P D BUFF : Z) (pl data : list Z) (msv tl dsz bsz lo : Z).
Variable POST : machine_state -> Prop.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis LO : lo <= SP - 16.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis BLO : 0 < BUFF /\ BUFF + bsz <= lo.
Hypothesis BP : BUFF + bsz <= P \/ P + 16 <= BUFF.
Hypothesis BD : BUFF + bsz <= D \/ D + zlen pl <= BUFF.
Hypothesis DSZ : zlen data = dsz.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis PPOS : 0 < P.
Hypothesis PAL : P mod 8 = 0.
Hypothesis DPOS : 0 < D.
Notation W := [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 16, SP)].
Definition TINV (m1 : fmem) (filled : list Z) (rest : list byte) (size : Z) : Prop :=
u8arr usegs m1 BUFF (map (Z_to_bv 8) filled ++ rest)
/\ prod_at m1 P D size /\ bytes_at usegs m1 D (map (Z_to_bv 8) pl)
/\ stk usegs m1 lo SP
/\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 tl) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 msv) (Z_to_bv 64 BUFF) (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
#[using="U32R RSP LO PLO DLO DP BLO BP BD DSZ PLB PPOS PAL DPOS"] Lemma tail_loop : forall f size acc rest m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
(1 <= f)%nat -> length rest = f -> dsz + zlen acc + Z.of_nat f = bsz -> 0 <= size <= zlen pl -> 0 <= dsz ->
TINV m1 (data ++ acc) rest size ->
(forall m2 junkF remF (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y25 y28 y29 y30 y31 : word),
fseB_tail_loop f pl size acc = (junkF, remF) ->
TINV m2 (data ++ junkF) [] remF -> 0 <= remF <= size ->
evt usegs POST (STpc 0x1370c m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y25 y28 y29 y30 y31)) ->
evt usegs POST (STpc 0x136d4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.of_nat f)) (Z_to_bv 64 (BUFF + (dsz + zlen acc))) (Z_to_bv 64 1) (Z_to_bv 64 (BUFF + (dsz + zlen acc))) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros size acc rest m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HF HR HB SZ DS0 (BA & PR & PAY & ST & MU & WM & MI) K.
{ exfalso.
lia. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
zstep. zstep. zstep. zstep.
unfold prod_u32r_stmt, PPROD_U32R in U32R.
assert (LBA : zlen (map (Z_to_bv 8) (data ++ acc) ++ rest) = bsz).
{ rewrite length_app, length_map, length_app. lia. }
assert (LBA' : Z.of_nat (length (map (Z_to_bv 8) (data ++ acc)) + length rest) = bsz) by (rewrite <- length_app; exact LBA).
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size 0 255 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
clear PR. rename POST0 into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
pose proof (uint32Range_spec pl size 0 255 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as UR.
rewrite fseB_tail_loop_step in K.
destruct (uint32Range pl size 0 255) as [c size'] eqn:EU. cbn [fst snd] in *. destruct UR as (CR & SZ' & _).
destruct rest as [|r0 rest']; [cbn in HR; lia|]. cbn [length] in HR.
zstep. if_cases G0; zify_cond G0; [exfalso; lia|]. clear G0.
zstep. zstep.
replace (BUFF + (dsz + zlen acc) <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
change (Z.lxor 1 (Z.b2z false)) with 1.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|]. clear G1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|]. clear G2.
pose proof (u8arr_store_ok usegs _ BUFF _ (dsz + zlen acc) (wa (BUFF + (dsz + zlen acc))) BA ltac:(rewrite LBA; lia) eq_refl) as SOK.
zstep. rewrite le1_lit.
pose proof (u8arr_write usegs _ BUFF _ (dsz + zlen acc) (Z_to_bv 8 c) BA ltac:(rewrite LBA; lia)) as BA2.
clear BA. store_done.
replace (Z.to_nat (dsz + zlen acc)) with (length (map (Z_to_bv 8) (data ++ acc))) in BA2 by (rewrite length_map, length_app; lia).
rewrite upd_app_mid in BA2.
replace (map (Z_to_bv 8) (data ++ acc) ++ Z_to_bv 8 c :: rest') with (map (Z_to_bv 8) (data ++ (acc ++ [to_byte c])) ++ rest') in BA2.
2:{ rewrite (app_assoc data acc), map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
unfold to_byte. rewrite (Z.mod_small c 256) by lia. reflexivity. }
zstep. zstep. zstep.
replace (Z.of_nat (S f) + -1) with (Z.of_nat f) by lia.
replace (BUFF + (dsz + zlen acc) + 1) with (BUFF + (dsz + zlen (acc ++ [to_byte c]))) by (rewrite length_app; cbn [length]; lia).
assert (INV2 : TINV m0 (data ++ (acc ++ [to_byte c])) rest' size').
{ split; [exact BA2|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
zstep. if_cases B; zify_cond B.
-
eapply (IH size' (acc ++ [to_byte c]) rest'); try lia; [rewrite length_app; cbn [length]; lia| exact INV2|].
intros. eapply K; try eassumption. lia.
-
assert (f = 0%nat) by lia. subst f. destruct rest'; [|cbn in HR; lia].
eapply K; [reflexivity| exact INV2| lia].
Qed.
End Tail.
