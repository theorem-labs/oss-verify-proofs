(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma f32_win : forall m B (l : list word) (n : Z) (cnt : nat), rw_cells asegs m B (f32 l) ->
0 <= n -> n + Z.of_nat cnt <= Z.of_nat (length l) ->
exists w, length w = cnt /\ rw_cells asegs m (B + 4 * n) (f32 w).
Proof.
intros m B l n cnt X Hn Hn2.
pose proof (rw_cells_f32_mid asegs m B l (Z.to_nat n) cnt X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
exists (firstn cnt (skipn (Z.to_nat n) l)). split; [| exact W].
rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.
Lemma f32_win1 : forall m B (l : list word) (n : Z), rw_cells asegs m B (f32 l) -> 0 <= n -> n + 1 <= Z.of_nat (length l) ->
exists y0, rw_cells asegs m (B + 4 * n) (f32 [y0]).
Proof.
intros m B l n X Hn Hn2. destruct (f32_win m B l n 1%nat X Hn ltac:(lia)) as (w & Lw & W).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia). exists y0. exact W.
Qed.

Section REV.
Variables (Y X NW XN : Z) (ys : list word).
Variables rav spv gp tp t0v t1v t2v s0v s1v a7v s2v s3v s4v s5v s6v s7v s8v s9v s10v t3v t4v t5v t6v : word.
Hypothesis Y4 : Y mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis SEP : Y + 4 * Z.of_nat (length ys) <= X \/ X + XN <= Y.
Hypothesis XI : IMG_TOP <= X.
Hypothesis XNW : 4 * NW <= XN.

Definition RV (xa ya cnt : Z) (a5v a6v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 xa) (Z_to_bv 64 ya) (Z_to_bv 64 ya) (Z_to_bv 64 cnt) (Z_to_bv 64 xa) a5v a6v a7v
s2v s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition rev_post (pcx : Z) (fc : bv 32) (mI : mem) (qe : Z) : machine_state -> Prop :=
fun ms' => exists a5' a6' F' m' (xs' : list word),
ms' = MS (RV (X + 4 * NW) (Y + 4 * qe) 0 a5' a6') F' (Z_to_bv 64 pcx) fc None m' (seg_rom asegs)
/\ munch [(X, X + 4 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ Z.of_nat (length xs') = NW /\ rw_cells asegs m' X (f32 xs').

Definition rev_stmt (pc0 pcx : Z) : Prop := forall (mI : mem) (rest done : list word) (cw : word) (q i xa ya cnt : Z) (a5v a6v : word) F1 fc mc,
xa = X + 4 * i -> ya = Y + 4 * q -> cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> Z.of_nat (length rest) <= q < Z.of_nat (length ys) ->
aobj asegs mI Y (4 * Z.of_nat (length ys)) -> aobj asegs mI X XN -> offsh [(X, X + 4 * NW)] ->
mem_inv asegs mc -> munch [(X, X + 4 * NW)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc Y (f32 ys) -> rw_cells asegs mc X (f32 done) -> rw_cells asegs mc (X + 4 * i) (f32 (cw :: rest)) ->
evt asegs (rev_post pcx fc mI (q - Z.of_nat (length rest) - 1))
(MS (RV xa ya cnt a5v a6v) F1 (Z_to_bv 64 pc0) fc None mc (seg_rom asegs)).

Ltac rev_script pc1 pc2 pc3 :=
intros mI rest;
induction rest as [|cw' rest IH]; intros done cw q i xa ya cnt a5v a6v F1 fc mc -> -> -> Hi HN Hq OBY OBX OF MI MU WM XY XD XC;
pose proof OBY as (OY0 & OY1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1 mc Y ys q XY ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold RV; rewrite !f32_cons in XC; cbn [length] in *;
hide_disj;
[ rewrite f32_nil in XC;
ato pc1; astep; chk_merge OBY 4;
ato pc2; astep; chk_merge OBX 4;
clear WIN;
ato pc3; astep; sh_if; astep;
chunk_snoc XD XC; rewrite f32_snoc in XD;
replace (X + 4 * i + 4) with (X + 4 * NW) by lia;
replace (Y + 4 * q + -4) with (Y + 4 * (q - Z.of_nat 0 - 1)) by lia;
replace (1 + Z.of_nat 0 + -1) with 0 by lia;
unfold rev_post, RV; finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia
| ato pc1; astep; chk_merge OBY 4;
ato pc2; astep; chk_merge OBX 4;
clear WIN;
ato pc3; astep; sh_if;
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC;
replace (X + 4 * i + 4) with (X + 4 * (i + 1)) in * by lia;
replace (Y + 4 * q + -4) with (Y + 4 * (q - 1)) by lia;
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia;
replace (q - Z.of_nat (S (length rest)) - 1) with (q - 1 - Z.of_nat (length rest) - 1) by lia;
eapply (IH _ cw' (q - 1) (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia) ].

Lemma qmf_L1 : rev_stmt 0xa4c98 0xa4cfc.
Proof using Y4 X4 SEP XI XNW. unfold rev_stmt. rev_script 0xa4ca4 0xa4cb8 0xa4cd4. Qed.
Lemma qmf_L3 : rev_stmt 0xa4da4 0xa4e08.
Proof using Y4 X4 SEP XI XNW. unfold rev_stmt. rev_script 0xa4db0 0xa4dc4 0xa4de0. Qed.
End REV.

Section MEMCP.
Variables (G X n0 NW XN : Z) (gs : list word).
Variables rav spv gp tp t0v t1v t2v s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v t3v t4v t5v t6v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LG : length gs = 64%nat.
Hypothesis SEP : G + 256 <= X \/ X + XN <= G.
Hypothesis XI : IMG_TOP <= X.
Hypothesis XNW : 0 <= n0 /\ 4 * (n0 + NW) <= XN.

Definition RM (ga xa sa cnt : Z) (a6v a7v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 ga) (Z_to_bv 64 xa) (Z_to_bv 64 xa) (Z_to_bv 64 ga)
(Z_to_bv 64 sa) (Z_to_bv 64 cnt) a6v a7v
s2v s3v s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition memcp_post (pcx : Z) (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists a6' a7' F' m' (xs' : list word),
ms' = MS (RM (G + 8 * NW + 4) (X + 4 * (n0 + NW)) (Z.shiftr (G + 8 * NW + 4) 3 + SHB) 0 a6' a7') F' (Z_to_bv 64 pcx) fc None m' (seg_rom asegs)
/\ munch [(X + 4 * n0, X + 4 * n0 + 4 * NW)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ Z.of_nat (length xs') = NW /\ rw_cells asegs m' (X + 4 * n0) (f32 xs').

Definition memcp_stmt (pc0 pcx : Z) : Prop := forall (mI : mem) (rest done : list word) (cw : word) (i ga xa sa cnt : Z) (a6v a7v : word) F1 fc mc,
ga = G + 8 * i + 4 -> xa = X + 4 * (n0 + i) -> sa = Z.shiftr (G + 8 * i + 4) 3 + SHB -> cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = NW -> NW <= 32 ->
aobj asegs mI G 256 -> aobj asegs mI X XN -> offsh [(X + 4 * n0, X + 4 * n0 + 4 * NW)] ->
mem_inv asegs mc -> munch [(X + 4 * n0, X + 4 * n0 + 4 * NW)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc G (f32 gs) -> rw_cells asegs mc (X + 4 * n0) (f32 done) -> rw_cells asegs mc (X + 4 * (n0 + i)) (f32 (cw :: rest)) ->
evt asegs (memcp_post pcx fc mI)
(MS (RM ga xa sa cnt a6v a7v) F1 (Z_to_bv 64 pc0) fc None mc (seg_rom asegs)).

Ltac memcp_script pc1 pc2 pc3 :=
intros mI rest;
induction rest as [|cw' rest IH]; intros done cw i ga xa sa cnt a6v a7v F1 fc mc -> -> -> -> Hi HN HNW OBG OBX OF MI MU WM XG XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof XI as XI'; unfold IMG_TOP in XI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1 mc G gs (2 * i + 1) XG ltac:(lia) ltac:(rewrite LG; cbn [length] in *; lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
replace (G + 4 * (2 * i + 1)) with (G + 8 * i + 4) in WIN by lia;
unfold RM; rewrite !f32_cons in XC; cbn [length] in *;
hide_disj;
[ rewrite f32_nil in XC;
ato pc1; astep; chk_merge OBG 4;
ato pc2; astep; chk_merge OBX 4;
clear WIN;
ato pc3; astep; sh_if; astep;
chunk_snoc XD XC; rewrite f32_snoc in XD;
replace (X + 4 * (n0 + i) + 4) with (X + 4 * (n0 + NW)) by lia;
replace (G + 8 * i + 12) with (G + 8 * NW + 4) by lia;
replace (Z.shiftr (G + 8 * i + 4) 3 + SHB + 1) with (Z.shiftr (G + 8 * NW + 4) 3 + SHB)
by (replace (G + 8 * NW + 4) with (G + 8 * i + 4 + 8 * 1) by lia; rewrite shiftr3_add; lia);
replace (1 + Z.of_nat 0 + -1) with 0 by lia;
unfold memcp_post, RM; finish; [ | exact XD ]; rewrite length_app; cbn [length]; lia
| ato pc1; astep; chk_merge OBG 4;
ato pc2; astep; chk_merge OBX 4;
clear WIN;
ato pc3; astep; sh_if;
(let X1c := fresh "X1c" in chunk_uncons XC as X1c; chunk_snoc XD X1c); rewrite f32_snoc in XD; rewrite <- ?f32_cons in XC;
replace (X + 4 * (n0 + i) + 4) with (X + 4 * (n0 + (i + 1))) in * by lia;
replace (G + 8 * i + 12) with (G + 8 * (i + 1) + 4) by lia;
replace (Z.shiftr (G + 8 * i + 4) 3 + SHB + 1) with (Z.shiftr (G + 8 * (i + 1) + 4) 3 + SHB)
by (replace (G + 8 * (i + 1) + 4) with (G + 8 * i + 4 + 8 * 1) by lia; rewrite shiftr3_add; lia);
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia;
eapply (IH _ cw' (i + 1)); try eassumption; try reflexivity;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia) ].

Lemma qmf_L2 : memcp_stmt 0xa4d20 0xa4d84.
Proof using G4 X4 LG SEP XI XNW. unfold memcp_stmt. memcp_script 0xa4d24 0xa4d38 0xa4d58. Qed.
Lemma qmf_L4 : memcp_stmt 0xa4e28 0xa4e8c.
Proof using G4 X4 LG SEP XI XNW. unfold memcp_stmt. memcp_script 0xa4e2c 0xa4e40 0xa4e60. Qed.
End MEMCP.

Section CPMEM.
Variables (G X XN : Z) (xs : list word).
Variables rav spv gp tp t0v t1v t2v s0v s1v a7v s4v s5v s6v s7v s8v s9v s10v t3v t4v t5v t6v : word.
Hypothesis G4 : G mod 4 = 0.
Hypothesis X4 : X mod 4 = 0.
Hypothesis LX : 32 <= Z.of_nat (length xs) /\ 4 * Z.of_nat (length xs) <= XN.
Hypothesis SEP : G + 256 <= X \/ X + XN <= G.

Variables a1f s2f a6f s3f : word.
Definition R5 (ga xa cnt : Z) (a5v a6v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 ga) a1f (Z_to_bv 64 ga) (Z_to_bv 64 cnt) (Z_to_bv 64 xa) a5v a6v a7v
s2f (Z_to_bv 64 xa) s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.
Definition R6 (ga xa cnt : Z) (a4v a5v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 ga) (Z_to_bv 64 ga) (Z_to_bv 64 cnt) (Z_to_bv 64 xa) a4v a5v a6f a7v
(Z_to_bv 64 xa) s3f s4v s5v s6v s7v s8v s9v s10v (Z_to_bv 64 SHB) t3v t4v t5v t6v.

Definition cpmem_post (RR : Z -> Z -> Z -> word -> word -> bvmap 5 word) (pcx : Z) (fc : bv 32) (mI : mem) : machine_state -> Prop :=
fun ms' => exists u' v' F' m' (gs' : list word),
ms' = MS (RR (G + 8 * 32 + 4) (X + 4 * 32) 0 u' v') F' (Z_to_bv 64 pcx) fc None m' (seg_rom asegs)
/\ munch [(G, G + 256)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ length gs' = 64%nat /\ rw_cells asegs m' G (f32 gs').

Definition cpmem_stmt (RR : Z -> Z -> Z -> word -> word -> bvmap 5 word) (pc0 pcx : Z) : Prop :=
forall (mI : mem) (k : nat) (rest done : list word) (ge go : word) (i ga xa cnt : Z) (u v : word) F1 fc mc,
ga = G + 8 * i + 4 -> xa = X + 4 * i -> cnt = 1 + Z.of_nat k -> length rest = (2 * k)%nat -> 2 * i = Z.of_nat (length done) -> i + 1 + Z.of_nat k = 32 ->
aobj asegs mI G 256 -> aobj asegs mI X XN -> offsh [(G, G + 256)] ->
mem_inv asegs mc -> munch [(G, G + 256)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc X (f32 xs) -> rw_cells asegs mc G (f32 done) -> rw_cells asegs mc (G + 8 * i) (f32 (ge :: go :: rest)) ->
evt asegs (cpmem_post RR pcx fc mI)
(MS (RR ga xa cnt u v) F1 (Z_to_bv 64 pc0) fc None mc (seg_rom asegs)).

Ltac cpmem_script RR pc1 pc2 pc3 :=
intros mI k;
induction k as [|k IH]; intros rest done ge go i ga xa cnt u v F1 fc mc -> -> -> LR Hi HN OBG OBX OF MI MU WM XX XD XC;
pose proof OBG as (OG0 & OG1 & _); pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1 mc X xs i XX ltac:(lia) ltac:(lia)) as (y0 & WIN); rewrite f32_cons, f32_nil in WIN;
unfold RR; rewrite !f32_cons in XC;
hide_disj;
[ destruct rest; [| cbn in LR; lia]; rewrite f32_nil in XC;
ato pc1; astep; chk_merge OBX 4;
ato pc2; astep; chk_merge OBG 4;
clear WIN;
ato pc3; astep; sh_if; astep;
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1); chunk_snoc XD XC; rewrite !f32_snoc in XD;
replace (X + 4 * i + 4) with (X + 4 * 32) by lia;
replace (G + 8 * i + 12) with (G + 8 * 32 + 4) by lia;
replace (1 + Z.of_nat 0 + -1) with 0 by lia;
unfold cpmem_post, RR; finish; [ | exact XD ]; rewrite !length_app; cbn [length]; lia
| destruct rest as [|ge' [|go' rest]]; try (cbn in LR; lia); rewrite ?f32_cons in XC;
ato pc1; astep; chk_merge OBX 4;
ato pc2; astep; chk_merge OBG 4;
clear WIN;
ato pc3; astep; sh_if;
(let C1 := fresh "C1" in chunk_uncons XC as C1; chunk_snoc XD C1);
(let C2 := fresh "C2" in chunk_uncons XC as C2; chunk_snoc XD C2); rewrite !f32_snoc in XD; rewrite <- ?f32_cons in XC;
replace (G + 8 * i + 4 + 4) with (G + 8 * (i + 1)) in * by lia;
replace (X + 4 * i + 4) with (X + 4 * (i + 1)) by lia;
replace (G + 8 * i + 12) with (G + 8 * (i + 1) + 4) by lia;
replace (1 + Z.of_nat (S k) + -1) with (1 + Z.of_nat k) by lia;
eapply (IH rest _ ge' go' (i + 1)); try eassumption; try reflexivity;
try (rewrite !length_app; cbn [length] in *; lia); try (cbn [length] in *; lia) ].

Lemma qmf_L5 : cpmem_stmt R5 0xa51dc 0xa5240.
Proof using G4 X4 LX SEP. unfold cpmem_stmt. cpmem_script R5 0xa51e8 0xa51fc 0xa5218. Qed.
Lemma qmf_L6 : cpmem_stmt R6 0xa5250 0xa52b4.
Proof using G4 X4 LX SEP. unfold cpmem_stmt. cpmem_script R6 0xa525c 0xa5270 0xa528c. Qed.
End CPMEM.
