(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0ys X0wh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yt X0z5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Ltac margin_leaf K := eapply K; eassumption.
Ltac margin_hi OB K :=
bato 0xaf004; astep; chk_merge OB 4;
bato 0xaf020; astep; chk_merge OB 4;
bato 0xaf030; astep; let B2 := fresh "B2" in if_cases B2;
[ bato 0xaf058; margin_leaf K
| bato 0xaf044; astep; chk_merge OB 4; bato 0xaf058; margin_leaf K ].
Ltac margin_iter OB K :=
bato 716736; astep; chk_merge OB 4;
bato 716756; astep; chk_merge OB 4;
bato 716772; astep; let B1 := fresh "B1" in if_cases B1;
[ margin_hi OB K
| bato 716792; astep; chk_merge OB 4; astep; margin_hi OB K ].

Section S.
Variables (OLD NEW IQ usp lo : Z) (n : nat).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation len := (Z.of_nat n).
Hypothesis N3 : 3 <= len < 2^31.
Hypothesis OBO : aobj bsegs m OLD (4 * len).
Hypothesis OBN : aobj bsegs m NEW (4 * len).
Hypothesis OBQ : aobj bsegs m IQ (4 * len).
Hypothesis O4 : OLD mod 4 = 0.
Hypothesis NW4 : NEW mod 4 = 0.
Hypothesis Q4 : IQ mod 4 = 0.
Hypothesis OPOS : 0 < OLD.
Hypothesis NPOS : 0 < NEW.
Hypothesis QPOS : 0 < IQ.
Hypothesis LO : lo <= usp - 64.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis QSH : IQ + 4 * len <= SH_LO \/ SH_HI <= IQ.
Hypothesis QAP : IQ + 4 * len <= lo \/ usp <= IQ.
Hypothesis OAP : OLD + 4 * len <= lo \/ usp <= OLD.
Hypothesis NAP : NEW + 4 * len <= lo \/ usp <= NEW.
Hypothesis SEPQO : IQ + 4 * len <= OLD \/ OLD + 4 * len <= IQ.
Hypothesis SEPQN : IQ + 4 * len <= NEW \/ NEW + 4 * len <= IQ.
Local Notation POST := (lsp_interpolate_postA ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo IQ n m).
Local Notation W := [(IQ, IQ + 4 * len); (usp + -64, usp)].
Local Notation FRB j0 := [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation NB := (Z_to_bv 64 (18446744073709551615 - IQ)).

Lemma margin_loop : forall (rest done : list word) (off kz : Z) (pw cw nw : word) (j0 : list byte)
(wa2 wa3 wa4 wa5 t0 t1 t2 ys0 ys1 a0 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
wa2 = Z_to_bv 64 (IQ + off + -4) -> wa3 = Z_to_bv 64 (IQ + off) -> wa4 = Z_to_bv 64 kz -> wa5 = Z_to_bv 64 (off + 4) ->
kz = Z.of_nat (S (length rest)) -> (length done + 3 + length rest = n)%nat -> off = 4 + 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) (FRB j0) ->
rw_cells bsegs mc IQ (f32 done) -> rw_cells bsegs mc (IQ + off + -4) (f32 [pw]) -> rw_cells bsegs mc (IQ + off) (f32 (cw :: nw :: rest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 ys0 ys1 a0 NB wa2 wa3 wa4 wa5 a6 (Z_to_bv 64 SHB)
ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 716712) fc None mc (seg_rom bsegs)).
Proof using N3 OBQ Q4 QPOS LO SPH QSH QAP.
clear OBO OBN O4 NW4 OPOS NPOS OAP NAP SEPQO SEPQN LOS.
induction rest as [|nw' rest IH]; intros done off kz pw cw nw j0 wa2 wa3 wa4 wa5 t0 t1 t2 ys0 ys1 a0 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 G fc mc
E2 E3 E4 E5 Hkz HN Hoff FRM MU OF WM MI ST FR DONE PREV CUR;
subst wa2 wa3 wa4 wa5;
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
rewrite !f32_cons, ?f32_nil in CUR; rewrite f32_cons, f32_nil in PREV; subst kz;
hide_disj.
-
cbn [length] in HN.
assert (TAIL : forall (y0 y2 yt0 yt1 yt2 : word) (G' : bvmap 5 word) fc' m' (cw' : word),
frm0 fc' -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
stk bsegs m' lo (usp + -64) -> rw_cells bsegs m' (usp + -64) (FRB j0) ->
rw_cells bsegs m' IQ (f32 done) -> rw_cells bsegs m' (IQ + off + -4) [C4 pw] -> rw_cells bsegs m' (IQ + off) [C4 cw'; C4 nw] ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp yt0 yt1 yt2 ys0 ys1 y0 NB y2 (Z_to_bv 64 (IQ + off)) (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 (off + 4))
(Z_to_bv 64 (IQ + off)) (Z_to_bv 64 SHB) ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xaf058) fc' None m' (seg_rom bsegs))).
{ clear FRM MU WM MI ST FR DONE PREV CUR STa STb fc mc. intros y0 y2 yt0 yt1 yt2 G' fc m1 cw' FRM MU WM MI ST FR DONE PREV CUR.
pose proof ST as (STa & STb & _).
bato 0xaf068. astep. cbn [length]. try sh_if.
bato 0xaf0ec. release_frame FR ST usp. astep. astep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE.
chunk_uncons CUR as C1. replace (IQ + off + -4 + 4) with (IQ + off) in DONE by lia. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
replace (IQ + off + 4) with (IQ + off + -4 + 4 + 4) in CUR by lia. chunk_snoc DONE CUR. rewrite f32_snoc in DONE.
unfold lsp_interpolate_postA, LSPI_DEPTH. finish; [ exact DONE | ].
rewrite !length_app. cbn [length]. lia. }
margin_iter OBQ TAIL.
-
cbn [length] in HN, BC.
assert (TAIL : forall (y0 y2 yt0 yt1 yt2 : word) (G' : bvmap 5 word) fc' m' (cw' : word),
frm0 fc' -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
stk bsegs m' lo (usp + -64) -> rw_cells bsegs m' (usp + -64) (FRB j0) ->
rw_cells bsegs m' IQ (f32 done) -> rw_cells bsegs m' (IQ + off + -4) [C4 pw] -> rw_cells bsegs m' (IQ + off) (C4 cw' :: C4 nw :: C4 nw' :: f32 rest) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp yt0 yt1 yt2 ys0 ys1 y0 NB y2 (Z_to_bv 64 (IQ + off)) (Z_to_bv 64 (Z.of_nat (S (length (nw' :: rest))))) (Z_to_bv 64 (off + 4))
(Z_to_bv 64 (IQ + off)) (Z_to_bv 64 SHB) ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xaf058) fc' None m' (seg_rom bsegs))).
{ clear FRM MU WM MI ST FR DONE PREV CUR STa STb fc mc. intros y0 y2 yt0 yt1 yt2 G' fc m1 cw' FRM MU WM MI ST FR DONE PREV CUR.
pose proof ST as (STa & STb & _).
bato 0xaf068. astep. cbn [length]. sh_if.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE.
chunk_uncons CUR as C1.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (IQ + off) with (IQ + (off + 4) + -4) in C1 by lia.
replace (IQ + off + 4) with (IQ + (off + 4)) in CUR by lia.
rewrite <- !f32_cons in CUR. rewrite <- f32_nil, <- f32_cons in C1.
eapply (IH (done ++ [pw]) (off + 4) (Z.of_nat (S (length rest)))); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite !length_app; cbn [length]; lia). }
margin_iter OBQ TAIL.
Qed.

Lemma tail2 : forall (qs : list word) (j0 : list byte) (t0 t1 t2 ys0 ys1 a0 a1 a3 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) (FRB j0) ->
rw_cells bsegs mc IQ (f32 qs) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 ys0 ys1 a0 a1 (Z_to_bv 64 IQ) a3 (Z_to_bv 64 (len + -1)) a5 a6 (Z_to_bv 64 SHB)
ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 716680) fc None mc (seg_rom bsegs)).
Proof using N3 OBQ Q4 QPOS LO SPH QSH QAP.
clear OBO OBN O4 NW4 OPOS NPOS OAP NAP SEPQO SEPQN LOS.
intros qs j0 t0 t1 t2 ys0 ys1 a0 a1 a3 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 rest]]]; try (cbn [length] in LQ; lia). cbn [length] in LQ.
bato 716712. bnorm.
chunk_split_f32 X at 1%nat as C0.
eapply (margin_loop rest [] 4 (Z.of_nat (S (length rest))) q0 q1 q2); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (cbn [length]; lia).
- apply rw_cells_nil. lia.
- replace (IQ + 4 + -4) with IQ by lia. exact C0.
Qed.

Lemma tail1 : forall (qs : list word) (j0 : list byte) (t0 t1 t2 ys0 ys1 a0 a1 a4 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) (FRB j0) ->
rw_cells bsegs mc IQ (f32 qs) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 ys0 ys1 a0 a1 (Z_to_bv 64 IQ) (Z_to_bv 64 len) a4 a5 a6 (Z_to_bv 64 SHB)
ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 716576) fc None mc (seg_rom bsegs)).
Proof using N3 OBQ Q4 QPOS LO SPH QSH QAP.
clear OBO OBN O4 NW4 OPOS NPOS OAP NAP SEPQO SEPQN LOS.
intros qs j0 t0 t1 t2 ys0 ys1 a0 a1 a4 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct (exists_last (l := qs)) as (qi & ql & E); [intros ->; cbn [length] in LQ; lia|].
assert (LQI : Z.of_nat (length qi) = len - 1) by (rewrite E, length_app in LQ; cbn [length] in LQ; lia).
rewrite E, f32_app in X. apply rw_cells_app in X. destruct X as [QI QL]. rewrite cells_size_f32 in QL.
hide_disj.
replace (IQ + Z.of_nat (4 * length qi)) with (IQ + (len + -1) * 4) in QL by lia. rewrite f32_cons, f32_nil in QL.
bato 716616. bnorm.
bato 716628. astep. chk_merge OBQ 4.
bato 716660. astep. let B := fresh "B" in if_cases B.
- bato 716680.
chunk_snoc QI QL. rewrite f32_snoc in QI.
eapply (tail2 (qi ++ [ql])); try eassumption. rewrite <- E. exact LQ.
- bato 716668. astep. chk_merge OBQ 4.
bato 716680.
chunk_snoc QI QL. rewrite f32_snoc in QI.
eapply (tail2 (qi ++ [_])); try eassumption. rewrite length_app. cbn [length]. lia.
Qed.

Lemma tail0 : forall (qs : list word) (j0 : list byte) (t1 t2 ys0 ys1 a0 a1 a4 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) (FRB j0) ->
rw_cells bsegs mc IQ (f32 qs) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 0) t1 t2 ys0 ys1 a0 a1 (Z_to_bv 64 IQ) (Z_to_bv 64 len) a4 a5 a6 (Z_to_bv 64 SHB)
ys2 ys3 ys4 ys5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xaeef0) fc None mc (seg_rom bsegs)).
Proof using N3 OBQ Q4 QPOS LO SPH QSH QAP.
clear OBO OBN O4 NW4 OPOS NPOS OAP NAP SEPQO SEPQN LOS.
intros qs j0 t1 t2 ys0 ys1 a0 a1 a4 a5 a6 ys2 ys3 ys4 ys5 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 qt]; [cbn [length] in LQ; lia|]. cbn [length] in LQ.
rewrite f32_cons in X. chunk_uncons X as Q0.
hide_disj.
bato 716548. astep. chk_merge OBQ 4.
bato 716560. astep. let B := fresh "B" in if_cases B.
- bato 716576.
rewrite <- f32_nil, <- f32_cons in Q0. chunk_cat Q0 X. rewrite <- f32_app in Q0. cbn [app] in Q0.
eapply (tail1 (q0 :: qt)); try eassumption. all: try (cbn [length]; lia).
- bato 716568. astep. chk_merge OBQ 4.
bato 716576.
rewrite <- f32_nil, <- f32_cons in Q0. chunk_cat Q0 X. rewrite <- f32_app in Q0. cbn [app] in Q0.
eapply (tail1 (_ :: qt)); try eassumption. all: try (cbn [length]; lia).
Qed.

Lemma interp_loop : forall (qrest orest nrest done : list word) (off kz : Z) (qw ow nw : word) (j0 : list byte)
(ws0 ws1 wa4 wa5 wa6 ws2 ws3 ys4 ys5 : word) (G : bvmap 5 word) fc mc,
ws0 = Z_to_bv 64 kz -> ws1 = Z_to_bv 64 (OLD + off) -> wa4 = Z_to_bv 64 (IQ + off) -> wa5 = Z_to_bv 64 (NEW + off) -> wa6 = Z_to_bv 64 (OLD + off) ->
ws2 = Z_to_bv 64 (NEW + off) -> ws3 = Z_to_bv 64 (IQ + off) ->
length orest = length qrest -> length nrest = length qrest -> (length done + 1 + length qrest = n)%nat ->
kz = Z.of_nat (S (length qrest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -64) -> rw_cells bsegs mc (usp + -64) (FRB j0) ->
rw_cells bsegs mc IQ (f32 done) -> rw_cells bsegs mc (IQ + off) (f32 (qw :: qrest)) ->
rw_cells bsegs mc (OLD + off) (f32 (ow :: orest)) -> rw_cells bsegs mc (NEW + off) (f32 (nw :: nrest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) ws0 ws1
(Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 len) wa4 wa5 wa6 (Z_to_bv 64 SHB)
ws2 ws3 ys4 ys5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1))
G (Z_to_bv 64 0xaee18) fc None mc (seg_rom bsegs)).
Proof using N3 OBO OBN OBQ O4 NW4 Q4 OPOS NPOS QPOS LO SPH QSH QAP OAP NAP SEPQO SEPQN.
clear LOS.
induction qrest as [|qw' qrest IH]; intros orest nrest done off kz qw ow nw j0 ws0 ws1 wa4 wa5 wa6 ws2 ws3 ys4 ys5 G fc mc
E0 E1 E4 E5 E6 E2 E3 LOR LNR HN Hkz Hoff FRM MU OF WM MI ST FR DONE X O N;
subst ws0 ws1 wa4 wa5 wa6 ws2 ws3;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBO as (OO0 & OO1 & _); pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32 in BO; cbn [length] in BO;
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32 in BN; cbn [length] in BN;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz; hide_disj.
- destruct orest; [|cbn [length] in LOR; lia]. destruct nrest; [|cbn [length] in LNR; lia]. cbn [length] in HN, BX, BO, BN.
rewrite f32_cons, f32_nil in X. rewrite f32_cons, f32_nil in O. rewrite f32_cons, f32_nil in N.
bato 0xaee38. astep. chk_merge OBO 4.
bato 0xaee60. astep. chk_merge OBN 4.
bato 0xaee88. astep. chk_merge OBQ 4.
bato 0xaeeb4. astep. cbn [length]. try sh_if.
bato 0xaeef0.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
eapply (tail0 (done ++ [_])); try eassumption.
rewrite length_app. cbn [length]. lia.
- destruct orest as [|ow' orest]; [cbn [length] in LOR; lia|]. destruct nrest as [|nw' nrest]; [cbn [length] in LNR; lia|].
cbn [length] in LOR, LNR, HN, BX, BO, BN.
chunk_split_f32 O at 1%nat as O1. rewrite ?f32_cons, ?f32_nil in O1.
chunk_split_f32 N at 1%nat as N1. rewrite ?f32_cons, ?f32_nil in N1.
rewrite f32_cons in X. chunk_uncons X as X1.
bato 0xaee38. astep. chk_merge OBO 4.
bato 0xaee60. astep. chk_merge OBN 4.
bato 0xaee88. astep. chk_merge OBQ 4.
bato 0xaeeb4. astep. cbn [length]. sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (IQ + off + 4) with (IQ + (off + 4)) in * by lia.
replace (OLD + off + 4) with (OLD + (off + 4)) in * by lia.
replace (NEW + off + 4) with (NEW + (off + 4)) in * by lia.
clear O1 N1.
eapply (IH orest nrest (done ++ [_]) (off + 4) (Z.of_nat (S (length qrest)))); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Lemma lsp_interpolate_walk : forall (os ns qs : list word) (sub : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells bsegs m OLD (f32 os) -> length os = n -> rw_cells bsegs m NEW (f32 ns) -> length ns = n ->
rw_cells bsegs m IQ (f32 qs) -> length qs = n -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= IQ ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 len) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom bsegs)).
Proof using N3 OBO OBN OBQ O4 NW4 Q4 OPOS NPOS QPOS LO LOS SPH QSH QAP OAP NAP SEPQO SEPQN.
intros os ns qs sub t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc O LOs N LNs X LQ FRM ST PTOP (G1 & G2 & _) MI.
unfold A_lsp_interpolate, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof QSH as QSH'. unfold SH_LO, SH_HI in QSH'. unfold IMG_TOP_B in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32, LOs in BO.
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32, LNs in BN.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct qs as [|q0 qrest]; [cbn [length] in LQ; lia|]. destruct os as [|o0 orest]; [cbn [length] in LOs; lia|]. destruct ns as [|n0 nrest]; [cbn [length] in LNs; lia|].
cbn [length] in LQ, LOs, LNs.
hide_disj.
carve_frame 64%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xaee18. rewrite ?(land3_al IQ Q4), ?(land3_al OLD O4), ?(land3_al NEW NW4). bdec.
replace IQ with (IQ + 0) in X at 1 by lia. replace OLD with (OLD + 0) in O at 1 by lia. replace NEW with (NEW + 0) in N at 1 by lia.
eapply (interp_loop qrest orest nrest [] 0 len); try eassumption; try reflexivity.
all: try (f_equal; lia).
all: try (cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End S.

Lemma lsp_interpolate_stmt : lsp_interpolate_stmtA.
Proof.
intros OLD NEW IQ usp lo sub n os ns qs ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
N3 OBO OBN OBQ O4 NW4 Q4 OPOS NPOS O LOs N LNs X LQ QSH PTOP QAP OAP NAP SEPQO SEPQN CC ST LO LOS SPH MI FRM.
unfold hidp, LSPI_DEPTH in *.
assert (QPOS : 0 < IQ) by (unfold IMG_TOP_B in PTOP; lia).
eapply lsp_interpolate_walk; eassumption.
Qed.
