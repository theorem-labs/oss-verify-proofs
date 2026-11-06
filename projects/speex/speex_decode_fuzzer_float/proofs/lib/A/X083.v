(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X082.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= tlia_one.
Local Notation mem := (word -> option byte).

Ltac margin_leaf K := eapply K; eassumption.
Ltac margin_hi OB K :=
ato 0xa9d8c; astep; chk_merge OB 4;
ato 0xa9da4; astep; chk_merge OB 4;
ato 0xa9db4; astep; let B2 := fresh "B2" in if_cases B2;
[ ato 0xa9ddc; margin_leaf K
| ato 0xa9dc8; astep; chk_merge OB 4; ato 0xa9ddc; margin_leaf K ].
Ltac margin_iter OB K :=
astep;
ato 0xa9d48; astep; chk_merge OB 4;
ato 0xa9d5c; astep; chk_merge OB 4;
ato 0xa9d6c; astep; let B1 := fresh "B1" in if_cases B1;
[ margin_hi OB K
| ato 0xa9d80; astep; chk_merge OB 4; astep; margin_hi OB K ].

Section S.
Variables (OLD NEW IQ usp lo : Z) (n : nat).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation len := (Z.of_nat n).
Hypothesis N3 : 3 <= len < 2^31.
Hypothesis OBO : aobj asegs m OLD (4 * len).
Hypothesis OBN : aobj asegs m NEW (4 * len).
Hypothesis OBQ : aobj asegs m IQ (4 * len).
Hypothesis O4 : OLD mod 4 = 0.
Hypothesis NW4 : NEW mod 4 = 0.
Hypothesis Q4 : IQ mod 4 = 0.
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

Lemma margin_loop : forall (rest done : list word) (off kz : Z) (pw cw nw : word) (j0 : list byte)
(t0 t1 t2 a0 a4 a5 a6 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
kz = Z.of_nat (S (length rest)) -> (length done + 3 + length rest = n)%nat -> off = 4 + 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc IQ (f32 done) -> rw_cells asegs mc (IQ + off + -4) (f32 [pw]) -> rw_cells asegs mc (IQ + off) (f32 (cw :: nw :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (IQ + off)) (Z_to_bv 64 (IQ + off + -4)) (Z_to_bv 64 kz) a4 a5 a6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa9d38) fc None mc (seg_rom asegs)).
Proof using N3 OBQ Q4 LO SPH QSH QAP.
clear OBO OBN O4 NW4 OAP NAP SEPQO SEPQN LOS.
induction rest as [|nw' rest IH]; intros done off kz pw cw nw j0 t0 t1 t2 a0 a4 a5 a6 t3 t4 t5 t6 G fc mc Hkz HN Hoff FRM MU OF WM MI ST FR DONE PREV CUR;
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ CUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
rewrite !f32_cons, ?f32_nil in CUR; rewrite f32_cons, f32_nil in PREV; subst kz;
hide_disj.
-
cbn [length] in HN.
assert (TAIL : forall (y0 y2 y5 y6 yt0 : word) (G' : bvmap 5 word) fc' m' (cw' : word),
frm0 fc' -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' IQ (f32 done) -> rw_cells asegs m' (IQ + off + -4) [C4 pw] -> rw_cells asegs m' (IQ + off) [C4 cw'; C4 nw] ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp yt0 t1 t2 s0 s1 y0 (Z_to_bv 64 (IQ + off)) y2 (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 (IQ + off)) y5 y6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa9ddc) fc' None m' (seg_rom asegs))).
{ clear FRM MU WM MI ST FR DONE PREV CUR STa STb fc mc. intros y0 y2 y5 y6 yt0 G' fc m1 cw' FRM MU WM MI ST FR DONE PREV CUR.
pose proof ST as (STa & STb & _).
ato 0xa9de8. astep. cbn [length]. try sh_if.
ato 0xa9e50. astep. release_frame FR ST usp. astep. astep.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE.
chunk_uncons CUR as C1. replace (IQ + off + -4 + 4) with (IQ + off) in DONE by lia. chunk_snoc DONE C1. rewrite f32_snoc in DONE.
replace (IQ + off + 4) with (IQ + off + -4 + 4 + 4) in CUR by lia. chunk_snoc DONE CUR. rewrite f32_snoc in DONE.
unfold lsp_interpolate_postA, LSPI_DEPTH. finish; [ exact DONE | ].
rewrite !length_app. cbn [length]. lia. }
margin_iter OBQ TAIL.
-
cbn [length] in HN, BC.
assert (TAIL : forall (y0 y2 y5 y6 yt0 : word) (G' : bvmap 5 word) fc' m' (cw' : word),
frm0 fc' -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' IQ (f32 done) -> rw_cells asegs m' (IQ + off + -4) [C4 pw] -> rw_cells asegs m' (IQ + off) (C4 cw' :: C4 nw :: C4 nw' :: f32 rest) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp yt0 t1 t2 s0 s1 y0 (Z_to_bv 64 (IQ + off)) y2 (Z_to_bv 64 (Z.of_nat (S (length (nw' :: rest))))) (Z_to_bv 64 (IQ + off)) y5 y6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa9ddc) fc' None m' (seg_rom asegs))).
{ clear FRM MU WM MI ST FR DONE PREV CUR STa STb fc mc. intros y0 y2 y5 y6 yt0 G' fc m1 cw' FRM MU WM MI ST FR DONE PREV CUR.
pose proof ST as (STa & STb & _).
ato 0xa9de8. astep. cbn [length]. sh_if.
chunk_snoc DONE PREV. rewrite f32_snoc in DONE.
chunk_uncons CUR as C1.
replace (Z.of_nat (S (S (length rest))) + -1) with (Z.of_nat (S (length rest))) by lia.
replace (Z_to_bv 64 (IQ + off + 4)) with (Z_to_bv 64 (IQ + (off + 4))) by (f_equal; lia).
replace (Z_to_bv 64 (IQ + off)) with (Z_to_bv 64 (IQ + (off + 4) + -4)) by (f_equal; lia).
replace (IQ + off) with (IQ + (off + 4) + -4) in C1 by lia.
replace (IQ + off + 4) with (IQ + (off + 4)) in CUR by lia.
rewrite <- !f32_cons in CUR. rewrite <- f32_nil, <- f32_cons in C1.
eapply (IH (done ++ [pw]) (off + 4)); try eassumption; try reflexivity.
all: try (rewrite !length_app; cbn [length]; lia). }
margin_iter OBQ TAIL.
Qed.

Lemma tail2 : forall (qs : list word) (j0 : list byte) (t0 t1 t2 a0 a4 a5 a6 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc IQ (f32 qs) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (len + -1)) (Z_to_bv 64 IQ) (Z_to_bv 64 len) a4 a5 a6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa9d18) fc None mc (seg_rom asegs)).
Proof using N3 OBQ Q4 LO SPH QSH QAP.
clear OBO OBN O4 NW4 OAP NAP SEPQO SEPQN LOS.
intros qs j0 t0 t1 t2 a0 a4 a5 a6 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 [|q1 [|q2 rest]]]; try (cbn [length] in LQ; lia). cbn [length] in LQ.
astep. astep. sh_if.
ato 0xa9d38.
rewrite ?(Z.mod_small (len + -1) 4294967296) by lia.
chunk_split_f32 X at 1%nat as C0.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR _ _ _ _ ?xt0 _ _ _ _ ?xa0 _ _ _ ?xa4 ?xa5 ?xa6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
replace R with (mkR ra (Z_to_bv 64 (usp + -16)) gp tp xt0 t1 t2 s0 s1 xa0 (Z_to_bv 64 (IQ + 4)) (Z_to_bv 64 (IQ + 4 + -4))
(Z_to_bv 64 (Z.of_nat (S (length rest)))) xa4 xa5 xa6 (Z_to_bv 64 SHB) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
by (replace (IQ + 4 + -4) with IQ by lia; replace (Z.of_nat (S (length rest))) with (len + -1 + -1) by lia; reflexivity)
end
end.
eapply (margin_loop rest [] 4 _ q0 q1 q2); try eassumption; try reflexivity.
all: try (cbn [length]; lia).
- apply rw_cells_nil. lia.
- replace (IQ + 4 + -4) with IQ by lia. exact C0.
Qed.

Lemma tail1 : forall (qs : list word) (j0 : list byte) (t0 t1 t2 a0 a1 a4 a5 a6 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc IQ (f32 qs) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 IQ) (Z_to_bv 64 len) a4 a5 a6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa9ccc) fc None mc (seg_rom asegs)).
Proof using N3 OBQ Q4 LO SPH QSH QAP.
clear OBO OBN O4 NW4 OAP NAP SEPQO SEPQN LOS.
intros qs j0 t0 t1 t2 a0 a1 a4 a5 a6 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct (exists_last (l := qs)) as (qi & ql & E); [intros ->; cbn [length] in LQ; lia|].
assert (LQI : Z.of_nat (length qi) = len - 1) by (rewrite E, length_app in LQ; cbn [length] in LQ; lia).
rewrite E, f32_app in X. apply rw_cells_app in X. destruct X as [QI QL]. rewrite cells_size_f32 in QL.
replace (IQ + Z.of_nat (4 * length qi)) with (IQ + 4 * (len - 1)) in QL by lia. rewrite f32_cons, f32_nil in QL.
hide_disj.
astep. rewrite (swrap32_small (len + -1)) by lia.
astep. rewrite ?(Z.mod_small (len + -1) 18446744073709551616) by lia.
replace (Z.shiftl (len + -1) 2) with (4 * (len - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
ato 0xa9ce4. astep. chk_merge OBQ 4. try rename x into xq1.
ato 0xa9d04. astep. let B := fresh "B" in if_cases B.
- ato 0xa9d18.
chunk_snoc QI QL. rewrite f32_snoc in QI.
eapply (tail2 (qi ++ [ql])); try eassumption. rewrite <- E. exact LQ.
- ato 0xa9d0c. astep. chk_merge OBQ 4.
ato 0xa9d18.
chunk_snoc QI QL. rewrite f32_snoc in QI.
eapply (tail2 (qi ++ [_])); try eassumption. rewrite length_app. cbn [length]. lia.
Qed.

Lemma tail0 : forall (qs : list word) (j0 : list byte) (t0 t1 t2 a0 a1 a4 a5 a6 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length qs = n ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc IQ (f32 qs) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 IQ) (Z_to_bv 64 len) a4 a5 a6 (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa9ca4) fc None mc (seg_rom asegs)).
Proof using N3 OBQ Q4 LO SPH QSH QAP.
clear OBO OBN O4 NW4 OAP NAP SEPQO SEPQN LOS.
intros qs j0 t0 t1 t2 a0 a1 a4 a5 a6 t3 t4 t5 t6 G fc mc LQ FRM MU OF WM MI ST FR X.
pose proof OBQ as (OQ0 & OQ1 & _); unfold APP_TOP in *.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
destruct qs as [|q0 qt]; [cbn [length] in LQ; lia|]. cbn [length] in LQ.
rewrite f32_cons in X. chunk_uncons X as Q0.
hide_disj.
ato 0xa9cb0. astep. chk_merge OBQ 4. try rename x into xq0.
ato 0xa9cbc. astep. let B := fresh "B" in if_cases B.
- ato 0xa9ccc.
rewrite <- f32_nil, <- f32_cons in Q0. chunk_cat Q0 X. rewrite <- f32_app in Q0. cbn [app] in Q0.
eapply (tail1 (q0 :: qt)); try eassumption. all: try (cbn [length]; lia).
- ato 0xa9cc4. astep. chk_merge OBQ 4.
ato 0xa9ccc.
rewrite <- f32_nil, <- f32_cons in Q0. chunk_cat Q0 X. rewrite <- f32_app in Q0. cbn [app] in Q0.
eapply (tail1 (_ :: qt)); try eassumption. all: try (cbn [length]; lia).
Qed.

Lemma interp_loop : forall (qrest orest nrest done : list word) (off kz : Z) (qw ow nw : word) (j0 : list byte)
(t2 t3 t4 t5 t6 : word) (G : bvmap 5 word) fc mc,
length orest = length qrest -> length nrest = length qrest -> (length done + 1 + length qrest = n)%nat ->
kz = Z.of_nat (S (length qrest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc IQ (f32 done) -> rw_cells asegs mc (IQ + off) (f32 (qw :: qrest)) ->
rw_cells asegs mc (OLD + off) (f32 (ow :: orest)) -> rw_cells asegs mc (NEW + off) (f32 (nw :: nrest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 kz) (Z_to_bv 64 (IQ + off)) t2 s0 s1
(Z_to_bv 64 (OLD + off)) (Z_to_bv 64 (NEW + off)) (Z_to_bv 64 IQ) (Z_to_bv 64 len) (Z_to_bv 64 (OLD + off)) (Z_to_bv 64 (NEW + off)) (Z_to_bv 64 (IQ + off)) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa9c08) fc None mc (seg_rom asegs)).
Proof using N3 OBO OBN OBQ O4 NW4 Q4 LO SPH QSH QAP OAP NAP SEPQO SEPQN.
clear LOS.
induction qrest as [|qw' qrest IH]; intros orest nrest done off kz qw ow nw j0 t2 t3 t4 t5 t6 G fc mc LOR LNR HN Hkz Hoff FRM MU OF WM MI ST FR DONE X O N;
pose proof OBQ as (OQ0 & OQ1 & _); pose proof OBO as (OO0 & OO1 & _); pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32 in BO; cbn [length] in BO;
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32 in BN; cbn [length] in BN;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
subst kz; hide_disj.
- destruct orest; [|cbn [length] in LOR; lia]. destruct nrest; [|cbn [length] in LNR; lia]. cbn [length] in HN, BX, BO, BN.
rewrite f32_cons, f32_nil in X. rewrite f32_cons, f32_nil in O. rewrite f32_cons, f32_nil in N.
ato 0xa9c14. astep. chk_merge OBO 4. try rename x into xo.
ato 0xa9c28. astep. chk_merge OBN 4. try rename x into xn.
ato 0xa9c3c. astep. chk_merge OBQ 4. try rename x into xq.
ato 0xa9c68. astep. cbn [length]. try sh_if.
ato 0xa9ca4.
chunk_snoc DONE X. rewrite f32_snoc in DONE.
eapply (tail0 (done ++ [_])); try eassumption.
rewrite length_app. cbn [length]. lia.
- destruct orest as [|ow' orest]; [cbn [length] in LOR; lia|]. destruct nrest as [|nw' nrest]; [cbn [length] in LNR; lia|].
cbn [length] in LOR, LNR, HN, BX, BO, BN.
chunk_split_f32 O at 1%nat as O1. rewrite ?f32_cons, ?f32_nil in O1.
chunk_split_f32 N at 1%nat as N1. rewrite ?f32_cons, ?f32_nil in N1.
rewrite f32_cons in X. chunk_uncons X as X1.
ato 0xa9c14. astep. chk_merge OBO 4. try rename x into xo.
ato 0xa9c28. astep. chk_merge OBN 4. try rename x into xn.
ato 0xa9c3c. astep. chk_merge OBQ 4. try rename x into xq.
ato 0xa9c68. astep. cbn [length]. sh_if.
chunk_snoc DONE X1. rewrite f32_snoc in DONE.
replace (Z.of_nat (S (S (length qrest))) + -1) with (Z.of_nat (S (length qrest))) by lia.
replace (IQ + off + 4) with (IQ + (off + 4)) in * by lia.
replace (OLD + off + 4) with (OLD + (off + 4)) in * by lia.
replace (NEW + off + 4) with (NEW + (off + 4)) in * by lia.
clear O1 N1.
eapply (IH orest nrest (done ++ [_]) (off + 4)); try eassumption; try reflexivity.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.

Lemma lsp_interpolate_walk : forall (os ns qs : list word) (sub : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
rw_cells asegs m OLD (f32 os) -> length os = n -> rw_cells asegs m NEW (f32 ns) -> length ns = n ->
rw_cells asegs m IQ (f32 qs) -> length qs = n -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= IQ ->
client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OLD) (Z_to_bv 64 NEW) (Z_to_bv 64 IQ) (Z_to_bv 64 len) (Z_to_bv 64 sub) (Z_to_bv 64 4) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom asegs)).
Proof using N3 OBO OBN OBQ O4 NW4 Q4 LO LOS SPH QSH QAP OAP NAP SEPQO SEPQN.
intros os ns qs sub t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc O LOs N LNs X LQ FRM ST PTOP (G1 & G2 & _) MI.
unfold A_lsp_interpolate, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof QSH as QSH'. unfold SH_LO, SH_HI in QSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LQ in BX.
pose proof (rw_cells_bound _ _ _ _ O) as BO; rewrite cells_size_f32, LOs in BO.
pose proof (rw_cells_bound _ _ _ _ N) as BN; rewrite cells_size_f32, LNs in BN.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct qs as [|q0 qrest]; [cbn [length] in LQ; lia|]. destruct os as [|o0 orest]; [cbn [length] in LOs; lia|]. destruct ns as [|n0 nrest]; [cbn [length] in LNs; lia|].
cbn [length] in LQ, LOs, LNs.
hide_disj.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa9bd4. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa9c08.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.of_nat (S (length qrest)))) (Z_to_bv 64 (IQ + 0)) t2 s0 s1
(Z_to_bv 64 (OLD + 0)) (Z_to_bv 64 (NEW + 0)) (Z_to_bv 64 IQ) (Z_to_bv 64 len) (Z_to_bv 64 (OLD + 0)) (Z_to_bv 64 (NEW + 0)) (Z_to_bv 64 (IQ + 0)) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
by (rewrite !Z.add_0_r; replace (Z.of_nat (S (length qrest))) with len by lia; reflexivity)
end.
replace IQ with (IQ + 0) in X at 1 by lia. replace OLD with (OLD + 0) in O at 1 by lia. replace NEW with (NEW + 0) in N at 1 by lia.
eapply (interp_loop qrest orest nrest [] 0); try eassumption; try reflexivity.
all: try (cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End S.

Lemma lsp_interpolate_stmt : lsp_interpolate_stmtA.
Proof.
intros OLD NEW IQ usp lo sub n os ns qs ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
N3 OBO OBN OBQ O4 NW4 Q4 OPOS NPOS O LOs N LNs X LQ QSH PTOP QAP OAP NAP SEPQO SEPQN CC ST LO LOS SPH MI FRM.
unfold hidp, LSPI_DEPTH in *.
eapply lsp_interpolate_walk; eassumption.
Qed.
