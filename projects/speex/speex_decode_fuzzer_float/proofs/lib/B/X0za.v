(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0wk X0z8 X0z9.
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

Section L1.
Variables (EO XB I1 NE : Z).
Variables rav spv gp tp t2v s0v s1v s8v s9v t3v t4v t5v t6v : word.
Hypothesis E4 : EO mod 4 = 0.
Hypothesis I4 : I1 mod 4 = 0.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis XBR : EO <= XB /\ XB + 320 <= EO + 2000 /\ (XB - EO) mod 4 = 0.
Hypothesis SEPE : NE + 320 <= EO \/ EO + 2000 <= NE.
Hypothesis SEPI : NE + 320 <= I1 \/ I1 + 640 <= NE.
Hypothesis NI : IMG_TOP_B <= NE.
Hypothesis EO0 : 0 < EO.
Hypothesis I10 : 0 < I1.

Definition R1 (i : Z) (a0v a1v a2v : word) : bvmap 5 word :=
mkR rav spv gp tp (Z_to_bv 64 1) (Z_to_bv 64 320) t2v s0v s1v a0v a1v a2v (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 XB) (Z_to_bv 64 640) (Z_to_bv 64 I1) (Z_to_bv 64 320) s8v s9v (Z_to_bv 64 SHB)
(Z_to_bv 64 (18446744073709551615 - I1)) t3v t4v t5v t6v.

Definition l1_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a0' a1' a2' F' fc' m' (ns' : list word),
ms' = MS (R1 80 a0' a1' a2') F' (Z_to_bv 64 0xa9404) fc' None m' (seg_rom bsegs)
/\ munch [(NE, NE + 320)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length ns' = 80%nat /\ rw_cells bsegs m' NE (f32 ns').

Lemma mc_L1 : forall (mI : mem) (rest xr ir jr done : list word) (cw xw iw jw : word) (i : Z) (a0v a1v a2v : word) F1 fc mc,
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 80 -> length xr = length rest -> length ir = length rest -> length jr = length rest ->
aobj bsegs mI EO 2000 -> aobj bsegs mI I1 640 -> aobj bsegs mI NE 320 -> offsh [(NE, NE + 320)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(NE, NE + 320)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (XB + 4 * i) (f32 (xw :: xr)) -> rw_cells bsegs mc (I1 + 4 * i) (f32 (iw :: ir)) -> rw_cells bsegs mc (I1 + 320 + 4 * i) (f32 (jw :: jr)) ->
rw_cells bsegs mc NE (f32 done) -> rw_cells bsegs mc (NE + 4 * i) (f32 (cw :: rest)) ->
evt bsegs (l1_post mI) (MS (R1 i a0v a1v a2v) F1 (Z_to_bv 64 0xa9304) fc None mc (seg_rom bsegs)).
Proof using E4 I4 N4 XBR SEPE SEPI NI EO0 I10.
intros mI rest.
induction rest as [|cw' rest IH]; intros xr ir jr done cw xw iw jw i a0v a1v a2v F1 fc mc Hi HN LX LI LJ OBE OBI OBN OF FRM MI MU WM XX XI XJ XD XC;
pose proof OBE as (OE0 & OE1 & _); pose proof OBI as (OI0 & OI1 & _); pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *;
pose proof NI as NI'; unfold IMG_TOP_B in NI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold R1; rewrite !f32_cons in XC; cbn [length] in *;
hide_disj.
- destruct xr; [|cbn in LX; lia]. destruct ir; [|cbn in LI; lia]. destruct jr; [|cbn in LJ; lia]. rewrite f32_nil in XC.
pose proof XX as X1h. pose proof XI as I1h. pose proof XJ as J1h. rewrite f32_cons, f32_nil in X1h, I1h, J1h.
replace (XB + 4 * i) with (EO + (XB - EO + 4 * i)) in * by lia.
assert (A1 : (EO + (XB - EO + 4 * i)) mod 4 = 0) by (clear - E4 XBR; Z.div_mod_to_equations; lia).
ato 0xa9308. replace (XB + 4 * i) with (EO + (XB - EO + 4 * i)) by lia.
bato 0xa9324.
astep. chk_merge OBE 4.
bato 0xa9344. astep. chk_merge OBI 4.
bato 0xa935c.
rewrite swrap32_small by lia. rewrite Z.add_0_r.
bato 0xa9368. replace (I1 + Z.shiftl (i + 80) 2) with (I1 + 320 + 4 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (I1 + (i + 80) * 4) with (I1 + 320 + 4 * i) by lia.
bato 0xa9378. astep. chk_merge OBI 4.
bato 0xa93a0. astep. chk_merge OBN 4.
clear X1h I1h J1h XX XI XJ.
bato 0xa93bc. rewrite swrap32_small by lia. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (4 * i + 4) with (4 * 80) by lia. replace (i + 1) with 80 by lia.
unfold l1_post, R1. finish; [ | exact XD ]. rewrite length_app. cbn [length]. lia.
- destruct xr as [|xw' xr]; [cbn in LX; lia|]. destruct ir as [|iw' ir]; [cbn in LI; lia|]. destruct jr as [|jw' jr]; [cbn in LJ; lia|]. cbn [length] in LX, LI, LJ.
pose proof XX as X1h. chunk_split_f32 X1h at 1%nat as X1c. rewrite ?f32_cons, ?f32_nil in X1c. clear X1h.
pose proof XI as I1h. chunk_split_f32 I1h at 1%nat as I1c. rewrite ?f32_cons, ?f32_nil in I1c. clear I1h.
pose proof XJ as J1h. chunk_split_f32 J1h at 1%nat as J1c. rewrite ?f32_cons, ?f32_nil in J1c. clear J1h.
replace (XB + 4 * i) with (EO + (XB - EO + 4 * i)) in X1c by lia.
assert (A1 : (EO + (XB - EO + 4 * i)) mod 4 = 0) by (clear - E4 XBR; Z.div_mod_to_equations; lia).
ato 0xa9308. replace (XB + 4 * i) with (EO + (XB - EO + 4 * i)) by lia.
bato 0xa9324. astep. chk_merge OBE 4.
bato 0xa9344. astep. chk_merge OBI 4.
bato 0xa935c. rewrite swrap32_small by lia. rewrite Z.add_0_r.
bato 0xa9368. replace (I1 + (i + 80) * 4) with (I1 + 320 + 4 * i) by lia.
bato 0xa9378. astep. chk_merge OBI 4.
bato 0xa93a0. astep. chk_merge OBN 4.
clear X1c I1c J1c.
bato 0xa93bc. rewrite swrap32_small by lia. astep. sh_if.
apply rw_f32_uncons in XX. apply rw_f32_uncons in XI. apply rw_f32_uncons in XJ.
chunk_uncons XC as C1c. chunk_snoc XD C1c. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (4 * i + 4) with (4 * (i + 1)) by lia.
replace (XB + 4 * i + 4) with (XB + 4 * (i + 1)) in XX by lia. replace (I1 + 4 * i + 4) with (I1 + 4 * (i + 1)) in XI by lia.
replace (I1 + 320 + 4 * i + 4) with (I1 + 320 + 4 * (i + 1)) in XJ by lia. replace (NE + 4 * i + 4) with (NE + 4 * (i + 1)) in XC by lia.
eapply (IH xr ir jr _ cw' xw' iw' jw' (i + 1)); try eassumption;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End L1.

Section L2.
Variables (NE : Z).
Variables rav spv gp tp t0v t1v t2v s0v s1v a6v a7v s3v s4v s5v s6v s7v s8v s9v s11v t3v t4v t5v t6v : word.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis NI : IMG_TOP_B <= NE.
Hypothesis N0 : 0 < NE.
Definition R2 (na cnt : Z) (a4v a5v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 na) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 na) a4v a5v a6v a7v
(Z_to_bv 64 cnt) (Z_to_bv 64 NE) s4v s5v s6v s7v s8v s9v (Z_to_bv 64 SHB) s11v t3v t4v t5v t6v.
Definition l2_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a4' a5' F' fc' m' (ns' : list word),
ms' = MS (R2 (NE + 320) 0 a4' a5') F' (Z_to_bv 64 0xa94c4) fc' None m' (seg_rom bsegs)
/\ munch [(NE, NE + 320)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ length ns' = 80%nat /\ rw_cells bsegs m' NE (f32 ns').
Lemma mc_L2 : forall (mI : mem) (rest done : list word) (cw : word) (i na cnt : Z) (a4v a5v : word) F1 fc mc,
na = NE + 4 * i -> cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 80 ->
aobj bsegs mI NE 320 -> offsh [(NE, NE + 320)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(NE, NE + 320)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc NE (f32 done) -> rw_cells bsegs mc na (f32 (cw :: rest)) ->
evt bsegs (l2_post mI) (MS (R2 na cnt a4v a5v) F1 (Z_to_bv 64 0xa9470) fc None mc (seg_rom bsegs)).
Proof using N4 NI N0.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i na cnt a4v a5v F1 fc mc -> -> Hi HN OBN OF FRM MI MU WM XD XC;
pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *; pose proof NI as NI'; unfold IMG_TOP_B in NI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold R2; rewrite !f32_cons in XC; cbn [length] in *.
- rewrite f32_nil in XC.
bato 0xa9490. astep. chk_merge OBN 4.
bato 0xa94ac. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (NE + 4 * i + 4) with (NE + 320) by lia. replace (1 + Z.of_nat 0 + -1) with 0 by lia.
unfold l2_post, R2. finish; [ | exact XD ]. rewrite length_app. cbn [length]. lia.
- bato 0xa9490. astep. chk_merge OBN 4.
bato 0xa94ac. astep. sh_if.
chunk_uncons XC as C1c. chunk_snoc XD C1c. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End L2.

Section Tail.
Variables (EO XB I1 I2 NE pitch usp lo : Z).
Variables gp tp : word.
Hypothesis HI1 : I1 = usp + -896.
Hypothesis HI2 : I2 = I1 + 320.
Hypothesis XBR : EO <= XB /\ XB + 320 <= EO + 2000.
Hypothesis E4 : EO mod 4 = 0.
Hypothesis X4 : XB mod 4 = 0.
Hypothesis I4 : I1 mod 4 = 0.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis SEPE : NE + 320 <= EO \/ EO + 2000 <= NE.
Hypothesis SEPI : NE + 320 <= I1 \/ I1 + 640 <= NE.
Hypothesis NI : IMG_TOP_B <= NE.
Hypothesis NSH : NE + 320 <= SH_LO \/ SH_HI <= NE.
Hypothesis EO0 : 0 < EO.
Hypothesis NE0 : 0 < NE /\ NE + 320 < 2^62.
Hypothesis NLO : NE + 320 <= lo.
Hypothesis XLO : XB + 320 <= lo.

Definition tail_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -928)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -224)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SHB) s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa94c4) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -944, usp + -928); (NE, NE + 320)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ stk bsegs m' lo (usp + -928)
/\ length ns' = 80%nat /\ rw_cells bsegs m' NE (f32 ns').

Lemma mc_tail : forall (xw i1 i2 ns : list word) (ra t2 a0 a1 a2 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length xw = 80%nat -> length i1 = 80%nat -> length i2 = 80%nat -> length ns = 80%nat ->
rw_cells bsegs m XB (f32 xw) -> rw_cells bsegs m I1 (f32 i1) -> rw_cells bsegs m I2 (f32 i2) -> rw_cells bsegs m NE (f32 ns) ->
aobj bsegs m EO 2000 -> aobj bsegs m I1 640 -> aobj bsegs m NE 320 ->
stk bsegs m lo (usp + -928) -> lo <= usp - 4320 -> SH_HI <= lo -> usp < 2^63 ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (tail_post m)
(MS (RMID XB I1 NE pitch usp gp tp ra (Z_to_bv 64 1) (Z_to_bv 64 320) t2 a0 a1 a2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0) t3 t4 t5 t6)
G (Z_to_bv 64 0xa9304) fc None m (seg_rom bsegs)).
Proof using HI1 HI2 XBR E4 X4 I4 N4 SEPE SEPI NI NSH EO0 NE0 NLO XLO.
intros xw i1 i2 ns ra t2 a0 a1 a2 t3 t4 t5 t6 G fc m LXW LI1 LI2 LNS XX XI1 XI2 XN OBE OBI OBN ST LO LOS SPH CC MI FRM.
unfold RMID.
pose proof OBE as (OE0 & OE1 & _). pose proof OBI as (OI0 & OI1 & _). pose proof OBN as (ON0 & ON1 & _). unfold APP_TOP in *.
pose proof NI as NI'. unfold IMG_TOP_B in NI'. pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof (munch_refl [(usp + -944, usp + -928); (NE, NE + 320)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -944, usp + -928); (NE, NE + 320)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (OFN : offsh [(NE, NE + 320)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (XBR' : EO <= XB /\ XB + 320 <= EO + 2000 /\ (XB - EO) mod 4 = 0) by (clear - XBR E4 X4; Z.div_mod_to_equations; lia).
assert (I10 : 0 < I1) by lia.
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in G1, G2, G3, G4. clear CC.
destruct xw as [|xw0 xwr]; [cbn in LXW; lia|]. destruct i1 as [|iw0 i1r]; [cbn in LI1; lia|]. destruct i2 as [|jw0 i2r]; [cbn in LI2; lia|].
destruct ns as [|nw0 nsr]; [cbn in LNS; lia|]. cbn [length] in LXW, LI1, LI2, LNS.

lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(NE, NE + 320)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc NE (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof XX as XX0; replace XB with (XB + 4 * 0) in XX0 at 1 by lia;
pose proof XI1 as XI0; replace I1 with (I1 + 4 * 0) in XI0 at 1 by lia;
pose proof XI2 as XJ0; rewrite HI2 in XJ0; replace (I1 + 320) with (I1 + 320 + 4 * 0) in XJ0 at 1 by lia;
pose proof XN as XN0; replace NE with (NE + 4 * 0) in XN0 at 1 by lia;
callc (mc_L1 EO XB I1 NE _ _ _ _ _ _ _ _ _ _ _ _ _ E4 I4 N4 XBR' SEPE SEPI NI EO0 I10 mc nsr xwr i1r i2r [] nw0 xw0 iw0 jw0 0 _ _ _ _ _ mc)
(clear XN XN0 XD0);
[ reflexivity | lia | lia | lia | lia | exact OBE | exact OBI | exact OBN | exact OFN
| exact FRM | exact MI | exact MU0 | exact WM0 | exact XX0 | exact XI0 | exact XJ0 | exact XD0 | exact XN0 | ] end.
clear MU0 WM0 FRM XX0 XI0 XJ0. rename MI0 into MI. unfold R1.
match goal with H : frm0 _, H2 : rw_cells _ _ NE (f32 ?l), H3 : length ?l = 80%nat |- _ => rename H into FRM; rename H2 into XN; rename H3 into LN end.
bato 0xa940c. astep.
lazymatch type of XN with rw_cells _ ?mc _ (f32 ?l) =>
pose proof (aobj_munch bsegs _ m mc NE 320 OBN MU (shfree_of_aobj bsegs _ m NE 320 OF OBN)) as OBNc;
replace (Z_to_bv 64 80) with (Z_to_bv 64 (Z.of_nat (length l))) by (rewrite LN; reflexivity);
call (compute_rms_walk l NE (usp + -928) lo);
[ lia | rewrite LN; exact OBNc | exact N4 | lia | lia | exact LOS | lia | lia
| exact XN | exact FRM | exact ST | exact (conj G1 (conj G2 (conj G3 G4))) | exact MI | ] end.
clear OBNc. rename MI0 into MI || idtac. rewrite LN. change (Z.of_nat 80) with 80.
bato 0xa941c. astep.
lazymatch type of XX with rw_cells _ ?mc _ (f32 ?l) =>
pose proof (aobj_munch bsegs _ m mc EO 2000 OBE MU (shfree_of_aobj bsegs _ m EO 2000 OF OBE)) as OBEc;
replace (Z_to_bv 64 80) with (Z_to_bv 64 (Z.of_nat (length l))) by (cbn [length]; rewrite LXW; reflexivity);
call (compute_rms_walk l XB (usp + -928) lo);
[ cbn [length]; lia | cbn [length]; rewrite LXW; apply (aobj_sub bsegs mc EO 2000); [exact OBEc | lia | lia] | exact X4 | lia | lia | exact LOS | lia | cbn [length]; lia
| exact XX | eassumption | eassumption | exact (conj G1 (conj G2 (conj G3 G4))) | exact MI | ] end.
clear OBEc. rename MI0 into MI || idtac. cbn [length]. rewrite LXW. change (Z.of_nat 80) with 80.

bato 0xa9430. astep. joinb 0xa9438 0 1.
bato 0xa943c. astep. joinb 0xa9444 0 1.
bato 0xa944c. astep. joinb 0xa9454 0 1.
bato 0xa9470.
replace (0 <? NE) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. alits.

lazymatch type of XN with rw_cells _ _ _ (f32 ?l) => destruct l as [|nw1 nsr1]; [cbn in LN; lia|]; cbn [length] in LN end.
lazymatch goal with |- evt _ _ (MS _ _ _ ?fc0 _ ?mc _) =>
pose proof (munch_refl [(NE, NE + 320)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (XD0 : rw_cells bsegs mc NE (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof (aobj_munch bsegs _ m mc NE 320 OBN MU (shfree_of_aobj bsegs _ m NE 320 OF OBN)) as OBNc;
callc (mc_L2 NE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N4 NI (proj1 NE0) mc nsr1 [] nw1 0 NE 80 _ _ _ fc0 mc)
(clear XN XD0);
[ lia | lia | reflexivity | lia | exact OBNc | exact OFN | eassumption | exact MI | exact MU0 | exact WM0 | exact XD0 | exact XN | ] end.
clear MU0 WM0 OBNc. rename MI0 into MI. unfold R2.
apply evt_done; unfold tail_post. do 29 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.
End Tail.
