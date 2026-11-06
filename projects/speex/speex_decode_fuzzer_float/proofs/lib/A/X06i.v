(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X09e.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition A_forced_pitch_unquant : Z := 0xa88d8.

Section Loop.
Variables (EB e32 start exc : Z) (neb : nat).
Variables ra sp gp tp s0 s1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis EX : EB + NE <= e32 \/ e32 + 160 <= EB.
Hypothesis EXC2 : exc + 160 <= EB + NE.
Local Notation W := [(exc, exc + 160); (e32, e32 + 160)].

Definition fp_loop_post (m0 : mem) : machine_state -> Prop :=
fun ms' => exists t1 t2 a0 a1 a3 a4 a5 t3 t4 t5 t6 F' fc' m' (eb' e32' : list word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 SHB) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa89b4) fc' None m' (seg_rom asegs)
/\ munch W m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ frm0 fc'
/\ rw_cells asegs m' EB (f32 eb') /\ length eb' = neb /\ rw_cells asegs m' e32 (f32 e32') /\ length e32' = 40%nat.

Lemma fp_loop_ind : forall (rest dn L MID R : list word) (y : word) (kz pr pw q : Z) (t2 t3 t4 t5 t6 : word) F0 fc m1,
Z.of_nat (length dn) + Z.of_nat (S (length rest)) = 40 -> kz = Z.of_nat (S (length rest)) ->
Z.of_nat (length MID) = start -> (S (length rest) <= length R)%nat -> (length L + length MID + length R = neb)%nat ->
pr = EB + 4 * Z.of_nat (length L) -> pw = pr + 4 * start -> pw = exc + 4 * Z.of_nat (length dn) -> q = e32 + 4 * Z.of_nat (length dn) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 EB (f32 L) -> rw_cells asegs m1 pr (f32 MID) -> rw_cells asegs m1 pw (f32 R) ->
rw_cells asegs m1 e32 (f32 dn) -> rw_cells asegs m1 q (f32 (y :: rest)) ->
evt asegs (fp_loop_post m)
(MS (mkR ra sp gp tp (Z_to_bv 64 SHB) (Z_to_bv 64 (0 - start * 4)) t2 s0 s1 (Z_to_bv 64 pw) (Z_to_bv 64 q) a2 (Z_to_bv 64 pw) (Z_to_bv 64 q)
(Z_to_bv 64 kz) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa891c) fc None m1 (seg_rom asegs)).
Proof.
induction rest as [|y' rest IH]; intros dn L MID R y kz pr pw q t2 t3 t4 t5 t6 F0 fc m1 HL Hkz HM HR HN Epr Epw Epw2 Eq FRM MU OF WM MI XL XM XR D32 R32;
pose proof OBE as (OE0 & OE1 & _); pose proof OB32 as (O320 & O321 & _); unfold APP_TOP in *;
(destruct MID as [|x M]; [cbn [length] in HM; lia|]); (destruct R as [|w R']; [cbn [length] in HR; lia|]);
pose proof (rw_cells_bound _ _ _ _ XM) as BM; rewrite cells_size_f32 in BM;
pose proof (rw_cells_bound _ _ _ _ XR) as BR; rewrite cells_size_f32 in BR;
pose proof (rw_cells_bound _ _ _ _ R32) as B32; rewrite cells_size_f32 in B32; cbn [length] in *;
subst kz; rewrite !f32_cons in XM, XR, R32.
- chunk_uncons XM as X1. chunk_uncons XR as W1. chunk_uncons R32 as Y1.
ato 0xa8920. replace (0 - start * 4 + pw) with pr by lia.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa892c. astep. chk_merge OBE 4. clear HINT.
ato 0xa8934. replace (pw + (0 - start * 4)) with pr by lia.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8944. astep. chk_merge OB32 4. clear HINT.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa895c. astep. chk_merge OBE 4. clear HINT.
ato 0xa8978. astep. try sh_if.
ato 0xa89b4.
chunk_snoc XL X1. chunk_cat XL XM. chunk_snoc XL W1. chunk_cat XL XR. chunk_snoc D32 Y1.
f32_norm XL. f32_norm D32.
unfold fp_loop_post. finish.
+ exact XL.
+ rewrite !length_app. cbn [length]. lia.
+ exact D32.
+ rewrite !length_app. cbn [length]. lia.
- chunk_uncons XM as X1. chunk_uncons XR as W1. chunk_uncons R32 as Y1.
ato 0xa8920. replace (0 - start * 4 + pw) with pr by lia.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa892c. astep. chk_merge OBE 4. clear HINT.
ato 0xa8934. replace (pw + (0 - start * 4)) with pr by lia.
pose proof (OB32 : sh_cur _) as HINT.
ato 0xa8944. astep. chk_merge OB32 4. clear HINT.
pose proof (OBE : sh_cur _) as HINT.
ato 0xa895c. astep. chk_merge OBE 4. clear HINT.
ato 0xa8978. astep. cbn [length]. sh_if.
chunk_snoc XL X1. chunk_snoc XM W1. chunk_snoc D32 Y1.
f32_norm XL. f32_norm XM. f32_norm D32.
lazymatch type of XM with rw_cells _ _ _ (f32 (M ++ [?v])) =>
eapply (IH (dn ++ [v]) (L ++ [x]) (M ++ [v]) R' y' _ (pr + 4) (pw + 4) (q + 4)); try eassumption end.
all: try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End Loop.

Section Tail.
Variables (pv pg usp lo start : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Hypothesis OBPV : aobj asegs m pv 4.
Hypothesis OBPG : aobj asegs m pg 12.
Hypothesis PV4 : pv mod 4 = 0.
Hypothesis PG4 : pg mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv).
Hypothesis GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg).
Hypothesis VAP : pv + 4 <= lo.
Hypothesis GAP : pg + 12 <= lo.
Hypothesis VG : pv + 4 <= pg \/ pg + 12 <= pv.
Local Notation W := [(pv, pv + 4); (pg, pg + 12); (usp + -16, usp)].

Definition fp_tail_post : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (pg' : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ frm0 fc'
/\ rw_cells asegs m' pv [C4 (Z_to_bv 64 start)] /\ rw_cells asegs m' pg (f32 pg') /\ length pg' = 3%nat.

Lemma fp_tail_seg : forall (g0 g1 g2 opv : word) (j0 : list byte) (t1 t2 a0 a1 a3 a4 a5 t3 t4 t5 t6 : word) F0 fc,
frm0 fc -> mem_inv asegs m ->
stk asegs m lo (usp + -16) -> rw_cells asegs m (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m pv [C4 opv] -> rw_cells asegs m pg (f32 [g0; g1; g2]) ->
evt asegs fp_tail_post
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 SHB) t1 t2 s0 s1 a0 a1 (Z_to_bv 64 start) a3 a4 a5 (Z_to_bv 64 pv) (Z_to_bv 64 pg)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa89b4) fc None m (seg_rom asegs)).
Proof.
intros g0 g1 g2 opv j0 t1 t2 a0 a1 a3 a4 a5 t3 t4 t5 t6 F0 fc FRM MI ST FR XPV XPG.
pose proof OBPV as (OV0 & OV1 & _). pose proof OBPG as (OG0 & OG1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (pose proof (VSH : _ \/ _) as Y1; pose proof (GSH : _ \/ _) as Y2; cbn; unfold SH_LO, SH_HI in *; lia).
rewrite !f32_cons, ?f32_nil in XPG.
ato 0xa89c0. astep. chk_merge OBPV 4.
ato 0xa89d8. astep. chk_merge OBPG 4.
ato 0xa89ec. astep. chk_merge OBPG 4.
ato 0xa8a04. astep. chk_merge OBPG 4.
ato 0xa8a0c. astep. release_frame FR ST usp. astep. astep.
unfold fp_tail_post. finish.
- lazymatch goal with H : rw_cells asegs ?mm pg [C4 ?a; C4 ?b; C4 ?c] |- rw_cells asegs ?mm pg _ => change (rw_cells asegs mm pg (f32 [a; b; c])) in H; exact H end.
- reflexivity.
Qed.
End Tail.

Definition forced_pitch_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(usp lo EB exc e32 pv pg start : Z) (neb : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (eb' e32' pg' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo usp /\ frm0 fc'
/\ rw_cells asegs m' EB (f32 eb') /\ length eb' = neb
/\ rw_cells asegs m' e32 (f32 e32') /\ length e32' = 40%nat
/\ rw_cells asegs m' pv [C4 (Z_to_bv 64 start)]
/\ rw_cells asegs m' pg (f32 pg') /\ length pg' = 3%nat.

Section FP.
Variables (EB e0 e32 pv pg usp lo start : Z) (neb : nat).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation NE := (4 * Z.of_nat neb).
Local Notation exc := (EB + 4 * e0).
Hypothesis OBE : aobj asegs m EB NE.
Hypothesis OB32 : aobj asegs m e32 160.
Hypothesis OBPV : aobj asegs m pv 4.
Hypothesis OBPG : aobj asegs m pg 12.
Hypothesis E4 : EB mod 4 = 0.
Hypothesis X4 : e32 mod 4 = 0.
Hypothesis PV4 : pv mod 4 = 0.
Hypothesis PG4 : pg mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ST17 : 17 <= start <= 144.
Hypothesis E0a : 290 <= e0.
Hypothesis E0b : e0 + 40 <= Z.of_nat neb.

Hypothesis ESH : hidp (EB + NE <= SH_LO \/ SH_HI <= EB).
Hypothesis XSH : hidp (e32 + 160 <= SH_LO \/ SH_HI <= e32).
Hypothesis VSH : hidp (pv + 4 <= SH_LO \/ SH_HI <= pv).
Hypothesis GSH : hidp (pg + 12 <= SH_LO \/ SH_HI <= pg).
Hypothesis EAP : EB + NE <= lo.
Hypothesis XAP : e32 + 160 <= lo.
Hypothesis VAP : pv + 4 <= lo.
Hypothesis GAP : pg + 12 <= lo.
Hypothesis EX : hidp (EB + NE <= e32 \/ e32 + 160 <= EB).
Hypothesis EV : hidp (EB + NE <= pv \/ pv + 4 <= EB).
Hypothesis EG : hidp (EB + NE <= pg \/ pg + 12 <= EB).
Hypothesis XV : hidp (e32 + 160 <= pv \/ pv + 4 <= e32).
Hypothesis XG : hidp (e32 + 160 <= pg \/ pg + 12 <= e32).
Hypothesis VG : hidp (pv + 4 <= pg \/ pg + 12 <= pv).
Local Notation POST := (forced_pitch_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo EB exc e32 pv pg start neb m).
Local Notation W := [(exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (usp + -16, usp)].

Lemma fp_rest : forall (eb e32s pgs : list word) (opv : word) (j0 : list byte) (t0 t1 t2 a3 a4 t3 t4 t5 t6 : word) (PAR : Z) F0 fc m1,
length eb = neb -> length e32s = 40%nat -> length pgs = 3%nat ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 EB (f32 eb) -> rw_cells asegs m1 e32 (f32 e32s) -> rw_cells asegs m1 pv [C4 opv] -> rw_cells asegs m1 pg (f32 pgs) ->
ro_cells asegs m1 1036920 [C8 (Z_to_bv 64 SHB)] ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32) (Z_to_bv 64 start) (Z_to_bv 64 1036920) a4
(Z_to_bv 64 40) (Z_to_bv 64 pv) (Z_to_bv 64 pg) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa8904) fc None m1 (seg_rom asegs)).
Proof.
intros eb e32s pgs opv j0 t0 t1 t2 a3 a4 t3 t4 t5 t6 PAR F0 fc m1 LE L32 LPG FRM MU OF WM MI ST FR XE X32 XPV XPG G2.
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
ato 0xa8908. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa8910. rewrite (Z.shiftl_mul_pow2 start 2) by lia. change (2^2) with 4. rewrite ?(Z.mod_small (start * 4)) by lia.
ato 0xa891c.

pose proof (aobj_munch asegs W m m1 EB NE OBE MU (shfree_of_aobj asegs W m EB NE OF OBE)) as OBE1.
pose proof (aobj_munch asegs W m m1 e32 160 OB32 MU (shfree_of_aobj asegs W m e32 160 OF OB32)) as OB321.
destruct (f32_split asegs m1 EB eb (Z.to_nat (e0 - start)) ltac:(lia) XE) as [XL XMR]. clear XE.
assert (LS : (Z.to_nat start <= length (skipn (Z.to_nat (e0 - start)) eb))%nat) by (rewrite length_skipn; lia).
destruct (f32_split asegs m1 _ _ (Z.to_nat start) LS XMR) as [XM XR]. clear XMR LS.
set (L := firstn (Z.to_nat (e0 - start)) eb) in *. set (MR := skipn (Z.to_nat (e0 - start)) eb) in *.
assert (LL : length L = Z.to_nat (e0 - start)) by (unfold L; rewrite firstn_length_le; lia).
assert (LMR : length MR = (neb - Z.to_nat (e0 - start))%nat) by (unfold MR; rewrite length_skipn; lia).
set (MID := firstn (Z.to_nat start) MR) in *. set (R := skipn (Z.to_nat start) MR) in *.
assert (LM : length MID = Z.to_nat start) by (unfold MID; rewrite firstn_length_le; lia).
assert (LR : length R = (neb - Z.to_nat (e0 - start) - Z.to_nat start)%nat) by (unfold R; rewrite length_skipn; lia).
destruct e32s as [|y rest32]; [cbn [length] in L32; lia|].
replace (EB + 4 * Z.of_nat (Z.to_nat (e0 - start)) + 4 * Z.of_nat (Z.to_nat start)) with exc in XR by lia.
assert (EXC2 : exc + 160 <= EB + NE) by lia.
rewrite <- LL in XM.
assert (OFL : offsh [(exc, exc + 160); (e32, e32 + 160)]) by (pose proof (ESH : _ \/ _) as Y1; pose proof (XSH : _ \/ _) as Y2; cbn; unfold SH_LO, SH_HI in *; lia).
eapply evt_cut; [ eapply (fp_loop_ind EB e32 start exc neb ra (Z_to_bv 64 (usp + -16)) gp tp s0 s1 (Z_to_bv 64 start) (Z_to_bv 64 pv) (Z_to_bv 64 pg)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 OBE1 OB321 E4 X4 ST17 EX EXC2
rest32 [] L MID R y 40 (EB + 4 * Z.of_nat (length L)) exc e32)
| clear XL XM XR X32 G2 LL LMR LM LR; clearbody L MID R MR;
pose proof (EV : _ \/ _) as EV'; pose proof (XV : _ \/ _) as XV'; pose proof (EG : _ \/ _) as EG'; pose proof (XG : _ \/ _) as XG';
post_call asegs m1; clear EV' XV' EG' XG' ].
all: try (cbn [length] in *; lia). all: try eassumption.
all: try (apply munch_refl). all: try (apply wmono_refl).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
clear OFL.

match goal with H : rw_cells asegs _ EB (f32 ?l), H' : length ?l = neb |- _ => rename H into XE2; rename H' into LE2 end.
match goal with H : rw_cells asegs _ e32 (f32 ?l), H' : length ?l = 40%nat |- _ => rename H into X322; rename H' into L322 end.
destruct pgs as [|g0 [|g1 [|g2 [|? ?]]]]; try (cbn [length] in LPG; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs W m mc pv 4 OBPV MU (shfree_of_aobj asegs W m pv 4 OF OBPV)) as OBPV2;
pose proof (aobj_munch asegs W m mc pg 12 OBPG MU (shfree_of_aobj asegs W m pg 12 OF OBPG)) as OBPG2;
eapply evt_cut; [ eapply (fp_tail_seg pv pg usp lo start ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mc OBPV2 OBPG2 PV4 PG4 LO LOS VSH GSH VAP GAP VG g0 g1 g2 opv j0)
| clear XPV XPG FR ST;
pose proof (EV : _ \/ _) as EV'; pose proof (XV : _ \/ _) as XV'; pose proof (EG : _ \/ _) as EG'; pose proof (XG : _ \/ _) as XG';
post_call asegs mc; clear EV' XV' EG' XG' ] end.
all: try eassumption.
unfold forced_pitch_post. finish.
all: eassumption.
Qed.

Lemma forced_pitch_unquant_walk : forall (eb e32s pgs : list word) (opv : word) (t0 t1 t2 a3 t3 t4 t5 t6 : word) (PAR : Z) F fc,
rw_cells asegs m EB (f32 eb) -> length eb = neb -> rw_cells asegs m e32 (f32 e32s) -> length e32s = 40%nat ->
rw_cells asegs m pv [C4 opv] -> rw_cells asegs m pg (f32 pgs) -> length pgs = 3%nat ->
frm0 fc -> stk asegs m lo usp -> client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 exc) (Z_to_bv 64 e32) (Z_to_bv 64 start) a3 (Z_to_bv 64 PAR)
(Z_to_bv 64 40) (Z_to_bv 64 pv) (Z_to_bv 64 pg) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_forced_pitch_unquant) fc None m (seg_rom asegs)).
Proof.
intros eb e32s pgs opv t0 t1 t2 a3 t3 t4 t5 t6 PAR F fc XE LE X32 L32 XPV XPG LPG FRM ST (G1 & G2 & _) MI.
unfold A_forced_pitch_unquant, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof OBE as (OE0 & OE1 & _). pose proof OB32 as (O320 & O321 & _). pose proof OBPV as (OV0 & OV1 & _). pose proof OBPG as (OG0 & OG1 & _).
unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (pose proof (ESH : _ \/ _) as Y1; pose proof (XSH : _ \/ _) as Y2; pose proof (VSH : _ \/ _) as Y3; pose proof (GSH : _ \/ _) as Y4; cbn; unfold SH_LO, SH_HI in *; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa88f8. astep. if_cases K.
- ato 0xa8904. eapply (fp_rest eb e32s pgs opv); eassumption.
- ato 0xa8904. eapply (fp_rest eb e32s pgs opv); eassumption.
Qed.
End FP.
