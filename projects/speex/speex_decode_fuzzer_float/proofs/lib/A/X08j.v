(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X08h X08i.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Tactic Notation "callc" uconstr(SPEC) tactic3(clr) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clr; post_call segs m ]
end.

Section Tail.
Variables (EO XB I1 I2 NE pitch usp : Z).
Variables gp tp s10 s11 : word.
Hypothesis HI2 : I2 = I1 + 320.
Hypothesis XBR : EO <= XB /\ XB + 320 <= EO + 2000.
Hypothesis E4 : EO mod 4 = 0.
Hypothesis X4 : XB mod 4 = 0.
Hypothesis I4 : I1 mod 4 = 0.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis SEPE : NE + 320 <= EO \/ EO + 2000 <= NE.
Hypothesis SEPI : NE + 320 <= I1 \/ I1 + 640 <= NE.
Hypothesis NI : IMG_TOP <= NE.
Hypothesis NSH : NE + 320 <= SH_LO \/ SH_HI <= NE.

Definition tail_post (m : mem) : machine_state -> Prop :=
fun ms' => exists (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -896)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 40) (Z_to_bv 64 pitch) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xa58b8) fc' None m' (seg_rom asegs)
/\ munch [(NE, NE + 320)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length ns' = 80%nat /\ rw_cells asegs m' NE (f32 ns').

Lemma mc_tail : forall (xw i1 i2 ns : list word) (ra t0 t1 t2 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length xw = 80%nat -> length i1 = 80%nat -> length i2 = 80%nat -> length ns = 80%nat ->
rw_cells asegs m XB (f32 xw) -> rw_cells asegs m I1 (f32 i1) -> rw_cells asegs m I2 (f32 i2) -> rw_cells asegs m NE (f32 ns) ->
aobj asegs m EO 2000 -> aobj asegs m I1 640 -> aobj asegs m NE 320 ->
mem_inv asegs m -> frm0 fc ->
evt asegs (tail_post m)
(MS (RMID XB I1 I2 NE pitch usp gp tp s10 s11 ra t0 t1 t2 (Z_to_bv 64 XB) (Z_to_bv 64 NE) (Z_to_bv 64 80) (Z_to_bv 64 XB) (Z_to_bv 64 I1) (Z_to_bv 64 NE) (Z_to_bv 64 I2) a7 t3 t4 t5 t6)
G (Z_to_bv 64 0xa569c) fc None m (seg_rom asegs)).
Proof using HI2 XBR E4 X4 I4 N4 SEPE SEPI NI NSH.
intros xw i1 i2 ns ra t0 t1 t2 a7 t3 t4 t5 t6 G fc m LXW LI1 LI2 LNS XX XI1 XI2 XN OBE OBI OBN MI FRM.
unfold RMID.
pose proof OBE as (OE0 & OE1 & _). pose proof OBI as (OI0 & OI1 & _). pose proof OBN as (ON0 & ON1 & _). unfold APP_TOP in *.
pose proof NI as NI'. unfold IMG_TOP in NI'.
pose proof (munch_refl [(NE, NE + 320)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(NE, NE + 320)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
assert (XBR' : EO <= XB /\ XB + 320 <= EO + 2000 /\ (XB - EO) mod 4 = 0) by (clear - XBR E4 X4; Z.div_mod_to_equations; lia).
destruct xw as [|xw0 xwr]; [cbn in LXW; lia|]. destruct i1 as [|iw0 i1r]; [cbn in LI1; lia|]. destruct i2 as [|jw0 i2r]; [cbn in LI2; lia|].
destruct ns as [|nw0 nsr]; [cbn in LNS; lia|]. cbn [length] in LXW, LI1, LI2, LNS.

lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(NE, NE + 320)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc NE (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
callc (mc_L1 EO XB I1 NE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E4 I4 N4 XBR' SEPE SEPI NI mc nsr xwr i1r i2r [] nw0 xw0 iw0 jw0 0 _ _ _ _ _ _ _ _ _ mc)
(clear XN XD0);
[ lia | lia | lia | lia | lia | reflexivity | lia | lia | lia | lia | exact OBE | exact OBI | exact OBN | exact OF
| exact FRM | exact MI | exact MU0 | exact WM0 | exact XX | exact XI1 | exact XI2 | exact XD0 | exact XN | ] end.
clear MU0 WM0 FRM. rename MI0 into MI. unfold R1.
match goal with H : frm0 _, H2 : rw_cells _ _ NE (f32 ?l), H3 : length ?l = 80%nat |- _ => rename H into FRM; rename H2 into XN; rename H3 into LN end.

ato 0xa577c. alits.
lazymatch type of XN with rw_cells _ _ _ (f32 ?l) => destruct l as [|nw1 nsr1]; [cbn in LN; lia|]; cbn [length] in LN end.
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ ?mc _) =>
eapply evt_cut; [eapply (mc_L2 mc NE 320) with (k := 79%nat) (xr := nsr1) (xw := nw1) (W := NE) (i := 0) (F1 := G0) (fc := fc0);
[ exact (aobj_munch asegs _ m mc NE 320 OBN MU (shfree_of_aobj asegs _ m NE 320 OF OBN)) | exact N4
| lia | reflexivity | lia | lia | lia | lia | lia | replace (NE - NE) with 0 by lia; reflexivity | exact FRM | exact MI | replace (NE + 4 * 0) with NE by lia; exact XN ] | ] end.
clear FRM. intros ms' (a3' & a4' & F2 & fc2 & -> & FRM). unfold R2.

ato 0xa57c8.
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ ?mc _) =>
eapply evt_cut; [eapply (mc_L3 mc EO 2000) with (k := 79%nat) (xr := xwr) (xw := xw0) (W := XB) (i := 0) (F1 := G0) (fc := fc0);
[ exact (aobj_munch asegs _ m mc EO 2000 OBE MU (shfree_of_aobj asegs _ m EO 2000 OF OBE)) | exact E4
| lia | reflexivity | lia | lia | lia | lia | lia | clear - E4 X4; Z.div_mod_to_equations; lia | exact FRM | exact MI | replace (XB + 4 * 0) with XB by lia; exact XX ] | ] end.
clear FRM. intros ms' (a2' & a3'' & F3 & fc3 & -> & FRM). unfold R3.

ato 0xa5848. astep. join 0xa5850 0 1.
do 2 astep. join 0xa585c 0 1.
do 3 astep. join 0xa586c 0 1.
ato 0xa5878.

rewrite <- f32_cons in XN || idtac.
lazymatch type of MU with munch _ _ ?mc =>
pose proof (munch_refl [(NE, NE + 320)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (XD0 : rw_cells asegs mc NE (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof (aobj_munch asegs _ m mc NE 320 OBN MU (shfree_of_aobj asegs _ m NE 320 OF OBN)) as OBNc;
callc (mc_L4 NE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N4 NI mc nsr1 [] nw1 0 _ _ _ _ _ _ mc)
(clear XN XD0);
[ lia | lia | reflexivity | lia | exact OBNc | exact OF | eassumption | exact MI | exact MU0 | exact WM0 | exact XD0 | exact XN | ] end.
clear MU0 WM0 OBNc. rename MI0 into MI. unfold R4.
apply evt_done; unfold tail_post. do 25 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [eassumption|]. split; eassumption.
Qed.
End Tail.
