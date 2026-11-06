(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X07r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yj X0z8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition JXB (pc : Z) (m : mem) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
: machine_state -> Prop :=
fun ms => exists (a0 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F' (Z_to_bv 64 pc) fc' None m (seg_rom bsegs)
/\ frm0 fc'.
Ltac jxb_done := apply evt_done; do 3 eexists; split; [reflexivity| assumption].

Tactic Notation "joinb" constr(pcJ) integer(n1) integer(n2) :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (evt_cut bsegs (JXB pcJ mc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _));
[ let B := fresh "B" in if_cases B;
[ do n1 astep; jxb_done | do n2 astep; jxb_done ]
| try match goal with H : frm0 _ |- _ => clear H end;
let FRM := fresh "FRM" in intros ? (? & ? & ? & -> & FRM) ]
end.

Lemma land_high0 : forall p, 0 <= p < 2^63 -> Z.land p (2^63) = 0.
Proof.
intros p Hp. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n 63) as [->|Hne].
- rewrite (Z.bits_above_log2 p 63); [reflexivity | lia |]. destruct (Z.eq_dec p 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
- rewrite (Z.pow2_bits_false 63 n) by lia. apply andb_false_r.
Qed.
Lemma slt40_norm : forall p, 0 <= p < 2^63 ->
(9223372036854775848 <? Z.lxor p 9223372036854775808) = (40 <? p).
Proof.
intros p Hp. change 9223372036854775808 with (2^63). rewrite <- Z.add_nocarry_lxor by (apply land_high0; lia).
destruct (Z.ltb_spec 40 p); [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
Qed.
Section Mid.
Variables (EO XB I1 I2 NE pitch usp lo : Z) (xw i1 i2 : list word).
Variables gp tp : word.
Hypothesis LXW : Z.of_nat (length xw) = 4 * 20.
Hypothesis LI1 : Z.of_nat (length i1) = 4 * 20.
Hypothesis LI2 : Z.of_nat (length i2) = 4 * 20.
Hypothesis HP : 17 <= pitch <= 144.
Hypothesis HI1 : I1 = usp + -896.
Hypothesis HI2 : I2 = I1 + 320.
Hypothesis XBR : EO <= XB /\ XB + 320 <= EO + 2000.
Hypothesis X4 : XB mod 4 = 0.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis EO0 : 0 < EO.
Hypothesis NE0 : 0 < NE /\ NE + 320 < 2^62.

Definition RMID (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -928)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -224)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 80) (Z_to_bv 64 NE) (Z_to_bv 64 XB) (Z_to_bv 64 640) (Z_to_bv 64 I1) (Z_to_bv 64 320) (Z_to_bv 64 pitch) s9 (Z_to_bv 64 SHB)
(Z_to_bv 64 (18446744073709551615 - I1)) t3 t4 t5 t6.

Definition mid_post (m : mem) (j8 j40 : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : machine_state -> Prop :=
fun ms' => exists (ra t2 a0 a1 a2 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (RMID ra (Z_to_bv 64 1) (Z_to_bv 64 320) t2 a0 a1 a2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 0) t3 t4 t5 t6)
F' (Z_to_bv 64 0xa9304) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -976, usp + -928); (usp + -208, usp + -200)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ stk bsegs m' lo (usp + -928)
/\ rw_cells bsegs m' (usp + -224) (mc_frame (CB 8 j8) (C8 (Z_to_bv 64 160)) (C8 (Z_to_bv 64 40)) (C8 (Z_to_bv 64 (usp + -928))) (CB 8 j40)
f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra).

Lemma mc_mid : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j8 j16 j40 : list byte) (f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells bsegs m XB (f32 xw) -> rw_cells bsegs m I1 (f32 i1) -> rw_cells bsegs m I2 (f32 i2) ->
rw_cells bsegs m (usp + -224) (mc_frame (CB 8 j8) (CB 8 j16) (C8 (Z_to_bv 64 40)) (C8 (Z_to_bv 64 (usp + -928))) (CB 8 j40)
f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
aobj bsegs m EO 2000 -> aobj bsegs m I1 640 ->
stk bsegs m lo (usp + -928) -> lo <= usp - 4320 -> SH_HI <= lo -> usp < 2^63 -> XB + 320 <= lo -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (mid_post m j8 j40 f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)
(MS (RMID (Z_to_bv 64 RA_mc_ip2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 160) t3 t4 t5 t6) G (ret_pc (Z_to_bv 64 RA_mc_ip2)) fc None m (seg_rom bsegs)).
Proof using LXW LI1 LI2 HP HI1 HI2 XBR X4 N4 EO0 NE0.
intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j8 j16 j40 f8 f7 f6 f5 f4 f3 f2 f1 f0 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra G fc m
XX XI1 XI2 FR OBE OBI ST LO LOS SPH XLO U32 CC MI FRM.
unfold RMID, RA_mc_ip2, mc_frame in *. replace (ret_pc (Z_to_bv 64 0xa90ec)) with (Z_to_bv 64 0xa90ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof OBE as (OE0 & OE1 & _). pose proof OBI as (OI0 & OI1 & _). unfold APP_TOP in *.
pose proof (munch_refl [(usp + -976, usp + -928); (usp + -208, usp + -200)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -976, usp + -928); (usp + -208, usp + -200)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (I14 : I1 mod 4 = 0) by (subst I1; clear - U32; Z.div_mod_to_equations; lia).
assert (I24 : I2 mod 4 = 0) by (subst I2; clear - I14; Z.div_mod_to_equations; lia).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in G1, G2, G3, G4.
clear CC.
Ltac ipcall MU OF OBE OBI xs ys px py usp lo G1 G2 G3 G4 :=
lazymatch type of MU with munch _ ?m0 ?mc =>
let OBEc := fresh "OBEc" in let OBIc := fresh "OBIc" in
pose proof (aobj_munch bsegs _ m0 mc _ 2000 OBE MU (shfree_of_aobj bsegs _ m0 _ 2000 OF OBE)) as OBEc;
pose proof (aobj_munch bsegs _ m0 mc _ 640 OBI MU (shfree_of_aobj bsegs _ m0 _ 640 OF OBI)) as OBIc;
call (inner_prodB_walk xs ys 20 px py (usp + -928) lo);
[ lia | eassumption | eassumption
| first [ apply (aobj_sub bsegs mc I1 640); [exact OBIc | lia | lia] | apply (aobj_sub bsegs mc EO 2000); [exact OBEc | lia | lia] ]
| first [ apply (aobj_sub bsegs mc I1 640); [exact OBIc | lia | lia] | apply (aobj_sub bsegs mc EO 2000); [exact OBEc | lia | lia] ]
| assumption | assumption | lia | lia | lia | assumption | lia
| eassumption | eassumption | eassumption | eassumption | lia | lia | exact (conj G1 (conj G2 (conj G3 G4))) | eassumption | ];
try (rename MI0 into MI);
clear OBEc OBIc end.

do 4 astep. change 80 with (4 * 20).
ipcall MU OF OBE OBI i1 i1 I1 I1 usp lo G1 G2 G3 G4.
bato 0xa9124. alits. replace (I1 + 320) with I2 by lia. astep.
ipcall MU OF OBE OBI i2 i2 I2 I2 usp lo G1 G2 G3 G4.
bato 0xa9138. astep.
ipcall MU OF OBE OBI xw xw XB XB usp lo G1 G2 G3 G4.
bato 0xa9154. astep.
ipcall MU OF OBE OBI i1 xw I1 XB usp lo G1 G2 G3 G4.

bato 0xa9164. astep. joinb 0xa916c 0 1.
bato 0xa9184. astep.
ipcall MU OF OBE OBI i2 xw I2 XB usp lo G1 G2 G3 G4.

bato 0xa918c. astep. joinb 0xa9194 0 1.
bato 0xa91a0. astep. joinb 0xa91ac 0 2.
bato 0xa91b4. astep. joinb 0xa91cc 2 3.
bato 0xa91d8. astep. joinb 0xa9220 0 17.
bato 0xa9248. astep. joinb 0xa9250 0 1.
bato 0xa9258. astep. joinb 0xa9260 0 1.
bato 0xa927c.
rewrite (land3_al NE N4). astep.
rewrite (slt40_norm pitch) by lia.
destruct (40 <? pitch) eqn:B40; cbn [Z.b2z]; alits.
- bato 0xa9304.
rewrite (land3_al XB X4). replace (0 <? XB) with true by (symmetry; apply Z.ltb_lt; lia). replace (0 <? NE) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z]. alits.
apply evt_done; unfold mid_post, RMID, mc_frame. do 12 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [eassumption|]. split; [eassumption| eassumption].
- bato 0xa9304.
rewrite (land3_al XB X4). replace (0 <? XB) with true by (symmetry; apply Z.ltb_lt; lia). replace (0 <? NE) with true by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z]. alits.
apply evt_done; unfold mid_post, RMID, mc_frame. do 12 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [eassumption|]. split; [eassumption| eassumption].
Qed.
End Mid.
