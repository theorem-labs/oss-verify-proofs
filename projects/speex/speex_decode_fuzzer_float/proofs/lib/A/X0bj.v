(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X05l X05k X082 X089 X0bn X0bk X0bl X0bm.
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

Lemma hull_split : forall (m : mem) H jh (k : nat), (4 * k <= 64)%nat -> rw_cells asegs m H [CB 96 jh] ->
exists j0 ws j1, rw_cells asegs m H [CB 32 j0] /\ rw_cells asegs m (H + 32) (f32 ws) /\ length ws = k /\ rw_cells asegs m (H + 32 + 4 * Z.of_nat k) [CB (64 - 4 * k) j1].
Proof.
intros m H jh k Hk HH.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [32; 4 * k; 64 - 4 * k]%nat) in HH; [| cbn [sum_nat]; lia].
cbn [mk_CB_cells app] in HH.
lazymatch type of HH with rw_cells _ _ _ [?a; ?b; ?c] => change [a; b; c] with ([a] ++ [b] ++ [c]) in HH end.
apply rw_cells_app in HH. destruct HH as (H0 & HH). apply rw_cells_app in HH. destruct HH as (H1 & H2).
cbn [cells_size csize Nat.add] in H1, H2.
replace (H + Z.of_nat 32) with (H + 32) in * by lia.
replace (H + 32 + Z.of_nat (4 * k + 0)) with (H + 32 + 4 * Z.of_nat k) in H2 by lia.
destruct (rw_cells_CB_f32 asegs m (H + 32) k _ H1) as (ws & Lws & HW).
eexists _, ws, _. split; [exact H0|]. split; [exact HW|]. split; [exact Lws| exact H2].
Qed.

Lemma hull_join : forall (m : mem) H j0 ws j1, (4 * length ws <= 64)%nat ->
rw_cells asegs m H [CB 32 j0] -> rw_cells asegs m (H + 32) (f32 ws) -> rw_cells asegs m (H + 32 + 4 * Z.of_nat (length ws)) [CB (64 - 4 * length ws) j1] ->
exists jh, rw_cells asegs m H [CB 96 jh].
Proof.
intros m H j0 ws j1 Hk H0 H1 H2.
assert (HH : rw_cells asegs m H ([CB 32 j0] ++ f32 ws ++ [CB (64 - 4 * length ws) j1])).
{ apply rw_cells_join; [exact H0|]. cbn [cells_size csize Nat.add]. replace (H + Z.of_nat 32) with (H + 32) by lia.
apply rw_cells_join; [exact H1|]. rewrite cells_size_f32. replace (H + 32 + Z.of_nat (4 * length ws)) with (H + 32 + 4 * Z.of_nat (length ws)) by lia. exact H2. }
exists (cells_bytes ([CB 32 j0] ++ f32 ws ++ [CB (64 - 4 * length ws) j1])).
apply (rw_cells_recast asegs m H _ _ HH); [| cbn [cells_bytes cbytes]; apply app_nil_r].
split; [| exact I]. destruct HH as [[Hwf _] _]. cbn [cell_wf]. rewrite (cells_bytes_length _ Hwf).
rewrite !cells_size_app, cells_size_f32. cbn [cells_size csize]. lia.
Qed.

Ltac cell_copy H k newH :=
lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
let pre := eval cbv [firstn] in (firstn k cs) in
let post := eval cbv [skipn] in (skipn k cs) in
lazymatch post with ?c :: ?post' =>
assert (newH : rw_cells segs m (A + Z.of_nat (cells_size pre)) [c])
by (let X := fresh in pose proof H as X; change cs with (pre ++ [c] ++ post') in X; apply rw_cells_app in X; destruct X as [_ X]; apply rw_cells_app in X; destruct X as [X _]; exact X);
cbn [cells_size csize Nat.add] in newH;
lazymatch type of newH with rw_cells _ _ (_ + Z.of_nat ?n) _ => let z := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with z in newH end
end end.
Lemma scb_body_proof : forall ptr, @scb_body_stmt ptr.
Proof.
intros ptr. unfold scb_body_stmt.
intros INN PAR A D ssz nb scb sbits hs usp lo b is0 tb c0 j8 j16 j24 j72 j80 jh1 jh2 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra
gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m.
intros RPAR OBP P8 PLO PHI HSS HNB HSN HSB HHS TB LTB OBT TLO THI FR H1 H2 OBI OBS REP OK OBA OBD ASH ALO DLO ATOP IS LIS OBN N4 NTOP NSH NAP SEPNA SEPND ST LO LOS SPH U32 CC MI FRM.
replace (ret_pc (Z_to_bv 64 RA_scb_pois2)) with (Z_to_bv 64 RA_scb_pois2) by (symmetry; apply ret_pc_even; [unfold RA_scb_pois2; lia | reflexivity]).
unfold RA_scb_pois2, scb_frame, scb_par_cells in *.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in *.
pose proof ST as (STa & STb & _).
pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
set (W := [(usp + -416, usp + -384); (usp + -384, usp + -192); (usp + -192, usp + -120); (INN, INN + 160); (A, A + BITS_SIZEOF)]).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (subst W; clear - ASH NSH LOS LO; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
subst W.
assert (NBR : 2 <= nb <= 8) by (clear - HNB; cbn [In] in HNB; lia).
assert (HS01 : hs = 0 \/ hs = 1) by lia.
assert (NB4 : 4 * nb = 4 * Z.of_nat (Z.to_nat nb)) by lia.
destruct (hull_split m (usp + -288) jh1 (Z.to_nat nb) ltac:(lia) H1) as (j10 & iws0 & j11 & H10 & IX & LI0 & H11).
destruct (hull_split m (usp + -384) jh2 (Z.to_nat nb) ltac:(lia) H2) as (j20 & sws0 & j21 & H20 & SX & LS0 & H21).
clear H1 H2.
replace (usp + -288 + 32) with (usp + -256) in * by lia. replace (usp + -384 + 32) with (usp + -352) in * by lia.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
assert (Lbs0 : Z.of_nat (length bs0) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs0, zlength_map_unsigned in OK'. lia. }
pose proof SIDE0 as (_ & _ & _ & _ & _ & SEPAD).
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBN as (ON0 & ON1 & _). pose proof OBT as (OT0 & OT1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof (rw_cells_bound _ _ _ _ IS) as BIS; rewrite cells_size_f32, LIS in BIS.
assert (P2 : 2 <= 2 ^ sbits <= 256).
{ clear - HSB. split; [change 2 with (2 ^ 1) at 1| change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia. }
assert (CNB : 2 ^ sbits * ssz <= 5120) by (clear - P2 HSS; nia).
pose proof (NAP : _ \/ _) as NAP'. pose proof (NSH : _ \/ _) as NSH'. pose proof (ASH : _ \/ _) as ASH'.
hide_disj.
ato 0xac7e8. astep. sh_if.
ato 0xac838.
rewrite sx32_small by (unfold int31; lia).

destruct iws0 as [|xi resti]; [cbn [length] in LI0; lia|]. destruct sws0 as [|xs rests]; [cbn [length] in LS0; lia|]. cbn [length] in LI0, LS0.
cell_copy FR 7%nat SLOT56.
replace (Z_to_bv 64 (usp + -256)) with (Z_to_bv 64 (usp + -256 + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (Z_to_bv 64 (usp + -352)) with (Z_to_bv 64 (usp + -352 + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (usp + -256) with (usp + -256 + 0) in IX at 1 by lia. replace (usp + -352) with (usp + -352 + 0) in SX at 1 by lia.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch asegs W m0 mc PAR 24 OBP MU (shfree_of_aobj asegs W m0 PAR 24 OF OBP)) as OBPc;
pose proof (aobj_munch asegs W m0 mc _ _ OBI MU (shfree_of_aobj asegs W m0 _ _ OF OBI)) as OBIc;
pose proof (aobj_munch asegs W m0 mc _ _ OBS MU (shfree_of_aobj asegs W m0 _ _ OF OBS)) as OBSc;
pose proof (aobj_munch asegs W m0 mc A 48 OBA MU (shfree_of_aobj asegs W m0 A 48 OF OBA)) as OBAc;
pose proof (aobj_munch asegs W m0 mc D _ OBD MU (shfree_of_aobj asegs W m0 D _ OF OBD)) as OBDc;
rewrite NB4 in OBIc, OBSc;
assert (REPc : bits_rep asegs mc A D b)
by (split; [exists rj0; split; [assumption| exact OBJ]| split; [exists bs0; split; [exact DAT| assumption]| assumption]]);
assert (CCc : client_consts mc)
by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))));
assert (ID0 : rw_cells asegs mc (usp + -256) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
assert (SD0 : rw_cells asegs mc (usp + -352) (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof (munch_refl [(usp + -384 + -32, usp + -384); (usp + -352, usp + -352 + 4 * Z.of_nat (Z.to_nat nb)); (usp + -256, usp + -256 + 4 * Z.of_nat (Z.to_nat nb)); (A, A + 48)] mc) as MU0;
pose proof (wmono_refl asegs mc) as WM0;
eapply evt_cut; [ eapply (scb_dec_loop gp tp _ _ F fc (usp + -384) (usp + -192) (usp + -256) (usp + -352) A D PAR lo ssz nb scb hs sbits (sb_buf_size b) (Z.to_nat nb) (scbb (Z.to_nat nb) hs sbits b) mc)
with (resti := resti) (rests := rests) (idw := []) (sdw := []) (xi := xi) (xs := xs) (off := 0) (kz := nb) (b := b)
| clear OBPc OBIc OBSc OBAc OBDc REPc CCc ID0 SD0 MU0 WM0 SLOT56 OBJ DAT IX SX ST REP; post_call segs mc ]
end end.
1: lia. 1: lia. 1: lia. 1: (clear - U32; Z.div_mod_to_equations; lia). 1: lia. 1: exact (HS01 : _ \/ _). 1: exact HSB.
1: exact OBPc. 1: exact P8. 1: exact PLO. 1: exact PHI. 1: exact OBIc. 1: exact OBSc. 1: exact OBAc. 1: exact OBDc.
1: exact (ASH : _ \/ _). 1: exact ALO. 1: exact DLO. 1: exact ATOP. 1: lia. 1: exact LOS. 1: lia.
1: reflexivity. 1: lia. 1: lia. 1: reflexivity. 1: (cbn [length]; lia). 1: (rewrite <- LI0; reflexivity).
1: exact REPc. 1: exact OK. 1: reflexivity. 1: exact RPAR. 1: exact SLOT56. 1: exact ID0. 1: exact IX. 1: exact SD0. 1: exact SX.
1: constructor. 1: constructor. 1: exact ST. 1: exact CCc. 1: exact MI. 1: exact MU0. 1: exact WM0.
rename PC into ST. rename PC0 into IX. rename PC1 into LIW. rename PC2 into FIW. rename PC3 into SX. rename PC4 into LSW. rename PC5 into FSW. rename PC6 into REP2. rename POST into OK2.
lazymatch type of IX with rw_cells _ _ _ (f32 ?l) => rename l into iws end. lazymatch type of SX with rw_cells _ _ _ (f32 ?l) => rename l into sws end.
destruct REP2 as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
assert (Lbs2 : Z.of_nat (length bs2) <= sb_buf_size b).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'.
assert (SZ2 : forall k (b0 : bits_st ptr), bits_ok b0 -> bits_ok (scbb k hs sbits b0) /\ sb_buf_size (scbb k hs sbits b0) = sb_buf_size b0).
{ clear - HSB. induction k as [|k IHk]; intros b0 OK0; [split; [exact OK0| reflexivity]|]. cbn [scbb].
destruct (negb (hs =? 0)).
- pose proof (ub_ok b0 1 OK0 ltac:(lia)) as (OKa & SZa & _). pose proof (ub_ok (ub b0 1) sbits OKa ltac:(lia)) as (OKb & SZb & _).
destruct (IHk _ OKb) as (I1 & I2). split; [exact I1| rewrite I2, SZb, SZa; reflexivity].
- pose proof (ub_ok b0 sbits OK0 ltac:(lia)) as (OKb & SZb & _).
destruct (IHk _ OKb) as (I1 & I2). split; [exact I1| rewrite I2, SZb; reflexivity]. }
destruct (SZ2 (Z.to_nat nb) b OK) as (_ & E). rewrite E in OK'. lia. }

ato 0xac900.
destruct iws as [|iw irest]; [cbn [length] in LIW; lia|]. destruct sws as [|sw srest]; [cbn [length] in LSW; lia|]. cbn [length] in LIW, LSW.
cell_copy FR 6%nat SLOT48.
pose proof IX as IXc. pose proof SX as SXc. pose proof IS as ISc.
replace (usp + -256) with (usp + -256 + 0) in IXc at 1 by lia. replace (usp + -352) with (usp + -352 + 0) in SXc at 1 by lia. replace INN with (INN + 0) in ISc at 1 by lia.
replace (Z.shiftl ssz 2) with (4 * ssz) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z_to_bv 64 INN) with (Z_to_bv 64 (INN + 0)) by (rewrite Z.add_0_r; reflexivity).
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of MU with munch ?W ?m0 mc =>
pose proof (aobj_munch asegs W m0 mc INN 160 OBN MU (shfree_of_aobj asegs W m0 INN 160 OF OBN)) as OBNc;
pose proof (aobj_munch asegs W m0 mc _ _ OBI MU (shfree_of_aobj asegs W m0 _ _ OF OBI)) as OBIc;
pose proof (aobj_munch asegs W m0 mc _ _ OBS MU (shfree_of_aobj asegs W m0 _ _ OF OBS)) as OBSc;
pose proof (aobj_munch asegs W m0 mc scb _ OBT MU (shfree_of_aobj asegs W m0 scb _ OF OBT)) as OBTc;
assert (ND0 : rw_cells asegs mc INN (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
assert (OFN : offsh [(INN, INN + 160)]) by (clear - NSH'; unfold hid in NSH'; cbn; lia);
pose proof (munch_refl [(INN, INN + 160)] mc) as MU0;
pose proof (wmono_refl asegs mc) as WM0;
eapply evt_cut; [ eapply (scb_outer (usp + -384) (usp + -192) (usp + -256) (usp + -352) INN scb ssz sbits nb tb mc)
with (irest := irest) (srest := srest) (iw := iw) (sw := sw) (done := []) (rest := is0) (i := 0) (off := 0) (offi := 0)
| clear OBNc OBIc OBSc OBTc ND0 OFN MU0 WM0 SLOT48 IXc SXc ISc IS FRM; post_call segs mc ]
end end.
1: lia. 1: lia. 1: lia. 1: (clear - U32; Z.div_mod_to_equations; lia). 1: lia. 1: lia. 1: exact HSS. 1: exact HSB. 1: lia.
1: exact N4. 1: exact OBNc. 1: exact OFN. 1: (clear - NAP' LO; unfold hid in NAP'; lia).
1: exact OBTc. 1: exact LTB. 1: lia. 1: lia. 1: exact OBIc. 1: exact OBSc.
1: lia. 1: lia. 1: reflexivity. 1: lia. 1: reflexivity.
1: (replace (Z.of_nat (S (length irest))) with nb by lia; lia).
1: (cbn [length]; lia).
1: exact FIW. 1: exact FSW. 1: exact SLOT48. 1: exact IXc. 1: exact SXc. 1: exact TB. 1: exact ND0. 1: exact ISc.
1: exact FRM. 1: assumption. 1: exact MU0. 1: exact WM0.
rename PC into FRM. rename PC0 into IS. rename POST into LIS'.
rewrite <- LIW in H11. rewrite <- LSW in H21.
replace (usp + -256) with (usp + -288 + 32) in IX, H11 by lia. replace (usp + -352) with (usp + -384 + 32) in SX, H21 by lia.
destruct (hull_join _ (usp + -288) j10 (iw :: irest) j11 ltac:(cbn [length]; lia) H10 IX H11) as (jh1' & H1').
destruct (hull_join _ (usp + -384) j20 (sw :: srest) j21 ltac:(cbn [length]; lia) H20 SX H21) as (jh2' & H2').
unfold A_scb_epi. finish.
1: exact FR. 1: exact H1'. 1: exact H2'.
1: (split; [exists rj2; split; [exact Lrj2| exact OBJ]| split; [exists bs2; split; [exact DAT| exact Hbs2]| exact SIDE2]]).
1: exact IS. 1: exact LIS'.
Qed.
