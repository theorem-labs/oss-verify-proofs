(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1cp X1dg X1df X1ck X1cu X1co X1dk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X05r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0x2 X0wr X0wk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Section ARMS2.
Variables (S P : Z) (ra sp gp tp t0 t1 t2 s1 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv bsegs m.
Hypothesis SB : 0 < S /\ S + 2968 < 2^63.
Hypothesis PB : 0 <= P /\ P + 24 < 2^63.
Hypothesis OBS : aobj bsegs m S 2968.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 2968 <= SH_LO \/ SH_HI <= S.

Lemma nbarm_set_isave : forall (old a2 a4 a5 : word),
rw_cells bsegs m (S + 2184) [C8 old] ->
evt bsegs (fun ms' => exists m', ms' = MS (R (Z_to_bv 64 (S + 2184)) (Z_to_bv 64 0) a2 (Z_to_bv 64 104) a4 a5) F (Z_to_bv 64 0xa1380) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' (S + 2184) [C8 (Z_to_bv 64 P)] /\ munch [(S + 2184, S + 2192)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R (Z_to_bv 64 (S + 2184)) (Z_to_bv 64 S) a2 (Z_to_bv 64 104) a4 a5) F (Z_to_bv 64 (nbctl_armpc 104)) fc None m (seg_rom bsegs)).
Proof using MI SB OBS S8 SOFF.
clear PB. intros old a2 a4 a5 ISV. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(S + 2184, S + 2192)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 2184, S + 2192)]) by (cbn; unfold SH_LO, SH_HI; lia).
bato 0xa1380.
apply evt_done. eexists. split; [reflexivity|]. split; [exact ISV|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

Lemma nbarm_get_dtx : forall (vo iw hp : word) (pad : list byte) (v : Z) (a2 a4 a5 : word), aobj bsegs m P 4 -> P mod 4 = 0 -> 0 < P ->
rw_cells bsegs m (S + 2948) [C4 vo; C4 (Z_to_bv 64 v); C4 iw; C4 hp; CB 4 pad] -> - 2^31 <= v < 2^31 ->
evt bsegs (fun ms' => exists xa1 xa2, ms' = MS (R (Z_to_bv 64 v) xa1 xa2 (Z_to_bv 64 103) a4 a5) F (Z_to_bv 64 0xa1378) fc None m (seg_rom bsegs))
(MS (R (Z_to_bv 64 (S + 2184)) (Z_to_bv 64 S) a2 (Z_to_bv 64 103) a4 a5) F (Z_to_bv 64 (nbctl_armpc 103)) fc None m (seg_rom bsegs)).
Proof using All.
intros vo iw hp pad v a2 a4 a5 OBP P4 PPOS TL RV. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
bato 0xa1374. astep. chk_merge OBP 4.
rewrite sx32_lit by lia.
apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma nbarm_get_pi_gain : forall (pg ws : list word) (a4 a5 : word), aobj bsegs m P 16 -> P mod 4 = 0 -> 0 < P ->
rw_cells bsegs m (S + 2168) (f32 pg) -> length pg = 4%nat -> rw_cells bsegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 2968 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) ->
evt bsegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (ws' : list word) (xt0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 : word),
ms' = MS (mkR ra sp gp tp xt0 t1 t2 (Z_to_bv 64 P) s1 xa0 (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7 s2 (Z_to_bv 64 SHB)
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0xa1380) fc None m' (seg_rom bsegs)
/\ munch [(P, P + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells bsegs m' (S + 2168) (f32 pg))
(MS (R (Z_to_bv 64 (S + 2184)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 100) a4 a5) F (Z_to_bv 64 (nbctl_armpc 100)) fc None m (seg_rom bsegs)).
Proof using All.
intros pg ws a4 a5 OBP P4 PPOS PG LPG WS LWS AP POFF. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct pg as [|g0 [|g1 [|g2 [|g3 []]]]]; cbn [length] in LPG; try lia.
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in PG, WS.
bato 0xa0a44.
astep. chk_merge OBP 4.
bato 0xa0a44. astep. chk_merge OBP 4.
bato 0xa0a44. astep. chk_merge OBP 4.
bato 0xa0a44. astep. chk_merge OBP 4.
bato 0xa1380.
apply evt_done. do 2 eexists. exists [nan_box (low32 g0); nan_box (low32 g1); nan_box (low32 g2); nan_box (low32 g3)].
do 8 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|]. rewrite !f32_cons, f32_nil; exact PG.
Qed.

Lemma nbarm_get_exc : forall (usp lo : Z) (x0 x1 x2 x3 ws : list word) (a4 a5 : word),
sp = Z_to_bv 64 usp -> stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 -> S + 2968 <= lo ->
aobj bsegs m P 16 -> P mod 4 = 0 -> 0 < P -> rw_cells bsegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 2968 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) -> (P + 16 <= lo \/ usp <= P) -> IMG_TOP_B <= P ->
rw_cells bsegs m (S + 2032) [C8 (Z_to_bv 64 (S + 1368))] ->
rw_cells bsegs m (S + 1368) (f32 x0) -> rw_cells bsegs m (S + 1528) (f32 x1) -> rw_cells bsegs m (S + 1688) (f32 x2) -> rw_cells bsegs m (S + 1848) (f32 x3) ->
length x0 = 40%nat -> length x1 = 40%nat -> length x2 = 40%nat -> length x3 = 40%nat ->
client_constsB m -> frm0 fc ->
evt bsegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (ws' : list word)
(xra xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
ms' = MS (mkR xra sp gp tp xt0 xt1 xt2 (Z_to_bv 64 P) xs1 xa0 (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 SHB) xs4 xs5 xs6 xs7 xs8 xs9 s10 s11
xt3 xt4 xt5 xt6)
F' (Z_to_bv 64 0xa1380) fc' None m' (seg_rom bsegs)
/\ munch [(usp + -16, usp); (P, P + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ frm0 fc'
/\ rw_cells bsegs m' P (f32 ws') /\ length ws' = 4%nat
/\ rw_cells bsegs m' (S + 2032) [C8 (Z_to_bv 64 (S + 1368))]
/\ rw_cells bsegs m' (S + 1368) (f32 x0) /\ rw_cells bsegs m' (S + 1528) (f32 x1) /\ rw_cells bsegs m' (S + 1688) (f32 x2) /\ rw_cells bsegs m' (S + 1848) (f32 x3))
(MS (R (Z_to_bv 64 (S + 2184)) (Z_to_bv 64 S) (Z_to_bv 64 (S + 2047)) (Z_to_bv 64 101) a4 a5) F (Z_to_bv 64 (nbctl_armpc 101)) fc None m (seg_rom bsegs)).
Proof using All.
intros usp lo x0 x1 x2 x3 ws a4 a5 -> ST LO LOS SPH SLO OBP P4 PPOS WS LWS AP POFF PAP PIMG EXR E0 E1 E2 E3 L0 L1 L2 L3 CC FRM.
unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'. pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP_B in PIMG.
pose proof ST as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(usp + -16, usp); (P, P + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp); (P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in WS.
bato 0xa12b8. astep.
replace (0 + (S + 1368)) with (S + 1368) by lia.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length x0))) by (rewrite L0; reflexivity).
lazymatch goal with |- evt _ _ (MS _ ?Fc _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc S 2968 OBS MUc (shfree_of_aobj bsegs W m S 2968 OF OBS)) as OBSc;
assert (OBX : aobj bsegs mc (S + 1368) (4 * Z.of_nat (length x0))) by (rewrite L0; eapply aobj_sub; [exact OBSc | lia | lia]);
call (compute_rms16_walk x0 (S + 1368) usp lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc ltac:(rewrite L0; cbn; lia) OBX
ltac:(clear - S8; Z.div_mod_to_equations; lia) ltac:(lia) LO LOS SPH ltac:(left; rewrite L0; cbn; lia))
end
end.
{ exact E0. } { exact FRM. } { exact ST. } { exact CC. } { exact MI. }
clear OBSc OBX. rename POST into FRM1. rename PC into ST1.
bato 0xa12dc. astep. chk_merge OBP 4.
bato 0xa12b8. astep.
replace (160 + (S + 1368)) with (S + 1528) by lia.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length x1))) by (rewrite L1; reflexivity).
lazymatch goal with |- evt _ _ (MS _ ?Fc _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc S 2968 OBS MUc (shfree_of_aobj bsegs W m S 2968 OF OBS)) as OBSc;
assert (OBX : aobj bsegs mc (S + 1528) (4 * Z.of_nat (length x1))) by (rewrite L1; eapply aobj_sub; [exact OBSc | lia | lia]);
call (compute_rms16_walk x1 (S + 1528) usp lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc ltac:(rewrite L1; cbn; lia) OBX
ltac:(clear - S8; Z.div_mod_to_equations; lia) ltac:(lia) LO LOS SPH ltac:(left; rewrite L1; cbn; lia))
end
end.
{ exact E1. } { assumption. } { assumption. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return. exact (conj G1 (conj G2 (conj G3 G4))). }
{ assumption. }
clear OBSc OBX FRM1. rename POST into FRM2. try clear ST1. rename PC into ST2.
bato 0xa12dc. astep. chk_merge OBP 4.
bato 0xa12b8. astep.
replace (320 + (S + 1368)) with (S + 1688) by lia.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length x2))) by (rewrite L2; reflexivity).
lazymatch goal with |- evt _ _ (MS _ ?Fc _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc S 2968 OBS MUc (shfree_of_aobj bsegs W m S 2968 OF OBS)) as OBSc;
assert (OBX : aobj bsegs mc (S + 1688) (4 * Z.of_nat (length x2))) by (rewrite L2; eapply aobj_sub; [exact OBSc | lia | lia]);
call (compute_rms16_walk x2 (S + 1688) usp lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc ltac:(rewrite L2; cbn; lia) OBX
ltac:(clear - S8; Z.div_mod_to_equations; lia) ltac:(lia) LO LOS SPH ltac:(left; rewrite L2; cbn; lia))
end
end.
{ exact E2. } { assumption. } { assumption. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return. exact (conj G1 (conj G2 (conj G3 G4))). }
{ assumption. }
clear OBSc OBX FRM2. rename POST into FRM3. try clear ST2. rename PC into ST3.
bato 0xa12dc. astep. chk_merge OBP 4.
bato 0xa12b8. astep.
replace (480 + (S + 1368)) with (S + 1848) by lia.
replace (Z_to_bv 64 40) with (Z_to_bv 64 (Z.of_nat (length x3))) by (rewrite L3; reflexivity).
lazymatch goal with |- evt _ _ (MS _ ?Fc _ _ _ ?mc _) =>
lazymatch goal with MUc : munch ?W m mc |- _ =>
pose proof (aobj_munch bsegs W m mc S 2968 OBS MUc (shfree_of_aobj bsegs W m S 2968 OF OBS)) as OBSc;
assert (OBX : aobj bsegs mc (S + 1848) (4 * Z.of_nat (length x3))) by (rewrite L3; eapply aobj_sub; [exact OBSc | lia | lia]);
call (compute_rms16_walk x3 (S + 1848) usp lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc ltac:(rewrite L3; cbn; lia) OBX
ltac:(clear - S8; Z.div_mod_to_equations; lia) ltac:(lia) LO LOS SPH ltac:(left; rewrite L3; cbn; lia))
end
end.
{ exact E3. } { assumption. } { assumption. }
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return. exact (conj G1 (conj G2 (conj G3 G4))). }
{ assumption. }
clear OBSc OBX FRM3. rename POST into FRM4. try clear ST3. rename PC into ST4.
bato 0xa12dc. astep. chk_merge OBP 4.
bato 0xa1380.
apply evt_done. do 3 eexists.
exists [A.X05r.rms_result (A.X05r.rms_sum fzero_s x0) (Z_to_bv 64 (Z.of_nat (length x0)));
A.X05r.rms_result (A.X05r.rms_sum fzero_s x1) (Z_to_bv 64 (Z.of_nat (length x1)));
A.X05r.rms_result (A.X05r.rms_sum fzero_s x2) (Z_to_bv 64 (Z.of_nat (length x2)));
A.X05r.rms_result (A.X05r.rms_sum fzero_s x3) (Z_to_bv 64 (Z.of_nat (length x3)))].
do 23 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST4|]. split; [exact FRM4|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|].
split; [exact EXR|]. split; [exact E0|]. split; [exact E1|]. split; [exact E2| exact E3].
Qed.
End ARMS2.

Ltac xport MU WM H :=
eapply rw_cells_transport in H; [| exact MU | exact WM |
cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; rewrite ?cells_size_f32, ?length_f32; cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; lia].
Ltac xport_mem mo MU WM :=
repeat match goal with H : rw_cells bsegs mo _ _ |- _ => first [xport MU WM H | clear H] end.
Ltac solve_munch MU1 MU2 ELBD :=
eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]];
unfold ctlW; cbn [creq_ivs creq_size app]; intros x; rewrite !outside_cons, outside_blocks_ivs; cbn [fst snd outside creq_size]; intros (O1 & O2 & O3);
[split; [lia| exact I]|]; split; [| exact I];
first [ lia | specialize (O3 _ ltac:(rewrite ELBD; left; reflexivity)); cbn [blk_addr blk_size fst snd] in O3; lia ].

Definition rctl2_at (d : dec_state bptr) : Prop :=
forall (OUTL OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo usp : Z)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
creq_grp1 r = false ->
DREP OUTL STEREO m S d LBD -> (match r with CtlSetInnovationSave _ => True | _ => OUTL = OUT end) ->
creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> ablk m lo b) ->
(match r with CtlSetInnovationSave _ => True
| _ => aobj bsegs m P (creq_size r) /\ P mod 4 = 0 /\ IMG_TOP_B <= P /\ (P + creq_size r <= SH_LO \/ SH_HI <= P) /\ (P + creq_size r <= lo \/ usp <= P)
/\ (forall b, In b LBD -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) end) ->
aobj bsegs m A_speex_nb_mode 96 ->
stk bsegs m lo usp -> SH_HI <= lo -> lo <= usp - NBCTL_STACK -> usp < 2^63 ->
client_constsB m -> lib_consts m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (rctl_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp OUT STEREO S d LBD r P lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (ctl_req_code r)) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs)).

Theorem rctl2_nb : forall st, rctl2_at (DecNB st).
Proof.
intros st OUTL OUT STEREO S LBD r P lo usp ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
GRP REP EOUT OK PRE BLK DSTP OBM ST LOS LO SPH CC LC MI FRM.
unfold NBCTL_STACK in LO. cbn [decst_rep] in REP. destruct REP as [ELBD NB].
pose proof (BLK _ ltac:(rewrite ELBD; left; reflexivity)) as BRS. unfold ablk, blk_addr, blk_size in BRS. cbn [fst snd] in BRS.
destruct BRS as (OBS & S8 & SOFF & _ & SLO). unfold NBSTATE_SIZEOF in *.
destruct NB as (AL & POS & INV & j & JOK & CBS & X).
pose proof JOK as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
pose proof INV as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis).
apply (nb_pieces_of_cells bsegs _ _ _ m S OUTL STEREO st j JOK) in X.
destruct X as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18).
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14. unfold nb_ucb_cells, cb_cells in P16. cbn [fst snd] in P16. unfold nb_tail_cells in P18.
pose proof OBS as (S0 & STOP & _). pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold APP_TOP in *.
assert (OF1 : offsh [(usp + -112, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).

eapply evt_cut.
{ eapply (nbctl_entry S P (ctl_req_code r) lo usp _ ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P0);
[reflexivity| exact OBS| exact S8| exact OBM| exact ST| lia| exact LOS| exact SPH| lia| lia| lia| | exact CC| exact LC| exact MI].
unfold nbctl_code_ok. destruct r; cbn [ctl_req_code]; clear - GRP; try discriminate GRP; tauto. }
cbv beta. intros ms1 (xt1 & xa2 & xa4 & xa5 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1 & EA1). unfold nbctl_frame in FR.
pose proof (aobj_munch bsegs _ m m1 S 2968 OBS MU1 (shfree_of_aobj bsegs _ m S 2968 OF1 OBS)) as OBS1.
xport MU1 WM1 P0. xport MU1 WM1 P1. xport MU1 WM1 P2. xport MU1 WM1 P3. xport MU1 WM1 P4. xport MU1 WM1 P5. xport MU1 WM1 P6.
xport MU1 WM1 P7. xport MU1 WM1 P8. xport MU1 WM1 P9. xport MU1 WM1 P10. xport MU1 WM1 P11. xport MU1 WM1 P12. xport MU1 WM1 P13.
xport MU1 WM1 P14. xport MU1 WM1 P15. xport MU1 WM1 P16. xport MU1 WM1 P17. xport MU1 WM1 P18.
destruct r; try discriminate GRP; cbn [ctl_req_code creq_size creq_align] in *; cbn [creq_pre creq_ok] in PRE, OK.
all: try (destruct DSTP as (OBP & PAL & PIMG & POFF & AP & APB);
pose proof (APB _ ltac:(rewrite ELBD; left; reflexivity)) as APS; unfold blk_addr, blk_size in APS; cbn [fst snd] in APS;
pose proof OBP as (PP0 & PTOP & _); unfold APP_TOP in PTOP;
pose proof (aobj_munch bsegs _ m m1 P _ OBP MU1 (shfree_of_aobj bsegs _ m P _ OF1 OBP)) as OBP1).
-
subst OUTL. destruct PRE as (ws & WS & LWS). xport MU1 WM1 WS.
rewrite (EA1 ltac:(discriminate)).
eapply evt_cut.
{ eapply (nbarm_get_pi_gain S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| (clear - PIMG; unfold IMG_TOP_B in PIMG; lia)| exact P7| exact E6| exact WS| exact LWS| lia| exact POFF]. }
cbv beta. intros ms2 (m2 & F2 & ws2 & yt0 & ya0 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & -> & MU2 & WM2 & MI2 & WS2 & LWS2 & P7').
clear P7 WS. xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit usp); [lia| reflexivity| exact FR| exact MI2]. }
cbv beta. intros ms3 (F' & ->).
assert (ST2 : stk bsegs m2 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m2.
split; [reflexivity|].
split; [solve_munch MU1 MU2 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists ws2; split; [exact WS2| exact LWS2]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
-
subst OUTL. destruct PRE as ((ws & WS & LWS) & EXR). cbn [dec_exc_ready] in EXR. unfold NB_EXC_OFF in EXR.
xport MU1 WM1 WS. xport MU1 WM1 EXR.

pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in G1, G2, G3, G4.
apply (ro_cells_transport bsegs [(usp + -112, usp)] m m1 _ _) in G1; [| exact MU1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (ro_cells_transport bsegs [(usp + -112, usp)] m m1 _ _) in G2; [| exact MU1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (ro_cells_transport bsegs [(usp + -112, usp)] m m1 _ _) in G3; [| exact MU1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
apply (ro_cells_transport bsegs [(usp + -112, usp)] m m1 _ _) in G4; [| exact MU1 | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (CC1 : client_constsB m1)
by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
clear G1 G2 G3 G4.

pose proof P1 as P1c.
apply (f32_split bsegs m1 (S + 32) (j_excbuf j) 334) in P1c; [| rewrite E1; lia]. destruct P1c as (_ & P1c). change (Z.of_nat 334) with 334 in P1c.
replace (S + 32 + 4 * 334) with (S + 1368) in P1c by lia.
apply (f32_split bsegs m1 (S + 1368) _ 40) in P1c; [| rewrite length_skipn, E1; lia]. destruct P1c as (X0 & P1c). change (Z.of_nat 40) with 40 in P1c.
replace (S + 1368 + 4 * 40) with (S + 1528) in P1c by lia.
apply (f32_split bsegs m1 (S + 1528) _ 40) in P1c; [| rewrite !length_skipn, E1; lia]. destruct P1c as (X1 & P1c). change (Z.of_nat 40) with 40 in P1c.
replace (S + 1528 + 4 * 40) with (S + 1688) in P1c by lia.
apply (f32_split bsegs m1 (S + 1688) _ 40) in P1c; [| rewrite !length_skipn, E1; lia]. destruct P1c as (X2 & P1c). change (Z.of_nat 40) with 40 in P1c.
replace (S + 1688 + 4 * 40) with (S + 1848) in P1c by lia.
apply (f32_split bsegs m1 (S + 1848) _ 40) in P1c; [| rewrite !length_skipn, E1; lia]. destruct P1c as (X3 & P1c). clear P1c.
rewrite (EA1 ltac:(discriminate)).
eapply evt_cut.
{ eapply (nbarm_get_exc S P) with (usp := usp + -112) (lo := lo);
[exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| reflexivity| exact ST1| lia| exact LOS| lia| lia| exact OBP1| exact PAL| (clear - PIMG; unfold IMG_TOP_B in PIMG; lia)| exact WS| exact LWS
| lia| exact POFF| lia| exact PIMG| exact EXR| exact X0| exact X1| exact X2| exact X3
| rewrite length_firstn, length_skipn, E1; reflexivity| rewrite length_firstn, !length_skipn, E1; reflexivity
| rewrite length_firstn, !length_skipn, E1; reflexivity| rewrite length_firstn, !length_skipn, E1; reflexivity| exact CC1| exact FRM]. }
cbv beta. intros ms2 (m2 & F2 & fc2 & ws2 & xra & xs1 & xs2 & xs4 & xs5 & xs6 & xs7 & xs8 & xs9 & yt0 & yt1 & yt2 & ya0 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6
& -> & MU2 & WM2 & MI2 & ST2 & FRM2 & WS2 & LWS2 & EXR2 & X0' & X1' & X2' & X3').
clear WS EXR X0 X1 X2 X3 X0' X1' X2' X3' CC1. xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit usp); [lia| reflexivity| exact FR| exact MI2]. }
cbv beta. intros ms3 (F' & ->).
release_frame FR ST2 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc2, m2.
split; [reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]];
unfold ctlW; cbn [creq_ivs creq_size app]; intros x; rewrite !outside_cons, outside_blocks_ivs; cbn [fst snd outside creq_size]; intros (O1 & O2 & O3).
- split; [lia| exact I].
- split; [lia|]. split; [lia| exact I]. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; exists ws2; split; [exact WS2| exact LWS2]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros _. exact EXR2.
-
subst OUTL. destruct PRE as (w & ARG). xport MU1 WM1 ARG.
eapply evt_cut.
{ eapply (nbarm_get_dtx S P); [exact MI1| lia| lia| exact OBS1| exact S8| exact SOFF| exact OBP1| exact PAL| (clear - PIMG; unfold IMG_TOP_B in PIMG; lia)| exact P18| clear - Idt; lia]. }
cbv beta. intros ms2 (ya1 & ya2 & ->).
eapply evt_cut. { eapply (nbctl_exit_get usp P w); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 (F' & m3 & -> & MU3 & WM3 & MI3 & ARG3 & FR3).
clear ARG FR. xport_mem m1 MU3 WM3.
assert (ST3 : stk bsegs m3 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
unfold nbctl_frame in FR3. release_frame FR3 ST3 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m3.
split; [reflexivity|].
split; [solve_munch MU1 MU3 ELBD|].
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|]. unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post speex_decoder_ctl nb_decoder_ctl fst snd]; split; [exact ARG3| exact Idt]|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU3 WM3 EXQ. exact EXQ.
-
destruct OK as (EP & OFF160).
eapply evt_cut. { eapply (nbarm_set_isave S P); [exact MI1| lia| exact OBS1| exact S8| exact SOFF| exact P8]. }
cbv beta. intros ms2 (m2 & -> & P8' & MU2 & WM2 & MI2). clear P8.
xport_mem m1 MU2 WM2.
eapply evt_cut. { eapply (nbctl_exit usp); [lia| reflexivity| exact FR| exact MI2]. }
cbv beta. intros ms3 (F' & ->).
assert (ST2 : stk bsegs m2 lo (usp + -112)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| cbn; lia]).
release_frame FR ST2 usp.
apply evt_done. unfold rctl_post. do 14 eexists. exists F', fc, m2.
split; [reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]];
unfold ctlW; cbn [creq_ivs app]; intros x; rewrite !outside_cons, outside_blocks_ivs; cbn [fst snd outside]; intros (O1 & O3).
- split; [lia| exact I].
- split; [| exact I]. specialize (O3 _ ltac:(rewrite ELBD; left; reflexivity)). cbn [blk_addr blk_size fst snd] in O3. unfold NBSTATE_SIZEOF in O3. lia. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM|]. split; [exact ST2|].
split.
+ cbn [decst_rep speex_decoder_ctl nb_decoder_ctl fst snd]. split; [exact ELBD|].
split; [exact AL|]. split; [exact POS|]. split.
{ unfold nb_inv in *. cbn [set_nb_innov_save nb_count_lost nb_encode_submode nb_highpass_enabled nb_first nb_voc_offset nb_pitch_gain_buf_idx nb_submodeID
nb_dtx_enabled nb_isWideband nb_lpc_enh_enabled nb_sampling_rate nb_innov_save]. repeat split; try assumption; try lia. }
exists j. split; [exact JOK|]. split; [exact CBS|].
apply nb_cells_of_pieces; [exact JOK|].
assert (P8n : rw_cells bsegs m2 (S + 2184) [C8 (Z_to_bv 64 (nb_isave_ptr OUT (set_nb_innov_save st (Some off))))])
by (unfold nb_isave_ptr; cbn [set_nb_innov_save nb_innov_save]; rewrite <- EP; exact P8').
unfold nb_pieces. cbn -[Z.add Z.mul rw_cells f32 nb_isave_ptr cbs_cells].
repeat match goal with |- _ /\ _ => split end; eassumption.
+ split; [cbn [creq_post]; exact I|].
cbn [dec_exc_ready speex_decoder_ctl nb_decoder_ctl fst snd]. intros EXQ. xport MU1 WM1 EXQ. xport MU2 WM2 EXQ. exact EXQ.
Qed.
