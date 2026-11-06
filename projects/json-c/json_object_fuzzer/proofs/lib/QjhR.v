(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QfYR QfcC Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y Qbf8 QSzV QvBB QmBS QKwd Qlfl QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import Qbf8 QSzV QvBB.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Definition SCANEXP : Z := 0xd8134.
Definition SCANEXP_DEPTH : Z := 240.

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof. intros. apply (proj2 (isdigitc_iff c ltac:(lia))). lia. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof. intros c Hc H. destruct (isdigitc c) eqn:E; [|reflexivity]. exfalso. apply H. apply (proj1 (isdigitc_iff c Hc)). exact E. Qed.

Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
match scanexp_l1_loop fuelc (0%Z, c, f) with
| None => None
| Some (x, c, f) =>
match scanexp_l2_loop fuelc (x, c, f) with
| None => None
| Some (y, c, f) =>
match scanexp_l3_loop fuelc (c, f) with
| None => None
| Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
end end end.

Lemma scanexp_eq : forall fuelc f pok,
scanexp fuelc f pok =
(let '(c, f) := sh_getc f in
let '(neg, c, f) :=
(if ((c =? 43) || (c =? 45))%Z then
let neg := b2z (c =? 45)%Z in
let '(c, f) := sh_getc f in
let f := if negb (isdigitc c) && nz pok then sh_unget f else f in (neg, c, f)
else (0%Z, c, f)) in
scanexp_tail fuelc neg c f).
Proof.
intros fuelc f pok. unfold scanexp, scanexp_tail.
destruct (sh_getc f) as [c1 f1].
destruct (if ((c1 =? 43) || (c1 =? 45))%Z then _ else _) as [[neg c2] f2]. reflexivity.
Qed.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - SCANEXP_DEPTH) q
/\ rw_cells rsegs m' Fp (rf_cells T p true fR J)
/\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
scanexp fuelc f0 pok = Some (fR, e10) ->
rw_cells rsegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
(sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
(ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m (seg_rom rsegs)).

Section Scanexp.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Hpok : (0 <= pok <= 1)%Z.
Hypothesis Q0 : (0 <= q)%Z.
Hypothesis Q1 : (q < 2^63)%Z.

Notation POST := (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Notation RFJ' := (RFJ T txt p true J).
Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
mem_inv rsegs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -80) (frame j8) /\ stk rsegs m (q - SCANEXP_DEPTH) (q + -80)
/\ bytes_at rsegs m T (zbytes txt) /\ ssp_cells m canary.
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST & BY & [SSP1 SSP2]); unfold frame in FR; unfold SCANEXP_DEPTH in MU, ST;
unfold got_ssp, ssp_guard in SSP1, SSP2;
try (let LTX := fresh "LTX" in assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length; unfold zlength in * ).
Ltac mk_finv := unfold finv, frame, SCANEXP_DEPTH, ssp_cells, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _); reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="pre"] Lemma L_ret : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c fX,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true fX J) -> RFJ' k c fX -> (1 <= k)%Z -> fX = fR ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 e10) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8374) fc None m (seg_rom rsegs)).
Proof.
intros until fX. intros FI FC RJ Hk EX. subst fX. dest_finv FI. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold scanexp_rpost, SCANEXP_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY | split; [exact SSP1 | exact SSP2]].
Qed.

Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_end : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (v neg : Z),
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
(0 <= neg <= 1)%Z -> (-2^63 <= v < 2^63)%Z ->
fR = sh_unget f -> e10 = (if nz neg then - v else v)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8358) fc None m (seg_rom rsegs)).
Proof.
intros until neg. intros FI FC RJ Hk Rneg Rv HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
-
rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
-
rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_ND : forall m j8 (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
fR = sh_unget f -> e10 = LLONG_MIN_ ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd821c) fc None m (seg_rom rsegs)).
Proof.
intros until f. intros FI FC RJ Hk HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
- rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
- rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
Ltac unfold_fc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac post_getc :=
match goal with H : ssp_cells ?m' _ |- _ =>
repeat match goal with H2 : rw_cells _ _ 945024 _ |- _ => clear H2 | H2 : rw_cells _ _ 6565536 _ |- _ => clear H2 end;
destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
match goal with H : stk _ ?m' (q + -80 - 160)%Z _ |- _ =>
replace (q + -80 - 160)%Z with (q - 240)%Z in H by lia;
try match goal with H2 : stk _ _ (q - 240)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.

Ltac site_facts FC RJ k c f :=
unfold SCANEXP_DEPTH in SPLO, SPT, SG1; unfold got_ssp, ssp_guard in SG1, SG2, SG3;
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L3 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (y neg cX : Z) fX,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z ->
scanexp_l3_loop n (sh_getc f) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y else y)%Z -> (0 <= neg <= 1)%Z -> (-2^63 <= y < 2^63)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 10) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8338) fc None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc HL HfR He Rneg Ry.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
rewrite (surjective_pairing (sh_getc f)) in HL. cbn [scanexp_l3_loop scanexp_l3_body] in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 10) x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd8338) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros. rewrite (isdigitc_t (fst (sh_getc f))) in HL by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd8358) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros. rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. injection HL as E1 E2. subst cX fX.
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition LM : Z := 92233720368547758.
#[using="Type"] Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof. reflexivity. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L2 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) x1 k c f (y neg y2 c2 : Z) f2 n3 cX fX,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= y < LM)%Z ->
scanexp_l2_loop n (y, c, f) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 9) (Z_to_bv 64 c) (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd82c4) fc None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hy HL HL3 HfR He Rneg. pose proof Hy as Hy0. unfold LM in Hy.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l2_loop scanexp_l2_cond scanexp_l2_body] in HL. rewrite (isdigitc_t c), LM_eq in HL by lia.
replace (y <? LM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hy0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (y' := (10 * y + c - 48)%Z) in HL.
assert (Ry' : (0 <= y' <= 10 * LM - 1)%Z) by (unfold y', LM in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x12' x13' x14' x15' x16' x17' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 9) x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd8310) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold LM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite LM_eq in HL. replace (y' <? LM) with false in HL by (symmetry; apply Z.ltb_ge; unfold LM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_t (fst (sh_getc f))) in HL3 by lia.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs.
eapply L_L3 with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x12' x13' x14' x15' x16' x17' x18' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') x10' (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd8318) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E4 E5. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
clear IH HL HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition IM : Z := 214748364.
#[using="Type"] Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof. reflexivity. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L1 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) x1 k c f (x neg xv c1 : Z) f1 n2 y2 c2 f2 n3 cX fX,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= x < IM)%Z ->
scanexp_l1_loop n (x, c, f) = Some (xv, c1, f1) ->
scanexp_l2_loop n2 (xv, c1, f1) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 x) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8258) fc None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hx HL HL2 HL3 HfR He Rneg. pose proof Hx as Hx0. unfold IM in Hx.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l1_loop scanexp_l1_cond scanexp_l1_body] in HL. rewrite (isdigitc_t c), IM_eq in HL by lia.
replace (x <? IM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hx0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (x' := (10 * x + c - 48)%Z) in HL.
assert (Rx' : (0 <= x' < 2^31)%Z) by (unfold x' in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd82a8) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold IM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite IM_eq in HL. replace (x' <? IM) with false in HL by (symmetry; apply Z.ltb_ge; unfold IM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst xv c1 f1.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs. zs.
eapply L_L2 with (k := (k + 1)%Z); try eassumption; unfold LM; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x19' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt rsegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xd82b0) fc None m2 (seg_rom rsegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst xv c1 f1.
destruct n2 as [|n2']; [discriminate HL2|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL2.
rewrite (isdigitc_f (fst (sh_getc f))) in HL2 by lia. cbn [andb] in HL2. injection HL2 as E4 E5 E6. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E7 E8. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL HL2 HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E4 : forall m j8 (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c f = Some (fR, e10) -> (0 <= neg <= 1)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8214) fc None m (seg_rom rsegs)).
Proof.
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg.
pose proof FI as FI'. dest_finv FI'. unfold scanexp_tail in HT.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb] in HT.
destruct (scanexp_l1_loop fuelc (0%Z, c, f)) as [[[xv c1] f1]|] eqn:HL1; [|discriminate HT].
destruct (scanexp_l2_loop fuelc (xv, c1, f1)) as [[[y2 c2] f2]|] eqn:HL2; [|discriminate HT].
destruct (scanexp_l3_loop fuelc (c2, f2)) as [[cX fX]|] eqn:HL3; [|discriminate HT].
injection HT as E1 E2.
zs. fixw2. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
zs. zs. zs.
eapply L_L1 with (k := k); try eassumption; unfold IM; try lia; try mlia2. all: symmetry; assumption.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb] in HT. injection HT as E1 E2.
eapply L_ND; try eassumption; try lia. all: symmetry; assumption.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_C4 : forall m j8 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (3 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c (if negb (isdigitc c) && nz pok then sh_unget f else f) = Some (fR, e10) ->
(0 <= neg <= 1)%Z -> pok <> 0%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd81f4) fc None m (seg_rom rsegs)).
Proof.
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg Hpk.
replace (nz pok) with true in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [lia|reflexivity]).
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb andb] in HT.
eapply L_E4; try eassumption; try lia.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb andb] in HT.
site_facts FC RJ k c f.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
pose proof (stdio_unget f) as Hstu. rewrite Hst in Hstu.
destruct (sh_shlim_neg f) eqn:SN.
+ rewrite (rf_unget_nop f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ rewrite (rf_unget_eq f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
1: mk_finv.
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_SGN : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (c = 43 \/ c = 45)%Z ->
scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10) ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd81a4) fc None m (seg_rom rsegs)).
Proof.
intros until f. intros FI FC RJ Hk Hst Hc HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (Rneg : (0 <= b2z (c =? 45)%Z <= 1)%Z) by (unfold b2z; destruct (c =? 45)%Z; lia).
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia. 1: mk_finv.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
+ eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2. mk_finv.
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2.
1: mk_finv. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ zs. eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia.
1: mk_finv. 1: unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_6c : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z -> c <> 43%Z ->
(c = 45%Z -> scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10)) ->
(c <> 45%Z -> scanexp_tail fuelc 0%Z c f = Some (fR, e10)) ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd819c) fc None m (seg_rom rsegs)).
Proof.
intros until f. intros FI FC RJ Hk Hst Hc H43 H45 Hother.
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
zs. zs. fixw2. zs.
eapply L_E4 with (k := k) (neg := 0%Z); try eassumption; try lia. apply Hother. mlia2.
- eapply L_SGN with (k := k); try eassumption; try lia. 1: right; mlia2. apply H45. mlia2.
Qed.

#[using="pre post fuelc HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rw_cells rsegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
bytes_at rsegs m0 T (zbytes txt) -> ssp_cells m0 canary ->
stk rsegs m0 (q - SCANEXP_DEPTH) q -> mem_inv rsegs m0 ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m0 (seg_rom rsegs)).
Proof.
intros until t6. intros FC RJ Hk Hc0nz BY [SSP1 SSP2] ST MI.
pose proof (munch_refl [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
unfold SCANEXP, SCANEXP_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length. unfold zlength in *.
pose proof HM as HT. rewrite scanexp_eq, (surjective_pairing (sh_getc f0)) in HT. cbn beta iota zeta in HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0nz) as RJ1.
pose proof (stdio_getc f0) as Hst1.
assert (Rc' : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).

assert (JS : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) = 43 \/ fst (sh_getc f0) = 45)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd81a4) fc None m2 (seg_rom rsegs))).
{ intros until x1. intros FI2 FC2 H4345.
eapply L_SGN with (k := (kmin0 + 1)%Z); try eassumption; try lia.
replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; destruct H4345 as [E|E]; rewrite E; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT. }
assert (J6 : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells rsegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) <> 43)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xd819c) fc None m2 (seg_rom rsegs))).
{ intros until x1. intros FI2 FC2 H43.
eapply L_6c with (k := (kmin0 + 1)%Z); try eassumption; try lia.
- intros E45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; rewrite E45; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT.
- intros N45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with false in HT
by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; assumption).
cbn beta iota zeta in HT. exact HT. }
site_facts FC RJ kmin0 c0 f0.
zs. carve_frame 80%nat ST.
do 9 zs.
zs.
destruct (Z.eq_dec (T + sh_rpos f0) (rf_rend T p true f0)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
destruct (ST0 STD) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply JS; [mk_finv | exact FC | left; mlia2].
+ eapply J6; [mk_finv | exact FC | mlia2].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f0)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f0) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f0) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f0))) by lia. clear RDb.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply J6; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | mlia2].
+ zs. eapply JS; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | left; mlia2].
Qed.
End Scanexp.

Lemma scanexp_rspec : scanexp_rstmt.
Proof.
unfold scanexp_rstmt. intros.
eapply L_main; eassumption.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeTw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1BE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1BE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvBB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvBB.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quzq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quzq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlfl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlfl.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Definition SCANEXP : Z := 0xda7f8.
Definition SCANEXP_DEPTH : Z := 240.

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof. intros. apply (proj2 (isdigitc_iff c ltac:(lia))). lia. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof. intros c Hc H. destruct (isdigitc c) eqn:E; [|reflexivity]. exfalso. apply H. apply (proj1 (isdigitc_iff c Hc)). exact E. Qed.

Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
match scanexp_l1_loop fuelc (0%Z, c, f) with
| None => None
| Some (x, c, f) =>
match scanexp_l2_loop fuelc (x, c, f) with
| None => None
| Some (y, c, f) =>
match scanexp_l3_loop fuelc (c, f) with
| None => None
| Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
end end end.

Lemma scanexp_eq : forall fuelc f pok,
scanexp fuelc f pok =
(let '(c, f) := sh_getc f in
let '(neg, c, f) :=
(if ((c =? 43) || (c =? 45))%Z then
let neg := b2z (c =? 45)%Z in
let '(c, f) := sh_getc f in
let f := if negb (isdigitc c) && nz pok then sh_unget f else f in (neg, c, f)
else (0%Z, c, f)) in
scanexp_tail fuelc neg c f).
Proof.
intros fuelc f pok. unfold scanexp, scanexp_tail.
destruct (sh_getc f) as [c1 f1].
destruct (if ((c1 =? 43) || (c1 =? 45))%Z then _ else _) as [[neg c2] f2]. reflexivity.
Qed.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - SCANEXP_DEPTH) q
/\ rw_cells usegs m' Fp (rf_cells T p true fR J)
/\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
/\ bytes_at usegs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
scanexp fuelc f0 pok = Some (fR, e10) ->
rw_cells usegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
(sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk usegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
(ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m (seg_rom usegs)).

Section Scanexp.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Hpok : (0 <= pok <= 1)%Z.
Hypothesis Q0 : (0 <= q)%Z.
Hypothesis Q1 : (q < 2^63)%Z.

Notation POST := (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m0).
Notation SPv := (Z_to_bv 64 (q + -80)).
Notation RFJ' := (RFJ T txt p true J).
Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
mem_inv usegs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono usegs m0 m
/\ rw_cells usegs m (q + -80) (frame j8) /\ stk usegs m (q - SCANEXP_DEPTH) (q + -80)
/\ bytes_at usegs m T (zbytes txt) /\ ssp_cells m canary.
Ltac dest_finv H := destruct H as (MI & MU & WM & FR & ST & BY & [SSP1 SSP2]); unfold frame in FR; unfold SCANEXP_DEPTH in MU, ST;
unfold got_ssp, ssp_guard in SSP1, SSP2;
try (let LTX := fresh "LTX" in assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length; unfold zlength in * ).
Ltac mk_finv := unfold finv, frame, SCANEXP_DEPTH, ssp_cells, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _); reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="pre"] Lemma L_ret : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c fX,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true fX J) -> RFJ' k c fX -> (1 <= k)%Z -> fX = fR ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 e10) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xdaa38) fc None m (seg_rom usegs)).
Proof.
intros until fX. intros FI FC RJ Hk EX. subst fX. dest_finv FI. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
do 12 zs.
release_frame FR ST q.
apply evt_done. unfold scanexp_rpost, SCANEXP_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY | split; [exact SSP1 | exact SSP2]].
Qed.

Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_end : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (v neg : Z),
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
(0 <= neg <= 1)%Z -> (-2^63 <= v < 2^63)%Z ->
fR = sh_unget f -> e10 = (if nz neg then - v else v)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xdaa1c) fc None m (seg_rom usegs)).
Proof.
intros until neg. intros FI FC RJ Hk Rneg Rv HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
-
rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
-
rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_ND : forall m j8 (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
fR = sh_unget f -> e10 = LLONG_MIN_ ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda8e0) fc None m (seg_rom usegs)).
Proof.
intros until f. intros FI FC RJ Hk HfR He.
pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof RJ as RJ2. destruct RJ2 as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
destruct (sh_shlim_neg f) eqn:SN.
- rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
- rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
Ltac unfold_fc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

Ltac post_getc :=
match goal with H : ssp_cells ?m' _ |- _ =>
repeat match goal with H2 : rw_cells _ _ 954256 _ |- _ => clear H2 | H2 : rw_cells _ _ 6575456 _ |- _ => clear H2 end;
destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
match goal with H : stk _ ?m' (q + -80 - 160)%Z _ |- _ =>
replace (q + -80 - 160)%Z with (q - 240)%Z in H by lia;
try match goal with H2 : stk _ _ (q - 240)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.

Ltac site_facts FC RJ k c f :=
unfold SCANEXP_DEPTH in SPLO, SPT, SG1; unfold got_ssp, ssp_guard in SG1, SG2, SG3;
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L3 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (y neg cX : Z) fX,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z ->
scanexp_l3_loop n (sh_getc f) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y else y)%Z -> (0 <= neg <= 1)%Z -> (-2^63 <= y < 2^63)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 10) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda9fc) fc None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc HL HfR He Rneg Ry.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
rewrite (surjective_pairing (sh_getc f)) in HL. cbn [scanexp_l3_loop scanexp_l3_body] in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 10) x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xda9fc) fc None m2 (seg_rom usegs))).
{ intros Hd. intros. rewrite (isdigitc_t (fst (sh_getc f))) in HL by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xdaa1c) fc None m2 (seg_rom usegs))).
{ intros Hd. intros. rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. injection HL as E1 E2. subst cX fX.
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. fixw2. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition LM : Z := 92233720368547758.
#[using="Type"] Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof. reflexivity. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L2 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) x1 k c f (y neg y2 c2 : Z) f2 n3 cX fX,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= y < LM)%Z ->
scanexp_l2_loop n (y, c, f) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 9) (Z_to_bv 64 c) (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda988) fc None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hy HL HL3 HfR He Rneg. pose proof Hy as Hy0. unfold LM in Hy.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l2_loop scanexp_l2_cond scanexp_l2_body] in HL. rewrite (isdigitc_t c), LM_eq in HL by lia.
replace (y <? LM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hy0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (y' := (10 * y + c - 48)%Z) in HL.
assert (Ry' : (0 <= y' <= 10 * LM - 1)%Z) by (unfold y', LM in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x12' x13' x14' x15' x16' x17' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 9) x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xda9d4) fc None m2 (seg_rom usegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold LM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite LM_eq in HL. replace (y' <? LM) with false in HL by (symmetry; apply Z.ltb_ge; unfold LM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_t (fst (sh_getc f))) in HL3 by lia.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs.
eapply L_L3 with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x12' x13' x14' x15' x16' x17' x18' x19' x23' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') x10' (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xda9dc) fc None m2 (seg_rom usegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E4 E5. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; unfold LM in *; try lia. }
clear IH HL HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

Definition IM : Z := 214748364.
#[using="Type"] Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof. reflexivity. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L1 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) x1 k c f (x neg xv c1 : Z) f1 n2 y2 c2 f2 n3 cX fX,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= x < IM)%Z ->
scanexp_l1_loop n (x, c, f) = Some (xv, c1, f1) ->
scanexp_l2_loop n2 (xv, c1, f1) = Some (y2, c2, f2) ->
scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 x) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda91c) fc None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; [intros; discriminate|].
intros until fX. intros FI FC RJ Hk Hst Hc Hx HL HL2 HL3 HfR He Rneg. pose proof Hx as Hx0. unfold IM in Hx.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
cbn [scanexp_l1_loop scanexp_l1_cond scanexp_l1_body] in HL. rewrite (isdigitc_t c), IM_eq in HL by lia.
replace (x <? IM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hx0)). cbn [andb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
set (x' := (10 * x + c - 48)%Z) in HL.
assert (Rx' : (0 <= x' < 2^31)%Z) by (unfold x' in *; lia).
assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xda96c) fc None m2 (seg_rom usegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
pose proof FI2 as FI'. dest_finv FI'. unfold IM in *.
zs. zs. brs K.
- eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try lia.
- destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite IM_eq in HL. replace (x' <? IM) with false in HL by (symmetry; apply Z.ltb_ge; unfold IM; lia). rewrite Bool.andb_false_r in HL.
injection HL as E1 E2 E3. subst xv c1 f1.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia); [ exfalso; lia | ]); try (exfalso; mlia2). zs. zs. zs.
eapply L_L2 with (k := (k + 1)%Z); try eassumption; unfold LM; try lia. }
assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x19' x28' x29' x30' x31' : word) x1',
finv m2 j8' -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
evt usegs POST
(MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
F (Z_to_bv 64 0xda974) fc None m2 (seg_rom usegs))).
{ intros Hd. intros until x1'. intros FI2 FC2.
destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst xv c1 f1.
destruct n2 as [|n2']; [discriminate HL2|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL2.
rewrite (isdigitc_f (fst (sh_getc f))) in HL2 by lia. cbn [andb] in HL2. injection HL2 as E4 E5 E6. subst y2 c2 f2.
destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
injection HL3 as E7 E8. subst cX fX.
pose proof FI2 as FI'. dest_finv FI'.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
eapply L_end with (k := (k + 1)%Z); try eassumption; try lia. }
clear IH HL HL2 HL3.
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
zs. zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply ND; [mlia2 | mk_finv | exact FC].
+ eapply DIG; [mlia2 | mk_finv | exact FC].
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. zs. fixw2. zs. fixw2.
let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
let v := getreg 10%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
+ zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E4 : forall m j8 (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c f = Some (fR, e10) -> (0 <= neg <= 1)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda8d8) fc None m (seg_rom usegs)).
Proof.
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg.
pose proof FI as FI'. dest_finv FI'. unfold scanexp_tail in HT.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb] in HT.
destruct (scanexp_l1_loop fuelc (0%Z, c, f)) as [[[xv c1] f1]|] eqn:HL1; [|discriminate HT].
destruct (scanexp_l2_loop fuelc (xv, c1, f1)) as [[[y2 c2] f2]|] eqn:HL2; [|discriminate HT].
destruct (scanexp_l3_loop fuelc (c2, f2)) as [[cX fX]|] eqn:HL3; [|discriminate HT].
injection HT as E1 E2.
zs. fixw2. zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)); try (exfalso; mlia2).
zs. zs. zs.
eapply L_L1 with (k := k); try eassumption; unfold IM; try lia; try mlia2. all: symmetry; assumption.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb] in HT. injection HT as E1 E2.
eapply L_ND; try eassumption; try lia. all: symmetry; assumption.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_C4 : forall m j8 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (3 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
scanexp_tail fuelc neg c (if negb (isdigitc c) && nz pok then sh_unget f else f) = Some (fR, e10) ->
(0 <= neg <= 1)%Z -> pok <> 0%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda8b8) fc None m (seg_rom usegs)).
Proof.
intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg Hpk.
replace (nz pok) with true in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [lia|reflexivity]).
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
rewrite (isdigitc_t c) in HT by mlia2. cbn [negb andb] in HT.
eapply L_E4; try eassumption; try lia.
-
rewrite (isdigitc_f c) in HT by mlia2. cbn [negb andb] in HT.
site_facts FC RJ k c f.
pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
pose proof (stdio_unget f) as Hstu. rewrite Hst in Hstu.
destruct (sh_shlim_neg f) eqn:SN.
+ rewrite (rf_unget_nop f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ | exfalso; lia ]).
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
+ rewrite (rf_unget_eq f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs.
eapply L_ND with (k := (k - 1)%Z); try eassumption; try lia.
all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
1: mk_finv.
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_SGN : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (c = 43 \/ c = 45)%Z ->
scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10) ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda868) fc None m (seg_rom usegs)).
Proof.
intros until f. intros FI FC RJ Hk Hst Hc HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
assert (Rneg : (0 <= b2z (c =? 45)%Z <= 1)%Z) by (unfold b2z; destruct (c =? 45)%Z; lia).
pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia. 1: mk_finv.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
+ eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2. mk_finv.
-
pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
zs. zs. fixw2.
let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+  eapply L_C4 with (k := (k + 1)%Z); try eassumption; try lia; try mlia2.
1: mk_finv. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ zs. eapply L_E4 with (k := (k + 1)%Z); try eassumption; try lia.
1: mk_finv. 1: unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_6c : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
finv m j8 -> rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z -> c <> 43%Z ->
(c = 45%Z -> scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
(if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10)) ->
(c <> 45%Z -> scanexp_tail fuelc 0%Z c f = Some (fR, e10)) ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda860) fc None m (seg_rom usegs)).
Proof.
intros until f. intros FI FC RJ Hk Hst Hc H43 H45 Hother.
pose proof FI as FI'. dest_finv FI'.
zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia)).
-
zs. zs. fixw2. zs.
eapply L_E4 with (k := k) (neg := 0%Z); try eassumption; try lia. apply Hother. mlia2.
- eapply L_SGN with (k := k); try eassumption; try lia. 1: right; mlia2. apply H45. mlia2.
Qed.

#[using="pre post fuelc HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rw_cells usegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
bytes_at usegs m0 T (zbytes txt) -> ssp_cells m0 canary ->
stk usegs m0 (q - SCANEXP_DEPTH) q -> mem_inv usegs m0 ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m0 (seg_rom usegs)).
Proof.
intros until t6. intros FC RJ Hk Hc0nz BY [SSP1 SSP2] ST MI.
pose proof (munch_refl [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
unfold SCANEXP, SCANEXP_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length. unfold zlength in *.
pose proof HM as HT. rewrite scanexp_eq, (surjective_pairing (sh_getc f0)) in HT. cbn beta iota zeta in HT.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0nz) as RJ1.
pose proof (stdio_getc f0) as Hst1.
assert (Rc' : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).

assert (JS : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) = 43 \/ fst (sh_getc f0) = 45)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda868) fc None m2 (seg_rom usegs))).
{ intros until x1. intros FI2 FC2 H4345.
eapply L_SGN with (k := (kmin0 + 1)%Z); try eassumption; try lia.
replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; destruct H4345 as [E|E]; rewrite E; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT. }
assert (J6 : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
finv m2 j8 -> rw_cells usegs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
(fst (sh_getc f0) <> 43)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0xda860) fc None m2 (seg_rom usegs))).
{ intros until x1. intros FI2 FC2 H43.
eapply L_6c with (k := (kmin0 + 1)%Z); try eassumption; try lia.
- intros E45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
by (symmetry; rewrite E45; reflexivity).
rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT.
- intros N45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with false in HT
by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; assumption).
cbn beta iota zeta in HT. exact HT. }
site_facts FC RJ kmin0 c0 f0.
zs. carve_frame 80%nat ST.
do 9 zs.
zs.
destruct (Z.eq_dec (T + sh_rpos f0) (rf_rend T p true f0)) as [SLOW|FAST].
-
pose proof FC as FC0. unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) as (STD & EJ & Hn & Hrp & Hc0).
destruct (ST0 STD) as [TXT Hpre].
zs. zs. callw (eapply shgetc_callJ;
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
zs. zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply JS; [mk_finv | exact FC | left; mlia2].
+ eapply J6; [mk_finv | exact FC | mlia2].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f0)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
unfold_fc2 FC.
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f0) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f0) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f0))) by lia. clear RDb.
zs. zs. (if_cases K2; zify_cond K2; try (rewrite ?signed_of_Z in K2 by lia)).
+ eapply J6; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | mlia2].
+ zs. eapply JS; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | left; mlia2].
Qed.
End Scanexp.

Lemma scanexp_rspec : scanexp_rstmt.
Proof.
unfold scanexp_rstmt. intros.
eapply L_main; eassumption.
Qed.
