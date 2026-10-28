(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g7 X1ff X1fn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

#[using="Type"] Lemma zbv_m64 : forall x, Z_to_bv 64 (18446744073709551615 - x) = Z_to_bv 64 (- x - 1).
Proof.
intros x. apply zbv_eqm. replace (18446744073709551615 - x) with ((- x - 1) + 1 * 18446744073709551616) by lia.
change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma srl30_g : forall x, 0 <= x < 2^29 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (x + 536870912)) 30) = 0.
Proof.
intros x Hx. unfold bv_wrap, bv_modulus. cbn -[Z.modulo Z.shiftr].
rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.
Ltac after_unpack b0 bb n rj Lrj OBJ bs DAT Hbs SIDE OKp OKn Hv Lbs :=
try rename MI0 into MI; rewrite (unpack_pair bb n) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub bb n) |- _ =>
destruct H as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE); unfold bits_cells in OBJ end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv bb n) |- _ => subst v end;
pose proof (speex_bits_unpack_unsigned_ok bb n _ _ OKp ltac:(lia) (unpack_pair bb n)) as (OKn & Hv & _);
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0)
by (let X := fresh in pose proof OKn as X; unfold bits_ok in X; rewrite Hbs, zlength_map_unsigned, ?ub_size in X; lia).

Ltac thaw_rw H MUF WMF :=
eapply (rw_cells_transport rsegs _ _ _ _ _) in H;
[| exact MUF | exact WMF | cbn [disjoint_from]; rewrite ?cells_size_f32; cbn [cells_size csize Nat.add length]; repeat split; alia ].
Ltac thaw_u8 H MUF WMF :=
eapply (u8arr_transport rsegs _ _ _ _ _) in H; [| exact MUF | exact WMF | cbn [disjoint_from]; repeat split; alia ].
Ltac thaw_u32 H MUF WMF :=
eapply (u32arr_transport rsegs _ _ _ _ _) in H; [| exact MUF | exact WMF | cbn [disjoint_from]; repeat split; alia ].

#[using="Type"] Lemma pitch_unquant_3tap_proof : forall p, ltp_params_ok p -> @ltp_unquant_stmt ptr (LtpPitchUnquant3tap p).
Proof.
intros p (PB & GB & GSZ).
unfold ltp_unquant_stmt. intros until m.
intros REP OK EBC EB1 EB2 EBm E32C L32 PVC PGC LPG PARC PARB GLA ARGS Hst1 Hst2 Hfin Hoff STK LO GLO
AQ1 AQ2 AQ3 AQ4 AQ5 AQ6 AQ7 AQ8 AQ9 AQ10 AQ11 AQ12 AQ13 AQ14 AQ15 AQ16 AQ17 AQ18 AQ19 AQ20
EXm E32m E32p PVm PVp PGm PGp PARa -> -> -> -> -> -> -> -> MI FRM.
destruct PARa as (PARm & PARp & APARGS).
cbn [ltp_pitch_span] in Hst2. unfold ltp_entry, A_pitch_unquant_3tap.
unfold LTP_DEPTH, NB_GLOBALS_TOP in *. assert (BS : BITS_SIZEOF = 48) by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rsp.
pose proof REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE).
pose proof SIDE as sfP_; first [ sf_destruct 6%nat sfP_ as AL Apos Dpos BUFMAX _ SEP | sf_fb; destruct sfP_ as (AL & Apos & Dpos & BUFMAX & _ & SEP) ]. unfold BITS_BUF_MAX in BUFMAX.
unfold bits_cells in OBJ. clear REP.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GBd. cbn [cells_size csize Nat.add length] in GBd.
pose proof (u8arr_bound _ _ _ _ DAT) as DB.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
pose proof (rw_cells_bound _ _ _ _ EBC) as GE. rewrite cells_size_f32 in GE.
pose proof (rw_cells_bound _ _ _ _ E32C) as G32. rewrite cells_size_f32, L32 in G32.
pose proof (rw_cells_bound _ _ _ _ PVC) as GPV. cbn [cells_size csize Nat.add] in GPV.
pose proof (rw_cells_bound _ _ _ _ PGC) as GPG. rewrite cells_size_f32, LPG in GPG.
pose proof (rw_cells_bound _ _ _ _ ARGS) as GAR. cbn [cells_size csize Nat.add] in GAR.
destruct pgs as [|g0 [|g1 [|g2 [|? ?]]]]; try (cbn in LPG; lia).
assert (P2lo : 0 < 2 ^ ltp_pitch_bits p) by (apply Z.pow_pos_nonneg; lia).
assert (G2lo : 0 < 2 ^ ltp_gain_bits p) by (apply Z.pow_pos_nonneg; lia).
pose proof (gain_cdbk_addr_range (ltp_gain_cdbk p)) as GR.
unfold ltp_par_cells in PARC.
pose proof (munch_refl [(lo, bv_unsigned sp); (exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
set (e0 := (exc - EB) / 4).
assert (He0 : exc = EB + 4 * e0) by (pose proof (Z.div_mod (exc - EB) 4 ltac:(lia)); lia).
clearbody e0. clear EBm.

pose proof (conj EBC (conj E32C (conj PVC (conj PGC (conj OBJ DAT))))) as HIDE. clear EBC E32C PVC PGC OBJ DAT.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUF. pose proof (wmono_refl rsegs m) as WMF.
carve_frame 128%nat STK.
apply (rw_cells_split_CB rsegs _ _ [] 128%nat junk [] [4;4;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
cbn [app mk_CB_cells] in FR.

do 15 zstep.
first [ sf_destruct 6%nat HIDE as EBC E32C PVC PGC OBJ DAT | sf_fb; destruct HIDE as (EBC & E32C & PVC & PGC & OBJ & DAT) ].
thaw_rw OBJ MUF WMF. thaw_u8 DAT MUF WMF. thaw_rw EBC MUF WMF. thaw_rw E32C MUF WMF. thaw_rw PVC MUF WMF. thaw_rw PGC MUF WMF.
clear MUF WMF.

pose proof (u32arr_of_f32 rsegs _ _ _ EBC) as EBA. pose proof (u32arr_of_f32 rsegs _ _ _ E32C) as E32A. clear EBC E32C.
rewrite f32_cons, f32_cons, f32_cons, f32_nil in PGC.
pose proof (conj EBA (conj E32A (conj PVC PGC))) as HIDE. clear EBA E32A PVC PGC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF)] mc) as MUB; pose proof (wmono_refl rsegs mc) as WMB end.

zstep. if_false_z.
zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. rewrite sx32_small by (unfold int31; lia).
zstep. zstep. if_false_z.
zstep. zstep. if_false_z.
zstep. zstep.
zstep. zstep. zstep. zstep. zstep. rewrite !Z.mul_0_r. change (bv_swrap 32 0) with 0. if_false_z.
zstep.
zstep. zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. rewrite sx32_small by (unfold int31; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(A, A + BITS_SIZEOF)] mc) as MUU; pose proof (wmono_refl rsegs mc) as WMU end.
pose proof (conj FR ARGS) as HFR. clear FR ARGS.
zstep. rebits REP A D b rj Lrj OBJ bs DAT Hbs SIDE.
zstep; call (speex_bits_unpack_unsigned_spec A D b (ltp_pitch_bits p)); [exact REP | exact OK | lia | exact MI |]. clear REP.
after_unpack b b (ltp_pitch_bits p) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1 OK OK1 Hv1 Lbs1.
zstep. zstep. zstep. rewrite (swrap32_small (uv b (ltp_pitch_bits p) + start)) by lia. if_false_z.
zstep. rewrite sx32_small by (unfold int31; lia). clear PARC.
rebits REP A D (ub b (ltp_pitch_bits p)) rj1 Lrj1 OBJ1 bs1 DAT1 Hbs1 SIDE1.
zstep. zstep; call (speex_bits_unpack_unsigned_spec A D (ub b (ltp_pitch_bits p)) (ltp_gain_bits p)); [exact REP | exact OK1 | lia | exact MI |]. clear REP.
after_unpack b (ub b (ltp_pitch_bits p)) (ltp_gain_bits p) rj2 Lrj2 OBJ2 bs2 DAT2 Hbs2 SIDE2 OK1 OK2 Hv2 Lbs2.
destruct HFR as [FR ARGS]. thaw_rw FR MUU WMU. thaw_rw ARGS MUU WMU. clear MUU WMU.
clear Hbs Hbs1 SIDE SIDE1 OK1 Lrj Lrj1 Lbs Lbs1 GBd DB. clear rj rj1 bs bs1.
zstep. zstep. zstep. rewrite srl30_g by lia.
zstep. if_false_z.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. sw32.
zstep. zstep. zstep. if_false_z.
zstep. zstep. rewrite (lxs64_nn (uv (ub b (ltp_pitch_bits p)) (ltp_gain_bits p) * 4)) by lia. zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
destruct (gain_cdbk_ro (ltp_gain_cdbk p) _ MI) as (GCD & GRO & LGC).
set (gi := uv (ub b (ltp_pitch_bits p)) (ltp_gain_bits p)) in *.
assert (GI4 : gi * 4 + 2 < gain_cdbk_size (ltp_gain_cdbk p)) by lia.
assert (Hn0 : nth_error GCD (Z.to_nat (gi * 4)) = Some (nth (Z.to_nat (gi * 4)) GCD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs _ _ GCD (gi * 4) _ _ GRO Hn0 ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD Hn0.
do 11 zstep. if_false_z.
zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. if_false_z.
assert (Hn1 : nth_error GCD (Z.to_nat (gi * 4 + 1)) = Some (nth (Z.to_nat (gi * 4 + 1)) GCD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs _ _ GCD (gi * 4 + 1) _ _ GRO Hn1 ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD Hn1.
do 7 zstep. if_false_z.
zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. if_false_z.
assert (Hn2 : nth_error GCD (Z.to_nat (gi * 4 + 2)) = Some (nth (Z.to_nat (gi * 4 + 2)) GCD (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read rsegs _ _ GCD (gi * 4 + 2) _ _ GRO Hn2 ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD Hn2.
do 5 zstep. clear GRO LGC.
zstep. if_true. clear ARGS GAR.

first [ sf_destruct 4%nat HIDE as EBA E32A PVC PGC | sf_fb; destruct HIDE as (EBA & E32A & PVC & PGC) ].
thaw_u32 EBA MUB WMB. thaw_u32 E32A MUB WMB. thaw_rw PVC MUB WMB. thaw_rw PGC MUB WMB. clear MUB WMB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(lo, bv_unsigned sp); (exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12)] mc) as MU2;
pose proof (wmono_refl rsegs mc) as WM2 end.
pose proof (conj OBJ2 DAT2) as HIDE2. clear OBJ2 DAT2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160); (pv, pv + 4); (pg, pg + 12)] mc) as MU5; pose proof (wmono_refl rsegs mc) as WM5 end.
pose proof (conj EBA I) as HIDE5. clear EBA.

zstep. if_false_z. zstep. zstep. if_false_z.
zstep.
zstep. if_false_z. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. if_false_z.
zstep. zstep. if_false_z.
zstep. zstep.
zstep. change (Z.shiftl 40 2) with 160. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MU3; pose proof (wmono_refl rsegs mc) as WM3 end.
pose proof (conj PVC PGC) as HIDE3. clear PVC PGC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (E32J : rw_cells rsegs mc e32 [CB (Z.to_nat 160) (u32s e32s)])
by (apply (rw_cells_samebytes rsegs mc e32 _ _ (f32_of_u32arr rsegs _ _ _ E32A));
[cbn; rewrite u32s_length, L32; split; [reflexivity| exact I]
| rewrite cells_bytes_f32; cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity
| rewrite cells_size_f32, L32; reflexivity]) end.
clear E32A. pose proof (conj E32J I) as XJ. clear E32J.
zstep; call (pmemset_specZ e32 160 0 (u32s e32s)); [exact (proj1 XJ) | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | (clear - G32 e32; lia) |].
clear XJ.
try rename MI0 into MI.
lazymatch goal with H : rw_cells rsegs ?mc e32 [CB _ (repeat _ _)] |- _ =>
rewrite u32s_zero40 in H; apply u8arr_of_rw_cells in H;
assert (E32A : u32arr rsegs mc e32 (repeat (Z_to_bv 64 0) 40))
by (destruct H as [HB HW]; split; [exact HB| rewrite u32s_length in HW; exact HW]); clear H end.
pose proof (proj1 HIDE5) as EBA. clear HIDE5. thaw_u32 EBA MU5 WM5. clear MU5 WM5.
zstep. sw32. zstep. brF.
do 10 zstep. cond_prep.
assert (EBm4 : EB mod 4 = 0) by (rewrite He0 in EXm; Z.div_mod_to_equations; lia).
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0] ++ [c1; c2; c3] ++ rest) in FR end.
apply rw_cells_app in FR. destruct FR as [FR1 FR]. apply rw_cells_app in FR. destruct FR as [FRG FR3].
cbn [cells_size csize Nat.add length app] in FRG, FR3.
lazymatch type of FRG with rw_cells _ _ ?a [C4 ?u; C4 ?v; C4 ?w] =>
replace a with (bv_unsigned sp + -124) in FRG by lia;
pose proof (u32arr_of_f32 rsegs _ _ [u; v; w] ltac:(rewrite f32_cons, f32_cons, f32_cons, f32_nil; exact FRG)) as GA; clear FRG end.
lazymatch type of FR3 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -112) in FR3 by lia end.
pose proof (u32arr_bound _ _ _ _ EBA) as BE.
pose proof (conj FR1 FR3) as HIDE4. clear FR1 FR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MU4; pose proof (wmono_refl rsegs mc) as WM4 end.

pose proof (conj E32A I) as XA. clear E32A.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_iter 0 EB e0 exc e32 (bv_unsigned sp + -124) (uv b (ltp_pitch_bits p) + start) _ _ (length eb) eb _ _ mc) end;
try exact (proj1 XA).
all: try (clear - Hv1 Hst2 Hst1 He0 EB1 EB2 GE E32p E32m EBm4; lia). all: try exact MUL. all: try exact WML. all: try exact (proj1 XA). all: try eassumption. all: try (rewrite repeat_length; reflexivity). all: try (unfold apart; alia).
clear MUL WML XA. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32A1; rename L into L32a end.

zstep. zstep. sw32. zstep. if_true.
pose proof (conj E32A1 I) as XA. clear E32A1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_iter 1 EB e0 exc e32 (bv_unsigned sp + -124) (uv b (ltp_pitch_bits p) + start) _ _ (length eb) eb _ _ mc) end;
try exact (proj1 XA).
all: try (clear - Hv1 Hst2 Hst1 He0 EB1 EB2 GE E32p E32m EBm4 L32a; lia). all: try exact MUL. all: try exact WML. all: try exact (proj1 XA). all: try eassumption. all: try (unfold apart; alia).
clear MUL WML L32a XA. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32A1; rename L into L32a end.

zstep. zstep. sw32. zstep. if_true.
pose proof (conj E32A1 I) as XA. clear E32A1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_iter 2 EB e0 exc e32 (bv_unsigned sp + -124) (uv b (ltp_pitch_bits p) + start) _ _ (length eb) eb _ _ mc) end;
try exact (proj1 XA).
all: try (clear - Hv1 Hst2 Hst1 He0 EB1 EB2 GE E32p E32m EBm4 L32a; lia). all: try exact MUL. all: try exact WML. all: try exact (proj1 XA). all: try eassumption. all: try (unfold apart; alia).
clear MUL WML L32a XA. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32A1; rename L into L32a end.
zstep. zstep. sw32. zstep. if_false.

destruct HIDE3 as [PVC PGC]. destruct HIDE4 as [FR1 FR3].
thaw_rw PVC MU3 WM3. thaw_rw PGC MU3 WM3. thaw_rw FR1 MU4 WM4. thaw_rw FR3 MU4 WM4. clear MU3 WM3 MU4 WM4.
pose proof (f32_of_u32arr rsegs _ _ _ GA) as FRG. rewrite f32_cons, f32_cons, f32_cons, f32_nil in FRG.
pose proof (rw_cells_join rsegs _ _ _ _ FR1 ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -128 + Z.of_nat 4) with (bv_unsigned sp + -124) by lia; exact FRG)) as FR12.
pose proof (rw_cells_join rsegs _ _ _ _ FR12 ltac:(cbn [cells_size csize Nat.add length app]; replace (bv_unsigned sp + -128 + Z.of_nat 16) with (bv_unsigned sp + -112) by lia; exact FR3)) as FR.
clear FR1 FRG FR12 FR3 GA. cbn [app] in FR.
do 15 zstep.
release_frame FR STK (bv_unsigned sp).
zstep.

destruct HIDE2 as [OBJ2 DAT2]. thaw_rw OBJ2 MU2 WM2. thaw_u8 DAT2 MU2 WM2. clear MU2 WM2.

apply evt_done. unfold ltp_unquant_post. cbn [ltp_pitch ltp_bits ltp3_pitch ltp3_bits].
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _. eexists _, _, [_; _; _].
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|]. split; [exact STK|].
split; [apply f32_of_u32arr; exact EBA|]. split; [reflexivity|].
split; [apply f32_of_u32arr; exact E32A1|]. split; [exact L32a|].
split; [exact PVC|].
split; [rewrite f32_cons, f32_cons, f32_cons, f32_nil; exact PGC|]. split; [reflexivity|].
split; [| exact OK2].
split; [exists rj2; split; [exact Lrj2| unfold bits_cells; exact OBJ2]| split; [exists bs2; split; [exact DAT2| exact Hbs2]| exact SIDE2]].
Qed.
End F.
