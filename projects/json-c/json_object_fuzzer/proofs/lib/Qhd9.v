(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx Q7wb Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX QwyL QhHa QN1y Q48O QGmo QTS6 QvBB QnkH Qi8L QmBS QKwd Qlfl QjhR QCqH QTp6 QHB6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX.Mq0 QwyL QhHa QN1y Q48O QGmo QTS6 QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0 QnkH.Mq0 Qi8L.Mq0 QjhR.Mq0.
Import QCqH.
Import QTp6.
Import QHB6.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A69C := (@QHB6.Mq0.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A62C := (@QHB6.Mq0.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq0.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq0.finv, QHB6.Mq0.Wfs, QHB6.Mq0.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq0.framL, RERRNO; split; hyp.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq0.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

Hypothesis HS_A69C : S_A69C.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A69C"] Lemma L_A62C : S_A62C.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (2 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 2) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 2) 2047) in *.
assert (Ek : kk = ((a + 2) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 1 <= 2052)%Z -> (3 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 3 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 XA) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7578) fct None m' (seg_rom rsegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read rsegs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A69C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. replace (2 + a)%Z with (a + 2)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 2 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 2 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 3) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 3) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear -Raw Ekz Ra Ez; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G648 _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | lia | | exact HL].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0 Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
* unfold inring. clear -Ra Rz Ez Hrs0 Rk K1. Z.div_mod_to_equations. lia.
* clear -Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
fix_idx.
pose proof (u32arr_store_ok rsegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 11%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write rsegs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
assert (XR' : xrel (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (zone h w a (z + 1))).
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr.
destruct (Z.eq_dec i0 z) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow a z i0 ltac:(lia) ltac:(lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a z i0); lia. }
assert (X31' : X31 (zupd x z 0)).
{ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
eapply (G648 _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | hlia Rz4 | | exact HL].
* apply (proj2 (inring_grow a z kk ltac:(lia) ltac:(lia))). right. rewrite Ek, Zminus_mod_idemp_l, Hrs0. f_equal. lia.
* replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)), Hrs0, Z.mod_small by lia. lia.
Qed.

End Floatscan.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX.Mq0 QwyL QhHa QN1y Q48O QGmo QTS6 QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0 QnkH.Mq0 Qi8L.Mq0 QjhR.Mq0.
Import QCqH.
Import QTp6.
Import QHB6.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation dfinvG_dfinv := (@QHB6.Mq0.dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_C38 := (@QHB6.Mq0.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@QHB6.Mq0.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@QHB6.Mq0.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SDn := (@QHB6.Mq0.SDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@QHB6.Mq0.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq0.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq0.finv, QHB6.Mq0.Wfs, QHB6.Mq0.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq0.framL, RERRNO; split; hyp.
Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq0.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

Hypothesis HS_E : S_E.
Hypothesis HS_C2C : S_C2C.
Hypothesis HS_C38 : S_C38.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac mk_facts := unfold digI, dig_facts; splits; try assumption; try lia.
#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. exact (proj1 (sh_getc_stdio f)). Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof.
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma b2z_land1 : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
Proof. clear. destruct b; reflexivity. Qed.
#[using="Type"] Lemma Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z.
Proof. clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; lia. Qed.

#[using="Type"] Lemma sh_getc_rpos : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E"] Lemma L_LATCH : forall n, SDn n ->
forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z -> c <> (-1)%Z ->
xrel ws x (digz k j) -> X31 x -> (0 <= j <= 8)%Z -> (0 <= k)%Z -> (9 * k + j <= dc)%Z -> (0 <= dc <= sh_rpos f)%Z ->
(0 <= lnz <= dc)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z -> (j <> 0%Z -> znth x k < 10 ^ j)%Z -> (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) ->
(- 2^31 <= lrp < 2^31)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (k <= 2045)%Z -> (k = 2045%Z -> j = 0%Z) ->
df_dig_loop n (mkDL (snd (sh_getc f)) (fst (sh_getc f)) j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6b20) fct None m (seg_rom rsegs)).
Proof.
intros n IH. intros until s'. intros DI RJ Hk FOK FRM' Hsg Hst Hc0 Hcn1 XR X31H Rj Rk Hkj9 Rdc Rlnz Hlnz Hxk Hkj Rlrp Rg Rgr Rk45 Hkj45 HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear -RJ Hc0. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | exact (proj2 (proj2 (NS0 eq_refl)) Hc0)]. }
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (sh_getc_rpos f Hbuf) as [Rrp1 Rrp2].

assert (NEXT : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
(evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 (if (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z then 0xd6a9c else 0xd69e4)) fct None m2 (seg_rom rsegs)))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2.
destruct (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z eqn:Hcond.
- eapply (IH m2); try eassumption; try lia. mk_facts.
- destruct n as [|n']; [discriminate HL|]. rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
injection HL as <-.
stmt HS_E. eapply NX with (gotdig := gotdig) (gotrad := gotrad); try eassumption; try lia.
all: try (rewrite <- dfinvG_dfinv in DI2; exact DI2). all: try (intros _; reflexivity). all: mk_facts. }

assert (N68 : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
fst (sh_getc f) <> 46%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd6a98) fct None m2 (seg_rom rsegs))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2 Hne.
clear HL. pose proof DI2 as DI3. dest_dfinv DI3.
set (c' := fst (sh_getc f)) in *.
zs. brf K; rewrite ?land_W64 in K.
-
pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with false in NX; [exact NX|].
replace (c' =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne).
replace (isdigitc c') with false; [reflexivity|]. symmetry. apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c' ltac:(lia))) in D.
clear -K D Rc'. Z.div_mod_to_equations. lia.
- pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with true in NX; [exact NX|].
replace (isdigitc c') with true; [reflexivity|]. symmetry. apply (proj2 (isdigitc_iff c' ltac:(lia))).
clear -K Rc'. Z.div_mod_to_equations. lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
set (c' := fst (sh_getc f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (E46 : c' = 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. mk_dfinv.
+ assert (N46 : c' <> 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
eapply N68; [mk_dfinv | exact N46].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c' := znth txt (sh_rpos f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (N46 : c' <> 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
eapply N68; [| exact N46]. unfold QHB6.Mq0.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ assert (E46 : c' = 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
zs.
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. unfold QHB6.Mq0.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
Qed.

#[using="Type"] Lemma seqz_land : forall e, (-2^63 < e < 2^63)%Z -> (Z.land e 18446744073709551615 <? 1)%Z = (e =? 0)%Z.
Proof.
clear. intros e He. rewrite land_W64. destruct (Z.eqb_spec e 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec (e mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E HS_C2C HS_C38"] Lemma L_D : S_D.
Proof.
unfold QHB6.Mq0.S_D. induction n as [|n IH].
{ intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK. discriminate HL. }
pose proof (L_LATCH n IH) as LATCH.
intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DG as (XR & X31H & Rj & Rk & Hkj9 & Rdc & Hdc1 & Rlnz & Hlnz & Hxk & Hkj & Rlrp & Rg & Rgr & Rk45 & Hkj45).
destruct XR as (LW' & LX & REL).
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
assert (Rrp' : (sh_rpos f <= p)%Z).
{ destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es.
- destruct (SS0 eq_refl) as (Qa & Qb & Qc). exact Qb.
- apply (proj2 (proj2 (NS0 eq_refl))). intros E0. rewrite E0 in Hcond. cbv in Hcond. discriminate Hcond. }
rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
unfold df_dig_body in HL. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in HL.
zs. rewrite b2z_land1. zs. brf K1.
-
replace (c =? 46)%Z with false in Hcond by (symmetry; apply Z.eqb_neq; exact K1). rewrite Bool.orb_false_r in Hcond.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K1).
assert (Hd : (48 <= c <= 57)%Z) by (apply (proj1 (isdigitc_iff c ltac:(lia))); exact Hcond).
zs. zs. brs K2.
{
assert (Ek : k = 2045%Z) by lia. pose proof (Hkj45 Ek) as Ej.
replace (k <? KMAX - 3)%Z with false in HL by (symmetry; apply Z.ltb_ge; unfold KMAX; lia).
change ((KMAX - 4) * 9)%Z with 18396%Z in HL. change (KMAX - 4)%Z with 2044%Z in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
zs. brf K3.
-
replace (c =? 48)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K3). cbv beta iota in HL.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k lrp (dc + 1)%Z lnz gotdig gotrad s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
-
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K3). cbv beta iota in HL.
pose proof (X31H 2044%Z) as Rt. pose proof (REL 2044%Z ltac:(lia) ltac:(unfold digz; left; lia)) as Et.
pose proof (u32arr_read rsegs _ _ _ 2044%Z _ _ XW (nth_error_wnth ws 2044%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws 2044%Z (znth x 2044) (eq_sym Et) Rt). set (t := znth x 2044) in *. clear RD.
zs.
pose proof (Z_lor_lt_pow2' t 1 31 Rt ltac:(lia)) as Rv.
set (v := Z.lor t 1) in *.
pose proof (u32arr_store_ok rsegs _ _ _ 2044%Z _ XW ltac:(lia) eq_refl) as SOK.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in SOK by lia.
zs.
pose proof (u32arr_write rsegs _ _ _ 2044%Z (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in XW' by lia.
store_done'. rename XW' into XW.
zs. zs. lo96b LOW.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat 2044) (Z_to_bv 64 v)) sign kmin c (zupd x 2044 v) f j k lrp (dc + 1)%Z 18396%Z gotdig gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 2044) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. exact Hr. }
{ intros i0. destruct (Z.eq_dec i0 2044) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. } }
assert (Hk7 : (k <= 2044)%Z) by lia.
replace (k <? KMAX - 3)%Z with true in HL by (symmetry; apply Z.ltb_lt; unfold KMAX; lia).
rewrite (s32_id (dc + 1)) in HL by lia.

assert (G94 : forall m2 (x12' : word) lnz2, lnz2 = (if (c =? 48)%Z then lnz else (dc + 1)%Z) ->
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz2)) ev ws sign f ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 (dc + 1)) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6ac4) fct None m2 (seg_rom rsegs))).
{ intros m2 x12' lnz2 Elnz2 DI2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL.
pose proof DI2 as DI3. dest_dfinv DI3.
zs. zs. zs. fix_idx. zs. brf K4.
+
assert (Ej : j = 0%Z) by exact K4. rewrite Ej in HL |- *. unfold nz in HL. rewrite Z.eqb_refl in HL. cbn [negb] in HL.
replace (0 + 1 =? 9)%Z with false in HL by reflexivity. cbv beta iota in HL. replace (0 + 1)%Z with 1%Z in HL by reflexivity.
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 (c + -48)) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. zs. zs. change (Z.b2z (18446744073709551608 <? 1)) with 0%Z. zs. fixw3. try rewrite (Z.add_0_r k). zs. zs. zs. zs.
try rewrite !swrap32_small by lia. try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 (c + -48))) sign kmin c (zupd x k (c - 48)) f 1%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz in Hr |- *. lia. }
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
{ rewrite Elnz2. destruct (c =? 48)%Z; lia. }
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- exfalso. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). lia.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). change (10 ^ 1)%Z with 10%Z. lia. }
+
assert (Hj : j <> 0%Z) by exact K4.
unfold nz in HL. replace (j =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HL.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) ltac:(unfold digz; right; right; split; [reflexivity | exact Hj])) as Et.
specialize (Hxk Hj).
pose proof (Z.pow_le_mono_r 10 j 8 ltac:(lia) ltac:(lia)) as P10. change (10 ^ 8)%Z with 100000000%Z in P10.
pose proof (u32arr_read rsegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. zs. zs.
rewrite (u32_id (t * 10 + c - 48)) in HL by lia.
replace (t * 10 + c - 48)%Z with (c + t * 10 + -48)%Z in HL by lia.
set (v := (c + t * 10 + -48)%Z) in *.
assert (P10j : (10 ^ j * 10 = 10 ^ (j + 1))%Z) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
assert (Rv : (0 <= v < 10 ^ (j + 1))%Z) by (subst v; nia).
assert (Rv2 : (10 ^ (j + 1) <= 1000000000)%Z) by (change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia).
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XR' : forall Q : Z -> Prop, (forall i, (0 <= i < 2048)%Z -> Q i -> (i <= k)%Z) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) (zupd x k v) Q).
{ intros Q HQ. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. specialize (HQ i0 Hq Hr). destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia. }
assert (X31' : X31 (zupd x k v)).
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
assert (Hx0' : znth (zupd x k v) 0 <> 0%Z -> (1 <= lnz2)%Z).
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- apply Hlnz. intros E0. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). subst v t. rewrite Ek, E0, Ec. reflexivity.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
zs. fixw3. zs. zs.
rewrite (seqz_land (j + -8)%Z) by lia.
destruct (Z.eq_dec j 8) as [Ej8|Hj8].
*
replace (j + -8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (j + 1 =? 9)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbv beta iota in HL.
change (Z.b2z true) with 1%Z.
zs. fixw3. zs. zs. zs. zs.
rewrite (Z.land_0_l (j + 1)).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f 0%Z (k + 1)%Z lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
* replace (j + -8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (j + 1 =? 9)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HL.
change (Z.b2z false) with 0%Z.
zs. fixw3. zs. zs. zs. zs.
replace (Z.land 18446744073709551615 (j + 1)) with (j + 1)%Z by (rewrite Z.land_comm, land_W64; symmetry; apply Z.mod_small; lia).
try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f (j + 1)%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). exact (proj2 Rv). } }

zs. brf K3.
+ eapply (G94 m _ lnz); [rewrite K3, Z.eqb_refl; reflexivity | exact DI0].
+ zs. lo96b LOW.
eapply (G94 _ _ (dc + 1)%Z); [replace (c =? 48)%Z with false by (symmetry; apply Z.eqb_neq; exact K3); reflexivity | mk_dfinv].
-
rewrite K1 in HL. change (46 =? 46)%Z with true in HL. unfold nz in HL. cbv beta iota in HL.
zs. brf K2.
+
replace (gotrad =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb] in HL. injection HL as <-.
pose proof FC as FC0. ufc2 FC.
zs. zs. zs.
rewrite (Eng gotdig Rg).
unfold dfK_exp in HK.
change (0 <=? 46)%Z with true in HK. replace (nz gotrad) with true in HK by (unfold nz; symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact K2).
cbn [negb Z.lor Pos.lor Z.eqb Pos.eqb andb] in HK. rewrite Bool.andb_false_r in HK. cbv beta iota in HK.
assert (DF : dig_facts ws x j k dc lnz) by (unfold dig_facts; splits; try assumption; try lia; exact (conj LW' (conj LX REL))).
destruct (sh_shlim_neg f) eqn:SN; unfold M64.
* rewrite (rf_unget_nop f SN) in HK.
zs. (brf K3; [ exfalso; lia | ]). zs.
stmt HS_C38. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
* zs. (brf K3; [ | exfalso; lia ]).
stmt HS_C2C. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
+
replace (gotrad =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K2). cbn [negb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
zs. zs. zs.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k dc dc lnz gotdig 1%Z s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
Qed.

End Floatscan.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX.Mq0 QwyL QhHa QN1y Q48O QGmo QTS6 QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0 QnkH.Mq0 Qi8L.Mq0 QjhR.Mq0.
Import QCqH.
Import QTp6.
Import QHB6.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_NK := (@QHB6.Mq0.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq0.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq0.finv, QHB6.Mq0.Wfs, QHB6.Mq0.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq0.framL, RERRNO; split; hyp.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq0.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

#[using="pre Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_NK : S_NK.
Proof.
unfold QHB6.Mq0.S_NK.
induction fi as [|fi IH]; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Hkz Nkz Rc Hsh Rrp Rw RB Re2 HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_dnk_loop_step in HL. cbn [dk_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; flia). cbn [negb] in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
assert (Kin : inring a z k) by (unfold inring; assert ((k - a) mod 2048 <> (z - a) mod 2048)%Z; [intros E; apply Nkz; apply (mod_eq_idx a z k); flia | flia]).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read rsegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *.
zs. rewrite srlw_small by flia.
pose proof (shr_half t sh ltac:(flia) ltac:(flia)) as Rts.
zs. fixw2. fixw.
set (v := (Z.shiftr t sh + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (subst v; flia).
zs. zs. showall.
pose proof (lor_lxor_nonneg k a v ltac:(flia) ltac:(flia) ltac:(flia)) as Rlor.
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 v) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
set (x' := zupd x k v) in *.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (zone h w a z)).
{ split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros i0 Hq Hr. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia | exact Hr]. }
assert (X31' : X31 x').
{ intros i0. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
set (tmp := Z.land t (Z.shiftl 1 sh - 1)) in *.
assert (Rtmp : (0 <= tmp <= 2^sh - 1)%Z) by (subst tmp; rewrite Z.shiftl_1_l; apply land_mask_range; destruct Hsh as [-> | ->]; cbn; flia).
pose proof (dn_carry_bound sh tmp Hsh Rtmp) as Rc'.
assert (Rtmp2 : (0 <= tmp < 512)%Z) by (destruct Hsh as [-> | ->]; cbn in Rtmp; flia).
assert (Ebody : df_dnk_body z sh (mkDK k carry a i rp x) =
mkDK (Z.land (k + 1) MASK) (Z.shiftr 1000000000 sh * tmp)
(if (k =? a) && (v =? 0) then Z.land (a + 1) MASK else a)%Z
(if (k =? a) && (v =? 0) then i - 1 else i)%Z
(if (k =? a) && (v =? 0) then rp - 9 else rp)%Z x').
{ unfold df_dnk_body. cbn [dk_k dk_x dk_carry dk_a dk_i dk_rp]. fold t. fold tmp.
replace (u32 (Z.shiftr t sh + carry)) with v by (subst v; unfold u32; symmetry; apply Z.mod_small; flia). fold x'.
replace (znth x' k) with v by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity).
replace (u32 (Z.shiftr 1000000000 sh * tmp)) with (Z.shiftr 1000000000 sh * tmp)%Z by (unfold u32; symmetry; apply Z.mod_small; flia).
destruct ((k =? a) && (v =? 0))%Z; reflexivity. }
rewrite Ebody in HL. clear Ebody. change MASK with 2047%Z in HL.
assert (Hk1 : ((k + 1 - a) mod 2048 = (k - a) mod 2048 + 1)%Z).
{ unfold inring in Kin. replace (k + 1 - a)%Z with ((k - a) + 1)%Z by flia. rewrite <- (Zplus_mod_idemp_l (k - a)). apply Z.mod_small. flia. }

assert (LATCH : forall (cnd : bool) m' (a' : Z) (x30' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign fR ->
(0 <? Z.lor (Z.lxor k a) v)%Z = cnd ->
a' = (if cnd then a else (a + 1) mod 2048)%Z ->
df_dnk_loop fi z sh (mkDK ((k + 1) mod 2048) (Z.shiftr 1000000000 sh * tmp) a' (if cnd then i else i - 1) (if cnd then rp else rp - 9) x')%Z = Some s1 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a') x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) (Z_to_bv 64 tmp) x30' (Z_to_bv 64 v))
Ft (Z_to_bv 64 0xd7360) fct None m' (seg_rom rsegs))).
{ intros cnd m' a' x30' DI2 Hcnd Ha' HL2. clear HL MI MU WM FRhi BY SSP1 SSP2 LOW ERR XW LW FC. try clear ST.
pose proof DI2 as DI2'. dest_dfinv DI2'.
assert (Ra' : (0 <= a' < 2048)%Z) by (subst a'; destruct cnd; [flia | apply Z.mod_pos_bound; flia]).

assert (Wz : forall i0, (if cnd then w else if (a =? 2047)%Z then false else w) = true -> (a' <= i0)%Z -> w = true /\ (a <= i0)%Z).
{ intros i0. rewrite Ha'. destruct cnd; [intros E L; split; [exact E | exact L] |].
destruct (Z.eqb_spec a 2047) as [Ea|Na]; [intros E; discriminate E|].
intros E L. split; [exact E|]. rewrite Z.mod_small in L by flia. clear -L. flia. }
assert (Wr : (if cnd then w else if (a =? 2047)%Z then false else w) = false -> (9 * a' + (if cnd then rp else rp - 9) <= 560)%Z).
{ rewrite Ha'. destruct cnd; [exact Rw|]. destruct (Z.eqb_spec a 2047) as [Ea|Na].
- intros _. rewrite Ea. change ((2047 + 1) mod 2048)%Z with 0%Z. clear -Rrp. flia.
- intros E. specialize (Rw E). rewrite Z.mod_small by flia. clear -Rw Na Ra. flia. }
zs. rewrite Hcnd. zs. zs. fixw2. fixw.
replace (Z_to_bv 64 (tmp * Z.shiftr 1000000000 sh)) with (Z_to_bv 64 (Z.shiftr 1000000000 sh * tmp)) by (f_equal; flia).
zs. zs. zs. rewrite land2047. zs.

rewrite rp_upd.
zs. brf K9; rewrite ?land_W64 in K9.
-
destruct fi as [|fi']; [discriminate HL2|]. rewrite df_dnk_loop_step in HL2. cbn [dk_k] in HL2. replace ((k + 1) mod 2048 =? z)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; clear -K9 Rk; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia). cbn [negb] in HL2.
injection HL2 as <-.
eapply (CONT _ _ _ _ _ _ _ _ (if cnd then w else if (a =? 2047)%Z then false else w)); [mk_dfinv | cbn [dk_x dk_a] | exact X31' | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ] | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ] | cbn; destruct cnd; flia | cbn [dk_a dk_rp]; exact Wr | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ]].
subst a'. destruct cnd; [exact XR'|].

destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear -Hr Hq Ra Rz Kin. unfold inring in Kin. Z.div_mod_to_equations. nia.
-
eapply IH with (x := x') (h := h) (w := (if cnd then w else if (a =? 2047)%Z then false else w)) (k := ((k + 1) mod 2048)%Z) (carry := (Z.shiftr 1000000000 sh * tmp)%Z) (a := a') (z := z) (sh := sh) (e2 := e2) (B := B) (s1 := s1);
[mk_dfinv | assumption | assumption | | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | | clear -K9 Rk; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia | flia | exact Hsh | destruct cnd; flia | exact Wr | flia | flia | exact HL2 | exact CONT].
+ subst a'. destruct cnd; [exact XR'|].
destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear -Hr Hq Ra Rz Kin. unfold inring in Kin. Z.div_mod_to_equations. nia.
+ subst a'. destruct cnd.
* rewrite Zminus_mod_idemp_l, Hk1. unfold inring in Kin. flia.
* rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. replace (k + 1 - (a + 1))%Z with (k - a)%Z by flia.
unfold inring in Kin. clear -Kin Ra Rz Rk K9 Hk1 Rrs Rks. Z.div_mod_to_equations. nia. }

zs. brf K2.
-
replace ((k =? a) && (v =? 0))%Z with false in HL.
2:{ symmetry. destruct (Z.eqb_spec k a); destruct (Z.eqb_spec v 0); cbn; try reflexivity. exfalso. apply K2. apply (proj2 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia))). split; assumption. }
zs.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite land2047 in HL.
eapply (LATCH true); [mk_dfinv | apply Z.ltb_lt; flia | reflexivity | exact HL].
-
destruct (proj1 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia)) ltac:(flia)) as [Eka Ev].
replace ((k =? a) && (v =? 0))%Z with true in HL by (symmetry; rewrite Eka, Ev, !Z.eqb_refl; reflexivity).
clear K2. zs. zs. zs. zs. rewrite land2047.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite !land2047 in HL. subst k.
eapply (LATCH false); [mk_dfinv | rewrite Z.lxor_nilpotent, Z.lor_0_l, Ev; reflexivity | reflexivity | exact HL].
Qed.

End Floatscan.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX.Mq0 QwyL QhHa QN1y Q48O QGmo QTS6 QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0 QnkH.Mq0 Qi8L.Mq0 QjhR.Mq0.
Import QCqH.
Import QTp6.
Import QHB6.Mq0.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation S_9EC := (@QHB6.Mq0.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq0.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@QHB6.Mq0.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@QHB6.Mq0.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_618 := (@QHB6.Mq0.S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq0.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq0.finv, QHB6.Mq0.Wfs, QHB6.Mq0.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq0.framL, RERRNO; split; hyp.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Hypothesis HS_9EC : S_9EC.
Hypothesis HS_7F4 : S_7F4.
Hypothesis HS_848 : S_848.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold QHB6.Mq0.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

Ltac call_shgetc FC0 RJ SLOW Hst :=
let STD := fresh "STD" in let EJ := fresh "EJ" in let Hn := fresh "Hn" in let Hrpe := fresh "Hrpe" in let Hc00 := fresh "Hc00" in
let STD0 := fresh "STD0" in let TXT := fresh "TXT" in let Hpre := fresh "Hpre" in
lazymatch type of RJ with RFJ _ _ _ _ _ ?kmin ?c ?f =>
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00);
assert (STD0 : sh_stdio f0 = true) by (first [rewrite <- Hst; exact STD | exact STD]); destruct (ST0 STD0) as [TXT Hpre];
call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]);
match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end;
match goal with H : ssp_cells ?m' _ |- _ => let S1 := fresh "SSP1'" in let S2 := fresh "SSP2'" in destruct H as [S1 S2]; unfold got_ssp, ssp_guard in S1, S2 end
end.

Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

#[using="Type"] Lemma RFJ_rechar : forall k c c' f, RFJ' k c f -> (-1 <= c' < 256)%Z -> (sh_stdio f = false -> sh_rpos f <= p)%Z -> RFJ' k c' f.
Proof.
clear. intros k c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hp'. unfold RFJ.
split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. intros _. exact (Hp' E).
Qed.

#[using="Hnul Hnum"] Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold fch, sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). rewrite N1. destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE]; cbn [negb fst].
+ right; right; reflexivity.
+ left. apply Hnum. lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). cbn [fst].
destruct (Z.eq_dec (sh_rpos f) p) as [E|NE]; [right; left; rewrite E; exact Hnul | left; apply Hnum; lia].
Qed.
Definition fch_ok (c : Z) : bool :=
(negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 73) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 78) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 88) &&
negb (Z.land c 18446744073709551583 =? 73) && negb (Z.land c 18446744073709551583 =? 78) && negb (Z.land c 18446744073709551583 =? 88) &&
negb (Z.lor c 32 =? 105) && negb (Z.lor c 32 =? 110) && negb (Z.lor c 32 =? 120) &&
negb (m_isspace c) && negb (c =? 32) && (5 <=? (c + -9) mod 2 ^ 64))%Z.
#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
#[using="Type"] Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
Proof.
clear. intros c N. unfold is_numch in N.
repeat (apply Bool.orb_true_iff in N; destruct N as [N|N]); try (apply Z.eqb_eq in N; lia).
apply andb_true_iff in N. destruct N as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2. lia.
Qed.
#[using="Type"] Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
Proof.
clear. intros c [N | [-> | ->]]; [| reflexivity | reflexivity].
pose proof (numch_range c N) as Rc.
pose proof (forallb_range (fun c => implb (is_numch c) (fch_ok c)) 256 ltac:(vm_compute; reflexivity) c Rc) as E.
cbv beta in E. rewrite N in E. exact E.
Qed.
#[using="Type"] Lemma fch_facts : forall c, fch c ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 73 /\ Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 78 /\
Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 88 /\
Z.land c 18446744073709551583 <> 73 /\ Z.land c 18446744073709551583 <> 78 /\ Z.land c 18446744073709551583 <> 88 /\
Z.lor c 32 <> 105 /\ Z.lor c 32 <> 110 /\ Z.lor c 32 <> 120 /\ m_isspace c = false /\ c <> 32 /\ 5 <= (c + -9) mod 2 ^ 64)%Z.
Proof.
clear. intros c H. pose proof (fch_ok_true c H) as E. unfold fch_ok in E.
repeat (apply andb_true_iff in E; destruct E as [E ?X]).
repeat match goal with H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H end.
repeat match goal with H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H end.
apply Z.leb_le in X.
repeat split; assumption.
Qed.
#[using="Type"] Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
Proof. clear. intros c [N | [-> | ->]]; [pose proof (numch_range c N); lia | lia | lia]. Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4"] Lemma L_6F8 : S_6F8.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
assert (HK' : dfK_rz fuelc 53 (-1074) sign pok 0 c f = Some (fR, yR)).
{ clear -HK Hne. destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|].
rewrite df_lz_loop_step in HK. replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbv iota in HK.
rewrite <- Efu in HK. exact HK. }
clear HK. rename HK' into HK.
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. try replace (Z_to_bv 64 (1074 + -53)) with (Z_to_bv 64 1021) by reflexivity.
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N46 : c <> 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_7F4. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E46 : c = 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK.
destruct (df_rz_loop fuelc _) as [[[[g2 l2] c3] f3]|] eqn:HRZ; [|discriminate HK]. cbv beta iota in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd691c) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 0%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4 HS_848"] Lemma L_618 : S_618.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold QHB6.Mq0.FS_tail in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt L_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_fch kmin 48 f RJ ltac:(lia)) as FCH.
replace (Z.lor (fst (sh_getc f)) 32 =? 120)%Z with false in HK
by (destruct (fch_facts _ FCH) as (_ & _ & _ & _ & _ & _ & _ & _ & L120 & _); symmetry; apply Z.eqb_neq; exact L120).
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd6778) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. zs. zs. brf K3.
* exfalso. clear -K3 FCH. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
* eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3.
* eapply JOIN. mk_winv2.
* exfalso. clear -K3 FCH. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
Qed.

End Floatscan.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x QCwx Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation dfinvG_dfinv := (@QHB6.Mq3.dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_C38 := (@QHB6.Mq3.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@QHB6.Mq3.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@QHB6.Mq3.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SDn := (@QHB6.Mq3.SDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@QHB6.Mq3.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq3.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq3.finv, QHB6.Mq3.Wfs, QHB6.Mq3.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq3.framL, RERRNO; split; hyp.
Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq3.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

Hypothesis HS_E : S_E.
Hypothesis HS_C2C : S_C2C.
Hypothesis HS_C38 : S_C38.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac mk_facts := unfold digI, dig_facts; splits; try assumption; try lia.
#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. exact (proj1 (sh_getc_stdio f)). Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof.
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma b2z_land1 : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
Proof. clear. destruct b; reflexivity. Qed.
#[using="Type"] Lemma Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z.
Proof. clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; lia. Qed.

#[using="Type"] Lemma sh_getc_rpos : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E"] Lemma L_LATCH : forall n, SDn n ->
forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z -> c <> (-1)%Z ->
xrel ws x (digz k j) -> X31 x -> (0 <= j <= 8)%Z -> (0 <= k)%Z -> (9 * k + j <= dc)%Z -> (0 <= dc <= sh_rpos f)%Z ->
(0 <= lnz <= dc)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z -> (j <> 0%Z -> znth x k < 10 ^ j)%Z -> (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) ->
(- 2^31 <= lrp < 2^31)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (k <= 2045)%Z -> (k = 2045%Z -> j = 0%Z) ->
df_dig_loop n (mkDL (snd (sh_getc f)) (fst (sh_getc f)) j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd91e4) fct None m (seg_rom usegs)).
Proof.
intros n IH. intros until s'. intros DI RJ Hk FOK FRM' Hsg Hst Hc0 Hcn1 XR X31H Rj Rk Hkj9 Rdc Rlnz Hlnz Hxk Hkj Rlrp Rg Rgr Rk45 Hkj45 HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear -RJ Hc0. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | exact (proj2 (proj2 (NS0 eq_refl)) Hc0)]. }
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (sh_getc_rpos f Hbuf) as [Rrp1 Rrp2].

assert (NEXT : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
(evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 (if (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z then 0xd9160 else 0xd90a8)) fct None m2 (seg_rom usegs)))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2.
destruct (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z eqn:Hcond.
- eapply (IH m2); try eassumption; try lia. mk_facts.
- destruct n as [|n']; [discriminate HL|]. rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
injection HL as <-.
stmt HS_E. eapply NX with (gotdig := gotdig) (gotrad := gotrad); try eassumption; try lia.
all: try (rewrite <- dfinvG_dfinv in DI2; exact DI2). all: try (intros _; reflexivity). all: mk_facts. }

assert (N68 : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
fst (sh_getc f) <> 46%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd915c) fct None m2 (seg_rom usegs))).
{ intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2 Hne.
clear HL. pose proof DI2 as DI3. dest_dfinv DI3.
set (c' := fst (sh_getc f)) in *.
zs. brf K; rewrite ?land_W64 in K.
-
pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with false in NX; [exact NX|].
replace (c' =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne).
replace (isdigitc c') with false; [reflexivity|]. symmetry. apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c' ltac:(lia))) in D.
clear -K D Rc'. Z.div_mod_to_equations. lia.
- pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
replace (isdigitc c' || (c' =? 46))%Z with true in NX; [exact NX|].
replace (isdigitc c') with true; [reflexivity|]. symmetry. apply (proj2 (isdigitc_iff c' ltac:(lia))).
clear -K Rc'. Z.div_mod_to_equations. lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
set (c' := fst (sh_getc f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (E46 : c' = 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. mk_dfinv.
+ assert (N46 : c' <> 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
eapply N68; [mk_dfinv | exact N46].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Qy5Y.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c' := znth txt (sh_rpos f)) in *.
zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (N46 : c' <> 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
eapply N68; [| exact N46]. unfold QHB6.Mq3.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
+ assert (E46 : c' = 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
zs.
pose proof NEXT as NX.
replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
eapply NX. unfold QHB6.Mq3.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
Qed.

#[using="Type"] Lemma seqz_land : forall e, (-2^63 < e < 2^63)%Z -> (Z.land e 18446744073709551615 <? 1)%Z = (e =? 0)%Z.
Proof.
clear. intros e He. rewrite land_W64. destruct (Z.eqb_spec e 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec (e mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_E HS_C2C HS_C38"] Lemma L_D : S_D.
Proof.
unfold QHB6.Mq3.S_D. induction n as [|n IH].
{ intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK. discriminate HL. }
pose proof (L_LATCH n IH) as LATCH.
intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DG as (XR & X31H & Rj & Rk & Hkj9 & Rdc & Hdc1 & Rlnz & Hlnz & Hxk & Hkj & Rlrp & Rg & Rgr & Rk45 & Hkj45).
destruct XR as (LW' & LX & REL).
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
assert (Rrp' : (sh_rpos f <= p)%Z).
{ destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es.
- destruct (SS0 eq_refl) as (Qa & Qb & Qc). exact Qb.
- apply (proj2 (proj2 (NS0 eq_refl))). intros E0. rewrite E0 in Hcond. cbv in Hcond. discriminate Hcond. }
rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
unfold df_dig_body in HL. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in HL.
zs. rewrite b2z_land1. zs. brf K1.
-
replace (c =? 46)%Z with false in Hcond by (symmetry; apply Z.eqb_neq; exact K1). rewrite Bool.orb_false_r in Hcond.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K1).
assert (Hd : (48 <= c <= 57)%Z) by (apply (proj1 (isdigitc_iff c ltac:(lia))); exact Hcond).
zs. zs. brs K2.
{
assert (Ek : k = 2045%Z) by lia. pose proof (Hkj45 Ek) as Ej.
replace (k <? KMAX - 3)%Z with false in HL by (symmetry; apply Z.ltb_ge; unfold KMAX; lia).
change ((KMAX - 4) * 9)%Z with 18396%Z in HL. change (KMAX - 4)%Z with 2044%Z in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
zs. brf K3.
-
replace (c =? 48)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K3). cbv beta iota in HL.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k lrp (dc + 1)%Z lnz gotdig gotrad s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
-
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K3). cbv beta iota in HL.
pose proof (X31H 2044%Z) as Rt. pose proof (REL 2044%Z ltac:(lia) ltac:(unfold digz; left; lia)) as Et.
pose proof (u32arr_read usegs _ _ _ 2044%Z _ _ XW (nth_error_wnth ws 2044%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws 2044%Z (znth x 2044) (eq_sym Et) Rt). set (t := znth x 2044) in *. clear RD.
zs.
pose proof (Z_lor_lt_pow2' t 1 31 Rt ltac:(lia)) as Rv.
set (v := Z.lor t 1) in *.
pose proof (u32arr_store_ok usegs _ _ _ 2044%Z _ XW ltac:(lia) eq_refl) as SOK.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in SOK by lia.
zs.
pose proof (u32arr_write usegs _ _ _ 2044%Z (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW.
replace (XA + 4 * 2044)%Z with (q + -136)%Z in XW' by lia.
store_done'. rename XW' into XW.
zs. zs. lo96b LOW.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat 2044) (Z_to_bv 64 v)) sign kmin c (zupd x 2044 v) f j k lrp (dc + 1)%Z 18396%Z gotdig gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 2044) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. exact Hr. }
{ intros i0. destruct (Z.eq_dec i0 2044) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. } }
assert (Hk7 : (k <= 2044)%Z) by lia.
replace (k <? KMAX - 3)%Z with true in HL by (symmetry; apply Z.ltb_lt; unfold KMAX; lia).
rewrite (s32_id (dc + 1)) in HL by lia.

assert (G94 : forall m2 (x12' : word) lnz2, lnz2 = (if (c =? 48)%Z then lnz else (dc + 1)%Z) ->
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz2)) ev ws sign f ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 (dc + 1)) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9188) fct None m2 (seg_rom usegs))).
{ intros m2 x12' lnz2 Elnz2 DI2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL.
pose proof DI2 as DI3. dest_dfinv DI3.
zs. zs. zs. fix_idx. zs. brf K4.
+
assert (Ej : j = 0%Z) by exact K4. rewrite Ej in HL |- *. unfold nz in HL. rewrite Z.eqb_refl in HL. cbn [negb] in HL.
replace (0 + 1 =? 9)%Z with false in HL by reflexivity. cbv beta iota in HL. replace (0 + 1)%Z with 1%Z in HL by reflexivity.
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 (c + -48)) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. zs. zs. change (Z.b2z (18446744073709551608 <? 1)) with 0%Z. zs. fixw3. try rewrite (Z.add_0_r k). zs. zs. zs. zs.
try rewrite !swrap32_small by lia. try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 (c + -48))) sign kmin c (zupd x k (c - 48)) f 1%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz in Hr |- *. lia. }
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
{ rewrite Elnz2. destruct (c =? 48)%Z; lia. }
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- exfalso. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). lia.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). change (10 ^ 1)%Z with 10%Z. lia. }
+
assert (Hj : j <> 0%Z) by exact K4.
unfold nz in HL. replace (j =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HL.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) ltac:(unfold digz; right; right; split; [reflexivity | exact Hj])) as Et.
specialize (Hxk Hj).
pose proof (Z.pow_le_mono_r 10 j 8 ltac:(lia) ltac:(lia)) as P10. change (10 ^ 8)%Z with 100000000%Z in P10.
pose proof (u32arr_read usegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. zs. zs.
rewrite (u32_id (t * 10 + c - 48)) in HL by lia.
replace (t * 10 + c - 48)%Z with (c + t * 10 + -48)%Z in HL by lia.
set (v := (c + t * 10 + -48)%Z) in *.
assert (P10j : (10 ^ j * 10 = 10 ^ (j + 1))%Z) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
assert (Rv : (0 <= v < 10 ^ (j + 1))%Z) by (subst v; nia).
assert (Rv2 : (10 ^ (j + 1) <= 1000000000)%Z) by (change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia).
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XR' : forall Q : Z -> Prop, (forall i, (0 <= i < 2048)%Z -> Q i -> (i <= k)%Z) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) (zupd x k v) Q).
{ intros Q HQ. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hq Hr. specialize (HQ i0 Hq Hr). destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia. }
assert (X31' : X31 (zupd x k v)).
{ intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
assert (Hx0' : znth (zupd x k v) 0 <> 0%Z -> (1 <= lnz2)%Z).
{ intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
destruct (Z.eq_dec k 0) as [Ek|Hk0].
- apply Hlnz. intros E0. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). subst v t. rewrite Ek, E0, Ec. reflexivity.
- rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
zs. fixw3. zs. zs.
rewrite (seqz_land (j + -8)%Z) by lia.
destruct (Z.eq_dec j 8) as [Ej8|Hj8].
*
replace (j + -8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (j + 1 =? 9)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbv beta iota in HL.
change (Z.b2z true) with 1%Z.
zs. fixw3. zs. zs. zs. zs.
rewrite (Z.land_0_l (j + 1)).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f 0%Z (k + 1)%Z lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
* replace (j + -8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
replace (j + 1 =? 9)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HL.
change (Z.b2z false) with 0%Z.
zs. fixw3. zs. zs. zs. zs.
replace (Z.land 18446744073709551615 (j + 1)) with (j + 1)%Z by (rewrite Z.land_comm, land_W64; symmetry; apply Z.mod_small; lia).
try rewrite (Z.add_0_r k).
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f (j + 1)%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
all: try assumption; try lia.
{ mk_dfinv. }
{ apply XR'. unfold digz. intros; lia. }
{ rewrite Elnz2; destruct (c =? 48)%Z; lia. }
{ intros _. rewrite znth_zupd_eq by (unfold zlength; lia). exact (proj2 Rv). } }

zs. brf K3.
+ eapply (G94 m _ lnz); [rewrite K3, Z.eqb_refl; reflexivity | exact DI0].
+ zs. lo96b LOW.
eapply (G94 _ _ (dc + 1)%Z); [replace (c =? 48)%Z with false by (symmetry; apply Z.eqb_neq; exact K3); reflexivity | mk_dfinv].
-
rewrite K1 in HL. change (46 =? 46)%Z with true in HL. unfold nz in HL. cbv beta iota in HL.
zs. brf K2.
+
replace (gotrad =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb] in HL. injection HL as <-.
pose proof FC as FC0. ufc2 FC.
zs. zs. zs.
rewrite (Eng gotdig Rg).
unfold dfK_exp in HK.
change (0 <=? 46)%Z with true in HK. replace (nz gotrad) with true in HK by (unfold nz; symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact K2).
cbn [negb Z.lor Pos.lor Z.eqb Pos.eqb andb] in HK. rewrite Bool.andb_false_r in HK. cbv beta iota in HK.
assert (DF : dig_facts ws x j k dc lnz) by (unfold dig_facts; splits; try assumption; try lia; exact (conj LW' (conj LX REL))).
destruct (sh_shlim_neg f) eqn:SN; unfold M64.
* rewrite (rf_unget_nop f SN) in HK.
zs. (brf K3; [ exfalso; lia | ]). zs.
stmt HS_C38. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
* zs. (brf K3; [ | exfalso; lia ]).
stmt HS_C2C. eapply NX with (gotdig := gotdig); try eassumption; try lia; try reflexivity.
+
replace (gotrad =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K2). cbn [negb] in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
zs. zs. zs.
eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k dc dc lnz gotdig 1%Z s').
all: try assumption; try lia.
exact (conj LW' (conj LX REL)).
Qed.

End Floatscan.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_NK := (@QHB6.Mq3.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq3.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq3.finv, QHB6.Mq3.Wfs, QHB6.Mq3.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq3.framL, RERRNO; split; hyp.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.
Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq3.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

#[using="pre Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_NK : S_NK.
Proof.
unfold QHB6.Mq3.S_NK.
induction fi as [|fi IH]; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Hkz Nkz Rc Hsh Rrp Rw RB Re2 HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_dnk_loop_step in HL. cbn [dk_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; flia). cbn [negb] in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
assert (Kin : inring a z k) by (unfold inring; assert ((k - a) mod 2048 <> (z - a) mod 2048)%Z; [intros E; apply Nkz; apply (mod_eq_idx a z k); flia | flia]).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read usegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *.
zs. rewrite srlw_small by flia.
pose proof (shr_half t sh ltac:(flia) ltac:(flia)) as Rts.
zs. fixw2. fixw.
set (v := (Z.shiftr t sh + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (subst v; flia).
zs. zs. showall.
pose proof (lor_lxor_nonneg k a v ltac:(flia) ltac:(flia) ltac:(flia)) as Rlor.
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 v) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
set (x' := zupd x k v) in *.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (zone h w a z)).
{ split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros i0 Hq Hr. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia | exact Hr]. }
assert (X31' : X31 x').
{ intros i0. subst x'. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
set (tmp := Z.land t (Z.shiftl 1 sh - 1)) in *.
assert (Rtmp : (0 <= tmp <= 2^sh - 1)%Z) by (subst tmp; rewrite Z.shiftl_1_l; apply land_mask_range; destruct Hsh as [-> | ->]; cbn; flia).
pose proof (dn_carry_bound sh tmp Hsh Rtmp) as Rc'.
assert (Rtmp2 : (0 <= tmp < 512)%Z) by (destruct Hsh as [-> | ->]; cbn in Rtmp; flia).
assert (Ebody : df_dnk_body z sh (mkDK k carry a i rp x) =
mkDK (Z.land (k + 1) MASK) (Z.shiftr 1000000000 sh * tmp)
(if (k =? a) && (v =? 0) then Z.land (a + 1) MASK else a)%Z
(if (k =? a) && (v =? 0) then i - 1 else i)%Z
(if (k =? a) && (v =? 0) then rp - 9 else rp)%Z x').
{ unfold df_dnk_body. cbn [dk_k dk_x dk_carry dk_a dk_i dk_rp]. fold t. fold tmp.
replace (u32 (Z.shiftr t sh + carry)) with v by (subst v; unfold u32; symmetry; apply Z.mod_small; flia). fold x'.
replace (znth x' k) with v by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity).
replace (u32 (Z.shiftr 1000000000 sh * tmp)) with (Z.shiftr 1000000000 sh * tmp)%Z by (unfold u32; symmetry; apply Z.mod_small; flia).
destruct ((k =? a) && (v =? 0))%Z; reflexivity. }
rewrite Ebody in HL. clear Ebody. change MASK with 2047%Z in HL.
assert (Hk1 : ((k + 1 - a) mod 2048 = (k - a) mod 2048 + 1)%Z).
{ unfold inring in Kin. replace (k + 1 - a)%Z with ((k - a) + 1)%Z by flia. rewrite <- (Zplus_mod_idemp_l (k - a)). apply Z.mod_small. flia. }

assert (LATCH : forall (cnd : bool) m' (a' : Z) (x30' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign fR ->
(0 <? Z.lor (Z.lxor k a) v)%Z = cnd ->
a' = (if cnd then a else (a + 1) mod 2048)%Z ->
df_dnk_loop fi z sh (mkDK ((k + 1) mod 2048) (Z.shiftr 1000000000 sh * tmp) a' (if cnd then i else i - 1) (if cnd then rp else rp - 9) x')%Z = Some s1 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a') x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) (Z_to_bv 64 tmp) x30' (Z_to_bv 64 v))
Ft (Z_to_bv 64 0xd9a24) fct None m' (seg_rom usegs))).
{ intros cnd m' a' x30' DI2 Hcnd Ha' HL2. clear HL MI MU WM FRhi BY SSP1 SSP2 LOW ERR XW LW FC. try clear ST.
pose proof DI2 as DI2'. dest_dfinv DI2'.
assert (Ra' : (0 <= a' < 2048)%Z) by (subst a'; destruct cnd; [flia | apply Z.mod_pos_bound; flia]).

assert (Wz : forall i0, (if cnd then w else if (a =? 2047)%Z then false else w) = true -> (a' <= i0)%Z -> w = true /\ (a <= i0)%Z).
{ intros i0. rewrite Ha'. destruct cnd; [intros E L; split; [exact E | exact L] |].
destruct (Z.eqb_spec a 2047) as [Ea|Na]; [intros E; discriminate E|].
intros E L. split; [exact E|]. rewrite Z.mod_small in L by flia. clear -L. flia. }
assert (Wr : (if cnd then w else if (a =? 2047)%Z then false else w) = false -> (9 * a' + (if cnd then rp else rp - 9) <= 560)%Z).
{ rewrite Ha'. destruct cnd; [exact Rw|]. destruct (Z.eqb_spec a 2047) as [Ea|Na].
- intros _. rewrite Ea. change ((2047 + 1) mod 2048)%Z with 0%Z. clear -Rrp. flia.
- intros E. specialize (Rw E). rewrite Z.mod_small by flia. clear -Rw Na Ra. flia. }
zs. rewrite Hcnd. zs. zs. fixw2. fixw.
replace (Z_to_bv 64 (tmp * Z.shiftr 1000000000 sh)) with (Z_to_bv 64 (Z.shiftr 1000000000 sh * tmp)) by (f_equal; flia).
zs. zs. zs. rewrite land2047. zs.

rewrite rp_upd.
zs. brf K9; rewrite ?land_W64 in K9.
-
destruct fi as [|fi']; [discriminate HL2|]. rewrite df_dnk_loop_step in HL2. cbn [dk_k] in HL2. replace ((k + 1) mod 2048 =? z)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; clear -K9 Rk; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia). cbn [negb] in HL2.
injection HL2 as <-.
eapply (CONT _ _ _ _ _ _ _ _ (if cnd then w else if (a =? 2047)%Z then false else w)); [mk_dfinv | cbn [dk_x dk_a] | exact X31' | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ] | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ] | cbn; destruct cnd; flia | cbn [dk_a dk_rp]; exact Wr | cbn; first [ clear - K9 LW Rt LTX Rrp Rk LX LW' SG3 SG1 SPT SPF SE_T Hp; flia | flia ]].
subst a'. destruct cnd; [exact XR'|].

destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear -Hr Hq Ra Rz Kin. unfold inring in Kin. Z.div_mod_to_equations. nia.
-
eapply IH with (x := x') (h := h) (w := (if cnd then w else if (a =? 2047)%Z then false else w)) (k := ((k + 1) mod 2048)%Z) (carry := (Z.shiftr 1000000000 sh * tmp)%Z) (a := a') (z := z) (sh := sh) (e2 := e2) (B := B) (s1 := s1);
[mk_dfinv | assumption | assumption | | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | | clear -K9 Rk; rewrite ?land2047 in K9; Z.div_mod_to_equations; flia | flia | exact Hsh | destruct cnd; flia | exact Wr | flia | flia | exact HL2 | exact CONT].
+ subst a'. destruct cnd; [exact XR'|].
destruct XR' as (L1 & L2 & R3). split; [exact L1|]. split; [exact L2|]. intros i0 Hq Hr. apply R3; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (Wz i0 Hw' Hai)].
unfold inring in Hr |- *. rewrite Zminus_mod_idemp_r in Hr. clear -Hr Hq Ra Rz Kin. unfold inring in Kin. Z.div_mod_to_equations. nia.
+ subst a'. destruct cnd.
* rewrite Zminus_mod_idemp_l, Hk1. unfold inring in Kin. flia.
* rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. replace (k + 1 - (a + 1))%Z with (k - a)%Z by flia.
unfold inring in Kin. clear -Kin Ra Rz Rk K9 Hk1 Rrs Rks. Z.div_mod_to_equations. nia. }

zs. brf K2.
-
replace ((k =? a) && (v =? 0))%Z with false in HL.
2:{ symmetry. destruct (Z.eqb_spec k a); destruct (Z.eqb_spec v 0); cbn; try reflexivity. exfalso. apply K2. apply (proj2 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia))). split; assumption. }
zs.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite land2047 in HL.
eapply (LATCH true); [mk_dfinv | apply Z.ltb_lt; flia | reflexivity | exact HL].
-
destruct (proj1 (lor_lxor_zero k a v ltac:(flia) ltac:(flia) ltac:(flia)) ltac:(flia)) as [Eka Ev].
replace ((k =? a) && (v =? 0))%Z with true in HL by (symmetry; rewrite Eka, Ev, !Z.eqb_refl; reflexivity).
clear K2. zs. zs. zs. zs. rewrite land2047.
replace (Z_to_bv 64 (Z.land t (Z.land (2 ^ sh - 1) 18446744073709551615))) with (Z_to_bv 64 tmp)
by (subst tmp; rewrite Z.shiftl_1_l; f_equal; f_equal; rewrite land_W64; symmetry; apply Z.mod_small; destruct Hsh as [-> | ->]; cbn; flia).
rewrite !land2047 in HL. subst k.
eapply (LATCH false); [mk_dfinv | rewrite Z.lxor_nilpotent, Z.lor_0_l, Ev; reflexivity | reflexivity | exact HL].
Qed.

End Floatscan.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation S_9EC := (@QHB6.Mq3.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq3.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@QHB6.Mq3.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@QHB6.Mq3.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_618 := (@QHB6.Mq3.S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq3.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq3.finv, QHB6.Mq3.Wfs, QHB6.Mq3.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq3.framL, RERRNO; split; hyp.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Hypothesis HS_9EC : S_9EC.
Hypothesis HS_7F4 : S_7F4.
Hypothesis HS_848 : S_848.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
Ltac mk_winv2 := norm_m1074; unfold QHB6.Mq3.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

Ltac call_shgetc FC0 RJ SLOW Hst :=
let STD := fresh "STD" in let EJ := fresh "EJ" in let Hn := fresh "Hn" in let Hrpe := fresh "Hrpe" in let Hc00 := fresh "Hc00" in
let STD0 := fresh "STD0" in let TXT := fresh "TXT" in let Hpre := fresh "Hpre" in
lazymatch type of RJ with RFJ _ _ _ _ _ ?kmin ?c ?f =>
destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00);
assert (STD0 : sh_stdio f0 = true) by (first [rewrite <- Hst; exact STD | exact STD]); destruct (ST0 STD0) as [TXT Hpre];
call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]);
match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H end;
match goal with H : ssp_cells ?m' _ |- _ => let S1 := fresh "SSP1'" in let S2 := fresh "SSP2'" in destruct H as [S1 S2]; unfold got_ssp, ssp_guard in S1, S2 end
end.

Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

#[using="Type"] Lemma RFJ_rechar : forall k c c' f, RFJ' k c f -> (-1 <= c' < 256)%Z -> (sh_stdio f = false -> sh_rpos f <= p)%Z -> RFJ' k c' f.
Proof.
clear. intros k c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hp'. unfold RFJ.
split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. intros _. exact (Hp' E).
Qed.

#[using="Hnul Hnum"] Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold fch, sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & N5). rewrite N1. destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE]; cbn [negb fst].
+ right; right; reflexivity.
+ left. apply Hnum. lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). cbn [fst].
destruct (Z.eq_dec (sh_rpos f) p) as [E|NE]; [right; left; rewrite E; exact Hnul | left; apply Hnum; lia].
Qed.
Definition fch_ok (c : Z) : bool :=
(negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 73) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 78) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 88) &&
negb (Z.land c 18446744073709551583 =? 73) && negb (Z.land c 18446744073709551583 =? 78) && negb (Z.land c 18446744073709551583 =? 88) &&
negb (Z.lor c 32 =? 105) && negb (Z.lor c 32 =? 110) && negb (Z.lor c 32 =? 120) &&
negb (m_isspace c) && negb (c =? 32) && (5 <=? (c + -9) mod 2 ^ 64))%Z.
#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
#[using="Type"] Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
Proof.
clear. intros c N. unfold is_numch in N.
repeat (apply Bool.orb_true_iff in N; destruct N as [N|N]); try (apply Z.eqb_eq in N; lia).
apply andb_true_iff in N. destruct N as [N1 N2]. apply Z.leb_le in N1. apply Z.leb_le in N2. lia.
Qed.
#[using="Type"] Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
Proof.
clear. intros c [N | [-> | ->]]; [| reflexivity | reflexivity].
pose proof (numch_range c N) as Rc.
pose proof (forallb_range (fun c => implb (is_numch c) (fch_ok c)) 256 ltac:(vm_compute; reflexivity) c Rc) as E.
cbv beta in E. rewrite N in E. exact E.
Qed.
#[using="Type"] Lemma fch_facts : forall c, fch c ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 73 /\ Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 78 /\
Z.land (Z.land c 18446744073709551615) 18446744073709551583 <> 88 /\
Z.land c 18446744073709551583 <> 73 /\ Z.land c 18446744073709551583 <> 78 /\ Z.land c 18446744073709551583 <> 88 /\
Z.lor c 32 <> 105 /\ Z.lor c 32 <> 110 /\ Z.lor c 32 <> 120 /\ m_isspace c = false /\ c <> 32 /\ 5 <= (c + -9) mod 2 ^ 64)%Z.
Proof.
clear. intros c H. pose proof (fch_ok_true c H) as E. unfold fch_ok in E.
repeat (apply andb_true_iff in E; destruct E as [E ?X]).
repeat match goal with H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H end.
repeat match goal with H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H end.
apply Z.leb_le in X.
repeat split; assumption.
Qed.
#[using="Type"] Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
Proof. clear. intros c [N | [-> | ->]]; [pose proof (numch_range c N); lia | lia | lia]. Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4"] Lemma L_6F8 : S_6F8.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
assert (HK' : dfK_rz fuelc 53 (-1074) sign pok 0 c f = Some (fR, yR)).
{ clear -HK Hne. destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|].
rewrite df_lz_loop_step in HK. replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbv iota in HK.
rewrite <- Efu in HK. exact HK. }
clear HK. rename HK' into HK.
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. try replace (Z_to_bv 64 (1074 + -53)) with (Z_to_bv 64 1021) by reflexivity.
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N46 : c <> 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_7F4. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E46 : c = 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK.
destruct (df_rz_loop fuelc _) as [[[[g2 l2] c3] f3]|] eqn:HRZ; [|discriminate HK]. cbv beta iota in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8fe0) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 0%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_7F4 HS_848"] Lemma L_618 : S_618.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold QHB6.Mq3.FS_tail in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt L_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_fch kmin 48 f RJ ltac:(lia)) as FCH.
replace (Z.lor (fst (sh_getc f)) 32 =? 120)%Z with false in HK
by (destruct (fch_facts _ FCH) as (_ & _ & _ & _ & _ & _ & _ & _ & L120 & _); symmetry; apply Z.eqb_neq; exact L120).
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8e3c) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. zs. zs. brf K3.
* exfalso. clear -K3 FCH. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
* eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3.
* eapply JOIN. mk_winv2.
* exfalso. clear -K3 FCH. destruct (fch_facts _ FCH) as (A73 & A78 & A88 & B73 & B78 & B88 & _). first [exact (A88 K3) | exact (B88 K3)].
Qed.

End Floatscan.
End Mq6.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPUx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeTw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1BE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1BE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5JI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5JI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkAv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkAv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNtS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNtS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXzy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXzy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Yb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Yb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFef.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFef. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW7x. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qra5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qra5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7ap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7ap. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuEo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvBB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvBB.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quzq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quzq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlfl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlfl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjhR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjhR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHB6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHB6.Mq3.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Local Ltac lia ::= first [ Qo9G.term_slim ltac:(zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker)
| Qo9G.term_slim ltac:(zify_prune_fast; Zify.zify; xlia zchecker)
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A69C := (@QHB6.Mq3.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A62C := (@QHB6.Mq3.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq3.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac mk_finv := unfold QHB6.Mq3.finv, QHB6.Mq3.Wfs, QHB6.Mq3.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac mk_framL := unfold QHB6.Mq3.framL, RERRNO; split; hyp.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinv := unfold QHB6.Mq3.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

Hypothesis HS_A69C : S_A69C.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A69C"] Lemma L_A62C : S_A62C.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (2 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 2) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 2) 2047) in *.
assert (Ek : kk = ((a + 2) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 1 <= 2052)%Z -> (3 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 3 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 XA) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9c3c) fct None m' (seg_rom usegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read usegs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A69C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. replace (2 + a)%Z with (a + 2)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 2 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 2 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 3) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 3) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear -Raw Ekz Ra Ez; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G648 _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | lia | | exact HL].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0 Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
* unfold inring. clear -Ra Rz Ez Hrs0 Rk K1. Z.div_mod_to_equations. lia.
* clear -Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
fix_idx.
pose proof (u32arr_store_ok usegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 11%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write usegs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
assert (XR' : xrel (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (zone h w a (z + 1))).
{ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr.
destruct (Z.eq_dec i0 z) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow a z i0 ltac:(lia) ltac:(lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a z i0); lia. }
assert (X31' : X31 (zupd x z 0)).
{ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
eapply (G648 _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | hlia Rz4 | | exact HL].
* apply (proj2 (inring_grow a z kk ltac:(lia) ltac:(lia))). right. rewrite Ek, Zminus_mod_idemp_l, Hrs0. f_equal. lia.
* replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)), Hrs0, Z.mod_small by lia. lia.
Qed.

End Floatscan.
