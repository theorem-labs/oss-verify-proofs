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
Local Notation S_F1 := (@QHB6.Mq0.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A69C := (@QHB6.Mq0.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_F1 : S_F1.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_F1"] Lemma L_A69C : S_A69C.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (3 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 3) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 3) 2047) in *.
assert (Ek : kk = ((a + 3) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL.

assert (G6BC : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (4 <= (z' - a) mod 2048)%Z ->
fin_K1 53 (-1074) sign 1024 zero0 a z' x' 4 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd75ec) fct None m' (seg_rom rsegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Hrs' HK'.
clear HL HK MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read rsegs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_F1. eapply NX; try eassumption; try lia; try mk_dfinv.
- apply (xrel_window _ _ h' w); split; [exact LW2 | split; [exact LX2 | exact REL2]].
- intros Hne. change MASK with 2047%Z in Hne |- *. destruct (inring_plus a z' 4 ltac:(lia) ltac:(lia) ltac:(lia) Hne) as [Hin' _]. exact Hin'. }
zs. replace (3 + a)%Z with (a + 3)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [as_i] in HL.
change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
destruct (inring_plus a z 3 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G6BC _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | exact Hrs' | exact HK].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 3 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
cbn [as_i] in HL. change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 4) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 4) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs. showall.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear -Raw Ekz Ra Ez; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G6BC _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | | exact HK].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0 Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
* unfold inring. clear -Ra Rz Ez Hrs0 Rk K1. Z.div_mod_to_equations. lia.
* clear -Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
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
eapply (G6BC _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | | exact HK].
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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation S_N324 := (@QHB6.Mq0.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N2D4 := (@QHB6.Mq0.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq0.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Hypothesis HS_N324 : S_N324.

#[using="HS_N324"] Lemma L_N2D4 : S_N2D4.
Proof.
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
do 20 zs.
rewrite ?land2047. fix_idx.
stmt HS_N324. eapply NX; try eassumption; try lia.
- rewrite Z.shiftl_mul_pow2 by lia. lia.
- rewrite landW_mod2048. replace (z + -1)%Z with (z - 1)%Z by lia. reflexivity.
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
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation L_RET1 := (@QHB6.Mq0.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinvG_dfinv := (@QHB6.Mq0.dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_DD0 := (@QHB6.Mq0.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@QHB6.Mq0.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@QHB6.Mq0.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_R := (@QHB6.Mq0.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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

Hypothesis HS_P : S_P.
Hypothesis HS_DD24 : S_DD24.
Hypothesis HS_DD0 : S_DD0.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_P HS_DD24 HS_DD0"] Lemma L_R : S_R.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Rdc Rlnz Hlnz Hxk Hkj Hkj45 Rrp Hw80 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_rng in HK.
change (Z.quot (- (-1074)) 2) with 537%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
change (30 <? 53)%Z with true in HK. cbn [orb] in HK.
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) ltac:(unfold digz; right; left; reflexivity)) as Et0.
pose proof (u32arr_read rsegs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. rewrite (sx32_wval ws 0%Z (znth x 0) (eq_sym Et0) Rt0). set (x0 := znth x 0) in *. clear RD0.
zs. brf K1; rewrite ?land_W64 in K1.
{
assert (E0 : x0 = 0%Z) by (clear -K1 Rt0; mlia).
rewrite E0, Z.eqb_refl in HK. some_snd HK.
assert (Rs : (-1 <= sign <= 1)%Z) by lia.
zs. zs. zs. zs. zs.
callx (eapply extenddftf2_callF; [eassumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL; try fok.
unfold D_ZERO in HK. symmetry. exact HK. }
assert (Hne0 : x0 <> 0%Z) by (clear -K1 Rt0; mlia). clear K1.
replace (x0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0).
specialize (Hlnz Hne0). specialize (Hw80 Hne0). subst w80. rewrite dfinvG_dfinv in DI0.

assert (G3C : forall (x10' : word),
((lrp =? dc) && (dc <? 10) = false)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10' x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6c6c) fct None m (seg_rom rsegs))).
{ intros x10' Hc. rewrite Hc in HK. cbv iota in HK.
zs. zs. zs. brs K5.
-
replace (537 <? lrp)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs.
try replace (Z_to_bv 64 18446744073709550316) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (18446744073709550542 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (-1074 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
zs. brs K6.
+
replace (lrp <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
stmt HS_P. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
replace (lrp <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MIN); try eassumption; try lia; try mk_dfinv. symmetry; exact HK.
-
replace (537 <? lrp)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. zs.
try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity). zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MAX); try eassumption; try lia; try mk_dfinv. symmetry; exact HK. }
zs. zs. brs K2.
{  apply G3C. replace (dc <? 10)%Z with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
zs. brf K3; rewrite ?land_W64 in K3.
{  assert (Hne : lrp <> dc) by (clear -K3 Rrp Rdc; mlia).
apply G3C. replace (lrp =? dc)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
assert (Heq : lrp = dc) by (clear -K3 Rrp Rdc; mlia). clear K3.
replace (lrp =? dc)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia).
replace (dc <? 10)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in HK. some_snd HK.

zs. zs. zs. zs. zs. zs. brf K4.
{ exfalso. clear -K4. rewrite ?land_W64 in K4.
match type of K4 with (?a = 0)%Z => idtac end.
revert K4. match goal with |- context [Z.lor 1 ?b] => destruct (Z.lor_eq_0_iff 1 b) as [F _]; intros K4; try (specialize (F K4); lia) end.
all: try (Z.div_mod_to_equations; lia). }
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs.
stmt HS_DD24. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
Qed.

End Floatscan.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
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
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis Hpok1 : pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
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

Local Notation ctx_all := (@QHB6.Mq0.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@QHB6.Mq0.Wfs q Fp).
Local Notation FokR := (@QHB6.Mq0.FokR F).
Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof.
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Definition and33_okb (c : Z) : bool :=
forallb (fun U => implb ((65 <=? U) && (U <=? 90))%Z (Bool.eqb (Z.land c 18446744073709551583 =? U) (Z.lor c 32 =? U + 32)))%Z
(map Z.of_nat (seq 0 91)).
#[using="Type"] Lemma and33_lor : forall c U, (0 <= c < 256)%Z -> (65 <= U <= 90)%Z ->
(Z.land c 18446744073709551583 = U <-> Z.lor c 32 = U + 32)%Z.
Proof.
clear. intros c U Hc HU.
pose proof (forallb_range and33_okb 256 ltac:(vm_compute; reflexivity) c Hc) as E. unfold and33_okb in E.
pose proof (forallb_range _ 91 E U ltac:(lia)) as E2. cbv beta in E2.
replace ((65 <=? U) && (U <=? 90))%Z with true in E2 by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia). cbn [implb] in E2.
apply Bool.eqb_prop in E2.
destruct (Z.eqb_spec (Z.land c 18446744073709551583) U); destruct (Z.eqb_spec (Z.lor c 32) (U + 32)); try discriminate E2; tauto.
Qed.
#[using="Type"] Lemma and33_range : forall c, (0 <= c < 256)%Z -> (0 <= Z.land c 18446744073709551583 < 256)%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => (0 <=? Z.land c 18446744073709551583) && (Z.land c 18446744073709551583 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma isspace_iff : forall c, (0 <= c < 256)%Z -> (m_isspace c = true <-> (c = 32 \/ 9 <= c <= 13))%Z.
Proof.
clear. intros c Hc. unfold m_isspace, u32.
destruct (Z.eqb_spec c 32) as [->|N]; cbn [orb]; [split; [intros _; left; reflexivity | reflexivity]|].
rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).
Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).
Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

Definition SWSn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (0 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
fs_ws_loop n f = Some (c', f') -> FS_sign' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6460) fc None m (seg_rom rsegs)).
Definition S_WS : Prop := forall n, SWSn n.

Definition S_AWS : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
(0 <= c < 256)%Z -> m_isspace c = false ->
FS_sign' c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6484) fc None m (seg_rom rsegs)).

Definition S_I1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
Z.lor c 32 = 105%Z ->
FS_infk' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd64c8) fc None m (seg_rom rsegs)).

Definition S_N1 : Prop := forall m (x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= c < 256)%Z -> Z.lor c 32 <> 105%Z ->
FS_nank' sign 0 c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6500) fc None m (seg_rom rsegs)).

Definition S_Z : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail_h' sign c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6548) fct None m (seg_rom rsegs)).

Definition S_ERR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> sh_stdio f = sh_stdio f0 ->
fR = sh_lim0 (sh_unget f) -> yR = f128_of_i32 0 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6e2c) fct None m (seg_rom rsegs)).

Definition sp_ok (v : word) (r : Z) : Prop :=
(v = Z_to_bv 64 0xffffffff7f800000 /\ r = C_INF) \/ (v = Z_to_bv 64 0xffffffffff800000 /\ r = C_NINF) \/ (v = Z_to_bv 64 0xffffffff7fc00000 /\ r = C_NAN).
Definition S_A38 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c (v : word),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
sp_ok v yR -> (forall r : bv 5, bv_unsigned r = 10%Z -> reg_get Ft r = v) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6e24) fct None m (seg_rom rsegs)).

Definition SPARn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (i i' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i <= kmin)%Z -> Fok Ft -> frm0 fct -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
(1 <= i <= sh_rpos f)%Z ->
fs_par_loop n (i, f) = Some (i', c', f') ->
(fR, yR) = (if (c' =? 41)%Z then (f', C_NAN) else (fs_unget_loop (Z.to_nat i') (sh_unget f'), C_NAN)) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6804) fct None m (seg_rom rsegs)).
Definition S_PAR : Prop := forall n, SPARn n.

Definition hinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv rsegs m /\ munch Wfs m0 m /\ wmono rsegs m0 m
/\ stk rsegs m (q - FS_DEPTH) q
/\ bytes_at rsegs m T (zbytes txt)
/\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary]
/\ rw_cells rsegs m RERRNO [C4 ev]
/\ rw_cells rsegs m Fp (rf_cells T p true f J).

Definition S_HEX : Prop := forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) Ft fct ev sign kmin c (f : shfile),
let _ := ctx_all in
hinv m ev f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> FokR Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> Z.lor c 32 = 120%Z ->
hexfloat_m fuelc f 53 (-1074) sign pok = Some (fR, yR) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 53) (Z_to_bv 64 (-1074)) (Z_to_bv 64 sign) (Z_to_bv 64 pok) a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (Z_to_bv 64 0xd7a1c) fct None m (seg_rom rsegs)).
End Floatscan.
End Mq3.

Module Mq4.

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
Local Notation S_U1A8 := (@QHB6.Mq0.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_T := (@QHB6.Mq0.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_U1A8 : S_U1A8.

#[using="Type"] Lemma lor_shl32 : forall k, (0 <= k < 2^31)%Z -> (Z.lor (Z.land (Z.shiftl k 32) 18446744073709551615) 4294967295 + 1 = (k + 1) * 4294967296)%Z.
Proof.
clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
rewrite land_W64, (Z.mod_small (k * 4294967296)) by lia.
rewrite <- Z.lxor_lor. 2:{ change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.mod_mul. reflexivity. lia. }
rewrite <- Z.add_nocarry_lxor. { lia. }
change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. apply Z.mod_mul. lia.
Qed.
#[using="Type"] Lemma tz_dec32 : forall j, Z_to_bv 64 ((j + 1) * 4294967296 + 18446744069414584320) = Z_to_bv 64 (j * 4294967296).
Proof. clear. intros j. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma df_tz_loop_step : forall n x z, df_tz_loop (S n) x z = if (znth x (z - 1) =? 0)%Z then df_tz_loop n x (z - 1) else Some z.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_al_loop_step : forall n p10 z s, df_al_loop (S n) p10 z s = if negb (al_k s =? z)%Z then df_al_loop n p10 z (df_al_body p10 s) else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
clear. intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i), (Z.mod_small v) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
assert (0 <= v / i < 2147483648)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma magic_q9 : forall rp, (-2^20 <= rp <= 2^20)%Z ->
(Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
+ Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63 = Z.quot rp 9)%Z.
Proof.
clear. intros rp Hrp.
rewrite (Z_to_bv_eqm (Z.land rp 18446744073709551615 * 954437177) (rp * 954437177)).
2:{ rewrite land_W64. apply Z.mul_mod_idemp_l. lia. }
rewrite signed_of_Z by lia. rewrite !land_W64. rewrite Z.mul_mod_idemp_l by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^33)%Z with 8589934592%Z. change (2^63)%Z with 9223372036854775808%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (intros; apply Z.rem_nonpos; lia).
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rem9_fix : forall rp, (-2^20 <= rp <= 2^20)%Z ->
bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - Z.land (Z.quot rp 9) 18446744073709551615)) 18446744073709551615
- Z.land (Z.shiftl (Z.land (Z.quot rp 9) 18446744073709551615) 3) 18446744073709551615) = Z.rem rp 9.
Proof.
clear. intros rp Hrp. rewrite !land_W64, !swrap32_eq, Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma shr63_neg : forall v, (-2^63 <= v < 0)%Z -> Z.shiftr v 63 = (-1)%Z.
Proof. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shr63_nonneg : forall v, (0 <= v < 2^63)%Z -> Z.shiftr v 63 = 0%Z.
Proof. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
#[using="Type"] Lemma shr30_4z : forall z, (0 <= z)%Z -> Z.shiftr (z * 4294967296) 30 = (4 * z)%Z.
Proof. clear. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma zext32_small : forall v, (0 <= v < 2^32)%Z -> Z.land v 4294967295 = v.
Proof. clear. intros v Hv. change 4294967295%Z with (2^32 - 1)%Z. apply land_mask_small; lia. Qed.

#[using="pre"] Lemma L_TZL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (rp kz j z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= j <= kz)%Z ->
df_tz_loop n x j = Some z ->
(forall x15', (1 <= z <= j)%Z -> znth x (z - 1) <> 0%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 (kz - z + 1)) (Z_to_bv 64 (XA + 4 * (z - 2))) (Z_to_bv 64 z) (Z_to_bv 64 18446744069414584320) x15' x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6fa4) fct None m (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 ((j + 1) * 4294967296)) (Z_to_bv 64 (kz - j)) (Z_to_bv 64 (XA + 4 * (j - 1))) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 18446744069414584320) x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6f8c) fct None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; intros until z; intros DI XR X31H Rkz Hx0 Rj HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_tz_loop_step in HL.
assert (Kin : inring 0 kz (j - 1)) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H (j - 1)%Z) as Rt. pose proof (REL (j - 1)%Z ltac:(lia) Kin) as Et.
pose proof (u32arr_read rsegs _ _ _ (j - 1)%Z _ _ XW (nth_error_wnth ws (j - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws (j - 1)%Z (znth x (j - 1)) (eq_sym Et) Rt). set (t := znth x (j - 1)) in *. clear RD.
zs. zs. rewrite tz_dec32. zs. replace (j + 1 + -1)%Z with j by lia. zs. replace (XA + 4 * (j - 1) + -4)%Z with (XA + 4 * (j - 1 - 1))%Z by lia.
zs. brf K1.
-
replace (t =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
assert (Hj1 : j <> 1%Z) by (intros E; apply Hx0; subst t; rewrite E in K1; exact K1).
replace (kz - j + 1)%Z with (kz - (j - 1))%Z by lia. replace (j * 4294967296)%Z with ((j - 1 + 1) * 4294967296)%Z by (f_equal; lia).
replace (Z_to_bv 64 j) with (Z_to_bv 64 (j - 1 + 1)) by (f_equal; lia).
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz (j - 1)%Z z);
[exact DI | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HL | ].
intros x15' Rz Hnz. eapply CONT; [lia | exact Hnz].
- replace (t =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). injection HL as <-.
replace (j - 1 - 1)%Z with (j - 2)%Z by lia.
eapply CONT; [lia | subst t; exact K1].
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 HS_U1A8"] Lemma L_UPI : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp a z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 z) -> X31 x -> (0 <= a < z)%Z -> (1 <= z <= 2047)%Z -> (-2^16 <= rp <= 2^16 /\ 9 * a + rp <= 560)%Z ->
dfK_up 53 (-1074) sign fR rp a z 0 x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd70b0) fct None m (seg_rom rsegs)).
Proof.
intros until z. intros DI RJ Hk FOK FRM' Hsg XR X31H Ra Rz Rrp HK.
unfold dfK_up in HK. destruct (df_up_loop FUEL_SCALE _) as [[rp' a' z' e2' x']|] eqn:HL; [|discriminate HK].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
stmt HS_U1A8. eapply (NX 2000%nat) with (h := false) (w := false) (x := x) (s' := mkUS rp' a' z' e2' x');
[exact DI | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | lia | | exact X31H | lia | intros _; lia | intros _; lia | lia | lia | cbn; lia | unfold FUEL_SCALE in HL; exact HL | ].
- eapply xrel_iff; [| exact XR]. intros i Hi [Hr | [[Hr _] | [Hr _]]]; [| discriminate Hr | discriminate Hr]. unfold inring in Hr |- *. clear -Hr Hi Ra Rz. Z.div_mod_to_equations. nia.
- unfold up_K, fin_K0. cbn [us_rp us_a us_z us_e2 us_x]. unfold dfK_dn in HK.
destruct (df_dn_loop FUEL_SCALE _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate HK]. cbn [ds_a ds_z ds_x ds_e2].
cbv beta zeta in HK. change (- (-1074) - 53 + 3)%Z with 1024%Z in HK. fold zero0 in HK.
destruct (df_final _ _ _ _ _ _ _ _ _ _) as [y|]; [|discriminate HK]. injection HK as <-. reflexivity.
Qed.

#[using="pre T1 SPF SPF2 SPT SG1"] Lemma L_ALK : forall (n : nat) m (x1 x6 x7 x8 x9 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (k carry a rp z p10 j10 rpm9 kz rp0 : Z) (s1 : st_al),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (inring 0 z) -> X31 x ->
(1 <= z <= 2046)%Z -> (0 <= k < z)%Z -> (0 <= a <= k)%Z -> (a = k -> carry <> 0%Z \/ (k = 0%Z /\ znth x 0 <> 0%Z)) ->
(0 <= carry < 2^30)%Z -> (0 <= j10 <= 7)%Z -> p10 = znth p10s j10 -> (rp = rp0 - 9 * a)%Z -> (-2^15 <= rp0 <= 2^15)%Z ->
(1 <= rpm9 <= 8)%Z -> (1 <= kz <= 2046)%Z ->
df_al_loop n p10 z (mkAL k a rp carry x) = Some s1 ->
(forall m' ws' (x6' x7' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (al_x s1) (inring 0 z) -> X31 (al_x s1) -> al_k s1 = z ->
(0 <= al_a s1 <= z)%Z -> (al_a s1 = z -> al_carry s1 <> 0%Z) -> (0 <= al_carry s1 < 2^30)%Z -> (al_rp s1 = rp0 - 9 * al_a s1)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * z)) x6' x7' x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) (Z_to_bv 64 (al_carry s1)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (al_a s1)) x20 x21 x22 (Z_to_bv 64 (al_rp s1)) (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 0xd707c) fct None m' (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 carry) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7054) fct None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; intros until s1; intros DI FOK FRM' XR X31H Rz Rk Ra Hak Rc Rj Hp10 Rrp Rrp0 Rrpm9 Rkz HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in HL.
unfold df_al_body in HL. cbn [al_k al_x al_a al_rp al_carry] in HL.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10]. rewrite <- Hp10 in Rp10, Dp10.
assert (Kin : inring 0 z k) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) Kin) as Et.
pose proof (u32arr_read rsegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. rewrite divuw_small by lia.
pose proof (Z.mod_pos_bound t p10 ltac:(lia)) as Rtm.
assert (Rtq : (0 <= t / p10 < 214748365)%Z) by (clear -Rt Rp10; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | nia]]).
zs. fixw3. fixw.
set (v := (t / p10 + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (clear -Rtq Rc; subst v; lia).
zs. zs.
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (Rc' : (0 <= t mod p10 * (1000000000 / p10) < 1000000000)%Z).
{ clear -Rtm Rp10 Dp10. set (u := (t mod p10)%Z) in *. set (w := (1000000000 / p10)%Z) in *. clearbody u w. nia. }
set (carry' := (t mod p10 * (1000000000 / p10))%Z) in *.
rewrite (u32_id v) in HL by (clear -Rv; lia). rewrite (Z.mul_comm (1000000000 / p10) (t mod p10)) in HL. fold carry' in HL. rewrite (u32_id carry') in HL by (clear -Rc'; lia).
set (x' := zupd x k v) in *.
assert (Exk : znth x' k = v) by (clear -LX Rk Rz; subst x'; rewrite znth_zupd_eq by (unfold zlength; lia); reflexivity). rewrite Exk in HL.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (inring 0 z)).
{ clear -LW' LX REL Rk Rz Rv. split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros q0 Hq Hr. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia | exact Hr]. }
assert (X31' : X31 x').
{ clear -X31H LX Rk Rz Rv. intros q0. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); exact Rv | rewrite znth_zupd_neq by lia; apply X31H]. }
pose proof (lor_lxor_nonneg k a v ltac:(lia) ltac:(lia) ltac:(lia)) as Rw.

assert (G0FC : forall (cb : bool),
cb = (0 <? Z.lor (Z.lxor k a) v)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 t) (Z_to_bv 64 (t / p10)) x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (if cb then a else a + 1)%Z) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 (Z_to_bv 64 v) x29 x30 x31)
Ft (Z_to_bv 64 0xd702c) fct None m1 (seg_rom rsegs))).
{ intros cb Hcb.
assert (Ecb : cb = negb ((k =? a) && (v =? 0))%Z).
{ rewrite Hcb. clear -Rw Rk Ra Rv. destruct ((k =? a) && (v =? 0))%Z eqn:Eb; cbn [negb].
- apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
apply Z.ltb_ge. rewrite (proj2 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia)) (conj E1 E2)). lia.
- apply Z.ltb_lt. assert (Hne : Z.lor (Z.lxor k a) v <> 0%Z); [|lia].
intros E0. apply (proj1 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia))) in E0. destruct E0 as [E1 E2].
apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.eqb_neq in Eb; lia. }
zs. zs. rewrite <- Hcb. zs. zs. fixw3. fixw. replace (t - t / p10 * p10)%Z with (t mod p10)%Z by (rewrite Zmod_eq_full by lia; lia).
zs. zs. try rewrite (land_W64_small (t mod p10)) by (clear -Rtm; lia). try rewrite (swrap32_small (t mod p10 * (1000000000 / p10))) by (clear -Rc'; lia). fold carry'.
zs. zs. rewrite rp_upd. zs. replace (XA + 4 * k + 4)%Z with (XA + 4 * (k + 1))%Z by lia.
set (a2 := (if cb then a else a + 1)%Z) in *. set (rp2 := (if cb then rp else rp - 9)%Z) in *.
assert (Ea2 : (if (k =? a) && (v =? 0) then (Z.land (a + 1) MASK, rp - 9) else (a, rp))%Z = (a2, rp2)).
{ subst a2 rp2. rewrite Ecb. destruct ((k =? a) && (v =? 0))%Z; cbn [negb]; [|reflexivity]. change MASK with 2047%Z. rewrite land2047, Z.mod_small by lia. reflexivity. }
rewrite Ea2 in HL. clear Ea2.
assert (Ra2 : (0 <= a2 <= k + 1)%Z) by (subst a2; destruct cb; lia).
assert (Hak2 : (a2 = k + 1 -> carry' <> 0)%Z).
{ subst a2. rewrite Ecb. destruct (Z.eqb_spec k a) as [Eka|Hka]; destruct (Z.eqb_spec v 0) as [Ev|Hv]; cbn [andb negb]; try lia.
intros _. destruct (Hak (eq_sym Eka)) as [Hc | [Hk0 Hx0]]; [exfalso; subst v; lia|].
assert (Ht0 : t <> 0%Z) by (subst t; rewrite Hk0; exact Hx0).
assert (Htp : (t < p10)%Z). { subst v. assert (t / p10 = 0)%Z by lia. destruct (Z.lt_ge_cases t p10); [assumption|]. exfalso. assert (1 <= t / p10)%Z by (apply Z.div_le_lower_bound; lia). lia. }
subst carry'. rewrite Z.mod_small by lia. assert (10 <= 1000000000 / p10)%Z by (apply Z.div_le_lower_bound; lia). nia. }
assert (Rrp2 : (rp2 = rp0 - 9 * a2)%Z) by (subst rp2 a2; destruct cb; lia).
clearbody a2 rp2. clear Hcb Ecb.
zs. brf K3.
-
destruct n as [|n']; [discriminate HL|]. rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k + 1 =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in HL. injection HL as <-.
replace (Z_to_bv 64 (XA + 4 * (k + 1))) with (Z_to_bv 64 (XA + 4 * z)) by (f_equal; lia).
replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
eapply CONT; [mk_dfinv | exact XR' | exact X31' | cbn; lia | cbn; lia | cbn; intros E; apply Hak2; lia | cbn; lia | cbn; lia].
-
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev _ sign x' (k + 1)%Z carry' a2 rp2 z p10 j10 rpm9 kz rp0 s1);
[mk_dfinv | exact FOK | exact FRM' | exact XR' | exact X31' | lia | lia | lia | intros E; left; exact (Hak2 E) | lia | lia | exact Hp10 | lia | lia | lia | lia | exact HL | exact CONT]. }
zs. brf K2.
-
eapply (G0FC true). symmetry. apply Z.ltb_lt. lia.
-
zs. zs. rewrite land2047, (Z.mod_small (a + 1) 2048) by lia. zs.
eapply (G0FC false). symmetry. apply Z.ltb_ge. lia.
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_U1A8"] Lemma L_T : S_T.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_tz in HK. destruct (df_tz_loop FUEL_RING x kz) as [z|] eqn:HTZ; [|discriminate HK]. unfold FUEL_RING in HTZ.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
rewrite lor_shl32 by lia. replace (Z.shiftl kz 2 + XA + -4)%Z with (XA + 4 * (kz - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (kz - kz)) by (f_equal; lia).
eapply (L_TZL 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz kz z);
[exact DI0 | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HTZ | ].
intros x15' Rz Hnz. clear HTZ.
unfold dfK_al in HK. unfold nz in HK.

zs. fixw3. fixw. replace (kz - (kz - z + 1))%Z with (z - 1)%Z by lia.
zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite magic_q9 by lia. rewrite rem9_fix by lia.
pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as Rrem.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (clear; intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (clear; intros; apply Z.rem_nonpos; lia).
set (r9 := Z.rem rp 9) in *. assert (Rr9 : (-8 <= r9 <= 8)%Z) by (clear -Rrem; lia). clearbody r9. clear Rrem.
zs. fixw3. fixw. replace (z - 1 + 1)%Z with z by lia.

assert (G178 : forall m' ws' x' (a' rp' z' rpm9 : Z) (x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (inring 0 z') -> X31 x' -> (0 <= a' < z')%Z -> (1 <= z' <= 2047)%Z -> (-2^15 - 9 * 2047 <= rp' <= 2^15 /\ 9 * a' + rp' <= 537)%Z -> (1 <= rpm9 <= 8)%Z ->
dfK_up 53 (-1074) sign fR (rp' + (9 - rpm9)) a' z' 0 x' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 x10' (Z_to_bv 64 rpm9) x12' x13' x14' x15'' x16' x17'
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 x21 x22 (Z_to_bv 64 rp') (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 0xd70a8) fct None m' (seg_rom rsegs))).
{ intros m' ws' x' a' rp' z' rpm9 x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' DI2 XR2 X312 Ra' Rz' Rrp' Rrpm9 HK2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HK. pose proof DI2 as DI'. dest_dfinv DI'.
zs. fixw3. fixw. zs. replace (rp' - rpm9 + 9)%Z with (rp' + (9 - rpm9))%Z by lia.
eapply L_UPI; [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | exact XR2 | exact X312 | lia | lia | lia | exact HK2]. }
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (E0 : r9 = 0%Z) by (clear -K1 Rr9; mlia).
rewrite E0, Z.eqb_refl in HK. cbv beta iota in HK.
zs. zs.
eapply L_UPI; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
-
assert (Hne0 : r9 <> 0%Z) by (clear -K1 Rr9; mlia).
replace (r9 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0). cbv beta iota in HK.

assert (G0B4 : forall rpm9 (x14' : word), rpm9 = (if 0 <=? rp then r9 else r9 + 9)%Z -> (1 <= rpm9 <= 8)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) x14' x15' x16 x17
(Z_to_bv 64 z) x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6fe4) fct None m (seg_rom rsegs))).
{ intros rpm9 x14' Hrpm9 Rrpm9. rewrite <- Hrpm9 in HK.
set (j10 := (8 - rpm9)%Z) in *.

assert (G0E4 : forall (x16' : word),
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (z - 1 + 1)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (znth p10s j10)) x16' (Z_to_bv 64 1000001536)
(Z_to_bv 64 z) (Z_to_bv 64 0) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7014) fct None m (seg_rom rsegs))).
{ intros x16'.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10].
destruct (df_al_loop FUEL_RING _ z _) as [[k1 a1 rp1 c1 x1']|] eqn:HAL; [|discriminate HK]. unfold FUEL_RING in HAL.
zs. zs. zs. rewrite zext32_small by lia. zs. rewrite divw_small by lia. zs. zs.
replace (Z_to_bv 64 (z - 1 + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
replace (Z_to_bv 64 XA) with (Z_to_bv 64 (XA + 4 * 0))%Z by (f_equal; lia).
eapply (L_ALK 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x 0%Z 0%Z 0%Z rp z (znth p10s j10) j10 rpm9 kz rp (mkAL k1 a1 rp1 c1 x1'));
[exact DI0 | exact FOK | exact FRM' | | exact X31H | lia | lia | lia | intros _; right; split; [reflexivity | exact Hx0] | lia | lia | reflexivity | lia | lia | lia | lia | exact HAL | ].
{ eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia. }
intros m' ws' x6' x7' x28' DI2 XR2 X312 Hk1 Ra1 Hac1 Rc1 Rrp1. cbn [al_x al_k al_a al_carry al_rp] in DI2, XR2, X312, Hk1, Ra1, Hac1, Rc1, Rrp1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HAL LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
unfold nz in HK.
zs. brf K4.
+
replace (negb (c1 =? 0)) with false in HK by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). cbv beta iota in HK.
eapply (G178 m' ws' x1' a1 rp1 z rpm9); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | lia | lia | lia | lia | exact HK].
+
replace (negb (c1 =? 0)) with true in HK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. fixw3. fixw. replace (z - 1 + 2)%Z with (z + 1)%Z by lia.
zs. try rewrite signed_of_Z by lia. rewrite shr30_4z by lia. zs. zs.
pose proof (u32arr_store_ok rsegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ z (Z_to_bv 64 c1) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (G178 _ (upd ws' (Z.to_nat z) (Z_to_bv 64 c1)) (zupd x1' z c1) a1 rp1 (z + 1)%Z rpm9); [mk_dfinv | | | lia | lia | lia | lia | exact HK].
* split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 z) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
-- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL2; [lia|].
unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
* intros q0. destruct (Z.eq_dec q0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X312]. }

zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
assert (Hc : (rpm9 = 1 \/ rpm9 = 2 \/ rpm9 = 3 \/ rpm9 = 4 \/ rpm9 = 5 \/ rpm9 = 6 \/ rpm9 = 7 \/ rpm9 = 8)%Z) by lia.
clear HK Hrpm9. subst j10.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rpm9; (zs; eapply G0E4). }

zs. try rewrite (signed_of_Z rp) by lia.
destruct (Z.lt_ge_cases rp 0) as [Hneg|Hpos].
+ rewrite (shr63_neg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+ rewrite (shr63_nonneg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.

End Floatscan.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x QCwx Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F1 := (@QHB6.Mq3.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A69C := (@QHB6.Mq3.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_F1 : S_F1.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_F1"] Lemma L_A69C : S_A69C.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (3 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 3) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 3) 2047) in *.
assert (Ek : kk = ((a + 3) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL.

assert (G6BC : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (4 <= (z' - a) mod 2048)%Z ->
fin_K1 53 (-1074) sign 1024 zero0 a z' x' 4 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) (Z_to_bv 64 (a + 4)) (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9cb0) fct None m' (seg_rom usegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Hrs' HK'.
clear HL HK MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (X312 kk) as Rt. pose proof (REL2 kk ltac:(lia) (zone_in _ _ _ _ _ Kin)) as Et.
pose proof (u32arr_read usegs _ _ _ kk _ _ XW (nth_error_wnth ws' kk ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws' kk (znth x' kk) (eq_sym Et) Rt).
set (t := znth x' kk) in *.
zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 Y) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_F1. eapply NX; try eassumption; try lia; try mk_dfinv.
- apply (xrel_window _ _ h' w); split; [exact LW2 | split; [exact LX2 | exact REL2]].
- intros Hne. change MASK with 2047%Z in Hne |- *. destruct (inring_plus a z' 4 ltac:(lia) ltac:(lia) ltac:(lia) Hne) as [Hin' _]. exact Hin'. }
zs. replace (3 + a)%Z with (a + 3)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [as_i] in HL.
change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
destruct (inring_plus a z 3 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G6BC _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | exact Hrs' | exact HK].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 3 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
cbn [as_i] in HL. change (3 + 1 <? LD_B1B_DIG)%Z with false in HL. rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 4) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 4) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs. showall.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
+
rewrite Ez in HL. rewrite Ez. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
assert (Ekz : kk = z) by lia.
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; rewrite Ek in Ekz; clear -Raw Ekz Ra Ez; Z.div_mod_to_equations; lia]).
let v := getreg 11%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; cbn; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
eapply (G6BC _ ws x 0%Z false); [mk_dfinv | | exact X31H | | lia | | exact HK].
* eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0 Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
* unfold inring. clear -Ra Rz Ez Hrs0 Rk K1. Z.div_mod_to_equations. lia.
* clear -Ra Rz Ez Hrs0. Z.div_mod_to_equations. lia.
+
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL. injection HL as <-. cbn [as_z as_x as_i as_y] in HK.
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
eapply (G6BC _ (upd ws (Z.to_nat z) (Z_to_bv 64 0)) (zupd x z 0) (z + 1)%Z h);
[mk_dfinv | exact XR' | exact X31' | | lia | | exact HK].
* apply (proj2 (inring_grow a z kk ltac:(lia) ltac:(lia))). right. rewrite Ek, Zminus_mod_idemp_l, Hrs0. f_equal. lia.
* replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)), Hrs0, Z.mod_small by lia. lia.
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

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation S_N324 := (@QHB6.Mq3.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N2D4 := (@QHB6.Mq3.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU; unfold QHB6.Mq3.hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Hypothesis HS_N324 : S_N324.

#[using="HS_N324"] Lemma L_N2D4 : S_N2D4.
Proof.
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
do 20 zs.
rewrite ?land2047. fix_idx.
stmt HS_N324. eapply NX; try eassumption; try lia.
- rewrite Z.shiftl_mul_pow2 by lia. lia.
- rewrite landW_mod2048. replace (z + -1)%Z with (z - 1)%Z by lia. reflexivity.
Qed.

End Floatscan.
End Mq6.

Module Mq7.

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

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation L_RET1 := (@QHB6.Mq3.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinvG_dfinv := (@QHB6.Mq3.dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_DD0 := (@QHB6.Mq3.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@QHB6.Mq3.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@QHB6.Mq3.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_R := (@QHB6.Mq3.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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

Hypothesis HS_P : S_P.
Hypothesis HS_DD24 : S_DD24.
Hypothesis HS_DD0 : S_DD0.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_P HS_DD24 HS_DD0"] Lemma L_R : S_R.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Rdc Rlnz Hlnz Hxk Hkj Hkj45 Rrp Hw80 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_rng in HK.
change (Z.quot (- (-1074)) 2) with 537%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
change (30 <? 53)%Z with true in HK. cbn [orb] in HK.
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) ltac:(unfold digz; right; left; reflexivity)) as Et0.
pose proof (u32arr_read usegs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. rewrite (sx32_wval ws 0%Z (znth x 0) (eq_sym Et0) Rt0). set (x0 := znth x 0) in *. clear RD0.
zs. brf K1; rewrite ?land_W64 in K1.
{
assert (E0 : x0 = 0%Z) by (clear -K1 Rt0; mlia).
rewrite E0, Z.eqb_refl in HK. some_snd HK.
assert (Rs : (-1 <= sign <= 1)%Z) by lia.
zs. zs. zs. zs. zs.
callx (eapply extenddftf2_callF; [eassumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL; try fok.
unfold D_ZERO in HK. symmetry. exact HK. }
assert (Hne0 : x0 <> 0%Z) by (clear -K1 Rt0; mlia). clear K1.
replace (x0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0).
specialize (Hlnz Hne0). specialize (Hw80 Hne0). subst w80. rewrite dfinvG_dfinv in DI0.

assert (G3C : forall (x10' : word),
((lrp =? dc) && (dc <? 10) = false)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10' x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9330) fct None m (seg_rom usegs))).
{ intros x10' Hc. rewrite Hc in HK. cbv iota in HK.
zs. zs. zs. brs K5.
-
replace (537 <? lrp)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs.
try replace (Z_to_bv 64 18446744073709550316) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (18446744073709550542 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
try replace (Z_to_bv 64 (-1074 + -226)) with (Z_to_bv 64 (-1300)) by (apply Z_to_bv_eqm; reflexivity).
zs. brs K6.
+
replace (lrp <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
stmt HS_P. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
replace (lrp <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MIN); try eassumption; try lia; try mk_dfinv. symmetry; exact HK.
-
replace (537 <? lrp)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). some_snd HK.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. zs.
try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. try replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity). zs. zs.
stmt HS_DD0. eapply NX with (Y := C_LDBL_MAX); try eassumption; try lia; try mk_dfinv. symmetry; exact HK. }
zs. zs. brs K2.
{  apply G3C. replace (dc <? 10)%Z with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
zs. brf K3; rewrite ?land_W64 in K3.
{  assert (Hne : lrp <> dc) by (clear -K3 Rrp Rdc; mlia).
apply G3C. replace (lrp =? dc)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
assert (Heq : lrp = dc) by (clear -K3 Rrp Rdc; mlia). clear K3.
replace (lrp =? dc)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia).
replace (dc <? 10)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in HK. some_snd HK.

zs. zs. zs. zs. zs. zs. brf K4.
{ exfalso. clear -K4. rewrite ?land_W64 in K4.
match type of K4 with (?a = 0)%Z => idtac end.
revert K4. match goal with |- context [Z.lor 1 ?b] => destruct (Z.lor_eq_0_iff 1 b) as [F _]; intros K4; try (specialize (F K4); lia) end.
all: try (Z.div_mod_to_equations; lia). }
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs.
stmt HS_DD24. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
Qed.

End Floatscan.
End Mq7.

Module Mq8.

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
Local Notation S_U1A8 := (@QHB6.Mq3.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_T := (@QHB6.Mq3.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_U1A8 : S_U1A8.

#[using="Type"] Lemma lor_shl32 : forall k, (0 <= k < 2^31)%Z -> (Z.lor (Z.land (Z.shiftl k 32) 18446744073709551615) 4294967295 + 1 = (k + 1) * 4294967296)%Z.
Proof.
clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change (2^32)%Z with 4294967296%Z.
rewrite land_W64, (Z.mod_small (k * 4294967296)) by lia.
rewrite <- Z.lxor_lor. 2:{ change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. rewrite Z.mod_mul. reflexivity. lia. }
rewrite <- Z.add_nocarry_lxor. { lia. }
change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32)%Z with 4294967296%Z. apply Z.mod_mul. lia.
Qed.
#[using="Type"] Lemma tz_dec32 : forall j, Z_to_bv 64 ((j + 1) * 4294967296 + 18446744069414584320) = Z_to_bv 64 (j * 4294967296).
Proof. clear. intros j. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma df_tz_loop_step : forall n x z, df_tz_loop (S n) x z = if (znth x (z - 1) =? 0)%Z then df_tz_loop n x (z - 1) else Some z.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_al_loop_step : forall n p10 z s, df_al_loop (S n) p10 z s = if negb (al_k s =? z)%Z then df_al_loop n p10 z (df_al_body p10 s) else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma divuw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z ->
v_divuw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
clear. intros v i Hv Hi. unfold v_divuw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i), (Z.mod_small v) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
assert (0 <= v / i < 2147483648)%Z by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite swrap32_eq. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma magic_q9 : forall rp, (-2^20 <= rp <= 2^20)%Z ->
(Z.shiftr (bv_signed (Z_to_bv 64 (Z.land rp 18446744073709551615 * 954437177))) 33
+ Z.shiftr (Z.land (Z.land rp 18446744073709551615 * 954437177) 18446744073709551615) 63 = Z.quot rp 9)%Z.
Proof.
clear. intros rp Hrp.
rewrite (Z_to_bv_eqm (Z.land rp 18446744073709551615 * 954437177) (rp * 954437177)).
2:{ rewrite land_W64. apply Z.mul_mod_idemp_l. lia. }
rewrite signed_of_Z by lia. rewrite !land_W64. rewrite Z.mul_mod_idemp_l by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2^33)%Z with 8589934592%Z. change (2^63)%Z with 9223372036854775808%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (intros; apply Z.rem_nonpos; lia).
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rem9_fix : forall rp, (-2^20 <= rp <= 2^20)%Z ->
bv_swrap 32 (Z.land (bv_swrap 32 (Z.land rp 18446744073709551615 - Z.land (Z.quot rp 9) 18446744073709551615)) 18446744073709551615
- Z.land (Z.shiftl (Z.land (Z.quot rp 9) 18446744073709551615) 3) 18446744073709551615) = Z.rem rp 9.
Proof.
clear. intros rp Hrp. rewrite !land_W64, !swrap32_eq, Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (Z.quot_rem' rp 9) as E. pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as B.
set (Qv := Z.quot rp 9) in *. set (Rv := Z.rem rp 9) in *. clearbody Qv Rv.
Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma shr63_neg : forall v, (-2^63 <= v < 0)%Z -> Z.shiftr v 63 = (-1)%Z.
Proof. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shr63_nonneg : forall v, (0 <= v < 2^63)%Z -> Z.shiftr v 63 = 0%Z.
Proof. clear. intros v Hv. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
#[using="Type"] Lemma shr30_4z : forall z, (0 <= z)%Z -> Z.shiftr (z * 4294967296) 30 = (4 * z)%Z.
Proof. clear. intros z Hz. rewrite Z.shiftr_div_pow2 by lia. change (2^30)%Z with 1073741824%Z. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma zext32_small : forall v, (0 <= v < 2^32)%Z -> Z.land v 4294967295 = v.
Proof. clear. intros v Hv. change 4294967295%Z with (2^32 - 1)%Z. apply land_mask_small; lia. Qed.

#[using="pre"] Lemma L_TZL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (rp kz j z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= j <= kz)%Z ->
df_tz_loop n x j = Some z ->
(forall x15', (1 <= z <= j)%Z -> znth x (z - 1) <> 0%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 (kz - z + 1)) (Z_to_bv 64 (XA + 4 * (z - 2))) (Z_to_bv 64 z) (Z_to_bv 64 18446744069414584320) x15' x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9668) fct None m (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 ((j + 1) * 4294967296)) (Z_to_bv 64 (kz - j)) (Z_to_bv 64 (XA + 4 * (j - 1))) (Z_to_bv 64 (j + 1)) (Z_to_bv 64 18446744069414584320) x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9650) fct None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; intros until z; intros DI XR X31H Rkz Hx0 Rj HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_tz_loop_step in HL.
assert (Kin : inring 0 kz (j - 1)) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H (j - 1)%Z) as Rt. pose proof (REL (j - 1)%Z ltac:(lia) Kin) as Et.
pose proof (u32arr_read usegs _ _ _ (j - 1)%Z _ _ XW (nth_error_wnth ws (j - 1)%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws (j - 1)%Z (znth x (j - 1)) (eq_sym Et) Rt). set (t := znth x (j - 1)) in *. clear RD.
zs. zs. rewrite tz_dec32. zs. replace (j + 1 + -1)%Z with j by lia. zs. replace (XA + 4 * (j - 1) + -4)%Z with (XA + 4 * (j - 1 - 1))%Z by lia.
zs. brf K1.
-
replace (t =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
assert (Hj1 : j <> 1%Z) by (intros E; apply Hx0; subst t; rewrite E in K1; exact K1).
replace (kz - j + 1)%Z with (kz - (j - 1))%Z by lia. replace (j * 4294967296)%Z with ((j - 1 + 1) * 4294967296)%Z by (f_equal; lia).
replace (Z_to_bv 64 j) with (Z_to_bv 64 (j - 1 + 1)) by (f_equal; lia).
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz (j - 1)%Z z);
[exact DI | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HL | ].
intros x15' Rz Hnz. eapply CONT; [lia | exact Hnz].
- replace (t =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). injection HL as <-.
replace (j - 1 - 1)%Z with (j - 2)%Z by lia.
eapply CONT; [lia | subst t; exact K1].
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 HS_U1A8"] Lemma L_UPI : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp a z : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 z) -> X31 x -> (0 <= a < z)%Z -> (1 <= z <= 2047)%Z -> (-2^16 <= rp <= 2^16 /\ 9 * a + rp <= 560)%Z ->
dfK_up 53 (-1074) sign fR rp a z 0 x = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9774) fct None m (seg_rom usegs)).
Proof.
intros until z. intros DI RJ Hk FOK FRM' Hsg XR X31H Ra Rz Rrp HK.
unfold dfK_up in HK. destruct (df_up_loop FUEL_SCALE _) as [[rp' a' z' e2' x']|] eqn:HL; [|discriminate HK].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
stmt HS_U1A8. eapply (NX 2000%nat) with (h := false) (w := false) (x := x) (s' := mkUS rp' a' z' e2' x');
[exact DI | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | lia | | exact X31H | lia | intros _; lia | intros _; lia | lia | lia | cbn; lia | unfold FUEL_SCALE in HL; exact HL | ].
- eapply xrel_iff; [| exact XR]. intros i Hi [Hr | [[Hr _] | [Hr _]]]; [| discriminate Hr | discriminate Hr]. unfold inring in Hr |- *. clear -Hr Hi Ra Rz. Z.div_mod_to_equations. nia.
- unfold up_K, fin_K0. cbn [us_rp us_a us_z us_e2 us_x]. unfold dfK_dn in HK.
destruct (df_dn_loop FUEL_SCALE _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate HK]. cbn [ds_a ds_z ds_x ds_e2].
cbv beta zeta in HK. change (- (-1074) - 53 + 3)%Z with 1024%Z in HK. fold zero0 in HK.
destruct (df_final _ _ _ _ _ _ _ _ _ _) as [y|]; [|discriminate HK]. injection HK as <-. reflexivity.
Qed.

#[using="pre T1 SPF SPF2 SPT SG1"] Lemma L_ALK : forall (n : nat) m (x1 x6 x7 x8 x9 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (k carry a rp z p10 j10 rpm9 kz rp0 : Z) (s1 : st_al),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (inring 0 z) -> X31 x ->
(1 <= z <= 2046)%Z -> (0 <= k < z)%Z -> (0 <= a <= k)%Z -> (a = k -> carry <> 0%Z \/ (k = 0%Z /\ znth x 0 <> 0%Z)) ->
(0 <= carry < 2^30)%Z -> (0 <= j10 <= 7)%Z -> p10 = znth p10s j10 -> (rp = rp0 - 9 * a)%Z -> (-2^15 <= rp0 <= 2^15)%Z ->
(1 <= rpm9 <= 8)%Z -> (1 <= kz <= 2046)%Z ->
df_al_loop n p10 z (mkAL k a rp carry x) = Some s1 ->
(forall m' ws' (x6' x7' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (al_x s1) (inring 0 z) -> X31 (al_x s1) -> al_k s1 = z ->
(0 <= al_a s1 <= z)%Z -> (al_a s1 = z -> al_carry s1 <> 0%Z) -> (0 <= al_carry s1 < 2^30)%Z -> (al_rp s1 = rp0 - 9 * al_a s1)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * z)) x6' x7' x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) (Z_to_bv 64 (al_carry s1)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (al_a s1)) x20 x21 x22 (Z_to_bv 64 (al_rp s1)) (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 0xd9740) fct None m' (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 carry) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9718) fct None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; intros until s1; intros DI FOK FRM' XR X31H Rz Rk Ra Hak Rc Rj Hp10 Rrp Rrp0 Rrpm9 Rkz HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'. destruct XR as (LW' & LX & REL). bury_disj.
rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbn [negb] in HL.
unfold df_al_body in HL. cbn [al_k al_x al_a al_rp al_carry] in HL.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10]. rewrite <- Hp10 in Rp10, Dp10.
assert (Kin : inring 0 z k) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) Kin) as Et.
pose proof (u32arr_read usegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
zs. rewrite divuw_small by lia.
pose proof (Z.mod_pos_bound t p10 ltac:(lia)) as Rtm.
assert (Rtq : (0 <= t / p10 < 214748365)%Z) by (clear -Rt Rp10; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | nia]]).
zs. fixw3. fixw.
set (v := (t / p10 + carry)%Z) in *.
assert (Rv : (0 <= v < 2^31)%Z) by (clear -Rtq Rc; subst v; lia).
zs. zs.
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (Rc' : (0 <= t mod p10 * (1000000000 / p10) < 1000000000)%Z).
{ clear -Rtm Rp10 Dp10. set (u := (t mod p10)%Z) in *. set (w := (1000000000 / p10)%Z) in *. clearbody u w. nia. }
set (carry' := (t mod p10 * (1000000000 / p10))%Z) in *.
rewrite (u32_id v) in HL by (clear -Rv; lia). rewrite (Z.mul_comm (1000000000 / p10) (t mod p10)) in HL. fold carry' in HL. rewrite (u32_id carry') in HL by (clear -Rc'; lia).
set (x' := zupd x k v) in *.
assert (Exk : znth x' k = v) by (clear -LX Rk Rz; subst x'; rewrite znth_zupd_eq by (unfold zlength; lia); reflexivity). rewrite Exk in HL.
assert (XR' : xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) x' (inring 0 z)).
{ clear -LW' LX REL Rk Rz Rv. split; [rewrite upd_length; exact LW'|]. split; [subst x'; rewrite zupd_length; exact LX|].
intros q0 Hq Hr. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia | exact Hr]. }
assert (X31' : X31 x').
{ clear -X31H LX Rk Rz Rv. intros q0. subst x'. destruct (Z.eq_dec q0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); exact Rv | rewrite znth_zupd_neq by lia; apply X31H]. }
pose proof (lor_lxor_nonneg k a v ltac:(lia) ltac:(lia) ltac:(lia)) as Rw.

assert (G0FC : forall (cb : bool),
cb = (0 <? Z.lor (Z.lxor k a) v)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 t) (Z_to_bv 64 (t / p10)) x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 k) (Z_to_bv 64 (Z.lor (Z.lxor k a) v)) (Z_to_bv 64 p10) (Z_to_bv 64 z) (Z_to_bv 64 (1000000000 / p10))
(Z_to_bv 64 z) (Z_to_bv 64 (if cb then a else a + 1)%Z) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 (Z_to_bv 64 v) x29 x30 x31)
Ft (Z_to_bv 64 0xd96f0) fct None m1 (seg_rom usegs))).
{ intros cb Hcb.
assert (Ecb : cb = negb ((k =? a) && (v =? 0))%Z).
{ rewrite Hcb. clear -Rw Rk Ra Rv. destruct ((k =? a) && (v =? 0))%Z eqn:Eb; cbn [negb].
- apply andb_prop in Eb. destruct Eb as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
apply Z.ltb_ge. rewrite (proj2 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia)) (conj E1 E2)). lia.
- apply Z.ltb_lt. assert (Hne : Z.lor (Z.lxor k a) v <> 0%Z); [|lia].
intros E0. apply (proj1 (lor_lxor_zero k a v ltac:(lia) ltac:(lia) ltac:(lia))) in E0. destruct E0 as [E1 E2].
apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; apply Z.eqb_neq in Eb; lia. }
zs. zs. rewrite <- Hcb. zs. zs. fixw3. fixw. replace (t - t / p10 * p10)%Z with (t mod p10)%Z by (rewrite Zmod_eq_full by lia; lia).
zs. zs. try rewrite (land_W64_small (t mod p10)) by (clear -Rtm; lia). try rewrite (swrap32_small (t mod p10 * (1000000000 / p10))) by (clear -Rc'; lia). fold carry'.
zs. zs. rewrite rp_upd. zs. replace (XA + 4 * k + 4)%Z with (XA + 4 * (k + 1))%Z by lia.
set (a2 := (if cb then a else a + 1)%Z) in *. set (rp2 := (if cb then rp else rp - 9)%Z) in *.
assert (Ea2 : (if (k =? a) && (v =? 0) then (Z.land (a + 1) MASK, rp - 9) else (a, rp))%Z = (a2, rp2)).
{ subst a2 rp2. rewrite Ecb. destruct ((k =? a) && (v =? 0))%Z; cbn [negb]; [|reflexivity]. change MASK with 2047%Z. rewrite land2047, Z.mod_small by lia. reflexivity. }
rewrite Ea2 in HL. clear Ea2.
assert (Ra2 : (0 <= a2 <= k + 1)%Z) by (subst a2; destruct cb; lia).
assert (Hak2 : (a2 = k + 1 -> carry' <> 0)%Z).
{ subst a2. rewrite Ecb. destruct (Z.eqb_spec k a) as [Eka|Hka]; destruct (Z.eqb_spec v 0) as [Ev|Hv]; cbn [andb negb]; try lia.
intros _. destruct (Hak (eq_sym Eka)) as [Hc | [Hk0 Hx0]]; [exfalso; subst v; lia|].
assert (Ht0 : t <> 0%Z) by (subst t; rewrite Hk0; exact Hx0).
assert (Htp : (t < p10)%Z). { subst v. assert (t / p10 = 0)%Z by lia. destruct (Z.lt_ge_cases t p10); [assumption|]. exfalso. assert (1 <= t / p10)%Z by (apply Z.div_le_lower_bound; lia). lia. }
subst carry'. rewrite Z.mod_small by lia. assert (10 <= 1000000000 / p10)%Z by (apply Z.div_le_lower_bound; lia). nia. }
assert (Rrp2 : (rp2 = rp0 - 9 * a2)%Z) by (subst rp2 a2; destruct cb; lia).
clearbody a2 rp2. clear Hcb Ecb.
zs. brf K3.
-
destruct n as [|n']; [discriminate HL|]. rewrite df_al_loop_step in HL. cbn [al_k] in HL.
replace (k + 1 =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbn [negb] in HL. injection HL as <-.
replace (Z_to_bv 64 (XA + 4 * (k + 1))) with (Z_to_bv 64 (XA + 4 * z)) by (f_equal; lia).
replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
eapply CONT; [mk_dfinv | exact XR' | exact X31' | cbn; lia | cbn; lia | cbn; intros E; apply Hak2; lia | cbn; lia | cbn; lia].
-
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev _ sign x' (k + 1)%Z carry' a2 rp2 z p10 j10 rpm9 kz rp0 s1);
[mk_dfinv | exact FOK | exact FRM' | exact XR' | exact X31' | lia | lia | lia | intros E; left; exact (Hak2 E) | lia | lia | exact Hp10 | lia | lia | lia | lia | exact HL | exact CONT]. }
zs. brf K2.
-
eapply (G0FC true). symmetry. apply Z.ltb_lt. lia.
-
zs. zs. rewrite land2047, (Z.mod_small (a + 1) 2048) by lia. zs.
eapply (G0FC false). symmetry. apply Z.ltb_ge. lia.
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_U1A8"] Lemma L_T : S_T.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_tz in HK. destruct (df_tz_loop FUEL_RING x kz) as [z|] eqn:HTZ; [|discriminate HK]. unfold FUEL_RING in HTZ.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
rewrite lor_shl32 by lia. replace (Z.shiftl kz 2 + XA + -4)%Z with (XA + 4 * (kz - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (kz - kz)) by (f_equal; lia).
eapply (L_TZL 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x rp kz kz z);
[exact DI0 | exact (conj LW' (conj LX REL)) | exact X31H | lia | exact Hx0 | lia | exact HTZ | ].
intros x15' Rz Hnz. clear HTZ.
unfold dfK_al in HK. unfold nz in HK.

zs. fixw3. fixw. replace (kz - (kz - z + 1))%Z with (z - 1)%Z by lia.
zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite magic_q9 by lia. rewrite rem9_fix by lia.
pose proof (Z.rem_bound_abs rp 9 ltac:(lia)) as Rrem.
assert (S1 : (0 <= rp -> 0 <= Z.rem rp 9)%Z) by (clear; intros; apply Z.rem_nonneg; lia).
assert (S2 : (rp <= 0 -> Z.rem rp 9 <= 0)%Z) by (clear; intros; apply Z.rem_nonpos; lia).
set (r9 := Z.rem rp 9) in *. assert (Rr9 : (-8 <= r9 <= 8)%Z) by (clear -Rrem; lia). clearbody r9. clear Rrem.
zs. fixw3. fixw. replace (z - 1 + 1)%Z with z by lia.

assert (G178 : forall m' ws' x' (a' rp' z' rpm9 : Z) (x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (inring 0 z') -> X31 x' -> (0 <= a' < z')%Z -> (1 <= z' <= 2047)%Z -> (-2^15 - 9 * 2047 <= rp' <= 2^15 /\ 9 * a' + rp' <= 537)%Z -> (1 <= rpm9 <= 8)%Z ->
dfK_up 53 (-1074) sign fR (rp' + (9 - rpm9)) a' z' 0 x' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 x10' (Z_to_bv 64 rpm9) x12' x13' x14' x15'' x16' x17'
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 x21 x22 (Z_to_bv 64 rp') (Z_to_bv 64 kz) x25 x26 x27 x28' x29 x30 x31)
Ft (Z_to_bv 64 0xd976c) fct None m' (seg_rom usegs))).
{ intros m' ws' x' a' rp' z' rpm9 x5' x6' x7' x10' x12' x13' x14' x15'' x16' x17' x28' DI2 XR2 X312 Ra' Rz' Rrp' Rrpm9 HK2.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HK. pose proof DI2 as DI'. dest_dfinv DI'.
zs. fixw3. fixw. zs. replace (rp' - rpm9 + 9)%Z with (rp' + (9 - rpm9))%Z by lia.
eapply L_UPI; [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | exact XR2 | exact X312 | lia | lia | lia | exact HK2]. }
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (E0 : r9 = 0%Z) by (clear -K1 Rr9; mlia).
rewrite E0, Z.eqb_refl in HK. cbv beta iota in HK.
zs. zs.
eapply L_UPI; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
-
assert (Hne0 : r9 <> 0%Z) by (clear -K1 Rr9; mlia).
replace (r9 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne0). cbv beta iota in HK.

assert (G0B4 : forall rpm9 (x14' : word), rpm9 = (if 0 <=? rp then r9 else r9 + 9)%Z -> (1 <= rpm9 <= 8)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 z) x14' x15' x16 x17
(Z_to_bv 64 z) x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd96a8) fct None m (seg_rom usegs))).
{ intros rpm9 x14' Hrpm9 Rrpm9. rewrite <- Hrpm9 in HK.
set (j10 := (8 - rpm9)%Z) in *.

assert (G0E4 : forall (x16' : word),
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 (z - 1 + 1)) x6 x7 x8 x9 (Z_to_bv 64 (z * 4294967296)) (Z_to_bv 64 rpm9) (Z_to_bv 64 (z - 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (znth p10s j10)) x16' (Z_to_bv 64 1000001536)
(Z_to_bv 64 z) (Z_to_bv 64 0) x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd96d8) fct None m (seg_rom usegs))).
{ intros x16'.
destruct (p10s_range j10 ltac:(lia)) as [Rp10 Dp10].
destruct (df_al_loop FUEL_RING _ z _) as [[k1 a1 rp1 c1 x1']|] eqn:HAL; [|discriminate HK]. unfold FUEL_RING in HAL.
zs. zs. zs. rewrite zext32_small by lia. zs. rewrite divw_small by lia. zs. zs.
replace (Z_to_bv 64 (z - 1 + 1)) with (Z_to_bv 64 z) by (f_equal; lia).
replace (Z_to_bv 64 XA) with (Z_to_bv 64 (XA + 4 * 0))%Z by (f_equal; lia).
eapply (L_ALK 2050%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign x 0%Z 0%Z 0%Z rp z (znth p10s j10) j10 rpm9 kz rp (mkAL k1 a1 rp1 c1 x1'));
[exact DI0 | exact FOK | exact FRM' | | exact X31H | lia | lia | lia | intros _; right; split; [reflexivity | exact Hx0] | lia | lia | reflexivity | lia | lia | lia | lia | exact HAL | ].
{ eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia. }
intros m' ws' x6' x7' x28' DI2 XR2 X312 Hk1 Ra1 Hac1 Rc1 Rrp1. cbn [al_x al_k al_a al_carry al_rp] in DI2, XR2, X312, Hk1, Ra1, Hac1, Rc1, Rrp1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HAL LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
unfold nz in HK.
zs. brf K4.
+
replace (negb (c1 =? 0)) with false in HK by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia). cbv beta iota in HK.
eapply (G178 m' ws' x1' a1 rp1 z rpm9); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | lia | lia | lia | lia | exact HK].
+
replace (negb (c1 =? 0)) with true in HK by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. fixw3. fixw. replace (z - 1 + 2)%Z with (z + 1)%Z by lia.
zs. try rewrite signed_of_Z by lia. rewrite shr30_4z by lia. zs. zs.
pose proof (u32arr_store_ok usegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ z (Z_to_bv 64 c1) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (G178 _ (upd ws' (Z.to_nat z) (Z_to_bv 64 c1)) (zupd x1' z c1) a1 rp1 (z + 1)%Z rpm9); [mk_dfinv | | | lia | lia | lia | lia | exact HK].
* split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 z) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
-- rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL2; [lia|].
unfold inring in Hr |- *. rewrite !Z.sub_0_r in Hr |- *. rewrite !Z.mod_small in Hr |- * by lia. lia.
* intros q0. destruct (Z.eq_dec q0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X312]. }

zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
assert (Hc : (rpm9 = 1 \/ rpm9 = 2 \/ rpm9 = 3 \/ rpm9 = 4 \/ rpm9 = 5 \/ rpm9 = 6 \/ rpm9 = 7 \/ rpm9 = 8)%Z) by lia.
clear HK Hrpm9. subst j10.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rpm9; (zs; eapply G0E4). }

zs. try rewrite (signed_of_Z rp) by lia.
destruct (Z.lt_ge_cases rp 0) as [Hneg|Hpos].
+ rewrite (shr63_neg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
+ rewrite (shr63_nonneg rp) by lia. zs. zs. fixw3. fixw. zs. (brf K2; [ exfalso; lia | ]).
eapply G0B4; [|lia]. replace (0 <=? rp) with true by (symmetry; apply Z.leb_le; lia). lia.
Qed.

End Floatscan.
End Mq8.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx2n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx2n.
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
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis Hpok1 : pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
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

Local Notation ctx_all := (@QHB6.Mq3.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@QHB6.Mq3.Wfs q Fp).
Local Notation FokR := (@QHB6.Mq3.FokR F).
Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
#[using="Type"] Lemma getc_rpos2 : forall f, sh_buf f = txt ->
(sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
Proof.
clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof.
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Definition and33_okb (c : Z) : bool :=
forallb (fun U => implb ((65 <=? U) && (U <=? 90))%Z (Bool.eqb (Z.land c 18446744073709551583 =? U) (Z.lor c 32 =? U + 32)))%Z
(map Z.of_nat (seq 0 91)).
#[using="Type"] Lemma and33_lor : forall c U, (0 <= c < 256)%Z -> (65 <= U <= 90)%Z ->
(Z.land c 18446744073709551583 = U <-> Z.lor c 32 = U + 32)%Z.
Proof.
clear. intros c U Hc HU.
pose proof (forallb_range and33_okb 256 ltac:(vm_compute; reflexivity) c Hc) as E. unfold and33_okb in E.
pose proof (forallb_range _ 91 E U ltac:(lia)) as E2. cbv beta in E2.
replace ((65 <=? U) && (U <=? 90))%Z with true in E2 by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia). cbn [implb] in E2.
apply Bool.eqb_prop in E2.
destruct (Z.eqb_spec (Z.land c 18446744073709551583) U); destruct (Z.eqb_spec (Z.lor c 32) (U + 32)); try discriminate E2; tauto.
Qed.
#[using="Type"] Lemma and33_range : forall c, (0 <= c < 256)%Z -> (0 <= Z.land c 18446744073709551583 < 256)%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => (0 <=? Z.land c 18446744073709551583) && (Z.land c 18446744073709551583 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma isspace_iff : forall c, (0 <= c < 256)%Z -> (m_isspace c = true <-> (c = 32 \/ 9 <= c <= 13))%Z.
Proof.
clear. intros c Hc. unfold m_isspace, u32.
destruct (Z.eqb_spec c 32) as [->|N]; cbn [orb]; [split; [intros _; left; reflexivity | reflexivity]|].
rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).
Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).
Notation FS_tail_h' := (FS_tail_h fuelc 53 (-1074) pok).
Notation FS_sign' := (FS_sign fuelc 53 (-1074) pok).

Definition SWSn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (0 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
fs_ws_loop n f = Some (c', f') -> FS_sign' c' f' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b24) fc None m (seg_rom usegs)).
Definition S_WS : Prop := forall n, SWSn n.

Definition S_AWS : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
(0 <= c < 256)%Z -> m_isspace c = false ->
FS_sign' c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b48) fc None m (seg_rom usegs)).

Definition S_I1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
Z.lor c 32 = 105%Z ->
FS_infk' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b8c) fc None m (seg_rom usegs)).

Definition S_N1 : Prop := forall m (x1 x5 x6 x7 x8 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= c < 256)%Z -> Z.lor c 32 <> 105%Z ->
FS_nank' sign 0 c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8bc4) fc None m (seg_rom usegs)).

Definition S_Z : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail_h' sign c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8c0c) fct None m (seg_rom usegs)).

Definition S_ERR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> sh_stdio f = sh_stdio f0 ->
fR = sh_lim0 (sh_unget f) -> yR = f128_of_i32 0 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd94f0) fct None m (seg_rom usegs)).

Definition sp_ok (v : word) (r : Z) : Prop :=
(v = Z_to_bv 64 0xffffffff7f800000 /\ r = C_INF) \/ (v = Z_to_bv 64 0xffffffffff800000 /\ r = C_NINF) \/ (v = Z_to_bv 64 0xffffffff7fc00000 /\ r = C_NAN).
Definition S_A38 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c (v : word),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
sp_ok v yR -> (forall r : bv 5, bv_unsigned r = 10%Z -> reg_get Ft r = v) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd94e8) fct None m (seg_rom usegs)).

Definition SPARn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile) (i i' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i <= kmin)%Z -> Fok Ft -> frm0 fct -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
(1 <= i <= sh_rpos f)%Z ->
fs_par_loop n (i, f) = Some (i', c', f') ->
(fR, yR) = (if (c' =? 41)%Z then (f', C_NAN) else (fs_unget_loop (Z.to_nat i') (sh_unget f'), C_NAN)) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8ec8) fct None m (seg_rom usegs)).
Definition S_PAR : Prop := forall n, SPARn n.

Definition hinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv usegs m /\ munch Wfs m0 m /\ wmono usegs m0 m
/\ stk usegs m (q - FS_DEPTH) q
/\ bytes_at usegs m T (zbytes txt)
/\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary]
/\ rw_cells usegs m RERRNO [C4 ev]
/\ rw_cells usegs m Fp (rf_cells T p true f J).

Definition S_HEX : Prop := forall m (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) Ft fct ev sign kmin c (f : shfile),
let _ := ctx_all in
hinv m ev f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> FokR Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> Z.lor c 32 = 120%Z ->
hexfloat_m fuelc f 53 (-1074) sign pok = Some (fR, yR) ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 53) (Z_to_bv 64 (-1074)) (Z_to_bv 64 sign) (Z_to_bv 64 pok) a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (Z_to_bv 64 0xda0e0) fct None m (seg_rom usegs)).
End Floatscan.
