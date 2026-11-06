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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A5C4 := (@QHB6.Mq0.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A568 := (@QHB6.Mq0.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@QHB6.Mq0.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A5C4 : S_A5C4.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SPLO SPF SPT SG1 Q1 HS_A5C4"] Lemma L_A578 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 t : Z) (f : nat) sres,
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 -> (0 <= t < 2^31)%Z ->
df_asm_loop f a (mkAS 1 (f128_add (f128_mul C_1E9 zero0) (f128_of_u32 t)) z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 t) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd74a8) fct None m (seg_rom rsegs)).
Proof.
intros until sres. intros DI RJ Hk FOK FRM' Hsg He2 Ra AI Rt HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := zero0); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 zero0) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A5C4. eapply NX; try eassumption; try lia; try mk_dfinv.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A568 : S_A568.
Proof.
intros m; intros until xa. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Naz Hxa HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (X31H a) as Rt. rewrite <- Hxa in Rt.
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). rewrite <- Hxa in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
assert (Hza : ((z - a) mod 2048 <> 0)%Z).
{ intros E. apply Naz. symmetry. apply (mod_eq_idx a a z); try lia. all: rewrite Z.sub_diag, E; reflexivity. }
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW' | split; [exact LX | exact REL]] |]. split; [exact X31H|]. split; [lia|]. split; [hlia Rz4|]. split; [lia|]. exact Raw.
Qed.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A534 : S_A534.
Proof.
intros m; intros until S1. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Eaz HS1 HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). rewrite !land2047 in HL.
subst a.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. zs. subst S1. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
-
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; lia]).
subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
pose proof (X31H 2047%Z) as Rt. pose proof (REL 2047%Z ltac:(lia) ltac:(right; right; split; [exact Hw | lia])) as Et.
pose proof (u32arr_read rsegs _ _ _ 2047%Z _ _ XW (nth_error_wnth ws 2047%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs. rewrite (sx32_wval ws 2047%Z (znth x 2047%Z) (eq_sym Et) Rt).
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := false) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [exact X31H | split; [lia | split; [lia| split; [cbn; lia | exact Raw]]]]].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0. Z.div_mod_to_equations. lia.
-
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
rewrite znth_zupd_eq in HL by (unfold zlength; lia).
pose proof (u32arr_store_ok rsegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write rsegs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
pose proof (u32arr_read rsegs _ _ _ z _ _ XW (nth_error_wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z ltac:(lia) ltac:(rewrite upd_length; lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs.
replace (sx32 (wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z)) with (Z_to_bv 64 0).
2:{ symmetry. apply (sx32_wval _ z 0); [rewrite wval_upd_same by lia; reflexivity | lia]. }
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := h) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [| split; [lia | split; [hlia Rz4| split; [| exact Raw]]]]].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr. destruct (Z.eq_dec i0 z) as [->|Hne].
* rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
* rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow z z i0 ltac:(lia) ltac:(rewrite Z.sub_diag; cbn; lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx z z i0); lia.
+ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H].
+ replace (z + 1 - z)%Z with 1%Z by lia. reflexivity.
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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A62C := (@QHB6.Mq0.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A5C4 := (@QHB6.Mq0.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A62C : S_A62C.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A62C"] Lemma L_A5C4 : S_A5C4.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (1 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 1) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 1) 2047) in *.
assert (Ek : kk = ((a + 1) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 2 <= 2052)%Z -> (2 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 2 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) x9 (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7518) fct None m' (seg_rom rsegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
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
stmt HS_A62C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. zs. replace (1 + a)%Z with (a + 1)%Z by lia. replace (a + 1 + 0)%Z with (a + 1)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 1 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 1 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 2) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 2) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs.
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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation S_N484 := (@QHB6.Mq0.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_N484 : S_N484.
Proof.
intros fo IH [kk carry a1 i rp1 xx] m'; intros until s'. intros _ DI2 RJ Hk FOK FRM' Hsg XR2 X312 Ra1 Rc1 Hkk Hsh Rz Rzf Rw Hfo Rrp Rrp1 Re2 HZ0 HS1 HA6 HL2 HK.
cbn [dk_x dk_a dk_carry dk_rp dk_k] in *. subst kk.

assert (Hshb : (1 <= sh <= 9)%Z) by (clear -Hsh; lia).
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (Z.mod_pos_bound (z - a1) 2048 ltac:(flia)) as Rrs1.
zs. brf K1.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with false in HL2 by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply IH with (h := h) (x := xx) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1: exact (conj LW2 (conj LX2 REL2)).
all: try hlia Rzf.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with true in HL2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).

assert (HZ0R__ : (0 <= Z0 < 2 ^ 64)%Z) by (first [ clear - LTX LW HZ0 Re2 Rrp Hfo Rz LX2 LW2 SG3 SG1 SPT SPF SE_T Hp; lia | lia ]).
zs. brf K2.
+
replace ((z + 1) mod 2048 =? a1)%Z with false in HL2 by (symmetry; apply Z.eqb_neq; first [ clear - K2 K1 LTX LW HZ0 Re2 Rrp Hfo Rzf Rz Rc1 LX2 LW2 SG3 SG1 SPT SPF SE_T Hp; flia | flia ]). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 < 2047)%Z).
{ clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok rsegs _ _ _ z _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ z (Z_to_bv 64 carry) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
assert (X31' : X31 (zupd xx z carry)).
{ intros ii. destruct (Z.eq_dec ii z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }

stash_mods. stash_disj. do 20 zs. unstash. rewrite ?land2047. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Hz47].
*
subst Z0. subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL2 |- *.
eapply IH with (h := false) (x := zupd xx 2047 carry) (z := 0%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr.
destruct (Z.eq_dec ii 2047) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hr _] | Hr]]; [left | discriminate Hr | right; right; exact Hr].
unfold inring in Hr |- *. clear -Hr Hne Hq Ra1 K2. Z.div_mod_to_equations. flia. }
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
* rewrite (Z.mod_small (z + 1) 2048) in HL2, HZ0 by flia. subst Z0.
eapply IH with (h := h) (x := zupd xx z carry) (z := (z + 1)%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii z) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hh Hzq] | Hr]]; [| right; left; split; [exact Hh | flia] | right; right; exact Hr].
apply (proj1 (inring_grow a1 z ii ltac:(flia) Hrs)) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a1 z ii); flia. }
all: try hlia Rzf.
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
all: try (replace (z + 1 + -1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; replace (z + 1 - 1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; reflexivity).
+
replace ((z + 1) mod 2048 =? a1)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; flia). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 = 2047)%Z).
{ clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
assert (Kin : inring a1 z km).
{ unfold inring. subst km. rewrite Zminus_mod_idemp_l. clear -Hrs Ra1 Rz. Z.div_mod_to_equations. flia. }
pose proof (X312 km) as Rt. pose proof (REL2 km ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read rsegs _ _ _ km _ _ XW (nth_error_wnth ws km ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(unfold wa; f_equal; flia)) as RD.
zs. rewrite (sx32_wval ws km (znth xx km) (eq_sym Et) Rt). set (t := znth xx km) in *.
zs.
assert (Rt1 : (0 <= Z.lor t 1 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t 1 31); flia. }
pose proof (u32arr_store_ok rsegs _ _ _ km _ XW ltac:(flia) ltac:(unfold wa; f_equal; flia)) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ km (Z_to_bv 64 (Z.lor t 1)) XW ltac:(flia)) as XW'. clear XW.
replace (A6 + 0)%Z with (q + -8312 + 4 * km)%Z by flia.
store_done'. rename XW' into XW.
zs.
eapply IH with (h := h) (x := zupd xx km (Z.lor t 1)) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii km) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia | exact Hr]. }
1:{ intros ii. destruct (Z.eq_dec ii km) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }
all: try hlia Rzf.
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
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_N2D4 := (@QHB6.Mq0.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1A8 := (@QHB6.Mq0.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_UK := (@QHB6.Mq0.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1C4 := (@QHB6.Mq0.S_U1C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
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

Hypothesis HS_N2D4 : S_N2D4.
Hypothesis HS_UK : S_UK.

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma th0_valU : znth th_list 0 = 10384593%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma mod_add2046 : forall u, ((u + 2046) mod 2048 = ((u - 1) mod 2048 - 1) mod 2048)%Z.
Proof. clear. intros u. rewrite Zminus_mod_idemp_l. rewrite <- (Z.mod_add (u - 1 - 1) 1 2048) by flia. f_equal. flia. Qed.

#[using="fc pre post fuelc f0 kmin0 c0 HS_N2D4"] Lemma L_UPX : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^20 <= rp <= 560)%Z -> (-2^20 <= e2 <= 0)%Z ->
up_K sign rp a z e2 x = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7204) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Rrp Re2 HK. unfold up_K in HK.
destruct (df_dn_loop FUEL_SCALE _) as [s'|] eqn:HL; [|discriminate HK].
stmt HS_N2D4. eapply (NX 2000%nat); try eassumption; try (cbn; flia).
all: try (intros E; specialize (Rzh E); cbn; flia).
all: try (intros E; specialize (Rw E); cbn; flia).
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1C4 : S_U1C4.
Proof.
unfold QHB6.Mq0.S_U1C4, QHB6.Mq0.SU1C4. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_up_loop_step in HL. unfold df_up_cond in HL. cbn [us_rp us_x us_a] in HL.
change (9 * LD_B1B_DIG)%Z with 36%Z in HL. rewrite th0_valU in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs.
assert (Hrs1 : (0 < (z - a) mod 2048)%Z) by (clear -Haz Ra Rz Rrs; Z.div_mod_to_equations; flia).

assert (GHEAD : forall m' ws' x' (h' w' : bool) (a' z' rp' : Z) (x6' x7' x16' x28' x29' x30' x31' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (zone h' w' a' z') -> X31 x' -> (0 <= a' < 2048)%Z -> (0 <= z' < 2048)%Z -> (h' = false -> z' <= 2047)%Z -> (w' = false -> 9 * a' + rp' <= 560)%Z -> a' <> z' ->
(-2^20 <= rp' <= 45)%Z ->
df_up_loop fo (mkUS rp' a' z' (e2 - 29) x') = Some s' ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp') x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a'))
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp') x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd70f4) fct None m' (seg_rom rsegs))).
{ intros m' ws' x' h' w' a' z' rp' x6' x7' x16' x28' x29' x30' x31' DI2 XR2 X312 Ra' Rz' Rzh' Rw' Haz' Rrp' HL'.
eapply (IH m' x1 x6' x7' x8 x9 x16' x20 x22 x24 x25 x26 x27 x28' x29' x30' x31' Ft fct j0 b96 ev ws' sign k c x' h' w' rp' a' z' (e2 - 29)%Z s');
[exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | flia | exact XR2 | exact X312 | flia | exact Rzh' | exact Rw' | exact Haz' | flia | flia | exact HL' | exact HK]. }
clear IH.

assert (GBODY : forall (x16' : word), (rp <= 36)%Z ->
match df_up_body (mkUS rp a z e2 x) with Some s'' => df_up_loop fo s'' | None => None end = Some s' ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7104) fct None m (seg_rom rsegs))).
{ intros x16' Rrp36 HB. clear HL HK. unfold df_up_body in HB. cbn [us_a us_z us_x us_rp us_e2] in HB. change MASK with 2047%Z in HB.
destruct (df_upk_loop FUEL_RING a _) as [[k1 carry1 z1 x1']|] eqn:HUK; [|discriminate HB].
unfold FUEL_RING in HUK. rewrite land2047 in HUK.

zs. zs. zs. zs. fixkg. rewrite mod_add2047.
stmt HS_UK.
eapply (NX 2050%nat) with (h := h) (w := w) (x := x) (s1 := mkUK k1 carry1 z1 x1');
[exact DI | exact FOK | exact FRM' | exact (conj LW' (conj LX REL)) | exact X31H | flia | flia | apply Z.mod_pos_bound; flia | | flia | exact HUK | ].
{ unfold inring. rewrite Zminus_mod_idemp_l. clear -Hrs1 Rrs Ra Rz. Z.div_mod_to_equations. flia. }
clear NX.
intros m' ws' x7' x18' x29' x30' x31' h' DI2 XR2 X312 Hk1 Rc1 Rz1 Hlow1 Haz1.
cbn [uk_x uk_z uk_k uk_carry] in DI2, XR2, X312, Hk1, Rc1, Rz1, Hlow1, Haz1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HUK Rrs Hrs1 LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
assert (Rzh1 : (h' = false -> z1 <= 2047)%Z) by (intros E; destruct (Hlow1 E) as [E0 R0]; specialize (Rzh E0); flia).
pose proof (Z.mod_pos_bound (z1 - a) 2048 ltac:(flia)) as Rrs2.
unfold nz in HB.

zs. fixw3. fixw. replace (e2 + -29)%Z with (e2 - 29)%Z by flia. zs. zs. brf K1.
-
replace (negb (carry1 =? 0)) with true in HB by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).
rewrite !land2047 in HB.
zs. zs. fixkg. replace (a + -1)%Z with (a - 1)%Z by flia.
pose proof (Z.mod_pos_bound (a - 1) 2048 ltac:(flia)) as Ra'. set (a' := ((a - 1) mod 2048)%Z) in *.
assert (FRONT : forall q0, (0 <= q0 < 2048)%Z -> inring a' z1 q0 -> q0 <> a' -> z1 <> a' -> inring a z1 q0).
{ intros q0 Hq H1 H2 H3. apply (inring_front a z1 q0); try flia; assumption. }
assert (FULL : z1 = a' -> forall q0, (0 <= q0 < 2048)%Z -> q0 <> a' -> inring a z1 q0).
{ intros E q0 Hq Hne. unfold inring. clear -E Hq Hne Ra Rz1 Ra' Haz1 Rrs2. subst a'. Z.div_mod_to_equations. nia. }
assert (Ea' : a' = (if (a =? 0)%Z then 2047%Z else (a - 1)%Z)).
{ subst a'. destruct (Z.eqb_spec a 0) as [->|Hne]; [reflexivity | rewrite Z.mod_small by flia; reflexivity]. }
set (w' := (w || (a =? 0)%Z)%bool).
assert (W1 : forall q0, (0 <= q0 < 2048)%Z -> w' = true -> (a' <= q0)%Z -> q0 <> a' -> w = true /\ (a <= q0)%Z).
{ intros q0 Hq. subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw' Hai Hne.
- exfalso. clear -Hq Hai Hne. flia.
- rewrite Bool.orb_false_r in Hw'. split; [exact Hw' | clear -Hai Hne; flia]. }
assert (W2 : w' = false -> (9 * a' + (rp + 9) <= 560)%Z).
{ subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw'; [rewrite Bool.orb_true_r in Hw'; discriminate Hw'|].
rewrite Bool.orb_false_r in Hw'. specialize (Rw Hw'). clear -Rw Na0 Ra. flia. }
clearbody w'. clear Ea'.
clearbody a'. clear Rrs2.

assert (TAIL : forall m2 ws2 x2 (h2 : bool) (z2 : Z) (x5' x6' x17' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws2 sign fR ->
xrel ws2 x2 (fun i => zone h2 w' a' z2 i /\ i <> a') -> X31 x2 -> (0 <= z2 < 2048)%Z -> (h2 = false -> z2 <= 2047)%Z -> a' <> z2 ->
df_up_loop fo (mkUS (rp + 9) a' z2 (e2 - 29) (zupd x2 a' carry1)) = Some s' ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 carry1) x17'
(Z_to_bv 64 z1) (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 z2) x29' x30' x31')
Ft (Z_to_bv 64 0xd71d8) fct None m2 (seg_rom rsegs))).
{ intros m2 ws2 x2 h2 z2 x5' x6' x17' DI3 XR3 X313 Rz2 Rzh2 Haz2 HL3.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC DI2 LW2 LX2 REL2 X312 HB.
pose proof DI3 as DI'. dest_dfinv DI'. destruct XR3 as (LW3 & LX3 & REL3).
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok rsegs _ _ _ a' _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ a' (Z_to_bv 64 carry1) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. zs. zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 9 + 0)%Z with (rp + 9)%Z by flia. zs.
eapply (GHEAD _ (upd ws2 (Z.to_nat a') (Z_to_bv 64 carry1)) (zupd x2 a' carry1) h2 w' a' z2 (rp + 9)%Z);
[mk_dfinv | | | flia | flia | exact Rzh2 | exact W2 | flia | flia | exact HL3].
* split; [rewrite upd_length; exact LW3|]. split; [rewrite zupd_length; exact LX3|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 a') as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL3; [flia|]. split; [exact Hr | exact Hne].
* intros q0. destruct (Z.eq_dec q0 a') as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X313]. }
zs. brf K2.
+
replace (a' =? z1) with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs.
eapply (TAIL m' ws' x1' h' z1); [exact DI2 | | exact X312 | flia | exact Rzh1 | flia | exact HB].
split; [exact LW2|]. split; [exact LX2|]. intros q0 Hq [Hr Hne]. apply REL2; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (W1 q0 Hq Hw' Hai Hne)]. apply (FRONT q0); try flia. exact Hr.
+
replace (a' =? z1) with true in HB by (symmetry; apply Z.eqb_eq; flia). cbv beta iota in HB.
pose proof (Z.mod_pos_bound (z1 - 1) 2048 ltac:(flia)) as Rz2. set (z2 := ((z1 - 1) mod 2048)%Z) in *.
zs. zs. zs. fix_idx. zs. fixkg. rewrite mod_add2046. fold z2.
pose proof (Z.mod_pos_bound (z2 - 1) 2048 ltac:(flia)) as Rz3. set (z3 := ((z2 - 1) mod 2048)%Z) in *.
assert (Hz2in : inring a z1 z2) by (apply (FULL ltac:(flia)); [flia | subst z2; clear -Rz1 Rz2 K2; Z.div_mod_to_equations; flia]).
assert (Hz3in : inring a z1 z3) by (apply (FULL ltac:(flia)); [flia | subst z3 z2; clear -Rz1 Rz2 Rz3 K2; Z.div_mod_to_equations; flia]).
assert (Hz23 : z3 <> z2) by (subst z3; clear -Rz2 Rz3; Z.div_mod_to_equations; flia).
assert (LOWz2 : z1 <> 0%Z -> z2 = (z1 - 1)%Z) by (intros; subst z2; apply Z.mod_small; flia).
assert (Hz21 : z2 <> z1) by (subst z2; clear -Rz1; Z.div_mod_to_equations; flia).
clearbody z2 z3.
pose proof (X312 z3) as Rt3. pose proof (REL2 z3 ltac:(flia) (or_introl Hz3in)) as Et3.
pose proof (X312 z2) as Rt2. pose proof (REL2 z2 ltac:(flia) (or_introl Hz2in)) as Et2.
zs. zs. fix_idx.
pose proof (u32arr_read rsegs _ _ _ z2 _ _ XW (nth_error_wnth ws' z2 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD2.
zs. rewrite (sx32_wval ws' z2 (znth x1' z2) (eq_sym Et2) Rt2). clear RD2.
pose proof (u32arr_read rsegs _ _ _ z3 _ _ XW (nth_error_wnth ws' z3 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD3.
zs. rewrite (sx32_wval ws' z3 (znth x1' z3) (eq_sym Et3) Rt3). clear RD3.
set (t3 := znth x1' z3) in *. set (t2 := znth x1' z2) in *.
zs.
assert (Rt23 : (0 <= Z.lor t3 t2 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t3 t2 31); flia. }
pose proof (u32arr_store_ok rsegs _ _ _ z3 _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ z3 (Z_to_bv 64 (Z.lor t3 t2)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (TAIL _ (upd ws' (Z.to_nat z3) (Z_to_bv 64 (Z.lor t3 t2))) (zupd x1' z3 (Z.lor t3 t2)) (if (z1 =? 0)%Z then true else h') z2);
[mk_dfinv | | | flia | | flia | exact HB].
* split; [rewrite !upd_length; exact LW2|]. split; [rewrite !zupd_length; exact LX2|].
intros q0 Hq [Hr Hne].
destruct (Z.eq_dec q0 z3) as [->|Hne3].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|]. left.
apply (FULL ltac:(flia) q0 Hq Hne).
* intros q0. destruct (Z.eq_dec q0 z3) as [->|Hne3]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312].
* destruct (Z.eqb_spec z1 0) as [Ez1|Hz1]; [intros E; discriminate E|]. intros E. specialize (Rzh1 E). specialize (LOWz2 Hz1). flia.
-
replace (negb (carry1 =? 0)) with false in HB by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply (GHEAD m' ws' x1' h' w a z1 rp); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | flia | flia | exact Rzh1 | exact Rw | flia | flia | exact HB]. }

zs. brs K0.
-
replace (rp <? 36) with true in HL by (symmetry; apply Z.ltb_lt; flia). cbn [orb] in HL.
eapply (GBODY x16); [flia | exact HL].
- replace (rp <? 36) with false in HL by (symmetry; apply Z.ltb_ge; flia). cbn [orb] in HL.
zs. brf K1; rewrite ?land_W64 in K1.
+
replace (rp =? 36) with false in HL by (symmetry; apply Z.eqb_neq; mlia). cbn [andb] in HL. injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
+ replace (rp =? 36) with true in HL by (symmetry; apply Z.eqb_eq; mlia). cbn [andb] in HL.

assert (Hain : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; exact Hrs1).
pose proof (X31H a) as Rta. pose proof (REL a ltac:(flia) (or_introl Hain)) as Eta.
pose proof (u32arr_read rsegs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RDa.
zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Eta) Rta). set (ta := znth x a) in *.
zs. brf K2.
*
replace (ta <? 10384593) with false in HL by (symmetry; apply Z.ltb_ge; flia). injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
* replace (ta <? 10384593) with true in HL by (symmetry; apply Z.ltb_lt; flia).
eapply (GBODY _); [flia | exact HL].
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1A8 : S_U1A8.
Proof.
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 0)%Z with rp by flia. zs.
pose proof L_U1C4 as NX. unfold QHB6.Mq0.S_U1C4, QHB6.Mq0.SU1C4 in NX. eapply NX; try eassumption; try flia.
Qed.

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
Local Notation S_UK := (@QHB6.Mq0.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma lor_b2z_zero : forall p q, Z.lor (Z.b2z p) (Z.b2z q) = 0%Z <-> (p = false /\ q = false).
Proof. clear. destruct p, q; cbn; split; intros H; try discriminate H; try (destruct H; congruence); auto. Qed.
#[using="Type"] Lemma lxor_pos_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((0 <? Z.lxor a b) = negb (a =? b))%Z.
Proof.
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne]; cbn.
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_lt. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.
#[using="Type"] Lemma lxor_lt1_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((Z.lxor a b <? 1) = (a =? b))%Z.
Proof.
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_ge. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.

#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_UK : S_UK.
Proof.
unfold QHB6.Mq0.S_UK. induction n as [|n IH]; intros m; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Kin Rc HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_upk_loop_step in HL. unfold df_upk_body in HL. cbn [uk_k uk_x uk_z uk_carry] in HL. change MASK with 2047%Z in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. unfold inring in Kin. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (or_introl Kin)) as Et.
pose proof (u32arr_read rsegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(clear -Rk; flia) ltac:(clear -Rk LW'; flia)) ltac:(clear -Rk; flia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite zx32_wval, <- Et. set (t := znth x k) in *. clear RD.
zs. zs.
set (tmp := (Z.shiftl t 29 + carry)%Z) in *.
assert (Rtmp : (0 <= tmp < 2^60 + 2^31)%Z) by (subst tmp; rewrite Z.shiftl_mul_pow2 by flia; flia).
assert (Etmp : u64 tmp = tmp) by (unfold u64; apply Z.mod_small; flia). rewrite !Etmp in HL.
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
rewrite !land2047 in HL. fold km in HL.

assert (G240 : forall (v carry' cand : Z) m' ws',
(0 <= v < 2^31)%Z -> (0 <= carry' < 2^31)%Z -> cand = (if v =? 0 then k else z)%Z ->
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
(forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel ws' (zupd x k v) (zone h' w a z')) ->
(let x' := zupd x k v in
let z' := (if (k =? km) && negb (k =? a) && (znth x' k =? 0) then k else z)%Z in
let s' := mkUK k carry' z' x' in
match (if (k =? a)%Z then inr s' else inl (mkUK ((k - 1) mod 2048) carry' z' x')) with
| inl s'' => df_upk_loop n a s''
| inr s'' => Some s''
end = Some s1) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 v) (Z_to_bv 64 cand) x31)
Ft (Z_to_bv 64 0xd7170) fct None m' (seg_rom rsegs))).
{ intros v carry' cand m' ws' Rv Rc' Hcand DI2 XRz HB. cbv zeta in HB.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'.
set (x' := zupd x k v) in *.
assert (X31' : X31 x').
{ intros ii. subst x'. destruct (Z.eq_dec ii k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
assert (Exk : znth x' k = v) by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity). rewrite Exk in HB.
assert (Hkm1 : k <> a -> inring a z ((k - 1) mod 2048) /\ inring a k ((k - 1) mod 2048)).
{ intros Hka. unfold inring. rewrite !Zminus_mod_idemp_l. clear -Kin Hka Ra Rz Rk Rrs Rks. Z.div_mod_to_equations. nia. }

zs. zs. zs. fixkg. replace (z + -1)%Z with (z - 1)%Z by flia. fold km. zs. zs. zs. zs. zs.
rewrite (lxor_pos_iff k km), (lxor_lt1_iff k a) by flia.

assert (LATCH : forall z' (x29' x30' : word),
z' = (if (k =? km) && negb (k =? a) && (v =? 0) then k else z)%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 km) x29' x30' (Z_to_bv 64 (Z.b2z (negb (k =? km)))))
Ft (Z_to_bv 64 0xd7110) fct None m' (seg_rom rsegs))).
{ intros z' x29' x30' Hz'. rewrite <- Hz' in HB.
assert (Rz' : (0 <= z' < 2048)%Z) by (rewrite Hz'; destruct (_ && _ && _); flia).
zs. zs. brf K4.
-
replace (k =? a)%Z with true in HB by (symmetry; apply Z.eqb_eq; flia). injection HB as <-.
assert (Ez' : z' = z) by (rewrite Hz'; replace (k =? a)%Z with true by (symmetry; apply Z.eqb_eq; flia); cbn [negb andb]; destruct (k =? km)%Z; reflexivity).
clear Hz'. subst z'.
replace (Z_to_bv 64 k) with (Z_to_bv 64 a) by (f_equal; flia).
eapply (CONT _ _ _ _ _ _ _ h); [mk_dfinv | cbn [uk_x uk_z]; apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | cbn; flia | cbn; flia | cbn; flia | cbn; intros E; split; [exact E | flia] | cbn; flia].
- replace (k =? a)%Z with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs. rewrite land2047, ?landW_mod2048. replace (k + -1)%Z with (k - 1)%Z by flia.
destruct (Hkm1 ltac:(flia)) as [Hin1 Hin2].
assert (Hz2 : z' = (if (k =? km) && (v =? 0) then k else z)%Z).
{ rewrite Hz'. replace (k =? a)%Z with false by (symmetry; apply Z.eqb_neq; flia). cbn [negb]. destruct (k =? km)%Z; reflexivity. }
clear Hz'.
replace ((k =? km) && negb false && (v =? 0))%Z with ((k =? km) && (v =? 0))%Z in HB by (destruct (k =? km)%Z; reflexivity).
destruct ((k =? km) && (v =? 0))%Z eqn:Ec; subst z'.
+
assert (Ekm : k = km) by (apply andb_prop in Ec; destruct Ec as [Ec _]; apply Z.eqb_eq in Ec; exact Ec).
destruct (Z.eq_dec z 0) as [Ez0|Hz0].
*
assert (Ek : k = 2047%Z) by (rewrite Ekm; subst km; rewrite Ez0; reflexivity).
eapply IH with (h := true) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[_ Hq] | Hq]]; [| left; flia | right; right; right; exact Hq]. right. left.
unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ez0 Ek. Z.div_mod_to_equations. nia.
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 _]. discriminate E2.
* assert (Ek : k = (z - 1)%Z) by (rewrite Ekm; subst km; apply Z.mod_small; flia).
eapply IH with (h := h) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[Hh Hq] | Hq]]; [ | | right; right; right; exact Hq].
{ right. left. unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ek. Z.div_mod_to_equations. nia. }
destruct (Z.eq_dec ii k) as [->|Hne]; [left; reflexivity | right; right; left; split; [exact Hh | flia]].
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 R2]. split; [exact E2 | flia].
+
eapply IH with (h := h) (z := z) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin1 | flia | exact HB | exact CONT]. }
zs. brf K3.
-
eapply LATCH. symmetry.
destruct (Z.eqb_spec k km); destruct (Z.eqb_spec k a); cbn [negb andb Z.b2z Z.lor] in K3 |- *; try reflexivity. exfalso. apply K3. reflexivity.
-
apply (proj1 (lor_b2z_zero _ _)) in K3. destruct K3 as [K3a K3b].
apply (proj1 (Bool.negb_false_iff _)) in K3a.
zs. zs.
eapply LATCH. rewrite K3a, K3b. cbn [negb andb]. exact Hcand. }
zs. zs. brf K2.
-
replace (1000000000 <? tmp)%Z with false in HL by (symmetry; apply Z.ltb_ge; flia).
rewrite (u32_id tmp) in HL by flia.
zs.
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 tmp) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 tmp)) (zupd x k tmp) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  eapply (G240 tmp 0%Z k); [flia | flia | replace (tmp =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 tmp 0%Z z); [flia | flia | replace (tmp =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
-
replace (1000000000 <? tmp)%Z with true in HL by (symmetry; apply Z.ltb_lt; flia).
assert (Rq : (0 <= tmp / 1000000000 < 2^31)%Z) by (split; [apply Z.div_pos; flia | apply Z.div_lt_upper_bound; flia]).
pose proof (Z.mod_pos_bound tmp 1000000000 ltac:(flia)) as Rr.
rewrite (u32_id (tmp / 1000000000)) in HL by flia. rewrite (u32_id (tmp mod 1000000000)) in HL by flia.
zs. zs. zs. showall.
rewrite (magic_div_1e9_reg tmp) by flia.
zs. zs.
replace (tmp - tmp / 1000000000 * 1000000000)%Z with (tmp mod 1000000000)%Z by (rewrite Zmod_eq_full by flia; flia).
pose proof (u32arr_store_ok rsegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ k (Z_to_bv 64 (tmp mod 1000000000)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 (tmp mod 1000000000))) (zupd x k (tmp mod 1000000000)) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z z); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z k); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A5C4 := (@QHB6.Mq3.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A568 := (@QHB6.Mq3.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@QHB6.Mq3.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A5C4 : S_A5C4.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SPLO SPF SPT SG1 Q1 HS_A5C4"] Lemma L_A578 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 t : Z) (f : nat) sres,
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 -> (0 <= t < 2^31)%Z ->
df_asm_loop f a (mkAS 1 (f128_add (f128_mul C_1E9 zero0) (f128_of_u32 t)) z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 t) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9b6c) fct None m (seg_rom usegs)).
Proof.
intros until sres. intros DI RJ Hk FOK FRM' Hsg He2 Ra AI Rt HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. callx (eapply floatunsitf_callv with (u := t); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 t) in *. pose proof (lo64_range XF) as R1l. pose proof (hi64_range XF) as R1h.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := C_1E9) (Y := zero0); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul C_1E9 zero0) in *. pose proof (lo64_range P) as R2l. pose proof (hi64_range P) as R2h.
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := P) (Y := XF); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y' := f128_add P XF) in *. pose proof (lo64_range Y') as R3l. pose proof (hi64_range Y') as R3h.
zs. zs.
stmt HS_A5C4. eapply NX; try eassumption; try lia; try mk_dfinv.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A568 : S_A568.
Proof.
intros m; intros until xa. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Naz Hxa HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (X31H a) as Rt. rewrite <- Hxa in Rt.
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). rewrite <- Hxa in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.
assert (Hza : ((z - a) mod 2048 <> 0)%Z).
{ intros E. apply Naz. symmetry. apply (mod_eq_idx a a z); try lia. all: rewrite Z.sub_diag, E; reflexivity. }
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW' | split; [exact LX | exact REL]] |]. split; [exact X31H|]. split; [lia|]. split; [hlia Rz4|]. split; [lia|]. exact Raw.
Qed.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A5C4"] Lemma L_A534 : S_A534.
Proof.
intros m; intros until S1. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI Eaz HS1 HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
unfold fin_K0 in HK. rewrite (df_final_split 53 (-1074) sign 1024 zero0) in HK. fold zero0 in HK.
destruct (df_asm_loop 5 a _) as [sres|] eqn:HL; [|discriminate HK].
rewrite df_asm_loop_step in HL. cbn [as_i] in HL. change (0 <? LD_B1B_DIG)%Z with true in HL.
unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
rewrite Z.add_0_r, land2047, (Z.mod_small a 2048) in HL by lia.
replace (a =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). rewrite !land2047 in HL.
subst a.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
zs. zs. zs. zs. zs. subst S1. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Nz].
-
assert (Hw : w = true) by (destruct w; [reflexivity | specialize (Raw eq_refl); exfalso; lia]).
subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL |- *. change (negb (0 =? 0)) with false in HL. cbv beta iota in HL.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (q + -8312)%Z) by (f_equal; lia).
zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : rw_cells _ mm (q + -8416)%Z _ |- _ =>
apply (cb44_merge _ _ [_;_;_;_;_;_;_;_;_;_;_;_]) in H; cbn [app] in H end end.
pose proof (X31H 2047%Z) as Rt. pose proof (REL 2047%Z ltac:(lia) ltac:(right; right; split; [exact Hw | lia])) as Et.
pose proof (u32arr_read usegs _ _ _ 2047%Z _ _ XW (nth_error_wnth ws 2047%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs. rewrite (sx32_wval ws 2047%Z (znth x 2047%Z) (eq_sym Et) Rt).
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := false) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [exact X31H | split; [lia | split; [lia| split; [cbn; lia | exact Raw]]]]].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i0 Ri0 Hq. destruct Hq as [Hq | [[Hq _] | Hq]]; [| discriminate Hq | right; right; exact Hq].
destruct (Z.eq_dec i0 2047) as [->|Hne]; [right; right; split; [exact Hw | lia] | left].
unfold inring in Hq |- *. clear -Hq Hne Ri0. Z.div_mod_to_equations. lia.
-
rewrite (Z.mod_small (z + 1) 2048) in HL |- * by lia.
replace (negb (z + 1 =? 0)) with true in HL by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
replace (z + 1 - 1)%Z with z in HL by lia. cbv beta iota in HL.
rewrite znth_zupd_eq in HL by (unfold zlength; lia).
pose proof (u32arr_store_ok usegs _ _ _ z _ XW ltac:(lia) eq_refl) as SOK.
let v := getreg 9%Z in replace v with (Z_to_bv 64 (XA + 4 * z + 4)%Z) by (f_equal; lia).
zs.
pose proof (u32arr_write usegs _ _ _ z (Z_to_bv 64 0) XW ltac:(lia)) as XW'. clear XW.
replace (q + -8312 + 4 * z + 4 + -4)%Z with (q + -8312 + 4 * z)%Z by lia.
store_done. rename XW' into XW.
pose proof (u32arr_read usegs _ _ _ z _ _ XW (nth_error_wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z ltac:(lia) ltac:(rewrite upd_length; lia)) ltac:(lia) eq_refl) as RD.
zs. fix_idx. zs.
replace (sx32 (wnth (upd ws (Z.to_nat z) (Z_to_bv 64 0)) z)) with (Z_to_bv 64 0).
2:{ symmetry. apply (sx32_wval _ z 0); [rewrite wval_upd_same by lia; reflexivity | lia]. }
zs. zs.
destruct sres as [i' y' z' x'].
eapply L_A578 with (h := h) (w := w); try eassumption; try lia; try mk_dfinv.
split; [|split; [| split; [lia | split; [hlia Rz4| split; [| exact Raw]]]]].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros i0 Hi0 Hr. destruct (Z.eq_dec i0 z) as [->|Hne].
* rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. reflexivity.
* rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|].
destruct Hr as [Hr | [[Hh Hzi] | Hr]]; [| right; left; split; [exact Hh | lia] | right; right; exact Hr].
apply (proj1 (inring_grow z z i0 ltac:(lia) ltac:(rewrite Z.sub_diag; cbn; lia))) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx z z i0); lia.
+ intros i0. destruct (Z.eq_dec i0 z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H].
+ replace (z + 1 - z)%Z with 1%Z by lia. reflexivity.
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
Notation XA := (q + -8312)%Z.

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_A62C := (@QHB6.Mq3.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A5C4 := (@QHB6.Mq3.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_A62C : S_A62C.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_A62C"] Lemma L_A5C4 : S_A5C4.
Proof.
intros m; intros until sres. intros _ DI RJ Hk FOK FRM' Hsg He2 Ra AI HL Hf HK. pose proof DI as DI0. dest_dfinv DI.
destruct AI as (XR & X31H & Rz & Rz4 & Hrs & Raw). destruct XR as (LW' & LX & REL).
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.
destruct f as [|f]; [lia|]. rewrite df_asm_loop_step in HL. cbn [as_i] in HL.
change (1 <? LD_B1B_DIG)%Z with true in HL. unfold df_asm_body in HL. cbn [as_i as_y as_z as_x] in HL. change MASK with 2047%Z in HL.
pose proof (land_mask_range (a + 1) 2047 ltac:(lia)) as Rk. set (kk := Z.land (a + 1) 2047) in *.
assert (Ek : kk = ((a + 1) mod 2048)%Z) by (subst kk; apply land2047).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)) as Rrs.

assert (G648 : forall m' ws' x' z' (h' : bool) b96' (x11' x12' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' x' (zone h' w a z') -> X31 x' -> inring a z' kk -> (0 <= z' < 2048)%Z -> (h' = false -> z' + 2 <= 2052)%Z -> (2 <= (z' - a) mod 2048)%Z ->
df_asm_loop f a (mkAS 2 (f128_add (f128_mul C_1E9 Y) (f128_of_u32 (znth x' kk))) z' x') = Some sres ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) x9 (Z_to_bv 64 kk) x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9bdc) fct None m' (seg_rom usegs))).
{ intros m' ws' x' z' h' b96' x11' x12' DI2 XR2 X312 Kin Rz' Rz4' Hrs' HL'.
clear HL MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
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
stmt HS_A62C. eapply NX; try eassumption; try lia; try mk_dfinv.
split; [split; [exact LW2 | split; [exact LX2 | exact REL2]] |]. split; [exact X312|]. split; [lia|]. split; [hlia Rz4'|]. split; [lia|]. exact Raw. }
zs. zs. replace (1 + a)%Z with (a + 1)%Z by lia. replace (a + 1 + 0)%Z with (a + 1)%Z by lia. fold kk. zs. zs. brf K1.
-
replace (kk =? z)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia).
destruct (inring_plus a z 1 ltac:(lia) ltac:(lia) Hrs ltac:(lia)) as [Kin Hrs'].
eapply (G648 _ ws x z h); [mk_dfinv | split; [exact LW' | split; [exact LX | exact REL]] | exact X31H | exact Kin | lia | hlia Rz4 | exact Hrs' | exact HL].
-
replace (kk =? z)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia).
pose proof (inring_hit a z 1 ltac:(lia) ltac:(lia) ltac:(lia)) as Hrs0.
rewrite !land2047 in HL.
assert (Ez1 : ((z + 1) mod 2048 = (a + 2) mod 2048)%Z).
{ rewrite <- K1, Ek. rewrite Zplus_mod_idemp_l. f_equal. lia. }
zs. replace (Z.land (a + 2) 2047) with ((z + 1) mod 2048)%Z by (rewrite land2047; exact Ez1).
zs. zs. zs.
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_N2D4 := (@QHB6.Mq3.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1A8 := (@QHB6.Mq3.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_UK := (@QHB6.Mq3.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1C4 := (@QHB6.Mq3.S_U1C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
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

Hypothesis HS_N2D4 : S_N2D4.
Hypothesis HS_UK : S_UK.

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma th0_valU : znth th_list 0 = 10384593%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma mod_add2046 : forall u, ((u + 2046) mod 2048 = ((u - 1) mod 2048 - 1) mod 2048)%Z.
Proof. clear. intros u. rewrite Zminus_mod_idemp_l. rewrite <- (Z.mod_add (u - 1 - 1) 1 2048) by flia. f_equal. flia. Qed.

#[using="fc pre post fuelc f0 kmin0 c0 HS_N2D4"] Lemma L_UPX : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^20 <= rp <= 560)%Z -> (-2^20 <= e2 <= 0)%Z ->
up_K sign rp a z e2 x = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd98c8) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Rrp Re2 HK. unfold up_K in HK.
destruct (df_dn_loop FUEL_SCALE _) as [s'|] eqn:HL; [|discriminate HK].
stmt HS_N2D4. eapply (NX 2000%nat); try eassumption; try (cbn; flia).
all: try (intros E; specialize (Rzh E); cbn; flia).
all: try (intros E; specialize (Rw E); cbn; flia).
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1C4 : S_U1C4.
Proof.
unfold QHB6.Mq3.S_U1C4, QHB6.Mq3.SU1C4. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_up_loop_step in HL. unfold df_up_cond in HL. cbn [us_rp us_x us_a] in HL.
change (9 * LD_B1B_DIG)%Z with 36%Z in HL. rewrite th0_valU in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs.
assert (Hrs1 : (0 < (z - a) mod 2048)%Z) by (clear -Haz Ra Rz Rrs; Z.div_mod_to_equations; flia).

assert (GHEAD : forall m' ws' x' (h' w' : bool) (a' z' rp' : Z) (x6' x7' x16' x28' x29' x30' x31' : word),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' x' (zone h' w' a' z') -> X31 x' -> (0 <= a' < 2048)%Z -> (0 <= z' < 2048)%Z -> (h' = false -> z' <= 2047)%Z -> (w' = false -> 9 * a' + rp' <= 560)%Z -> a' <> z' ->
(-2^20 <= rp' <= 45)%Z ->
df_up_loop fo (mkUS rp' a' z' (e2 - 29) x') = Some s' ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp') x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a'))
(Z_to_bv 64 z') (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp') x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd97b8) fct None m' (seg_rom usegs))).
{ intros m' ws' x' h' w' a' z' rp' x6' x7' x16' x28' x29' x30' x31' DI2 XR2 X312 Ra' Rz' Rzh' Rw' Haz' Rrp' HL'.
eapply (IH m' x1 x6' x7' x8 x9 x16' x20 x22 x24 x25 x26 x27 x28' x29' x30' x31' Ft fct j0 b96 ev ws' sign k c x' h' w' rp' a' z' (e2 - 29)%Z s');
[exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | flia | exact XR2 | exact X312 | flia | exact Rzh' | exact Rw' | exact Haz' | flia | flia | exact HL' | exact HK]. }
clear IH.

assert (GBODY : forall (x16' : word), (rp <= 36)%Z ->
match df_up_body (mkUS rp a z e2 x) with Some s'' => df_up_loop fo s'' | None => None end = Some s' ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd97c8) fct None m (seg_rom usegs))).
{ intros x16' Rrp36 HB. clear HL HK. unfold df_up_body in HB. cbn [us_a us_z us_x us_rp us_e2] in HB. change MASK with 2047%Z in HB.
destruct (df_upk_loop FUEL_RING a _) as [[k1 carry1 z1 x1']|] eqn:HUK; [|discriminate HB].
unfold FUEL_RING in HUK. rewrite land2047 in HUK.

zs. zs. zs. zs. fixkg. rewrite mod_add2047.
stmt HS_UK.
eapply (NX 2050%nat) with (h := h) (w := w) (x := x) (s1 := mkUK k1 carry1 z1 x1');
[exact DI | exact FOK | exact FRM' | exact (conj LW' (conj LX REL)) | exact X31H | flia | flia | apply Z.mod_pos_bound; flia | | flia | exact HUK | ].
{ unfold inring. rewrite Zminus_mod_idemp_l. clear -Hrs1 Rrs Ra Rz. Z.div_mod_to_equations. flia. }
clear NX.
intros m' ws' x7' x18' x29' x30' x31' h' DI2 XR2 X312 Hk1 Rc1 Rz1 Hlow1 Haz1.
cbn [uk_x uk_z uk_k uk_carry] in DI2, XR2, X312, Hk1, Rc1, Rz1, Hlow1, Haz1 |- *. subst k1.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HUK Rrs Hrs1 LW' LX REL X31H.
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
assert (Rzh1 : (h' = false -> z1 <= 2047)%Z) by (intros E; destruct (Hlow1 E) as [E0 R0]; specialize (Rzh E0); flia).
pose proof (Z.mod_pos_bound (z1 - a) 2048 ltac:(flia)) as Rrs2.
unfold nz in HB.

zs. fixw3. fixw. replace (e2 + -29)%Z with (e2 - 29)%Z by flia. zs. zs. brf K1.
-
replace (negb (carry1 =? 0)) with true in HB by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).
rewrite !land2047 in HB.
zs. zs. fixkg. replace (a + -1)%Z with (a - 1)%Z by flia.
pose proof (Z.mod_pos_bound (a - 1) 2048 ltac:(flia)) as Ra'. set (a' := ((a - 1) mod 2048)%Z) in *.
assert (FRONT : forall q0, (0 <= q0 < 2048)%Z -> inring a' z1 q0 -> q0 <> a' -> z1 <> a' -> inring a z1 q0).
{ intros q0 Hq H1 H2 H3. apply (inring_front a z1 q0); try flia; assumption. }
assert (FULL : z1 = a' -> forall q0, (0 <= q0 < 2048)%Z -> q0 <> a' -> inring a z1 q0).
{ intros E q0 Hq Hne. unfold inring. clear -E Hq Hne Ra Rz1 Ra' Haz1 Rrs2. subst a'. Z.div_mod_to_equations. nia. }
assert (Ea' : a' = (if (a =? 0)%Z then 2047%Z else (a - 1)%Z)).
{ subst a'. destruct (Z.eqb_spec a 0) as [->|Hne]; [reflexivity | rewrite Z.mod_small by flia; reflexivity]. }
set (w' := (w || (a =? 0)%Z)%bool).
assert (W1 : forall q0, (0 <= q0 < 2048)%Z -> w' = true -> (a' <= q0)%Z -> q0 <> a' -> w = true /\ (a <= q0)%Z).
{ intros q0 Hq. subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw' Hai Hne.
- exfalso. clear -Hq Hai Hne. flia.
- rewrite Bool.orb_false_r in Hw'. split; [exact Hw' | clear -Hai Hne; flia]. }
assert (W2 : w' = false -> (9 * a' + (rp + 9) <= 560)%Z).
{ subst w'. rewrite Ea'. destruct (Z.eqb_spec a 0) as [Ea0|Na0]; intros Hw'; [rewrite Bool.orb_true_r in Hw'; discriminate Hw'|].
rewrite Bool.orb_false_r in Hw'. specialize (Rw Hw'). clear -Rw Na0 Ra. flia. }
clearbody w'. clear Ea'.
clearbody a'. clear Rrs2.

assert (TAIL : forall m2 ws2 x2 (h2 : bool) (z2 : Z) (x5' x6' x17' : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws2 sign fR ->
xrel ws2 x2 (fun i => zone h2 w' a' z2 i /\ i <> a') -> X31 x2 -> (0 <= z2 < 2048)%Z -> (h2 = false -> z2 <= 2047)%Z -> a' <> z2 ->
df_up_loop fo (mkUS (rp + 9) a' z2 (e2 - 29) (zupd x2 a' carry1)) = Some s' ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 carry1) x17'
(Z_to_bv 64 z1) (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 z2) x29' x30' x31')
Ft (Z_to_bv 64 0xd989c) fct None m2 (seg_rom usegs))).
{ intros m2 ws2 x2 h2 z2 x5' x6' x17' DI3 XR3 X313 Rz2 Rzh2 Haz2 HL3.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC DI2 LW2 LX2 REL2 X312 HB.
pose proof DI3 as DI'. dest_dfinv DI'. destruct XR3 as (LW3 & LX3 & REL3).
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok usegs _ _ _ a' _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ a' (Z_to_bv 64 carry1) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. zs. zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 9 + 0)%Z with (rp + 9)%Z by flia. zs.
eapply (GHEAD _ (upd ws2 (Z.to_nat a') (Z_to_bv 64 carry1)) (zupd x2 a' carry1) h2 w' a' z2 (rp + 9)%Z);
[mk_dfinv | | | flia | flia | exact Rzh2 | exact W2 | flia | flia | exact HL3].
* split; [rewrite upd_length; exact LW3|]. split; [rewrite zupd_length; exact LX3|].
intros q0 Hq Hr. destruct (Z.eq_dec q0 a') as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL3; [flia|]. split; [exact Hr | exact Hne].
* intros q0. destruct (Z.eq_dec q0 a') as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X313]. }
zs. brf K2.
+
replace (a' =? z1) with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs.
eapply (TAIL m' ws' x1' h' z1); [exact DI2 | | exact X312 | flia | exact Rzh1 | flia | exact HB].
split; [exact LW2|]. split; [exact LX2|]. intros q0 Hq [Hr Hne]. apply REL2; [flia|].
destruct Hr as [Hr | [Hr | [Hw' Hai]]]; [left | right; left; exact Hr | right; right; exact (W1 q0 Hq Hw' Hai Hne)]. apply (FRONT q0); try flia. exact Hr.
+
replace (a' =? z1) with true in HB by (symmetry; apply Z.eqb_eq; flia). cbv beta iota in HB.
pose proof (Z.mod_pos_bound (z1 - 1) 2048 ltac:(flia)) as Rz2. set (z2 := ((z1 - 1) mod 2048)%Z) in *.
zs. zs. zs. fix_idx. zs. fixkg. rewrite mod_add2046. fold z2.
pose proof (Z.mod_pos_bound (z2 - 1) 2048 ltac:(flia)) as Rz3. set (z3 := ((z2 - 1) mod 2048)%Z) in *.
assert (Hz2in : inring a z1 z2) by (apply (FULL ltac:(flia)); [flia | subst z2; clear -Rz1 Rz2 K2; Z.div_mod_to_equations; flia]).
assert (Hz3in : inring a z1 z3) by (apply (FULL ltac:(flia)); [flia | subst z3 z2; clear -Rz1 Rz2 Rz3 K2; Z.div_mod_to_equations; flia]).
assert (Hz23 : z3 <> z2) by (subst z3; clear -Rz2 Rz3; Z.div_mod_to_equations; flia).
assert (LOWz2 : z1 <> 0%Z -> z2 = (z1 - 1)%Z) by (intros; subst z2; apply Z.mod_small; flia).
assert (Hz21 : z2 <> z1) by (subst z2; clear -Rz1; Z.div_mod_to_equations; flia).
clearbody z2 z3.
pose proof (X312 z3) as Rt3. pose proof (REL2 z3 ltac:(flia) (or_introl Hz3in)) as Et3.
pose proof (X312 z2) as Rt2. pose proof (REL2 z2 ltac:(flia) (or_introl Hz2in)) as Et2.
zs. zs. fix_idx.
pose proof (u32arr_read usegs _ _ _ z2 _ _ XW (nth_error_wnth ws' z2 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD2.
zs. rewrite (sx32_wval ws' z2 (znth x1' z2) (eq_sym Et2) Rt2). clear RD2.
pose proof (u32arr_read usegs _ _ _ z3 _ _ XW (nth_error_wnth ws' z3 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD3.
zs. rewrite (sx32_wval ws' z3 (znth x1' z3) (eq_sym Et3) Rt3). clear RD3.
set (t3 := znth x1' z3) in *. set (t2 := znth x1' z2) in *.
zs.
assert (Rt23 : (0 <= Z.lor t3 t2 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t3 t2 31); flia. }
pose proof (u32arr_store_ok usegs _ _ _ z3 _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ z3 (Z_to_bv 64 (Z.lor t3 t2)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
eapply (TAIL _ (upd ws' (Z.to_nat z3) (Z_to_bv 64 (Z.lor t3 t2))) (zupd x1' z3 (Z.lor t3 t2)) (if (z1 =? 0)%Z then true else h') z2);
[mk_dfinv | | | flia | | flia | exact HB].
* split; [rewrite !upd_length; exact LW2|]. split; [rewrite !zupd_length; exact LX2|].
intros q0 Hq [Hr Hne].
destruct (Z.eq_dec q0 z3) as [->|Hne3].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|]. left.
apply (FULL ltac:(flia) q0 Hq Hne).
* intros q0. destruct (Z.eq_dec q0 z3) as [->|Hne3]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312].
* destruct (Z.eqb_spec z1 0) as [Ez1|Hz1]; [intros E; discriminate E|]. intros E. specialize (Rzh1 E). specialize (LOWz2 Hz1). flia.
-
replace (negb (carry1 =? 0)) with false in HB by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply (GHEAD m' ws' x1' h' w a z1 rp); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | flia | flia | exact Rzh1 | exact Rw | flia | flia | exact HB]. }

zs. brs K0.
-
replace (rp <? 36) with true in HL by (symmetry; apply Z.ltb_lt; flia). cbn [orb] in HL.
eapply (GBODY x16); [flia | exact HL].
- replace (rp <? 36) with false in HL by (symmetry; apply Z.ltb_ge; flia). cbn [orb] in HL.
zs. brf K1; rewrite ?land_W64 in K1.
+
replace (rp =? 36) with false in HL by (symmetry; apply Z.eqb_neq; mlia). cbn [andb] in HL. injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
+ replace (rp =? 36) with true in HL by (symmetry; apply Z.eqb_eq; mlia). cbn [andb] in HL.

assert (Hain : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; exact Hrs1).
pose proof (X31H a) as Rta. pose proof (REL a ltac:(flia) (or_introl Hain)) as Eta.
pose proof (u32arr_read usegs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RDa.
zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Eta) Rta). set (ta := znth x a) in *.
zs. brf K2.
*
replace (ta <? 10384593) with false in HL by (symmetry; apply Z.ltb_ge; flia). injection HL as <-.
cbn [us_rp us_a us_z us_e2 us_x] in HK.
eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | exact Rw | flia | flia | exact HK].
* replace (ta <? 10384593) with true in HL by (symmetry; apply Z.ltb_lt; flia).
eapply (GBODY _); [flia | exact HL].
Qed.

#[using="T1 SPF SPF2 SPT SG1 HS_N2D4 HS_UK"] Lemma L_U1A8 : S_U1A8.
Proof.
intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rw Haz Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 0)%Z with rp by flia. zs.
pose proof L_U1C4 as NX. unfold QHB6.Mq3.S_U1C4, QHB6.Mq3.SU1C4 in NX. eapply NX; try eassumption; try flia.
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
Local Notation S_UK := (@QHB6.Mq3.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
#[using="Type"] Lemma lor_b2z_zero : forall p q, Z.lor (Z.b2z p) (Z.b2z q) = 0%Z <-> (p = false /\ q = false).
Proof. clear. destruct p, q; cbn; split; intros H; try discriminate H; try (destruct H; congruence); auto. Qed.
#[using="Type"] Lemma lxor_pos_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((0 <? Z.lxor a b) = negb (a =? b))%Z.
Proof.
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne]; cbn.
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_lt. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.
#[using="Type"] Lemma lxor_lt1_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((Z.lxor a b <? 1) = (a =? b))%Z.
Proof.
clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne].
- rewrite Z.lxor_nilpotent. reflexivity.
- apply Z.ltb_ge. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
Qed.

#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_UK : S_UK.
Proof.
unfold QHB6.Mq3.S_UK. induction n as [|n IH]; intros m; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Kin Rc HL CONT; [discriminate HL|].
pose proof DI as DI'. dest_dfinv DI'.
destruct XR as (LW' & LX & REL).
rewrite df_upk_loop_step in HL. unfold df_upk_body in HL. cbn [uk_k uk_x uk_z uk_carry] in HL. change MASK with 2047%Z in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. unfold inring in Kin. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (or_introl Kin)) as Et.
pose proof (u32arr_read usegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(clear -Rk; flia) ltac:(clear -Rk LW'; flia)) ltac:(clear -Rk; flia) eq_refl) as RD.
zs. zs. fix_idx. zs. rewrite zx32_wval, <- Et. set (t := znth x k) in *. clear RD.
zs. zs.
set (tmp := (Z.shiftl t 29 + carry)%Z) in *.
assert (Rtmp : (0 <= tmp < 2^60 + 2^31)%Z) by (subst tmp; rewrite Z.shiftl_mul_pow2 by flia; flia).
assert (Etmp : u64 tmp = tmp) by (unfold u64; apply Z.mod_small; flia). rewrite !Etmp in HL.
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
rewrite !land2047 in HL. fold km in HL.

assert (G240 : forall (v carry' cand : Z) m' ws',
(0 <= v < 2^31)%Z -> (0 <= carry' < 2^31)%Z -> cand = (if v =? 0 then k else z)%Z ->
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
(forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel ws' (zupd x k v) (zone h' w a z')) ->
(let x' := zupd x k v in
let z' := (if (k =? km) && negb (k =? a) && (znth x' k =? 0) then k else z)%Z in
let s' := mkUK k carry' z' x' in
match (if (k =? a)%Z then inr s' else inl (mkUK ((k - 1) mod 2048) carry' z' x')) with
| inl s'' => df_upk_loop n a s''
| inr s'' => Some s''
end = Some s1) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 v) (Z_to_bv 64 cand) x31)
Ft (Z_to_bv 64 0xd9834) fct None m' (seg_rom usegs))).
{ intros v carry' cand m' ws' Rv Rc' Hcand DI2 XRz HB. cbv zeta in HB.
clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
pose proof DI2 as DI2'. dest_dfinv DI2'.
set (x' := zupd x k v) in *.
assert (X31' : X31 x').
{ intros ii. subst x'. destruct (Z.eq_dec ii k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
assert (Exk : znth x' k = v) by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity). rewrite Exk in HB.
assert (Hkm1 : k <> a -> inring a z ((k - 1) mod 2048) /\ inring a k ((k - 1) mod 2048)).
{ intros Hka. unfold inring. rewrite !Zminus_mod_idemp_l. clear -Kin Hka Ra Rz Rk Rrs Rks. Z.div_mod_to_equations. nia. }

zs. zs. zs. fixkg. replace (z + -1)%Z with (z - 1)%Z by flia. fold km. zs. zs. zs. zs. zs.
rewrite (lxor_pos_iff k km), (lxor_lt1_iff k a) by flia.

assert (LATCH : forall z' (x29' x30' : word),
z' = (if (k =? km) && negb (k =? a) && (v =? 0) then k else z)%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
(Z_to_bv 64 z') (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 km) x29' x30' (Z_to_bv 64 (Z.b2z (negb (k =? km)))))
Ft (Z_to_bv 64 0xd97d4) fct None m' (seg_rom usegs))).
{ intros z' x29' x30' Hz'. rewrite <- Hz' in HB.
assert (Rz' : (0 <= z' < 2048)%Z) by (rewrite Hz'; destruct (_ && _ && _); flia).
zs. zs. brf K4.
-
replace (k =? a)%Z with true in HB by (symmetry; apply Z.eqb_eq; flia). injection HB as <-.
assert (Ez' : z' = z) by (rewrite Hz'; replace (k =? a)%Z with true by (symmetry; apply Z.eqb_eq; flia); cbn [negb andb]; destruct (k =? km)%Z; reflexivity).
clear Hz'. subst z'.
replace (Z_to_bv 64 k) with (Z_to_bv 64 a) by (f_equal; flia).
eapply (CONT _ _ _ _ _ _ _ h); [mk_dfinv | cbn [uk_x uk_z]; apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | cbn; flia | cbn; flia | cbn; flia | cbn; intros E; split; [exact E | flia] | cbn; flia].
- replace (k =? a)%Z with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
zs. rewrite land2047, ?landW_mod2048. replace (k + -1)%Z with (k - 1)%Z by flia.
destruct (Hkm1 ltac:(flia)) as [Hin1 Hin2].
assert (Hz2 : z' = (if (k =? km) && (v =? 0) then k else z)%Z).
{ rewrite Hz'. replace (k =? a)%Z with false by (symmetry; apply Z.eqb_neq; flia). cbn [negb]. destruct (k =? km)%Z; reflexivity. }
clear Hz'.
replace ((k =? km) && negb false && (v =? 0))%Z with ((k =? km) && (v =? 0))%Z in HB by (destruct (k =? km)%Z; reflexivity).
destruct ((k =? km) && (v =? 0))%Z eqn:Ec; subst z'.
+
assert (Ekm : k = km) by (apply andb_prop in Ec; destruct Ec as [Ec _]; apply Z.eqb_eq in Ec; exact Ec).
destruct (Z.eq_dec z 0) as [Ez0|Hz0].
*
assert (Ek : k = 2047%Z) by (rewrite Ekm; subst km; rewrite Ez0; reflexivity).
eapply IH with (h := true) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[_ Hq] | Hq]]; [| left; flia | right; right; right; exact Hq]. right. left.
unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ez0 Ek. Z.div_mod_to_equations. nia.
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 _]. discriminate E2.
* assert (Ek : k = (z - 1)%Z) by (rewrite Ekm; subst km; apply Z.mod_small; flia).
eapply IH with (h := h) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
-- destruct Hq as [Hq | [[Hh Hq] | Hq]]; [ | | right; right; right; exact Hq].
{ right. left. unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ek. Z.div_mod_to_equations. nia. }
destruct (Z.eq_dec ii k) as [->|Hne]; [left; reflexivity | right; right; left; split; [exact Hh | flia]].
-- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
intros E. destruct (Hlow3 E) as [E2 R2]. split; [exact E2 | flia].
+
eapply IH with (h := h) (z := z) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin1 | flia | exact HB | exact CONT]. }
zs. brf K3.
-
eapply LATCH. symmetry.
destruct (Z.eqb_spec k km); destruct (Z.eqb_spec k a); cbn [negb andb Z.b2z Z.lor] in K3 |- *; try reflexivity. exfalso. apply K3. reflexivity.
-
apply (proj1 (lor_b2z_zero _ _)) in K3. destruct K3 as [K3a K3b].
apply (proj1 (Bool.negb_false_iff _)) in K3a.
zs. zs.
eapply LATCH. rewrite K3a, K3b. cbn [negb andb]. exact Hcand. }
zs. zs. brf K2.
-
replace (1000000000 <? tmp)%Z with false in HL by (symmetry; apply Z.ltb_ge; flia).
rewrite (u32_id tmp) in HL by flia.
zs.
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 tmp) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 tmp)) (zupd x k tmp) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  eapply (G240 tmp 0%Z k); [flia | flia | replace (tmp =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 tmp 0%Z z); [flia | flia | replace (tmp =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
-
replace (1000000000 <? tmp)%Z with true in HL by (symmetry; apply Z.ltb_lt; flia).
assert (Rq : (0 <= tmp / 1000000000 < 2^31)%Z) by (split; [apply Z.div_pos; flia | apply Z.div_lt_upper_bound; flia]).
pose proof (Z.mod_pos_bound tmp 1000000000 ltac:(flia)) as Rr.
rewrite (u32_id (tmp / 1000000000)) in HL by flia. rewrite (u32_id (tmp mod 1000000000)) in HL by flia.
zs. zs. zs. showall.
rewrite (magic_div_1e9_reg tmp) by flia.
zs. zs.
replace (tmp - tmp / 1000000000 * 1000000000)%Z with (tmp mod 1000000000)%Z by (rewrite Zmod_eq_full by flia; flia).
pose proof (u32arr_store_ok usegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ k (Z_to_bv 64 (tmp mod 1000000000)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' w a z' ii -> ii = k \/ zone h w a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 (tmp mod 1000000000))) (zupd x k (tmp mod 1000000000)) (zone h' w a z')).
{ intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
zs. zs. brf K5.
+  zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z z); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
+ zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z k); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
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

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation S_N484 := (@QHB6.Mq3.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_N484 : S_N484.
Proof.
intros fo IH [kk carry a1 i rp1 xx] m'; intros until s'. intros _ DI2 RJ Hk FOK FRM' Hsg XR2 X312 Ra1 Rc1 Hkk Hsh Rz Rzf Rw Hfo Rrp Rrp1 Re2 HZ0 HS1 HA6 HL2 HK.
cbn [dk_x dk_a dk_carry dk_rp dk_k] in *. subst kk.

assert (Hshb : (1 <= sh <= 9)%Z) by (clear -Hsh; lia).
pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
pose proof (Z.mod_pos_bound (z - a1) 2048 ltac:(flia)) as Rrs1.
zs. brf K1.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with false in HL2 by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
eapply IH with (h := h) (x := xx) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1: exact (conj LW2 (conj LX2 REL2)).
all: try hlia Rzf.
-
unfold nz in HL2. replace (negb (carry =? 0))%Z with true in HL2 by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).

assert (HZ0R__ : (0 <= Z0 < 2 ^ 64)%Z) by (first [ clear - LTX LW HZ0 Re2 Rrp Hfo Rz LX2 LW2 SG3 SG1 SPT SPF SE_T Hp; lia | lia ]).
zs. brf K2.
+
replace ((z + 1) mod 2048 =? a1)%Z with false in HL2 by (symmetry; apply Z.eqb_neq; first [ clear - K2 K1 LTX LW HZ0 Re2 Rrp Hfo Rzf Rz Rc1 LX2 LW2 SG3 SG1 SPT SPF SE_T Hp; flia | flia ]). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 < 2047)%Z).
{ clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
zs. zs. zs. fix_idx.
pose proof (u32arr_store_ok usegs _ _ _ z _ XW ltac:(flia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ z (Z_to_bv 64 carry) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs.
assert (X31' : X31 (zupd xx z carry)).
{ intros ii. destruct (Z.eq_dec ii z) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }

stash_mods. stash_disj. do 20 zs. unstash. rewrite ?land2047. fix_idx.
destruct (Z.eq_dec z 2047) as [Ez|Hz47].
*
subst Z0. subst z. change ((2047 + 1) mod 2048)%Z with 0%Z in HL2 |- *.
eapply IH with (h := false) (x := zupd xx 2047 carry) (z := 0%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr.
destruct (Z.eq_dec ii 2047) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hr _] | Hr]]; [left | discriminate Hr | right; right; exact Hr].
unfold inring in Hr |- *. clear -Hr Hne Hq Ra1 K2. Z.div_mod_to_equations. flia. }
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
* rewrite (Z.mod_small (z + 1) 2048) in HL2, HZ0 by flia. subst Z0.
eapply IH with (h := h) (x := zupd xx z carry) (z := (z + 1)%Z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii z) as [->|Hne].
++ rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
++ rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|].
destruct Hr as [Hr | [[Hh Hzq] | Hr]]; [| right; left; split; [exact Hh | flia] | right; right; exact Hr].
apply (proj1 (inring_grow a1 z ii ltac:(flia) Hrs)) in Hr.
destruct Hr as [Hr|Hr]; [left; exact Hr|]. exfalso. apply Hne. apply (mod_eq_idx a1 z ii); flia. }
all: try hlia Rzf.
all: rewrite ?Z.shiftl_mul_pow2 by flia; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia.
all: try (replace (z + 1 + -1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; replace (z + 1 - 1)%Z with z by flia; rewrite (Z.mod_small z 2048) by flia; reflexivity).
+
replace ((z + 1) mod 2048 =? a1)%Z with true in HL2 by (symmetry; apply Z.eqb_eq; flia). cbn [negb] in HL2.
assert (Hrs : ((z - a1) mod 2048 = 2047)%Z).
{ clear -K2 Ra1 Rz HZ0. subst Z0. Z.div_mod_to_equations. flia. }
pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
assert (Kin : inring a1 z km).
{ unfold inring. subst km. rewrite Zminus_mod_idemp_l. clear -Hrs Ra1 Rz. Z.div_mod_to_equations. flia. }
pose proof (X312 km) as Rt. pose proof (REL2 km ltac:(flia) (zone_in h _ _ _ _ Kin)) as Et.
pose proof (u32arr_read usegs _ _ _ km _ _ XW (nth_error_wnth ws km ltac:(flia) ltac:(flia)) ltac:(flia) ltac:(unfold wa; f_equal; flia)) as RD.
zs. rewrite (sx32_wval ws km (znth xx km) (eq_sym Et) Rt). set (t := znth xx km) in *.
zs.
assert (Rt1 : (0 <= Z.lor t 1 < 2^31)%Z).
{ split; [apply Z.lor_nonneg; flia|]. apply (OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2 t 1 31); flia. }
pose proof (u32arr_store_ok usegs _ _ _ km _ XW ltac:(flia) ltac:(unfold wa; f_equal; flia)) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ km (Z_to_bv 64 (Z.lor t 1)) XW ltac:(flia)) as XW'. clear XW.
replace (A6 + 0)%Z with (q + -8312 + 4 * km)%Z by flia.
store_done'. rename XW' into XW.
zs.
eapply IH with (h := h) (x := zupd xx km (Z.lor t 1)) (z := z); try eassumption; rewrite ?landW_mod2048, ?land2047; try reflexivity; try flia; try mk_dfinv.
1:{ split; [rewrite upd_length; exact LW2|]. split; [rewrite zupd_length; exact LX2|].
intros ii Hq Hr. destruct (Z.eq_dec ii km) as [->|Hne].
-- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
-- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia | exact Hr]. }
1:{ intros ii. destruct (Z.eq_dec ii km) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312]. }
all: try hlia Rzf.
Qed.

End Floatscan.
