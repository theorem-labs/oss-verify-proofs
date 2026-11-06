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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation S_A568 := (@QHB6.Mq0.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@QHB6.Mq0.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N324 := (@QHB6.Mq0.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@QHB6.Mq0.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

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

Hypothesis HS_N3E8 : S_N3E8.
Hypothesis HS_A534 : S_A534.
Hypothesis HS_A568 : S_A568.

#[using="Type"] Lemma th0_val : znth th_list 0 = 10384593%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th1_val : znth th_list 1 = 717069655%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th2_val : znth th_list 2 = 257060992%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th3_val : znth th_list 3 = 658440191%Z. Proof. reflexivity. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3 HS_N3E8 HS_A534 HS_A568"] Lemma L_N324 : S_N324.
Proof.
unfold QHB6.Mq0.S_N324, QHB6.Mq0.SN324. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 HL HK; [discriminate HL|].
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).
rewrite df_dn_loop_step in HL. unfold df_dn_body in HL. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HL.
destruct (df_dni_loop 6 a z x 0) as [i1|] eqn:HI; [|discriminate HL].
change LD_B1B_DIG with 4%Z in HL. change (9 * 4)%Z with 36%Z in HL. change (9 + 36)%Z with 45%Z in HL. change MASK with 2047%Z in HL.
rewrite !land2047 in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs0.
assert (Naz_none : a = z -> rp <> 36%Z -> False).
{ intros Eaz Hrp. subst a. pose proof (dn_az_none (S fo) rp z e2 x i0 ltac:(flia) Hrp) as HN.
rewrite df_dn_loop_step in HN. unfold df_dn_body in HN. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HN. rewrite HI in HN.
change LD_B1B_DIG with 4%Z in HN. change (9 * 4)%Z with 36%Z in HN. change (9 + 36)%Z with 45%Z in HN. change MASK with 2047%Z in HN.
rewrite !land2047 in HN. rewrite HN in HL. discriminate HL. }

assert (G358 : forall (x5' x17' : word), i1 = 4%Z -> a <> z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5' x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (znth x a)) (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7288) fct None m (seg_rom rsegs))).
{ intros x5' x17' -> Naz. change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp; lia)).
brf K7.
-
replace (rp =? 36)%Z with false in HL by (symmetry; apply Z.eqb_neq; first [ clear - H0 H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]).
stmt HS_N3E8. eapply (NX fo IH 4%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
-
replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
zs. stmt HS_A568. eapply NX; try eassumption; try flia; try reflexivity.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]]. }

stash HZ0. stash HA6. stash HS1.
unfold df_dni_body in HI.
rewrite df_dni_loop_step in HI. change (0 <? LD_B1B_DIG)%Z with true in HI. cbv beta iota in HI. unfold df_dni_body in HI at 1.
change MASK with 2047%Z in HI. change LD_B1B_DIG with 4%Z in HI. rewrite Z.add_0_r, land2047, (Z.mod_small a 2048), th0_val in HI by flia.
zs. rewrite land2047, (Z.mod_small a 2048) by flia. zs. brf K1.
-
replace (a =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; flia). cbn [orb] in HI.
assert (Kin0 : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; clear -K1 Ra Rz Rrs0; Z.div_mod_to_equations; flia).
pose proof (X31H a) as Rt0. pose proof (REL a ltac:(flia) (zone_in h _ _ _ _ Kin0)) as Et0. clear Kin0.
pose proof (u32arr_read rsegs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(clear -Ra; flia) ltac:(clear -Ra LW'; flia)) ltac:(clear -Ra; flia) eq_refl) as RD0.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Et0) Rt0). set (t0v := znth x a) in *.
zs. zs. zs. brf K2.
+
replace (t0v <? 10384593)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K3.
*
replace (10384593 <? t0v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (0 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL.
stmt HS_N3E8. eapply (NX fo IH 0%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
*
replace (10384593 <? t0v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD0 Et0 K2 K3.
replace (0 + 1)%Z with 1%Z in HI by reflexivity.
rewrite df_dni_loop_step in HI. change (1 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th1_val in HI. replace (1 + 1)%Z with 2%Z in HI by reflexivity.
pose proof (land_mask_range (a + 1) 2047 ltac:(flia)) as Rk1. set (k1 := Z.land (a + 1) 2047) in *.
zs. zs. zs. brf K4.
--
replace (k1 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K4). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-- replace (k1 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K4). cbn [orb] in HI.
assert (Hd1 : (1 <= (z - a) mod 2048)%Z) by (clear -K1 Ra Rz Rrs0; Z.div_mod_to_equations; flia).
destruct (inring_plus a z 1 ltac:(flia) ltac:(flia) Hd1 K4) as [Kin1 Hd2]. fold k1 in Kin1.
pose proof (X31H k1) as Rt1. pose proof (REL k1 ltac:(flia) (zone_in h _ _ _ _ Kin1)) as Et1. clear Kin1.
pose proof (u32arr_read rsegs _ _ _ k1 _ _ XW (nth_error_wnth ws k1 ltac:(clear -Rk1; flia) ltac:(clear -Rk1 LW'; flia)) ltac:(clear -Rk1; flia) eq_refl) as RD1.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws k1 _ (eq_sym Et1) Rt1). set (t1v := znth x k1) in *.
zs. zs. zs. brf K5.
++
replace (t1v <? 717069655)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
eapply G358; [reflexivity | flia].
++ replace (t1v <? 717069655)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K6.
** replace (717069655 <? t1v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (1 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 1%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
** replace (717069655 <? t1v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD1 Et1 K5 K6.
rewrite df_dni_loop_step in HI. change (2 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th2_val in HI. replace (2 + 1)%Z with 3%Z in HI by reflexivity.
pose proof (land_mask_range (a + 2) 2047 ltac:(flia)) as Rk2. set (k2 := Z.land (a + 2) 2047) in *.
zs. zs. zs. brf K7.
{ replace (k2 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K7). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia]. }
replace (k2 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K7). cbn [orb] in HI.
destruct (inring_plus a z 2 ltac:(flia) ltac:(flia) Hd2 K7) as [Kin2 Hd3]. fold k2 in Kin2.
pose proof (X31H k2) as Rt2. pose proof (REL k2 ltac:(flia) (zone_in h _ _ _ _ Kin2)) as Et2. clear Kin2.
pose proof (u32arr_read rsegs _ _ _ k2 _ _ XW (nth_error_wnth ws k2 ltac:(clear -Rk2; flia) ltac:(clear -Rk2 LW'; flia)) ltac:(clear -Rk2; flia) eq_refl) as RD2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k2 _ (eq_sym Et2) Rt2). set (t2v := znth x k2) in *.
zs. zs. zs. brf K8.
{ replace (t2v <? 257060992)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (t2v <? 257060992)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K9.
{ replace (257060992 <? t2v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (2 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 2%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)). }
replace (257060992 <? t2v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD2 Et2 K8 K9.
rewrite df_dni_loop_step in HI. change (3 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th3_val in HI. replace (3 + 1)%Z with 4%Z in HI by reflexivity.
pose proof (land_mask_range (a + 3) 2047 ltac:(flia)) as Rk3. set (k3 := Z.land (a + 3) 2047) in *.
zs. zs. zs. brf K10.
{ replace (k3 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K10). cbn [orb] in HI. injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (k3 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K10). cbn [orb] in HI.
destruct (inring_plus a z 3 ltac:(flia) ltac:(flia) Hd3 K10) as [Kin3 Hd4]. fold k3 in Kin3.
pose proof (X31H k3) as Rt3. pose proof (REL k3 ltac:(flia) (zone_in h _ _ _ _ Kin3)) as Et3. clear Kin3.
pose proof (u32arr_read rsegs _ _ _ k3 _ _ XW (nth_error_wnth ws k3 ltac:(clear -Rk3; flia) ltac:(clear -Rk3 LW'; flia)) ltac:(clear -Rk3; flia) eq_refl) as RD3.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k3 _ (eq_sym Et3) Rt3). set (t3v := znth x k3) in *.
zs. zs. zs. brf K11.
{
assert (Hi4 : i1 = 4%Z).
{ destruct (Z.ltb_spec t3v 658440191).
- cbv iota in HI. injection HI as <-. reflexivity.
- replace (658440191 <? t3v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
rewrite df_dni_loop_step in HI. change (4 <? 4)%Z with false in HI. injection HI as <-. reflexivity. }
eapply G358; [exact Hi4 | flia]. }
replace (t3v <? 658440191)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
replace (658440191 <? t3v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
replace (3 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 3%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
+
replace (t0v <? 10384593)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-
replace (a =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; flia). cbn [orb] in HI. injection HI as <-.
change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp; lia)).
brf K7.
+  exfalso. exact (Naz_none ltac:(flia) ltac:(mlia2)).
+ replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
unstash. subst Z0 a. zs. stmt HS_A534. eapply NX; try eassumption; try flia.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]].
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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation S_NK := (@QHB6.Mq0.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).
Local Notation S_N484 := (@QHB6.Mq0.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@QHB6.Mq0.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_NK : S_NK.
Hypothesis HS_N484 : S_N484.

#[using="Hp SE_T SPF SPT SG1 SG3 HS_NK HS_N484"] Lemma L_N3E8 : S_N3E8.
Proof.
intros fo IH iq m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 Naz HB HK.
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).

assert (GC : forall sh, (sh = (if 45 <? rp then 9 else 1))%Z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) (Z_to_bv 64 rp)
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7330) fct None m (seg_rom rsegs))).
{ intros sh Hsh. rewrite <- Hsh in HB.
assert (Hsh2 : (sh = 1 \/ sh = 9)%Z) by (destruct (45 <? rp)%Z; lia).
destruct (df_dnk_loop FUEL_RING z sh _) as [[kk carry a1 i rp1 xx]|] eqn:HDK; [|discriminate HB]. unfold FUEL_RING in HDK.
zs. (brf K6; [ exfalso; lia | ]).
zs. zs. fixw3. replace (sh + e2)%Z with (e2 + sh)%Z by lia. zs. zs. zs. zs. zs. zs. zs. zs.
let v17 := getreg 17%Z in
replace v17 with (Z_to_bv 64 (2 ^ sh - 1)%Z) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
let v7 := getreg 7%Z in
replace v7 with (Z_to_bv 64 (Z.shiftr 1000000000 sh)) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
stmt HS_NK. eapply (NX 2050%nat) with (x := x) (h := h) (w := w) (k := a) (carry := 0%Z) (a := a) (i := iq) (rp := rp) (z := z) (sh := sh) (e2 := (e2 + sh)%Z) (B := (rp - 18450)%Z) (s1 := mkDK kk carry a1 i rp1 xx);
[mk_dfinv | assumption | assumption | exact (conj LW' (conj LX REL)) | exact X31H | lia | lia | lia | rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; lia | exact Naz | lia | exact Hsh2 | cbn; lia | exact Rw | lia | lia | exact HDK | ].
intros m' ws' b96' y17 y28 y29 y30 y31 w' DI2 XR2 X312 Ra1 Rc1 Rrp1 Rw1 Hk1; cbn [dk_x dk_a dk_carry dk_rp dk_k] in DI2, XR2, X312, Ra1, Rc1, Rrp1, Rw1, Hk1 |- *.
eapply (HS_N484 fo IH (mkDK kk carry a1 i rp1 xx)); try eassumption; try lia; cbn [dk_x dk_a dk_carry dk_rp dk_k]; try lia.
all: try (revert HB; destruct (nz carry); [destruct (negb ((z + 1) mod 2048 =? a1)%Z) |]; intros HB; exact HB).
all: show_goal. }
zs. fixw2. fixw. zs. zs. brs K5.
- zs. eapply GC. replace (45 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- zs. zs. eapply GC. replace (45 <? rp)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
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
Local Notation S_M := (@QHB6.Mq0.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@QHB6.Mq0.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
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

Hypothesis HS_M : S_M.

#[using="Type"] Lemma df_pad_loop_step : forall n k j x, df_pad_loop (S n) k (j, x) = if (j <? 9)%Z then df_pad_loop n k (df_pad_body k (j, x)) else Some (j, x).
Proof. reflexivity. Qed.

#[using="Type"] Lemma df_pad_loop_pow : forall (n : nat) (j k : Z) (x : list Z) jx,
(1 <= j <= 9)%Z -> (0 <= k < zlength x)%Z -> (0 <= znth x k)%Z -> (znth x k * 10 ^ (9 - j) < 2^32)%Z ->
df_pad_loop n k (j, x) = Some jx ->
length (snd jx) = length x /\ znth (snd jx) k = (znth x k * 10 ^ (9 - j))%Z /\ (forall i, i <> k -> znth (snd jx) i = znth x i).
Proof.
clear. induction n as [|n IH]; intros j k x jx Hj Hk Hx Hb HL; [discriminate HL|].
rewrite df_pad_loop_step in HL. destruct (Z.ltb_spec j 9) as [Hlt|Hge].
- unfold df_pad_body in HL.
assert (P1 : (10 ^ (9 - j) = 10 * 10 ^ (9 - (j + 1)))%Z) by (replace (9 - j)%Z with (Z.succ (9 - (j + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (j + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (E10 : u32 (znth x k * 10) = (znth x k * 10)%Z) by (unfold u32; apply Z.mod_small; nia).
rewrite E10 in HL.
destruct (IH (j + 1)%Z k (zupd x k (znth x k * 10)%Z) jx ltac:(lia)
ltac:(unfold zlength in *; rewrite zupd_length; lia)
ltac:(rewrite znth_zupd_eq by lia; lia)
ltac:(rewrite znth_zupd_eq by lia; rewrite P1 in Hb; lia) HL) as (L1 & L2 & L3).
split; [rewrite L1; apply zupd_length|]. split.
+ rewrite L2. rewrite znth_zupd_eq by lia. rewrite P1. lia.
+ intros i Hi. rewrite (L3 i Hi). apply znth_zupd_neq. lia.
- injection HL as <-. cbn [snd]. replace (9 - j)%Z with 0%Z by lia. rewrite Z.pow_0_r, Z.mul_1_r. auto.
Qed.

#[using="pre"] Lemma L_PADL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (i v : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
Z.of_nat n = (9 - i)%Z -> (1 <= i <= 8)%Z -> (0 <= v)%Z -> (v * 10 ^ (9 - i) < 2^32)%Z ->
(evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (v * 10 ^ (9 - i))) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d44) fct None m (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 v) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (i - 9)) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d38) fct None m (seg_rom rsegs)).
Proof.
induction n as [|n IH]; intros until v; intros DI Hn Ri Rv Hb CONT; [lia|].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
assert (P1 : (10 ^ (9 - i) = 10 * 10 ^ (9 - (i + 1)))%Z) by (replace (9 - i)%Z with (Z.succ (9 - (i + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (i + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Rv10 : (0 <= v * 10 < 2^32)%Z) by nia.
zs. fixw3. fixw. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Hi7 : i <> 8%Z) by (clear -K1 Ri; mlia).
replace (i - 9 + 1)%Z with ((i + 1) - 9)%Z by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign (i + 1)%Z (v * 10)%Z);
[exact DI | lia | lia | lia | rewrite P1 in Hb; lia | ].
replace (v * 10 * 10 ^ (9 - (i + 1)))%Z with (v * 10 ^ (9 - i))%Z by (rewrite P1; lia). apply CONT.
- assert (Ei : i = 8%Z) by (clear -K1 Ri; mlia). subst i.
replace (Z_to_bv 64 (8 - 9 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
replace (v * 10)%Z with (v * 10 ^ (9 - 8))%Z by (change (10 ^ (9 - 8))%Z with 10%Z; lia). apply CONT.
Qed.

#[using="T0 T1 SPLO SPF SPF2 SPT SG1 Q1 HS_M"] Lemma L_P : S_P.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Hx0 Rlnz Rrp Hxk Hkj Hkj45 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_pad in HK. unfold nz in HK. rewrite (s32_id lrp) in HK by lia.
pose proof LOW as LOWw. lo96w LOWw. rewrite le_bytes_to_word_le8 in LOWw.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Ej : j = 0%Z) by (clear -K1 Rj; mlia).
rewrite Ej, Z.eqb_refl in HK. cbn [negb] in HK. cbv beta iota in HK.
assert (Hk1 : (1 <= kz)%Z) by (destruct (Z.eq_dec kz 0) as [E|]; [exfalso; apply Hx0; apply Hkj; [exact E | exact Ej] | lia]).
zs. try rewrite le_bytes_to_word_le8.
stmt HS_M. eapply NX; [exact DI0 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | exact Hx0 | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia. left. lia.
- assert (Hj : j <> 0%Z) by (clear -K1 Rj; mlia).
replace (j =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HK.
destruct (df_pad_loop 10 kz (j, x)) as [jx|] eqn:HL; [|discriminate HK]. cbv beta iota in HK. destruct jx as [j' x']. cbn [snd] in HK |- *.
specialize (Hxk Hj). pose proof (X31H kz) as Rt.
assert (P10 : (10 ^ j <= 10 ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
assert (P9 : (10 ^ j * 10 ^ (9 - j) = 1000000000)%Z) by (rewrite <- Z.pow_add_r by lia; replace (j + (9 - j))%Z with 9%Z by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - j))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Hb : (0 <= znth x kz * 10 ^ (9 - j) < 1000000000)%Z) by nia.
destruct (df_pad_loop_pow 10 j kz x (j', x') ltac:(lia) ltac:(unfold zlength; lia) ltac:(lia) ltac:(lia) HL) as (L1 & L2 & L3). cbn [snd] in L1, L2, L3.
set (v' := (znth x kz * 10 ^ (9 - j))%Z) in *.
assert (Kin : digz kz j kz) by (unfold digz; right; right; split; [reflexivity | exact Hj]).
pose proof (REL kz ltac:(lia) Kin) as Et.
pose proof (u32arr_read rsegs _ _ _ kz _ _ XW (nth_error_wnth ws kz ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. try rewrite le_bytes_to_word_le8. brs K2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws kz (znth x kz) (eq_sym Et) Rt).
zs. zs.
replace (j + -9)%Z with (j - 9)%Z by lia.
eapply (L_PADL (Z.to_nat (9 - j)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 _ ev ws sign j (znth x kz));
[exact DI0 | lia | lia | lia | lia | ].
fold v'.
pose proof (u32arr_store_ok rsegs _ _ _ kz _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ kz (Z_to_bv 64 v') XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. fixw. zs.
stmt HS_M. eapply NX; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | | lia | | lia | lia | exact HK].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite L1; exact LX|].
intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia.
destruct (Z.eq_dec i kz) as [->|Hne].
* rewrite L2. rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
* rewrite (L3 i Hne). rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia.
+ intros i. destruct (Z.eq_dec i kz) as [->|Hne]; [rewrite L2; lia | rewrite (L3 i Hne); apply X31H].
+ destruct (Z.eq_dec 0 kz) as [E0|Hne]; [| rewrite (L3 0%Z Hne); exact Hx0].
subst kz. rewrite L2. subst v'. clear -Hx0 Rt P2. nia.
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
Local Notation S_A64 := (@QHB6.Mq0.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq0.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9C8 := (@QHB6.Mq0.S_9C8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_LZ := (@QHB6.Mq0.S_LZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_990 := (@QHB6.Mq0.S_990 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@QHB6.Mq0.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Hypothesis HS_A64 : S_A64.
Hypothesis HS_7F4 : S_7F4.

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

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_9C8 : S_9C8.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (N46 : c <> 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_A64. eapply NX; try eassumption; try lia. mk_winv2.
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
(Z_to_bv 64 53) (Z_to_bv 64 1) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd691c) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 1%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_LZ : S_LZ.
Proof.
unfold QHB6.Mq0.S_LZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK.
dest_winv WI. bury_disj.
rewrite df_lz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (HEAD : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd68dc) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1, HL.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w8 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) 1%Z g' c' f');
try eassumption; try lia. }
assert (EXIT : forall m2 (x1' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd68f8) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', c', f') = (1%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
stmt L_9C8. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
- pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
- pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_990 : S_990.
Proof.
intros n m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_LZ as NX. unfold QHB6.Mq0.S_LZ, QHB6.Mq0.SLZn in NX. eapply (NX n); try eassumption; try lia. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
assert (E : (g', c', f') = (1%Z, c, f)).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
zs. stmt L_9C8. eapply NX; try eassumption; try lia. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_848 : S_848.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|]. rewrite df_lz_loop_step, Z.eqb_refl in HK.
set (g := sh_unget f) in *.
destruct (df_lz_loop fu _) as [[[g' c'] f']|] eqn:HL; [|discriminate HK].
assert (Hg : RFJ' (kmin - 1) 48 g /\ sh_stdio g = sh_stdio f0 /\ sh_buf g = txt).
{ subst g. split; [|split; [unfold sh_unget; destruct (sh_shlim_neg f); exact Hst | unfold sh_unget; destruct (sh_shlim_neg f); exact Hbuf]].
apply (RFJ_rechar (kmin - 1) c); [apply (RFI_unget T txt p J Hp kmin c f RJ); lia | lia |].
intros E. rewrite (rf_unget_eq f (proj1 (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)))). cbn.
destruct (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)) as (_ & N2 & _). lia. }
destruct Hg as (RJg & Hstg & Hbufg).

assert (CONT : forall m2 (x10' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws g ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (T + sh_rpos g)) (Z_to_bv 64 sign) x10' x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd678c) fct None m2 (seg_rom rsegs))).
{ intros m2 x10' WI2. clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL BFC.
pose proof WI2 as WI3. dest_winv WI3.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof (RFI_rpos T txt p J Hp (kmin - 1) 48 g RJg) as Rrpg.
assert (RRg : (0 <= rf_rend T p true g <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio g); unfold zlength in *; lia). unfold M64 in RRg.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin - 1) 48 g RJg ltac:(lia)) as RJ1.
pose proof (getc_stdio g) as Hst1. rewrite Hstg in Hst1.
assert (Rc' : (-1 <= fst (sh_getc g) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 g Hbufg) as [Rrp1 Rrp2].
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.

assert (JOIN : forall m3 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x28' x29' x30' x31' : word),
winv m3 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc g)) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc g))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd68c0) fct None m3 (seg_rom rsegs))).
{ intros until x31'. intros WI4.
stmt L_990. eapply (NX fu) with (kmin := (kmin - 1 + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). rewrite Efu. exact HK. }
zs.
destruct (Z.eq_dec (T + sh_rpos g)%Z (rf_rend T p true g)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJg SLOW Hstg.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp (kmin - 1) 48 g RJg ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp (kmin - 1) 48 g RJg FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos g) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char g. zs.
eapply JOIN. mk_winv2. }

pose proof FC as FC0. ufc2 FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
-
assert (Eg : g = f) by (subst g; apply rf_unget_nop; exact SN).
zs. zs. zs. (brf K0; [ | exfalso; lia ]).
replace (Z_to_bv 64 (T + sh_rpos f)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; reflexivity).
eapply CONT. rewrite Eg. mk_winv2.
- assert (Eg : g = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) by (subst g; apply rf_unget_eq; exact SN).
clear FC0.
zs. zs. zs. (brf K0; [ exfalso; lia | ]).
zs. zs0.
replace (Z_to_bv 64 (T + sh_rpos f + -1)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; cbn [sh_rpos]; f_equal; lia).
eapply CONT. rewrite Eg. unfold QHB6.Mq0.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite SN. unfold rf_rend in FC. hyp_cells.
Qed.

End Floatscan.
End Mq3.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QM7w QNAo QCwx QFqQ Q98Z QkLq QdZ1 Qv4L Qkaz QULt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QmBS.Mq1 Qlfl.Mq3 QHB6.Mq2 Qkaz.Mq0 Qlfl.Mq2 QHB6.Mq1.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Definition rHAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (ag_body f sc req k bail st2 mm) s' Q
(MS (rag_regs (Z_to_bv 64 0xceb98) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
F (Z_to_bv 64 0xceba4) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : rHAG_stmt.

#[using="RC__ TP"] Lemma rerrno_lit2 : errno_addr tp = 0x622dbc.
Proof. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="RC__ m MR"] Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="m ER MR"] Lemma rta_fp_malloc_fp stE mE a :
rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right.
pose proof (AREAS q MSq) as MSq'.
destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [exact H0|]. split; [exact K0|].
rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
- do 3 right. left. pose proof MR as (WF & _).
destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
rewrite Cb in Xq. lia.
Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_image a : 0x10000 <= a < 0x645000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

#[using="RC__ m sc MR CLO LO"] Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
pose proof (RAS_STACK_ge sc) as ASG. unfold alloc_ceiling in CLO.
intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- unfold RCTX in X. lia.
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in RC. lia.
Qed.

#[using="UA"] Lemma runk_agree_keep stE mE :
s_shadow stE = s_shadow st ->
(forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
(forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
(forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
unk_agree stE o mE.
Proof.
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_inband rid r off :
(s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC, CLO.
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

#[using="st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG"] Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
rimplT o (as_grp full_lay f sc req k bail st1) s Q
(MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb80) fc None m1 (seg_rom rsegs)).
Proof.
intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
pose proof rerrno_lit2 as EA.
pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
rewrite (as_grp_eq f sc req k bail st1).
riprefixT. unfold rag_regs.
eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.

assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
assert (BL1 : brk_link_ps st1 s).
{ unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
{ apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| unfold alloc_ceiling; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
- intros a Ha. apply rta_fp_not_high. exact Ha.
- intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
[ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
| rewrite unsigned_lit by lia; exact ST1 | exact CLO
| rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
intros st2 mo s' ms' PO BL2 LF.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL & E12).
rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
replace (ret_pc (Z_to_bv 64 0xceb98)) with (Z_to_bv 64 0xceb98) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).

assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x645000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x622dbc <= a < 0x622dc0)) ->
~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
{ intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. lia.
- unfold RCTX in *. lia.
- destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). unfold alloc_ceiling in BC.
pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
- destruct X as [XC XF]. unfold alloc_ceiling in XC.
pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
{ eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }

assert (REL02 : mrel st st2).
{ split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
{ intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
exists ar, arr', kk. auto. }
assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
- eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
+ left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
+ do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
* rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
* intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }

assert (UA3 : unk_agree st2 o m3).
{ eapply (runk_agree_keep st2 m3).
- rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
- intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
+ destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
+ exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
- intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
- intros rid r off h Hr Hk Ho Hc NG.
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
transitivity (m1 (wa (r_base r + off))).
+ refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
* lia.
* rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
* destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
* assert (Hr2 : (s_regions st2) !! rid = Some r).
{ rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
* rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
+ refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
destruct mo as [mm|].
-
destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [unfold alloc_ceiling in GC; lia| exact MI3]. }
cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply evt_done.
eapply (HAG st1 st2 mm m3 s'); try eassumption.
+ eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
+ eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
+ eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
+ eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
-
cbn iota.
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
cbv beta. intros ms' ->. cbn [Z.eqb].
eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
apply HK. unfold ras_post2.
do 14 eexists. exists m3, errv3. split; [reflexivity|].
split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
split. { constructor.
- intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
- rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
left. split; [reflexivity| exact (E12 eq_refl)].
Qed.
End LEVEL.

End RC__1.
End Mq4.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE Q6y7 Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 QFkE Q6y7 QJE4.Mq2 Q3o5.Mq0 QULt.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq2 QdZ1.Mq4 QmBS.Mq4 QdZ1.Mq1 Qlfl.Mq4.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rauxv_ok_pres_B : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 6434236 <= a < 6434240) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 6434236 <= a < 6434240.

#[using="RC__ m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- pose proof (rfree_fp_lt (RC__:=RC__) st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- lia.
Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_img a : 0xe2000 <= a < 0x645000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (6434236 <= a < 6434240) -> ~ FPT a.
Proof.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- exact (N2 ER).
Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_image a : 0xe2000 <= a < 0x645000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RMLOCK, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

#[using="RC__ m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). unfold alloc_ceiling in RGC.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold RCTX in X. lia.
+ destruct X as (rid & r & Hr & NK & Hin).
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.

#[using="RC__ st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
intros HLB a Ha CA. apply PE; [exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply rfp_not_high. exact CA.
- apply rfp_not_image; assumption.
- apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
- intros a Ha. apply rfp_not_high. lia.
- intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

#[using="Type"] Theorem rfree_impl_spec_proof : rfree_impl_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.
destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
pose proof (QNAo.Mq2.areach_cinv_proof _ _ AR) as C.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_addr blk_slot fst snd] in OA.
pose proof (Q3o5.Mq1.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
(fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
/\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
- exact Hst.
- exact HOK.
- apply rimplT_reach.
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
[unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
- intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
unfold rfree_post. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
split; [reflexivity|]. split; [reflexivity|].
exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
split; [reflexivity|]. split; [exact MR'|]. split.
+  unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
+ destruct LEAF as (ans & o' & FO).
eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

#[using="Type"] Theorem rfree_spec_proof : rfree_stmt.
Proof. exact (rfree_stmt_of_impl rfree_impl_spec_proof). Qed.

End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF Q8P7 QTyG QnOf Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 Qy5Y.Mq4 Q4J3.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9 Q6y7.Mq2 QDUx.Mq7 Q3o5 Q8P7 QTyG.Mq1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq7 Qv4L.Mq0 Qv4L.Mq8 QnkH.Mq7 Qi8L.Mq4 QmBS.Mq3 Qv4L.Mqa QnkH.Mq6.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_ext : forall st st' m,
rmrep st m ->
s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_reserved st' = s_reserved st ->
rmrep st' m.
Proof.
intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^63.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.

#[using="Type"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbf_regions : s_regions stF = s_regions st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_areas : s_areas stF = s_areas st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof. reflexivity. Qed.
#[using="GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite rbf_ctx. reflexivity. Qed.

#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof.
intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
- exact rbf_ctx.
- intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
- rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

#[using="Type"] Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

#[using="NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

#[using="Type"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

#[using="Type"] Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ (RMLOCK <= a < RMLOCK + 4 \/ 0x6446f8 <= a < 0x6446f8 + 4) \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x645000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="Type"] Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
rmrep st m -> munch [(spv - 80, spv); (0x622dbc, 0x622dbc + 4)] m m' -> wmono rsegs m m' -> alloc_ceiling <= spv - 80 ->
rmrep st m'.
Proof.
intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

#[using="Type"] Lemma rfp_below_ceiling K st3 stx m lo spv a :
rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
- rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
- unfold RCTX, alloc_ceiling in *. lia.
- pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.

#[using="Type"] Lemma rbig_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

#[using="Type"] Lemma rregion_facts_hi : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
r_base r + round_up_pg (r_len r) <= 0xe7000 \/ 0x645000 <= r_base r.
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.

Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

#[using="Type"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved rc_secret).
Proof.
intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (QULt.Mq1.areach_ampre_proof _ _ AR)|].
unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

#[using="ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof.
pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).

riprefixT. unfold alloc_ceiling in CLO. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
unfold RMLOCK.
step. step. step. step. step. step. step. step. step.
apply evt_done.
set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
eapply rimplT_mmap_rw.
{ eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
[ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
| reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rewrite Q9A7.Mq0.alloc_ceiling_val; lia
| rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
intros ans ms' PO.
assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (6434400 + -164, 6434400 + -164 + 4)] m1 m2 -> wmono rsegs m1 m2 ->
rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
{ intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
- eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
- eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| unfold alloc_ceiling; lia].
eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
- eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
- eapply unk_agree_munch; [exact UA1| exact MU| |].
+ intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. unfold alloc_ceiling in R2. cbn. lia.
+ intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). unfold alloc_ceiling in R2. lia. }
destruct ans as [e|xa].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He).
cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e ltac:(clear -He; lia)) as [-> ->]. cbn [negb].
apply rimplT_ret.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
replace (ret_pc (Z_to_bv 64 0xce6c8)) with (Z_to_bv 64 0xce6c8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
exists m2, (Z_to_bv 64 (Q9A7.Mq0.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
split; [apply mrel_same; reflexivity|]. split; [exact BL|]. rewrite He. repeat split; reflexivity.
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
2:{ cbn [negb]. apply rimplT_undef. }
cbn [negb].
destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).

unfold new_region.
set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
assert (PT1 : ptrs_in (fun r => r <> rid) st1).
{ eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
set (L := mmap_len (n + IB + UNIT)).
assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
unfold Q9A7.Mq0.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. unfold alloc_ceiling in XC. unfold IB, UNIT in LG.
set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
{ intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
{ intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (MRz : rmrep st2 mz).
{ rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
rewrite <- ?EL; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
fold mz in ST2 |- *.

pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
assert (XI : xa + L <= 0x10000 \/ 0x645000 <= xa).
{ assert (RFimg : ranges_free ref_reserved xa L = true).
{ apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
apply (rreserved_disjoint1 _ _ RFimg). lia. }
assert (MIz : mem_inv rsegs mz).
{ unfold mz. apply (mem_inv_zeros rsegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
assert (FRz : rw_cells rsegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
assert (UAz : unk_agree st2 o mz).
{ eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
- right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
- left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }

riprefixT.
replace (ret_pc (Z_to_bv 64 0xce6c8)) with (Z_to_bv 64 0xce6c8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
eapply evt_cut.
{ eapply (rbig_seq_walk sp gp (Z_to_bv 64 6434400)) with (st := st2) (lo := lo);
[exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| unfold alloc_ceiling; lia| exact MIz]. }
intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
apply evt_done.

assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
assert (WMz : wmono rsegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono rsegs m2 xa L); try lia; exact Hw).
assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
assert (ERRz : rw_cells rsegs mz (6434400 + -164) [C4 errv]).
{ eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (ERR3 : rw_cells rsegs m3 (6434400 + -164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
assert (BL2 : brk_link_ps (step_seq st2) s).
{ eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
eapply AM.
{ apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
{ exact MR3. }
{ exact TK2'. }
{ exact BL2. }
{ rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| unfold alloc_ceiling; lia]. }
{ rewrite SP'. exact ST3. }
{ unfold alloc_ceiling; lia. }
{ rewrite SP'. unfold RAM_STACK. lia. }
{ unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
{ exact MI3. }
{ reflexivity. }
intros st3 mo s' ms' PO3 BL3.
destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL & E12).
rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
replace (ret_pc (Z_to_bv 64 0xce7bc)) with (Z_to_bv 64 0xce7bc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -48) cs) end.
{ eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| unfold alloc_ceiling; lia]. }
assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
assert (PT3 : ptrs_in (fun q => q <> rid) st3).
{ apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.

assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
(forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
{ intros stF RSF HFP.
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
{ transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
destruct mo as [g|].
+
apply rimplT_ret.
destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
set (G := conc st3 g) in *.
assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; unfold alloc_ceiling in GC; lia).
assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
{ intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
{ intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (SHN3 : (s_shadow st3) !! rid = None).
{ rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. exact FRs. }
assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
{ rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. reflexivity. }
eapply evt_cut.
{ eapply (rbig_succ_walk (RC__:=RC__) st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold alloc_ceiling; lia) sp gp (Z_to_bv 64 6434400));
[exact HG| exact FR4| exact ST4| lia| exact MI4]. }
intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
apply evt_done. cbn [rcoreQ].
set (stF := big_final st3 g rid n).
rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
change (pw st3 (Some g)) with (pw stF (Some g)).
exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
split; [reflexivity|].
assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
split; [exact MRF|].
split; [exact TK7|].
assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
{ intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
split.
{
assert (UA3 : unk_agree (step_seq st2) o m3).
{ eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
assert (UA4 : unk_agree st3 o m4).
{ eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
{ destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
- destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
- exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). unfold alloc_ceiling in BC.
refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
- pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
- right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
- left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
assert (ERR8 : rw_cells rsegs m7 (6434400 + -164) [C4 errv4]).
{ eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
{ eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_trans.
{ eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
- left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
- do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
- left. right; right; left. unfold RCTX in *. lia. }
apply rpres_except_refl. }
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. exact Hr'.
- change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
split. { intros a Ha. do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
split. { unfold u32. Z.div_mod_to_equations. lia. }
assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
rewrite <- big_ml_eq in RU by lia.
split.
{  constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
- reflexivity.
- exact RR3.
- reflexivity.
- lia.
- reflexivity.
- lia.
- lia.
- rewrite <- EL. lia.
- lia.
- rewrite RU. Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
- change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- intros off Ho Hfit. Z.div_mod_to_equations. lia.
- unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
- exact MSL.
- lia.
- lia.
- lia.
- lia.
- right. repeat split; lia. }
split. { intros _. unfold Q4J3.Mq1.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
split; [exact MRELF|].
split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
repeat split; assumption.
+
cbn [pw oconc].
riprefixT.
eapply evt_cut.
{ apply rbig_fail2a_walk. exact ML4. }
intros ms2 ->. apply evt_done.
eapply rimplT_munmap.
{ eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
[ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4
| pose proof MR4 as (_ & _ & (_ & _ & _ & _ & _ & VML4) & _); exact VML4 | unfold RVMLOCK, alloc_ceiling in *; lia | rewrite ELm; unfold RVMLOCK, alloc_ceiling in *; lia
| reflexivity | unfold IB, UNIT; f_equal; lia
| lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; unfold alloc_ceiling in *; lia
| rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
intros ans2 ms3 PM. unfold rmunmap_post in PM.
destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
rewrite (munmap_answer_ok_range ans2 ltac:(destruct ans2; cbn in He6 |- *; [lia| exact Logic.I])). apply rimplT_ret.
rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
replace (ret_pc (Z_to_bv 64 0xce894)) with (Z_to_bv 64 0xce894) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -48) cs) end.
{ eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. unfold alloc_ceiling in *. lia. }
eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
set (stF := drop_region rid st3).
assert (MRF : rmrep stF m6).
{ eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
rewrite <- EL in Hout.
assert (A1 : a < alloc_ceiling /\ (a + 1 <= 6434400 + -164 \/ 6434400 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
{ destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
[unfold RMLOCK, alloc_ceiling in *; lia| unfold RLIBC, alloc_ceiling in *; lia| unfold RGOT_SSP, alloc_ceiling in *; lia| unfold RSSP_GUARD, alloc_ceiling in *; lia|].
destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
split; [lia|]. split; [lia|].
destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
unfold alloc_ceiling in A1.
apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
{ eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
exists m6, (Q9A7.Mq0.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
- unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
split; [exact MRELF|].
split.
{ eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
repeat split; try assumption.
destruct ans2 as [e2|b2]; cbn [Q9A7.Mq0.rg_errno]; cbn in He6; [rewrite He6; reflexivity| exact (E12 eq_refl)].
Qed.
End BIG.

End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Q4J3.Mq3 Qnxq QPjm.Mq4 QBpc QNAo.Mq1 QULt.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq2.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rregion_addr_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x645000 <= r_base r).
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma rblock_inside st LB m blk :
MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
/\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
/\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
/\ 0 <= blk_size blk
/\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x645000 <= r_base r).
Proof.
intros MF MR IN.
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
destruct BR as (r & Hr & Hk).
pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
pose proof (round_up_pg_ge (r_len r)) as RU.
rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Esnd in EA. unfold alloc_ceiling in *.
assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof.
intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (QTyG.Mq2.areach_facts_proof _ _ AR)) as ND.
eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
inversion ND; subst. constructor; [|apply IH; assumption].
intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof.
intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
assert (32 <= round_up_pg (r_len r)) by nia.
unfold rblock_range. unfold alloc_ceiling in *. split; [lia|]. split; [|lia].
rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_disjoint_proof : forall s LB m b1 b2,
RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros s LB m b1 b2 (st & LB0 & HP & _ & MR & [_ AR]) I1 I2 NE. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
- exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
+ exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
+ exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
- destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
+ exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
+ destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

#[using="Type"] Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
\/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ 0x6446f8 <= a < 0x6446f8 + 4 \/ a < 0x10000 \/ 0x645000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="Type"] Lemma RHEAP_frame_proof : forall s LB m m' W,
RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof.
intros s LB m m' W (st & LB0 & HP & Hst & MR & HI) MU WM FW. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
split; [|exact HI].
destruct HI as [_ AR]. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
eapply (rmrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (rrepfoot_where st m a MR RF) as [AC AW].
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
- unfold alloc_ceiling in *. lia.
- unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, RVMLOCK, alloc_ceiling in *. lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
+ unfold RCTX in R1. lia.
+ unfold RMLOCK in R2. lia.
+ unfold RNEED_LOCKS in R3. lia.
+ unfold RPAGE_SIZE in R4'. lia.
+ destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
+ unfold RGOT_SSP in R8. lia.
+ unfold RSSP_GUARD in R9. lia.
Qed.

#[using="Type"] Lemma reservedZ_ref : reservedZ rsegs = ref_reserved.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
u64arr rsegs m A (repeat (wz 0) k).
Proof.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.
End RC__1.

Ltac rimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

End RC__2.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation S_A568 := (@QHB6.Mq3.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@QHB6.Mq3.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N324 := (@QHB6.Mq3.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@QHB6.Mq3.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

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

Hypothesis HS_N3E8 : S_N3E8.
Hypothesis HS_A534 : S_A534.
Hypothesis HS_A568 : S_A568.

#[using="Type"] Lemma th0_val : znth th_list 0 = 10384593%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th1_val : znth th_list 1 = 717069655%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th2_val : znth th_list 2 = 257060992%Z. Proof. reflexivity. Qed.
#[using="Type"] Lemma th3_val : znth th_list 3 = 658440191%Z. Proof. reflexivity. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3 HS_N3E8 HS_A534 HS_A568"] Lemma L_N324 : S_N324.
Proof.
unfold QHB6.Mq3.S_N324, QHB6.Mq3.SN324. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 HL HK; [discriminate HL|].
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).
rewrite df_dn_loop_step in HL. unfold df_dn_body in HL. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HL.
destruct (df_dni_loop 6 a z x 0) as [i1|] eqn:HI; [|discriminate HL].
change LD_B1B_DIG with 4%Z in HL. change (9 * 4)%Z with 36%Z in HL. change (9 + 36)%Z with 45%Z in HL. change MASK with 2047%Z in HL.
rewrite !land2047 in HL.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs0.
assert (Naz_none : a = z -> rp <> 36%Z -> False).
{ intros Eaz Hrp. subst a. pose proof (dn_az_none (S fo) rp z e2 x i0 ltac:(flia) Hrp) as HN.
rewrite df_dn_loop_step in HN. unfold df_dn_body in HN. cbn [ds_a ds_z ds_x ds_rp ds_e2] in HN. rewrite HI in HN.
change LD_B1B_DIG with 4%Z in HN. change (9 * 4)%Z with 36%Z in HN. change (9 + 36)%Z with 45%Z in HN. change MASK with 2047%Z in HN.
rewrite !land2047 in HN. rewrite HN in HL. discriminate HL. }

assert (G358 : forall (x5' x17' : word), i1 = 4%Z -> a <> z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5' x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (znth x a)) (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd994c) fct None m (seg_rom usegs))).
{ intros x5' x17' -> Naz. change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp; lia)).
brf K7.
-
replace (rp =? 36)%Z with false in HL by (symmetry; apply Z.eqb_neq; first [ clear - H0 H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]).
stmt HS_N3E8. eapply (NX fo IH 4%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
-
replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
zs. stmt HS_A568. eapply NX; try eassumption; try flia; try reflexivity.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]]. }

stash HZ0. stash HA6. stash HS1.
unfold df_dni_body in HI.
rewrite df_dni_loop_step in HI. change (0 <? LD_B1B_DIG)%Z with true in HI. cbv beta iota in HI. unfold df_dni_body in HI at 1.
change MASK with 2047%Z in HI. change LD_B1B_DIG with 4%Z in HI. rewrite Z.add_0_r, land2047, (Z.mod_small a 2048), th0_val in HI by flia.
zs. rewrite land2047, (Z.mod_small a 2048) by flia. zs. brf K1.
-
replace (a =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; flia). cbn [orb] in HI.
assert (Kin0 : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; clear -K1 Ra Rz Rrs0; Z.div_mod_to_equations; flia).
pose proof (X31H a) as Rt0. pose proof (REL a ltac:(flia) (zone_in h _ _ _ _ Kin0)) as Et0. clear Kin0.
pose proof (u32arr_read usegs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(clear -Ra; flia) ltac:(clear -Ra LW'; flia)) ltac:(clear -Ra; flia) eq_refl) as RD0.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Et0) Rt0). set (t0v := znth x a) in *.
zs. zs. zs. brf K2.
+
replace (t0v <? 10384593)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K3.
*
replace (10384593 <? t0v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (0 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL.
stmt HS_N3E8. eapply (NX fo IH 0%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
*
replace (10384593 <? t0v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD0 Et0 K2 K3.
replace (0 + 1)%Z with 1%Z in HI by reflexivity.
rewrite df_dni_loop_step in HI. change (1 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th1_val in HI. replace (1 + 1)%Z with 2%Z in HI by reflexivity.
pose proof (land_mask_range (a + 1) 2047 ltac:(flia)) as Rk1. set (k1 := Z.land (a + 1) 2047) in *.
zs. zs. zs. brf K4.
--
replace (k1 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K4). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-- replace (k1 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K4). cbn [orb] in HI.
assert (Hd1 : (1 <= (z - a) mod 2048)%Z) by (clear -K1 Ra Rz Rrs0; Z.div_mod_to_equations; flia).
destruct (inring_plus a z 1 ltac:(flia) ltac:(flia) Hd1 K4) as [Kin1 Hd2]. fold k1 in Kin1.
pose proof (X31H k1) as Rt1. pose proof (REL k1 ltac:(flia) (zone_in h _ _ _ _ Kin1)) as Et1. clear Kin1.
pose proof (u32arr_read usegs _ _ _ k1 _ _ XW (nth_error_wnth ws k1 ltac:(clear -Rk1; flia) ltac:(clear -Rk1 LW'; flia)) ltac:(clear -Rk1; flia) eq_refl) as RD1.
zs. zs. fix_idx. zs. rewrite (sx32_wval ws k1 _ (eq_sym Et1) Rt1). set (t1v := znth x k1) in *.
zs. zs. zs. brf K5.
++
replace (t1v <? 717069655)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
eapply G358; [reflexivity | flia].
++ replace (t1v <? 717069655)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K6.
** replace (717069655 <? t1v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (1 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 1%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
** replace (717069655 <? t1v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD1 Et1 K5 K6.
rewrite df_dni_loop_step in HI. change (2 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th2_val in HI. replace (2 + 1)%Z with 3%Z in HI by reflexivity.
pose proof (land_mask_range (a + 2) 2047 ltac:(flia)) as Rk2. set (k2 := Z.land (a + 2) 2047) in *.
zs. zs. zs. brf K7.
{ replace (k2 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K7). cbn [orb] in HI. injection HI as <-.
eapply G358; [reflexivity | flia]. }
replace (k2 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K7). cbn [orb] in HI.
destruct (inring_plus a z 2 ltac:(flia) ltac:(flia) Hd2 K7) as [Kin2 Hd3]. fold k2 in Kin2.
pose proof (X31H k2) as Rt2. pose proof (REL k2 ltac:(flia) (zone_in h _ _ _ _ Kin2)) as Et2. clear Kin2.
pose proof (u32arr_read usegs _ _ _ k2 _ _ XW (nth_error_wnth ws k2 ltac:(clear -Rk2; flia) ltac:(clear -Rk2 LW'; flia)) ltac:(clear -Rk2; flia) eq_refl) as RD2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k2 _ (eq_sym Et2) Rt2). set (t2v := znth x k2) in *.
zs. zs. zs. brf K8.
{ replace (t2v <? 257060992)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (t2v <? 257060992)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]). cbv iota in HI.
zs. brf K9.
{ replace (257060992 <? t2v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). injection HI as <-.
replace (2 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 2%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)). }
replace (257060992 <? t2v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
clear RD2 Et2 K8 K9.
rewrite df_dni_loop_step in HI. change (3 <? 4)%Z with true in HI. unfold df_dni_body in HI. cbv beta iota in HI.
change MASK with 2047%Z in HI. rewrite th3_val in HI. replace (3 + 1)%Z with 4%Z in HI by reflexivity.
pose proof (land_mask_range (a + 3) 2047 ltac:(flia)) as Rk3. set (k3 := Z.land (a + 3) 2047) in *.
zs. zs. zs. brf K10.
{ replace (k3 =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; exact K10). cbn [orb] in HI. injection HI as <-. eapply G358; [reflexivity | flia]. }
replace (k3 =? z)%Z with false in HI by (symmetry; apply Z.eqb_neq; exact K10). cbn [orb] in HI.
destruct (inring_plus a z 3 ltac:(flia) ltac:(flia) Hd3 K10) as [Kin3 Hd4]. fold k3 in Kin3.
pose proof (X31H k3) as Rt3. pose proof (REL k3 ltac:(flia) (zone_in h _ _ _ _ Kin3)) as Et3. clear Kin3.
pose proof (u32arr_read usegs _ _ _ k3 _ _ XW (nth_error_wnth ws k3 ltac:(clear -Rk3; flia) ltac:(clear -Rk3 LW'; flia)) ltac:(clear -Rk3; flia) eq_refl) as RD3.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k3 _ (eq_sym Et3) Rt3). set (t3v := znth x k3) in *.
zs. zs. zs. brf K11.
{
assert (Hi4 : i1 = 4%Z).
{ destruct (Z.ltb_spec t3v 658440191).
- cbv iota in HI. injection HI as <-. reflexivity.
- replace (658440191 <? t3v)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
rewrite df_dni_loop_step in HI. change (4 <? 4)%Z with false in HI. injection HI as <-. reflexivity. }
eapply G358; [exact Hi4 | flia]. }
replace (t3v <? 658440191)%Z with false in HI by (symmetry; apply Z.ltb_ge; first [assumption | flia]).
replace (658440191 <? t3v)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
replace (3 =? 4)%Z with false in HL by reflexivity. cbn [andb] in HL. stmt HS_N3E8. eapply (NX fo IH 3%Z); try eassumption; try flia. exact (conj LW' (conj LX REL)).
+
replace (t0v <? 10384593)%Z with true in HI by (symmetry; apply Z.ltb_lt; first [assumption | flia]). cbv iota in HI. injection HI as <-.
eapply G358; [reflexivity | flia].
-
replace (a =? z)%Z with true in HI by (symmetry; apply Z.eqb_eq; flia). cbn [orb] in HI. injection HI as <-.
change (4 =? 4)%Z with true in HL. cbn [andb] in HL.
zs. fixw2. fixw. zs. zs.
try (assert (HrpR__ : (0 <= rp < 2 ^ 64)%Z) by (clear - K1 Naz_none LTX Re2 Rrp Hfo Rzf Rz LX LW' LW SG3 SG1 SPT SPF SE_T Hp; lia)).
brf K7.
+  exfalso. exact (Naz_none ltac:(flia) ltac:(mlia2)).
+ replace (rp =? 36)%Z with true in HL by (symmetry; apply Z.eqb_eq; first [ clear - H K7 Naz Naz_none LTX Re2 Rrp Hfo Rzf LX LW' LW SG3 SG1 SPT SPF SE_T Hp; mlia2 | mlia2 ]). injection HL as <-. cbn [ds_a ds_z ds_x ds_e2] in HK.
unstash. subst Z0 a. zs. stmt HS_A534. eapply NX; try eassumption; try flia.
split; [exact (conj LW' (conj LX REL)) | split; [exact X31H | split; [flia | split; [hlia Rzf | split; [flia | intros E; specialize (Rw E); mlia2]]]]].
Qed.

End Floatscan.
End Mq8.

Module Mq9.

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
Local Notation S_NK := (@QHB6.Mq3.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).
Local Notation S_N484 := (@QHB6.Mq3.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@QHB6.Mq3.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_NK : S_NK.
Hypothesis HS_N484 : S_N484.

#[using="Hp SE_T SPF SPT SG1 SG3 HS_NK HS_N484"] Lemma L_N3E8 : S_N3E8.
Proof.
intros fo IH iq m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzf Rw Hfo Rrp Re2 HZ0 HS1 HA6 Naz HB HK.
pose proof DI as DI0. dest_dfinv DI. destruct XR as (LW' & LX & REL).

assert (GC : forall sh, (sh = (if 45 <? rp then 9 else 1))%Z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) (Z_to_bv 64 rp)
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd99f4) fct None m (seg_rom usegs))).
{ intros sh Hsh. rewrite <- Hsh in HB.
assert (Hsh2 : (sh = 1 \/ sh = 9)%Z) by (destruct (45 <? rp)%Z; lia).
destruct (df_dnk_loop FUEL_RING z sh _) as [[kk carry a1 i rp1 xx]|] eqn:HDK; [|discriminate HB]. unfold FUEL_RING in HDK.
zs. (brf K6; [ exfalso; lia | ]).
zs. zs. fixw3. replace (sh + e2)%Z with (e2 + sh)%Z by lia. zs. zs. zs. zs. zs. zs. zs. zs.
let v17 := getreg 17%Z in
replace v17 with (Z_to_bv 64 (2 ^ sh - 1)%Z) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
let v7 := getreg 7%Z in
replace v7 with (Z_to_bv 64 (Z.shiftr 1000000000 sh)) by (destruct Hsh2 as [E|E]; rewrite E; apply Z_to_bv_eqm; vm_compute; reflexivity).
stmt HS_NK. eapply (NX 2050%nat) with (x := x) (h := h) (w := w) (k := a) (carry := 0%Z) (a := a) (i := iq) (rp := rp) (z := z) (sh := sh) (e2 := (e2 + sh)%Z) (B := (rp - 18450)%Z) (s1 := mkDK kk carry a1 i rp1 xx);
[mk_dfinv | assumption | assumption | exact (conj LW' (conj LX REL)) | exact X31H | lia | lia | lia | rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; lia | exact Naz | lia | exact Hsh2 | cbn; lia | exact Rw | lia | lia | exact HDK | ].
intros m' ws' b96' y17 y28 y29 y30 y31 w' DI2 XR2 X312 Ra1 Rc1 Rrp1 Rw1 Hk1; cbn [dk_x dk_a dk_carry dk_rp dk_k] in DI2, XR2, X312, Ra1, Rc1, Rrp1, Rw1, Hk1 |- *.
eapply (HS_N484 fo IH (mkDK kk carry a1 i rp1 xx)); try eassumption; try lia; cbn [dk_x dk_a dk_carry dk_rp dk_k]; try lia.
all: try (revert HB; destruct (nz carry); [destruct (negb ((z + 1) mod 2048 =? a1)%Z) |]; intros HB; exact HB).
all: show_goal. }
zs. fixw2. fixw. zs. zs. brs K5.
- zs. eapply GC. replace (45 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- zs. zs. eapply GC. replace (45 <? rp)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

End Floatscan.
End Mq9.

Module Mqa.

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
Local Notation S_M := (@QHB6.Mq3.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@QHB6.Mq3.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
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

Hypothesis HS_M : S_M.

#[using="Type"] Lemma df_pad_loop_step : forall n k j x, df_pad_loop (S n) k (j, x) = if (j <? 9)%Z then df_pad_loop n k (df_pad_body k (j, x)) else Some (j, x).
Proof. reflexivity. Qed.

#[using="Type"] Lemma df_pad_loop_pow : forall (n : nat) (j k : Z) (x : list Z) jx,
(1 <= j <= 9)%Z -> (0 <= k < zlength x)%Z -> (0 <= znth x k)%Z -> (znth x k * 10 ^ (9 - j) < 2^32)%Z ->
df_pad_loop n k (j, x) = Some jx ->
length (snd jx) = length x /\ znth (snd jx) k = (znth x k * 10 ^ (9 - j))%Z /\ (forall i, i <> k -> znth (snd jx) i = znth x i).
Proof.
clear. induction n as [|n IH]; intros j k x jx Hj Hk Hx Hb HL; [discriminate HL|].
rewrite df_pad_loop_step in HL. destruct (Z.ltb_spec j 9) as [Hlt|Hge].
- unfold df_pad_body in HL.
assert (P1 : (10 ^ (9 - j) = 10 * 10 ^ (9 - (j + 1)))%Z) by (replace (9 - j)%Z with (Z.succ (9 - (j + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (j + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (E10 : u32 (znth x k * 10) = (znth x k * 10)%Z) by (unfold u32; apply Z.mod_small; nia).
rewrite E10 in HL.
destruct (IH (j + 1)%Z k (zupd x k (znth x k * 10)%Z) jx ltac:(lia)
ltac:(unfold zlength in *; rewrite zupd_length; lia)
ltac:(rewrite znth_zupd_eq by lia; lia)
ltac:(rewrite znth_zupd_eq by lia; rewrite P1 in Hb; lia) HL) as (L1 & L2 & L3).
split; [rewrite L1; apply zupd_length|]. split.
+ rewrite L2. rewrite znth_zupd_eq by lia. rewrite P1. lia.
+ intros i Hi. rewrite (L3 i Hi). apply znth_zupd_neq. lia.
- injection HL as <-. cbn [snd]. replace (9 - j)%Z with 0%Z by lia. rewrite Z.pow_0_r, Z.mul_1_r. auto.
Qed.

#[using="pre"] Lemma L_PADL : forall (n : nat) m (x1 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (i v : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
Z.of_nat n = (9 - i)%Z -> (1 <= i <= 8)%Z -> (0 <= v)%Z -> (v * 10 ^ (9 - i) < 2^32)%Z ->
(evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (v * 10 ^ (9 - i))) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9408) fct None m (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 (Z_to_bv 64 v) (Z_to_bv 64 10) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 (i - 9)) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd93fc) fct None m (seg_rom usegs)).
Proof.
induction n as [|n IH]; intros until v; intros DI Hn Ri Rv Hb CONT; [lia|].
pose proof DI as DI'. dest_dfinv DI'. bury_disj.
assert (P1 : (10 ^ (9 - i) = 10 * 10 ^ (9 - (i + 1)))%Z) by (replace (9 - i)%Z with (Z.succ (9 - (i + 1)))%Z by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - (i + 1)))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Rv10 : (0 <= v * 10 < 2^32)%Z) by nia.
zs. fixw3. fixw. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Hi7 : i <> 8%Z) by (clear -K1 Ri; mlia).
replace (i - 9 + 1)%Z with ((i + 1) - 9)%Z by lia.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 b96 ev ws sign (i + 1)%Z (v * 10)%Z);
[exact DI | lia | lia | lia | rewrite P1 in Hb; lia | ].
replace (v * 10 * 10 ^ (9 - (i + 1)))%Z with (v * 10 ^ (9 - i))%Z by (rewrite P1; lia). apply CONT.
- assert (Ei : i = 8%Z) by (clear -K1 Ri; mlia). subst i.
replace (Z_to_bv 64 (8 - 9 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
replace (v * 10)%Z with (v * 10 ^ (9 - 8))%Z by (change (10 ^ (9 - 8))%Z with 10%Z; lia). apply CONT.
Qed.

#[using="T0 T1 SPLO SPF SPF2 SPT SG1 Q1 HS_M"] Lemma L_P : S_P.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rj Rk Hx0 Rlnz Rrp Hxk Hkj Hkj45 HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_pad in HK. unfold nz in HK. rewrite (s32_id lrp) in HK by lia.
pose proof LOW as LOWw. lo96w LOWw. rewrite le_bytes_to_word_le8 in LOWw.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Ej : j = 0%Z) by (clear -K1 Rj; mlia).
rewrite Ej, Z.eqb_refl in HK. cbn [negb] in HK. cbv beta iota in HK.
assert (Hk1 : (1 <= kz)%Z) by (destruct (Z.eq_dec kz 0) as [E|]; [exfalso; apply Hx0; apply Hkj; [exact E | exact Ej] | lia]).
zs. try rewrite le_bytes_to_word_le8.
stmt HS_M. eapply NX; [exact DI0 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | exact X31H | lia | exact Hx0 | lia | lia | exact HK].
eapply xrel_iff; [| exact (conj LW' (conj LX REL))]. intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia. left. lia.
- assert (Hj : j <> 0%Z) by (clear -K1 Rj; mlia).
replace (j =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HK.
destruct (df_pad_loop 10 kz (j, x)) as [jx|] eqn:HL; [|discriminate HK]. cbv beta iota in HK. destruct jx as [j' x']. cbn [snd] in HK |- *.
specialize (Hxk Hj). pose proof (X31H kz) as Rt.
assert (P10 : (10 ^ j <= 10 ^ 8)%Z) by (apply Z.pow_le_mono_r; lia).
assert (P9 : (10 ^ j * 10 ^ (9 - j) = 1000000000)%Z) by (rewrite <- Z.pow_add_r by lia; replace (j + (9 - j))%Z with 9%Z by lia; reflexivity).
assert (P2 : (1 <= 10 ^ (9 - j))%Z) by (change 1%Z with (10 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
assert (Hb : (0 <= znth x kz * 10 ^ (9 - j) < 1000000000)%Z) by nia.
destruct (df_pad_loop_pow 10 j kz x (j', x') ltac:(lia) ltac:(unfold zlength; lia) ltac:(lia) ltac:(lia) HL) as (L1 & L2 & L3). cbn [snd] in L1, L2, L3.
set (v' := (znth x kz * 10 ^ (9 - j))%Z) in *.
assert (Kin : digz kz j kz) by (unfold digz; right; right; split; [reflexivity | exact Hj]).
pose proof (REL kz ltac:(lia) Kin) as Et.
pose proof (u32arr_read usegs _ _ _ kz _ _ XW (nth_error_wnth ws kz ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. try rewrite le_bytes_to_word_le8. brs K2.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws kz (znth x kz) (eq_sym Et) Rt).
zs. zs.
replace (j + -9)%Z with (j - 9)%Z by lia.
eapply (L_PADL (Z.to_nat (9 - j)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 _ ev ws sign j (znth x kz));
[exact DI0 | lia | lia | lia | lia | ].
fold v'.
pose proof (u32arr_store_ok usegs _ _ _ kz _ XW ltac:(lia) eq_refl) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ kz (Z_to_bv 64 v') XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
zs. fixw3. fixw. zs.
stmt HS_M. eapply NX; [mk_dfinv | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | | | lia | | lia | lia | exact HK].
+ split; [rewrite upd_length; exact LW'|]. split; [rewrite L1; exact LX|].
intros i Hi Hr. unfold inring in Hr. rewrite !Z.sub_0_r, !Z.mod_small in Hr by lia.
destruct (Z.eq_dec i kz) as [->|Hne].
* rewrite L2. rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
* rewrite (L3 i Hne). rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia.
+ intros i. destruct (Z.eq_dec i kz) as [->|Hne]; [rewrite L2; lia | rewrite (L3 i Hne); apply X31H].
+ destruct (Z.eq_dec 0 kz) as [E0|Hne]; [| rewrite (L3 0%Z Hne); exact Hx0].
subst kz. rewrite L2. subst v'. clear -Hx0 Rt P2. nia.
Qed.

End Floatscan.
End Mqa.

Module Mqb.

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
Local Notation S_A64 := (@QHB6.Mq3.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq3.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9C8 := (@QHB6.Mq3.S_9C8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_LZ := (@QHB6.Mq3.S_LZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_990 := (@QHB6.Mq3.S_990 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@QHB6.Mq3.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Hypothesis HS_A64 : S_A64.
Hypothesis HS_7F4 : S_7F4.

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

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_9C8 : S_9C8.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
-
assert (N46 : c <> 46%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
unfold dfK_rz in HK. replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46). cbv beta iota in HK.
stmt HS_A64. eapply NX; try eassumption; try lia. mk_winv2.
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
(Z_to_bv 64 53) (Z_to_bv 64 1) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8fe0) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2.
stmt HS_9EC. eapply NX with (gotdig := 1%Z) (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HK HRZ.
zs.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ | exfalso; lia ]).
zs. zs0. read_char f. zs.
eapply JOIN. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_LZ : S_LZ.
Proof.
unfold QHB6.Mq3.S_LZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst HL HK.
dest_winv WI. bury_disj.
rewrite df_lz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (HEAD : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8fa0) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1, HL.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w8 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) 1%Z g' c' f');
try eassumption; try lia. }
assert (EXIT : forall m2 (x1' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8fbc) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', c', f') = (1%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
stmt L_9C8. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
- pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJ SLOW Hst.
set (c'' := fst (sh_getc f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
- pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_990 : S_990.
Proof.
intros n m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_LZ as NX. unfold QHB6.Mq3.S_LZ, QHB6.Mq3.SLZn in NX. eapply (NX n); try eassumption; try lia. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
assert (E : (g', c', f') = (1%Z, c, f)).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_lz_loop_step in HL.
replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-. reflexivity. }
injection E as -> -> ->. clear HL.
zs. stmt L_9C8. eapply NX; try eassumption; try lia. mk_winv2.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_9EC HS_A64"] Lemma L_848 : S_848.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite (decfloat_split fuelc 53 (-1074) sign pok) in HK.
destruct fuelc as [|fu] eqn:Efu in HK; [discriminate HK|]. rewrite df_lz_loop_step, Z.eqb_refl in HK.
set (g := sh_unget f) in *.
destruct (df_lz_loop fu _) as [[[g' c'] f']|] eqn:HL; [|discriminate HK].
assert (Hg : RFJ' (kmin - 1) 48 g /\ sh_stdio g = sh_stdio f0 /\ sh_buf g = txt).
{ subst g. split; [|split; [unfold sh_unget; destruct (sh_shlim_neg f); exact Hst | unfold sh_unget; destruct (sh_shlim_neg f); exact Hbuf]].
apply (RFJ_rechar (kmin - 1) c); [apply (RFI_unget T txt p J Hp kmin c f RJ); lia | lia |].
intros E. rewrite (rf_unget_eq f (proj1 (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)))). cbn.
destruct (NS ltac:(unfold sh_unget in E; destruct (sh_shlim_neg f); exact E)) as (_ & N2 & _). lia. }
destruct Hg as (RJg & Hstg & Hbufg).

assert (CONT : forall m2 (x10' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws g ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (T + sh_rpos g)) (Z_to_bv 64 sign) x10' x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8e50) fct None m2 (seg_rom usegs))).
{ intros m2 x10' WI2. clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL BFC.
pose proof WI2 as WI3. dest_winv WI3.
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC.
pose proof (RFI_rpos T txt p J Hp (kmin - 1) 48 g RJg) as Rrpg.
assert (RRg : (0 <= rf_rend T p true g <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio g); unfold zlength in *; lia). unfold M64 in RRg.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin - 1) 48 g RJg ltac:(lia)) as RJ1.
pose proof (getc_stdio g) as Hst1. rewrite Hstg in Hst1.
assert (Rc' : (-1 <= fst (sh_getc g) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 g Hbufg) as [Rrp1 Rrp2].
zs. replace (Z_to_bv 64 (-18446744073709550542)) with (Z_to_bv 64 1074) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]). fold zero0.
pose proof (lo64_range zero0) as R0l. pose proof (hi64_range zero0) as R0h.

assert (JOIN : forall m3 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x28' x29' x30' x31' : word),
winv m3 j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc g)) ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sign) (Z_to_bv 64 (fst (sh_getc g))) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8f84) fct None m3 (seg_rom usegs))).
{ intros until x31'. intros WI4.
stmt L_990. eapply (NX fu) with (kmin := (kmin - 1 + 1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia). rewrite Efu. exact HK. }
zs.
destruct (Z.eq_dec (T + sh_rpos g)%Z (rf_rend T p true g)) as [SLOW|FAST].
+ pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
zs. zs. call_shgetc FC0 RJg SLOW Hstg.
eapply JOIN. mk_winv2.
+ pose proof (rf_getc_fast_lt T txt p J Hp (kmin - 1) 48 g RJg ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp (kmin - 1) 48 g RJg FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos g) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0. read_char g. zs.
eapply JOIN. mk_winv2. }

pose proof FC as FC0. ufc2 FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
-
assert (Eg : g = f) by (subst g; apply rf_unget_nop; exact SN).
zs. zs. zs. (brf K0; [ | exfalso; lia ]).
replace (Z_to_bv 64 (T + sh_rpos f)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; reflexivity).
eapply CONT. rewrite Eg. mk_winv2.
- assert (Eg : g = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) by (subst g; apply rf_unget_eq; exact SN).
clear FC0.
zs. zs. zs. (brf K0; [ exfalso; lia | ]).
zs. zs0.
replace (Z_to_bv 64 (T + sh_rpos f + -1)) with (Z_to_bv 64 (T + sh_rpos g)) by (rewrite Eg; cbn [sh_rpos]; f_equal; lia).
eapply CONT. rewrite Eg. unfold QHB6.Mq3.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite SN. unfold rf_rend in FC. hyp_cells.
Qed.

End Floatscan.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QmBS.Mq6 Qlfl QHB6.Mq4 Qkaz.Mq8 Qlfl.Mq7 QHB6.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : RAMP_AS ram_pre.

Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Definition rHAG_stmt : Prop :=
forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
rmrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv usegs m3 -> stk usegs m3 lo (bv_unsigned sp + -144) ->
rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
rw_cells usegs m3 (errno_addr tp) [C4 errv'] -> rauxv_ok m3 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (ag_body f sc req k bail st2 mm) s' Q
(MS (rag_regs (Z_to_bv 64 0xd125c) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) t3' t4' t5' t6')
F (Z_to_bv 64 0xd1268) fc None m3 (seg_rom usegs)).
Hypothesis HAG : rHAG_stmt.

#[using="RC__ TP"] Lemma rerrno_lit2 : errno_addr tp = 0x62547c.
Proof. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="RC__ m MR"] Lemma rconc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="m ER MR"] Lemma rta_fp_malloc_fp stE mE a :
rmrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right.
pose proof (AREAS q MSq) as MSq'.
destruct (rmeta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. split; [exact H0|]. split; [exact K0|].
rewrite (rconc_meta_stable stE q REL MSq) in L0, H0'. lia.
- do 3 right. left. pose proof MR as (WF & _).
destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
rewrite Cb in Xq. lia.
Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_image a : 0x10000 <= a < 0x647000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _).
destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

#[using="RC__ m sc MR CLO LO"] Lemma rta_fp_not_high a : bv_unsigned sp <= a -> ~ rta_fp st lo (bv_unsigned sp) a.
Proof.
pose proof (RAS_STACK_ge sc) as ASG. unfold alloc_ceiling in CLO.
intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- unfold RCTX in X. lia.
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). lia.
- pose proof MR as (WF & _). destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in RC. lia.
Qed.

#[using="UA"] Lemma runk_agree_keep stE mE :
s_shadow stE = s_shadow st ->
(forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
(forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
(forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
unk_agree stE o mE.
Proof.
intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
pose proof (ERG rid r Hk Hr) as Hr0.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

#[using="RC__ m MR CLO"] Lemma rta_fp_not_inband rid r off :
(s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
~ rta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
intros Hr Hk Ho NG. pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC, CLO.
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- lia.
- destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

#[using="st0 LB errv AR IS ER AC SC MR TK UA BL AUX CLO LO ERR TP HK F0 ram_pre AM AMP HAG"] Lemma rag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m1 -> mem_inv usegs m1 -> rw_cells usegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk usegs m1 lo (bv_unsigned sp + -144) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m1 ->
rimplT o (as_grp full_lay f sc req k bail st1) s Q
(MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1244) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. unfold alloc_ceiling in CLO'.
pose proof rerrno_lit2 as EA.
pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
rewrite (as_grp_eq f sc req k bail st1).
riprefixT. unfold rag_regs.
eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
cbv beta. intros ms' ->. apply evt_done. unfold rt1_regs.

assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
assert (BL1 : brk_link_ps st1 s).
{ unfold brk_link_ps in *. unfold ctx in *. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
assert (AUX2 : rauxv_ok m1 (bv_unsigned sp + -144)).
{ apply (rauxv_ok_weaken m1 (bv_unsigned sp)); [| unfold alloc_ceiling; lia]. eapply rauxv_ok_pres; [exact AUX| exact PE1| |].
- intros a Ha. apply rta_fp_not_high. exact Ha.
- intros a Ha. apply rta_fp_not_image; unfold RAUXV_CELL, RCTX in *; lia. }
assert (ERR2 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply rta_fp_not_image; [lia| unfold RCTX; lia]. }
eapply (ralloc_meta_stmtL ram_pre AM) with (lo := lo);
[ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2
| rewrite unsigned_lit by lia; exact ST1 | exact CLO
| rewrite unsigned_lit by lia; unfold RAM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
intros st2 mo s' ms' PO BL2 LF.
destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL & E12).
rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
replace (ret_pc (Z_to_bv 64 0xd125c)) with (Z_to_bv 64 0xd125c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof MR3 as (WF3 & _). pose proof WF3 as (RS3 & WR3 & DJ3 & _).

assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x647000 /\ ~ (RCTX <= a < RCTX + 928) /\ ~ (0x62547c <= a < 0x625480)) ->
~ (ralloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
{ intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. lia.
- unfold RCTX in *. lia.
- destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF'). pose proof (lr_lo_ge rq2). unfold alloc_ceiling in BC.
pose proof (rreserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4). pose proof (round_up_pg_ge (r_len rq2)). lia.
- destruct X as [XC XF]. unfold alloc_ceiling in XC.
pose proof (rfresh_image st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM junk)).
{ eapply rpres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, rta_frame in Ha. cbn in Ha. lia. }

assert (REL02 : mrel st st2).
{ split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _). exists r'. auto. }
assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
{ intros q (ar & arr & kk & Ha & Hk & E). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
exists ar, arr', kk. auto. }
assert (PE03 : rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans.
- eapply rpres_except_mono; [exact PE1|]. intros a Ha. eapply (rta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
- eapply rpres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
+ left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
+ do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
* rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
* intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L'). exists r'. rewrite REG1. auto. }

assert (UA3 : unk_agree st2 o m3).
{ eapply (runk_agree_keep st2 m3).
- rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
- intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
+ destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G'). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
+ exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
- intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
- intros rid r off h Hr Hk Ho Hc NG.
destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _). unfold alloc_ceiling in RC.
transitivity (m1 (wa (r_base r + off))).
+ refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
* lia.
* rewrite unsigned_lit in X by lia. destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2).
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
* destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
* assert (Hr2 : (s_regions st2) !! rid = Some r).
{ rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G'). rewrite H'. f_equal. apply G'. exact Hk. }
assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
* rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
+ refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (rta_fp_not_inband rid r off Hr Hk Ho NG). }
destruct mo as [mm|].
-
destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
pose proof (rmeta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _).
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := conc st2 mm); [unfold alloc_ceiling in GC; lia| exact MI3]. }
cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
apply evt_done.
eapply (HAG st1 st2 mm m3 s'); try eassumption.
+ eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
+ eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
+ eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
+ eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
-
cbn iota.
riprefixT. eapply evt_cut.
{ unfold pw. cbn [oconc]. unfold wz. eapply rag_ret_walk with (gm := 0); [lia| exact MI3]. }
cbv beta. intros ms' ->. cbn [Z.eqb].
eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
cbv beta. intros ms' (a1x & a2x & -> & ST4). apply evt_done.
apply HK. unfold ras_post2.
do 14 eexists. exists m3, errv3. split; [reflexivity|].
split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
split. { eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
split. { constructor.
- intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
- intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
- rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
- intros H; exfalso; lia.
- intros _ H; exfalso; lia. }
split. { rewrite (amr_counter _ _ _ REL). unfold ctx. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
left. split; [reflexivity| exact (E12 eq_refl)].
Qed.
End LEVEL.

End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Qy5Y.Mq6 QPjm.Mq2 QFkE Q6y7 QJE4.Mq2 Q3o5.Mq0 QULt.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq4 QdZ1.Mq8 QmBS.Mq8 QdZ1.Mq6 Qlfl.Mq8.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rauxv_ok_pres_B : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 6444156 <= a < 6444160) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 6444156 <= a < 6444160.

#[using="RC__ m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof.
intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- pose proof (rfree_fp_lt (RC__:=RC__) st m lo sp a MR ltac:(unfold alloc_ceiling; lia) LS FP). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- lia.
Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_img a : 0xe4000 <= a < 0x647000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (6444156 <= a < 6444160) -> ~ FPT a.
Proof.
intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ exact (N1 X).
+ destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
+ destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
+ destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- exact (N2 ER).
Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_image a : 0xe4000 <= a < 0x647000 -> ~ ralloc_static a -> ~ FPT a.
Proof.
intros Ha NS. apply rfp_not_img; [exact Ha| |]; intros X; apply NS; unfold ralloc_static, RLIBC, RMLOCK, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP in *; lia.
Qed.

#[using="RC__ m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof.
intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
destruct (UNK a Hab) as [h UNKa].
destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). unfold alloc_ceiling in RGC.
pose proof (lr_lo_group rg Krg) as LRG.
intros [FP|[DR|ER]].
- destruct FP as [[X|[X|X]]|[X|X]].
+ lia.
+ unfold RCTX in X. lia.
+ destruct X as (rid & r & Hr & NK & Hin).
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
destruct (DJ _ _ _ _ Hr Hrg NE); lia.
+ destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
* specialize (HD b gh Hb E). unfold IB in HD. lia.
* destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
+ destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
* rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
* pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
- lia.
Qed.

#[using="RC__ st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof.
intros HLB a Ha CA. apply PE; [exact Ha|].
destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
- apply rfp_not_high. exact CA.
- apply rfp_not_image; assumption.
- apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof.
intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
- intros a Ha. apply rfp_not_high. lia.
- intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

#[using="Type"] Theorem rfree_impl_spec_proof : rfree_impl_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
HP Hin AV HB ST LO SLO ERR MI TP A0.
destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
pose proof (QNAo.Mq2.areach_cinv_proof _ _ AR) as C.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
cbn [blk_addr blk_slot fst snd] in OA.
pose proof (Q3o5.Mq1.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
eapply (rraw_free_bridge st s p (aadd (blk_slot (p, A, n)) (UNIT * off)) m
(fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
/\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
- exact Hst.
- exact HOK.
- apply rimplT_reach.
apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
[unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
- intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
unfold rfree_post. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
split; [reflexivity|]. split; [reflexivity|].
exists st', (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
split; [reflexivity|]. split; [exact MR'|]. split.
+  unfold brk_link. cbn [ps_brk set_m]. rewrite EB. unfold brk_link in BL.
destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
rewrite ?HB0 in BL. unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
+ destruct LEAF as (ans & o' & FO).
eapply (areach_free st LB0 (p, A, n) (aadd (blk_slot (p, A, n)) (UNIT * off)) m o' ans st' AR Hin0); [reflexivity| | exact FO].
cbn [blk_addr blk_slot fst snd]. rewrite OA, conc_aadd; [reflexivity|].
cbn [fst]. rewrite <- FB. destruct (go_region _ _ _ (ci_gmetas _ _ C b g HBg)) as (r & Hr & _). rewrite Hr. eexists; reflexivity.
Qed.

#[using="Type"] Theorem rfree_spec_proof : rfree_stmt.
Proof. exact (rfree_stmt_of_impl rfree_impl_spec_proof). Qed.

End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Q4J3.Mq3 Qnxq QPjm.Mq4 QBpc QNAo.Mq1 QULt.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq.Mq4.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rregion_addr_facts : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
4096 <= r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (0 < round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x647000 <= r_base r).
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
clear RFr. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma rblock_inside st LB m blk :
MFACTS_g (resv:=ref_reserved) st LB -> rmrep st m -> In blk LB ->
exists r g idx, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
/\ (s_slots st) !! (blk_slot blk) = Some (g, idx)
/\ r_base r <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
/\ 0 <= blk_size blk
/\ 4096 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x647000 <= r_base r).
Proof.
intros MF MR IN.
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
destruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
destruct BR as (r & Hr & Hk).
pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
exists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
pose proof (round_up_pg_ge (r_len r)) as RU.
rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
rewrite Esnd in EA. unfold alloc_ceiling in *.
assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof.
intros s LB m (st & LB0 & HP & _ & _ & [_ AR]). pose proof (mf_nodup _ _ (QTyG.Mq2.areach_facts_proof _ _ AR)) as ND.
eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
inversion ND; subst. constructor; [|apply IH; assumption].
intros HI. apply H1. apply in_map_iff in HI. destruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof.
intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
destruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
destruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
assert (32 <= round_up_pg (r_len r)) by nia.
unfold rblock_range. unfold alloc_ceiling in *. split; [lia|]. split; [|lia].
rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_disjoint_proof : forall s LB m b1 b2,
RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros s LB m b1 b2 (st & LB0 & HP & _ & MR & [_ AR]) I1 I2 NE. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
- exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
+ exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
+ exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
- destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
+ exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
+ destruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
destruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
pose proof MR as (WF & _). pose proof WF as (_ & _ & DJ & _).
pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

#[using="Type"] Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
\/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ 0x646db8 <= a < 0x646db8 + 4 \/ a < 0x10000 \/ 0x647000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="Type"] Lemma RHEAP_frame_proof : forall s LB m m' W,
RHEAP s LB m -> munch W m m' -> wmono usegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.
Proof.
intros s LB m m' W (st & LB0 & HP & Hst & MR & HI) MU WM FW. exists st, LB0. split; [exact HP|]. split; [exact Hst|].
split; [|exact HI].
destruct HI as [_ AR]. pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
eapply (rmrep_transport_unowned st m m' W MR MU WM).
intros lo hi a Hin Ha RF.
pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
destruct (rrepfoot_where st m a MR RF) as [AC AW].
destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
- unfold alloc_ceiling in *. lia.
- unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD, RVMLOCK, alloc_ceiling in *. lia.
-
assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
destruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
+ unfold RCTX in R1. lia.
+ unfold RMLOCK in R2. lia.
+ unfold RNEED_LOCKS in R3. lia.
+ unfold RPAGE_SIZE in R4'. lia.
+ destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
destruct (DJ _ _ _ _ Hra Hr NEr); lia.
+ destruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
* rewrite E, Hr in Hrb. inversion Hrb; subst rb.
pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
* pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
+ destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
* rewrite Hr in Hq. inversion Hq; subst rq.
destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
* pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
+ unfold RGOT_SSP in R8. lia.
+ unfold RSSP_GUARD in R9. lia.
Qed.

#[using="Type"] Lemma reservedZ_ref : reservedZ usegs = ref_reserved.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells usegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
u64arr usegs m A (repeat (wz 0) k).
Proof.
intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.
End RC__1.

Ltac rimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells usegs m A cs);
[ apply (rw_cells_recast usegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 usegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

End RC__2.
End Mqe.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnOf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn9M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqh.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmrep_ext : forall st st' m,
rmrep st m ->
s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
s_reserved st' = s_reserved st ->
rmrep st' m.
Proof.
intros st st' m (WF & CX & GL & AR & GR & SH) ER EC EM EA EG ES ERs.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
split; [|split; [|split; [exact GL|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. exact WF.
- eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
- intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^63.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
rewrite G0. reflexivity.
Qed.

#[using="Type"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="Type"] Lemma rbf_regions : s_regions stF = s_regions st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_areas : s_areas stF = s_areas st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof. reflexivity. Qed.
#[using="GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
rewrite GN. reflexivity.
Qed.
#[using="Type"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
#[using="Type"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite rbf_ctx. reflexivity. Qed.

#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof.
intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
- exact rbf_ctx.
- intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
- rewrite rbf_groups, rbm_groups. reflexivity.
Qed.

#[using="Type"] Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

#[using="NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

#[using="Type"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

#[using="Type"] Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ (RMLOCK <= a < RMLOCK + 4 \/ 0x646db8 <= a < 0x646db8 + 4) \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x647000 <= a).
Proof.
intros MR RF. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
- lia. - lia. - lia. - lia.
- destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. unfold alloc_ceiling in RBC.
pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. unfold alloc_ceiling in RC. lia.
- lia. - lia.
Qed.

#[using="Type"] Lemma rwrapper_munch_keeps st m m' (spv lo : Z) :
rmrep st m -> munch [(spv - 80, spv); (0x62547c, 0x62547c + 4)] m m' -> wmono usegs m m' -> alloc_ceiling <= spv - 80 ->
rmrep st m'.
Proof.
intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; unfold alloc_ceiling, RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof.
intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

#[using="Type"] Lemma rfp_below_ceiling K st3 stx m lo spv a :
rmrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (ralloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
- rewrite unsigned_lit in X by lia. unfold alloc_ceiling in H2. lia.
- unfold RCTX, alloc_ceiling in *. lia.
- pose proof MR as (WF & _). pose proof WF as (_ & WR & _). destruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.

#[using="Type"] Lemma rbig_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

#[using="Type"] Lemma rregion_facts_hi : forall st m rid r,
rmrep st m -> (s_regions st) !! rid = Some r ->
r_base r + round_up_pg (r_len r) <= 0xea000 \/ 0x647000 <= r_base r.
Proof.
intros st m rid r (WF & _) Hr. pose proof WF as (_ & WR & _).
destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.

Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

#[using="Type"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved rc_secret).
Proof.
intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (QULt.Mq1.areach_ampre_proof _ _ AR)|].
unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

#[using="ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof.
pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).

riprefixT. unfold alloc_ceiling in CLO. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
unfold RMLOCK.
step. step. step. step. step. step. step. step. step.
apply evt_done.
set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
eapply rimplT_mmap_rw.
{ eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
[ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
| reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rewrite Q9A7.Mq0.alloc_ceiling_val; lia
| rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
intros ans ms' PO.
assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (6444320 + -164, 6444320 + -164 + 4)] m1 m2 -> wmono usegs m1 m2 ->
rw_cells usegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
{ intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
- eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
- eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| unfold alloc_ceiling; lia].
eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
- eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
- eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
- eapply unk_agree_munch; [exact UA1| exact MU| |].
+ intros rid r Hr Hk. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. unfold alloc_ceiling in R2. cbn. lia.
+ intros rid r Hr. pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). unfold alloc_ceiling in R2. lia. }
destruct ans as [e|xa].
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He).
cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e ltac:(clear -He; lia)) as [-> ->]. cbn [negb].
apply rimplT_ret.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
replace (ret_pc (Z_to_bv 64 0xd0d8c)) with (Z_to_bv 64 0xd0d8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
exists m2, (Z_to_bv 64 (Q9A7.Mq0.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
split; [apply mrel_same; reflexivity|]. split; [exact BL|]. rewrite He. repeat split; reflexivity.
-
cbn [rmmap_anon_post] in PO.
destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK).
cbn [mmap_val].
destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
2:{ cbn [negb]. apply rimplT_undef. }
cbn [negb].
destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).

unfold new_region.
set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
assert (PT1 : ptrs_in (fun r => r <> rid) st1).
{ eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
set (L := mmap_len (n + IB + UNIT)).
assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
unfold Q9A7.Mq0.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. unfold alloc_ceiling in XC. unfold IB, UNIT in LG.
set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
{ intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
{ intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
assert (MRz : rmrep st2 mz).
{ rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
rewrite <- ?EL; [unfold alloc_ceiling; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
fold mz in ST2 |- *.

pose proof MR1 as (WF1 & _). pose proof WF1 as (RS1 & WR1 & _).
assert (XI : xa + L <= 0x10000 \/ 0x647000 <= xa).
{ assert (RFimg : ranges_free ref_reserved xa L = true).
{ apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
apply (rreserved_disjoint1 _ _ RFimg). lia. }
assert (MIz : mem_inv usegs mz).
{ unfold mz. apply (mem_inv_zeros usegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
assert (FRz : rw_cells usegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
assert (UAz : unk_agree st2 o mz).
{ eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
- right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
- left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
intros off h Ho Hc NG. destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }

riprefixT.
replace (ret_pc (Z_to_bv 64 0xd0d8c)) with (Z_to_bv 64 0xd0d8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
pose proof (mf_ctx _ _ MF) as FC. destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
eapply evt_cut.
{ eapply (rbig_seq_walk sp gp (Z_to_bv 64 6444320)) with (st := st2) (lo := lo);
[exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| unfold alloc_ceiling; lia| exact MIz]. }
intros ms1 (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3).
apply evt_done.

assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
assert (WMz : wmono usegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono usegs m2 xa L); try lia; exact Hw).
assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
{ eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
assert (ERRz : rw_cells usegs mz (6444320 + -164) [C4 errv]).
{ eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
assert (ERR3 : rw_cells usegs m3 (6444320 + -164) [C4 errv]).
{ eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
assert (BL2 : brk_link_ps (step_seq st2) s).
{ eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
apply Hconc2. cbn. destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
eapply AM.
{ apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
{ exact MR3. }
{ exact TK2'. }
{ exact BL2. }
{ rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| unfold alloc_ceiling; lia]. }
{ rewrite SP'. exact ST3. }
{ unfold alloc_ceiling; lia. }
{ rewrite SP'. unfold RAM_STACK. lia. }
{ unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
{ exact MI3. }
{ reflexivity. }
intros st3 mo s' ms' PO3 BL3.
destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL & E12).
rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
replace (ret_pc (Z_to_bv 64 0xd0e80)) with (Z_to_bv 64 0xd0e80) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells usegs m4 (bv_unsigned sp + -48) cs) end.
{ eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| unfold alloc_ceiling; lia]. }
assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
{ destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
assert (PT3 : ptrs_in (fun q => q <> rid) st3).
{ apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
pose proof MR4 as (WF4 & _ & (ML4 & _) & _). pose proof WF4 as (RS4 & WR4 & DJ4 & _).
assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.

assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
(forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
{ intros stF RSF HFP.
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
{ transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
destruct mo as [g|].
+
apply rimplT_ret.
destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
pose proof (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
set (G := conc st3 g) in *.
assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; unfold alloc_ceiling in GC; lia).
assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
{ intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
{ intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
assert (SHN3 : (s_shadow st3) !! rid = None).
{ rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. exact FRs. }
assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
{ rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2. reflexivity. }
eapply evt_cut.
{ eapply (rbig_succ_walk (RC__:=RC__) st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(unfold alloc_ceiling; lia) sp gp (Z_to_bv 64 6444320));
[exact HG| exact FR4| exact ST4| lia| exact MI4]. }
intros ms5 (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7).
apply evt_done. cbn [rcoreQ].
set (stF := big_final st3 g rid n).
rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
change (pw st3 (Some g)) with (pw stF (Some g)).
exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
split; [reflexivity|].
assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
split; [exact MRF|].
split; [exact TK7|].
assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
{ intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
split.
{
assert (UA3 : unk_agree (step_seq st2) o m3).
{ eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
intros off h Ho Hc NG. pose proof MRz as (WFz & _). pose proof WFz as (_ & WRz & _).
destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
assert (UA4 : unk_agree st3 o m4).
{ eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
{ destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
- destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
- exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). unfold alloc_ceiling in BC.
refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
- lia.
- rewrite unsigned_lit in X by lia. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
- assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
- pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
destruct (N.eq_dec q rid) as [->|NE].
- right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
- left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
split. { intros off (b & gh & Hb & Hf & Ho). exists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
intros off h Ho Hc NG. destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). unfold alloc_ceiling in BC.
pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
assert (ERR8 : rw_cells usegs m7 (6444320 + -164) [C4 errv4]).
{ eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
{ eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_trans.
{ eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
- left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
- do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
- left. right; right; left. unfold RCTX in *. lia. }
apply rpres_except_refl. }
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. exact Hr'.
- change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
split. { intros a Ha. do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
split. { unfold u32. Z.div_mod_to_equations. lia. }
assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
rewrite <- big_ml_eq in RU by lia.
split.
{  constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
- reflexivity.
- exact RR3.
- reflexivity.
- lia.
- reflexivity.
- lia.
- lia.
- rewrite <- EL. lia.
- lia.
- rewrite RU. Z.div_mod_to_equations. lia.
- lia.
- lia.
- lia.
- intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
- change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- intros off Ho Hfit. Z.div_mod_to_equations. lia.
- unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
- exact MSL.
- lia.
- lia.
- lia.
- lia.
- right. repeat split; lia. }
split. { intros _. unfold Q4J3.Mq1.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
split; [exact MRELF|].
split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
repeat split; assumption.
+
cbn [pw oconc].
riprefixT.
eapply evt_cut.
{ apply rbig_fail2a_walk. exact ML4. }
intros ms2 ->. apply evt_done.
eapply rimplT_munmap.
{ eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
[ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4
| pose proof MR4 as (_ & _ & (_ & _ & _ & _ & _ & VML4) & _); exact VML4 | unfold RVMLOCK, alloc_ceiling in *; lia | rewrite ELm; unfold RVMLOCK, alloc_ceiling in *; lia
| reflexivity | unfold IB, UNIT; f_equal; lia
| lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; unfold alloc_ceiling in *; lia
| rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
intros ans2 ms3 PM. unfold rmunmap_post in PM.
destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
rewrite (munmap_answer_ok_range ans2 ltac:(destruct ans2; cbn in He6 |- *; [lia| exact Logic.I])). apply rimplT_ret.
rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
replace (ret_pc (Z_to_bv 64 0xd0f58)) with (Z_to_bv 64 0xd0f58) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -48) cs) end.
{ eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. unfold alloc_ceiling in *. lia. }
eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
set (stF := drop_region rid st3).
assert (MRF : rmrep stF m6).
{ eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
rewrite <- EL in Hout.
assert (A1 : a < alloc_ceiling /\ (a + 1 <= 6444320 + -164 \/ 6444320 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
{ destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
[unfold RMLOCK, alloc_ceiling in *; lia| unfold RLIBC, alloc_ceiling in *; lia| unfold RGOT_SSP, alloc_ceiling in *; lia| unfold RSSP_GUARD, alloc_ceiling in *; lia|].
destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
split; [lia|]. split; [lia|].
destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
unfold alloc_ceiling in A1.
apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
{ intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
{ eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
do 4 right. split; [unfold alloc_ceiling; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
exists m6, (Q9A7.Mq0.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| unfold alloc_ceiling; lia| lia]. }
assert (MRELF : mrel st stF).
{ split.
- intros q rq Hq.
assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
{ transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
- unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
- unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
split; [exact MRELF|].
split.
{ eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
repeat split; try assumption.
destruct ans2 as [e2|b2]; cbn [Q9A7.Mq0.rg_errno]; cbn in He6; [rewrite He6; reflexivity| exact (E12 eq_refl)].
Qed.
End BIG.

End RC__1.
