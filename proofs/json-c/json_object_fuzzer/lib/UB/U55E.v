(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3 QWxq Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Lib.SepCache QnDM QDUx Q9Ay Qy5Y QPUx Q7wb U4l4 UzHs UDgQ Uwbh UGbx UB5o U4WT Ujqb UGEX UFHW UfbZ UJ2O UHhK UL4p UP89 UuJ9 UxDK Uoo0 UnKY UqYW U3qs UTgq UNt7 UUNy QCqH UEQM UmCU Uaq3 UZUm UIZl U6c3 UBDZ U970 U5dj U1dE U6b2 Uvme UxUc U6g2 UTDc UQAd UwUH UjRB UxG6 U2ON Ukhc UT19 UZ8X U16e Uucr Ukg3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM.
Import QDUx Q9Ay.
Import Qy5Y QPUx.
Import Q7wb.
Import U4l4 UzHs UDgQ Uwbh UGbx UB5o U4WT Ujqb UGEX UFHW UfbZ UJ2O UHhK UL4p UP89 UuJ9 UxDK Uoo0 UnKY UqYW U3qs UTgq UNt7 UUNy.
Import QCqH.
Import UEQM.
Export UmCU.

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
Notation RFJ' := (RFJ T txt p true J).

Local Notation ctx_all := (@UmCU.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Fok_refl := (@UmCU.Fok_refl F).
Local Notation Fok_set := (@UmCU.Fok_set F).
Local Notation fs_post := (@UmCU.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@UmCU.zbytes_len txt).
Local Notation S_F3 := (@UmCU.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F2 := (@UmCU.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F1 := (@UmCU.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A69C := (@UmCU.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A62C := (@UmCU.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A5C4 := (@UmCU.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A568 := (@UmCU.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A534 := (@UmCU.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N324 := (@UmCU.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N2D4 := (@UmCU.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_U1A8 := (@UmCU.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_NK := (@UmCU.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).
Local Notation S_N484 := (@UmCU.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N3E8 := (@UmCU.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_UK := (@UmCU.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_T := (@UmCU.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD0 := (@UmCU.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@UmCU.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_M := (@UmCU.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_P := (@UmCU.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_R := (@UmCU.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C38 := (@UmCU.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@UmCU.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@UmCU.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@UmCU.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9EC := (@UmCU.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A64 := (@UmCU.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@UmCU.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_848 := (@UmCU.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_618 := (@UmCU.S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F3 : S_F3.
Proof. apply (Uaq3.L_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F2 : S_F2.
Proof. apply (UZUm.L_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_F3 ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F1 : S_F1.
Proof. apply (UIZl.L_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_F2 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_A69C : S_A69C.
Proof. apply (U6c3.L_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_F1 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_A62C : S_A62C.
Proof. apply (UBDZ.L_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_A69C ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_A5C4 : S_A5C4.
Proof. apply (U970.L_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_A62C ]. Qed.
#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_NK : S_NK.
Proof. unfold UmCU.S_NK. intros. eapply U1dE.L_NK; first [ eassumption ]. Qed.
#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_N484 : S_N484.
Proof. apply (U6b2.L_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_N3E8 : S_N3E8.
Proof. apply (Uvme.L_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_NK | exact L_N484 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_A534 : S_A534.
Proof. apply (U5dj.L_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_A5C4 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_A568 : S_A568.
Proof. apply (U5dj.L_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_A5C4 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_N324 : S_N324.
Proof. apply (UxUc.L_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_N3E8 | exact L_A534 | exact L_A568 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_N2D4 : S_N2D4.
Proof. apply (U6g2.L_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_N324 ]. Qed.
#[using="Hp T1 SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_UK : S_UK.
Proof. apply (UTDc.L_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_U1A8 : S_U1A8.
Proof. apply (UQAd.L_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_N2D4 | exact L_UK ]. Qed.
#[using="HM Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_T : S_T.
Proof. apply (UwUH.L_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_U1A8 ]. Qed.
#[using="HM Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_M : S_M.
Proof. apply (UjRB.L_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="HM Hp T0 T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_P : S_P.
Proof. apply (UxG6.L_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_M ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD24 : S_DD24.
Proof. apply (UjRB.L_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD0 : S_DD0.
Proof. apply (UjRB.L_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="HM Hp T0 T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_R : S_R.
Proof. apply (U2ON.L_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_P | exact L_DD24 | exact L_DD0 ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E : S_E.
Proof. apply (Ukhc.L_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="HM Hpok Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_C2C : S_C2C.
Proof. apply (Ukhc.L_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="HM Hpok Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_C38 : S_C38.
Proof. apply (Ukhc.L_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_D : S_D.
Proof. apply (UT19.L_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_E | exact L_C2C | exact L_C38 ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_9EC : S_9EC.
Proof. apply (UZ8X.L_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_A64 : S_A64.
Proof. apply (UZ8X.L_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_7F4 : S_7F4.
Proof. apply (UZ8X.L_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_848 : S_848.
Proof. apply (U16e.L_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_9EC | exact L_A64 | exact L_7F4 ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_618 : S_618.
Proof. apply (Uucr.L_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_9EC | exact L_7F4 | exact L_848 ]. Qed.
#[using="HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM"] Lemma L_ENTRY : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
stk rsegs m0 (q - FS_DEPTH) q -> mem_inv rsegs m0 ->
rw_cells rsegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at rsegs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells rsegs m0 RERRNO [C4 ev] ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom rsegs)).
Proof. apply (Ukg3.L_ENTRY ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_618 ]. Qed.
End Floatscan.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma RHEAP_at_main : forall (m : mem),
(forall a : word, 0x97f78 <= bv_unsigned a < 0x98320 -> m a = None) ->
rw_cells rsegs m RNEED_LOCKS [C1 (Z_to_bv 8 0)] ->
rw_cells rsegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RSSP_GUARD)] ->
rw_cells rsegs m RSSP_GUARD [C8 rc_canary] ->
mem_inv rsegs m ->
RHEAP (ps_init_s rc_secret (reservedZ rsegs)) [] m.
Proof.
intros m NONE NL PS GOT GUARD MI.
set (st0 := minit rc_secret ref_reserved).
rimg_chunk NONE m 0x97f80%Z (ctx_head_cells st0) CXH.
rimg_chunk NONE m (0x97f80 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
rimg_chunk NONE m (0x97f80 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
rimg_chunk NONE m (0x97f80 + 848)%Z [CB 32 (zeros 32)] CXS.
rimg_chunk NONE m (0x97f80 + 880)%Z [CB 32 (zeros 32)] CXB.
rimg_chunk NONE m (0x97f80 + 912)%Z (ctx_tail_cells st0) CXT.
rimg_chunk NONE m 0x97f78%Z [C4 (wz 0)] ML.
exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init_s; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
split.
2:{ unfold ps_init_s; cbn [ps_brk]. apply HINV_from_init. exact rc_secret_range. }
split; [|split; [|split; [|split; [|split]]]].
-  split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
- unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
+ replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
+ replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
+ replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
+ replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
+ exact CXT.
- unfold rmrep_globals. split; [unfold RMLOCK; exact ML|]. split; [|split; [|split]].
+ change (b8 0) with (Z_to_bv 8 0). exact NL.
+ change (wz 4096) with (Z_to_bv 64 4096). exact PS.
+ exact GOT.
+ exact GUARD.
- intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End RC__1.
