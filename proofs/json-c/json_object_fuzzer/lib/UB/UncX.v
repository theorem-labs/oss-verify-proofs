(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3 QWxq Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n Lib.SepCache QnDM QDUx Q9Ay Qy5Y QPUx Q7wb U4l4 UzHs UDgQ Uwbh UGbx UB5o U4WT Ujqb UGEX UFHW UfbZ UJ2O UHhK UL4p UP89 UuJ9 UxDK Uoo0 UnKY UqYW U3qs UTgq UNt7 UUNy QCqH UEQM UmCU UuIP UEG5 Uaq3 UZUm UIZl U6c3 UBDZ U970 U5dj U1dE U6b2 Uvme UxUc U6g2 UTDc UQAd Uo2L UjRB UxG6 U2ON Ukhc UT19 UZ8X U16e Uucr UKPB UeFr UpKv UzhX Uhqa UGoi UgCp Utsl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM.
Import QDUx Q9Ay.
Import Qy5Y QPUx.
Import Q7wb.
Import U4l4 UzHs UDgQ Uwbh UGbx UB5o U4WT Ujqb UGEX UFHW UfbZ UJ2O UHhK UL4p UP89 UuJ9 UxDK Uoo0 UnKY UqYW U3qs UTgq UNt7 UUNy.
Import QCqH.
Import UEQM.
Import UmCU UuIP UEG5.

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
Notation RFJ' := (RFJ T txt p true J).

Local Notation ctx_all := (@UmCU.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Fok := (@UmCU.Fok F).
Local Notation Fok_refl := (@UmCU.Fok_refl F).
Local Notation Fok_set := (@UmCU.Fok_set F).
Local Notation fs_post := (@UmCU.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@UmCU.zbytes_len txt).
Local Notation txt_char := (@UmCU.txt_char txt BYT).
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
Local Notation S_6F8 := (@UmCU.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.

Ltac lia_goal P := lazymatch P with
| (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
| (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
| ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
| ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
end.
Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
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

#[using="Type"] Lemma rfj_ns : forall kmin c f, RFJ' kmin c f -> sh_stdio f = false /\ sh_shlim_neg f = false.
Proof.
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct (sh_stdio f) eqn:E.
- destruct (SS eq_refl) as (_ & _ & _ & _ & [_ FF]). destruct FF.
- split; [reflexivity|]. exact (proj1 (NS eq_refl)).
Qed.
#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof.
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

#[using="Type"] Lemma RFJ_rechar : forall kmin c c' f, RFJ' kmin c f -> (-1 <= c' < 256)%Z -> (c' <> 0%Z -> sh_rpos f <= p)%Z -> RFJ' kmin c' f.
Proof.
clear. intros kmin c c' f (OK & Rc & CC & KM & NS & SS) Hc' Hr. split; [exact OK|]. split; [exact Hc'|]. split; [exact CC|]. split; [exact KM|]. split; [|exact SS].
intros E. destruct (NS E) as (N1 & N2 & N3). split; [exact N1|]. split; [exact N2|]. exact Hr.
Qed.
#[using="Type"] Lemma RFJ_weak : forall kmin k' c f, RFJ' kmin c f -> (k' <= kmin)%Z -> RFJ' k' c f.
Proof.
clear. intros kmin k' c f (OK & Rc & CC & KM & NS & SS) Hk. split; [exact OK|]. split; [exact Rc|]. split; [exact CC|]. split; [intros E; specialize (KM E); lia|]. split; [exact NS | exact SS].
Qed.
#[using="Hp"] Lemma RFJ_ungetn : forall n kmin c f, RFJ' kmin c f -> sh_shlim_neg f = false -> (Z.of_nat n <= kmin)%Z ->
RFJ' (kmin - Z.of_nat n) c (fs_unget_loop n f).
Proof.
clear -Hp. induction n as [|n IH]; intros kmin c f RJ Hsn Hn.
- replace (kmin - Z.of_nat 0)%Z with kmin by lia. exact RJ.
- cbn [fs_unget_loop]. replace (kmin - Z.of_nat (S n))%Z with ((kmin - 1) - Z.of_nat n)%Z by lia.
apply IH; [ exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(lia)) | rewrite (rf_unget_eq f Hsn); exact Hsn | lia ].
Qed.

Local Notation S_WS := (@UuIP.S_WS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_AWS := (@UuIP.S_AWS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_I1 := (@UuIP.S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N1 := (@UuIP.S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_Z := (@UuIP.S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@UuIP.S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@UuIP.S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_PAR := (@UuIP.S_PAR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HEX := (@UuIP.S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Local Notation S_HLZ := (@UEG5.S_HLZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H778 := (@UEG5.S_H778 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H720 := (@UEG5.S_H720 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HRZ := (@UEG5.S_HRZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H7F0 := (@UEG5.S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HD := (@UEG5.S_HD ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HTL := (@UEG5.S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HE2 := (@UEG5.S_HE2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HNL := (@UEG5.S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@UEG5.S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HZR := (@UEG5.S_HZR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

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
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_T : S_T.
Proof. apply (Uo2L.L_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_U1A8 ]. Qed.
#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_M : S_M.
Proof. apply (UjRB.L_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="Hp T0 T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_P : S_P.
Proof. apply (UxG6.L_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_M ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD24 : S_DD24.
Proof. apply (UjRB.L_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD0 : S_DD0.
Proof. apply (UjRB.L_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_T ]. Qed.
#[using="Hp T0 T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1"] Lemma L_R : S_R.
Proof. apply (U2ON.L_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_P | exact L_DD24 | exact L_DD0 ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E : S_E.
Proof. apply (Ukhc.L_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_C2C : S_C2C.
Proof. apply (Ukhc.L_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_C38 : S_C38.
Proof. apply (Ukhc.L_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_R ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_D : S_D.
Proof. apply (UT19.L_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_E | exact L_C2C | exact L_C38 ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_9EC : S_9EC.
Proof. apply (UZ8X.L_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_A64 : S_A64.
Proof. apply (UZ8X.L_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_7F4 : S_7F4.
Proof. apply (UZ8X.L_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_D | exact L_E ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_848 : S_848.
Proof. apply (U16e.L_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_9EC | exact L_A64 | exact L_7F4 ]. Qed.
#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_6F8 : S_6F8.
Proof. apply (Uucr.L_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_9EC | exact L_7F4 | exact L_848 ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HFIN : S_HFIN.
Proof. apply (Utsl.L_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HNL : S_HNL.
Proof. apply (Utsl.L_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Type"] Lemma L_HZR : S_HZR.
Proof. apply (UgCp.L_HZR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_HNL | exact L_HFIN ]. Qed.
#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HE2 : S_HE2.
Proof. apply (UgCp.L_HE2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_HNL | exact L_HFIN ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_HTL : S_HTL.
Proof. apply (UgCp.L_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_HNL | exact L_HFIN ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_HD : S_HD.
Proof. apply (UGoi.L_HD ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_HTL ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_H7F0 : S_H7F0.
Proof. apply (UGoi.L_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_HTL ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_HRZ : S_HRZ.
Proof. apply (Uhqa.L_HRZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_H7F0 ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_H720 : S_H720.
Proof. apply (Uhqa.L_H720 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_H7F0 ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_H778 : S_H778.
Proof. apply (Uhqa.L_H778 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_H7F0 ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_HLZ : S_HLZ.
Proof. apply (Uhqa.L_HLZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_H7F0 ]. Qed.
#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_HEX : S_HEX.
Proof. apply (Uhqa.L_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_H7F0 ]. Qed.
#[using="Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_Z : S_Z.
Proof. apply (UzhX.L_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_848 | exact L_6F8 | exact L_HEX ]. Qed.
#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_A38 : S_A38.
Proof. apply (UeFr.L_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_ERR : S_ERR.
Proof. apply (UeFr.L_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I1 : S_I1.
Proof. apply (UeFr.L_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption ]. Qed.
#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_PAR : S_PAR.
Proof. apply (UpKv.L_PAR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_Z | exact L_ERR | exact L_A38 ]. Qed.
#[using="Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM"] Lemma L_N1 : S_N1.
Proof. apply (UpKv.L_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_Z | exact L_ERR | exact L_A38 ]. Qed.
#[using="Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM"] Lemma L_AWS : S_AWS.
Proof. apply (UKPB.L_AWS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_I1 | exact L_N1 ]. Qed.
#[using="Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM"] Lemma L_WS : S_WS.
Proof. apply (UKPB.L_WS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_I1 | exact L_N1 ]. Qed.
#[using="Hpok Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM"] Lemma L_ENTRYh : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
floatscan_h fuelc f0 1 pok = Some (fR, yR) ->
stk rsegs m0 (q - FS_DEPTH) q -> mem_inv rsegs m0 ->
rw_cells rsegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at rsegs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells rsegs m0 RERRNO [C4 ev] ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom rsegs)).
Proof. apply (UKPB.L_ENTRYh ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR); first [ assumption | exact L_I1 | exact L_N1 ]. Qed.
End Floatscan.
End Mq0.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qkeu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh29.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh29. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4EM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4EM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x53d40%Z.
Definition w_15 := 0xde5fc0ef%Z.
Definition w_59 := 0x00044797%Z.
Definition w_62 := 0x1547b783%Z.
Definition w_67 := 0xfffc2797%Z.
Definition w_70 := 0x6f478793%Z.
Definition w_145 := 0xfffc2317%Z.
Definition w_147 := 0x59c30313%Z.
Definition w_185 := 0x31c000ef%Z.
Definition w_238 := 0x3400b0ef%Z.
Definition hi_59 := (Z_to_bv 20 68).
Definition hi_67 := (Z_to_bv 20 1048514).
Definition hi_145 := (Z_to_bv 20 1048514).
Definition lo_62 := (Z_to_bv 12 340).
Definition lo_70 := (Z_to_bv 12 1780).
Definition lo_147 := (Z_to_bv 12 1436).
Definition joff_15 := (Z_to_bv 21 2084324).
Definition joff_185 := (Z_to_bv 21 796).
Definition joff_238 := (Z_to_bv 21 45888).
Definition e_memcpy := 0x5f438%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QSsB.Mq9.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qkeu.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition lor_shl5 := ltac:(pose proof (@lor_shl5) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Definition land_m4096 := ltac:(pose proof (@land_m4096) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qkeu.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QKZH.rr_ss_mem) (@U4EM.rr_ss_mem) Q6nq.gwt_nil).
#[using="Type"] Lemma write_to_mem_idem : ltac2:(Q6nq.ty2 'GwI.segs '(@Qkeu.write_to_mem_idem) [] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qkeu.write_to_mem_idem) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qkeu.write_to_mem_idem)]. Qed.

Definition rr_mr_mem (m : word -> option byte) (G NB mw E P n k : Z) : word -> option byte :=
rr_ss_mem (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (wz NB))) (wa (G + 32)) (le8 (wz mw))) (wa E) [b8 0]) P E n k.
Lemma gw_eq_rr_mr_mem : @rr_mr_mem = ltac:(GwInst.gw_term (@Qkeu.rr_mr_mem) (@rr_mr_mem)). Proof. unfold rr_mr_mem, Qkeu.rr_mr_mem; ltac2:(GwEq.gw_rw [[@gw_eq_rr_ss_mem__3; @gw_eq_rr_ss_mem__2; @gw_eq_rr_ss_mem]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rr_mr_mem : gw_eqs.

#[using="Type"] Lemma land_high_low' x k y : 0 <= x -> 0 <= k -> 0 <= y < 2^k -> Z.land (x * 2^k) y = 0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qkeu.land_high_low') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qkeu.land_high_low')]. Qed.

#[using="Type"] Lemma lor_low12_pg (w nd : Z) : 0 <= w -> 0 <= nd -> nd mod 4096 = 0 -> Z.lor (Z.land w 4095) nd = nd + w mod 4096.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qkeu.lor_low12_pg) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qkeu.lor_low12_pg)]. Qed.

Definition rr_tail2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (G NB mw' E P n k : Z) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ m' = rr_mr_mem m G NB mw' E P n k
/\ mem_inv rsegs m'.
Lemma gw_eq_rr_tail2_post : @rr_tail2_post = ltac:(GwInst.gw_term (@Qkeu.rr_tail2_post rsegs) (@rr_tail2_post)). Proof. unfold rr_tail2_post, Qkeu.rr_tail2_post; rewrite ?gw_eq_rr_mr_mem; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rr_tail2_post : gw_eqs.
End RC__1.
Lemma gw_eq_rr_mr_mem__2 : @rr_mr_mem = ltac:(GwInst.gw_term (@Qkeu.rr_mr_mem) (@rr_mr_mem)). Proof. unfold rr_mr_mem, Qkeu.rr_mr_mem; ltac2:(GwEq.gw_rw [[@gw_eq_rr_ss_mem__3; @gw_eq_rr_ss_mem__2; @gw_eq_rr_ss_mem]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rr_mr_mem__2 : gw_eqs.
Lemma gw_eq_rr_tail2_post__2 : @rr_tail2_post = ltac:(GwInst.gw_term (@Qkeu.rr_tail2_post rsegs) (@rr_tail2_post)). Proof. unfold rr_tail2_post, Qkeu.rr_tail2_post; rewrite ?gw_eq_rr_mr_mem__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rr_tail2_post__2 : gw_eqs.

Ltac sok_at W off len addr := lazymatch type of W with wr_at rsegs ?mc ?A0 _ =>
let H := fresh "SO" in
pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
replace (A0 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rr_tail2_walk : forall (x1 sp gp tp t0 t1 t2 s0 a0 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(v0 v1 v2 v3 v4 v5 v6 ra gw : word) F fc (m : word -> option byte) (G NB base nd n mw k lo : Z) (prev next memw : word) (avail freed : Z),
let P := NB + 16 + base in
bv_unsigned gw = G ->
let E := NB + nd - 4 in
mem_inv rsegs m ->
rw_cells rsegs m G [C8 prev; C8 next; C8 memw; C4 (wz avail); C4 (wz freed); C8 (wz mw)] ->
wr_at rsegs m (P - 3) (E - P + 4) ->
bytes_at rsegs m (P - 3) [b8 k] ->
rw_cells rsegs m (bv_unsigned sp + -64) [C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 ra] ->
E + 1 <= lo -> G + 40 <= lo -> lo <= bv_unsigned sp + -64 ->
(G + 40 <= P - 3 \/ E + 1 <= G) -> 0 <= G ->
(G + 40 <= 0x10000 \/ 0x99000 <= G) -> (E + 1 <= 0x10000 \/ 0x99000 <= P - 3) ->
16 <= NB -> 0 <= base -> P + n <= E -> E - P - n < 2^31 -> 0 <= n -> 0 <= k < 256 ->
0 <= mw < 2^64 -> 0 <= nd -> nd mod 4096 = 0 -> nd + mw mod 4096 < 2^64 ->
evt rsegs (rr_tail2_post ra sp gp tp v0 v1 v2 v3 v4 v5 v6 s7 s8 s9 s10 s11 t5 t6 F fc m G NB (nd + mw mod 4096) E P n k)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 nd) gw
a0 (Z_to_bv 64 n) (Z_to_bv 64 NB) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5403c) fc None m (seg_rom rsegs)).
Proof. rewrite ?gw_eq_rr_tail2_post__2; first [GwApply2.gw_by_name2 GwI.segs (@Qkeu.rr_tail2_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qkeu.rr_tail2_walk)]. Qed.

#[using="Type"] Lemma rr_mr_head_walk : forall (ra sp gp tp t2 s0 gw a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : word -> option byte) (P S E B mword maplen n : Z) Q,
a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 n -> 0 <= n < 2^63 - 4097 -> 0 <= S <= P -> P - S <= 4080 -> P < 2^64 -> 0 <= B < 2^64 - 1 ->
0 <= mword < 2^64 -> mword - mword mod 4096 = 4096 * maplen ->
let base := P - S in
let nd := rr_needed n base in
(4096 * maplen = nd -> forall a3v a5v,
evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 (Z_to_bv 64 nd) gw
a0 a1 (Z_to_bv 64 B) a3v (Z_to_bv 64 (4096 * maplen)) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5403c) fc None m (seg_rom rsegs))) ->
(4096 * maplen <> nd -> forall a5v,
evt rsegs Q (MS (mkR (Z_to_bv 64 0x54028) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 (Z_to_bv 64 nd) gw
(Z_to_bv 64 B) (Z_to_bv 64 (4096 * maplen)) (Z_to_bv 64 nd) (Z_to_bv 64 1) (Z_to_bv 64 (4096 * maplen)) a5v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) a0 a1 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54340) fc None m (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 S) t2 s0 gw
a0 a1 (Z_to_bv 64 B) (Z_to_bv 64 63) (wz mword) (Z_to_bv 64 48) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x53fd8) fc None m (seg_rom rsegs)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qkeu.rr_mr_head_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qkeu.rr_mr_head_walk)]. Qed.

End RC__2.
