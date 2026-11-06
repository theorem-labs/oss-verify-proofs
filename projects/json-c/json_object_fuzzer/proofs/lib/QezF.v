(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx Q7wb Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX QwyL QhHa QN1y Q48O QGmo QTS6 QvBB QnkH Qi8L QmBS QKwd Qlfl QjhR QCqH QTp6 QHB6 QOy4 Q4KR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

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
Import QHB6.Mq0 QOy4.Mq3 Q4KR.Mq4.
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).

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

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

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

Ltac c8ify_all H := repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
go constr:(@nil cell) cs end).

Ltac read_char_at r :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read rsegs _ T (zbytes txt) r _ _ BY (Qy5Y.zbytes_nth txt r ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt r)) by lia; clear RDb end.

Local Notation S_HEX := (@QOy4.Mq3.S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Ltac dest_hinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Local Notation S_HLZ := (@Q4KR.Mq4.S_HLZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H778 := (@Q4KR.Mq4.S_H778 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H720 := (@Q4KR.Mq4.S_H720 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HRZ := (@Q4KR.Mq4.S_HRZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H7F0 := (@Q4KR.Mq4.S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mq4.hxinv, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mq4.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Hypothesis HS_H7F0 : S_H7F0.

#[using="Type"] Lemma lz_some_S : forall n g c f r, df_lz_loop n (g, c, f) = Some r ->
exists n', n = S n' /\ df_lz_loop n (g, c, f) = (if (c =? 48)%Z then df_lz_loop n' (1%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f)).
Proof.
clear. intros [|n'] g c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_lz_loop_S. unfold df_lz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.
#[using="Type"] Lemma rz_some_S : forall n g l c f r, df_rz_loop n (g, l, c, f) = Some r ->
exists n', n = S n' /\ df_rz_loop n (g, l, c, f) = (if (c =? 48)%Z then df_rz_loop n' (1%Z, (l - 1)%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f)).
Proof.
clear. intros [|n'] g l c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_rz_loop_S. unfold df_rz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HRZ : S_HRZ.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rrp0 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H720 : S_H720.
Proof.
intros m; intros until gd. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Hc0 Rg HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_rz in HK. destruct (df_rz_loop fuelc _) as [[[[gd' rp'] c3] f3]|] eqn:HL; [|discriminate HK].
zs. zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply (L_HRZ fuelc); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H778 : S_H778.
Proof.
intros m; intros until f. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rcb HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold HX_alz in HK.
zs. zs. brf K1.
-
assert (N46 : c <> 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46).
zs. zs. zs.
stmt HS_H7F0. eapply NX; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mq4.kminH; flia).
- assert (E46 : c = 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E46 in RJ.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
ufc2 FC. zs. zs. zs. zs. (brf K2; [ | exfalso; lia ]).
eapply L_H720; try eassumption; try flia; try mk_hxinv; try mk_hxfr.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HLZ : S_HLZ.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (lz_some_S _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <-.
stmt L_H778. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_H7F0"] Lemma L_HEX : S_HEX.
Proof.
intros m; intros until f. intros _ HI RJ Hk FOKR FRM' Hsg Hst Hcx HM.
pose proof HI as HI0. dest_hinv HI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite hexfloat_m_eq in HM.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hcx; discriminate Hcx).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HM.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
assert (FOK : Fok Ft) by (intros kk H8 H10 H14 H15; apply FOKR; assumption).

zs. carve_frame 176%nat ST. rename FR into HFR.
do 14 zs.
lazymatch type of HFR with rw_cells _ _ _ (CB 64 ?jk :: ?rest) =>
apply (rw_cells_split_CB _ _ _ [] 64 jk rest [8;8;8;8;8;8;8;8]%nat) in HFR; [|reflexivity] end.
cbn [mk_CB_cells app] in HFR. c8ify_all HFR.
lazymatch type of HFR with rw_cells _ _ _ (C8 ?b0 :: C8 ?b1 :: C8 ?b2 :: C8 ?b3 :: C8 ?b4 :: C8 ?b5 :: C8 ?b6 :: C8 ?b7 :: _) =>
set (w0 := b0) in HFR; set (w8 := b1) in HFR; set (w16 := b2) in HFR; set (w24 := b3) in HFR;
set (w32 := b4) in HFR; set (w40 := b5) in HFR; set (w48 := b6) in HFR; set (w56 := b7) in HFR;
clearbody w0 w8 w16 w24 w32 w40 w48 w56 end.
match goal with H : list byte |- _ => try clear H end.
rewrite (FOKR 8 ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; lia)) in HFR.
zs. zs. zs. zs. zs.

zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs.

ufc2 FC. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_lz in HM. destruct (df_lz_loop fuelc _) as [[[gd' c3] f3]|] eqn:HL; [|discriminate HM].
zs. zs. zs. brf K1.
-
assert (E46 : c'' = 46%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. rewrite E46 in HL. change (46 =? 48)%Z with false in HL. injection HL as <- <- <-.
unfold HX_alz in HM. change (46 =? 48)%Z with false in HM. cbn [Z.eqb Pos.eqb] in HM. rewrite (surjective_pairing (sh_getc _)) in HM. rewrite E46 in RJ1.
zs.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
replace (Z_to_bv 64 (T + sh_rpos f + 1)) with (Z_to_bv 64 (T + sh_rpos (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)))) by (cbn [sh_rpos]; f_equal; lia).
stmt L_H720. eapply NX with (kmin := (kmin + 1)%Z) (gd := 0%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N46 : c'' <> 46%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (N48 : c'' <> 48%Z) by (clear -K2 Rch; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-.
unfold HX_alz in HM. replace (c'' =? 46)%Z with false in HM by (symmetry; apply Z.eqb_neq; exact N46).
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mq4.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
+
assert (E48 : c'' = 48%Z) by (clear -K2 Rch; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & En2 & HL2). rewrite HL2 in HL. rewrite E48, Z.eqb_refl in HL. rewrite E48 in RJ1.
assert (Z48 : 48%Z <> 0%Z) by lia.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin + 1) 48 _ RJ1 Z48) as RJ2.
pose proof (getc_stdio (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) as Hst2. cbn [sh_stdio] in Hst2.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
pose proof (rf_getc_fast_lt T txt p J Hp (kmin + 1) 48 _ RJ1 Z48 FAST2) as LT2. cbn [sh_rpos] in LT2.
rewrite (rf_getc_fast T txt p J Hp (kmin + 1) 48 _ RJ1 FAST2) in *. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
pose proof (txt_char (sh_rpos f + 1) ltac:(unfold zlength in *; lia)) as Rch2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs0.
read_char_at (sh_rpos f + 1)%Z.
set (c4 := znth txt (sh_rpos f + 1)) in *.
zs. zs. brf K4.
*
assert (E48' : c4 = 48%Z) by (clear -K4 Rch2; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
rewrite E48' in HL, RJ2.
pose proof (L_HLZ n2) as NX2; unfold Q4KR.Mq4.SHLZn in NX2. eapply NX2 with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
* assert (N48' : c4 <> 48%Z) by (clear -K4 Rch2; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n3 & _ & HL3). rewrite HL3 in HL. replace (c4 =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48'). injection HL as <- <- <-.
zs.
stmt L_H778. eapply NX with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
Qed.
End Floatscan.
End Mq0.

Module Mq1.

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
Import QHB6.Mq0 QOy4.Mq3 Q4KR.Mq4.
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

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

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

Local Notation S_H7F0 := (@Q4KR.Mq4.S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SHDn := (@Q4KR.Mq4.SHDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HD := (@Q4KR.Mq4.S_HD ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HTL := (@Q4KR.Mq4.S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mq4.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mq4.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).
Notation HX_tail' := (HX_tail fuelc 53 (-1074)).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mq4.hxinv, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mq4.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac hx_side := lazymatch goal with
| |- Q4KR.Mq4.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mq4.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mq4.kminH _ _ _ => unfold Q4KR.Mq4.kminH; flia
| |- Q4KR.Mq4.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- _ => idtac end.

Hypothesis HS_HTL : S_HTL.

#[using="Type"] Lemma ishexc_iff : forall c, (0 <= c < 256)%Z ->
(ishexc c = true <-> (48 <= c <= 57 \/ 65 <= c <= 70 \/ 97 <= c <= 102))%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (ishexc c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le. tauto.
Qed.
#[using="Type"] Lemma isdigitc_iff' : forall c, (0 <= c < 256)%Z -> (isdigitc c = true <-> (48 <= c <= 57))%Z.
Proof.
clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma lor32_letter : forall c, (65 <= c <= 70 \/ 97 <= c <= 102)%Z -> (97 <= Z.lor c 32 <= 102)%Z /\ (Z.lor c 32 = c \/ Z.lor c 32 = c + 32)%Z.
Proof.
clear. intros c Hc.
assert (R : (0 <= c < 256)%Z) by lia.
pose proof (forallb_range (fun c => implb (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z
(((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) && ((Z.lor c 32 =? c) || (Z.lor c 32 =? c + 32))))%Z 256 ltac:(vm_compute; reflexivity) c R) as E.
cbv beta in E.
replace (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z with true in E by (symmetry; rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite !Bool.andb_true_iff, Bool.orb_true_iff, !Z.leb_le, !Z.eqb_eq in E. lia.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="Type"] Lemma x16_step : forall x d, (0 <= x < 2^32)%Z -> (0 <= d < 16)%Z ->
Z_to_bv 64 (bv_swrap 32 (d + Z.land (Z.shiftl (Z.land (sext32 x) 18446744073709551615) 4) 18446744073709551615)) = Z_to_bv 64 (sext32 (u32 (x * 16 + d))).
Proof.
clear. intros x d Hx Hd. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite !land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low x) as L. pose proof (sext32_range x) as R. rewrite (Z.mod_small x) in L by lia.
set (S := sext32 x) in *. clearbody S.
Z.div_mod_to_equations. nia.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1"] Lemma L_HBODY : forall n, SHDn n ->
forall m (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc d : Z) (s' : st_hex),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc -> c <> 0%Z -> (0 <= d <= 15)%Z ->
(let '(x', y', sc', gt') :=
(if dc <=? 7 then (u32 (x * 16 + d), y, sc, gt)
else if dc <=? 29 then
let df := f128_of_i32 d in let c16 := f128_of_i32 16 in let sc := f128_div sc c16 in let t := f128_mul df sc in
(x, f128_add t y, sc, gt)
else if nz d && negb (nz gt) then
let h := f128_of_d (bv_unsigned D_05) in let t := f128_mul h sc in (x, f128_add t y, sc, 1)
else (x, y, sc, gt))%Z in
hx_dig_loop n (mkHX (fst (sh_getc f)) (snd (sh_getc f)) x' y' sc' gt' gr 1 rp (dc + 1))) = Some s' ->
HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) x10 (Z_to_bv 64 d) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7c48) fct None m (seg_rom rsegs)).
Proof.
intros n IH. intros until s'. intros HI HF RJ HKM FOK FRM' Hsg Hst HXI Hc0 Rd HLB HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.

assert (NEXTC : forall m2 (x1' x5' x6' x7' x8' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft2 fct2 ev2 (x2 y2 sc2 gt2 : Z),
hxinv m2 ev2 f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt2) (Z_to_bv 64 (lo64 sc2)) m2 ->
Fok Ft2 -> frm0 fct2 -> (0 <= x2 < 2^32)%Z -> (0 <= gt2 <= 1)%Z ->
hx_dig_loop n (mkHX (znth txt (sh_rpos f)) (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) x2 y2 sc2 gt2 gr 1 rp (dc + 1)) = Some s' ->
evt rsegs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' x8' (Z_to_bv 64 gr) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x2)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y2)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc2)) x28' x29' x30' x31')
Ft2 (Z_to_bv 64 0xd7d10) fct2 None m2 (seg_rom rsegs))).
{ intros until gt2. intros HI2 HF2 FOK2 FRM2 Rx2 Rgt2 HL2.
pose proof HI2 as HI3. dest_hxinv HI3. unfold Q4KR.Mq4.hxfr in HF2.
match goal with H : rw_cells _ m2 Fp _ |- _ => rename H into FC2 end. ufc2 FC2.
zs. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF.
zs. zs. zs. brf K1; kswrap K1.
-
assert (D : isdigitc c'' = true) by (apply (proj2 DIF); clear -K1 Rch; Z.div_mod_to_equations; lia).
assert (Hc1 : c'' <> 0%Z) by (clear -K1 Rch; Z.div_mod_to_equations; lia).
eapply (IH 0xd7c40%Z); try eassumption. all: hx_side.
- assert (ND : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear -K1 Rch DD; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH 0xd7d3c%Z); try eassumption. all: hx_side. }

zs. zs. brf K1.
-
replace (dc <=? 7)%Z with false in HLB by (symmetry; apply Z.leb_gt; lia).
zs. zs. brf K2; rewrite ?land_W64 in K2.
+
replace (dc <=? 29)%Z with false in HLB by (symmetry; apply Z.leb_gt; clear -K2 Rdc Rr; Z.div_mod_to_equations; lia).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Ed : d = 0%Z) by (clear -K3 Rd; Z.div_mod_to_equations; lia). rewrite Ed in HLB. cbn [nz Z.eqb negb andb] in HLB.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
* assert (Nd : d <> 0%Z) by (clear -K3 Rd; Z.div_mod_to_equations; lia).
replace (nz d) with true in HLB by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Nd). cbn [andb] in HLB.
zs. zs. brf K4; rewrite ?land_W64 in K4.
--
assert (Eg : gt = 1%Z) by (clear -K4 Rgt; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with false in HLB by (rewrite Eg; reflexivity).
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-- assert (Eg : gt = 0%Z) by (clear -K4 Rgt; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with true in HLB by (rewrite Eg; reflexivity). cbv zeta in HLB.
zs. zs.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; reflexivity]).
set (Hv := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range Hv). pose proof (hi64_range Hv).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Hv) (Y := sc); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Hv sc) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
+
replace (dc <=? 29)%Z with true in HLB by (symmetry; apply Z.leb_le; clear -K2 Rdc Rr; Z.div_mod_to_equations; lia). cbv zeta in HLB.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (Dv := f128_of_i32 d) in *. pose proof (lo64_range Dv). pose proof (hi64_range Dv).
zs. zs. zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (C16 := f128_of_i32 16) in *. pose proof (lo64_range C16). pose proof (hi64_range C16).
zs. zs. zs. zs. zs.
hcall_split 112%Z (eapply div_callE with (X := sc) (Y := C16); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (SC2 := f128_div sc C16) in *. pose proof (lo64_range SC2). pose proof (hi64_range SC2).
zs. zs. zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Dv) (Y := SC2); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Dv SC2) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-
replace (dc <=? 7)%Z with true in HLB by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. rewrite x16_step by lia.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok. apply u32_range.
Qed.

#[using="Type"] Lemma lor32_range : forall c, (0 <= c < 256)%Z -> (32 <= Z.lor c 32 < 256)%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => (32 <=? Z.lor c 32) && (Z.lor c 32 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma lor32_af : forall c, (0 <= c < 256)%Z -> (97 <= Z.lor c 32 <= 102)%Z -> (65 <= c <= 70 \/ 97 <= c <= 102)%Z.
Proof.
clear. intros c Hc HL.
pose proof (forallb_range (fun c => implb ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. replace ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102))%Z with true in E by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le in E. lia.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_HD : S_HD.
Proof.
intros n. induction n as [|n IH]; intros pc m; intros until s'; intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HL HK Hpc; [discriminate HL|].
pose proof (L_HBODY n IH) as BODY.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof HXI as HXI0. destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). pose proof HKM as HKM0. destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.
rewrite hx_dig_loop_S in HL. unfold hx_dig_cond in HL. cbn [hx_c] in HL.
pose proof (ishexc_iff c Rcb) as HIF. pose proof (isdigitc_iff' c Rcb) as DIF. pose proof (lor32_range c Rcb) as RL.

assert (DIGIT : forall d, (ishexc c || (c =? 46))%Z = true -> c <> 46%Z -> d = (if (c <=? 57)%Z then (c - 48)%Z else (Z.lor c 32 - 87)%Z) -> (0 <= d <= 15)%Z ->
forall m1 (x12' x13' x14' : word), m1 = m ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 d) x12' x13' x14' x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7c48) fct None m1 (seg_rom rsegs))).
{ intros d CND N46 Ed Rd m1 x12' x13' x14' ->. rewrite CND in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). rewrite <- Ed in HL. cbv zeta in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
remember (if (dc <=? 7)%Z then _ else _) as U eqn:EU in HL.
destruct U as [[[x2 y2] sc2] gt2]. cbv beta iota in HL.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in CND; discriminate CND).
eapply BODY; try eassumption; try flia. rewrite <- EU. exact HL. }
destruct Hpc as [[-> D] | [-> ND]].
-
assert (R9 : (48 <= c <= 57)%Z) by (apply (proj1 DIF); exact D).
zs. (brf K1; [ | exfalso; lia ]).
replace (Z_to_bv 64 (bv_swrap 32 (c + -48))) with (Z_to_bv 64 (c - 48)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | lia | replace (c <=? 57)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity | lia | reflexivity ].
-
zs. zs. brf K1.
+
assert (E46 : c = 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). rewrite Bool.orb_true_r in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). cbv iota in HL.
zs. (brf K2; [ exfalso; lia | ]).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Eg : gr = 1%Z) by (clear -K3 Rgr; Z.div_mod_to_equations; lia). replace (nz gr) with true in HL by (rewrite Eg; reflexivity). cbv iota in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
* assert (Eg : gr = 0%Z) by (clear -K3 Rgr; Z.div_mod_to_equations; lia). replace (nz gr) with false in HL by (rewrite Eg; reflexivity). cbv iota in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
assert (Z46 : 46%Z <> 0%Z) by lia. rewrite E46 in RJ.
zs. zs.
hx_read FC RJ kmin 46%Z f Z46.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF2.
zs. zs. zs. brf K4; kswrap K4.
-- assert (D2 : isdigitc c'' = true) by (apply (proj2 DIF2); clear -K4 Rch; Z.div_mod_to_equations; lia).
eapply (IH 0xd7c40%Z); try eassumption. all: hx_side.
-- assert (ND2 : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF2 eq_refl) as DD; clear -K4 Rch DD; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH 0xd7d3c%Z); try eassumption. all: hx_side.
+ assert (N46 : c <> 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. brf K2; kswrap K2.
*
pose proof (lor32_af c Rcb ltac:(clear -K2 RL; Z.div_mod_to_equations; lia)) as RLc.
zs. (brf K3; [ | exfalso; lia ]). zs. (brf K4; [ exfalso; lia | ]). zs.
replace (Z_to_bv 64 (bv_swrap 32 (Z.lor c 32 + -87))) with (Z_to_bv 64 (Z.lor c 32 - 87)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | exact N46
| replace (c <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity | clear -K2 RL RLc; Z.div_mod_to_equations; lia | reflexivity ].
*
assert (NH : ishexc c = false).
{ destruct (ishexc c) eqn:E; [|reflexivity]. exfalso. pose proof (proj1 HIF eq_refl) as CC0.
destruct CC0 as [C1 | C23].
- apply (proj2 DIF) in C1. rewrite C1 in ND. discriminate ND.
- pose proof (lor32_letter c C23) as [A B]. clear -K2 A. Z.div_mod_to_equations. lia. }
rewrite NH in HL. replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). cbn [orb] in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_H7F0 : S_H7F0.
Proof.
intros m; intros until rp. intros _ HI HF RJ HKM FOK FRM' Hsg Hst Rcb Rgd Rgr Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range Y0) as R0l. pose proof (hi64_range Y0) as R0h. pose proof (lo64_range SC0) as R1l. pose proof (hi64_range SC0) as R1h.
unfold HX_dig in HK. destruct (hx_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
destruct s' as [c9 f9 x9 y9 sc9 gt9 gr9 gd9 rp9 dc9]. cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
pose proof (isdigitc_iff' c Rcb) as DIF.
zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. zs. zs. brf K1; kswrap K1.
- assert (ND : isdigitc c = false) by (destruct (isdigitc c); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear -K1 Rcb DD; Z.div_mod_to_equations; lia | reflexivity]).
pose proof (L_HD fuelc 0xd7d3c%Z) as NX; unfold Q4KR.Mq4.SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
- assert (D : isdigitc c = true) by (apply (proj2 DIF); clear -K1 Rcb; Z.div_mod_to_equations; lia).
zs.
pose proof (L_HD fuelc 0xd7c40%Z) as NX; unfold Q4KR.Mq4.SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
Qed.
End Floatscan.
End Mq1.

Module Mq2.

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
Import QHB6.Mq0 QOy4.Mq3 Q4KR.Mq4.
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

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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

#[using="Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof.
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.
Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

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

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

Local Notation S_HTL := (@Q4KR.Mq4.S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HE2 := (@Q4KR.Mq4.S_HE2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HNL := (@Q4KR.Mq4.S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@Q4KR.Mq4.S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HZR := (@Q4KR.Mq4.S_HZR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mq4.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mq4.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation HX_e2' := (HX_e2 53 (-1074)).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mq4.hxinv, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mq4.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- Q4KR.Mq4.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mq4.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mq4.kminH _ _ _ => unfold Q4KR.Mq4.kminH; flia
| |- Q4KR.Mq4.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

Hypothesis HS_HNL : S_HNL.
Hypothesis HS_HFIN : S_HFIN.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk rsegs m (q - FS_DEPTH) q.
Proof.
intros until w56. intros HI HF. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="pre"] Lemma L_HRET : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7eb4) fct None m (seg_rom rsegs)).
Proof.
intros until c. intros HI HF RJ Hk FOK FRM'.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range yR). pose proof (hi64_range yR).
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
apply evt_done. unfold fs_post, QHB6.Mq0.fs_post, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY|]. split; [split; [exact SSP1 | exact SSP2]|]. split; [exact ERR|].
split; [|exact FRM'].
intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="Type"] Lemma L_HZR : S_HZR.
Proof.
intros m; intros until c. intros _ HI HF RJ Hk FOK FRM' Hsg Hy.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
zs. destruct Hsg as [-> | ->]; (zs; zs; zs; zs; callx (eapply extenddftf2_callF; [eassumption | simpF; reflexivity]);
unfold hx_zero, D_ZERO in Hy; rewrite <- Hy; eapply L_HRET; try eassumption).
all: hx_side.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof.
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_HE2 : S_HE2.
Proof.
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_e2 in HK. replace (x =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia).
change (- (-1074))%Z with 1074%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
zs. zs. zs.
let v := getreg 24%Z in replace v with (Z_to_bv 64 (4 * rp + e2 - 32)%Z) by (apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2, ?land_W64 by lia; Z.div_mod_to_equations; lia).
set (E := (4 * rp + e2 - 32)%Z) in *.
assert (RE : (-2^62 <= E <= 2^62)%Z) by (subst E; lia).
zs. zs. zs. brf K1.
-
replace (1074 <? E)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs. brf K2.
+
replace (E <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
destruct (hx_norm_loop 33 (x, y, E)) as [[[x' y'] E']|] eqn:HN; [|discriminate HK].
pose proof (HX_fin_f _ _ _ _ _ _ _ HK) as Ef.
zs. brf K3.
*
assert (Rx2 : (2^31 <= x)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear -K3 A Rx; Z.div_mod_to_equations; lia).
rewrite hx_norm_loop_S in HN. replace (2 ^ 31 <=? x)%Z with true in HN by (symmetry; apply Z.leb_le; lia). injection HN as <- <- <-.
zs.
stmt HS_HFIN. eapply NX; try eassumption. all: hx_side.
* assert (Rx2 : (x < 2^31)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear -K3 A Rx; Z.div_mod_to_equations; lia).
zs. zs. zs. zs.
stmt HS_HNL. eapply NX; try eassumption. all: hx_side. all: try (simpF; reflexivity).
+
replace (E <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
-
replace (1074 <? E)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
Qed.

#[using="Type"] Lemma shl4_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 4)) = Z_to_bv 64 (sext32 (u32 (xv * 16))).
Proof.
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma u32_mul16 : forall xv k, (0 <= xv)%Z -> u32 (u32 (xv * 16) * 16 ^ Z.of_nat k) = u32 (xv * 16 ^ Z.of_nat (S k)).
Proof.
clear. intros xv k Hx. unfold u32. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma L_X16 : forall (k : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct (xv : Z),
(1 <= k <= 8)%nat -> (0 <= xv < 2^32)%Z ->
(forall xv', xv' = u32 (xv * 16 ^ Z.of_nat k) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0) (Z_to_bv 64 (sext32 xv')) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7d78) fct None m (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- Z.of_nat k)) (Z_to_bv 64 (sext32 xv)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7d6c) fct None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros until xv; intros Hk Rxv KONT; [lia|].
zs. zs. rewrite shl4_step by lia. zs. brf K1; rewrite ?land_W64 in K1.
-
replace (Z_to_bv 64 (- Z.of_nat (S k) + 1)) with (Z_to_bv 64 (- Z.of_nat k)) by (f_equal; lia).
eapply IH; [clear -K1 Hk; Z.div_mod_to_equations; lia | apply u32_range |].
intros xv' ->. rewrite u32_mul16 by lia. apply KONT. reflexivity.
- assert (Ek : k = 0%nat) by (clear -K1 Hk; Z.div_mod_to_equations; lia). subst k.
replace (Z_to_bv 64 (- Z.of_nat 1 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
apply KONT. change (16 ^ Z.of_nat 1)%Z with 16%Z. reflexivity.
Qed.

#[using="Hpok1 BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (f : shfile) (kmin c : Z) (fS : shfile) (e10 : Z),
scanexp fuelc f pok = Some (fS, e10) ->
rw_cells rsegs m Fp (rf_cells T p true f J) -> RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z ->
(sh_stdio f = true -> rtext T txt pre post /\ p = zlength pre) ->
bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
stk rsegs m (q' - 240) q' -> (4096 <= q' - 240)%Z -> (q' <= Fp)%Z ->
(T + zlength txt <= q' - 240 \/ q' <= T)%Z -> (ssp_guard + 8 <= q' - 240)%Z -> (0 <= q')%Z -> (q' < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' k' c',
ms' = MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0' t1' t2' s0 s1 (Z_to_bv 64 e10) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra') fc' None m' (seg_rom rsegs)
/\ munch [(q' - 240, q'); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q' - 240) q'
/\ rw_cells rsegs m' Fp (rf_cells T p true fS J)
/\ RFJ' k' c' fS /\ (1 <= k')%Z
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary)
(MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 SCANEXP) fc' None m (seg_rom rsegs)).
Proof.
intros until e10. intros HS FC RJ Hk Hc STX BY SSP ST Q1' Q2 Q3 Q4 Q5 Q6 MI.
pose proof scanexp_rspec as SX. unfold scanexp_rstmt in SX.
eapply evt_mono.
{ eapply SX with (pre := pre) (post := post); try eassumption; unfold SCANEXP_DEPTH; try flia; clear -Hpok; unfold hide2 in *; flia. }
intros ms' P. unfold scanexp_rpost, SCANEXP_DEPTH in P. exact P.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9D0 : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7dbc) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
zs. brf K1; rewrite ?land_W64 in K1.
- assert (Nx : x <> 0%Z) by (intros ->; apply K1; reflexivity).
stmt L_HE2. eapply NX; try eassumption. all: hx_side.
- assert (Ex : x = 0%Z) by (destruct (sext32_u32_cases x Rx) as [[A B]|[A B]]; rewrite B in K1; clear -K1 A Rx; Z.div_mod_to_equations; lia).
unfold HX_e2 in HK. rewrite Ex, Z.eqb_refl in HK. injection HK as Ey.
zs. stmt L_HZR. eapply NX; try eassumption. all: hx_side. all: symmetry; exact Ey.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9B8 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (g : shfile) (x y rp : Z),
hxinv m ev g -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c g -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
HX_e2' sign (sh_unget g) x y (4 * rp + 0 - 32) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7da4) fct None m (seg_rom rsegs)).
Proof.
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin c g. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp kmin c g RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq g Hsn) in RJu, Ef, HK. rewrite <- Ef in RJu.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_H9D0 with (e2 := 0%Z) (ev := ev); try eassumption. all: hx_side.
unfold Q4KR.Mq4.hxinv. rewrite Ef. mk_hxinv. rewrite Ef in HK |- *. exact HK.
Qed.

#[using="fc pre post kmin0 c0 Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_H98C : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (f : shfile) (x y rp : Z),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
match (if (Z.lor c 32 =? 112)%Z then
match scanexp fuelc f pok with
| None => None
| Some (f, e2) =>
if (e2 =? LLONG_MIN_)%Z then
(if nz pok then Some (inl (sh_unget f, 0%Z))
else Some (inr (sh_lim0 f, f128_of_i32 0)))
else Some (inl (f, e2))
end
else Some (inl (sh_unget f, 0%Z))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, e2)) => HX_e2' sign f x y (4 * rp + e2 - 32)
end = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7d78) fct None m (seg_rom rsegs)).
Proof.
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Hst Rcb Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1.
-
and33n K1 c Rcb 80%Z N1. replace (Z.lor c 32 =? 112)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
eapply L_H9B8; try eassumption. all: hx_side.
- and33y K1 c Rcb 80%Z E1. rewrite E1, Z.eqb_refl in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in E1; discriminate E1).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
zs. zs. zs. zs.
hcall_split 240%Z (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | flia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| eassumption | eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ fS _) |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
zs. zs. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (Hne : e10 <> LLONG_MIN_) by (intros E; apply K2; rewrite E; vm_compute; reflexivity).
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne).
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
eapply L_H9D0 with (ev := ev); try eassumption. all: hx_side.
unfold Q4KR.Mq4.hxinv. rewrite Ef. mk_hxinv. rewrite Ef. exact RJ2. flia. rewrite Ef in HK |- *. exact HK.
+ assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear -K2 R; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; lia]).
rewrite Ee, Z.eqb_refl in HK. replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity).
rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_H9B8 with (ev := ev); try eassumption. all: hx_side.
Qed.

#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_HTL : S_HTL.
Proof.
intros m; intros until dc. intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_tail in HK.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Eg : gd = 0%Z) by (clear -K1 Rgd; Z.div_mod_to_equations; lia). specialize (Hk2 Eg).
replace (negb (nz gd)) with true in HK by (rewrite Eg; reflexivity). replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. zs0. zs. rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1. zs. zs0.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
assert (Hsn1 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
pose proof (RFI_unget T txt p J Hp (kmin - 1) c (sh_unget f) RJu ltac:(flia)) as RJu2.
assert (Hsn2 : sh_shlim_neg (sh_unget (sh_unget f)) = false) by (rewrite (rf_unget_eq _ Hsn1); cbn; exact Hsn1).
zs. brf K4; rewrite ?land_W64 in K4.
+
assert (Er : gr = 0%Z) by (clear -K4 Rgr; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu2. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu2. rewrite Ef in RJu2.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold Q4KR.Mq4.hxinv; rewrite <- Ef; mk_hxinv.
+ assert (Er : gr = 1%Z) by (clear -K4 Rgr; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
pose proof (RFI_unget T txt p J Hp (kmin - 1 - 1) c _ RJu2 ltac:(flia)) as RJu3.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu3. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu3. rewrite Ef in RJu3.
zs. zs0. zs.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold Q4KR.Mq4.hxinv; rewrite <- Ef; mk_hxinv.
-
assert (Eg : gd = 1%Z) by (clear -K1 Rgd; Z.div_mod_to_equations; lia).
replace (negb (nz gd)) with false in HK by (rewrite Eg; reflexivity). cbv iota in HK.

assert (G974 : forall rpF, rpF = (if nz gr then rp else dc) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rpF) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7d60) fct None m (seg_rom rsegs))).
{ intros rpF ErpF. rewrite <- ErpF in HK. cbv zeta in HK.
assert (RrpF : (-2^32 <= rpF <= 2^32)%Z) by (subst rpF; destruct (nz gr); flia).
zs. zs. brf K2.
-
replace (dc <=? 7)%Z with false in HK by (symmetry; apply Z.leb_gt; lia).
eapply L_H98C; try eassumption. all: hx_side.
- replace (dc <=? 7)%Z with true in HK by (symmetry; apply Z.leb_le; lia).
zs. replace (Z_to_bv 64 (dc + -8)) with (Z_to_bv 64 (- Z.of_nat (Z.to_nat (8 - dc)))) by (f_equal; lia).
eapply (L_X16 (Z.to_nat (8 - dc))); [lia | exact Rx |]. intros xv' Exv.
replace (Z.of_nat (Z.to_nat (8 - dc))) with (8 - dc)%Z in Exv by lia. rewrite <- Exv in HK.
eapply L_H98C; try eassumption. all: hx_side. all: subst xv'; apply u32_range. }
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ assert (Er : gr = 0%Z) by (clear -K2 Rgr; Z.div_mod_to_equations; lia).
apply G974. rewrite Er. reflexivity.
+ assert (Er : gr = 1%Z) by (clear -K2 Rgr; Z.div_mod_to_equations; lia).
zs. apply G974. rewrite Er. reflexivity.
Qed.
End Floatscan.
End Mq2.

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
Import QHB6.Mq0 QOy4.Mq3 Q4KR.Mq4.
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

Local Notation FokR := (@QHB6.Mq0.FokR F).
Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac unbury := unfold hide2 in *.
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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

Local Notation S_HNL := (@Q4KR.Mq4.S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@Q4KR.Mq4.S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mq4.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mq4.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mq4.hxinv, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mq4.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- Q4KR.Mq4.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mq4.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mq4.kminH _ _ _ => unfold Q4KR.Mq4.kminH; flia
| |- Q4KR.Mq4.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mq4.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk rsegs m (q - FS_DEPTH) q.
Proof.
intros until w56. intros HI HF. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="Type"] Lemma shl1_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 1)) = Z_to_bv 64 (sext32 (u32 (2 * xv))).
Proof.
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma lor1_even : forall a, (a mod 2 = 0)%Z -> Z.lor a 1 = (a + 1)%Z.
Proof.
clear. intros a Ha. assert (L : Z.land a 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones; [exact Ha | lia]).
rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by exact L. reflexivity.
Qed.
#[using="Type"] Lemma sext32_succ_even : forall a, (0 <= a < 2^32)%Z -> (a mod 2 = 0)%Z -> sext32 (a + 1) = (sext32 a + 1)%Z /\ (sext32 a mod 2 = 0)%Z.
Proof.
clear. intros a Ha Ea. rewrite !sext32_eq. change (2^32)%Z with 4294967296%Z in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof.
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="pre SPF SPT SG1"] Lemma hx_post_tail : forall m m' F' fc' k c ev w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> RFJ' k c fR -> (0 <= k)%Z ->
FokR F' -> frm0 fc' ->
munch [(q - 112, q)]%Z m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (q - 112) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)).
Proof.
intros until w56. intros HI HF RJ Hk FOK FRM' MU2 WM2 MI2 ST2. intros.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI HF) as STK. unfold FS_DEPTH in STK.
dest_hxinv HI. bury_disj. unbury.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 _].
unfold fs_post, QHB6.Mq0.fs_post, QHB6.Mq0.Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split.
{ eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST2 | lia ]. }
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="pre SPLO SPF SPT SG1 Q1"] Lemma L_HCFC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c (Y e2 : Z),
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd80e8) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' He2 Hy.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. rewrite ?swrap32_landW. rewrite swrap32_small by lia.
zs. zs.
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof scalbnl_spec as SS. unfold scalbnl_stmt in SS.
replace (Z_to_bv 64 (q + -176 + 176)) with (Z_to_bv 64 q) by (f_equal; lia).
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. unbury. eapply (hx_post_tail m m'); try eassumption.
intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="pre Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HC64 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w48 w56 : word) sign k c (x y BI e2 : Z),
hxinv m ev fR -> hxfr w0 (Z_to_bv 64 (hi64 BI)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> (0 <= x < 2^32)%Z -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl (f128_sub (f128_add (f128_mul (f128_of_i32 sign) y) (f128_add (f128_mul (f128_of_i32 sign) (f128_of_u32 x)) BI)) BI) e2 ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8050) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx He2 Hy.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range BI). pose proof (hi64_range BI).
pose proof (sext32_range x) as RSx.
zs. destruct Hsg as [Hsg | Hsg]; rewrite Hsg in *.
all: zs; callx (eapply floatsitf_callsg; [eassumption | lia]).
all: set (SF := f128_of_i32 _) in *; pose proof (lo64_range SF); pose proof (hi64_range SF).
all: zs; zs; zs; zs; callx (eapply floatunsitf_callv with (u := x); [eassumption | lia | reflexivity]).
all: set (XF := f128_of_u32 x) in *; pose proof (lo64_range XF); pose proof (hi64_range XF).
all: zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V1 := f128_mul SF XF) in *; pose proof (lo64_range V1); pose proof (hi64_range V1).
all: zs; zs; zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V1) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V2 := f128_add V1 BI) in *; pose proof (lo64_range V2); pose proof (hi64_range V2).
all: zs; zs; zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V3 := f128_mul SF y) in *; pose proof (lo64_range V3); pose proof (hi64_range V3).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V3) (Y := V2); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V4 := f128_add V3 V2) in *; pose proof (lo64_range V4); pose proof (hi64_range V4).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply sub_callE with (X := V4) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (YF := f128_sub V4 BI) in *; pose proof (lo64_range YF); pose proof (hi64_range YF).
all: zs; zs; zs; zs; zs; callx (eapply letf2_callE with (X := YF) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
all: pose proof (f128_le_range YF 0) as RLE.
all: zs; brf K1.
1,3: eapply L_HCFC; try eassumption; hx_side.
all: zs; callx (eapply errno_loc_spec; eassumption).
all: zs; unfold RERRNO; zs0.
all: eapply L_HCFC; try eassumption; hx_side.
Qed.
#[using="Type"] Lemma sgtz_b2z : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808) = (if 0 <? E then 1 else 0)%Z.
Proof.
clear. intros E HE. rewrite (land_W64 E). change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (Z.div_mod_to_equations; lia).
destruct (Z.ltb_spec 0 E).
- replace (2^63 <? _)%Z with true; [reflexivity|]. symmetry. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
- replace (2^63 <? _)%Z with false; [reflexivity|]. symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma bits_clamp : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land E 18446744073709551615) = Z.max 0 E.
Proof.
clear. intros E HE. rewrite sgtz_b2z by lia. destruct (Z.ltb_spec 0 E).
- change (0 - 1)%Z with (-1)%Z. rewrite Z.land_m1_l. rewrite (land_W64_small E) by lia. rewrite Z.land_comm, land_W64_small by lia. lia.
- change (0 - 0)%Z with 0%Z. rewrite !Z.land_0_l. lia.
Qed.
#[using="Type"] Lemma land1_sext32 : forall x, (0 <= x < 2^32)%Z -> Z.land (sext32 x) 1 = (x mod 2)%Z.
Proof.
clear. intros x Hx. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1)%Z with 2%Z.
rewrite sext32_eq. change (2^32)%Z with 4294967296%Z in Hx. Z.div_mod_to_equations. lia.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HFIN : S_HFIN.
Proof.
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (sext32_range x) as RSx.
unfold HX_fin in HK.
remember (if (53 <=? 32 + e2 - -1074)%Z then 53%Z else Z.max 0 (32 + e2 - -1074)) as bits eqn:Eb in HK.
assert (Rb : (0 <= bits <= 53)%Z) by (subst bits; destruct (Z.leb_spec 53 (32 + e2 - -1074))%Z; lia).
replace (bits <=? 112)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv zeta in HK.

assert (G : forall (xa xb : word),
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 xa xb x12 x13 x14 x15 x16 x17
(Z_to_bv 64 bits) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7fb8) fct None m (seg_rom rsegs))).
2: { zs. zs. zs. zs. brf K1.
- replace (53 <=? 32 + e2 - -1074)%Z with true in Eb by (symmetry; apply Z.leb_le; lia). subst bits. apply G.
- replace (53 <=? 32 + e2 - -1074)%Z with false in Eb by (symmetry; apply Z.leb_gt; lia).
zs. fixw3. zs. zs. zs.
let v := getreg 18%Z in replace v with (Z_to_bv 64 bits) by (rewrite bits_clamp by lia; f_equal; rewrite Eb; lia).
let v := getreg 11%Z in set (JK := v); clearbody JK.
apply G. }
intros xa xb.
zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. zs. zs. zs.
rewrite !swrap32_small by lia. rewrite Z.add_0_r.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]).
lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) with D1 in HK.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (HB := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range HB). pose proof (hi64_range HB).
zs. zs. zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs. callx (eapply copysignl_callE with (X := HB) (Y := SF); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl HB SF) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. brf K3.
-
replace (bits <=? 31)%Z with false in HK by (symmetry; apply Z.leb_gt; clear -K3 Rb; Z.div_mod_to_equations; lia).
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
- replace (bits <=? 31)%Z with true in HK by (symmetry; apply Z.leb_le; clear -K3 Rb; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. callx (eapply letf2_callE with (X := y) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range y 0) as RLE. set (LE := f128_le y 0) in *.
zs. zs. brf K4; rewrite (land1_sext32 x) in K4 by lia; rewrite Zmod_odd in K4.
+
replace (Z.odd x) with true in HK by (destruct (Z.odd x); [reflexivity | exfalso; apply K4; reflexivity]). cbn [negb andb] in HK.
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
+ replace (Z.odd x) with false in HK by (destruct (Z.odd x); [exfalso; clear -K4; lia | reflexivity]). cbn [negb andb] in HK.
assert (Ex2 : (x mod 2 = 0)%Z) by (rewrite Zmod_odd; destruct (Z.odd x); [exfalso; clear -K4; lia | reflexivity]).
zs. zs. brf K5; rewrite ?land_W64 in K5.
*
assert (EL : LE = 0%Z) by (clear -K5 RLE; Z.div_mod_to_equations; lia).
replace (nz LE) with false in HK by (rewrite EL; reflexivity). injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
* assert (NL : LE <> 0%Z) by (clear -K5 RLE; Z.div_mod_to_equations; lia).
replace (nz LE) with true in HK by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NL). injection HK as Ey.
rewrite lor1_even in Ey by exact Ex2.
destruct (sext32_succ_even x ltac:(lia) Ex2) as [SE1 SE2].
zs. rewrite ?land_W64_small by lia. rewrite (lor1_even (sext32 x)) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HNL : S_HNL.
Proof.
intros n. induction n as [|n IH]; intros m; intros until e2'; intros _ HI HF RJ Hk FOK FRM' Hsg HF5 Rx Re2 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mq4.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
rewrite hx_norm_loop_S in HL. replace (2 ^ 31 <=? x)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
unfold hx_norm_body in HL. replace (u32 (2 * x)) with (2 * x)%Z in HL by (unfold u32; symmetry; apply Z.mod_small; lia).
set (H5 := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range H5). pose proof (hi64_range H5).
assert (Rn : (Z.of_nat (S n) = Z.of_nat n + 1)%Z) by lia. rewrite Rn in Re2.

assert (TAIL : forall m1 (x1' x5' x6' x7' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft1 fct1 (x2 y2 : Z),
hxinv m1 ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m1 ->
Fok Ft1 -> frm0 fct1 -> reg_get Ft1 8 = D_05 -> (2 * x <= x2 <= 2 * x + 1)%Z ->
hx_norm_loop n (x2, y2, e2 - 1)%Z = Some (x', y', e2') ->
evt rsegs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' (Z_to_bv 64 (-1074)) x9 (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 (hi64 y2)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x2)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28' x29' x30' x31')
Ft1 (Z_to_bv 64 0xd7f3c) fct1 None m1 (seg_rom rsegs))).
{ intros until y2. intros HI1 HF1 FOK1 FRM1 HF51 Rx2 HL2. clear HL.
clear MI MU WM ST BY SSP1 SSP2 ERR FC HF. dest_hxinv HI1. unfold Q4KR.Mq4.hxfr in HF1.
pose proof (lo64_range y2). pose proof (hi64_range y2).
zs. zs. zs. replace (Z_to_bv 64 (e2 + -1)) with (Z_to_bv 64 (e2 - 1)%Z) by (f_equal; lia).
destruct (sext32_u32_cases x2 ltac:(lia)) as [[A B]|[A B]].
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [clear -K1 A Rx; exfalso; Z.div_mod_to_equations; lia|].
eapply IH; try eassumption. all: hx_side.
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [|clear -K1 A Rx; exfalso; Z.div_mod_to_equations; lia].
destruct n as [|n2]; [discriminate HL2|]. rewrite hx_norm_loop_S in HL2.
replace (2 ^ 31 <=? x2)%Z with true in HL2 by (symmetry; apply Z.leb_le; lia). injection HL2 as <- <- <-.
stmt L_HFIN. eapply NX; try eassumption. all: hx_side. }
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; rewrite <- HF5; do 2 f_equal; apply bv_eq; vm_compute; reflexivity]).
fold H5.
zs. zs. zs. zs. zs. callx (eapply getf2_callE with (X := y) (Y := H5); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range y H5) as RGE. set (GE := f128_ge y H5) in *.
zs. rewrite shl1_step by lia. replace (u32 (2 * x)) with (2 * x)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
zs. brs K1.
-
replace (0 <=? GE)%Z with true in HL by (symmetry; apply Z.leb_le; lia).
rewrite lor1_even in HL by (Z.div_mod_to_equations; lia).
destruct (sext32_succ_even (2 * x) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as [SE1 SE2].
pose proof (sext32_range (2 * x)) as RS2.
zs. rewrite ?land_W64. rewrite (lor1_even (sext32 (2 * x))) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (ONE := f128_of_i32 1) in *. pose proof (lo64_range ONE). pose proof (hi64_range ONE).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply sub_callE with (X := y) (Y := ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (YM1 := f128_sub y ONE) in *. pose proof (lo64_range YM1). pose proof (hi64_range YM1).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := YM1); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
-
replace (0 <=? GE)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
zs. zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
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

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3 QOy4 Q4KR.Mqc.
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).

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

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

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

Ltac c8ify_all H := repeat (lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
go constr:(@nil cell) cs end).

Ltac read_char_at r :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read usegs _ T (zbytes txt) r _ _ BY (Qy5Y.zbytes_nth txt r ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt r)) by lia; clear RDb end.

Local Notation S_HEX := (@QOy4.S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Ltac dest_hinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Local Notation S_HLZ := (@Q4KR.Mqc.S_HLZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H778 := (@Q4KR.Mqc.S_H778 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H720 := (@Q4KR.Mqc.S_H720 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HRZ := (@Q4KR.Mqc.S_HRZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_H7F0 := (@Q4KR.Mqc.S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mqc.hxinv, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mqc.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Hypothesis HS_H7F0 : S_H7F0.

#[using="Type"] Lemma lz_some_S : forall n g c f r, df_lz_loop n (g, c, f) = Some r ->
exists n', n = S n' /\ df_lz_loop n (g, c, f) = (if (c =? 48)%Z then df_lz_loop n' (1%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f)).
Proof.
clear. intros [|n'] g c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_lz_loop_S. unfold df_lz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.
#[using="Type"] Lemma rz_some_S : forall n g l c f r, df_rz_loop n (g, l, c, f) = Some r ->
exists n', n = S n' /\ df_rz_loop n (g, l, c, f) = (if (c =? 48)%Z then df_rz_loop n' (1%Z, (l - 1)%Z, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f)).
Proof.
clear. intros [|n'] g l c f r H; [discriminate H|]. exists n'. split; [reflexivity|].
rewrite df_rz_loop_S. unfold df_rz_body. rewrite (surjective_pairing (sh_getc f)). reflexivity.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HRZ : S_HRZ.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rrp0 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mqc.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H720 : S_H720.
Proof.
intros m; intros until gd. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Hc0 Rg HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_rz in HK. destruct (df_rz_loop fuelc _) as [[[[gd' rp'] c3] f3]|] eqn:HL; [|discriminate HK].
zs. zs. zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply (L_HRZ fuelc); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (rz_some_S _ _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <- <-.
zs. zs. zs.
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mqc.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_H778 : S_H778.
Proof.
intros m; intros until f. intros _ HI HF RJ Hk FOK FRM' Hsg Hst Rcb HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold HX_alz in HK.
zs. zs. brf K1.
-
assert (N46 : c <> 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N46).
zs. zs. zs.
stmt HS_H7F0. eapply NX; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mqc.kminH; flia).
- assert (E46 : c = 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E46, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E46 in RJ.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
ufc2 FC. zs. zs. zs. zs. (brf K2; [ | exfalso; lia ]).
eapply L_H720; try eassumption; try flia; try mk_hxinv; try mk_hxfr.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_H7F0"] Lemma L_HLZ : S_HLZ.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ HI HF RJ Hk FOK FRM' Hsg Hst HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin 48%Z f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
destruct (lz_some_S _ _ _ _ _ HL) as (n' & En & HL'). injection En as En'. subst n'. change (48 =? 48)%Z with true in HL'. cbv iota in HL'. rewrite HL' in HL. clear HL'.
assert (Z48 : 48%Z <> 0%Z) by lia.
hx_read FC RJ kmin 48%Z f Z48.
set (c'' := znth txt (sh_rpos f)) in *.
zs. brf K1.
-
assert (E48 : c'' = 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E48 in HL, RJ1.
eapply IH; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N48 : c'' <> 48%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48).
injection HL as <- <- <-.
stmt L_H778. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_H7F0"] Lemma L_HEX : S_HEX.
Proof.
intros m; intros until f. intros _ HI RJ Hk FOKR FRM' Hsg Hst Hcx HM.
pose proof HI as HI0. dest_hinv HI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite hexfloat_m_eq in HM.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hcx; discriminate Hcx).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HM.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
assert (FOK : Fok Ft) by (intros kk H8 H10 H14 H15; apply FOKR; assumption).

zs. carve_frame 176%nat ST. rename FR into HFR.
do 14 zs.
lazymatch type of HFR with rw_cells _ _ _ (CB 64 ?jk :: ?rest) =>
apply (rw_cells_split_CB _ _ _ [] 64 jk rest [8;8;8;8;8;8;8;8]%nat) in HFR; [|reflexivity] end.
cbn [mk_CB_cells app] in HFR. c8ify_all HFR.
lazymatch type of HFR with rw_cells _ _ _ (C8 ?b0 :: C8 ?b1 :: C8 ?b2 :: C8 ?b3 :: C8 ?b4 :: C8 ?b5 :: C8 ?b6 :: C8 ?b7 :: _) =>
set (w0 := b0) in HFR; set (w8 := b1) in HFR; set (w16 := b2) in HFR; set (w24 := b3) in HFR;
set (w32 := b4) in HFR; set (w40 := b5) in HFR; set (w48 := b6) in HFR; set (w56 := b7) in HFR;
clearbody w0 w8 w16 w24 w32 w40 w48 w56 end.
match goal with H : list byte |- _ => try clear H end.
rewrite (FOKR 8 ltac:(vm_compute; lia) ltac:(vm_compute; lia) ltac:(vm_compute; lia)) in HFR.
zs. zs. zs. zs. zs.

zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs.

ufc2 FC. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
unfold HX_lz in HM. destruct (df_lz_loop fuelc _) as [[[gd' c3] f3]|] eqn:HL; [|discriminate HM].
zs. zs. zs. brf K1.
-
assert (E46 : c'' = 46%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. rewrite E46 in HL. change (46 =? 48)%Z with false in HL. injection HL as <- <- <-.
unfold HX_alz in HM. change (46 =? 48)%Z with false in HM. cbn [Z.eqb Pos.eqb] in HM. rewrite (surjective_pairing (sh_getc _)) in HM. rewrite E46 in RJ1.
zs.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
replace (Z_to_bv 64 (T + sh_rpos f + 1)) with (Z_to_bv 64 (T + sh_rpos (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)))) by (cbn [sh_rpos]; f_equal; lia).
stmt L_H720. eapply NX with (kmin := (kmin + 1)%Z) (gd := 0%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst1; exact Hst).
- assert (N46 : c'' <> 46%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (N48 : c'' <> 48%Z) by (clear -K2 Rch; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & _ & HL2). rewrite HL2 in HL. replace (c'' =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <-.
unfold HX_alz in HM. replace (c'' =? 46)%Z with false in HM by (symmetry; apply Z.eqb_neq; exact N46).
stmt HS_H7F0. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (unfold Q4KR.Mqc.kminH; flia); try (rewrite Hst1; exact Hst); try (cbn [sh_rpos]; flia).
+
assert (E48 : c'' = 48%Z) by (clear -K2 Rch; rewrite ?land_W64 in K2; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n2 & En2 & HL2). rewrite HL2 in HL. rewrite E48, Z.eqb_refl in HL. rewrite E48 in RJ1.
assert (Z48 : 48%Z <> 0%Z) by lia.
pose proof (RFI_getc T txt p J BYT Hp Hnul (kmin + 1) 48 _ RJ1 Z48) as RJ2.
pose proof (getc_stdio (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) as Hst2. cbn [sh_stdio] in Hst2.
destruct (Z.eq_dec (T + (sh_rpos f + 1))%Z (rf_rend T p true f)) as [SLOW2|FAST2];
[exfalso; exact (rf_slow_false _ _ _ RJ1 SLOW2)|].
pose proof (rf_getc_fast_lt T txt p J Hp (kmin + 1) 48 _ RJ1 Z48 FAST2) as LT2. cbn [sh_rpos] in LT2.
rewrite (rf_getc_fast T txt p J Hp (kmin + 1) 48 _ RJ1 FAST2) in *. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *.
pose proof (txt_char (sh_rpos f + 1) ltac:(unfold zlength in *; lia)) as Rch2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs0.
read_char_at (sh_rpos f + 1)%Z.
set (c4 := znth txt (sh_rpos f + 1)) in *.
zs. zs. brf K4.
*
assert (E48' : c4 = 48%Z) by (clear -K4 Rch2; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
rewrite E48' in HL, RJ2.
pose proof (L_HLZ n2) as NX2; unfold Q4KR.Mqc.SHLZn in NX2. eapply NX2 with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
* assert (N48' : c4 <> 48%Z) by (clear -K4 Rch2; rewrite ?land_W64 in K4; Z.div_mod_to_equations; lia).
destruct (lz_some_S _ _ _ _ _ HL) as (n3 & _ & HL3). rewrite HL3 in HL. replace (c4 =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48'). injection HL as <- <- <-.
zs.
stmt L_H778. eapply NX with (kmin := (kmin + 1 + 1)%Z); try eassumption; try flia; try mk_hxinv; try mk_hxfr; try (rewrite Hst2; exact Hst).
Qed.
End Floatscan.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3 QOy4 Q4KR.Mqc.
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.

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

Local Notation S_H7F0 := (@Q4KR.Mqc.S_H7F0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation SHDn := (@Q4KR.Mqc.SHDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HD := (@Q4KR.Mqc.S_HD ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HTL := (@Q4KR.Mqc.S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mqc.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mqc.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).
Notation HX_tail' := (HX_tail fuelc 53 (-1074)).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mqc.hxinv, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mqc.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Ltac hx_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac hx_side := lazymatch goal with
| |- Q4KR.Mqc.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mqc.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mqc.kminH _ _ _ => unfold Q4KR.Mqc.kminH; flia
| |- Q4KR.Mqc.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mqc.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- _ => idtac end.

Hypothesis HS_HTL : S_HTL.

#[using="Type"] Lemma ishexc_iff : forall c, (0 <= c < 256)%Z ->
(ishexc c = true <-> (48 <= c <= 57 \/ 65 <= c <= 70 \/ 97 <= c <= 102))%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (ishexc c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le. tauto.
Qed.
#[using="Type"] Lemma isdigitc_iff' : forall c, (0 <= c < 256)%Z -> (isdigitc c = true <-> (48 <= c <= 57))%Z.
Proof.
clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. change (2 ^ 32)%Z with 4294967296%Z. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma lor32_letter : forall c, (65 <= c <= 70 \/ 97 <= c <= 102)%Z -> (97 <= Z.lor c 32 <= 102)%Z /\ (Z.lor c 32 = c \/ Z.lor c 32 = c + 32)%Z.
Proof.
clear. intros c Hc.
assert (R : (0 <= c < 256)%Z) by lia.
pose proof (forallb_range (fun c => implb (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z
(((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) && ((Z.lor c 32 =? c) || (Z.lor c 32 =? c + 32))))%Z 256 ltac:(vm_compute; reflexivity) c R) as E.
cbv beta in E.
replace (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102)))%Z with true in E by (symmetry; rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite !Bool.andb_true_iff, Bool.orb_true_iff, !Z.leb_le, !Z.eqb_eq in E. lia.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="Type"] Lemma x16_step : forall x d, (0 <= x < 2^32)%Z -> (0 <= d < 16)%Z ->
Z_to_bv 64 (bv_swrap 32 (d + Z.land (Z.shiftl (Z.land (sext32 x) 18446744073709551615) 4) 18446744073709551615)) = Z_to_bv 64 (sext32 (u32 (x * 16 + d))).
Proof.
clear. intros x d Hx Hd. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite !land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low x) as L. pose proof (sext32_range x) as R. rewrite (Z.mod_small x) in L by lia.
set (S := sext32 x) in *. clearbody S.
Z.div_mod_to_equations. nia.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1"] Lemma L_HBODY : forall n, SHDn n ->
forall m (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc d : Z) (s' : st_hex),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc -> c <> 0%Z -> (0 <= d <= 15)%Z ->
(let '(x', y', sc', gt') :=
(if dc <=? 7 then (u32 (x * 16 + d), y, sc, gt)
else if dc <=? 29 then
let df := f128_of_i32 d in let c16 := f128_of_i32 16 in let sc := f128_div sc c16 in let t := f128_mul df sc in
(x, f128_add t y, sc, gt)
else if nz d && negb (nz gt) then
let h := f128_of_d (bv_unsigned D_05) in let t := f128_mul h sc in (x, f128_add t y, sc, 1)
else (x, y, sc, gt))%Z in
hx_dig_loop n (mkHX (fst (sh_getc f)) (snd (sh_getc f)) x' y' sc' gt' gr 1 rp (dc + 1))) = Some s' ->
HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) x10 (Z_to_bv 64 d) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda30c) fct None m (seg_rom usegs)).
Proof.
intros n IH. intros until s'. intros HI HF RJ HKM FOK FRM' Hsg Hst HXI Hc0 Rd HLB HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.

assert (NEXTC : forall m2 (x1' x5' x6' x7' x8' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft2 fct2 ev2 (x2 y2 sc2 gt2 : Z),
hxinv m2 ev2 f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt2) (Z_to_bv 64 (lo64 sc2)) m2 ->
Fok Ft2 -> frm0 fct2 -> (0 <= x2 < 2^32)%Z -> (0 <= gt2 <= 1)%Z ->
hx_dig_loop n (mkHX (znth txt (sh_rpos f)) (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) x2 y2 sc2 gt2 gr 1 rp (dc + 1)) = Some s' ->
evt usegs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' x8' (Z_to_bv 64 gr) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x2)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y2)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc2)) x28' x29' x30' x31')
Ft2 (Z_to_bv 64 0xda3d4) fct2 None m2 (seg_rom usegs))).
{ intros until gt2. intros HI2 HF2 FOK2 FRM2 Rx2 Rgt2 HL2.
pose proof HI2 as HI3. dest_hxinv HI3. unfold Q4KR.Mqc.hxfr in HF2.
match goal with H : rw_cells _ m2 Fp _ |- _ => rename H into FC2 end. ufc2 FC2.
zs. zs. zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF.
zs. zs. zs. brf K1; kswrap K1.
-
assert (D : isdigitc c'' = true) by (apply (proj2 DIF); clear -K1 Rch; Z.div_mod_to_equations; lia).
assert (Hc1 : c'' <> 0%Z) by (clear -K1 Rch; Z.div_mod_to_equations; lia).
eapply (IH 0xda304%Z); try eassumption. all: hx_side.
- assert (ND : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear -K1 Rch DD; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH 0xda400%Z); try eassumption. all: hx_side. }

zs. zs. brf K1.
-
replace (dc <=? 7)%Z with false in HLB by (symmetry; apply Z.leb_gt; lia).
zs. zs. brf K2; rewrite ?land_W64 in K2.
+
replace (dc <=? 29)%Z with false in HLB by (symmetry; apply Z.leb_gt; clear -K2 Rdc Rr; Z.div_mod_to_equations; lia).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Ed : d = 0%Z) by (clear -K3 Rd; Z.div_mod_to_equations; lia). rewrite Ed in HLB. cbn [nz Z.eqb negb andb] in HLB.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
* assert (Nd : d <> 0%Z) by (clear -K3 Rd; Z.div_mod_to_equations; lia).
replace (nz d) with true in HLB by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Nd). cbn [andb] in HLB.
zs. zs. brf K4; rewrite ?land_W64 in K4.
--
assert (Eg : gt = 1%Z) by (clear -K4 Rgt; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with false in HLB by (rewrite Eg; reflexivity).
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-- assert (Eg : gt = 0%Z) by (clear -K4 Rgt; Z.div_mod_to_equations; lia). replace (negb (nz gt)) with true in HLB by (rewrite Eg; reflexivity). cbv zeta in HLB.
zs. zs.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; reflexivity]).
set (Hv := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range Hv). pose proof (hi64_range Hv).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Hv) (Y := sc); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Hv sc) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
+
replace (dc <=? 29)%Z with true in HLB by (symmetry; apply Z.leb_le; clear -K2 Rdc Rr; Z.div_mod_to_equations; lia). cbv zeta in HLB.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (Dv := f128_of_i32 d) in *. pose proof (lo64_range Dv). pose proof (hi64_range Dv).
zs. zs. zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (C16 := f128_of_i32 16) in *. pose proof (lo64_range C16). pose proof (hi64_range C16).
zs. zs. zs. zs. zs.
hcall_split 112%Z (eapply div_callE with (X := sc) (Y := C16); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (SC2 := f128_div sc C16) in *. pose proof (lo64_range SC2). pose proof (hi64_range SC2).
zs. zs. zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := Dv) (Y := SC2); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Tv := f128_mul Dv SC2) in *. pose proof (lo64_range Tv). pose proof (hi64_range Tv).
zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := Tv) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_add Tv y) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok.
-
replace (dc <=? 7)%Z with true in HLB by (symmetry; apply Z.leb_le; lia).
zs. zs. zs. rewrite x16_step by lia.
eapply NEXTC; try eassumption; try flia; try mk_hxinv; try mk_hxfr; try fok. apply u32_range.
Qed.

#[using="Type"] Lemma lor32_range : forall c, (0 <= c < 256)%Z -> (32 <= Z.lor c 32 < 256)%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => (32 <=? Z.lor c 32) && (Z.lor c 32 <? 256))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

#[using="Type"] Lemma lor32_af : forall c, (0 <= c < 256)%Z -> (97 <= Z.lor c 32 <= 102)%Z -> (65 <= c <= 70 \/ 97 <= c <= 102)%Z.
Proof.
clear. intros c Hc HL.
pose proof (forallb_range (fun c => implb ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102)) (((65 <=? c) && (c <=? 70)) || ((97 <=? c) && (c <=? 102))))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. replace ((97 <=? Z.lor c 32) && (Z.lor c 32 <=? 102))%Z with true in E by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
cbn [implb] in E. rewrite Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le in E. lia.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_HD : S_HD.
Proof.
intros n. induction n as [|n IH]; intros pc m; intros until s'; intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HL HK Hpc; [discriminate HL|].
pose proof (L_HBODY n IH) as BODY.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof HXI as HXI0. destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). pose proof HKM as HKM0. destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range sc) as Rsl. pose proof (hi64_range sc) as Rsh.
rewrite hx_dig_loop_S in HL. unfold hx_dig_cond in HL. cbn [hx_c] in HL.
pose proof (ishexc_iff c Rcb) as HIF. pose proof (isdigitc_iff' c Rcb) as DIF. pose proof (lor32_range c Rcb) as RL.

assert (DIGIT : forall d, (ishexc c || (c =? 46))%Z = true -> c <> 46%Z -> d = (if (c <=? 57)%Z then (c - 48)%Z else (Z.lor c 32 - 87)%Z) -> (0 <= d <= 15)%Z ->
forall m1 (x12' x13' x14' : word), m1 = m ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 d) x12' x13' x14' x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda30c) fct None m1 (seg_rom usegs))).
{ intros d CND N46 Ed Rd m1 x12' x13' x14' ->. rewrite CND in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). rewrite <- Ed in HL. cbv zeta in HL.
rewrite (surjective_pairing (sh_getc f)) in HL.
remember (if (dc <=? 7)%Z then _ else _) as U eqn:EU in HL.
destruct U as [[[x2 y2] sc2] gt2]. cbv beta iota in HL.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in CND; discriminate CND).
eapply BODY; try eassumption; try flia. rewrite <- EU. exact HL. }
destruct Hpc as [[-> D] | [-> ND]].
-
assert (R9 : (48 <= c <= 57)%Z) by (apply (proj1 DIF); exact D).
zs. (brf K1; [ | exfalso; lia ]).
replace (Z_to_bv 64 (bv_swrap 32 (c + -48))) with (Z_to_bv 64 (c - 48)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | lia | replace (c <=? 57)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity | lia | reflexivity ].
-
zs. zs. brf K1.
+
assert (E46 : c = 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). rewrite Bool.orb_true_r in HL. unfold hx_dig_body in HL.
replace (c =? 46)%Z with true in HL by (rewrite E46; reflexivity). cbv iota in HL.
zs. (brf K2; [ exfalso; lia | ]).
zs. brf K3; rewrite ?land_W64 in K3.
*
assert (Eg : gr = 1%Z) by (clear -K3 Rgr; Z.div_mod_to_equations; lia). replace (nz gr) with true in HL by (rewrite Eg; reflexivity). cbv iota in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
* assert (Eg : gr = 0%Z) by (clear -K3 Rgr; Z.div_mod_to_equations; lia). replace (nz gr) with false in HL by (rewrite Eg; reflexivity). cbv iota in HL.
rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
assert (Z46 : 46%Z <> 0%Z) by lia. rewrite E46 in RJ.
zs. zs.
hx_read FC RJ kmin 46%Z f Z46.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isdigitc_iff' c'' Rch) as DIF2.
zs. zs. zs. brf K4; kswrap K4.
-- assert (D2 : isdigitc c'' = true) by (apply (proj2 DIF2); clear -K4 Rch; Z.div_mod_to_equations; lia).
eapply (IH 0xda304%Z); try eassumption. all: hx_side.
-- assert (ND2 : isdigitc c'' = false) by (destruct (isdigitc c''); [exfalso; pose proof (proj1 DIF2 eq_refl) as DD; clear -K4 Rch DD; Z.div_mod_to_equations; lia | reflexivity]).
eapply (IH 0xda400%Z); try eassumption. all: hx_side.
+ assert (N46 : c <> 46%Z) by (clear -K1 Rcb; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
zs. zs. zs. brf K2; kswrap K2.
*
pose proof (lor32_af c Rcb ltac:(clear -K2 RL; Z.div_mod_to_equations; lia)) as RLc.
zs. (brf K3; [ | exfalso; lia ]). zs. (brf K4; [ exfalso; lia | ]). zs.
replace (Z_to_bv 64 (bv_swrap 32 (Z.lor c 32 + -87))) with (Z_to_bv 64 (Z.lor c 32 - 87)%Z) by (rewrite swrap32_small by lia; f_equal; lia).
eapply DIGIT; [ apply Bool.orb_true_iff; left; apply (proj2 HIF); lia | exact N46
| replace (c <=? 57)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity | clear -K2 RL RLc; Z.div_mod_to_equations; lia | reflexivity ].
*
assert (NH : ishexc c = false).
{ destruct (ishexc c) eqn:E; [|reflexivity]. exfalso. pose proof (proj1 HIF eq_refl) as CC0.
destruct CC0 as [C1 | C23].
- apply (proj2 DIF) in C1. rewrite C1 in ND. discriminate ND.
- pose proof (lor32_letter c C23) as [A B]. clear -K2 A. Z.div_mod_to_equations. lia. }
rewrite NH in HL. replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N46). cbn [orb] in HL. injection HL as <-.
cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
stmt HS_HTL. eapply NX; try eassumption. all: hx_side.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_HTL"] Lemma L_H7F0 : S_H7F0.
Proof.
intros m; intros until rp. intros _ HI HF RJ HKM FOK FRM' Hsg Hst Rcb Rgd Rgr Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
pose proof (lo64_range Y0) as R0l. pose proof (hi64_range Y0) as R0h. pose proof (lo64_range SC0) as R1l. pose proof (hi64_range SC0) as R1h.
unfold HX_dig in HK. destruct (hx_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
destruct s' as [c9 f9 x9 y9 sc9 gt9 gr9 gd9 rp9 dc9]. cbn [hx_c hx_f hx_x hx_y hx_gr hx_gd hx_rp hx_dc] in HK.
pose proof (isdigitc_iff' c Rcb) as DIF.
zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. zs. zs. brf K1; kswrap K1.
- assert (ND : isdigitc c = false) by (destruct (isdigitc c); [exfalso; pose proof (proj1 DIF eq_refl) as DD; clear -K1 Rcb DD; Z.div_mod_to_equations; lia | reflexivity]).
pose proof (L_HD fuelc 0xda400%Z) as NX; unfold Q4KR.Mqc.SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
- assert (D : isdigitc c = true) by (apply (proj2 DIF); clear -K1 Rcb; Z.div_mod_to_equations; lia).
zs.
pose proof (L_HD fuelc 0xda304%Z) as NX; unfold Q4KR.Mqc.SHDn in NX. eapply NX with (x := 0%Z) (dc := 0%Z) (gt := 0%Z); try eassumption. all: hx_side.
Qed.
End Floatscan.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0 Qx2n.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import QHB6.Mq3 QOy4 Q4KR.Mqc.
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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

#[using="Hp T1"] Lemma rf_slow_false : forall kmin c f, RFJ' kmin c f -> (T + sh_rpos f)%Z = rf_rend T p true f -> False.
Proof.
intros kmin c f RJ SLOW. destruct (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) as (STD & _).
destruct RJ as (_ & _ & _ & _ & _ & SS). destruct (SS STD) as (_ & _ & _ & _ & [_ FF]). exact FF.
Qed.
Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

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

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

Local Notation S_HTL := (@Q4KR.Mqc.S_HTL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HE2 := (@Q4KR.Mqc.S_HE2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HNL := (@Q4KR.Mqc.S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@Q4KR.Mqc.S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HZR := (@Q4KR.Mqc.S_HZR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mqc.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mqc.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation HX_e2' := (HX_e2 53 (-1074)).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mqc.hxinv, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mqc.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- Q4KR.Mqc.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mqc.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mqc.kminH _ _ _ => unfold Q4KR.Mqc.kminH; flia
| |- Q4KR.Mqc.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mqc.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

Hypothesis HS_HNL : S_HNL.
Hypothesis HS_HFIN : S_HFIN.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk usegs m (q - FS_DEPTH) q.
Proof.
intros until w56. intros HI HF. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="pre"] Lemma L_HRET : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda578) fct None m (seg_rom usegs)).
Proof.
intros until c. intros HI HF RJ Hk FOK FRM'.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range yR). pose proof (hi64_range yR).
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
apply evt_done. unfold fs_post, QHB6.Mq3.fs_post, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK|].
split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY|]. split; [split; [exact SSP1 | exact SSP2]|]. split; [exact ERR|].
split; [|exact FRM'].
intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="Type"] Lemma L_HZR : S_HZR.
Proof.
intros m; intros until c. intros _ HI HF RJ Hk FOK FRM' Hsg Hy.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
zs. destruct Hsg as [-> | ->]; (zs; zs; zs; zs; callx (eapply extenddftf2_callF; [eassumption | simpF; reflexivity]);
unfold hx_zero, D_ZERO in Hy; rewrite <- Hy; eapply L_HRET; try eassumption).
all: hx_side.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof.
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_HE2 : S_HE2.
Proof.
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_e2 in HK. replace (x =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia).
change (- (-1074))%Z with 1074%Z in HK. change (-1074 - 2 * LDBL_MANT_DIG_)%Z with (-1300)%Z in HK.
zs. zs. zs.
let v := getreg 24%Z in replace v with (Z_to_bv 64 (4 * rp + e2 - 32)%Z) by (apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2, ?land_W64 by lia; Z.div_mod_to_equations; lia).
set (E := (4 * rp + e2 - 32)%Z) in *.
assert (RE : (-2^62 <= E <= 2^62)%Z) by (subst E; lia).
zs. zs. zs. brf K1.
-
replace (1074 <? E)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
zs. zs. brf K2.
+
replace (E <? -1300)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
destruct (hx_norm_loop 33 (x, y, E)) as [[[x' y'] E']|] eqn:HN; [|discriminate HK].
pose proof (HX_fin_f _ _ _ _ _ _ _ HK) as Ef.
zs. brf K3.
*
assert (Rx2 : (2^31 <= x)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear -K3 A Rx; Z.div_mod_to_equations; lia).
rewrite hx_norm_loop_S in HN. replace (2 ^ 31 <=? x)%Z with true in HN by (symmetry; apply Z.leb_le; lia). injection HN as <- <- <-.
zs.
stmt HS_HFIN. eapply NX; try eassumption. all: hx_side.
* assert (Rx2 : (x < 2^31)%Z) by (destruct (sext32_u32_cases x ltac:(lia)) as [[A B]|[A B]]; rewrite B, ?land_W64 in K3; clear -K3 A Rx; Z.div_mod_to_equations; lia).
zs. zs. zs. zs.
stmt HS_HNL. eapply NX; try eassumption. all: hx_side. all: try (simpF; reflexivity).
+
replace (E <? -1300)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MIN) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MIN); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
-
replace (1074 <? E)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). injection HK as Ey.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs.
hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (M1 := f128_mul SF C_LDBL_MAX) in *. pose proof (lo64_range M1). pose proof (hi64_range M1).
zs. let v := getreg 12%Z in replace v with (Z_to_bv 64 (lo64 C_LDBL_MAX)) by (apply Z_to_bv_eqm; reflexivity).
zs. zs. zs.
hcall_split 80%Z (eapply mul_callE with (X := M1) (Y := C_LDBL_MAX); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. rewrite Ey. eapply L_HRET; try eassumption. all: hx_side.
Qed.

#[using="Type"] Lemma shl4_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 4)) = Z_to_bv 64 (sext32 (u32 (xv * 16))).
Proof.
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^4)%Z with 16%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma u32_mul16 : forall xv k, (0 <= xv)%Z -> u32 (u32 (xv * 16) * 16 ^ Z.of_nat k) = u32 (xv * 16 ^ Z.of_nat (S k)).
Proof.
clear. intros xv k Hx. unfold u32. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.

#[using="Type"] Lemma L_X16 : forall (k : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct (xv : Z),
(1 <= k <= 8)%nat -> (0 <= xv < 2^32)%Z ->
(forall xv', xv' = u32 (xv * 16 ^ Z.of_nat k) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 0) (Z_to_bv 64 (sext32 xv')) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda43c) fct None m (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (- Z.of_nat k)) (Z_to_bv 64 (sext32 xv)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda430) fct None m (seg_rom usegs)).
Proof.
induction k as [|k IH]; intros until xv; intros Hk Rxv KONT; [lia|].
zs. zs. rewrite shl4_step by lia. zs. brf K1; rewrite ?land_W64 in K1.
-
replace (Z_to_bv 64 (- Z.of_nat (S k) + 1)) with (Z_to_bv 64 (- Z.of_nat k)) by (f_equal; lia).
eapply IH; [clear -K1 Hk; Z.div_mod_to_equations; lia | apply u32_range |].
intros xv' ->. rewrite u32_mul16 by lia. apply KONT. reflexivity.
- assert (Ek : k = 0%nat) by (clear -K1 Hk; Z.div_mod_to_equations; lia). subst k.
replace (Z_to_bv 64 (- Z.of_nat 1 + 1)) with (Z_to_bv 64 0) by (f_equal; lia).
apply KONT. change (16 ^ Z.of_nat 1)%Z with 16%Z. reflexivity.
Qed.

#[using="Hpok1 BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F' : bvmap 5 word) (fc' : bv 32) (m : word -> option byte) (f : shfile) (kmin c : Z) (fS : shfile) (e10 : Z),
scanexp fuelc f pok = Some (fS, e10) ->
rw_cells usegs m Fp (rf_cells T p true f J) -> RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z ->
(sh_stdio f = true -> rtext T txt pre post /\ p = zlength pre) ->
bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
stk usegs m (q' - 240) q' -> (4096 <= q' - 240)%Z -> (q' <= Fp)%Z ->
(T + zlength txt <= q' - 240 \/ q' <= T)%Z -> (ssp_guard + 8 <= q' - 240)%Z -> (0 <= q')%Z -> (q' < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' k' c',
ms' = MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0' t1' t2' s0 s1 (Z_to_bv 64 e10) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra') fc' None m' (seg_rom usegs)
/\ munch [(q' - 240, q'); (Fp, Fp + 232)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q' - 240) q'
/\ rw_cells usegs m' Fp (rf_cells T p true fS J)
/\ RFJ' k' c' fS /\ (1 <= k')%Z
/\ bytes_at usegs m' T (zbytes txt)
/\ ssp_cells m' canary)
(MS (mkR ra' (Z_to_bv 64 q') gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 SCANEXP) fc' None m (seg_rom usegs)).
Proof.
intros until e10. intros HS FC RJ Hk Hc STX BY SSP ST Q1' Q2 Q3 Q4 Q5 Q6 MI.
pose proof scanexp_rspec as SX. unfold scanexp_rstmt in SX.
eapply evt_mono.
{ eapply SX with (pre := pre) (post := post); try eassumption; unfold SCANEXP_DEPTH; try flia; clear -Hpok; unfold hide2 in *; flia. }
intros ms' P. unfold scanexp_rpost, SCANEXP_DEPTH in P. exact P.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9D0 : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda480) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
zs. brf K1; rewrite ?land_W64 in K1.
- assert (Nx : x <> 0%Z) by (intros ->; apply K1; reflexivity).
stmt L_HE2. eapply NX; try eassumption. all: hx_side.
- assert (Ex : x = 0%Z) by (destruct (sext32_u32_cases x Rx) as [[A B]|[A B]]; rewrite B in K1; clear -K1 A Rx; Z.div_mod_to_equations; lia).
unfold HX_e2 in HK. rewrite Ex, Z.eqb_refl in HK. injection HK as Ey.
zs. stmt L_HZR. eapply NX; try eassumption. all: hx_side. all: symmetry; exact Ey.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 Q1 HS_HNL HS_HFIN"] Lemma L_H9B8 : forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (g : shfile) (x y rp : Z),
hxinv m ev g -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c g -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
HX_e2' sign (sh_unget g) x y (4 * rp + 0 - 32) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda468) fct None m (seg_rom usegs)).
Proof.
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin c g. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp kmin c g RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq g Hsn) in RJu, Ef, HK. rewrite <- Ef in RJu.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_H9D0 with (e2 := 0%Z) (ev := ev); try eassumption. all: hx_side.
unfold Q4KR.Mqc.hxinv. rewrite Ef. mk_hxinv. rewrite Ef in HK |- *. exact HK.
Qed.

#[using="fc pre post kmin0 c0 Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_H98C : forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign kmin c (f : shfile) (x y rp : Z),
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z ->
match (if (Z.lor c 32 =? 112)%Z then
match scanexp fuelc f pok with
| None => None
| Some (f, e2) =>
if (e2 =? LLONG_MIN_)%Z then
(if nz pok then Some (inl (sh_unget f, 0%Z))
else Some (inr (sh_lim0 f, f128_of_i32 0)))
else Some (inl (f, e2))
end
else Some (inl (sh_unget f, 0%Z))) with
| None => None
| Some (inr r) => Some r
| Some (inl (f, e2)) => HX_e2' sign f x y (4 * rp + e2 - 32)
end = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda43c) fct None m (seg_rom usegs)).
Proof.
intros until rp. intros HI HF RJ Hk FOK FRM' Hsg Hst Rcb Rx Rrp0 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
site_facts FC RJ kmin c f.
zs. zs. zs. brf K1.
-
and33n K1 c Rcb 80%Z N1. replace (Z.lor c 32 =? 112)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
eapply L_H9B8; try eassumption. all: hx_side.
- and33y K1 c Rcb 80%Z E1. rewrite E1, Z.eqb_refl in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in E1; discriminate E1).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
zs. zs. zs. zs.
hcall_split 240%Z (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | flia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| eassumption | eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ fS _) |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
zs. zs. zs. brf K2; rewrite ?land_W64 in K2.
+
assert (Hne : e10 <> LLONG_MIN_) by (intros E; apply K2; rewrite E; vm_compute; reflexivity).
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne).
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
pose proof (HX_e2_f _ _ _ _ _ _ _ HK) as Ef.
eapply L_H9D0 with (ev := ev); try eassumption. all: hx_side.
unfold Q4KR.Mqc.hxinv. rewrite Ef. mk_hxinv. rewrite Ef. exact RJ2. flia. rewrite Ef in HK |- *. exact HK.
+ assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear -K2 R; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; lia]).
rewrite Ee, Z.eqb_refl in HK. replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity).
rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_H9B8 with (ev := ev); try eassumption. all: hx_side.
Qed.

#[using="Hpok1 ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_HNL HS_HFIN"] Lemma L_HTL : S_HTL.
Proof.
intros m; intros until dc. intros _ HI HF RJ HKM FOK FRM' Hsg Hst HXI HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
destruct HXI as (Rcb & Rx & Rgt & Rgr & Rgd & Rdc & Rrp0). destruct HKM as [Hk1 Hk2].
site_facts FC RJ kmin c f. destruct (rfj_ns _ _ _ RJ) as [Hns Hsn]. specialize (KM Hsn).
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
unfold HX_tail in HK.
zs. brf K1; rewrite ?land_W64 in K1.
-
assert (Eg : gd = 0%Z) by (clear -K1 Rgd; Z.div_mod_to_equations; lia). specialize (Hk2 Eg).
replace (negb (nz gd)) with true in HK by (rewrite Eg; reflexivity). replace (nz pok) with true in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. zs0. zs. rewrite Hpok1. zs. (brf K3; [ exfalso; lia | ]). rewrite <- Hpok1. zs. zs0.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
assert (Hsn1 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
pose proof (RFI_unget T txt p J Hp (kmin - 1) c (sh_unget f) RJu ltac:(flia)) as RJu2.
assert (Hsn2 : sh_shlim_neg (sh_unget (sh_unget f)) = false) by (rewrite (rf_unget_eq _ Hsn1); cbn; exact Hsn1).
zs. brf K4; rewrite ?land_W64 in K4.
+
assert (Er : gr = 0%Z) by (clear -K4 Rgr; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu2. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu2. rewrite Ef in RJu2.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold Q4KR.Mqc.hxinv; rewrite <- Ef; mk_hxinv.
+ assert (Er : gr = 1%Z) by (clear -K4 Rgr; Z.div_mod_to_equations; lia). rewrite Er in HK. cbn [nz Z.eqb negb] in HK. injection HK as Ef Ey.
pose proof (RFI_unget T txt p J Hp (kmin - 1 - 1) c _ RJu2 ltac:(flia)) as RJu3.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in Ef. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in Ef.
rewrite (rf_unget_eq _ Hsn2), (rf_unget_eq _ Hsn1), (rf_unget_eq f Hsn) in RJu3. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJu3. rewrite Ef in RJu3.
zs. zs0. zs.
stmt L_HZR. eapply NX with (ev := ev); try eassumption. all: hx_side. all: unfold Q4KR.Mqc.hxinv; rewrite <- Ef; mk_hxinv.
-
assert (Eg : gd = 1%Z) by (clear -K1 Rgd; Z.div_mod_to_equations; lia).
replace (negb (nz gd)) with false in HK by (rewrite Eg; reflexivity). cbv iota in HK.

assert (G974 : forall rpF, rpF = (if nz gr then rp else dc) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rpF) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda424) fct None m (seg_rom usegs))).
{ intros rpF ErpF. rewrite <- ErpF in HK. cbv zeta in HK.
assert (RrpF : (-2^32 <= rpF <= 2^32)%Z) by (subst rpF; destruct (nz gr); flia).
zs. zs. brf K2.
-
replace (dc <=? 7)%Z with false in HK by (symmetry; apply Z.leb_gt; lia).
eapply L_H98C; try eassumption. all: hx_side.
- replace (dc <=? 7)%Z with true in HK by (symmetry; apply Z.leb_le; lia).
zs. replace (Z_to_bv 64 (dc + -8)) with (Z_to_bv 64 (- Z.of_nat (Z.to_nat (8 - dc)))) by (f_equal; lia).
eapply (L_X16 (Z.to_nat (8 - dc))); [lia | exact Rx |]. intros xv' Exv.
replace (Z.of_nat (Z.to_nat (8 - dc))) with (8 - dc)%Z in Exv by lia. rewrite <- Exv in HK.
eapply L_H98C; try eassumption. all: hx_side. all: subst xv'; apply u32_range. }
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ assert (Er : gr = 0%Z) by (clear -K2 Rgr; Z.div_mod_to_equations; lia).
apply G974. rewrite Er. reflexivity.
+ assert (Er : gr = 1%Z) by (clear -K2 Rgr; Z.div_mod_to_equations; lia).
zs. apply G974. rewrite Er. reflexivity.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHB6.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOy4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOy4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4KR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4KR.Mqc.
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

Local Notation FokR := (@QHB6.Mq3.FokR F).
Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).

Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
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
Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
Ltac unbury := unfold hide2 in *.
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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
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

Local Notation S_HNL := (@Q4KR.Mqc.S_HNL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HFIN := (@Q4KR.Mqc.S_HFIN ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation hxfr := (@Q4KR.Mqc.hxfr ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F).
Local Notation hxinv := (@Q4KR.Mqc.hxinv q m0 Fp T p J txt canary).
Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Ltac dest_hxinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let ST := fresh "ST" in let TXT := fresh "BY" in
let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let ERR := fresh "ERR" in let FC := fresh "FC" in
destruct H as (MI & MU & WM & ST & TXT & SSP1 & SSP2 & ERR & FC); unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST; unfold RERRNO in ERR;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Ltac mk_hxinv := unfold Q4KR.Mqc.hxinv, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; unfold M64; hyp_cells
| unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg];
repeat match goal with H : ?b = false |- context [?b] => rewrite H end; unfold M64; hyp_cells ].
Ltac mk_hxfr := norm_m1074; unfold Q4KR.Mqc.hxfr; first [hyp | hyp_cells].
Tactic Notation "hcall_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -176)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -176 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -176 - K)%Z (q + -176)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -176 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

Ltac hx_side := try lazymatch goal with
| |- Q4KR.Mqc.hxinv _ _ _ _ _ _ _ _ _ _ _ => mk_hxinv
| |- Q4KR.Mqc.hxfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => mk_hxfr
| |- Q4KR.Mqc.kminH _ _ _ => unfold Q4KR.Mqc.kminH; flia
| |- Q4KR.Mqc.hxI _ _ _ _ _ _ _ _ => unfold Q4KR.Mqc.hxI; cbn [sh_rpos]; flia
| |- (_ = _ /\ _) \/ _ => first [left; split; [reflexivity | assumption] | right; split; [reflexivity | assumption]]
| |- sh_stdio _ = sh_stdio _ => cbn [sh_stdio]; first [assumption | symmetry; assumption]
| |- Fok _ => fok
| |- frm0 _ => assumption
| |- (_ <= _)%Z => flia | |- (_ < _)%Z => flia | |- (_ <= _ < _)%Z => flia | |- (_ <= _ <= _)%Z => flia | |- (_ < _ <= _)%Z => flia | |- (_ < _ < _)%Z => flia
| |- @eq Z _ _ => flia
| |- _ => idtac end.

#[using="pre"] Lemma hx_release : forall m ev f w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev f -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> stk usegs m (q - FS_DEPTH) q.
Proof.
intros until w56. intros HI HF. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF.
release_frame HF ST q. unfold FS_DEPTH. exact ST.
Qed.

#[using="Type"] Lemma shl1_step : forall xv, (0 <= xv < 2^32)%Z ->
Z_to_bv 64 (bv_swrap 32 (Z.shiftl (Z.land (sext32 xv) 18446744073709551615) 1)) = Z_to_bv 64 (sext32 (u32 (2 * xv))).
Proof.
clear. intros xv Hx. rewrite Z_to_bv_swrap32. f_equal. apply sext32_congr. unfold u32.
rewrite land_W64, Z.shiftl_mul_pow2 by lia. change (2^1)%Z with 2%Z. change (2^32)%Z with 4294967296%Z. change (2^64)%Z with 18446744073709551616%Z.
pose proof (sext32_low xv) as L. pose proof (sext32_range xv) as R. rewrite (Z.mod_small xv) in L by lia.
set (S := sext32 xv) in *. clearbody S. Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma lor1_even : forall a, (a mod 2 = 0)%Z -> Z.lor a 1 = (a + 1)%Z.
Proof.
clear. intros a Ha. assert (L : Z.land a 1 = 0%Z) by (change 1%Z with (Z.ones 1); rewrite Z.land_ones; [exact Ha | lia]).
rewrite <- Z.lxor_lor, Z.add_nocarry_lxor by exact L. reflexivity.
Qed.
#[using="Type"] Lemma sext32_succ_even : forall a, (0 <= a < 2^32)%Z -> (a mod 2 = 0)%Z -> sext32 (a + 1) = (sext32 a + 1)%Z /\ (sext32 a mod 2 = 0)%Z.
Proof.
clear. intros a Ha Ea. rewrite !sext32_eq. change (2^32)%Z with 4294967296%Z in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma sext32_u32_cases : forall x, (0 <= x < 2^32)%Z ->
((x < 2^31)%Z /\ sext32 x = x) \/ ((2^31 <= x)%Z /\ sext32 x = (x + 18446744069414584320)%Z).
Proof.
clear. intros x Hx. rewrite sext32_eq. change (2^31)%Z with 2147483648%Z. change (2^32)%Z with 4294967296%Z in Hx.
destruct (Z.lt_ge_cases x 2147483648) as [L|G]; [left | right]; split; try lia; Z.div_mod_to_equations; lia.
Qed.

#[using="pre SPF SPT SG1"] Lemma hx_post_tail : forall m m' F' fc' k c ev w0 w8 w16 w24 w32 w40 w48 w56,
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m -> RFJ' k c fR -> (0 <= k)%Z ->
FokR F' -> frm0 fc' ->
munch [(q - 112, q)]%Z m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' (q - 112) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom usegs)).
Proof.
intros until w56. intros HI HF RJ Hk FOK FRM' MU2 WM2 MI2 ST2. intros.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI HF) as STK. unfold FS_DEPTH in STK.
dest_hxinv HI. bury_disj. unbury.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 _].
unfold fs_post, QHB6.Mq3.fs_post, QHB6.Mq3.Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split.
{ eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST2 | lia ]. }
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="pre SPLO SPF SPT SG1 Q1"] Lemma L_HCFC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w40 w48 w56 : word) k c (Y e2 : Z),
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 w40 w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda7ac) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' He2 Hy.
pose proof HI as HI0. pose proof HF as HF0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. rewrite ?swrap32_landW. rewrite swrap32_small by lia.
zs. zs.
do 14 zs. zs. zs.
pose proof (hx_release _ _ _ _ _ _ _ _ _ _ _ HI0 HF0) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof scalbnl_spec as SS. unfold scalbnl_stmt in SS.
replace (Z_to_bv 64 (q + -176 + 176)) with (Z_to_bv 64 q) by (f_equal; lia).
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. unbury. eapply (hx_post_tail m m'); try eassumption.
intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.

#[using="pre Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HC64 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w48 w56 : word) sign k c (x y BI e2 : Z),
hxinv m ev fR -> hxfr w0 (Z_to_bv 64 (hi64 BI)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> (0 <= x < 2^32)%Z -> (-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl (f128_sub (f128_add (f128_mul (f128_of_i32 sign) y) (f128_add (f128_mul (f128_of_i32 sign) (f128_of_u32 x)) BI)) BI) e2 ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda714) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros HI HF RJ Hk FOK FRM' Hsg Rx He2 Hy.
pose proof HI as HI0. dest_hxinv HI. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (lo64_range BI). pose proof (hi64_range BI).
pose proof (sext32_range x) as RSx.
zs. destruct Hsg as [Hsg | Hsg]; rewrite Hsg in *.
all: zs; callx (eapply floatsitf_callsg; [eassumption | lia]).
all: set (SF := f128_of_i32 _) in *; pose proof (lo64_range SF); pose proof (hi64_range SF).
all: zs; zs; zs; zs; callx (eapply floatunsitf_callv with (u := x); [eassumption | lia | reflexivity]).
all: set (XF := f128_of_u32 x) in *; pose proof (lo64_range XF); pose proof (hi64_range XF).
all: zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V1 := f128_mul SF XF) in *; pose proof (lo64_range V1); pose proof (hi64_range V1).
all: zs; zs; zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V1) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V2 := f128_add V1 BI) in *; pose proof (lo64_range V2); pose proof (hi64_range V2).
all: zs; zs; zs; zs; zs; zs; zs.
all: hcall_split 80%Z (eapply mul_callE with (X := SF) (Y := y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V3 := f128_mul SF y) in *; pose proof (lo64_range V3); pose proof (hi64_range V3).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply add_callE with (X := V3) (Y := V2); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (V4 := f128_add V3 V2) in *; pose proof (lo64_range V4); pose proof (hi64_range V4).
all: zs; zs; zs.
all: hcall_split 48%Z (eapply sub_callE with (X := V4) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
all: set (YF := f128_sub V4 BI) in *; pose proof (lo64_range YF); pose proof (hi64_range YF).
all: zs; zs; zs; zs; zs; callx (eapply letf2_callE with (X := YF) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
all: pose proof (f128_le_range YF 0) as RLE.
all: zs; brf K1.
1,3: eapply L_HCFC; try eassumption; hx_side.
all: zs; callx (eapply errno_loc_spec; eassumption).
all: zs; unfold RERRNO; zs0.
all: eapply L_HCFC; try eassumption; hx_side.
Qed.
#[using="Type"] Lemma sgtz_b2z : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808) = (if 0 <? E then 1 else 0)%Z.
Proof.
clear. intros E HE. rewrite (land_W64 E). change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (Z.div_mod_to_equations; lia).
destruct (Z.ltb_spec 0 E).
- replace (2^63 <? _)%Z with true; [reflexivity|]. symmetry. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
- replace (2^63 <? _)%Z with false; [reflexivity|]. symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma bits_clamp : forall E, (-2^62 <= E <= 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land E 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land E 18446744073709551615) = Z.max 0 E.
Proof.
clear. intros E HE. rewrite sgtz_b2z by lia. destruct (Z.ltb_spec 0 E).
- change (0 - 1)%Z with (-1)%Z. rewrite Z.land_m1_l. rewrite (land_W64_small E) by lia. rewrite Z.land_comm, land_W64_small by lia. lia.
- change (0 - 0)%Z with 0%Z. rewrite !Z.land_0_l. lia.
Qed.
#[using="Type"] Lemma land1_sext32 : forall x, (0 <= x < 2^32)%Z -> Z.land (sext32 x) 1 = (x mod 2)%Z.
Proof.
clear. intros x Hx. change 1%Z with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1)%Z with 2%Z.
rewrite sext32_eq. change (2^32)%Z with 4294967296%Z in Hx. Z.div_mod_to_equations. lia.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HFIN : S_HFIN.
Proof.
intros m; intros until e2. intros _ HI HF RJ Hk FOK FRM' Hsg Rx Re2 HK.
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh. pose proof (sext32_range x) as RSx.
unfold HX_fin in HK.
remember (if (53 <=? 32 + e2 - -1074)%Z then 53%Z else Z.max 0 (32 + e2 - -1074)) as bits eqn:Eb in HK.
assert (Rb : (0 <= bits <= 53)%Z) by (subst bits; destruct (Z.leb_spec 53 (32 + e2 - -1074))%Z; lia).
replace (bits <=? 112)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv zeta in HK.

assert (G : forall (xa xb : word),
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 xa xb x12 x13 x14 x15 x16 x17
(Z_to_bv 64 bits) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda67c) fct None m (seg_rom usegs))).
2: { zs. zs. zs. zs. brf K1.
- replace (53 <=? 32 + e2 - -1074)%Z with true in Eb by (symmetry; apply Z.leb_le; lia). subst bits. apply G.
- replace (53 <=? 32 + e2 - -1074)%Z with false in Eb by (symmetry; apply Z.leb_gt; lia).
zs. fixw3. zs. zs. zs.
let v := getreg 18%Z in replace v with (Z_to_bv 64 bits) by (rewrite bits_clamp by lia; f_equal; rewrite Eb; lia).
let v := getreg 11%Z in set (JK := v); clearbody JK.
apply G. }
intros xa xb.
zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. zs. zs. zs.
rewrite !swrap32_small by lia. rewrite Z.add_0_r.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]).
lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (144 - bits)) with D1 in HK.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (HB := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range HB). pose proof (hi64_range HB).
zs. zs. zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs. callx (eapply copysignl_callE with (X := HB) (Y := SF); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl HB SF) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. brf K3.
-
replace (bits <=? 31)%Z with false in HK by (symmetry; apply Z.leb_gt; clear -K3 Rb; Z.div_mod_to_equations; lia).
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
- replace (bits <=? 31)%Z with true in HK by (symmetry; apply Z.leb_le; clear -K3 Rb; Z.div_mod_to_equations; lia).
zs. zs. zs. zs. zs. callx (eapply letf2_callE with (X := y) (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range y 0) as RLE. set (LE := f128_le y 0) in *.
zs. zs. brf K4; rewrite (land1_sext32 x) in K4 by lia; rewrite Zmod_odd in K4.
+
replace (Z.odd x) with true in HK by (destruct (Z.odd x); [reflexivity | exfalso; apply K4; reflexivity]). cbn [negb andb] in HK.
injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
+ replace (Z.odd x) with false in HK by (destruct (Z.odd x); [exfalso; clear -K4; lia | reflexivity]). cbn [negb andb] in HK.
assert (Ex2 : (x mod 2 = 0)%Z) by (rewrite Zmod_odd; destruct (Z.odd x); [exfalso; clear -K4; lia | reflexivity]).
zs. zs. brf K5; rewrite ?land_W64 in K5.
*
assert (EL : LE = 0%Z) by (clear -K5 RLE; Z.div_mod_to_equations; lia).
replace (nz LE) with false in HK by (rewrite EL; reflexivity). injection HK as Ey.
zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
* assert (NL : LE <> 0%Z) by (clear -K5 RLE; Z.div_mod_to_equations; lia).
replace (nz LE) with true in HK by (unfold nz; symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact NL). injection HK as Ey.
rewrite lor1_even in Ey by exact Ex2.
destruct (sext32_succ_even x ltac:(lia) Ex2) as [SE1 SE2].
zs. rewrite ?land_W64_small by lia. rewrite (lor1_even (sext32 x)) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
zs. zs. zs. eapply L_HC64; try eassumption. all: hx_side. all: try (symmetry; exact Ey).
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 Q1"] Lemma L_HNL : S_HNL.
Proof.
intros n. induction n as [|n IH]; intros m; intros until e2'; intros _ HI HF RJ Hk FOK FRM' Hsg HF5 Rx Re2 HL HK; [discriminate HL|].
pose proof HI as HI0. dest_hxinv HI. pose proof HF as HF0. unfold Q4KR.Mqc.hxfr in HF. bury_disj.
pose proof (lo64_range y) as Ryl. pose proof (hi64_range y) as Ryh.
rewrite hx_norm_loop_S in HL. replace (2 ^ 31 <=? x)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
unfold hx_norm_body in HL. replace (u32 (2 * x)) with (2 * x)%Z in HL by (unfold u32; symmetry; apply Z.mod_small; lia).
set (H5 := f128_of_d (bv_unsigned D_05)) in *. pose proof (lo64_range H5). pose proof (hi64_range H5).
assert (Rn : (Z.of_nat (S n) = Z.of_nat n + 1)%Z) by lia. rewrite Rn in Re2.

assert (TAIL : forall m1 (x1' x5' x6' x7' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word) Ft1 fct1 (x2 y2 : Z),
hxinv m1 ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m1 ->
Fok Ft1 -> frm0 fct1 -> reg_get Ft1 8 = D_05 -> (2 * x <= x2 <= 2 * x + 1)%Z ->
hx_norm_loop n (x2, y2, e2 - 1)%Z = Some (x', y', e2') ->
evt usegs POST
(MS (mkR x1' HSP gp TPv x5' x6' x7' (Z_to_bv 64 (-1074)) x9 (Z_to_bv 64 (lo64 y2)) (Z_to_bv 64 (hi64 y2)) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x2)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28' x29' x30' x31')
Ft1 (Z_to_bv 64 0xda600) fct1 None m1 (seg_rom usegs))).
{ intros until y2. intros HI1 HF1 FOK1 FRM1 HF51 Rx2 HL2. clear HL.
clear MI MU WM ST BY SSP1 SSP2 ERR FC HF. dest_hxinv HI1. unfold Q4KR.Mqc.hxfr in HF1.
pose proof (lo64_range y2). pose proof (hi64_range y2).
zs. zs. zs. replace (Z_to_bv 64 (e2 + -1)) with (Z_to_bv 64 (e2 - 1)%Z) by (f_equal; lia).
destruct (sext32_u32_cases x2 ltac:(lia)) as [[A B]|[A B]].
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [clear -K1 A Rx; exfalso; Z.div_mod_to_equations; lia|].
eapply IH; try eassumption. all: hx_side.
-
zs. brf K1; rewrite ?B, ?land_W64 in K1; [|clear -K1 A Rx; exfalso; Z.div_mod_to_equations; lia].
destruct n as [|n2]; [discriminate HL2|]. rewrite hx_norm_loop_S in HL2.
replace (2 ^ 31 <=? x2)%Z with true in HL2 by (symmetry; apply Z.leb_le; lia). injection HL2 as <- <- <-.
stmt L_HFIN. eapply NX; try eassumption. all: hx_side. }
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D_05); [eassumption | simpF; rewrite <- HF5; do 2 f_equal; apply bv_eq; vm_compute; reflexivity]).
fold H5.
zs. zs. zs. zs. zs. callx (eapply getf2_callE with (X := y) (Y := H5); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range y H5) as RGE. set (GE := f128_ge y H5) in *.
zs. rewrite shl1_step by lia. replace (u32 (2 * x)) with (2 * x)%Z by (unfold u32; symmetry; apply Z.mod_small; lia).
zs. brs K1.
-
replace (0 <=? GE)%Z with true in HL by (symmetry; apply Z.leb_le; lia).
rewrite lor1_even in HL by (Z.div_mod_to_equations; lia).
destruct (sext32_succ_even (2 * x) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as [SE1 SE2].
pose proof (sext32_range (2 * x)) as RS2.
zs. rewrite ?land_W64. rewrite (lor1_even (sext32 (2 * x))) by exact SE2. rewrite <- SE1.
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
set (ONE := f128_of_i32 1) in *. pose proof (lo64_range ONE). pose proof (hi64_range ONE).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply sub_callE with (X := y) (Y := ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (YM1 := f128_sub y ONE) in *. pose proof (lo64_range YM1). pose proof (hi64_range YM1).
zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := YM1); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
-
replace (0 <=? GE)%Z with false in HL by (symmetry; apply Z.leb_gt; lia).
zs. zs. zs. zs. zs. zs.
hcall_split 48%Z (eapply add_callE with (X := y) (Y := y); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply TAIL; try eassumption. all: hx_side. all: try (simpF; first [exact HF5 | reflexivity]).
Qed.
End Floatscan.
