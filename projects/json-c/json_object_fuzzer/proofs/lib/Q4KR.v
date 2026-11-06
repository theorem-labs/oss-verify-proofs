(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx Q7wb Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX QwyL QhHa QN1y Q48O QGmo QTS6 QvBB QnkH Qi8L QmBS QKwd Qlfl QjhR QCqH QTp6 QHB6 QOy4.
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
Import QHB6.Mq0 QOy4.Mq3.
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
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| [CB 8 _] => fail
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
lazymatch cs with ?c0 :: ?l => go constr:([c0]) l end end.

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

Local Notation S_WS := (@QOy4.Mq3.S_WS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_AWS := (@QOy4.Mq3.S_AWS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_I1 := (@QOy4.Mq3.S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N1 := (@QOy4.Mq3.S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

Hypothesis HS_I1 : S_I1.
Hypothesis HS_N1 : S_N1.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_AWS : S_AWS.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hr1 Rcb Hns HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_sign in HK.

assert (GOI : forall m2 (x8' x10' x11' x12' : word) sg c2 (f2 : shfile) k2,
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f2 -> RFJ' k2 c2 f2 -> (1 <= k2)%Z -> sh_stdio f2 = sh_stdio f0 ->
(sg = 1 \/ sg = -1)%Z -> (0 <= c2 < 256)%Z -> (c2 <> (-1)%Z -> 1 <= sh_rpos f2)%Z ->
FS_infk' sg 0 c2 f2 = Some (fR, yR) ->
forall K : Prop, ((Z.land c2 18446744073709551583 = 73%Z /\ K = (evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) x10' x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd64c8) fc None m2 (seg_rom rsegs))))
\/ (Z.land c2 18446744073709551583 <> 73%Z /\ K = (evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) (Z_to_bv 64 c2) (Z_to_bv 64 (Z.land c2 18446744073709551583)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6500) fc None m2 (seg_rom rsegs))))) -> K).
{ intros m2 x8' x10' x11' x12' sg c2 f2 k2 WI2 RJ2 Hk2 Hst2 Hsg Rc2 Hr2 HK2 K [[E73 ->] | [N73 ->]].
- and33y E73 c2 Rc2 73%Z E1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
rewrite E1, Z.eqb_refl in HK2. change (0 <? 7)%Z with true in HK2. cbv iota in HK2.
stmt HS_I1. eapply NX; try eassumption; try flia.
- and33n N73 c2 Rc2 73%Z N1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
replace (Z.lor c2 32 =? 105)%Z with false in HK2 by (symmetry; apply Z.eqb_neq; exact N1). rewrite FS_inf_0 in HK2.
stmt HS_N1. eapply NX; try eassumption; try flia. }
assert (SGN : forall x11', (c = 43%Z \/ c = 45%Z) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6494) fc None m (seg_rom rsegs))).
{ intros x11' Hc.
assert (Hc0 : c <> 0%Z) by lia.
replace ((c =? 43) || (c =? 45))%Z with true in HK by (destruct Hc as [-> | ->]; reflexivity).
set (sg := (1 - 2 * b2z (c =? 45))%Z) in HK. assert (Hsg : (sg = 1 \/ sg = -1)%Z) by (subst sg; destruct (c =? 45)%Z; cbn; lia).
rewrite (surjective_pairing (sh_getc f)) in HK. cbv beta iota zeta in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf Kc.
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (right; split; [clear -Kc Rch; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK].
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (left; split; [clear -Kc Rch; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK]. }
zs. zs. brf Ka.
-
assert (E45 : c = 45%Z) by (clear -Ka Rcb; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
apply SGN. right. exact E45.
- assert (N45 : c <> 45%Z) by (clear -Ka Rcb; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
zs. zs. brf Kb.
+
assert (N43 : c <> 43%Z) by (clear -Kb Rcb; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
replace ((c =? 43) || (c =? 45))%Z with false in HK by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N43), (proj2 (Z.eqb_neq _ _) N45); reflexivity).
zs. zs. zs. zs. brf Kc.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (left; split; [clear -Kc Rcb; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (right; split; [clear -Kc Rcb; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
+ assert (E43 : c = 43%Z) by (clear -Kb Rcb; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
apply SGN. left. exact E43.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_WS : S_WS.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk Hc0 Hst HL HK; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite fs_ws_loop_S in HL.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HL.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isspace_iff c'' Rch) as SPI.
assert (LOOP : forall m2 (x10' x11' : word), m_isspace c'' = true ->
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10' x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6460) fc None m2 (seg_rom rsegs))).
{ intros m2 x10' x11' SP WI2. rewrite SP in HL.
assert (Hc1 : c'' <> 0%Z) by (intros E0; rewrite E0 in SP; discriminate SP).
eapply (IH m2); try eassumption; try flia. }
zs. zs. brf K1.
-
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). right. clear -K1 Rch. rewrite ?land_W64 in K1. Z.div_mod_to_equations; lia.
- zs. brf K2.
+
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). left. clear -K2 Rch. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
+
assert (NSP : m_isspace c'' = false).
{ destruct (m_isspace c''); [|reflexivity]. exfalso. pose proof (proj1 SPI eq_refl) as SPD. clear -K1 K2 Rch SPD. rewrite ?land_W64 in K1. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia. }
rewrite NSP in HL. injection HL as <- <-.
stmt L_AWS. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia. mk_winv2. cbn [sh_rpos]. intros _. flia.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_I1 HS_N1"] Lemma L_ENTRYh : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
floatscan_h fuelc f0 1 pok = Some (fR, yR) ->
stk rsegs m0 (q - FS_DEPTH) q -> mem_inv rsegs m0 ->
rw_cells rsegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at rsegs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells rsegs m0 RERRNO [C4 ev] ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom rsegs)).
Proof.
intros until ev. intros _ HMh ST MI FC RJ Hk0 Hc0 Hst BY [SSP1 SSP2] ERR.
pose proof (munch_refl Wfs m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold QHB6.Mq0.Wfs, FS_DEPTH, RERRNO in MU. unfold FS_DEPTH in ST.
unfold got_ssp, ssp_guard in SSP1, SSP2. unfold RERRNO in ERR.
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T.
pose proof zbytes_len as LTX. unfold zlength in *. bury_disj.
site_facts FC RJ kmin0 c0 f0.

pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0) as RJ1.
pose proof (getc_stdio f0) as Hst1.
assert (Rc1 : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f0 Hbuf) as [Rrp1 Rrp2].
unfold FLOATSCAN.

zs.
carve_frame 120%nat ST. rename FR into FRhi.
do 14 zs.
lazymatch type of FRhi with rw_cells _ _ _ (CB 8 ?b :: _) => set (jc := b) in FRhi; clearbody jc end.
zs. zs.
replace (Z_to_bv 64 (q + -2032 - 4096))%Z with (Z_to_bv 64 (q + -6128))%Z by (f_equal; lia).

assert (Hcv1 : (q - 8656 <= q + -120 - Z.of_nat (Z.to_nat 6000))%Z) by lia;
destruct (stk_carve rsegs _ _ _ (Z.to_nat 6000) ST Hcv1) as [ST' [junka XBa]]; clear ST Hcv1; rename ST' into ST;
replace (q + -120 - Z.of_nat (Z.to_nat 6000))%Z with (q + -6120)%Z in ST, XBa by lia.
assert (Hcv2 : (q - 8656 <= q + -6120 - Z.of_nat 8)%Z) by lia;
destruct (stk_carve rsegs _ _ _ 8%nat ST Hcv2) as [ST' [junkb XBb]]; clear ST Hcv2; rename ST' into ST;
replace (q + -6120 - Z.of_nat 8)%Z with (q + -6128)%Z in ST, XBb by lia.
assert (Hcv3 : (q - 8656 <= q + -6128 - Z.of_nat (Z.to_nat 2184))%Z) by lia;
destruct (stk_carve rsegs _ _ _ (Z.to_nat 2184) ST Hcv3) as [ST' [junkc XBc]]; clear ST Hcv3; rename ST' into ST;
replace (q + -6128 - Z.of_nat (Z.to_nat 2184))%Z with (q + -8312)%Z in ST, XBc by lia.
zs.
release_frame XBc ST (q + -6128)%Z. release_frame XBb ST (q + -6120)%Z. release_frame XBa ST (q + -120)%Z.
clear junka junkb junkc.
let n := eval vm_compute in (Z.to_nat 8192) in
assert (Hcv : (q - 8656 <= q + -120 - Z.of_nat n)%Z) by (change (Z.of_nat n) with 8192%Z; lia);
destruct (stk_carve rsegs _ _ _ n ST Hcv) as [ST' [junkx XB2]]; clear ST Hcv; rename ST' into ST;
change (Z.of_nat n) with 8192%Z in ST, XB2.
replace (q + -120 - 8192)%Z with (q + -8312)%Z in ST, XB2 by lia.
pose proof XB2 as XB0. destruct XB0 as [[[LB _] _] _]. cbn in LB.
apply u8arr_of_rw_cells in XB2.
destruct (u32arr_of_u8arr rsegs _ _ _ 2048%nat XB2 ltac:(rewrite LB; reflexivity)) as (ws0 & LW0 & XW). clear XB2 LB junkx.
zs. zs.
replace (Z_to_bv 64 (q + -6128 + -2048 + -240))%Z with SPv by (f_equal; lia).
carve_frame 104%nat ST. rename FR into LOW.
apply (rw_cells_split_CB _ _ _ [] 104 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
do 11 (c8ify LOW).
lazymatch type of LOW with rw_cells _ _ _ [CB 8 ?a; C8 ?b1; C8 ?b2; C8 ?b3; C8 ?b4; C8 ?b5; C8 ?b6; C8 ?b7; C8 ?b8; C8 ?b9; C8 ?b10; C8 ?b11; CB 8 ?c] =>
set (j0 := a) in LOW; set (w8 := b1) in LOW; set (w16 := b2) in LOW; set (w24 := b3) in LOW; set (w32 := b4) in LOW;
set (w40 := b5) in LOW; set (w48 := b6) in LOW; set (w56 := b7) in LOW; set (w64 := b8) in LOW; set (w72 := b9) in LOW;
set (w80 := b10) in LOW; set (w88 := b11) in LOW; set (b96 := c) in LOW;
clearbody j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 end.
match goal with H : list byte |- _ => try clear H end.

zs. zs. zs. zs. zs. zs. zs. zs.

zs. (brf K1; [ exfalso; lia | ]). zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs. zs. zs. zs. zs.
clear K1 K2 K3.

rewrite floatscan_h_1 in HMh. destruct (fs_ws_loop fuelc f0) as [[c1 f1]|] eqn:HWS; [|discriminate HMh].
eapply (L_WS fuelc) with (kmin := kmin0) (c := c0) (f := f0); try eassumption; try flia.
mk_winv2.
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
Import QHB6.Mq0 QOy4.Mq3.
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

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation L_RET30 := (@QHB6.Mq0.L_RET30 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_I1 := (@QOy4.Mq3.S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@QOy4.Mq3.S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@QOy4.Mq3.S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_A38 : S_A38.
Proof.
intros m; intros until v. intros _ WI RJ Hk FOK FRM' SP E10. pose proof WI as WI0. dest_winv WI. bury_disj.
zs.
zs. match goal with |- context [reg_get Ft ?i] => rewrite (E10 i) by (vm_compute; reflexivity) end.
destruct SP as [[-> Hy] | [[-> Hy] | [-> Hy]]];
match goal with |- context [sx32 ?v] => let w := eval vm_compute in (bv_swrap 32 (bv_unsigned v)) in change (sx32 v) with (Z_to_bv 64 w) end;
(do 5 zs; (brf K1; [ exfalso; lia | ]); zs; zs; (brf K2; [ exfalso; lia | ]); do 11 zs);
(let a := getreg 10%Z in let b := getreg 11%Z in
lazymatch type of Hy with yR = ?r =>
replace a with (Z_to_bv 64 (lo64 r)) by reflexivity; replace b with (Z_to_bv 64 (hi64 r)) by reflexivity end);
eapply L_RET30; try eassumption; try lia.
Qed.

#[using="fc pre post pok fuelc f0 kmin0 c0 Hp SE_T SPF SPT SG1 SG3"] Lemma L_INFR : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c sign,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = sINF sign ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6e14) fct None m (seg_rom rsegs)).
Proof.
intros until sign. intros WI RJ Hk FOK FRM' Hsg Hy.
destruct Hsg as [-> | ->]; unfold sINF in Hy; cbn in Hy;
(zs; zs; zs; zs; stmt L_A38; eapply NX; try eassumption; try lia;
[ fok | | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity]);
[left | right; left]; (split; [apply bv_eq; vm_compute; reflexivity | exact Hy]).
Qed.

#[using="Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_ERR : S_ERR.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hst HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC2 : rw_cells rsegs mm Fp (rf_cells T p true (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) J))
by (unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite Hsn, Hns; unfold M64; hyp_cells) end.
rewrite rf_cells_raw_eq in FC2.
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (J := J);
[exact FC2 | exact (RFI_ok T txt p J _ _ _ RJu) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ (sh_lim0 _) _) |- _ => rename H into FC3 end. rewrite <- HfR in FC3.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
rewrite <- Hy. eapply L_RET30; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJu). all: try flia.
Qed.

#[using="pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i s0v : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(3 <= i <= 7)%Z -> (0 <= s0v < 256)%Z -> ((i = 3 /\ s0v <> 73) \/ (4 <= i /\ s0v = 73))%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6de4) fc None m (seg_rom rsegs)).
Proof.
intros until s0v. intros WI RJ Hk Hst Hsg Ri Rs0 Hs0 HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (RJR : RFJ' (kmin - 1 - (i - 3)) c fR).
{ rewrite HfR. replace (i - 3)%Z with (Z.of_nat (Z.to_nat (i - 3))) at 1 by lia. apply RFJ_ungetn; [| rewrite (rf_unget_eq f Hsn); exact Hsn | lia].
exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)). }
assert (Hsn2 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
rewrite (fs_unget_loop_eq (Z.to_nat (i - 3)) (sh_unget f) Hsn2) in HfR. rewrite (rf_unget_eq f Hsn) in HfR. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in HfR.
specialize (KM Hsn).
ufc FC. rewrite Hsn, Hns in FC. rewrite Hpok1.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. brf K3.
-
assert (Ei : i = 3%Z) by (clear -K3 Hs0 Rs0; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
subst i. change (Z.of_nat (Z.to_nat (3 - 3))) with 0%Z in HfR. replace (sh_rpos f - 1 - 0)%Z with (sh_rpos f - 1)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold QHB6.Mq0.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
- assert (Es : s0v = 73%Z) by (clear -K3 Hs0 Rs0; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
zs. zs. zs. zs0.
replace (Z.of_nat (Z.to_nat (i - 3))) with (i - 3)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold QHB6.Mq0.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
Qed.

#[using="pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX4 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(4 <= i <= 7)%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6de0) fc None m (seg_rom rsegs)).
Proof.
intros until i. intros WI RJ Hk Hst Hsg Ri HfR Hy. pose proof WI as WI0. dest_winv WI.
rewrite Hpok1. zs. (brf K; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_IEX; try eassumption; try lia.
Qed.

Ltac inf_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I7 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (4 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 7 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6d64) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 7) with 121%Z in HK. change (7 <? 7)%Z with false in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
-
and33y K1 c'' Rch 89%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_infk_8, FS_inf_8 in HK. injection HK as EfR EyR.
eapply L_INFR; [rewrite <- EfR; mk_winv2 | rewrite <- EfR; exact RJ1 | flia | apply Fok_refl | exact FRM | exact Hsg | symmetry; exact EyR].
- and33n K1 c'' Rch 89%Z N1. replace (Z.lor c'' 32 =? 121)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. change (Z_to_bv 64 (-7)) with (Z_to_bv 64 (- 7)).
eapply L_IEX4 with (i := 7%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I6 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (3 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 6 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6be8) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 6) with 116%Z in HK. change (6 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 84%Z N1. replace (Z.lor c'' 32 =? 116)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-6)) with (Z_to_bv 64 (- 6)).
eapply L_IEX4 with (i := 6%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 84%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I7; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I5 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 5 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6708) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 5) with 105%Z in HK. change (5 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-5)) with (Z_to_bv 64 (- 5)).
eapply L_IEX4 with (i := 5%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I6; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I4 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 4 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd66e4) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 4) with 110%Z in HK. change (4 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-4)) with (Z_to_bv 64 (- 4)).
eapply L_IEX4 with (i := 4%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I5; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 3 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd66c0) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 3) with 105%Z in HK. change (3 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_3 _ _ _ _ _ _ _ Hpok1) in HK. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-3)) with (Z_to_bv 64 (- 3)).
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *.
eapply L_IEX with (i := 3%Z) (s0v := Z.land c'' 18446744073709551583); try eassumption; try flia; try (symmetry; assumption);
try mk_winv2; try (apply and33_range; exact Rch); try (left; split; [reflexivity | exact K1]).
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *. rewrite K1.
eapply L_I4; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6600) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 2) with 102%Z in HK. change (2 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 70%Z N1. replace (Z.lor c'' 32 =? 102)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 70%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_I3; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I1 : S_I1.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hci HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hci; discriminate Hci).
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 1) with 110%Z in HK. change (1 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I2; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
zs.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
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
Import QHB6.Mq0 QOy4.Mq3.
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

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_N1 := (@QOy4.Mq3.S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_Z := (@QOy4.Mq3.S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@QOy4.Mq3.S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@QOy4.Mq3.S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_PAR := (@QOy4.Mq3.S_PAR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).
Notation FS_nan' := (FS_nan fuelc 53 (-1074) pok).

Hypothesis HS_Z : S_Z.
Hypothesis HS_ERR : S_ERR.
Hypothesis HS_A38 : S_A38.

Ltac nan_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.
Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="fc pre post pok fuelc f0 kmin0 c0 HS_A38"] Lemma L_NANR : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> yR = C_NAN ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6bc8) fct None m (seg_rom rsegs)).
Proof.
intros until c. intros WI RJ Hk FOK FRM' Hy.
zs. zs. zs.
stmt HS_A38. eapply NX; try eassumption; try lia;
[ fok | right; right; split; [reflexivity | exact Hy] | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity ].
Qed.

#[using="fc pre post pok fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PUNG : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
fR = sh_unget f -> yR = C_NAN ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6bb4) fct None m (seg_rom rsegs)).
Proof.
intros until f. intros WI RJ Hk FOK FRM' HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite HfR. unfold QHB6.Mq0.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
rewrite HfR. exact RJu. flia.
Qed.

Definition alnumb (c : Z) : bool := ((u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95))%Z.
#[using="Type"] Lemma alnumb_iff : forall c, (0 <= c < 256)%Z ->
(alnumb c = true <-> (48 <= c <= 57 \/ 65 <= c <= 90 \/ 97 <= c <= 122 \/ c = 95))%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (alnumb c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)) || (c =? 95)))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, Z.eqb_eq. tauto.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PAR : S_PAR.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk FOK FRM' Hc0 Hst Ri HL HR; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite fs_par_loop_S in HL. unfold fs_par_body in HL.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
fold (alnumb c'') in HL. pose proof (alnumb_iff c'' Rch) as AIF. destruct (alnumb c'') eqn:AL.
-
pose proof (proj1 AIF eq_refl) as RANGE. clear AIF.
assert (CONT : forall m2 (x11' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) (Z_to_bv 64 c'') x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6800) fct None m2 (seg_rom rsegs))).
{ intros m2 x11' WI2.
assert (Hc1 : c'' <> 0%Z) by (clear -RANGE; lia).
pose proof WI2 as WI3. destruct WI3 as (FI3 & FL3 & XW3 & LW3 & FC3). pose proof FI3 as FI4. dest_finv FI4.
zs.
eapply (IH m2); try eassumption; try flia. cbn [sh_rpos]. flia. }
zs. zs. brf K1; kswrap K1.
+ zs. zs. brf K2; kswrap K2.
* eapply CONT. mk_winv2.
* zs. brf K3.
-- eapply CONT. mk_winv2.
-- zs. zs. brf K4; kswrap K4.
++ eapply CONT. mk_winv2.
++ exfalso. clear -K1 K2 K3 K4 RANGE Rch. Z.div_mod_to_equations. lia.
+ zs. eapply CONT. mk_winv2.
-
assert (NR : ~ (48 <= c'' <= 57 \/ 65 <= c'' <= 90 \/ 97 <= c'' <= 122 \/ c'' = 95)%Z) by (intros X; apply (proj2 AIF) in X; discriminate X). clear AIF.
injection HL as <- <- <-.
zs. zs. brf K1; kswrap K1; [| exfalso; clear -K1 NR Rch; Z.div_mod_to_equations; lia].
zs. zs. brf K2; kswrap K2; [exfalso; clear -K1 K2 NR Rch; Z.div_mod_to_equations; lia |].
zs. brf K3; [exfalso; clear -K3 NR Rch; lia|].
zs. zs. brf K4; kswrap K4; [exfalso; clear -K1 K2 K3 K4 NR Rch; Z.div_mod_to_equations; lia|].
zs. zs. brf K5.
+
assert (E41 : c'' = 41%Z) by (clear -K5 Rch; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
rewrite E41, Z.eqb_refl in HR. injection HR as EfR EyR.
eapply L_NANR with (k := (kmin + 1)%Z) (c := c''); [ rewrite EfR; mk_winv2 | rewrite EfR; exact RJ1 | flia | exact FOK | exact FRM' | exact EyR ].
+ assert (N41 : c'' <> 41%Z) by (clear -K5 Rch; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
replace (c'' =? 41)%Z with false in HR by (symmetry; apply Z.eqb_neq; exact N41). injection HR as EfR EyR.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (Hsn2 : sh_shlim_neg (sh_unget (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) = false).
{ unfold sh_unget. cbn [sh_shlim_neg]. rewrite Hsn. reflexivity. }
rewrite (fs_unget_loop_eq (Z.to_nat i) _ Hsn2) in EfR. unfold sh_unget in EfR. cbn [sh_shlim_neg] in EfR. rewrite Hsn in EfR.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in EfR.
assert (RJR : RFJ' (kmin + 1 - 1 - Z.of_nat (Z.to_nat i)) c'' fR).
{ rewrite EfR.
pose proof (RFI_unget T txt p J Hp _ _ _ RJ1 ltac:(flia)) as RJu. unfold sh_unget in RJu. cbn [sh_shlim_neg] in RJu. rewrite Hsn in RJu.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in RJu.
pose proof (RFJ_ungetn (Z.to_nat i) _ _ _ RJu ltac:(reflexivity) ltac:(lia)) as RJv.
rewrite fs_unget_loop_eq in RJv by reflexivity. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJv.
replace (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z with (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z by lia. exact RJv. }
unfold rf_rend in FC. rewrite ?Hsn, ?Hns in FC. unfold M64 in FC. rewrite Hpok1.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K7; [ exfalso; lia | ]). zs. (brf K8; [ exfalso; lia | ]). zs. (brf K9; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite EfR. unfold QHB6.Mq0.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
all: flia.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nan' sign 3 c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd67cc) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold FS_nan in HK. change (3 =? 3)%Z with true in HK. replace (negb (nz pok)) with false in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
nan_read FC RJ kmin c f Hc0. cbv beta iota zeta in HK.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (N40 : c'' <> 40%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c'' =? 40)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N40). cbn [negb] in HK. injection HK as EfR EyR.
eapply L_PUNG with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; eassumption); try mk_winv2; try apply Fok_refl.
- assert (E40 : c'' = 40%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E40, Z.eqb_refl in HK. cbn [negb] in HK.
destruct (fs_par_loop fuelc _) as [[[i' c'] f']|] eqn:HL; [|discriminate HK].
zs. zs. zs. zs. zs.
eapply (L_PAR fuelc) with (kmin := (kmin + 1)%Z) (i := 1%Z) (c := c''); try eassumption; try flia;
try mk_winv2; try apply Fok_refl; try (cbn [sh_rpos]; flia); try (rewrite E40; lia).
destruct (c' =? 41)%Z; cbv zeta iota in HK; injection HK as <- <-; reflexivity.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6684) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 2) with 110%Z in HK. change (2 <? 2)%Z with false in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_nank_3 in HK.
zs.
eapply L_NK3; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK1 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd6508) fc None m (seg_rom rsegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 1) with 97%Z in HK. change (1 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 65%Z N1. replace (Z.lor c'' 32 =? 97)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 65%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_NK2; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_N1 : S_N1.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hr1 Rc0 Hni HK. pose proof WI as WI0. dest_winv WI. bury_disj.
rewrite FS_nank_step in HK by lia. change (znth str_nan 0) with 110%Z in HK. change (0 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. brf K1.
- and33n K1 c Rc0 78%Z N1. replace (Z.lor c 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_0 in HK.
stmt HS_Z. eapply NX; try eassumption; try flia. apply Fok_refl.
- and33y K1 c Rc0 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_NK1; only 6: exact HK; [exact WI0 | exact RJ | flia | intros E0; rewrite E0 in E1; discriminate E1 | exact Hst].
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
Import QHB6.Mq0 QOy4.Mq3.
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

Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation frame_release := (@QHB6.Mq0.frame_release ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T txt pre canary).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation S_848 := (@QHB6.Mq0.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@QHB6.Mq0.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_Z := (@QOy4.Mq3.S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HEX := (@QOy4.Mq3.S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Hypothesis HS_848 : S_848.
Hypothesis HS_6F8 : S_6F8.
Hypothesis HS_HEX : S_HEX.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_848 HS_6F8 HS_HEX"] Lemma L_Z : S_Z.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_tail_h in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt HS_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
unfold FS_zero in HK.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
(Z.lor (fst (sh_getc f)) 32 =? 120)%Z = false ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd6778) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2 NX120. rewrite NX120 in HK.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3; rewrite ?land_W64 in K3.
+
eapply JOIN. { mk_winv2. }
apply Z.eqb_neq. intros E. apply (proj2 (and33_lor c'' 88 Rch ltac:(lia))) in E. clear -K3 E Rch. Z.div_mod_to_equations; lia.
+
assert (E120 : Z.lor c'' 32 = 120%Z).
{ apply (proj1 (and33_lor c'' 88 Rch ltac:(lia))). clear -K3 Rch. pose proof (and33_range c'' Rch). Z.div_mod_to_equations; lia. }
rewrite E120, Z.eqb_refl in HK.
unfold ssp_guard. zs. zs. zs. zs. zs. (brf K4; [ | exfalso; lia ]).
zs. zs. zs. zs. zs. zs. zs. zs.
do 14 zs. zs. zs.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (WI9 : winv mm j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws
(mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) by mk_winv2 end.
destruct WI9 as (FI9 & FL9 & XW9 & LW9 & FC9).
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI9 FL9 XW9 LW9) as STK.
stmt HS_HEX. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia.
* destruct FI9 as (MI9 & MU9 & WM9 & FRhi9 & ST9 & BY9 & SSA & SSB). destruct FL9 as [LOW9 ERR9].
unfold QOy4.Mq3.hinv. split; [exact MI9|]. split; [exact MU9|]. split; [exact WM9|]. split; [exact STK|]. split; [exact BY9|].
split; [exact SSA|]. split; [exact SSB|]. split; [exact ERR9|]. exact FC9.
* intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
-- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
-- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.
End Floatscan.
End Mq3.

Module Mq4.

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
Import QHB6.Mq0 QOy4.Mq3.
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

Local Notation ctx_all := (@QHB6.Mq0.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@QHB6.Mq0.Wfs q Fp).
Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).

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

Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).
Notation HX_alz' := (HX_alz fuelc 53 (-1074)).
Notation HX_rz' := (HX_rz fuelc 53 (-1074)).
Notation HX_dig' := (HX_dig fuelc 53 (-1074)).
Notation HX_tail' := (HX_tail fuelc 53 (-1074)).
Notation HX_e2' := (HX_e2 53 (-1074)).
Notation HX_fin' := (HX_fin 53 (-1074)).

Definition hxfr (w0 w8 w16 w24 w32 w40 w48 w56 : word) (m : word -> option byte) : Prop :=
rw_cells rsegs m (q + -176) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 (reg_get F 8);
C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition hxinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv rsegs m /\ munch Wfs m0 m /\ wmono rsegs m0 m
/\ stk rsegs m (q - FS_DEPTH) (q + -176)
/\ bytes_at rsegs m T (zbytes txt)
/\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary]
/\ rw_cells rsegs m RERRNO [C4 ev]
/\ rw_cells rsegs m Fp (rf_cells T p true f J).

Definition kminH (kmin gd gr : Z) : Prop := (1 <= kmin)%Z /\ (gd = 0%Z -> 2 + gr <= kmin)%Z.

Definition SHLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd gd' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (gd, 48, f)%Z = Some (gd', c', f') -> HX_alz' sign pok gd' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7b48) fct None m (seg_rom rsegs)).
Definition S_HLZ : Prop := forall n, SHLZn n.

Definition S_H778 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
HX_alz' sign pok 1 c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 0) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7b64) fct None m (seg_rom rsegs)).

Definition S_H720 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z ->
(0 <= gd <= 1)%Z ->
HX_rz' sign pok gd 0 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) x9 (Z_to_bv 64 (T + sh_rpos f)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7b0c) fct None m (seg_rom rsegs)).

Definition SHRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd rp gd' rp' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(- sh_rpos f <= rp <= 0)%Z ->
df_rz_loop n (gd, rp, 48, f)%Z = Some (gd', rp', c', f') -> HX_dig' sign pok (mkHX c' f' 0 Y0 SC0 0 1 gd' rp' 0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 48) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7ba8) fct None m (seg_rom rsegs)).
Definition S_HRZ : Prop := forall n, SHRZn n.

Definition S_H7F0 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd gr rp : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= gd <= 1)%Z -> (0 <= gr <= 1)%Z -> (- sh_rpos f <= rp <= 0)%Z ->
HX_dig' sign pok (mkHX c f 0 Y0 SC0 0 gr gd rp 0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7bdc) fct None m (seg_rom rsegs)).

Definition hxI (f : shfile) (c x gt gr gd rp dc : Z) : Prop :=
(0 <= c < 256)%Z /\ (0 <= x < 2^32)%Z /\ (0 <= gt <= 1)%Z /\ (0 <= gr <= 1)%Z /\ (0 <= gd <= 1)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (- sh_rpos f <= rp <= sh_rpos f)%Z.

Definition SHDn (n : nat) : Prop := forall (pc : Z) m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z) (s' : st_hex),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
hx_dig_loop n (mkHX c f x y sc gt gr gd rp dc) = Some s' -> HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
((pc = 0xd7c40%Z /\ isdigitc c = true) \/ (pc = 0xd7d3c%Z /\ isdigitc c = false)) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 (bv_swrap 32 (c + -48))) (Z_to_bv 64 c) x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 pc) fct None m (seg_rom rsegs)).
Definition S_HD : Prop := forall n, SHDn n.

Definition S_HTL : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
HX_tail' sign pok c f x y gr gd rp dc = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7d50) fct None m (seg_rom rsegs)).

Definition S_HE2 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 < x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7e00) fct None m (seg_rom rsegs)).

Definition SHNLn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 x' y' e2' : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> reg_get Ft 8 = D_05 ->
(0 < x < 2^31)%Z -> (-1340 + Z.of_nat n <= e2 <= 1074)%Z ->
hx_norm_loop n (x, y, e2) = Some (x', y', e2') -> HX_fin' sign fR x' y' e2' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7f4c) fct None m (seg_rom rsegs)).
Definition S_HNL : Prop := forall n, SHNLn n.

Definition S_HFIN : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(2^31 <= x < 2^32)%Z -> (-1500 <= e2 <= 1074)%Z ->
HX_fin' sign fR x y e2 = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7f98) fct None m (seg_rom rsegs)).

Definition S_HZR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w48 w56 : word) sign k c,
let _ := ctx_all in
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = hx_zero sign ->
evt rsegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7ea0) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma HX_fin_f : forall sign f x y e2 f' y', HX_fin' sign f x y e2 = Some (f', y') -> f' = f.
Proof.
clear. intros until y'. unfold HX_fin.
match goal with |- context [match ?X with pair _ _ => _ end] => destruct X as [[bias x2] y2] end. intros H; injection H as <- _; reflexivity.
Qed.
#[using="Type"] Lemma HX_e2_f : forall sign f x y e2 f' y', HX_e2' sign f x y e2 = Some (f', y') -> f' = f.
Proof.
clear. intros until y'. unfold HX_e2.
destruct (x =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (- (-1074) <? e2)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (e2 <? -1074 - 2 * LDBL_MANT_DIG_)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x3 y3] e3]|]; [apply HX_fin_f | discriminate].
Qed.
End Floatscan.
End Mq4.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QM7w QNAo QFs1 QCwx QFqQ Q98Z QkLq QdZ1 Qv4L QULt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0 QFs1.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QHB6.Mq2 QHB6.Mq1.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="LB sc F ER SC RQ FIT TR GM MSK K0 LBK"] Lemma rta_slot_ok : exists b r,
m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
/\ slot_ok st' g b r k req
/\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
free_slot_addr st0 a).
Proof.
pose proof (isf_mf _ _ F) as MF.
pose proof (gmf_cls _ _ _ GM) as GSC.
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).

destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
{ rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }

assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
{ apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
destruct (FM g b Hmem) as (FM1 & FM2 & _).
assert (KLI : k <= m_last_idx (get_meta_rec st g)).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
{ pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
assert (P2k : 0 < 2 ^ k <= msk).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
exists b, r.
split; [exact Hmem|]. split; [exact Hr|].
split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
split; [| split; [exact ST'|]].
- pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
+ exact Hmem.
+ unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
+ exact Hk.
+ exact B0.
+ exact B16.
+ lia.
+ lia.
+ exact SPAN.
+ unfold UNIT in S16. lia.
+ unfold UNIT in SMOD. exact SMOD.
+ lia.
+ exact RQ.
+ lia.
+ intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
+ unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
+ intros off O0 OF.
assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
+ unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
+ unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
+ unfold msk, mr in *. lia.
+ unfold mr. lia.
+ lia.
+ lia.
+ left. lia.
- intros a Ha. rewrite ST' in Ha.
destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
+ pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
+ assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End TASLOT.

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

#[using="RC__ R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK"] Lemma rerrno_lit : errno_addr tp = 0x622dbc.
Proof. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0"] Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
pose proof (isf_mf _ _ F0) as MF.
set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
subst msk.
destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
fold st' in Hr', SO, STR, FSA.

pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).

assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
{ intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
- do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).

assert (NIMG : forall a, 0x10000 <= a < 0x645000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
{ intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
apply HK. unfold ras_post2.
exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
+ lia. + unfold RCTX in X. unfold alloc_ceiling in CLO. lia.
+ destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). unfold alloc_ceiling in CLO. lia.
+ destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in *. lia.
- intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
split; [exact MR'|].
split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
split. {
intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
{ revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
refine (proj1 (PE (r_base rr + off) _ _)).
{ destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). unfold alloc_ceiling in RC. lia. }
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
- destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
split; [exact PE'|].
split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split. {  constructor.
- intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
- intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
- unfold st'. cbn. apply (tr_tick _ _ _ TR).
- intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
exact (AC rid sh o' v t Esh Hc).
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
right. split; [lia|]. exists g3, b, r.
split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
- intros a Ha. do 2 right. left. apply FSA. exact Ha.
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.

End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF QYnB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QXxF.Mq0 QM7w QNAo.Mq0 QFs1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QmBS.Mq1 Qlfl.Mq3 Qlfl.Mq1 QHB6.Mq1 QYnB.Mq4.

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

Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv rsegs m3 /\ stk rsegs m3 lo (bv_unsigned sp + -144) /\
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0xceb98) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
(wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
a1 (wz cnt1) (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 pc) fc None m3 (seg_rom rsegs).

Definition rHMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0xcec6c st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0xcecb0 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof.
intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.
pose proof (QULt.Mq1.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
pose proof (size_class_range sc SC) as SZR.
rewrite (ag_body_eq f sc req k bail st2 mm).
riprefixT. unfold rag_regs.
eapply evt_cut.
{ eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
cbv beta. intros ms' (a2'' & a3'' & a4'' & ->).
set (size := size_class sc * UNIT).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
assert (C0R : 1 <= cnt0 <= 32).
{ pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
subst cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
destruct (negb _); [lia|]. destruct (negb _); lia.
- apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
eapply evt_cut.
{ eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
cbv beta. intros ms' ->. unfold rcnt_regs.
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
assert (EC : ag_cnt1 sc st2 = cnt1).
{ unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
apply evt_done.
destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
- pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
- pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.

End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7 Qn9M Q3o5 QTyG Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq4 Q4J3.Mq3 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9 Q6y7.Mq2 QNAo.Mq1.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QdZ1.Mq3 QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq7 Qv4L.Mq0 Qv4L.Mq8 QnkH.Mq7 Qi8L.Mq4 QmBS.Mq3 QkLq.Mq2 QYnB.Mq7 QdZ1.Mq4.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
implM rsegs (membed t1) s Q1 ms ->
implM rsegs (membed t2) s
(fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
exists r1, []. cbn. auto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
impl rsegs (at_node rsegs) (QlEo_c1.Mq0.bind _ (Ret Unr) f) Qx msx = impl rsegs (at_node rsegs) (f Unr) Qx msx) by reflexivity.
destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w|ma ol nl fl].
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. exact H. }
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. exact H. }
all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
eapply impl_epost_mono; [eapply IH; exact H1|];
intros [r2' s2] ms2; cbn; intros (r1' & ans & F1 & F2 & HR & HQ);
exists r1', (z :: ans); cbn; auto.
Qed.

#[using="Type"] Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
strip st = ps_m s ->
rimplT o (malloc st n) s Q1 ms ->
(forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
Q1 (st', p) s' ms' -> ptr_rel p r ->
follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
follow (cmalloc (strip st) n) ans = Some (cst, c) ->
cst = strip st' ->
r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
Q r (set_m (strip st') s') ms') ->
implM rsegs (raw_malloc n) s Q ms.
Proof.
intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind rsegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
/\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
{ rewrite <- Hst. unfold rimplT in H.
eapply implM_mono.
- eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
unfold mrun. apply malloc_control. apply pans_mem_range.
- intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
exists st', p, ans, o1. auto. }
intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
eapply (implM_bind rsegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

#[using="Type"] Lemma rimplT_silent {R} o (t : QUZl.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

#[using="Type"] Lemma rheap_pres_of_fp st st' LB lo sp m m' :
RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
rheap_pres LB sp m m'.
Proof.
intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
- destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
- destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RMLOCK, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
- destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
unfold alloc_ceiling in *.
pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
pose proof (round_up_pg_mono _ _ L1) as RL1.
pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
+ lia.
+ rewrite unsigned_lit in H by lia. lia.
+ unfold RCTX in H. lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

#[using="Type"] Lemma ruser_chunk st' m' (p : aptr) r n :
rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
exists junk, rw_cells rsegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
intros MR Hr Hk P0 PN N0.
pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). unfold alloc_ceiling in RC.
rewrite (conc_region' st' p r Hr).
assert (W : wr_at rsegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
split; [exact L| exact I].
Qed.

Definition malloc_core_allzero_stmt : Prop :=
forall st L BL LS n (o : mem) ans (o' : mem) st1 g idx,
Qatc.INVL Qatc.x0 st L BL LS -> 0 <= n ->
follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
is_allzero_ctrl (Qatc.MR st1 g) = true ->
exists bg, m_mem (Qatc.MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (Qatc.MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (Qatc.sstart (Qatc.MR st1 g) idx + k) = Known 0.

#[using="Type"] Lemma bytes_at_inj0 m a bs bs' : bytes_at rsegs m a bs -> bytes_at rsegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rzeros_of_shadow st m rid r base (cnt : nat) :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= base -> base + Z.of_nat cnt <= round_up_pg (r_len r) ->
(forall j, 0 <= j < Z.of_nat cnt -> cell_read (get_shadow st rid) (base + j) = Known 0) ->
bytes_at rsegs m (r_base r + base) (zeros cnt).
Proof.
intros MR Hr Hk B0. pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH rid r Hr Hk) as [HW HB].
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
induction cnt as [|cnt IH]; intros BC HC.
- cbn. apply bytes_at_nil. lia.
- replace (zeros (S cnt)) with (zeros cnt ++ [b8 0]) by (unfold zeros; rewrite <- repeat_cons; cbn; reflexivity).
apply bytes_at_app. split; [apply IH; [lia| intros j Hj; apply HC; lia]|].
unfold zeros. rewrite repeat_length. replace (r_base r + base + Z.of_nat cnt) with (r_base r + (base + Z.of_nat cnt)) by lia.
exact (proj1 (HB (base + Z.of_nat cnt) 0 ltac:(lia) (HC (Z.of_nat cnt) ltac:(lia)))).
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis MCZ : malloc_core_allzero_stmt.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_impl_spec_proof : rmalloc_impl_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR0.
assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
unfold raw_malloc.
eapply (implM_bind rsegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind rsegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
{ rewrite <- Hst. unfold cmalloc.
eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
x = (strip st2, r)
/\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
- eapply implM_mono.
+ eapply (rmembed_strel_follow CREL).
* pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
* unfold rimplT in |- *.
pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
unfold rimplT in X. exact X.
+ intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
- intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
intros [cs c] s' ms'' MQ. cbv beta iota.
destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
eapply (implM_bind rsegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.

assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
| Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
follow (cmalloc (strip st) n) ans = Some y).
{ intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
destruct r as [[g idx]|].
-
cbn [rcoreQ] in CQ.
destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
set (stride := get_stride (get_meta_rec st2 g)) in *.
set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.
pose proof (renf_implT (RC__:=RC__) sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
eapply evt_mono; [exact EV|]. clear EV.
intros msf [_ EP]. unfold renf_post in EP.
destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF & UB).
destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
{ rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
set (A := conc st' p) in *.

assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
{ unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
fold A in UCH.
unfold rmalloc_post. do 15 eexists. exists m', errv1.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
- lia.
- lia. }
assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
{ eapply rpres_except_mono.
+ eapply rpres_except_trans; [exact PE2|].
eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
+ intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
exists A, ujunk.
split; [reflexivity|].
split. { unfold rblock_range, alloc_ceiling. rewrite EA.
split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
- apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
- exact AR'. }
split; [exact UCH|].
split.
2:{
intros g0 idx0 SL0 AZ. cbn [ps_m set_m fst] in SL0, AZ.
rewrite s_slots_strip in SL0. unfold slot_of, slot_start' in SL0. rewrite Hmem in SL0. cbn [default from_option id] in SL0.
unfold aadd in SL0. cbn [fst snd] in SL0.
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + get_stride (get_meta_rec st2 g) * idx) in SL0 by (unfold UNIT; lia).
rewrite SSL in SL0. assert (g0 = g /\ idx0 = idx) as [-> ->] by (inversion SL0; auto). clear SL0.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g) in AZ.
destruct (Q3o5.Mq1.areach_inv _ st LB AR) as (L & LS & BL0 & INV & _).
destruct (MCZ st L BL0 LS n m ans m st2 g idx INV ltac:(lia) F1 AZ) as (bg & Hbg & CZ).
change (Qatc.MR st2 g) with (get_meta_rec st2 g) in Hbg, CZ. rewrite Hmem in Hbg. assert (bg = b) as -> by congruence.
unfold Qatc.sstart, Qatc.gbase in CZ. rewrite Hmem in CZ. cbn [default id snd] in CZ. fold stride in CZ.
assert (Z0 : bytes_at rsegs m1 A (zeros (Z.to_nat n))).
{ rewrite EA. replace (r_base rg + snd b + 16 + stride * idx + 16 * off) with (r_base rg + (snd b + 16 + stride * idx + 16 * off)) by lia.
apply (rzeros_of_shadow st2 m1 (fst b) rg); [exact MR2| exact Hr| exact Hk| lia| |].
- rewrite Ep in *. cbn [snd] in *. subst stride. lia.
- intros j Hj. replace (snd b + 16 + stride * idx + 16 * off + j) with (snd b + UNIT + stride * idx + (16 * off + j)) by (unfold UNIT; lia).
apply CZ. unfold IB. lia. }
pose proof (UB (zeros (Z.to_nat n)) Z0 ltac:(unfold zeros; rewrite repeat_length; lia)) as Z1.
pose proof (rw_cells_bytes_at _ _ _ _ UCH) as UJ. cbn [cells_bytes cbytes] in UJ. rewrite app_nil_r in UJ.
pose proof (proj1 (proj1 UCH)) as WFJ. cbn in WFJ. destruct WFJ as [LJ _].
apply (bytes_at_inj0 m' A); [exact UJ| exact Z1| unfold zeros; rewrite repeat_length; lia]. }

intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
{ apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
unfold fresh_off. cbn [s_slots strip].
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
-
cbn [rcoreQ] in CQ.
destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO & E12).
apply evt_done. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
split; [reflexivity|]. split; [exact E12|].
exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
split.
+ apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
+ eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof. exact (rmalloc_stmt_of_impl rmalloc_impl_spec_proof). Qed.

End TOPLEVEL.

End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

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
Import QHB6.Mq3 QOy4.
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
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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
Ltac read_char f :=
let RDb := fresh "RDb" in
lazymatch goal with BY : bytes_at _ ?m T (zbytes txt) |- evt _ _ (MS _ _ _ _ _ ?m _) =>
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb;
zs; cbv beta; try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia; clear RDb end.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let rec go pre l := lazymatch l with
| [CB 8 _] => fail
| CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
| ?c :: ?l' => go constr:(pre ++ [c]) l' end in
lazymatch cs with ?c0 :: ?l => go constr:([c0]) l end end.

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

Local Notation S_WS := (@QOy4.S_WS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_AWS := (@QOy4.S_AWS ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_I1 := (@QOy4.S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_N1 := (@QOy4.S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

Hypothesis HS_I1 : S_I1.
Hypothesis HS_N1 : S_N1.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_AWS : S_AWS.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hr1 Rcb Hns HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_sign in HK.

assert (GOI : forall m2 (x8' x10' x11' x12' : word) sg c2 (f2 : shfile) k2,
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f2 -> RFJ' k2 c2 f2 -> (1 <= k2)%Z -> sh_stdio f2 = sh_stdio f0 ->
(sg = 1 \/ sg = -1)%Z -> (0 <= c2 < 256)%Z -> (c2 <> (-1)%Z -> 1 <= sh_rpos f2)%Z ->
FS_infk' sg 0 c2 f2 = Some (fR, yR) ->
forall K : Prop, ((Z.land c2 18446744073709551583 = 73%Z /\ K = (evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) x10' x11' x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b8c) fc None m2 (seg_rom usegs))))
\/ (Z.land c2 18446744073709551583 <> 73%Z /\ K = (evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8' (Z_to_bv 64 sg) (Z_to_bv 64 c2) (Z_to_bv 64 (Z.land c2 18446744073709551583)) x12' x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8bc4) fc None m2 (seg_rom usegs))))) -> K).
{ intros m2 x8' x10' x11' x12' sg c2 f2 k2 WI2 RJ2 Hk2 Hst2 Hsg Rc2 Hr2 HK2 K [[E73 ->] | [N73 ->]].
- and33y E73 c2 Rc2 73%Z E1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
rewrite E1, Z.eqb_refl in HK2. change (0 <? 7)%Z with true in HK2. cbv iota in HK2.
stmt HS_I1. eapply NX; try eassumption; try flia.
- and33n N73 c2 Rc2 73%Z N1. rewrite FS_infk_step in HK2 by lia. change (znth str_infinity 0) with 105%Z in HK2.
replace (Z.lor c2 32 =? 105)%Z with false in HK2 by (symmetry; apply Z.eqb_neq; exact N1). rewrite FS_inf_0 in HK2.
stmt HS_N1. eapply NX; try eassumption; try flia. }
assert (SGN : forall x11', (c = 43%Z \/ c = 45%Z) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 32) (Z_to_bv 64 c) x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b58) fc None m (seg_rom usegs))).
{ intros x11' Hc.
assert (Hc0 : c <> 0%Z) by lia.
replace ((c =? 43) || (c =? 45))%Z with true in HK by (destruct Hc as [-> | ->]; reflexivity).
set (sg := (1 - 2 * b2z (c =? 45))%Z) in HK. assert (Hsg : (sg = 1 \/ sg = -1)%Z) by (subst sg; destruct (c =? 45)%Z; cbn; lia).
rewrite (surjective_pairing (sh_getc f)) in HK. cbv beta iota zeta in HK.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. zs. zs. zs.
let v := getreg 9%Z in replace v with (Z_to_bv 64 sg) by (subst sg; destruct Hc as [-> | ->]; apply Z_to_bv_eqm; reflexivity).
zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf Kc.
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (right; split; [clear -Kc Rch; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK].
+ eapply (GOI _ x8 (Z_to_bv 64 c'') (Z_to_bv 64 (Z.land c'' 18446744073709551583)) (Z_to_bv 64 73) sg c'' (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) (kmin + 1)%Z);
only 9: (left; split; [clear -Kc Rch; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rch) in Kc; exact Kc | reflexivity]);
[mk_winv2 | exact RJ1 | flia | exact Hst1 | exact Hsg | exact Rch | cbn [sh_rpos]; intros _; flia | exact HK]. }
zs. zs. brf Ka.
-
assert (E45 : c = 45%Z) by (clear -Ka Rcb; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
apply SGN. right. exact E45.
- assert (N45 : c <> 45%Z) by (clear -Ka Rcb; rewrite ?land_W64 in Ka; Z.div_mod_to_equations; lia).
zs. zs. brf Kb.
+
assert (N43 : c <> 43%Z) by (clear -Kb Rcb; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
replace ((c =? 43) || (c =? 45))%Z with false in HK by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N43), (proj2 (Z.eqb_neq _ _) N45); reflexivity).
zs. zs. zs. zs. brf Kc.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (left; split; [clear -Kc Rcb; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
* eapply (GOI m x8 (Z_to_bv 64 c) (Z_to_bv 64 (Z.land c 18446744073709551583)) (Z_to_bv 64 73) 1%Z c f kmin);
only 9: (right; split; [clear -Kc Rcb; rewrite ?land_W64 in Kc; rewrite ?(Z.mod_small _ _ Rcb) in Kc; exact Kc | reflexivity]); try eassumption; try flia.
+ assert (E43 : c = 43%Z) by (clear -Kb Rcb; rewrite ?land_W64 in Kb; Z.div_mod_to_equations; lia).
apply SGN. left. exact E43.
Qed.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_I1 HS_N1"] Lemma L_WS : S_WS.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk Hc0 Hst HL HK; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
rewrite fs_ws_loop_S in HL.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *. cbv beta iota zeta in HL.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf KS; [ exfalso; lia | ]). zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
pose proof (isspace_iff c'' Rch) as SPI.
assert (LOOP : forall m2 (x10' x11' : word), m_isspace c'' = true ->
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 5) (Z_to_bv 64 32) x10' x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8b24) fc None m2 (seg_rom usegs))).
{ intros m2 x10' x11' SP WI2. rewrite SP in HL.
assert (Hc1 : c'' <> 0%Z) by (intros E0; rewrite E0 in SP; discriminate SP).
eapply (IH m2); try eassumption; try flia. }
zs. zs. brf K1.
-
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). right. clear -K1 Rch. rewrite ?land_W64 in K1. Z.div_mod_to_equations; lia.
- zs. brf K2.
+
eapply LOOP; [| mk_winv2]. apply (proj2 SPI). left. clear -K2 Rch. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia.
+
assert (NSP : m_isspace c'' = false).
{ destruct (m_isspace c''); [|reflexivity]. exfalso. pose proof (proj1 SPI eq_refl) as SPD. clear -K1 K2 Rch SPD. rewrite ?land_W64 in K1. rewrite ?land_W64 in K2. Z.div_mod_to_equations; lia. }
rewrite NSP in HL. injection HL as <- <-.
stmt L_AWS. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia. mk_winv2. cbn [sh_rpos]. intros _. flia.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 Q1 HS_I1 HS_N1"] Lemma L_ENTRYh : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev : word),
let _ := ctx_all in
floatscan_h fuelc f0 1 pok = Some (fR, yR) ->
stk usegs m0 (q - FS_DEPTH) q -> mem_inv usegs m0 ->
rw_cells usegs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (0 <= kmin0)%Z -> c0 <> 0%Z -> sh_stdio f0 = sh_stdio f0 ->
bytes_at usegs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells usegs m0 RERRNO [C4 ev] ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 1) (Z_to_bv 64 pok) a3 a4 a5 a6 a7
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (Z_to_bv 64 FLOATSCAN) fc None m0 (seg_rom usegs)).
Proof.
intros until ev. intros _ HMh ST MI FC RJ Hk0 Hc0 Hst BY [SSP1 SSP2] ERR.
pose proof (munch_refl Wfs m0) as MU. pose proof (wmono_refl usegs m0) as WM. unfold QHB6.Mq3.Wfs, FS_DEPTH, RERRNO in MU. unfold FS_DEPTH in ST.
unfold got_ssp, ssp_guard in SSP1, SSP2. unfold RERRNO in ERR.
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T.
pose proof zbytes_len as LTX. unfold zlength in *. bury_disj.
site_facts FC RJ kmin0 c0 f0.

pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0) as RJ1.
pose proof (getc_stdio f0) as Hst1.
assert (Rc1 : (-1 <= fst (sh_getc f0) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f0 Hbuf) as [Rrp1 Rrp2].
unfold FLOATSCAN.

zs.
carve_frame 120%nat ST. rename FR into FRhi.
do 14 zs.
lazymatch type of FRhi with rw_cells _ _ _ (CB 8 ?b :: _) => set (jc := b) in FRhi; clearbody jc end.
zs. zs.
replace (Z_to_bv 64 (q + -2032 - 4096))%Z with (Z_to_bv 64 (q + -6128))%Z by (f_equal; lia).

assert (Hcv1 : (q - 8656 <= q + -120 - Z.of_nat (Z.to_nat 6000))%Z) by lia;
destruct (stk_carve usegs _ _ _ (Z.to_nat 6000) ST Hcv1) as [ST' [junka XBa]]; clear ST Hcv1; rename ST' into ST;
replace (q + -120 - Z.of_nat (Z.to_nat 6000))%Z with (q + -6120)%Z in ST, XBa by lia.
assert (Hcv2 : (q - 8656 <= q + -6120 - Z.of_nat 8)%Z) by lia;
destruct (stk_carve usegs _ _ _ 8%nat ST Hcv2) as [ST' [junkb XBb]]; clear ST Hcv2; rename ST' into ST;
replace (q + -6120 - Z.of_nat 8)%Z with (q + -6128)%Z in ST, XBb by lia.
assert (Hcv3 : (q - 8656 <= q + -6128 - Z.of_nat (Z.to_nat 2184))%Z) by lia;
destruct (stk_carve usegs _ _ _ (Z.to_nat 2184) ST Hcv3) as [ST' [junkc XBc]]; clear ST Hcv3; rename ST' into ST;
replace (q + -6128 - Z.of_nat (Z.to_nat 2184))%Z with (q + -8312)%Z in ST, XBc by lia.
zs.
release_frame XBc ST (q + -6128)%Z. release_frame XBb ST (q + -6120)%Z. release_frame XBa ST (q + -120)%Z.
clear junka junkb junkc.
let n := eval vm_compute in (Z.to_nat 8192) in
assert (Hcv : (q - 8656 <= q + -120 - Z.of_nat n)%Z) by (change (Z.of_nat n) with 8192%Z; lia);
destruct (stk_carve usegs _ _ _ n ST Hcv) as [ST' [junkx XB2]]; clear ST Hcv; rename ST' into ST;
change (Z.of_nat n) with 8192%Z in ST, XB2.
replace (q + -120 - 8192)%Z with (q + -8312)%Z in ST, XB2 by lia.
pose proof XB2 as XB0. destruct XB0 as [[[LB _] _] _]. cbn in LB.
apply u8arr_of_rw_cells in XB2.
destruct (u32arr_of_u8arr usegs _ _ _ 2048%nat XB2 ltac:(rewrite LB; reflexivity)) as (ws0 & LW0 & XW). clear XB2 LB junkx.
zs. zs.
replace (Z_to_bv 64 (q + -6128 + -2048 + -240))%Z with SPv by (f_equal; lia).
carve_frame 104%nat ST. rename FR into LOW.
apply (rw_cells_split_CB _ _ _ [] 104 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
do 11 (c8ify LOW).
lazymatch type of LOW with rw_cells _ _ _ [CB 8 ?a; C8 ?b1; C8 ?b2; C8 ?b3; C8 ?b4; C8 ?b5; C8 ?b6; C8 ?b7; C8 ?b8; C8 ?b9; C8 ?b10; C8 ?b11; CB 8 ?c] =>
set (j0 := a) in LOW; set (w8 := b1) in LOW; set (w16 := b2) in LOW; set (w24 := b3) in LOW; set (w32 := b4) in LOW;
set (w40 := b5) in LOW; set (w48 := b6) in LOW; set (w56 := b7) in LOW; set (w64 := b8) in LOW; set (w72 := b9) in LOW;
set (w80 := b10) in LOW; set (w88 := b11) in LOW; set (b96 := c) in LOW;
clearbody j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 end.
match goal with H : list byte |- _ => try clear H end.

zs. zs. zs. zs. zs. zs. zs. zs.

zs. (brf K1; [ exfalso; lia | ]). zs. zs. (brf K2; [ exfalso; lia | ]). zs. zs. (brf K3; [ exfalso; lia | ]). zs. zs. zs. zs. zs. zs.
clear K1 K2 K3.

rewrite floatscan_h_1 in HMh. destruct (fs_ws_loop fuelc f0) as [[c1 f1]|] eqn:HWS; [|discriminate HMh].
eapply (L_WS fuelc) with (kmin := kmin0) (c := c0) (f := f0); try eassumption; try flia.
mk_winv2.
Qed.
End Floatscan.
End Mq8.

Module Mq9.

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
Import QHB6.Mq3 QOy4.
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation L_RET30 := (@QHB6.Mq3.L_RET30 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_I1 := (@QOy4.S_I1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@QOy4.S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@QOy4.S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_infk' := (FS_infk fuelc 53 (-1074) pok).

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_A38 : S_A38.
Proof.
intros m; intros until v. intros _ WI RJ Hk FOK FRM' SP E10. pose proof WI as WI0. dest_winv WI. bury_disj.
zs.
zs. match goal with |- context [reg_get Ft ?i] => rewrite (E10 i) by (vm_compute; reflexivity) end.
destruct SP as [[-> Hy] | [[-> Hy] | [-> Hy]]];
match goal with |- context [sx32 ?v] => let w := eval vm_compute in (bv_swrap 32 (bv_unsigned v)) in change (sx32 v) with (Z_to_bv 64 w) end;
(do 5 zs; (brf K1; [ exfalso; lia | ]); zs; zs; (brf K2; [ exfalso; lia | ]); do 11 zs);
(let a := getreg 10%Z in let b := getreg 11%Z in
lazymatch type of Hy with yR = ?r =>
replace a with (Z_to_bv 64 (lo64 r)) by reflexivity; replace b with (Z_to_bv 64 (hi64 r)) by reflexivity end);
eapply L_RET30; try eassumption; try lia.
Qed.

#[using="fc pre post pok fuelc f0 kmin0 c0 Hp SE_T SPF SPT SG1 SG3"] Lemma L_INFR : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c sign,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = sINF sign ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd94d8) fct None m (seg_rom usegs)).
Proof.
intros until sign. intros WI RJ Hk FOK FRM' Hsg Hy.
destruct Hsg as [-> | ->]; unfold sINF in Hy; cbn in Hy;
(zs; zs; zs; zs; stmt L_A38; eapply NX; try eassumption; try lia;
[ fok | | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity]);
[left | right; left]; (split; [apply bv_eq; vm_compute; reflexivity | exact Hy]).
Qed.

#[using="Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3"] Lemma L_ERR : S_ERR.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hst HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC2 : rw_cells usegs mm Fp (rf_cells T p true (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) J))
by (unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite Hsn, Hns; unfold M64; hyp_cells) end.
rewrite rf_cells_raw_eq in FC2.
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (J := J);
[exact FC2 | exact (RFI_ok T txt p J _ _ _ RJu) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ (sh_lim0 _) _) |- _ => rename H into FC3 end. rewrite <- HfR in FC3.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
rewrite <- Hy. eapply L_RET30; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJu). all: try flia.
Qed.

#[using="pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i s0v : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(3 <= i <= 7)%Z -> (0 <= s0v < 256)%Z -> ((i = 3 /\ s0v <> 73) \/ (4 <= i /\ s0v = 73))%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 s0v) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd94a8) fc None m (seg_rom usegs)).
Proof.
intros until s0v. intros WI RJ Hk Hst Hsg Ri Rs0 Hs0 HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (RJR : RFJ' (kmin - 1 - (i - 3)) c fR).
{ rewrite HfR. replace (i - 3)%Z with (Z.of_nat (Z.to_nat (i - 3))) at 1 by lia. apply RFJ_ungetn; [| rewrite (rf_unget_eq f Hsn); exact Hsn | lia].
exact (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)). }
assert (Hsn2 : sh_shlim_neg (sh_unget f) = false) by (rewrite (rf_unget_eq f Hsn); exact Hsn).
rewrite (fs_unget_loop_eq (Z.to_nat (i - 3)) (sh_unget f) Hsn2) in HfR. rewrite (rf_unget_eq f Hsn) in HfR. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in HfR.
specialize (KM Hsn).
ufc FC. rewrite Hsn, Hns in FC. rewrite Hpok1.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K2; [ exfalso; lia | ]).
zs. zs. brf K3.
-
assert (Ei : i = 3%Z) by (clear -K3 Hs0 Rs0; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
subst i. change (Z.of_nat (Z.to_nat (3 - 3))) with 0%Z in HfR. replace (sh_rpos f - 1 - 0)%Z with (sh_rpos f - 1)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold QHB6.Mq3.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
- assert (Es : s0v = 73%Z) by (clear -K3 Hs0 Rs0; rewrite ?land_W64 in K3; Z.div_mod_to_equations; lia).
zs. zs. zs. zs0.
replace (Z.of_nat (Z.to_nat (i - 3))) with (i - 3)%Z in HfR by lia.
eapply L_INFR; try eassumption; try flia.
+ unfold QHB6.Mq3.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
rewrite HfR. unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite Hns. unfold M64. hyp_cells.
+ apply Fok_refl.
Qed.

#[using="pre post fuelc kmin0 c0 Hpok1 Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_IEX4 : forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (i : Z),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (i - 2 <= kmin)%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
(4 <= i <= 7)%Z ->
fR = fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f) -> yR = sINF sign ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) (Z_to_bv 64 (- i)) x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd94a4) fc None m (seg_rom usegs)).
Proof.
intros until i. intros WI RJ Hk Hst Hsg Ri HfR Hy. pose proof WI as WI0. dest_winv WI.
rewrite Hpok1. zs. (brf K; [ exfalso; lia | ]). rewrite <- Hpok1.
eapply L_IEX; try eassumption; try lia.
Qed.

Ltac inf_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.

Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I7 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (4 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 7 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd9428) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 7) with 121%Z in HK. change (7 <? 7)%Z with false in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
-
and33y K1 c'' Rch 89%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_infk_8, FS_inf_8 in HK. injection HK as EfR EyR.
eapply L_INFR; [rewrite <- EfR; mk_winv2 | rewrite <- EfR; exact RJ1 | flia | apply Fok_refl | exact FRM | exact Hsg | symmetry; exact EyR].
- and33n K1 c'' Rch 89%Z N1. replace (Z.lor c'' 32 =? 121)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. change (Z_to_bv 64 (-7)) with (Z_to_bv 64 (- 7)).
eapply L_IEX4 with (i := 7%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I6 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (3 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 6 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd92ac) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 6) with 116%Z in HK. change (6 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 84%Z N1. replace (Z.lor c'' 32 =? 116)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-6)) with (Z_to_bv 64 (- 6)).
eapply L_IEX4 with (i := 6%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 84%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I7; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I5 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 5 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8dcc) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 5) with 105%Z in HK. change (5 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-5)) with (Z_to_bv 64 (- 5)).
eapply L_IEX4 with (i := 5%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I6; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I4 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 4 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 73) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8da8) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 4) with 110%Z in HK. change (4 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_mid _ _ _ _ _ _ _ _ Hpok1) in HK by lia. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-4)) with (Z_to_bv 64 (- 4)).
eapply L_IEX4 with (i := 4%Z); try eassumption; try flia; try (symmetry; assumption). mk_winv2.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I5; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 3 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8d84) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 3) with 105%Z in HK. change (3 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 73%Z N1. replace (Z.lor c'' 32 =? 105)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite (FS_inf_3 _ _ _ _ _ _ _ Hpok1) in HK. injection HK as EfR EyR.
zs. zs. change (Z_to_bv 64 (-3)) with (Z_to_bv 64 (- 3)).
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *.
eapply L_IEX with (i := 3%Z) (s0v := Z.land c'' 18446744073709551583); try eassumption; try flia; try (symmetry; assumption);
try mk_winv2; try (apply and33_range; exact Rch); try (left; split; [reflexivity | exact K1]).
- and33y K1 c'' Rch 73%Z E1. rewrite E1, Z.eqb_refl in HK.
rewrite ?land_W64 in *. rewrite ?(Z.mod_small _ _ Rch) in *. rewrite K1.
eapply L_I4; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 -> (sign = 1 \/ sign = -1)%Z ->
FS_infk' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 pok) x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8cc4) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst Hsg HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 2) with 102%Z in HK. change (2 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 70%Z N1. replace (Z.lor c'' 32 =? 102)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 70%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_I3; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
Qed.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG3 FRM"] Lemma L_I1 : S_I1.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hci HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in Hci; discriminate Hci).
inf_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_infk_step in HK by lia. change (znth str_infinity 1) with 110%Z in HK. change (1 <? 7)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_I2; only 7: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst | exact Hsg].
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_inf_err in HK by lia. injection HK as EfR EyR.
zs.
stmt L_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
Qed.
End Floatscan.
End Mq9.

Module Mqa.

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
Import QHB6.Mq3 QOy4.
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_N1 := (@QOy4.S_N1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_Z := (@QOy4.S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_ERR := (@QOy4.S_ERR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A38 := (@QOy4.S_A38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_PAR := (@QOy4.S_PAR ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Notation FS_nank' := (FS_nank fuelc 53 (-1074) pok).
Notation FS_nan' := (FS_nan fuelc 53 (-1074) pok).

Hypothesis HS_Z : S_Z.
Hypothesis HS_ERR : S_ERR.
Hypothesis HS_A38 : S_A38.

Ltac nan_read FC RJ kmin c f Hc0 :=
let KS := fresh "KS" in
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1;
pose proof (getc_stdio f) as Hst1;
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|];
pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT;
rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *; cbn [fst snd] in *;
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch;
ufc2 FC;
zs; zs; zs; br KS; zs; zs0; read_char f.
Ltac and33y K c R U E := assert (E : Z.lor c 32 = (U + 32)%Z)
by (apply (proj1 (and33_lor c U R ltac:(lia))); rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
first [exact K | clear -K R; Z.div_mod_to_equations; lia]).
Ltac and33n K c R U N := assert (N : Z.lor c 32 <> (U + 32)%Z)
by (intros EE; apply (proj2 (and33_lor c U R ltac:(lia))) in EE; rewrite ?land_W64 in K; rewrite ?(Z.mod_small _ _ R) in K;
clear -K EE; lia).

#[using="fc pre post pok fuelc f0 kmin0 c0 HS_A38"] Lemma L_NANR : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws k c,
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws fR ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> yR = C_NAN ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd928c) fct None m (seg_rom usegs)).
Proof.
intros until c. intros WI RJ Hk FOK FRM' Hy.
zs. zs. zs.
stmt HS_A38. eapply NX; try eassumption; try lia;
[ fok | right; right; split; [reflexivity | exact Hy] | intros r Hr; apply freg_get_same; rewrite Hr; vm_compute; reflexivity ].
Qed.

#[using="fc pre post pok fuelc f0 kmin0 c0 Hp HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PUNG : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
fR = sh_unget f -> yR = C_NAN ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9278) fct None m (seg_rom usegs)).
Proof.
intros until f. intros WI RJ Hk FOK FRM' HfR Hy. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu. rewrite (rf_unget_eq f Hsn) in RJu, HfR.
ufc FC. rewrite Hsn, Hns in FC.
zs. zs. (brf K1; [ exfalso; lia | ]). zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite HfR. unfold QHB6.Mq3.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
rewrite HfR. exact RJu. flia.
Qed.

Definition alnumb (c : Z) : bool := ((u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95))%Z.
#[using="Type"] Lemma alnumb_iff : forall c, (0 <= c < 256)%Z ->
(alnumb c = true <-> (48 <= c <= 57 \/ 65 <= c <= 90 \/ 97 <= c <= 122 \/ c = 95))%Z.
Proof.
clear. intros c Hc.
pose proof (forallb_range (fun c => Bool.eqb (alnumb c) (((48 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)) || (c =? 95)))%Z 256 ltac:(vm_compute; reflexivity) c Hc) as E.
cbv beta in E. apply Bool.eqb_prop in E. rewrite E.
rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le, Z.eqb_eq. tauto.
Qed.
Ltac kswrap K := rewrite swrap32_small in K by lia; rewrite land_W64 in K.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_A38"] Lemma L_PAR : S_PAR.
Proof.
intros n. induction n as [|n IH]; intros m; intros until f'; intros _ WI RJ Hk FOK FRM' Hc0 Hst Ri HL HR; [discriminate HL|].
pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
rewrite fs_par_loop_S in HL. unfold fs_par_body in HL.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
fold (alnumb c'') in HL. pose proof (alnumb_iff c'' Rch) as AIF. destruct (alnumb c'') eqn:AL.
-
pose proof (proj1 AIF eq_refl) as RANGE. clear AIF.
assert (CONT : forall m2 (x11' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 i) (Z_to_bv 64 10) (Z_to_bv 64 c'') x11' x12 x13 x14 x15 x16 x17
(Z_to_bv 64 26) (Z_to_bv 64 95) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8ec4) fct None m2 (seg_rom usegs))).
{ intros m2 x11' WI2.
assert (Hc1 : c'' <> 0%Z) by (clear -RANGE; lia).
pose proof WI2 as WI3. destruct WI3 as (FI3 & FL3 & XW3 & LW3 & FC3). pose proof FI3 as FI4. dest_finv FI4.
zs.
eapply (IH m2); try eassumption; try flia. cbn [sh_rpos]. flia. }
zs. zs. brf K1; kswrap K1.
+ zs. zs. brf K2; kswrap K2.
* eapply CONT. mk_winv2.
* zs. brf K3.
-- eapply CONT. mk_winv2.
-- zs. zs. brf K4; kswrap K4.
++ eapply CONT. mk_winv2.
++ exfalso. clear -K1 K2 K3 K4 RANGE Rch. Z.div_mod_to_equations. lia.
+ zs. eapply CONT. mk_winv2.
-
assert (NR : ~ (48 <= c'' <= 57 \/ 65 <= c'' <= 90 \/ 97 <= c'' <= 122 \/ c'' = 95)%Z) by (intros X; apply (proj2 AIF) in X; discriminate X). clear AIF.
injection HL as <- <- <-.
zs. zs. brf K1; kswrap K1; [| exfalso; clear -K1 NR Rch; Z.div_mod_to_equations; lia].
zs. zs. brf K2; kswrap K2; [exfalso; clear -K1 K2 NR Rch; Z.div_mod_to_equations; lia |].
zs. brf K3; [exfalso; clear -K3 NR Rch; lia|].
zs. zs. brf K4; kswrap K4; [exfalso; clear -K1 K2 K3 K4 NR Rch; Z.div_mod_to_equations; lia|].
zs. zs. brf K5.
+
assert (E41 : c'' = 41%Z) by (clear -K5 Rch; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
rewrite E41, Z.eqb_refl in HR. injection HR as EfR EyR.
eapply L_NANR with (k := (kmin + 1)%Z) (c := c''); [ rewrite EfR; mk_winv2 | rewrite EfR; exact RJ1 | flia | exact FOK | exact FRM' | exact EyR ].
+ assert (N41 : c'' <> 41%Z) by (clear -K5 Rch; rewrite ?land_W64 in K5; Z.div_mod_to_equations; lia).
replace (c'' =? 41)%Z with false in HR by (symmetry; apply Z.eqb_neq; exact N41). injection HR as EfR EyR.
destruct (rfj_ns _ _ _ RJ) as [Hns Hsn].
assert (Hsn2 : sh_shlim_neg (sh_unget (mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) = false).
{ unfold sh_unget. cbn [sh_shlim_neg]. rewrite Hsn. reflexivity. }
rewrite (fs_unget_loop_eq (Z.to_nat i) _ Hsn2) in EfR. unfold sh_unget in EfR. cbn [sh_shlim_neg] in EfR. rewrite Hsn in EfR.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in EfR.
assert (RJR : RFJ' (kmin + 1 - 1 - Z.of_nat (Z.to_nat i)) c'' fR).
{ rewrite EfR.
pose proof (RFI_unget T txt p J Hp _ _ _ RJ1 ltac:(flia)) as RJu. unfold sh_unget in RJu. cbn [sh_shlim_neg] in RJu. rewrite Hsn in RJu.
cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb] in RJu.
pose proof (RFJ_ungetn (Z.to_nat i) _ _ _ RJu ltac:(reflexivity) ltac:(lia)) as RJv.
rewrite fs_unget_loop_eq in RJv by reflexivity. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in RJv.
replace (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z with (sh_rpos f + 1 - 1 - Z.of_nat (Z.to_nat i))%Z by lia. exact RJv. }
unfold rf_rend in FC. rewrite ?Hsn, ?Hns in FC. unfold M64 in FC. rewrite Hpok1.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs0. zs. (brf K7; [ exfalso; lia | ]). zs. (brf K8; [ exfalso; lia | ]). zs. (brf K9; [ exfalso; lia | ]). zs. zs. zs. zs0.
eapply L_NANR; try eassumption; try flia.
rewrite EfR. unfold QHB6.Mq3.winv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. rewrite ?Hns, ?Hsn. unfold M64. hyp_cells.
all: flia.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK3 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nan' sign 3 c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8e90) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f. specialize (KM (proj2 (rfj_ns _ _ _ RJ))).
unfold FS_nan in HK. change (3 =? 3)%Z with true in HK. replace (negb (nz pok)) with false in HK by (rewrite Hpok1; reflexivity). cbv iota in HK.
nan_read FC RJ kmin c f Hc0. cbv beta iota zeta in HK.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K1.
-
assert (N40 : c'' <> 40%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
replace (c'' =? 40)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N40). cbn [negb] in HK. injection HK as EfR EyR.
eapply L_PUNG with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; eassumption); try mk_winv2; try apply Fok_refl.
- assert (E40 : c'' = 40%Z) by (clear -K1 Rch; rewrite ?land_W64 in K1; Z.div_mod_to_equations; lia).
rewrite E40, Z.eqb_refl in HK. cbn [negb] in HK.
destruct (fs_par_loop fuelc _) as [[[i' c'] f']|] eqn:HL; [|discriminate HK].
zs. zs. zs. zs. zs.
eapply (L_PAR fuelc) with (kmin := (kmin + 1)%Z) (i := 1%Z) (c := c''); try eassumption; try flia;
try mk_winv2; try apply Fok_refl; try (cbn [sh_rpos]; flia); try (rewrite E40; lia).
destruct (c' =? 41)%Z; cbv zeta iota in HK; injection HK as <- <-; reflexivity.
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK2 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 2 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8d48) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 2) with 110%Z in HK. change (2 <? 2)%Z with false in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 78%Z N1. replace (Z.lor c'' 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 78%Z E1. rewrite E1, Z.eqb_refl in HK. rewrite FS_nank_3 in HK.
zs.
eapply L_NK3; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="pre post kmin0 c0 Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_NK1 : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x25 x26 x27 x28 x29 x30 x31 : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> c <> 0%Z -> sh_stdio f = sh_stdio f0 ->
FS_nank' sign 1 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xd8bcc) fc None m (seg_rom usegs)).
Proof.
intros m; intros until f. intros WI RJ Hk Hc0 Hst HK. pose proof WI as WI0. dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
nan_read FC RJ kmin c f Hc0.
set (c'' := znth txt (sh_rpos f)) in *.
rewrite FS_nank_step in HK by lia. change (znth str_nan 1) with 97%Z in HK. change (1 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. zs. brf K1.
- and33n K1 c'' Rch 65%Z N1. replace (Z.lor c'' 32 =? 97)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_err in HK by lia. injection HK as EfR EyR.
stmt HS_ERR. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try flia; try (symmetry; assumption); try mk_winv2; try apply Fok_refl; try (rewrite Hst1; exact Hst).
- and33y K1 c'' Rch 65%Z E1. rewrite E1, Z.eqb_refl in HK.
zs.
eapply L_NK2; only 6: exact HK; [mk_winv2 | exact RJ1 | flia | intros E0; rewrite E0 in E1; discriminate E1 | rewrite Hst1; exact Hst].
Qed.

#[using="Hpok1 BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 FRM HS_Z HS_ERR HS_A38"] Lemma L_N1 : S_N1.
Proof.
intros m; intros until f. intros _ WI RJ Hk Hst Hsg Hr1 Rc0 Hni HK. pose proof WI as WI0. dest_winv WI. bury_disj.
rewrite FS_nank_step in HK by lia. change (znth str_nan 0) with 110%Z in HK. change (0 <? 2)%Z with true in HK. cbv iota in HK.
zs. zs. brf K1.
- and33n K1 c Rc0 78%Z N1. replace (Z.lor c 32 =? 110)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N1).
rewrite FS_nan_0 in HK.
stmt HS_Z. eapply NX; try eassumption; try flia. apply Fok_refl.
- and33y K1 c Rc0 78%Z E1. rewrite E1, Z.eqb_refl in HK.
eapply L_NK1; only 6: exact HK; [exact WI0 | exact RJ | flia | intros E0; rewrite E0 in E1; discriminate E1 | exact Hst].
Qed.
End Floatscan.
End Mqa.

Module Mqb.

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
Import QHB6.Mq3 QOy4.
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

Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation frame_release := (@QHB6.Mq3.frame_release ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T txt pre canary).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation S_848 := (@QHB6.Mq3.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_6F8 := (@QHB6.Mq3.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Notation POST := (fs_post m0).

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
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

Local Notation S_Z := (@QOy4.S_Z ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_HEX := (@QOy4.S_HEX ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Hypothesis HS_848 : S_848.
Hypothesis HS_6F8 : S_6F8.
Hypothesis HS_HEX : S_HEX.

#[using="BYT Hp Hnul HP30 T0 T1 SEP SPF SPF2 SPT SG1 HS_848 HS_6F8 HS_HEX"] Lemma L_Z : S_Z.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 HK.
dest_winv WI. bury_disj.
site_facts FC RJ kmin c f.
unfold FS_tail_h in HK.
zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
replace (c =? 48)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact N48).
stmt HS_6F8. eapply NX; try eassumption; try lia. mk_winv2.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
rewrite E48, Z.eqb_refl in HK. rewrite (surjective_pairing (sh_getc f)) in HK. rewrite E48 in RJ.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
unfold FS_zero in HK.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
assert (JOIN : forall m2 (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws (snd (sh_getc f)) ->
(Z.lor (fst (sh_getc f)) 32 =? 120)%Z = false ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8 (Z_to_bv 64 sign) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd8e3c) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2 NX120. rewrite NX120 in HK.
stmt HS_848. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia. }
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST]; [exfalso; exact (rf_slow_false _ _ _ RJ SLOW)|].
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K2; [ exfalso; lia | ]).
zs. zs0. read_char f.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. zs. brf K3; rewrite ?land_W64 in K3.
+
eapply JOIN. { mk_winv2. }
apply Z.eqb_neq. intros E. apply (proj2 (and33_lor c'' 88 Rch ltac:(lia))) in E. clear -K3 E Rch. Z.div_mod_to_equations; lia.
+
assert (E120 : Z.lor c'' 32 = 120%Z).
{ apply (proj1 (and33_lor c'' 88 Rch ltac:(lia))). clear -K3 Rch. pose proof (and33_range c'' Rch). Z.div_mod_to_equations; lia. }
rewrite E120, Z.eqb_refl in HK.
unfold ssp_guard. zs. zs. zs. zs. zs. (brf K4; [ | exfalso; lia ]).
zs. zs. zs. zs. zs. zs. zs. zs.
do 14 zs. zs. zs.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (WI9 : winv mm j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws
(mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f))) by mk_winv2 end.
destruct WI9 as (FI9 & FL9 & XW9 & LW9 & FC9).
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI9 FL9 XW9 LW9) as STK.
stmt HS_HEX. eapply NX with (kmin := (kmin + 1)%Z); try eassumption; try lia.
* destruct FI9 as (MI9 & MU9 & WM9 & FRhi9 & ST9 & BY9 & SSA & SSB). destruct FL9 as [LOW9 ERR9].
unfold QOy4.hinv. split; [exact MI9|]. split; [exact MU9|]. split; [exact WM9|]. split; [exact STK|]. split; [exact BY9|].
split; [exact SSA|]. split; [exact SSB|]. split; [exact ERR9|]. exact FC9.
* intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
-- rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
-- rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
Qed.
End Floatscan.
End Mqb.

Module Mqc.

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
Import QHB6.Mq3 QOy4.
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

Local Notation ctx_all := (@QHB6.Mq3.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Wfs := (@QHB6.Mq3.Wfs q Fp).
Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).

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

Notation HSP := (Z_to_bv 64 (q + -176)).
Notation Y0 := (f128_of_i32 0).
Notation SC0 := (f128_of_i32 1).
Notation HX_alz' := (HX_alz fuelc 53 (-1074)).
Notation HX_rz' := (HX_rz fuelc 53 (-1074)).
Notation HX_dig' := (HX_dig fuelc 53 (-1074)).
Notation HX_tail' := (HX_tail fuelc 53 (-1074)).
Notation HX_e2' := (HX_e2 53 (-1074)).
Notation HX_fin' := (HX_fin 53 (-1074)).

Definition hxfr (w0 w8 w16 w24 w32 w40 w48 w56 : word) (m : word -> option byte) : Prop :=
rw_cells usegs m (q + -176) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 (reg_get F 8);
C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition hxinv (m : word -> option byte) (ev : word) (f : shfile) : Prop :=
mem_inv usegs m /\ munch Wfs m0 m /\ wmono usegs m0 m
/\ stk usegs m (q - FS_DEPTH) (q + -176)
/\ bytes_at usegs m T (zbytes txt)
/\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary]
/\ rw_cells usegs m RERRNO [C4 ev]
/\ rw_cells usegs m Fp (rf_cells T p true f J).

Definition kminH (kmin gd gr : Z) : Prop := (1 <= kmin)%Z /\ (gd = 0%Z -> 2 + gr <= kmin)%Z.

Definition SHLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd gd' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (gd, 48, f)%Z = Some (gd', c', f') -> HX_alz' sign pok gd' c' f' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda20c) fct None m (seg_rom usegs)).
Definition S_HLZ : Prop := forall n, SHLZn n.

Definition S_H778 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
HX_alz' sign pok 1 c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 0) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 0) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda228) fct None m (seg_rom usegs)).

Definition S_H720 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z ->
(0 <= gd <= 1)%Z ->
HX_rz' sign pok gd 0 (fst (sh_getc f)) (snd (sh_getc f)) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) x9 (Z_to_bv 64 (T + sh_rpos f)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda1d0) fct None m (seg_rom usegs)).

Definition SHRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin (f : shfile) (gd rp gd' rp' c' : Z) (f' : shfile),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin 48 f -> (3 <= kmin)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(- sh_rpos f <= rp <= 0)%Z ->
df_rz_loop n (gd, rp, 48, f)%Z = Some (gd', rp', c', f') -> HX_dig' sign pok (mkHX c' f' 0 Y0 SC0 0 1 gd' rp' 0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 (Z_to_bv 64 48) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda26c) fct None m (seg_rom usegs)).
Definition S_HRZ : Prop := forall n, SHRZn n.

Definition S_H7F0 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x26 x28 x29 x30 x31 : word) Ft fct
ev (w8 w16 w32 w48 : word) sign kmin c (f : shfile) (gd gr rp : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) w8 w16 (Z_to_bv 64 (-1074)) w32 (Z_to_bv 64 sign) w48 (Z_to_bv 64 (lo64 SC0)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> (0 <= c < 256)%Z ->
(0 <= gd <= 1)%Z -> (0 <= gr <= 1)%Z -> (- sh_rpos f <= rp <= 0)%Z ->
HX_dig' sign pok (mkHX c f 0 Y0 SC0 0 gr gd rp 0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 pok) x21 x22 (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 Fp) x25 x26 (Z_to_bv 64 (hi64 SC0)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda2a0) fct None m (seg_rom usegs)).

Definition hxI (f : shfile) (c x gt gr gd rp dc : Z) : Prop :=
(0 <= c < 256)%Z /\ (0 <= x < 2^32)%Z /\ (0 <= gt <= 1)%Z /\ (0 <= gr <= 1)%Z /\ (0 <= gd <= 1)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (- sh_rpos f <= rp <= sh_rpos f)%Z.

Definition SHDn (n : nat) : Prop := forall (pc : Z) m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z) (s' : st_hex),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
hx_dig_loop n (mkHX c f x y sc gt gr gd rp dc) = Some s' -> HX_tail' sign pok (hx_c s') (hx_f s') (hx_x s') (hx_y s') (hx_gr s') (hx_gd s') (hx_rp s') (hx_dc s') = Some (fR, yR) ->
((pc = 0xda304%Z /\ isdigitc c = true) \/ (pc = 0xda400%Z /\ isdigitc c = false)) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) (Z_to_bv 64 (bv_swrap 32 (c + -48))) (Z_to_bv 64 c) x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 pc) fct None m (seg_rom usegs)).
Definition S_HD : Prop := forall n, SHDn n.

Definition S_HTL : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
ev sign kmin c (f : shfile) (x y sc gt gr gd rp dc : Z),
let _ := ctx_all in
hxinv m ev f -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 gt) (Z_to_bv 64 (lo64 sc)) m ->
RFJ' kmin c f -> kminH kmin gd gr -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
hxI f c x gt gr gd rp dc ->
HX_tail' sign pok c f x y gr gd rp dc = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 gd) (Z_to_bv 64 gr) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 rp) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 dc) (Z_to_bv 64 (sext32 x)) (Z_to_bv 64 46) (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 57) (Z_to_bv 64 (hi64 sc)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda414) fct None m (seg_rom usegs)).

Definition S_HE2 : Prop := forall m (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y rp e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(0 < x < 2^32)%Z -> (-2^32 <= rp <= 2^32)%Z -> (-2^60 <= e2 <= 2^60)%Z ->
HX_e2' sign fR x y (4 * rp + e2 - 32) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 rp) x9 (Z_to_bv 64 e2) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 Fp) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda4c4) fct None m (seg_rom usegs)).

Definition SHNLn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 x' y' e2' : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> reg_get Ft 8 = D_05 ->
(0 < x < 2^31)%Z -> (-1340 + Z.of_nat n <= e2 <= 1074)%Z ->
hx_norm_loop n (x, y, e2) = Some (x', y', e2') -> HX_fin' sign fR x' y' e2' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda610) fct None m (seg_rom usegs)).
Definition S_HNL : Prop := forall n, SHNLn n.

Definition S_HFIN : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w48 w56 : word) sign k c (x y e2 : Z),
let _ := ctx_all in
hxinv m ev fR -> hxfr (Z_to_bv 64 53) (Z_to_bv 64 (hi64 Y0)) (Z_to_bv 64 (lo64 Y0)) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z ->
(2^31 <= x < 2^32)%Z -> (-1500 <= e2 <= 1074)%Z ->
HX_fin' sign fR x y e2 = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 (Z_to_bv 64 (-1074)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 (lo64 y)) x20 (Z_to_bv 64 (sext32 x)) x22 (Z_to_bv 64 (hi64 y)) (Z_to_bv 64 e2) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda65c) fct None m (seg_rom usegs)).

Definition S_HZR : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
ev (w0 w8 w16 w24 w32 w48 w56 : word) sign k c,
let _ := ctx_all in
hxinv m ev fR -> hxfr w0 w8 w16 w24 w32 (Z_to_bv 64 sign) w48 w56 m ->
RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct -> (sign = 1 \/ sign = -1)%Z -> yR = hx_zero sign ->
evt usegs POST
(MS (mkR x1 HSP gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda564) fct None m (seg_rom usegs)).

#[using="Type"] Lemma HX_fin_f : forall sign f x y e2 f' y', HX_fin' sign f x y e2 = Some (f', y') -> f' = f.
Proof.
clear. intros until y'. unfold HX_fin.
match goal with |- context [match ?X with pair _ _ => _ end] => destruct X as [[bias x2] y2] end. intros H; injection H as <- _; reflexivity.
Qed.
#[using="Type"] Lemma HX_e2_f : forall sign f x y e2 f' y', HX_e2' sign f x y e2 = Some (f', y') -> f' = f.
Proof.
clear. intros until y'. unfold HX_e2.
destruct (x =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (- (-1074) <? e2)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (e2 <? -1074 - 2 * LDBL_MANT_DIG_)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (hx_norm_loop 33 _) as [[[x3 y3] e3]|]; [apply HX_fin_f | discriminate].
Qed.
End Floatscan.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QXxF.Mq0 QM7w QNAo.Mq0 QFs1.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QmBS.Mq6 Qlfl Qlfl.Mq6 QHB6 QYnB.Mqc.

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

Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv usegs m3 /\ stk usegs m3 lo (bv_unsigned sp + -144) /\
rw_cells usegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rw_cells usegs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0xd125c) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
(wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
a1 (wz cnt1) (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 pc) fc None m3 (seg_rom usegs).

Definition rHMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0xd1330 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0xd1374 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof.
intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.
pose proof (QULt.Mq1.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
pose proof (size_class_range sc SC) as SZR.
rewrite (ag_body_eq f sc req k bail st2 mm).
riprefixT. unfold rag_regs.
eapply evt_cut.
{ eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
cbv beta. intros ms' (a2'' & a3'' & a4'' & ->).
set (size := size_class sc * UNIT).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
assert (C0R : 1 <= cnt0 <= 32).
{ pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
subst cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
destruct (negb _); [lia|]. destruct (negb _); lia.
- apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
eapply evt_cut.
{ eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
cbv beta. intros ms' ->. unfold rcnt_regs.
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
assert (EC : ag_cnt1 sc st2 = cnt1).
{ unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
apply evt_done.
destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
- pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
- pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.

End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq4 Q4J3.Mq3 QPjm.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9 Q6y7.Mq2 QNAo.Mq1.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QdZ1 QQbX Qn9M Qv4L.Mqi Qv4L.Mqb Qv4L QnkH.Mqi Qi8L.Mq9 QmBS QkLq.Mq4 QYnB.Mqe QdZ1.Mq8.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : QUZl.M R1) (t2 : QUZl.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
implM usegs (membed t1) s Q1 ms ->
implM usegs (membed t2) s
(fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
exists r1, []. cbn. auto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
impl usegs (at_node usegs) (QlEo_c1.Mq0.bind _ (Ret Unr) f) Qx msx = impl usegs (at_node usegs) (f Unr) Qx msx) by reflexivity.
destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w|ma ol nl fl].
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. exact H. }
5:{ cbn [ev_step] in *. unfold munr in *. cbn [QlEo_c1.Mq0.bind] in *. exact H. }
all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
eapply impl_epost_mono; [eapply IH; exact H1|];
intros [r2' s2] ms2; cbn; intros (r1' & ans & F1 & F2 & HR & HQ);
exists r1', (z :: ans); cbn; auto.
Qed.

#[using="Type"] Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
strip st = ps_m s ->
rimplT o (malloc st n) s Q1 ms ->
(forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
Q1 (st', p) s' ms' -> ptr_rel p r ->
follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
follow (cmalloc (strip st) n) ans = Some (cst, c) ->
cst = strip st' ->
r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
Q r (set_m (strip st') s') ms') ->
implM usegs (raw_malloc n) s Q ms.
Proof.
intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
eapply (implM_bind usegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind usegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
/\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
{ rewrite <- Hst. unfold rimplT in H.
eapply implM_mono.
- eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
unfold mrun. apply malloc_control. apply pans_mem_range.
- intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
exists st', p, ans, o1. auto. }
intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
eapply (implM_bind usegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

#[using="Type"] Lemma rimplT_silent {R} o (t : QUZl.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt usegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

#[using="Type"] Lemma rheap_pres_of_fp st st' LB lo sp m m' :
RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
rpres_except (rmalloc_fp st st' lo sp) m m' -> alloc_ceiling <= lo -> lo <= sp ->
rheap_pres LB sp m m'.
Proof.
intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
- destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); unfold alloc_ceiling in *; lia.
- destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RMLOCK, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
- destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
unfold alloc_ceiling in *.
pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
pose proof (round_up_pg_mono _ _ L1) as RL1.
pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
+ lia.
+ rewrite unsigned_lit in H by lia. lia.
+ unfold RCTX in H. lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
* pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
* pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
+
exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

#[using="Type"] Lemma ruser_chunk st' m' (p : aptr) r n :
rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
exists junk, rw_cells usegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
intros MR Hr Hk P0 PN N0.
pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). unfold alloc_ceiling in RC.
rewrite (conc_region' st' p r Hr).
assert (W : wr_at usegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
split; [exact L| exact I].
Qed.

Definition malloc_core_allzero_stmt : Prop :=
forall st L BL LS n (o : mem) ans (o' : mem) st1 g idx,
Qatc.INVL Qatc.x0 st L BL LS -> 0 <= n ->
follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
is_allzero_ctrl (Qatc.MR st1 g) = true ->
exists bg, m_mem (Qatc.MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (Qatc.MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (Qatc.sstart (Qatc.MR st1 g) idx + k) = Known 0.

#[using="Type"] Lemma bytes_at_inj0 m a bs bs' : bytes_at usegs m a bs -> bytes_at usegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros (_ & _ & H) (_ & _ & H') L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H i Hi), <- (H' i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rzeros_of_shadow st m rid r base (cnt : nat) :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= base -> base + Z.of_nat cnt <= round_up_pg (r_len r) ->
(forall j, 0 <= j < Z.of_nat cnt -> cell_read (get_shadow st rid) (base + j) = Known 0) ->
bytes_at usegs m (r_base r + base) (zeros cnt).
Proof.
intros MR Hr Hk B0. pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH rid r Hr Hk) as [HW HB].
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & _). unfold alloc_ceiling in RBC.
induction cnt as [|cnt IH]; intros BC HC.
- cbn. apply bytes_at_nil. lia.
- replace (zeros (S cnt)) with (zeros cnt ++ [b8 0]) by (unfold zeros; rewrite <- repeat_cons; cbn; reflexivity).
apply bytes_at_app. split; [apply IH; [lia| intros j Hj; apply HC; lia]|].
unfold zeros. rewrite repeat_length. replace (r_base r + base + Z.of_nat cnt) with (r_base r + (base + Z.of_nat cnt)) by lia.
exact (proj1 (HB (base + Z.of_nat cnt) 0 ltac:(lia) (HC (Z.of_nat cnt) ltac:(lia)))).
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis MCZ : malloc_core_allzero_stmt.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_impl_spec_proof : rmalloc_impl_stmt.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR0.
assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
pose proof (QTyG.Mq2.areach_facts_proof _ _ AR) as MF.
assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
unfold raw_malloc.
eapply (implM_bind usegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0' s1' ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind usegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
{ rewrite <- Hst. unfold cmalloc.
eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
x = (strip st2, r)
/\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
- eapply implM_mono.
+ eapply (rmembed_strel_follow CREL).
* pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
* unfold rimplT in |- *.
pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
unfold rimplT in X. exact X.
+ intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
- intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
intros [cs c] s' ms'' MQ. cbv beta iota.
destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
eapply (implM_bind usegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] sx msx [-> ->]. apply implM_ret.

assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
| Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
follow (cmalloc (strip st) n) ans = Some y).
{ intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
destruct r as [[g idx]|].
-
cbn [rcoreQ] in CQ.
destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
{ rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
set (stride := get_stride (get_meta_rec st2 g)) in *.
set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
unfold alloc_ceiling in RC, CLO. unfold RMALLOC_STACK in LO.
pose proof (renf_implT (RC__:=RC__) sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
eapply evt_mono; [exact EV|]. clear EV.
intros msf [_ EP]. unfold renf_post in EP.
destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF & UB).
destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
{ rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
set (A := conc st' p) in *.

assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
{ unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
fold A in UCH.
unfold rmalloc_post. do 15 eexists. exists m', errv1.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
- lia.
- lia. }
assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
{ eapply rpres_except_mono.
+ eapply rpres_except_trans; [exact PE2|].
eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
+ intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
exists A, ujunk.
split; [reflexivity|].
split. { unfold rblock_range, alloc_ceiling. rewrite EA.
split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
- apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
- exact AR'. }
split; [exact UCH|].
split.
2:{
intros g0 idx0 SL0 AZ. cbn [ps_m set_m fst] in SL0, AZ.
rewrite s_slots_strip in SL0. unfold slot_of, slot_start' in SL0. rewrite Hmem in SL0. cbn [default from_option id] in SL0.
unfold aadd in SL0. cbn [fst snd] in SL0.
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + get_stride (get_meta_rec st2 g) * idx) in SL0 by (unfold UNIT; lia).
rewrite SSL in SL0. assert (g0 = g /\ idx0 = idx) as [-> ->] by (inversion SL0; auto). clear SL0.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g) in AZ.
destruct (Q3o5.Mq1.areach_inv _ st LB AR) as (L & LS & BL0 & INV & _).
destruct (MCZ st L BL0 LS n m ans m st2 g idx INV ltac:(lia) F1 AZ) as (bg & Hbg & CZ).
change (Qatc.MR st2 g) with (get_meta_rec st2 g) in Hbg, CZ. rewrite Hmem in Hbg. assert (bg = b) as -> by congruence.
unfold Qatc.sstart, Qatc.gbase in CZ. rewrite Hmem in CZ. cbn [default id snd] in CZ. fold stride in CZ.
assert (Z0 : bytes_at usegs m1 A (zeros (Z.to_nat n))).
{ rewrite EA. replace (r_base rg + snd b + 16 + stride * idx + 16 * off) with (r_base rg + (snd b + 16 + stride * idx + 16 * off)) by lia.
apply (rzeros_of_shadow st2 m1 (fst b) rg); [exact MR2| exact Hr| exact Hk| lia| |].
- rewrite Ep in *. cbn [snd] in *. subst stride. lia.
- intros j Hj. replace (snd b + 16 + stride * idx + 16 * off + j) with (snd b + UNIT + stride * idx + (16 * off + j)) by (unfold UNIT; lia).
apply CZ. unfold IB. lia. }
pose proof (UB (zeros (Z.to_nat n)) Z0 ltac:(unfold zeros; rewrite repeat_length; lia)) as Z1.
pose proof (rw_cells_bytes_at _ _ _ _ UCH) as UJ. cbn [cells_bytes cbytes] in UJ. rewrite app_nil_r in UJ.
pose proof (proj1 (proj1 UCH)) as WFJ. cbn in WFJ. destruct WFJ as [LJ _].
apply (bytes_at_inj0 m' A); [exact UJ| exact Z1| unfold zeros; rewrite repeat_length; lia]. }

intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
{ apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
unfold fresh_off. cbn [s_slots strip].
replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
-
cbn [rcoreQ] in CQ.
destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO & E12).
apply evt_done. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
split; [exact PSF|]. split; [exact PSO|].
split; [reflexivity|]. split; [exact E12|].
exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
split.
+ apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
+ eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof. exact (rmalloc_stmt_of_impl rmalloc_impl_spec_proof). Qed.

End TOPLEVEL.

End RC__1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFs1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFs1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHB6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHB6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHB6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHB6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TASLOT.
Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : RISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="LB sc F ER SC RQ FIT TR GM MSK K0 LBK"] Lemma rta_slot_ok : exists b r,
m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
/\ slot_ok st' g b r k req
/\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
free_slot_addr st0 a).
Proof.
pose proof (isf_mf _ _ F) as MF.
pose proof (gmf_cls _ _ _ GM) as GSC.
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK).
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20).

destruct (tr_geom _ _ _ TR g) as (EM & EL & EF & ES & EP).
assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite EL, ES, EP; reflexivity).
assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
{ rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }

assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
{ apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
destruct (FM g b Hmem) as (FM1 & FM2 & _).
assert (KLI : k <= m_last_idx (get_meta_rec st g)).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
cbv zeta in FC. destruct FC as [NOGRP _].
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
{ pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
assert (P2k : 0 < 2 ^ k <= msk).
{ split; [apply Z.pow_pos_nonneg; lia|]. destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE'). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
exists b, r.
split; [exact Hmem|]. split; [exact Hr|].
split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
split; [| split; [exact ST'|]].
- pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4).
assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
rewrite ?ST2; fold mr; rewrite ?EM, ?EL, ?EF, ?ES, ?EP, ?STX.
+ exact Hmem.
+ unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
+ exact Hk.
+ exact B0.
+ exact B16.
+ lia.
+ lia.
+ exact SPAN.
+ unfold UNIT in S16. lia.
+ unfold UNIT in SMOD. exact SMOD.
+ lia.
+ exact RQ.
+ lia.
+ intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _). exact (NOGRP b' gh1 Hb1 Hf').
+ unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
+ intros off O0 OF.
assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
+ unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
+ unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
+ unfold msk, mr in *. lia.
+ unfold mr. lia.
+ lia.
+ lia.
+ left. lia.
- intros a Ha. rewrite ST' in Ha.
destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0').
exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
+ pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
+ assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
lia.
Qed.
End TASLOT.

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

#[using="RC__ R k o s Q ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req errv ERR TP HK"] Lemma rerrno_lit : errno_addr tp = 0x62547c.
Proof. subst tp. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="st0 LB errv AR IS ER AC SC RQ FIT MR TK UA BL AUX CLO LO ERR TP HK F0"] Lemma rhk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
rpres_except (rta_fp st lo (bv_unsigned sp)) m m' ->
rimplT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof.
intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
pose proof rerrno_lit as EA. pose proof (RAS_STACK_ge sc) as ASG.
pose proof (isf_mf _ _ F0) as MF.
set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
subst msk.
destruct (rta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA).
fold st' in Hr', SO, STR, FSA.

pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).

assert (FPC : forall a, rta_fp st lo (bv_unsigned sp) a -> rmalloc_fp st0 st' lo (bv_unsigned sp) a).
{ intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- left. left. exact X.
- left. right. right. left. exact X.
- left. do 3 right. destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
- do 3 right. left. destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct ER as [_ EG EGR _ _ _ _ _].
destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
assert (PE' : rpres_except (rmalloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply rpres_except_mono; [exact PE| exact FPC]).

assert (NIMG : forall a, 0x10000 <= a < 0x647000 -> ~ (RCTX <= a < RCTX + 928) -> ~ rta_fp st lo (bv_unsigned sp) a).
{ intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- unfold alloc_ceiling in CLO. lia.
- exact (Hc X).
- destruct (rmeta_slot_bounds st m q MR MSq) as (_ & _ & GI & _). lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _). destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2).
pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
apply HK. unfold ras_post2.
exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold RCTX; lia]. }
split. { eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
+ lia. + unfold RCTX in X. unfold alloc_ceiling in CLO. lia.
+ destruct (rmeta_slot_bounds st m q MR MSq) as (_ & GC & _). unfold alloc_ceiling in CLO. lia.
+ destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC). unfold alloc_ceiling in *. lia.
- intros a Ha. apply NIMG; unfold RAUXV_CELL, RCTX in *; lia. }
split; [exact MR'|].
split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
split. {
intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
{ revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
assert (NG0 : ~ grp_hdr_cov st rid off).
{ intros (bq & gh & Hbq & Hf & Hoff). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
refine (proj1 (PE (r_base rr + off) _ _)).
{ destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). pose proof (round_up_pg_ge (r_len rr)). unfold alloc_ceiling in RC. lia. }
intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
- destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _). lia.
- destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold RCTX in X. lia.
- destruct (rmeta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid rr Hrr Kr); lia.
- destruct (rgroup_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _).
destruct (N.eq_dec (fst bq) rid) as [E|NE].
+ apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
+ pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
split; [exact PE'|].
split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
intros rid rr Hrr. exists rr. rewrite REGX. repeat split; auto. lia. }
split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB').
unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split. {  constructor.
- intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
- intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
- unfold st'. cbn. apply (tr_tick _ _ _ TR).
- intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
exact (AC rid sh o' v t Esh Hc).
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
split. { unfold st', ctx. cbn. destruct (tr_ctx _ _ _ TR) as (_&_&CC&_). unfold ctx in CC. rewrite CC.
pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
right. split; [lia|]. exists g3, b, r.
split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
- intros a Ha. do 2 right. left. apply FSA. exact Ha.
- intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.

End RC__1.
