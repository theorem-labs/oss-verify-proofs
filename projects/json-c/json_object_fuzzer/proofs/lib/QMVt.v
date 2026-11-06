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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation L_RET1 := (@QHB6.Mq0.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinvG := (@QHB6.Mq0.dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_R := (@QHB6.Mq0.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C38 := (@QHB6.Mq0.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@QHB6.Mq0.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@QHB6.Mq0.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinvG := unfold QHB6.Mq0.dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
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

Hypothesis HS_R : S_R.

Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; flia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma stdio_lim0 : forall f, sh_stdio (sh_lim0 f) = sh_stdio f.
Proof. clear. intros f. reflexivity. Qed.

#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof.
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.

#[using="Type"] Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_dn. destruct (df_dn_loop _ _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate].
destruct (df_final _ _ _ _ _ _ _ _ _ _); [|discriminate]. intros H. injection H as <- _. reflexivity.
Qed.
#[using="Type"] Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. clear. intros until y. unfold dfK_up. destruct (df_up_loop _ _) as [[rp2 a2 z2 e22 x2]|]; [|discriminate]. apply dfK_dn_f. Qed.
#[using="Type"] Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_al.
destruct (if nz (Z.rem rp 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|discriminate]. apply dfK_up_f.
Qed.
#[using="Type"] Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
Proof. clear. intros until y. unfold dfK_tz. destruct (df_tz_loop _ _ _); [|discriminate]. apply dfK_al_f. Qed.
#[using="Type"] Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_mid.
destruct (_ && _ && _)%Z; cbv beta iota zeta; [|apply dfK_tz_f].
destruct (rp =? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (rp <? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (_ || _); cbv beta iota. { intros H; injection H as <- _; reflexivity. }
apply dfK_tz_f.
Qed.
#[using="Type"] Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_pad. destruct (if nz j then _ else _) as [[k2 x2]|]; [|discriminate]. apply dfK_mid_f.
Qed.
#[using="Type"] Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_rng.
destruct (znth x 0 =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (_ && _ && _); [intros H; injection H as <- _; reflexivity|].
destruct (_ <? lrp)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (lrp <? _)%Z; [intros H; injection H as <- _; reflexivity|].
apply dfK_pad_f.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [flia|]. apply in_seq. flia.
Qed.
#[using="Type"] Lemma and33_iff : forall c, (-1 <= c < 256)%Z ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 = 69 <-> Z.lor c 32 = 101)%Z.
Proof.
clear. intros c Hc. destruct (Z.eq_dec c (-1)) as [->|Hne].
{ cbn. split; intros H; discriminate H. }
rewrite (land_W64_small c) by flia.
pose proof (forallb_range (fun c => Bool.eqb (Z.land c 18446744073709551583 =? 69) (Z.lor c 32 =? 101))%Z 256 ltac:(vm_compute; reflexivity) c ltac:(flia)) as E.
cbv beta in E. destruct (Z.eqb_spec (Z.land c 18446744073709551583) 69); destruct (Z.eqb_spec (Z.lor c 32) 101); cbn in E; try discriminate E; tauto.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3"] Lemma L_C48 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) b96 ev ws sign kmin c (f : shfile),
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> Fok Ft -> frm0 fct ->
fR = sh_lim0 f -> yR = f128_of_i32 0 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6b78) fct None m (seg_rom rsegs)).
Proof.
intros until f. intros DI RJ FOK FRM' HfR Hy. pose proof DI as DI0. dest_dfinv DI.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
pose proof FC as FC0. rewrite rf_cells_raw_eq in FC0.
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (f := f) (J := J);
[exact FC0 | exact (RFI_ok T txt p J _ _ _ RJ) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- HfR in FC2.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
zs. eapply L_RET1; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJ). all: flia.
Qed.

#[using="Hpok BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
Ltac eplia := unfold SCANEXP_DEPTH, zlength, got_ssp, ssp_guard in *; unfold hide2 in *; flia.
Ltac some_pair H := let E1 := fresh "Ef" in injection H as E1 H.

#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3 HS_R"] Lemma L_C38 : S_C38.
Proof.
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
unfold nz in HK.
destruct (Z.eqb_spec gotdig 0) as [Eg|Ng]; cbn [Z.b2z negb] in Hng, HK; subst ng.
-
some_pair HK.
zs. (brf K1; [ exfalso; lia | ]).
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
- pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. symmetry in Ef. subst f.
zs. (brf K1; [ | exfalso; lia ]).
stmt HS_R. eapply NX; try eassumption; try flia.
Qed.

#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG2 SG3 HS_R"] Lemma L_C2C : S_C2C.
Proof.
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst Hsn DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
rewrite (rf_unget_eq f Hsn) in HK, RJu.
ufc FC. rewrite Hsn in FC.
zs. zs. zs0.
pose proof L_C38 as NX. unfold QHB6.Mq0.S_C38 in NX. eapply NX with (f := mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)); try eassumption; try flia.
unfold QHB6.Mq0.dfinvG. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?Hsn; unfold M64; hyp_cells.
Qed.

#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_R"] Lemma L_E : S_E.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Rgr Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof DF as DF0. destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
site_facts FC RJ kmin c f.
unfold dfK_exp in HK. cbv beta iota zeta in HK.
set (lrp' := (if nz gotrad then lrp else dc)%Z) in HK.
assert (Rlrp' : (- 2^31 <= lrp' < 2^31)%Z) by (subst lrp'; destruct (nz gotrad); flia).

assert (GAC0 :
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69f0) fct None m (seg_rom rsegs))).
2:{ zs. zs. brf K1.
- replace lrp' with dc in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity.
- zs. replace lrp' with lrp in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia). reflexivity. }
clearbody lrp'.

assert (GC1C : forall (x11' x12' : word),
(nz gotdig && (Z.lor c 32 =? 101))%Z = false ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11' x12' x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6b4c) fct None m (seg_rom rsegs))).
{ intros x11' x12' Hne. rewrite Hne in HK.
assert (Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z).
{ clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; flia. }
zs. rewrite (Eng gotdig Rg). zs. brs K2.
-
replace (0 <=? c)%Z with false in HK by (symmetry; apply Z.leb_gt; flia).
pose proof L_C38 as NX. unfold QHB6.Mq0.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
- replace (0 <=? c)%Z with true in HK by (symmetry; apply Z.leb_le; flia).
pose proof FC as FC0. ufc FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
+
rewrite (rf_unget_nop f SN) in HK.
zs. zs. (brf K3; [ | exfalso; lia ]).
pose proof L_C38 as NX. unfold QHB6.Mq0.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
+ zs. zs. (brf K3; [ exfalso; lia | ]).
pose proof L_C2C as NX. unfold QHB6.Mq0.S_C2C in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity. }

zs. brf K2.
{  apply GC1C. unfold nz. replace (gotdig =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity. }
zs. zs. zs. brf K3.
{  apply GC1C. replace (Z.lor c 32 =? 101)%Z with false; [apply Bool.andb_false_r|].
symmetry. apply Z.eqb_neq. intros E. apply K3. apply (proj2 (and33_iff c ltac:(flia))). exact E. }
assert (He : Z.lor c 32 = 101%Z) by (apply (proj1 (and33_iff c ltac:(flia))); exact K3).
unfold nz in HK at 1. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).
rewrite He in HK. cbn [negb andb Z.eqb Pos.eqb] in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in He; discriminate He).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.

zs. zs. zs. zs.
callx (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | eplia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| replace (q + -8416 - 240)%Z with (q - 8656)%Z by flia; exact ST
| eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
match goal with H : stk _ ?m' (q + -8416 - 240)%Z _ |- _ => replace (q + -8416 - 240)%Z with (q - 8656)%Z in H by flia end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
pose proof RJ2 as RJ3. destruct RJ3 as (OK2 & Rc2 & CC2 & KM2 & NS2 & SS2). destruct OK2 as (Hbuf2 & Rl2 & Rr2 & Rc02 & Rn2 & Rst2).
assert (RR2 : (0 <= rf_rend T p true fS <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fS); unfold zlength in *; flia). unfold M64 in RR2.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
unfold nz in HK. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).

zs. zs. zs. brf K4; rewrite ?land_W64 in K4.
-
assert (Hne : e10 <> LLONG_MIN_).
{ intros E. apply K4. rewrite E. vm_compute. reflexivity. }
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. subst fS.
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + e10)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + e10)%Z); try eassumption; try flia. mk_dfinvG.
- assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear -K4 R; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; flia]).
rewrite Ee, Z.eqb_refl in HK.
zs. brf K5; rewrite ?land_W64 in K5.
+
assert (Ep : pok = 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
rewrite Ep in HK. cbn [Z.eqb negb] in HK. cbv beta iota in HK. some_pair HK.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
+ assert (Ep : pok <> 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
replace (pok =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Ep). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp _ _ fS RJ2 ltac:(flia)) as RJu.
pose proof FC2 as FC3. ufc FC3.
destruct (sh_shlim_neg fS) eqn:SN; unfold M64 in FC3.
*
rewrite (rf_unget_nop fS SN) in HK, Ef, RJu. subst fS.
zs. zs. (brf K6; [ | exfalso; lia ]). zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
* rewrite (rf_unget_eq fS SN) in HK, Ef, RJu.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs. zs1. zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
rewrite <- Ef in RJu, HK.
assert (Hst3 : sh_stdio fR = sh_stdio f0) by (rewrite Ef; cbn [sh_stdio]; exact Hst2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC4 : rw_cells rsegs mm Fp (rf_cells T p true fR J))
by (rewrite Ef; unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells) end.
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
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

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation Fok_trans10 := (@QHB6.Mq0.Fok_trans10 F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F2 := (@QHB6.Mq0.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F1 := (@QHB6.Mq0.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Hypothesis HS_F2 : S_F2.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F2"] Lemma L_F1 : S_F1.
Proof.
intros m; intros until e2. intros _ DI RJ Hk FOK FRM' Hsg He2 XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as Rz0l. pose proof (hi64_range zero0) as Rz0h.
assert (Rsg : (-1 <= sign <= 1)%Z) by lia.
unfold fin_K1 in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
replace (113 + e2 - -1074)%Z with (e2 + 1187)%Z in HK by lia. change (2 * 113)%Z with 226%Z in HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := Y) (Y := SF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y1 := f128_mul Y SF) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

assert (G74C : forall bits' m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x23' x24' x28' x29' x30' x31' : word) Ft' fct',
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft' -> frm0 fct' ->
(0 <= bits' <= 53)%Z ->
(let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1) in
let t := f128_of_d (bv_unsigned d) in
let bias := m_copysignl t Y1 in
let d0 := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits') in
let t0 := f128_of_d (bv_unsigned d0) in
match match m_fmodl Y1 t0 with
| Some frac => Some (f128_add (f128_sub Y1 frac) bias, frac, bias)
| None => None
end with
| Some (y, frac, bias) => fin_K2 sign 1024 a z x 4 bits' y frac bias e2
| None => None
end = Some yR) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y1)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y1)) x23' x24'
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') (Z_to_bv 64 53) x28' x29' x30' x31')
Ft' (Z_to_bv 64 0xd767c) fct' None m' (seg_rom rsegs))).
{ intros until fct'. intros DI2 FOK2 FRM2 Hb HK2. clear HK. dest_dfinv DI2. cbv zeta in HK2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). match goal with H : frm0 _ |- evt _ _ (MS _ _ _ ?f _ _ _) => idtac end; lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (225 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) with (scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) in HK2.
replace (226 - bits' - 1)%Z with (225 - bits')%Z in HK2 by lia. fold D1 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (TBv := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range TBv). pose proof (hi64_range TBv).
zs. zs. zs. callx (eapply copysignl_callE with (X := TBv) (Y := Y1); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl TBv Y1) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM4 end end. simpF.
set (D2 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) with D2 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D2); [eassumption | simpF; reflexivity]).
set (TFv := f128_of_d (bv_unsigned D2)) in *. pose proof (lo64_range TFv). pose proof (hi64_range TFv).
destruct (m_fmodl Y1 TFv) as [frac|] eqn:HFM; [|discriminate HK2]. cbv beta iota in HK2.
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := Y1) (Y := TFv) (r := frac); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK5 end.
pose proof (lo64_range frac). pose proof (hi64_range frac).
zs. zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply sub_callE with (X := Y1) (Y := frac); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_sub Y1 frac) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := Y2) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y3 := f128_add Y2 BI) in *. pose proof (lo64_range Y3). pose proof (hi64_range Y3).
zs. zs. zs.
stmt HS_F2. eapply NX; try eassumption; try lia; try mk_dfinv.
eapply Fok_trans10; [|exact FOK5]. fok. }
zs. zs. zs. zs. fixw.
match goal with |- context [Z_to_bv 64 (e2 + 113 + 1074)%Z] => replace (Z_to_bv 64 (e2 + 113 + 1074)%Z) with (Z_to_bv 64 (e2 + 1187)%Z) by (f_equal; lia) end.
zs. zs. zs. brs K1.
-
replace (e2 + 1187 <? 53)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. zs. rewrite clamp0_idiom by lia.
set (bits' := (if e2 + 1187 <? 0 then 0 else e2 + 1187)%Z) in *.
assert (Hb : (0 <= bits' < 53)%Z) by (subst bits'; destruct (Z.ltb_spec (e2 + 1187) 0); lia).
replace (bits' <? 113)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
- replace (e2 + 1187 <? 53)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). change (53 <? 113)%Z with true in HK. cbv beta iota in HK.
zs. zs.
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq0.Fok F).
Local Notation Fok_refl := (@QHB6.Mq0.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq0.Fok_set F).
Local Notation Fok_trans10 := (@QHB6.Mq0.Fok_trans10 F).
Local Notation fs_post := (@QHB6.Mq0.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq0.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F3 := (@QHB6.Mq0.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F2 := (@QHB6.Mq0.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_F3 : S_F3.

Ltac pickC := first [left; reflexivity | right; left; reflexivity | right; right; reflexivity].

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_8BC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR C_ONE) else Some FR
end
else Some FR) with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd77ec) fct None m (seg_rom rsegs)).
Proof.
intros until bits'. intros DI RJ Hk FOK FRM' Hsg He2 Hb HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
change LDBL_MANT_DIG_ with 113%Z in HK.
replace (2 <=? 113 - bits')%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv beta iota in HK.
destruct (m_fmodl FR (f128_of_i32 1)) as [rr|] eqn:HFM; [|discriminate HK].
zs. fixw2. zs. zs. (brf K1; [ exfalso; lia | ]); try (exfalso; mlia2).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 1)). pose proof (hi64_range (f128_of_i32 1)).
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := FR) (Y := f128_of_i32 1) (r := rr); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK1 end.
pose proof (lo64_range rr). pose proof (hi64_range rr).
zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range rr 0) as RLE.
zs. brf K2.
-
replace (f128_le rr 0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; mlia2).
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
- replace (f128_le rr 0 =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; mlia2).
zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (Y := C_ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_898 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 : word) Ft fct
j0 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z) (C : word),
dfinv m j0 (Z_to_bv 64 (lo64 FR)) w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
reg_get Ft 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(let FR' := f128_add FR (f128_of_d (bv_unsigned (fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))))) in
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR' one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR' C_ONE) else Some FR'
end
else Some FR') with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd77c8) fct None m (seg_rom rsegs)).
Proof.
intros until C. intros DI RJ Hk FOK FRM' Hsg He2 Hb HF10 HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
cbv zeta in HK.
set (DW := fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))) in *.
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned DW); [eassumption | rewrite HF10; reflexivity]).
set (E := f128_of_d (bv_unsigned DW)) in *. pose proof (lo64_range E). pose proof (hi64_range E).
zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := FR) (Y := E); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
eapply L_8BC; try eassumption; try lia. mk_dfinv.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_F2 : S_F2.
Proof.
intros m; intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
destruct XR as (LW' & LX & REL).
unfold fin_K2 in HK. change (Z.land (a + 4) MASK) with (Z.land (a + 4) 2047) in *. change (Z.land (a + 4 + 1) MASK) with (Z.land (a + 4 + 1) 2047) in HK.
pose proof (land_mask_range (a + 4) 2047 ltac:(lia)) as Rk. pose proof (land_mask_range (a + 5) 2047 ltac:(lia)) as Rk5.
replace (a + 4 + 1)%Z with (a + 5)%Z in HK by lia.
zs. zs. brf K1.
-
replace (Z.land (a + 4) 2047 =? z)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
set (k4 := Z.land (a + 4) 2047) in *.
specialize (Hin ltac:(lia)).
pose proof (X31H k4) as Rt. pose proof (REL k4 ltac:(lia) Hin) as E4.
pose proof (u32arr_read rsegs _ _ _ k4 _ _ XW (nth_error_wnth ws k4 ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k4 (znth x k4) (eq_sym E4) Rt).
set (t := znth x k4) in *.

assert (G898 : forall (C : word) m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x27' x28' x29' x30' x31' : word) Ft' fct' ev',
dfinv m' j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev' ws sign fR -> Fok Ft' -> frm0 fct' ->
reg_get Ft' 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(C = D_025 \/ C = D_05 \/ C = D_075) ->
(let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in
let od := if (t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)) then Some (fmul_d RNE D_025 signd)
else if 500000000 <? t then Some (fmul_d RNE D_075 signd)
else if t =? 500000000 then (if Z.land (a + 5) 2047 =? z then Some (fmul_d RNE D_05 signd) else Some (fmul_d RNE D_075 signd))
else None in
od = Some (fmul_d RNE C signd))%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27' x28' x29' x30' x31')
Ft' (Z_to_bv 64 0xd77c8) fct' None m' (seg_rom rsegs))).
{ intros until ev'. intros DI2 FOK2 FRM2 HF HC Hod. cbv zeta in Hod. rewrite Hod in HK. cbv beta iota in HK.
eapply L_898; [exact DI2 | exact RJ | exact Hk | exact FOK2 | exact FRM2 | exact Hsg | lia | lia | exact HF | cbv zeta; exact HK]. }
zs. zs. zs. zs. brf K2.
+
zs. zs. brf K3.
*
zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
*
zs. zs. zs. zs. zs. brf K4.
--
zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
-- zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
+ zs. brf K3.
*
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
unfold nz. replace (t =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
*
zs. zs. zs. brf K4.
--
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). unfold nz. cbn [negb orb andb].
destruct (t =? 0)%Z; reflexivity.
--
replace ((t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)))%Z with false in HK
by (unfold nz; replace (t =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia);
cbn [negb orb andb]; destruct (t <? 500000000)%Z; reflexivity).
replace (500000000 <? t)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. zs. zs.
eapply L_8BC; try eassumption; try lia; try mk_dfinv.
-
replace (Z.land (a + 4) 2047 =? z)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. zs. zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia; try mk_dfinv.
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
Local Notation L_RET1 := (@QHB6.Mq0.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_T := (@QHB6.Mq0.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD0 := (@QHB6.Mq0.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@QHB6.Mq0.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_M := (@QHB6.Mq0.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_T : S_T.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD0 : S_DD0.
Proof.
intros m; intros until Y. intros _ DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. call_split 80%Z (eapply mul_callE with (X := X) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD28 : forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6c58) fct None m (seg_rom rsegs)).
Proof.
intros until Y. intros DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. zs. zs. zs. zs.
pose proof L_DD0 as NX. unfold QHB6.Mq0.S_DD0 in NX. eapply NX; try eassumption.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD24 : S_DD24.
Proof.
intros m; intros until u. intros _ DI RJ Hk FOK FRM' Ru Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h.
zs. callx (eapply floatunsitf_callv with (u := u); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
eapply L_DD28; try eassumption; try mk_dfinv.
Qed.

Ltac pose_rd0 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with XW2 : u32arr rsegs mm _ ?wsx |- _ =>
let R := fresh "RD" in
pose proof (u32arr_read rsegs _ _ _ 0%Z _ _ XW2 (nth_error_wnth wsx 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as R;
replace (XA + 4 * 0)%Z with XA in R by lia end end.
#[using="Type"] Lemma p10s_lit : forall j, (0 <= j <= 7)%Z -> (0 <= znth p10s j < 2^31)%Z.
Proof. clear. intros j Hj. destruct (p10s_range j Hj) as [R _]. lia. Qed.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_T"] Lemma L_M : S_M.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rlnz Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_mid in HK.
assert (Kin0 : inring 0 kz 0) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) Kin0) as Et0.
set (x0 := znth x 0) in *.

zs. fixw3. fixw. try replace (lnz + 0)%Z with lnz by lia.
zs. zs. brs K1.
{
replace (lnz <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. brs K2.
{
replace (rp <? 18)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r in HK. cbv iota in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (rp <? 18)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. fixw3. fixw. try replace (rp + 0)%Z with rp by lia.
zs. brs K3.
{
replace (lnz <=? rp)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <=? rp)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbn [andb] in HK.

pose proof (u32arr_read rsegs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. zs. brf K4.
-
replace (rp =? 9)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
zs. zs. brs K5.
+
assert (Rrp2 : (10 <= rp <= 17)%Z) by lia.
replace (rp <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite (Z.shiftl_mul_pow2 rp 1) by lia. change (2^1)%Z with 2%Z.
zs. zs. fixw3. fixw.
zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0).
zs. fixw3. fixw. zs. fixw3. fixw.
match goal with |- context [Z_to_bv 64 (?e + 27)%Z] => replace (e + 27)%Z with (53 - 3 * (rp - 9))%Z by lia end.
set (bitlim := (53 - 3 * (rp - 9))%Z) in *.

assert (G94 : forall (x10' : word), yR = f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10' (Z_to_bv 64 30) x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
(Z_to_bv 64 8) x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd79c4) fct None m (seg_rom rsegs))).
{ intros x10' Hy. clear HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. rewrite (Z.shiftl_mul_pow2 (rp + -10)) by lia. change (2^2)%Z with 4%Z. zs. zs.

assert (G_DC : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt rsegs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (rp - 10))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 0xd7a0c) fct None m2 (seg_rom rsegs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (rp - 10)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
zs. eapply L_DD28; try eassumption; try mk_dfinv. }
assert (Hc : (rp = 10 \/ rp = 11 \/ rp = 12 \/ rp = 13 \/ rp = 14 \/ rp = 15 \/ rp = 16 \/ rp = 17)%Z) by lia.
clear Hy. clearbody bitlim.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_DC; mk_dfinv). }
zs. zs. brs K6.
*
replace (30 <? bitlim)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
* replace (30 <? bitlim)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite srlw_small by lia.
assert (Rs0 : (0 <= Z.shiftr x0 bitlim)%Z) by (apply Z.shiftr_nonneg; lia).
assert (Rs1 : (Z.shiftr x0 bitlim <= x0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]; assert (1 <= 2 ^ bitlim)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia); nia).
zs. brf K7.
--
replace (Z.shiftr x0 bitlim =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
-- replace (Z.shiftr x0 bitlim =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
assert (Rrp1 : (1 <= rp <= 8)%Z) by lia.
replace (rp <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK. rename HK into HyR.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs.
zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. zs. try rewrite zext32_small by lia. try (rewrite (Z.shiftl_mul_pow2 (8 - rp)) by lia; change (2^2)%Z with 4%Z). zs. zs.

assert (G_E4 : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt rsegs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (8 - rp))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 0xd6f14) fct None m2 (seg_rom rsegs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (8 - rp)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
set (PF := f128_of_i32 (znth p10s (8 - rp))) in *. pose proof (lo64_range PF) as R4l. pose proof (hi64_range PF) as R4h.
zs. zs. zs. zs.
zs. call_split 112%Z (eapply div_callE with (X := P) (Y := PF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL. }
assert (Hc : (rp = 1 \/ rp = 2 \/ rp = 3 \/ rp = 4 \/ rp = 5 \/ rp = 6 \/ rp = 7 \/ rp = 8)%Z) by lia.
clear HyR.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_E4; mk_dfinv).
-
replace (rp =? 9)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs. zs.
pose proof L_DD24 as NX. unfold QHB6.Mq0.S_DD24 in NX. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation L_RET1 := (@QHB6.Mq3.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinvG := (@QHB6.Mq3.dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_R := (@QHB6.Mq3.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C38 := (@QHB6.Mq3.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_C2C := (@QHB6.Mq3.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_E := (@QHB6.Mq3.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_dfinvG := unfold QHB6.Mq3.dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
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

Hypothesis HS_R : S_R.

Ltac ufc FC := unfold rf_cells, rf_rend in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac site_facts FC RJ k c f :=
pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; flia); unfold M64 in RR;
pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
#[using="Type"] Lemma stdio_lim0 : forall f, sh_stdio (sh_lim0 f) = sh_stdio f.
Proof. clear. intros f. reflexivity. Qed.

#[using="Type"] Lemma RFJ_lim0 : forall kmin c f, RFJ' kmin c f -> RFJ' 0 c (sh_lim0 f).
Proof.
clear. intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold RFJ, sh_ok, sh_lim0; cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
split. { split; [exact Hbuf|]. split; [exact Rl|]. split; [exact Rr|]. split; [flia|]. split; [exact Rn | exact Rst]. }
split; [exact Rc|]. split; [flia|]. split; [intros _; flia|]. split.
- intros E. destruct (NS E) as (N1 & N2 & N3). split; [reflexivity|]. split; [exact N2 | exact N3].
- intros E. destruct (SS E) as (N1 & N2 & N3 & N4 & N5). split; [exact N1|]. split; [exact N2|]. split; [intros X; discriminate X|]. split; [intros X; discriminate X | exact N5].
Qed.

#[using="Type"] Lemma dfK_dn_f : forall sg f rp a z e2 x f' y, dfK_dn 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_dn. destruct (df_dn_loop _ _) as [[rp2 a2 z2 e22 x2 i2]|]; [|discriminate].
destruct (df_final _ _ _ _ _ _ _ _ _ _); [|discriminate]. intros H. injection H as <- _. reflexivity.
Qed.
#[using="Type"] Lemma dfK_up_f : forall sg f rp a z e2 x f' y, dfK_up 53 (-1074) sg f rp a z e2 x = Some (f', y) -> f' = f.
Proof. clear. intros until y. unfold dfK_up. destruct (df_up_loop _ _) as [[rp2 a2 z2 e22 x2]|]; [|discriminate]. apply dfK_dn_f. Qed.
#[using="Type"] Lemma dfK_al_f : forall sg f rp z x f' y, dfK_al 53 (-1074) sg f rp z x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_al.
destruct (if nz (Z.rem rp 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|discriminate]. apply dfK_up_f.
Qed.
#[using="Type"] Lemma dfK_tz_f : forall sg f rp k x f' y, dfK_tz 53 (-1074) sg f rp k x = Some (f', y) -> f' = f.
Proof. clear. intros until y. unfold dfK_tz. destruct (df_tz_loop _ _ _); [|discriminate]. apply dfK_al_f. Qed.
#[using="Type"] Lemma dfK_mid_f : forall sg f rp lnz k x f' y, dfK_mid 53 (-1074) sg f rp lnz k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_mid.
destruct (_ && _ && _)%Z; cbv beta iota zeta; [|apply dfK_tz_f].
destruct (rp =? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (rp <? 9)%Z; cbv beta iota. { intros H; injection H as <- _; reflexivity. }
destruct (_ || _); cbv beta iota. { intros H; injection H as <- _; reflexivity. }
apply dfK_tz_f.
Qed.
#[using="Type"] Lemma dfK_pad_f : forall sg f lrp lnz j k x f' y, dfK_pad 53 (-1074) sg f lrp lnz j k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_pad. destruct (if nz j then _ else _) as [[k2 x2]|]; [|discriminate]. apply dfK_mid_f.
Qed.
#[using="Type"] Lemma dfK_rng_f : forall sg f lrp dc lnz j k x f' y, dfK_rng 53 (-1074) sg f lrp dc lnz j k x = Some (f', y) -> f' = f.
Proof.
clear. intros until y. unfold dfK_rng.
destruct (znth x 0 =? 0)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (_ && _ && _); [intros H; injection H as <- _; reflexivity|].
destruct (_ <? lrp)%Z; [intros H; injection H as <- _; reflexivity|].
destruct (lrp <? _)%Z; [intros H; injection H as <- _; reflexivity|].
apply dfK_pad_f.
Qed.

#[using="Type"] Lemma forallb_range : forall (P : Z -> bool) n, forallb P (map Z.of_nat (seq 0 n)) = true -> forall c, (0 <= c < Z.of_nat n)%Z -> P c = true.
Proof.
clear. intros P n H c Hc. apply (proj1 (forallb_forall P _) H). apply in_map_iff. exists (Z.to_nat c). split; [flia|]. apply in_seq. flia.
Qed.
#[using="Type"] Lemma and33_iff : forall c, (-1 <= c < 256)%Z ->
(Z.land (Z.land c 18446744073709551615) 18446744073709551583 = 69 <-> Z.lor c 32 = 101)%Z.
Proof.
clear. intros c Hc. destruct (Z.eq_dec c (-1)) as [->|Hne].
{ cbn. split; intros H; discriminate H. }
rewrite (land_W64_small c) by flia.
pose proof (forallb_range (fun c => Bool.eqb (Z.land c 18446744073709551583 =? 69) (Z.lor c 32 =? 101))%Z 256 ltac:(vm_compute; reflexivity) c ltac:(flia)) as E.
cbv beta in E. destruct (Z.eqb_spec (Z.land c 18446744073709551583) 69); destruct (Z.eqb_spec (Z.lor c 32) 101); cbn in E; try discriminate E; tauto.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3"] Lemma L_C48 : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) b96 ev ws sign kmin c (f : shfile),
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> Fok Ft -> frm0 fct ->
fR = sh_lim0 f -> yR = f128_of_i32 0 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd923c) fct None m (seg_rom usegs)).
Proof.
intros until f. intros DI RJ FOK FRM' HfR Hy. pose proof DI as DI0. dest_dfinv DI.
site_facts FC RJ kmin c f.
assert (L0 : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat).
{ destruct FC as [[Hwf _] _]. cbn in Hwf. tauto. }
destruct L0 as [L0 L1].
pose proof FC as FC0. rewrite rf_cells_raw_eq in FC0.
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (f := f) (J := J);
[exact FC0 | exact (RFI_ok T txt p J _ _ _ RJ) | exact L0 | exact L1 | flia | flia | unfold zlength in *; flia | assumption]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- HfR in FC2.
zs. zs. callx (eapply floatsitf_callp; [eassumption | flia]).
zs. eapply L_RET1; try eassumption; try flia; try mk_finv; try mk_framL.
all: try (rewrite HfR; eapply RFJ_lim0; exact RJ). all: flia.
Qed.

#[using="Hpok BYT Hp Hnul T0 T1 SEP SPF2 SG2 SG3"] Lemma scanexp_callE : forall (ra' : word) (q' : Z) (gp' tp' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
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
Ltac eplia := unfold SCANEXP_DEPTH, zlength, got_ssp, ssp_guard in *; unfold hide2 in *; flia.
Ltac some_pair H := let E1 := fresh "Ef" in injection H as E1 H.

#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPF SPT SG1 SG2 SG3 HS_R"] Lemma L_C38 : S_C38.
Proof.
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
unfold nz in HK.
destruct (Z.eqb_spec gotdig 0) as [Eg|Ng]; cbn [Z.b2z negb] in Hng, HK; subst ng.
-
some_pair HK.
zs. (brf K1; [ exfalso; lia | ]).
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
- pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. symmetry in Ef. subst f.
zs. (brf K1; [ | exfalso; lia ]).
stmt HS_R. eapply NX; try eassumption; try flia.
Qed.

#[using="Hpok Hp HP30 T0 T1 SEP SE_T SPF SPF2 SPT SG1 SG2 SG3 HS_R"] Lemma L_C2C : S_C2C.
Proof.
intros m; intros until ng. intros _ DI RJ Hk FOK FRM' Hsg Hst Hsn DF Hw80 Rg Hng Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
site_facts FC RJ kmin c f.
pose proof (RFI_unget T txt p J Hp kmin c f RJ ltac:(flia)) as RJu.
rewrite (rf_unget_eq f Hsn) in HK, RJu.
ufc FC. rewrite Hsn in FC.
zs. zs. zs0.
pose proof L_C38 as NX. unfold QHB6.Mq3.S_C38 in NX. eapply NX with (f := mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)); try eassumption; try flia.
unfold QHB6.Mq3.dfinvG. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?Hsn; unfold M64; hyp_cells.
Qed.

#[using="Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_R"] Lemma L_E : S_E.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst DF Hw80 Rg Rgr Rlrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof DF as DF0. destruct DF as (XR & X31H & Rj & Rk & Rdc & Rlnz & Hlnz & Hxk & Hkj & Hkj45).
site_facts FC RJ kmin c f.
unfold dfK_exp in HK. cbv beta iota zeta in HK.
set (lrp' := (if nz gotrad then lrp else dc)%Z) in HK.
assert (Rlrp' : (- 2^31 <= lrp' < 2^31)%Z) by (subst lrp'; destruct (nz gotrad); flia).

assert (GAC0 :
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd90b4) fct None m (seg_rom usegs))).
2:{ zs. zs. brf K1.
- replace lrp' with dc in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity.
- zs. replace lrp' with lrp in GAC0; [exact GAC0|]. subst lrp'. unfold nz. replace (gotrad =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia). reflexivity. }
clearbody lrp'.

assert (GC1C : forall (x11' x12' : word),
(nz gotdig && (Z.lor c 32 =? 101))%Z = false ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11' x12' x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp') (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9210) fct None m (seg_rom usegs))).
{ intros x11' x12' Hne. rewrite Hne in HK.
assert (Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z).
{ clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; flia. }
zs. rewrite (Eng gotdig Rg). zs. brs K2.
-
replace (0 <=? c)%Z with false in HK by (symmetry; apply Z.leb_gt; flia).
pose proof L_C38 as NX. unfold QHB6.Mq3.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
- replace (0 <=? c)%Z with true in HK by (symmetry; apply Z.leb_le; flia).
pose proof FC as FC0. ufc FC.
destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
+
rewrite (rf_unget_nop f SN) in HK.
zs. zs. (brf K3; [ | exfalso; lia ]).
pose proof L_C38 as NX. unfold QHB6.Mq3.S_C38 in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity.
+ zs. zs. (brf K3; [ exfalso; lia | ]).
pose proof L_C2C as NX. unfold QHB6.Mq3.S_C2C in NX. eapply NX with (gotdig := gotdig); try eassumption; try flia; try reflexivity. }

zs. brf K2.
{  apply GC1C. unfold nz. replace (gotdig =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia). reflexivity. }
zs. zs. zs. brf K3.
{  apply GC1C. replace (Z.lor c 32 =? 101)%Z with false; [apply Bool.andb_false_r|].
symmetry. apply Z.eqb_neq. intros E. apply K3. apply (proj2 (and33_iff c ltac:(flia))). exact E. }
assert (He : Z.lor c 32 = 101%Z) by (apply (proj1 (and33_iff c ltac:(flia))); exact K3).
unfold nz in HK at 1. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).
rewrite He in HK. cbn [negb andb Z.eqb Pos.eqb] in HK.
destruct (scanexp fuelc f pok) as [[fS e10]|] eqn:HSX; [|discriminate HK].
assert (Hc0 : c <> 0%Z) by (intros E0; rewrite E0 in He; discriminate He).
pose proof (scanexp_bound fuelc f pok fS e10 ltac:(rewrite Hbuf; exact BYT) HSX) as Re10.

zs. zs. zs. zs.
callx (eapply scanexp_callE with (f := f) (kmin := kmin) (c := c) (fS := fS) (e10 := e10);
[ exact HSX | exact FC | exact RJ | eplia | exact Hc0 | intros E; apply ST0; rewrite <- Hst; exact E | exact BY | exact (conj SSP1 SSP2)
| replace (q + -8416 - 240)%Z with (q - 8656)%Z by flia; exact ST
| eplia | eplia | eplia | eplia | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ ?k ?c fS |- _ => rename H into RJ2 end.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
match goal with H : stk _ ?m' (q + -8416 - 240)%Z _ |- _ => replace (q + -8416 - 240)%Z with (q - 8656)%Z in H by flia end.
match goal with H : (1 <= ?k)%Z, H2 : RFJ _ _ _ _ _ ?k _ fS |- _ => rename H into Hk2 end.
pose proof RJ2 as RJ3. destruct RJ3 as (OK2 & Rc2 & CC2 & KM2 & NS2 & SS2). destruct OK2 as (Hbuf2 & Rl2 & Rr2 & Rc02 & Rn2 & Rst2).
assert (RR2 : (0 <= rf_rend T p true fS <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fS); unfold zlength in *; flia). unfold M64 in RR2.
assert (Hst2 : sh_stdio fS = sh_stdio f0) by (rewrite <- Hst; exact (proj1 (scanexp_stdio _ _ _ _ _ HSX))).
unfold nz in HK. replace (gotdig =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; flia).

zs. zs. zs. brf K4; rewrite ?land_W64 in K4.
-
assert (Hne : e10 <> LLONG_MIN_).
{ intros E. apply K4. rewrite E. vm_compute. reflexivity. }
replace (e10 =? LLONG_MIN_)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Hne). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef. subst fS.
assert (Re : (-2^60 <= e10 <= 2^60)%Z) by (destruct Re10 as [E|R]; [exfalso; exact (Hne E) | exact R]).
zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + e10)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + e10)%Z); try eassumption; try flia. mk_dfinvG.
- assert (Ee : e10 = LLONG_MIN_) by (destruct Re10 as [E|R]; [exact E | exfalso; clear -K4 R; unfold LLONG_MIN_ in *; Z.div_mod_to_equations; flia]).
rewrite Ee, Z.eqb_refl in HK.
zs. brf K5; rewrite ?land_W64 in K5.
+
assert (Ep : pok = 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
rewrite Ep in HK. cbn [Z.eqb negb] in HK. cbv beta iota in HK. some_pair HK.
eapply L_C48; try eassumption; try (symmetry; assumption). mk_dfinvG.
+ assert (Ep : pok <> 0%Z) by (clear -K5 Hpok; unfold hide2 in *; mlia).
replace (pok =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; exact Ep). cbn [negb] in HK. cbv beta iota in HK.
pose proof (dfK_rng_f _ _ _ _ _ _ _ _ _ _ HK) as Ef.
pose proof (RFI_unget T txt p J Hp _ _ fS RJ2 ltac:(flia)) as RJu.
pose proof FC2 as FC3. ufc FC3.
destruct (sh_shlim_neg fS) eqn:SN; unfold M64 in FC3.
*
rewrite (rf_unget_nop fS SN) in HK, Ef, RJu. subst fS.
zs. zs. (brf K6; [ | exfalso; lia ]). zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
* rewrite (rf_unget_eq fS SN) in HK, Ef, RJu.
zs. zs. (brf K6; [ exfalso; lia | ]). zs. zs. zs. zs1. zs. zs.
let v := getreg 23%Z in replace v with (Z_to_bv 64 (lrp' + 0)%Z) by (apply Z_to_bv_eqm; rewrite ?land_W64; Z.div_mod_to_equations; flia).
rewrite <- Ef in RJu, HK.
assert (Hst3 : sh_stdio fR = sh_stdio f0) by (rewrite Ef; cbn [sh_stdio]; exact Hst2).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (FC4 : rw_cells usegs mm Fp (rf_cells T p true fR J))
by (rewrite Ef; unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells) end.
stmt HS_R. eapply NX with (lrp := (lrp' + 0)%Z); try eassumption; try flia. mk_dfinvG.
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation Fok_trans10 := (@QHB6.Mq3.Fok_trans10 F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F2 := (@QHB6.Mq3.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F1 := (@QHB6.Mq3.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
Notation POST := (fs_post m0).

Hypothesis HS_F2 : S_F2.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F2"] Lemma L_F1 : S_F1.
Proof.
intros m; intros until e2. intros _ DI RJ Hk FOK FRM' Hsg He2 XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range zero0) as Rz0l. pose proof (hi64_range zero0) as Rz0h.
assert (Rsg : (-1 <= sign <= 1)%Z) by lia.
unfold fin_K1 in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
replace (113 + e2 - -1074)%Z with (e2 + 1187)%Z in HK by lia. change (2 * 113)%Z with 226%Z in HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF). pose proof (hi64_range SF).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (X := Y) (Y := SF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y1 := f128_mul Y SF) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

assert (G74C : forall bits' m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x23' x24' x28' x29' x30' x31' : word) Ft' fct',
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft' -> frm0 fct' ->
(0 <= bits' <= 53)%Z ->
(let d := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1) in
let t := f128_of_d (bv_unsigned d) in
let bias := m_copysignl t Y1 in
let d0 := m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits') in
let t0 := f128_of_d (bv_unsigned d0) in
match match m_fmodl Y1 t0 with
| Some frac => Some (f128_add (f128_sub Y1 frac) bias, frac, bias)
| None => None
end with
| Some (y, frac, bias) => fin_K2 sign 1024 a z x 4 bits' y frac bias e2
| None => None
end = Some yR) ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10' x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y1)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y1)) x23' x24'
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') (Z_to_bv 64 53) x28' x29' x30' x31')
Ft' (Z_to_bv 64 0xd9d40) fct' None m' (seg_rom usegs))).
{ intros until fct'. intros DI2 FOK2 FRM2 Hb HK2. clear HK. dest_dfinv DI2. cbv zeta in HK2.
zs. zs. zs. (brf K3; [ exfalso; lia | ]).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). match goal with H : frm0 _ |- evt _ _ (MS _ _ _ ?f _ _ _) => idtac end; lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM3 end end. simpF.
set (D1 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (225 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) with (scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (226 - bits' - 1)) in HK2.
replace (226 - bits' - 1)%Z with (225 - bits')%Z in HK2 by lia. fold D1 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D1); [eassumption | simpF; reflexivity]).
set (TBv := f128_of_d (bv_unsigned D1)) in *. pose proof (lo64_range TBv). pose proof (hi64_range TBv).
zs. zs. zs. callx (eapply copysignl_callE with (X := TBv) (Y := Y1); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
set (BI := m_copysignl TBv Y1) in *. pose proof (lo64_range BI). pose proof (hi64_range BI).
zs. zs. zs. zs. fixw2. zs. simpF.
zs. callx (eapply scalbn_callE; [eassumption | eassumption | lia]). lazymatch goal with |- evt _ _ (MS _ _ _ ?f _ _ _) => match goal with H : frm0 f |- _ => rename H into FRM4 end end. simpF.
set (D2 := scalbn_model (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) in *.
change (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) (113 - bits')) with D2 in HK2.
zs. callx (eapply extenddftf2_callF with (D := bv_unsigned D2); [eassumption | simpF; reflexivity]).
set (TFv := f128_of_d (bv_unsigned D2)) in *. pose proof (lo64_range TFv). pose proof (hi64_range TFv).
destruct (m_fmodl Y1 TFv) as [frac|] eqn:HFM; [|discriminate HK2]. cbv beta iota in HK2.
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := Y1) (Y := TFv) (r := frac); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK5 end.
pose proof (lo64_range frac). pose proof (hi64_range frac).
zs. zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply sub_callE with (X := Y1) (Y := frac); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y2 := f128_sub Y1 frac) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := Y2) (Y := BI); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (Y3 := f128_add Y2 BI) in *. pose proof (lo64_range Y3). pose proof (hi64_range Y3).
zs. zs. zs.
stmt HS_F2. eapply NX; try eassumption; try lia; try mk_dfinv.
eapply Fok_trans10; [|exact FOK5]. fok. }
zs. zs. zs. zs. fixw.
match goal with |- context [Z_to_bv 64 (e2 + 113 + 1074)%Z] => replace (Z_to_bv 64 (e2 + 113 + 1074)%Z) with (Z_to_bv 64 (e2 + 1187)%Z) by (f_equal; lia) end.
zs. zs. zs. brs K1.
-
replace (e2 + 1187 <? 53)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. zs. rewrite clamp0_idiom by lia.
set (bits' := (if e2 + 1187 <? 0 then 0 else e2 + 1187)%Z) in *.
assert (Hb : (0 <= bits' < 53)%Z) by (subst bits'; destruct (Z.ltb_spec (e2 + 1187) 0); lia).
replace (bits' <? 113)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
- replace (e2 + 1187 <? 53)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). change (53 <? 113)%Z with true in HK. cbv beta iota in HK.
zs. zs.
eapply G74C; try eassumption; try lia; try mk_dfinv; try (cbv zeta; exact HK).
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

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation Fok_trans10 := (@QHB6.Mq3.Fok_trans10 F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F3 := (@QHB6.Mq3.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_F2 := (@QHB6.Mq3.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_F3 : S_F3.

Ltac pickC := first [left; reflexivity | right; left; reflexivity | right; right; reflexivity].

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_8BC : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR C_ONE) else Some FR
end
else Some FR) with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9eb0) fct None m (seg_rom usegs)).
Proof.
intros until bits'. intros DI RJ Hk FOK FRM' Hsg He2 Hb HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
change LDBL_MANT_DIG_ with 113%Z in HK.
replace (2 <=? 113 - bits')%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbv beta iota in HK.
destruct (m_fmodl FR (f128_of_i32 1)) as [rr|] eqn:HFM; [|discriminate HK].
zs. fixw2. zs. zs. (brf K1; [ exfalso; lia | ]); try (exfalso; mlia2).
zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 1)). pose proof (hi64_range (f128_of_i32 1)).
zs. zs. zs. zs. zs.
callx (eapply fmodl_callE with (X := FR) (Y := f128_of_i32 1) (r := rr); [eassumption | eassumption | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | exact HFM]).
match goal with H : forall k : bv 5, _ -> reg_get _ k = reg_get _ k |- _ => rename H into FOK1 end.
pose proof (lo64_range rr). pose proof (hi64_range rr).
zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range rr 0) as RLE.
zs. brf K2.
-
replace (f128_le rr 0 =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; mlia2).
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
- replace (f128_le rr 0 =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; mlia2).
zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (Y := C_ONE); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia. mk_dfinv. eapply Fok_trans10; eassumption.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_898 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x27 x28 x29 x30 x31 : word) Ft fct
j0 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z) (C : word),
dfinv m j0 (Z_to_bv 64 (lo64 FR)) w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
reg_get Ft 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(let FR' := f128_add FR (f128_of_d (bv_unsigned (fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))))) in
match (if 2 <=? LDBL_MANT_DIG_ - bits' then
let one := f128_of_i32 1 in
match m_fmodl FR' one with
| None => None
| Some rr => if f128_le rr 0 =? 0 then Some (f128_add FR' C_ONE) else Some FR'
end
else Some FR') with
| None => None
| Some frac => fin_K3 1024 Y frac BI e2
end = Some yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9e8c) fct None m (seg_rom usegs)).
Proof.
intros until C. intros DI RJ Hk FOK FRM' Hsg He2 Hb HF10 HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
cbv zeta in HK.
set (DW := fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign))) in *.
zs. zs. callx (eapply extenddftf2_callF with (D := bv_unsigned DW); [eassumption | rewrite HF10; reflexivity]).
set (E := f128_of_d (bv_unsigned DW)) in *. pose proof (lo64_range E). pose proof (hi64_range E).
zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE with (X := FR) (Y := E); [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs.
eapply L_8BC; try eassumption; try lia. mk_dfinv.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1 HS_F3"] Lemma L_F2 : S_F2.
Proof.
intros m; intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb XR X31H Ra Rz Hin HK. pose proof DI as DI0. dest_dfinv DI.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
destruct XR as (LW' & LX & REL).
unfold fin_K2 in HK. change (Z.land (a + 4) MASK) with (Z.land (a + 4) 2047) in *. change (Z.land (a + 4 + 1) MASK) with (Z.land (a + 4 + 1) 2047) in HK.
pose proof (land_mask_range (a + 4) 2047 ltac:(lia)) as Rk. pose proof (land_mask_range (a + 5) 2047 ltac:(lia)) as Rk5.
replace (a + 4 + 1)%Z with (a + 5)%Z in HK by lia.
zs. zs. brf K1.
-
replace (Z.land (a + 4) 2047 =? z)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
set (k4 := Z.land (a + 4) 2047) in *.
specialize (Hin ltac:(lia)).
pose proof (X31H k4) as Rt. pose proof (REL k4 ltac:(lia) Hin) as E4.
pose proof (u32arr_read usegs _ _ _ k4 _ _ XW (nth_error_wnth ws k4 ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
zs. zs. zs. fix_idx. zs. rewrite (sx32_wval ws k4 (znth x k4) (eq_sym E4) Rt).
set (t := znth x k4) in *.

assert (G898 : forall (C : word) m' (x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x27' x28' x29' x30' x31' : word) Ft' fct' ev',
dfinv m' j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev' ws sign fR -> Fok Ft' -> frm0 fct' ->
reg_get Ft' 10 = fmul_d RNE C (fcvt_d_w RNE (Z_to_bv 64 sign)) ->
(C = D_025 \/ C = D_05 \/ C = D_075) ->
(let signd := fcvt_d_w RNE (Z_to_bv 64 sign) in
let od := if (t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)) then Some (fmul_d RNE D_025 signd)
else if 500000000 <? t then Some (fmul_d RNE D_075 signd)
else if t =? 500000000 then (if Z.land (a + 5) 2047 =? z then Some (fmul_d RNE D_05 signd) else Some (fmul_d RNE D_075 signd))
else None in
od = Some (fmul_d RNE C signd))%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27' x28' x29' x30' x31')
Ft' (Z_to_bv 64 0xd9e8c) fct' None m' (seg_rom usegs))).
{ intros until ev'. intros DI2 FOK2 FRM2 HF HC Hod. cbv zeta in Hod. rewrite Hod in HK. cbv beta iota in HK.
eapply L_898; [exact DI2 | exact RJ | exact Hk | exact FOK2 | exact FRM2 | exact Hsg | lia | lia | exact HF | cbv zeta; exact HK]. }
zs. zs. zs. zs. brf K2.
+
zs. zs. brf K3.
*
zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
*
zs. zs. zs. zs. zs. brf K4.
--
zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
-- zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (500000000 <? t)%Z with false by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with true by (symmetry; apply Z.eqb_eq; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
+ zs. brf K3.
*
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
unfold nz. replace (t =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
*
zs. zs. zs. brf K4.
--
zs. zs. zs. zs. zs. zs. zs.
eapply G898; [mk_dfinv | fok | assumption | rewrite freg_get_same by (vm_compute; reflexivity); reflexivity | pickC | ].
cbv zeta. replace (t <? 500000000)%Z with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z.land (a + 5) 2047 =? z)%Z with false by (symmetry; apply Z.eqb_neq; lia). unfold nz. cbn [negb orb andb].
destruct (t =? 0)%Z; reflexivity.
--
replace ((t <? 500000000) && (nz t || negb (Z.land (a + 5) 2047 =? z)))%Z with false in HK
by (unfold nz; replace (t =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); replace (Z.land (a + 5) 2047 =? z)%Z with true by (symmetry; apply Z.eqb_eq; lia);
cbn [negb orb andb]; destruct (t <? 500000000)%Z; reflexivity).
replace (500000000 <? t)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
replace (t =? 500000000)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HK.
zs. zs. zs.
eapply L_8BC; try eassumption; try lia; try mk_dfinv.
-
replace (Z.land (a + 4) 2047 =? z)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbv beta iota zeta in HK.
zs. zs. zs. zs.
stmt HS_F3. eapply NX; try eassumption; try lia; try mk_dfinv.
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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation L_RET1 := (@QHB6.Mq3.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_T := (@QHB6.Mq3.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD0 := (@QHB6.Mq3.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_DD24 := (@QHB6.Mq3.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_M := (@QHB6.Mq3.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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

Hypothesis HS_T : S_T.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD0 : S_DD0.
Proof.
intros m; intros until Y. intros _ DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. call_split 80%Z (eapply mul_callE with (X := X) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD28 : forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd931c) fct None m (seg_rom usegs)).
Proof.
intros until Y. intros DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
zs. zs. zs. zs. zs.
pose proof L_DD0 as NX. unfold QHB6.Mq3.S_DD0 in NX. eapply NX; try eassumption.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_DD24 : S_DD24.
Proof.
intros m; intros until u. intros _ DI RJ Hk FOK FRM' Ru Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h.
zs. callx (eapply floatunsitf_callv with (u := u); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
eapply L_DD28; try eassumption; try mk_dfinv.
Qed.

Ltac pose_rd0 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with XW2 : u32arr usegs mm _ ?wsx |- _ =>
let R := fresh "RD" in
pose proof (u32arr_read usegs _ _ _ 0%Z _ _ XW2 (nth_error_wnth wsx 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as R;
replace (XA + 4 * 0)%Z with XA in R by lia end end.
#[using="Type"] Lemma p10s_lit : forall j, (0 <= j <= 7)%Z -> (0 <= znth p10s j < 2^31)%Z.
Proof. clear. intros j Hj. destruct (p10s_range j Hj) as [R _]. lia. Qed.

#[using="Hp T1 SE_T SPLO SPF SPF2 SPT SG1 SG3 Q1 HS_T"] Lemma L_M : S_M.
Proof.
intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rlnz Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
destruct XR as (LW' & LX & REL).
unfold dfK_mid in HK.
assert (Kin0 : inring 0 kz 0) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) Kin0) as Et0.
set (x0 := znth x 0) in *.

zs. fixw3. fixw. try replace (lnz + 0)%Z with lnz by lia.
zs. zs. brs K1.
{
replace (lnz <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. zs. brs K2.
{
replace (rp <? 18)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r in HK. cbv iota in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (rp <? 18)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
zs. fixw3. fixw. try replace (rp + 0)%Z with rp by lia.
zs. brs K3.
{
replace (lnz <=? rp)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). cbn [andb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)). }
replace (lnz <=? rp)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbn [andb] in HK.

pose proof (u32arr_read usegs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
replace (XA + 4 * 0)%Z with XA in RD0 by lia.
zs. zs. brf K4.
-
replace (rp =? 9)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
zs. zs. brs K5.
+
assert (Rrp2 : (10 <= rp <= 17)%Z) by lia.
replace (rp <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite (Z.shiftl_mul_pow2 rp 1) by lia. change (2^1)%Z with 2%Z.
zs. zs. fixw3. fixw.
zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0).
zs. fixw3. fixw. zs. fixw3. fixw.
match goal with |- context [Z_to_bv 64 (?e + 27)%Z] => replace (e + 27)%Z with (53 - 3 * (rp - 9))%Z by lia end.
set (bitlim := (53 - 3 * (rp - 9))%Z) in *.

assert (G94 : forall (x10' : word), yR = f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10' (Z_to_bv 64 30) x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
(Z_to_bv 64 8) x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda088) fct None m (seg_rom usegs))).
{ intros x10' Hy. clear HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. zs. zs. zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. rewrite (Z.shiftl_mul_pow2 (rp + -10)) by lia. change (2^2)%Z with 4%Z. zs. zs.

assert (G_DC : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt usegs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (rp - 10))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 0xda0d0) fct None m2 (seg_rom usegs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (rp - 10)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
zs. eapply L_DD28; try eassumption; try mk_dfinv. }
assert (Hc : (rp = 10 \/ rp = 11 \/ rp = 12 \/ rp = 13 \/ rp = 14 \/ rp = 15 \/ rp = 16 \/ rp = 17)%Z) by lia.
clear Hy. clearbody bitlim.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_DC; mk_dfinv). }
zs. zs. brs K6.
*
replace (30 <? bitlim)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
* replace (30 <? bitlim)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
zs. rewrite srlw_small by lia.
assert (Rs0 : (0 <= Z.shiftr x0 bitlim)%Z) by (apply Z.shiftr_nonneg; lia).
assert (Rs1 : (Z.shiftr x0 bitlim <= x0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]; assert (1 <= 2 ^ bitlim)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia); nia).
zs. brf K7.
--
replace (Z.shiftr x0 bitlim =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
eapply G94. symmetry. exact HK.
-- replace (Z.shiftr x0 bitlim =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
stmt HS_T. eapply NX; try eassumption; try lia. exact (conj LW' (conj LX REL)).
+
assert (Rrp1 : (1 <= rp <= 8)%Z) by lia.
replace (rp <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK. rename HK into HyR.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs.
zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
zs. zs. zs. zs.
zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
zs. zs. fixw3. fixw. zs. zs. zs. try rewrite zext32_small by lia. try (rewrite (Z.shiftl_mul_pow2 (8 - rp)) by lia; change (2^2)%Z with 4%Z). zs. zs.

assert (G_E4 : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
evt usegs POST
(MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (8 - rp))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Ft (Z_to_bv 64 0xd95d8) fct None m2 (seg_rom usegs))).
{ intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
pose proof DI2 as DI'. dest_dfinv DI'.
pose proof (p10s_lit (8 - rp)%Z ltac:(lia)) as Rp.
zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
set (PF := f128_of_i32 (znth p10s (8 - rp))) in *. pose proof (lo64_range PF) as R4l. pose proof (hi64_range PF) as R4h.
zs. zs. zs. zs.
zs. call_split 112%Z (eapply div_callE with (X := P) (Y := PF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. eapply L_RET1; try eassumption; try lia; try mk_finv; try mk_framL. }
assert (Hc : (rp = 1 \/ rp = 2 \/ rp = 3 \/ rp = 4 \/ rp = 5 \/ rp = 6 \/ rp = 7 \/ rp = 8)%Z) by lia.
clear HyR.
destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_E4; mk_dfinv).
-
replace (rp =? 9)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs. zs.
pose proof L_DD24 as NX. unfold QHB6.Mq3.S_DD24 in NX. eapply NX; try eassumption; try lia; try mk_dfinv; try (symmetry; exact HK).
Qed.

End Floatscan.
