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
Local Notation L_SCL := (@QHB6.Mq0.L_SCL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPLO SPF SPT SG1 SG3 Q1).
Local Notation dfinv := (@QHB6.Mq0.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F3 := (@QHB6.Mq0.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
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

#[using="Type"] Lemma land31_eq : forall v, Z.land (u32 v) INT_MAX_ = Z.land (Z.land v 18446744073709551615) 2147483647.
Proof.
clear. intros v. unfold u32, INT_MAX_. change (2^32)%Z with (2^32)%Z. rewrite <- (Z.land_ones v 32) by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_E9FC : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y e2 : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd792c) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros DI RJ Hk FOK FRM' He2 Hy.
dest_dfinv DI. unfold ssp_guard in LOW |- *.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F9F0 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR e2 dn : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^25 <= e2 < 2^25)%Z -> (0 <= dn <= 1)%Z ->
yR = m_scalbnl Y e2 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 dn) (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 FR)) x23 x24 x25 x26 (Z_to_bv 64 (hi64 FR)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7920) fct None m (seg_rom rsegs)).
Proof.
intros until dn. intros DI RJ Hk FOK FRM' He2 Hdn Hy.
pose proof DI as DI0. dest_dfinv DI. unfold ssp_guard in LOW.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR).
zs. fixw2. zs. zs. brs K3.
-  zs. brf K4.
+ eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
+ zs. zs. zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range FR 0) as RLE.
zs. brf K5.
* eapply L_E9FC; try eassumption; try lia; try mk_dfinv.
* eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
- eapply L_E9FC; try eassumption; try lia; try exact DI0.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F3 : S_F3.
Proof.
intros m. intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb HK.
dest_dfinv DI. unfold FS_DEPTH in SPLO. unfold ssp_guard in LOW.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
unfold fin_K3 in HK. rewrite land31_eq in HK. change (1024 - 5)%Z with 1019%Z in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
pose proof (land_mask_range (Z.land (e2 + 113) 18446744073709551615) 2147483647 ltac:(lia)) as R31.

zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM1.
set (Y1 := f128_add Y FR) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

zs. zs. zs.
call_split 48%Z (eapply sub_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM2.
set (Y2 := f128_sub Y1 BI) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs. zs. zs. brs K.
-
replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
injection HK as HK'.
zs. zs.
eapply L_SCL; try eassumption; try lia; try (symmetry; exact HK'); try mk_finv; try mk_framL.
- replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).

zs. zs. zs. callx (eapply fabsl_callE; [eassumption | reflexivity | reflexivity]).
set (AY := m_fabsl Y2) in *. pose proof (lo64_range AY). pose proof (hi64_range AY).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 2)). pose proof (hi64_range (f128_of_i32 2)).
zs. zs. zs. zs.
call_split 112%Z (eapply div_callE with (Y := C_LDBL_EPS); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (LIM := f128_div (f128_of_i32 2) C_LDBL_EPS) in *. pose proof (lo64_range LIM). pose proof (hi64_range LIM).
zs. zs. zs. zs. zs. callx (eapply getf2_callE; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range AY LIM) as RGE.
zs. zs. brs K2.
+
replace (0 <=? f128_ge AY LIM)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). injection HK as HK'.
zs. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try (lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end).
+
replace (0 <=? f128_ge AY LIM)%Z with true in HK by (symmetry; apply Z.leb_le; lia). injection HK as HK'.
zs. zs. zs. zs. zs. zs. zs. zs.
zs. callx (eapply extenddftf2_callv with (D := 0x3FE0000000000000%Z); [eassumption | lia]).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (Y := f128_of_d 0x3FE0000000000000); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs. zs. fixw2. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try fok; try b2z_01. all: show_goal.
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
Local Notation txt_char := (@QHB6.Mq0.txt_char txt BYT).
Local Notation S_E := (@QHB6.Mq0.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@QHB6.Mq0.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation winv := (@QHB6.Mq0.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation winv_dfinvG := (@QHB6.Mq0.winv_dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_B0C := (@QHB6.Mq0.S_B0C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A9C := (@QHB6.Mq0.S_A9C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A44 := (@QHB6.Mq0.S_A44 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_RZ := (@QHB6.Mq0.S_RZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9EC := (@QHB6.Mq0.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A64 := (@QHB6.Mq0.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq0.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_winv := unfold QHB6.Mq0.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Notation POST := (fs_post m0).

Hypothesis HS_D : S_D.
Hypothesis HS_E : S_E.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.

Ltac mk_winv2 := unfold QHB6.Mq0.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma znth_X0 : forall i, znth X0 i = 0%Z.
Proof.
clear. intros i. unfold X0. destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite znth_zupd_eq; [reflexivity|]. rewrite zlength_zrepeat; unfold KMAX; lia.
- rewrite znth_zupd_neq by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity.
Qed.
#[using="Type"] Lemma X0_len : length X0 = 2048%nat.
Proof. clear. unfold X0, KMAX. rewrite zupd_length. pose proof (zlength_zrepeat 0 2048 ltac:(lia)) as E. unfold zlength in E. lia. Qed.
#[using="Type"] Lemma xrel_X0 : forall ws, length ws = 2048%nat -> wval ws 0 = 0%Z -> xrel ws X0 (digz 0 0).
Proof.
clear. intros ws LW W0. split; [exact LW|]. split; [exact X0_len|].
intros i Hi Hr. unfold digz in Hr. assert (Ei : i = 0%Z) by lia. rewrite Ei, znth_X0, W0. reflexivity.
Qed.
Ltac x0_facts := splits; try lia; try (apply xrel_X0; assumption); unfold X31; intros; rewrite ?znth_X0 in *; try lia.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof.
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
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

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D"] Lemma L_B0C : S_B0C.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hcond HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear -RJ Hcond. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | apply (proj2 (proj2 (NS0 eq_refl))); intros E0; rewrite E0 in Hcond; cbv in Hcond; discriminate Hcond]. }
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
unfold dfK_dig in HK. destruct (df_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite (seqz46 c) by lia. zs. zs. zs. zs. zs.
match goal with |- context [Z_to_bv 64 (q + -8416 + 104 + 8176)%Z] => replace (q + -8416 + 104 + 8176)%Z with (q + -136)%Z by lia | _ => idtac end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_D. eapply (NX fuelc) with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinv. }
{ unfold digI. x0_facts. }
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A9C : S_A9C.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hne HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. brf K1; rewrite ?land_W64 in K1.
-
stmt L_B0C. eapply NX; try eassumption; try lia.
replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Bool.orb_false_r.
apply (proj2 (isdigitc_iff c ltac:(lia))). clear -K1 Rc. Z.div_mod_to_equations. lia.
-
assert (Hd : isdigitc c = false).
{ apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c ltac:(lia))) in D. clear -K1 D Rc. Z.div_mod_to_equations. lia. }
assert (HL : df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0)).
{ clear -HK Hd Hne. unfold dfK_dig in HK. destruct fuelc as [|fu]; [discriminate HK|].
cbn [df_dig_loop]. unfold df_dig_cond. cbn [dl_c]. rewrite Hd. replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
unfold dfK_dig in HK. rewrite HL in HK.
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_E. eapply NX with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinvG. }
{ unfold dig_facts. x0_facts. }
{ rewrite znth_X0. intros X; exfalso; exact (X eq_refl). }
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A44 : S_A44.
Proof.
intros m; intros until gotdig. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rlrp Rg Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs.
pose proof (u32arr_store_ok rsegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1.
- stmt L_A9C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
clear -K1 Rc. rewrite land_W64 in K1. Z.div_mod_to_equations; lia.
- assert (E46 : c = 46%Z) by (clear -K1 Rc; rewrite land_W64 in K1; Z.div_mod_to_equations; lia).
zs. stmt L_B0C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
all: rewrite E46; reflexivity.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_RZ : S_RZ.
Proof.
unfold QHB6.Mq0.S_RZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK.
dest_winv WI. bury_disj.
rewrite df_rz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].

assert (HEAD : forall m2 (x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd6950) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w32 w48 w80 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) (lrp + -1)%Z 1%Z g' lrp' c' f');
try eassumption; try lia.
rewrite E48 in HL. replace (lrp + -1)%Z with (lrp - 1)%Z by lia. exact HL. }

assert (EXIT : forall m2 (x1' x5' x6' x7' x9' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd6970) fct None m2 (seg_rom rsegs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', lrp', c', f') = (1%Z, (lrp - 1)%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_rz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
pose proof WI2 as WI3. dest_winv WI3.
zs.
stmt L_A44. eapply NX with (gotdig := 1%Z) (lrp := (lrp + -1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia).
all: replace (lrp + -1)%Z with (lrp - 1)%Z by lia; exact HK. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin 48 f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
set (c'' := fst (sh_getc f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_9EC : S_9EC.
Proof.
intros m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rg HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_RZ as NX. unfold QHB6.Mq0.S_RZ, QHB6.Mq0.SRZn in NX. eapply (NX fuelc) with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
assert (E : (g', lrp', c', f') = (gotdig, 0%Z, c, f)).
{ clear -HL HK N48. unfold dfK_dig in HK. destruct fuelc as [|n2]; [|rewrite df_rz_loop_step in HL].
- exfalso. cbn [df_dig_loop] in HK. discriminate HK.
- replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
zs. stmt L_A44. eapply NX with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A64 : S_A64.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok rsegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 1%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_7F4 : S_7F4.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok rsegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write rsegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 0%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
- exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
Qed.

End Floatscan.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x QCwx Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

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
Local Notation txt_char := (@QHB6.Mq3.txt_char txt BYT).
Local Notation S_E := (@QHB6.Mq3.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_D := (@QHB6.Mq3.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation winv := (@QHB6.Mq3.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation winv_dfinvG := (@QHB6.Mq3.winv_dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_B0C := (@QHB6.Mq3.S_B0C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A9C := (@QHB6.Mq3.S_A9C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A44 := (@QHB6.Mq3.S_A44 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_RZ := (@QHB6.Mq3.S_RZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_9EC := (@QHB6.Mq3.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_A64 := (@QHB6.Mq3.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation S_7F4 := (@QHB6.Mq3.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
Ltac mk_winv := unfold QHB6.Mq3.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
Notation POST := (fs_post m0).

Hypothesis HS_D : S_D.
Hypothesis HS_E : S_E.

Ltac ufc2 FC := unfold rf_cells in FC;
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.

Ltac mk_winv2 := unfold QHB6.Mq3.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
split; [first [assumption | rewrite ?upd_length; assumption]|];
first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
#[using="Type"] Lemma znth_X0 : forall i, znth X0 i = 0%Z.
Proof.
clear. intros i. unfold X0. destruct (Z.eq_dec i 0) as [->|Hne].
- rewrite znth_zupd_eq; [reflexivity|]. rewrite zlength_zrepeat; unfold KMAX; lia.
- rewrite znth_zupd_neq by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity.
Qed.
#[using="Type"] Lemma X0_len : length X0 = 2048%nat.
Proof. clear. unfold X0, KMAX. rewrite zupd_length. pose proof (zlength_zrepeat 0 2048 ltac:(lia)) as E. unfold zlength in E. lia. Qed.
#[using="Type"] Lemma xrel_X0 : forall ws, length ws = 2048%nat -> wval ws 0 = 0%Z -> xrel ws X0 (digz 0 0).
Proof.
clear. intros ws LW W0. split; [exact LW|]. split; [exact X0_len|].
intros i Hi Hr. unfold digz in Hr. assert (Ei : i = 0%Z) by lia. rewrite Ei, znth_X0, W0. reflexivity.
Qed.
Ltac x0_facts := splits; try lia; try (apply xrel_X0; assumption); unfold X31; intros; rewrite ?znth_X0 in *; try lia.
#[using="Type"] Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
Proof.
clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
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

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D"] Lemma L_B0C : S_B0C.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hcond HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rrpp : (sh_rpos f <= p)%Z).
{ clear -RJ Hcond. destruct RJ as (R0 & R1 & R2 & R3 & NS0 & SS0). destruct (sh_stdio f) eqn:Es; [destruct (SS0 eq_refl) as (Qa & Qb & Qc); exact Qb | apply (proj2 (proj2 (NS0 eq_refl))); intros E0; rewrite E0 in Hcond; cbv in Hcond; discriminate Hcond]. }
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
unfold dfK_dig in HK. destruct (df_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite (seqz46 c) by lia. zs. zs. zs. zs. zs.
match goal with |- context [Z_to_bv 64 (q + -8416 + 104 + 8176)%Z] => replace (q + -8416 + 104 + 8176)%Z with (q + -136)%Z by lia | _ => idtac end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_D. eapply (NX fuelc) with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinv. }
{ unfold digI. x0_facts. }
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A9C : S_A9C.
Proof.
intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hne HK.
pose proof DI as DI0. dest_dfinv DI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. brf K1; rewrite ?land_W64 in K1.
-
stmt L_B0C. eapply NX; try eassumption; try lia.
replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Bool.orb_false_r.
apply (proj2 (isdigitc_iff c ltac:(lia))). clear -K1 Rc. Z.div_mod_to_equations. lia.
-
assert (Hd : isdigitc c = false).
{ apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c ltac:(lia))) in D. clear -K1 D Rc. Z.div_mod_to_equations. lia. }
assert (HL : df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0)).
{ clear -HK Hd Hne. unfold dfK_dig in HK. destruct fuelc as [|fu]; [discriminate HK|].
cbn [df_dig_loop]. unfold df_dig_cond. cbn [dl_c]. rewrite Hd. replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
unfold dfK_dig in HK. rewrite HL in HK.
pose proof LOW as LOWw. lo96w LOWw.
zs. zs. zs. zs.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
stmt HS_E. eapply NX with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try lia.
{ mk_dfinvG. }
{ unfold dig_facts. x0_facts. }
{ rewrite znth_X0. intros X; exfalso; exact (X eq_refl). }
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A44 : S_A44.
Proof.
intros m; intros until gotdig. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rlrp Rg Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs.
pose proof (u32arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1.
- stmt L_A9C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
clear -K1 Rc. rewrite land_W64 in K1. Z.div_mod_to_equations; lia.
- assert (E46 : c = 46%Z) by (clear -K1 Rc; rewrite land_W64 in K1; Z.div_mod_to_equations; lia).
zs. stmt L_B0C. eapply NX with (gotrad := 1%Z); try eassumption; try lia. { rewrite <- winv_dfinvG. mk_winv. }
all: rewrite E46; reflexivity.
Qed.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_RZ : S_RZ.
Proof.
unfold QHB6.Mq3.S_RZ. induction n as [|n IH].
{ intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK. discriminate HL. }
intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK.
dest_winv WI. bury_disj.
rewrite df_rz_loop_step in HL. rewrite Z.eqb_refl in HL.
site_facts FC RJ kmin 48%Z f.
pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); exact R).
pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].

assert (HEAD : forall m2 (x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) = 48%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' x10' x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd9014) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2 E48. rewrite E48 in RJ1.
eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w32 w48 w80 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) (lrp + -1)%Z 1%Z g' lrp' c' f');
try eassumption; try lia.
rewrite E48 in HL. replace (lrp + -1)%Z with (lrp - 1)%Z by lia. exact HL. }

assert (EXIT : forall m2 (x1' x5' x6' x7' x9' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
fst (sh_getc f) <> 48%Z ->
evt usegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd9034) fct None m2 (seg_rom usegs))).
{ intros until x31'. intros WI2 N48.
assert (E : (g', lrp', c', f') = (1%Z, (lrp - 1)%Z, fst (sh_getc f), snd (sh_getc f))).
{ clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_rz_loop_step in HL.
replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
pose proof WI2 as WI3. dest_winv WI3.
zs.
stmt L_A44. eapply NX with (gotdig := 1%Z) (lrp := (lrp + -1)%Z); try eassumption; try lia.
all: try (intros Hn1; specialize (Rrp2 Hn1); lia).
all: replace (lrp + -1)%Z with (lrp - 1)%Z by lia; exact HK. }
clear HL HK IH.
destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
-
pose proof FC as FC0. ufc2 FC.
zs. zs. zs. (brf K1; [ | exfalso; lia ]).
destruct (rf_getc_slow T txt p J Hp T1 kmin 48 f RJ SLOW) as (STD & EJ & Hn & Hrpe & Hc00).
assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
zs. zs. call_split 160%Z (eapply shgetc_callJ with (pre := pre) (post := post);
[ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
| eplia | eplia | exact SEP | replace (q + -8416 - 160)%Z with (q + -8416 - 160)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption ]).
match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
set (c'' := fst (sh_getc f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply EXIT; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
+ eapply HEAD; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
-
pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
ufc2 FC.
zs. zs. zs. (brf K1; [ exfalso; lia | ]).
zs. zs0.
pose proof (u8ro_read usegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Qy5Y.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
zs. cbv beta. try rewrite (Qy5Y.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
set (c'' := znth txt (sh_rpos f)) in *.
zs. zs. brf K2; rewrite ?land_W64 in K2.
+ eapply HEAD; [mk_winv2 | exact K2].
+ eapply EXIT; [mk_winv2 | exact K2].
Qed.
Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.

#[using="ST0 BYT Hp Hnul HP30 T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 HS_D HS_E"] Lemma L_9EC : S_9EC.
Proof.
intros m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rg HL HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
- assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
pose proof L_RZ as NX. unfold QHB6.Mq3.S_RZ, QHB6.Mq3.SRZn in NX. eapply (NX fuelc) with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
- assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
assert (E : (g', lrp', c', f') = (gotdig, 0%Z, c, f)).
{ clear -HL HK N48. unfold dfK_dig in HK. destruct fuelc as [|n2]; [|rewrite df_rz_loop_step in HL].
- exfalso. cbn [df_dig_loop] in HK. discriminate HK.
- replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
injection E as -> -> -> ->. clear HL.
zs. stmt L_A44. eapply NX with (lrp := 0%Z); try eassumption; try lia. norm_m1074. mk_winv2.
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_A64 : S_A64.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 1%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
Qed.

#[using="Hp HP30 SPLO SPF SPT SG1 Q1 HS_D HS_E"] Lemma L_7F4 : S_7F4.
Proof.
intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
dest_winv WI. bury_disj.
pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
assert (Rc : (-1 <= c < 256)%Z) by (destruct RJ as (_ & R & _); exact R).
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
pose proof (u32arr_store_ok usegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
zs.
pose proof (u32arr_write usegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
zs. zs. fixw3. zs. brf K1; rewrite ?land_W64 in K1.
- norm_m1074. stmt L_A9C. eapply NX with (gotdig := 0%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try lia. rewrite <- winv_dfinvG. mk_winv.
- exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
Qed.

End Floatscan.
End Mq2.

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
Notation RFJ' := (RFJ T txt p true J).

Local Notation Fok := (@QHB6.Mq3.Fok F).
Local Notation Fok_refl := (@QHB6.Mq3.Fok_refl F).
Local Notation Fok_set := (@QHB6.Mq3.Fok_set F).
Local Notation fs_post := (@QHB6.Mq3.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QHB6.Mq3.zbytes_len txt).
Local Notation L_SCL := (@QHB6.Mq3.L_SCL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPLO SPF SPT SG1 SG3 Q1).
Local Notation dfinv := (@QHB6.Mq3.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
Local Notation S_F3 := (@QHB6.Mq3.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

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
Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
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

#[using="Type"] Lemma land31_eq : forall v, Z.land (u32 v) INT_MAX_ = Z.land (Z.land v 18446744073709551615) 2147483647.
Proof.
clear. intros v. unfold u32, INT_MAX_. change (2^32)%Z with (2^32)%Z. rewrite <- (Z.land_ones v 32) by lia.
rewrite <- !Z.land_assoc. reflexivity.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_E9FC : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y e2 : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9ff0) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros DI RJ Hk FOK FRM' He2 Hy.
dest_dfinv DI. unfold ssp_guard in LOW |- *.
zs. callx (eapply errno_loc_spec; eassumption).
zs. unfold RERRNO. zs0.
zs. eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
Qed.

#[using="fc pre post fuelc f0 kmin0 c0 Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F9F0 : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR e2 dn : Z),
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^25 <= e2 < 2^25)%Z -> (0 <= dn <= 1)%Z ->
yR = m_scalbnl Y e2 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 dn) (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 FR)) x23 x24 x25 x26 (Z_to_bv 64 (hi64 FR)) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9fe4) fct None m (seg_rom usegs)).
Proof.
intros until dn. intros DI RJ Hk FOK FRM' He2 Hdn Hy.
pose proof DI as DI0. dest_dfinv DI. unfold ssp_guard in LOW.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR).
zs. fixw2. zs. zs. brs K3.
-  zs. brf K4.
+ eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
+ zs. zs. zs. zs. zs. callx (eapply letf2_callE with (Y := 0%Z); [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_le_range FR 0) as RLE.
zs. brf K5.
* eapply L_E9FC; try eassumption; try lia; try mk_dfinv.
* eapply L_SCL; try eassumption; try lia; try mk_finv; try mk_framL.
- eapply L_E9FC; try eassumption; try lia; try exact DI0.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_F3 : S_F3.
Proof.
intros m. intros until bits'. intros _ DI RJ Hk FOK FRM' Hsg He2 Hb HK.
dest_dfinv DI. unfold FS_DEPTH in SPLO. unfold ssp_guard in LOW.
pose proof (lo64_range Y). pose proof (hi64_range Y). pose proof (lo64_range FR). pose proof (hi64_range FR). pose proof (lo64_range BI). pose proof (hi64_range BI).
unfold fin_K3 in HK. rewrite land31_eq in HK. change (1024 - 5)%Z with 1019%Z in HK. change LDBL_MANT_DIG_ with 113%Z in HK.
pose proof (land_mask_range (Z.land (e2 + 113) 18446744073709551615) 2147483647 ltac:(lia)) as R31.

zs. zs. zs. zs. zs. zs.
call_split 48%Z (eapply add_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM1.
set (Y1 := f128_add Y FR) in *. pose proof (lo64_range Y1). pose proof (hi64_range Y1).

zs. zs. zs.
call_split 48%Z (eapply sub_callE; [eassumption | eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
rename PC into FRM2.
set (Y2 := f128_sub Y1 BI) in *. pose proof (lo64_range Y2). pose proof (hi64_range Y2).
zs. zs. zs. zs. zs. zs. brs K.
-
replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia).
injection HK as HK'.
zs. zs.
eapply L_SCL; try eassumption; try lia; try (symmetry; exact HK'); try mk_finv; try mk_framL.
- replace (1019 <? Z.land (Z.land (e2 + 113) 18446744073709551615) 2147483647)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).

zs. zs. zs. callx (eapply fabsl_callE; [eassumption | reflexivity | reflexivity]).
set (AY := m_fabsl Y2) in *. pose proof (lo64_range AY). pose proof (hi64_range AY).
zs. zs. zs. zs. callx (eapply floatsitf_callp; [eassumption | lia]).
pose proof (lo64_range (f128_of_i32 2)). pose proof (hi64_range (f128_of_i32 2)).
zs. zs. zs. zs.
call_split 112%Z (eapply div_callE with (Y := C_LDBL_EPS); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
set (LIM := f128_div (f128_of_i32 2) C_LDBL_EPS) in *. pose proof (lo64_range LIM). pose proof (hi64_range LIM).
zs. zs. zs. zs. zs. callx (eapply getf2_callE; [eassumption | reflexivity | reflexivity | reflexivity | reflexivity]).
pose proof (f128_ge_range AY LIM) as RGE.
zs. zs. brs K2.
+
replace (0 <=? f128_ge AY LIM)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). injection HK as HK'.
zs. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try (lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end).
+
replace (0 <=? f128_ge AY LIM)%Z with true in HK by (symmetry; apply Z.leb_le; lia). injection HK as HK'.
zs. zs. zs. zs. zs. zs. zs. zs.
zs. callx (eapply extenddftf2_callv with (D := 0x3FE0000000000000%Z); [eassumption | lia]).
zs. zs. zs. zs. zs.
call_split 80%Z (eapply mul_callE with (Y := f128_of_d 0x3FE0000000000000); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
zs. zs. zs. fixw2. zs.
let v := getreg 8%Z in lazymatch v with Z_to_bv 64 ?dv =>
eapply L_F9F0 with (dn := dv); try eassumption; try lia; try (symmetry; exact HK'); try mk_dfinv end.
all: try fok; try b2z_01. all: show_goal.
Qed.

End Floatscan.
