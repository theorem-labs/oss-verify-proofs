(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20 YC7x YC21 YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03 YO08 YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACek ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACel ACer ACfm ACf5 ACf9 ACf7 ACf8 ACf6 ACfh ACf4 ACfk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac gcfg_rewin HS wlo whi ptac :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := eval vm_compute in (idx_of (fun r => match YP09.r_base r with Some 75%nat => Z.eqb (YP09.r_lo r) 32 | _ => false end) rs) in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r wlo whi (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; ptac))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma land4_mod32 : forall x, 0 <= x -> Z.land (x mod 2 ^ 32) 4 = Z.land x 4.
Proof.
intros x Hx. apply Z.bits_inj'. intros i Hi.
rewrite !Z.land_spec. destruct (Z.ltb_spec i 32) as [Hl|Hl].
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit 4 i) with false; [rewrite !Bool.andb_false_r; reflexivity|].
symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Variable XN : xnums.
Variable XN_LIB : Z -> Z.
Variables (wfn rlo rhi : Z).
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis AFREEN4 : afree_null04_rule tfibsegs B MT.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis TNEWGIFX : tnewgif_x tfibsegs tfib_K B MT XN A_cgif_newgif CTX_cgif_newgif wfn rlo rhi.
Hypothesis AUNLINKX : aunlink_x tfibsegs B tfib_K 0x9c9cc.
Hypothesis XNpos : forall n, 0 <= n -> 0 <= xm_newgif XN n.
Hypothesis XNle : forall n, 0 <= n -> 0 <= xn_newgif XN n <= xm_newgif XN n.
Hypothesis HRO : forall rd, arodata_ok B rd -> arodata_okP tfibsegs rlo rhi B rd.
Hypothesis RFX : rt_fromX B MT XN_LIB PTF ss_F (INV_FX B MT XN wfn).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma lx_E_aux : True -> forall (cx : rtcx) (E : env) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
rt_base B MT cx -> rt_E cx E ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = [(2, c_fpos cx)] ->
mo_le MT (c_S cx) S3 acc ->
INV_E B MT [] cx E k acc ly3 S3 W3 ms3 md3 ->
st_ok tfibsegs E ss_E (restrict (w_H W3) ms3) ->
forall (pl : list byte) (aM : Z) (Kl : lleaf -> TSet),
AI tfibsegs (w_H W3) (w_A W3) md3 ->
rt_xbase B MT XN_LIB cx pl aM Kl ->
acc + xm_newgif XN (hdr_ngp (zbytes pl)) + mo_free MT <= c_T cx ->
srealizes tfibsegs (mkCfg ms3 md3) (aff_tree Kl (m_fs (c_md cx)) (zbytes pl)).
Proof.
intros _. rt_prelude. intros pl aM Kl HAI3 (Hnpl & HPL & HSNK0 & HFD0 & HSORT0 & HAM0 & HLEAF & HTX) HROOM. pose proof (conj Hnpl (conj HPL (conj HSNK0 (conj HFD0 (conj HSORT0 (conj HAM0 (conj HLEAF HTX))))))) as HXB1. cbn [c_n c_p c_W c_mem c_T c_md c_ly] in Hnpl, HPL, HSNK0, HFD0, HSORT0, HAM0, HROOM, HTX.
apply (srz_enter tfibsegs W3 (mkCfg ms3 md3) _ HAI3). clear HAI3.
pose proof HINV as (Hk1 & Hacc & attr & gen & w16 & h16 & ngp & cur & pal & HGC & E194 & HNle & E191 & Rpal & Hpal).
pose proof HGC as (E185 & E186 & E187 & E188 & E189 & E192 & Rattr & Rgen & Rw & Rh & Rngp & Rcur & Rr & Hr14 & Vp & Vn & Vc & Hprov & Hwhy).
cbn [c_n c_sp1 c_p] in Rcur, Hr14, Vp, Vn, Vc.
pose proof (Hr14 eq_refl) as Hn14.
pose proof Hpal as HpalU. unfold rt_palD, rt_newblk in HpalU. cbn [c_ly c_S c_regs c_T] in HpalU.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
assert (B70 : bv_unsigned (ew E 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (B75 : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (HSPB : alloc_ceiling <= spZ regs - LLVMF_STK /\ spZ regs <= 2 ^ 47) by (clear - Hceil Hslo Hshi H47 Hstk0; lia).
gcfg_rewin HS 40 48 ltac:(rewrite RF, unsigned_lit_small by (clear - HF4096 HFceil C1; lia); intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres3 (F + o) ltac:(clear - Ho; lia)))).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ F <= a < F + 32 \/ F + 80 <= a < F + 256 \/ F + 40 <= a < F + 48).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RTBspan A_cgif_newgif.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 HF8hi; lia).
palv_run HFr Hpal AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096).
unrunRD HFr Zsm Usp B70 Hsp1 UN1. clear_frames.
vkeepUN UN1 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN1.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
assert (UF : bv_unsigned (ew E 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x809f8) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iF := idx_of_base_off rs 75%nat 32 in let iF := eval vm_compute in iF in
let rF := eval vm_compute in (nth iF rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iF rF HS ltac:(vm_compute; reflexivity)) as HRF; cbn [ms_mem restrict] in HRF end.
Ltac fieldF HRF UF od w e V :=
lazymatch type of HRF with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 75 _ cs lo hi wlo whi od w e HRF UF ltac:(cbn; tauto) ltac:(cbn; lia)) as V;
cbn [sv_denot] in V; rewrite ?ew_ewset_other, ?ew_havoc_old in V by nat_side;
try change (N.to_nat 8) with 8%nat in V; try change (N.to_nat 4) with 4%nat in V; try change (N.to_nat 2) with 2%nat in V; try change (N.to_nat 1) with 1%nat in V;
try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V; try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in V;
try change (2 ^ (8 * Z.of_N 2)) with 65536 in V; try change (2 ^ (8 * Z.of_N 1)) with 256 in V end.
fieldF HRF UF 32 8%N (SOff 191 0) V0. fieldF HRF UF 40 8%N (SLit 134656) V1.     fieldF HRF UF 48 4%N (SOff 185 0) V2. fieldF HRF UF 52 4%N (SOff 186 0) V3.
fieldF HRF UF 56 2%N (SOff 187 0) V4. fieldF HRF UF 58 2%N (SOff 188 0) V5. fieldF HRF UF 60 2%N (SOff 189 0) V6. fieldF HRF UF 62 2%N (SLit 0) V7.
lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch cs with context [YP09.mkChunk 64 (CVal 8%N ?ea)] => fieldF HRF UF 64 8%N ea V8 end end.
fieldF HRF UF 72 8%N (SLit 0) V9.
rewrite (denot_atom_mod _ 191 pal _ E191 Rpal), Z.mod_small in V0 by (exact Rpal).
rewrite (denot_atom_mod _ 185 attr _ E185 ltac:(clear - Rattr; lia)) in V2. rewrite (denot_atom_mod _ 186 gen _ E186 ltac:(clear - Rgen; lia)) in V3.
rewrite (denot_atom_mod _ 187 w16 _ E187 ltac:(clear - Rw; lia)), Z.mod_small in V4 by (clear - Rw; lia).
rewrite (denot_atom_mod _ 188 h16 _ E188 ltac:(clear - Rh; lia)), Z.mod_small in V5 by (clear - Rh; lia).
rewrite (denot_atom_mod _ 189 ngp _ E189 ltac:(clear - Rngp; lia)), Z.mod_small in V6 by (clear - Rngp; lia).
cbn [bv_unsigned Z_to_bv] in V7, V8, V9. change (bv_unsigned (Z_to_bv 64 134656) mod 2 ^ 64) with 134656 in V1.
assert (Rattr' : 0 <= attr mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; clear; lia).
assert (Rgen' : 0 <= gen mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; clear; lia).
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (OcfgX : obj_at tfibsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_Config
[pal; ak_path tfib_K; attr mod 2 ^ 32; gen mod 2 ^ 32; w16; h16; ngp; 0; 0; 0]) end.
{ change (ak_path tfib_K) with 134656. cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
split; [split; [exact V0 | exact Rpal]|].
split; [split; [first [exact V1 | match type of V1 with ?t => idtac "V1-SHAPE" t end; fail] | clear; lia]|].
split; [split; [exact V2 | exact Rattr']|]. split; [split; [exact V3 | exact Rgen']|].
split; [split; [exact V4 | clear - Rw; lia]|]. split; [split; [exact V5 | clear - Rh; lia]|]. split; [split; [exact V6 | clear - Rngp; lia]|].
split; [split; [first [exact V7 | match type of V7 with ?t => idtac "V7-SHAPE" t end; fail] | clear; lia]|].
split; [split; [first [exact V8 | match type of V8 with ?t => idtac "V8-SHAPE" t end; fail] | clear; lia]|].
split; [split; [first [exact V9 | match type of V9 with ?t => idtac "V9-SHAPE" t end; fail] | clear; lia]|]. exact I. }
clear V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 HRF.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew E 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview tfibsegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (AF : afobj B ly3 S3 Wx (ms_mem msX) (F + 32) 48) end.
{ split; [|split].
- exists 2, fpos. split; [exact Hfin3|]. split; [clear; lia|]. rewrite EFA3. fold F. split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|].
change (fs_frame_bytes 2) with 256. clear; lia.
- rewrite HFq. replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia). apply Z_mod_mult.
- apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (48 / 8) with 6 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by (clear; lia).
assert (Hj6 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by (clear - Hj; lia).
destruct Hj6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; apply ZS; cbn; tauto. }
clear ZS.
assert (HBL : Permutation (ablocks B ly3 S3) ((if Z.land (attr mod 2 ^ 32) 4 =? 0 then [(pal, 3 * ngp)] else []) ++ ablocks B ly S)).
{ rewrite (land4_mod32 attr ltac:(clear - Rattr; lia)).
destruct HpalU as [(Ha4 & Hp0 & Eab3 & _) | (Ha4 & Hp1 & (_ & _ & _ & Eab3 & _) & _)].
- destruct (Z.eqb_spec (Z.land attr 4) 0) as [He|Hne]; [exfalso; exact (Ha4 He)|]. cbn [app]. rewrite Eab3. apply Permutation_refl.
- rewrite Ha4. cbn [Z.eqb app]. rewrite Eab3. apply Permutation_sym. apply Permutation_cons_append. }
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _).
assert (HEVc : st_nev S3 + EV_NEWGIF <= EV_MAX) by (replace EV_NEWGIF with 12 by reflexivity; rewrite HEV in Hev; clear - Hnev3 Hev Hk1; lia).
assert (HNGP : 0 <= 3 * ngp <= 3 * 65535) by (clear - Rngp; lia).
assert (HLIVEc : blocks_bytes S3 + LIVE_NEWGIF <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3). unfold LIVE_LIB in Hlive. unfold LIVE_NEWGIF.
destruct HpalU as [(_ & _ & Eab3 & _) | (_ & _ & (_ & _ & _ & Eab3 & _) & _)]; rewrite Eab3.
- rewrite <- (blocks_bytes_bsum B ly S). clear - Hlive. lia.
- rewrite bsum_app, <- (blocks_bytes_bsum B ly S). cbn [bsum fold_right snd]. clear - Hlive HNGP. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HPRE1 : afn_pre tfibsegs B TNEWGIFX_STK ly3 S3 W3 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ eapply (afn_pre_at tfibsegs B LLVMF_STK (spZ regs) [] ly S W mem md [(2, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) TNEWGIFX_STK (sp1 - spZ regs));
[ exact HJ3
| rewrite EspX; clear; lia
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| apply Zle_bool_imp_le; vm_compute; reflexivity
| replace TNEWGIFX_STK with 18816 by reflexivity; rewrite FFS; clear - Hsp1; lia
| rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Ugp; exact Hgp
| rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite Utp; exact Htp
| rewrite Es0X, EspX; exact Hch1 ]
| ] end.
pose proof (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 sink_closed_nil HSNK0) as HSNKc.
pose proof (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HAM0) as HAMc.
destruct (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efds Efs].
pose proof (ajournal_fp_nil tfibsegs B _ _ RTFP _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HJ3r.
apply SRr_ret. intros HAIc. cbn [cfg_model] in HAIc.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
cbn [c_md].
assert (Hlen14 : (14 <= length pl)%nat) by (clear - Hn14 Hnpl; lia).
pose proof (hdr_prov_hdr5 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) pl attr gen w16 h16 ngp HPL (Hprov eq_refl) Hlen14) as Hhdr.
set (attr' := attr mod 2 ^ 32) in *. set (gen' := gen mod 2 ^ 32) in *.
assert (Ha4' : Z.land attr' 4 = Z.land attr 4) by (subst attr'; apply land4_mod32; clear - Rattr; lia).
set (GPAL := if Z.land attr 4 =? 0 then firstn (Z.to_nat (3 * ngp)) (skipn 14 (zbytes pl)) else []).
assert (Hcfg : ff_cfg (zbytes pl) = Some (YO07.mkG w16 h16 attr' gen' ngp GPAL, 0, skipn (Z.to_nat cur) (zbytes pl))).
{ apply (ff_cfg_of_walk (zbytes pl) w16 h16 attr' gen' ngp GPAL cur Hhdr HNle).
- rewrite Ha4'. destruct HpalU as [(Ha4 & _ & _ & Hc14) | (Ha4 & _ & _ & Hcp)].
+ destruct (Z.eqb_spec (Z.land attr 4) 0) as [He|Hne]; [exfalso; exact (Ha4 He)|]. rewrite (Hc14 eq_refl). clear; lia.
+ rewrite Ha4. cbn [Z.eqb]. exact (proj1 (Hcp eq_refl)).
- clear - Rngp; lia.
- rewrite Ha4'. intros Ha4. subst GPAL. rewrite (proj2 (Z.eqb_eq _ _) Ha4). split; [|reflexivity].
destruct HpalU as [(Hn4 & _) | (_ & _ & _ & Hcp)]; [exfalso; exact (Hn4 Ha4)|].
pose proof (proj1 (Hcp eq_refl)) as Hc. unfold zbytes. rewrite length_map. clear - Hc Rcur Hnpl. lia.
- rewrite Ha4'. intros Hn4. subst GPAL. destruct (Z.eqb_spec (Z.land attr 4) 0) as [He|Hne]; [exfalso; exact (Hn4 He) | reflexivity]. }
unfold aff_tree. rewrite Hcfg. cbv beta iota zeta.
assert (Hngp : hdr_ngp (zbytes pl) = ngp) by (pose proof Hhdr as Hh; rewrite hdr5_bytes in Hh by (unfold zbytes; rewrite length_map; exact Hlen14); unfold hdr_ngp; congruence).
assert (HGP : Z.land attr' 4 = 0 -> garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms)) pal GPAL /\ Z.of_nat (length GPAL) = 3 * ngp).
{ rewrite Ha4'. intros Ha4. subst GPAL. rewrite (proj2 (Z.eqb_eq _ _) Ha4).
destruct HpalU as [(Hn4 & _) | (_ & Hp1 & _ & Hcp)]; [exfalso; exact (Hn4 Ha4)|]. destruct (Hcp eq_refl) as [Hc Hpp].
split.
- apply (pal_prov_garr8 (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) pl pal ngp); [exact HPL | | clear - Rngp; lia | cbn [c_n]; clear - Hc Rcur Hnpl; lia].
eapply (rt_palD_kept B [] _ attr pal ngp cur 0 ly3 S3 (w_H W3) (ms_mem ms3) (ms_mem ms) Hpalv) in Hpal.
destruct Hpal as [(Hn4 & _) | (_ & _ & _ & Hcp')]; [exfalso; exact (Hn4 Ha4)|]. exact (proj2 (Hcp' eq_refl)).
- rewrite length_firstn, length_skipn. unfold zbytes. rewrite length_map. clear - Hc Rcur Hnpl Rngp. lia. }
rewrite <- Efs.
pose proof (TNEWGIFX ly3 S3 W3 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T))
(F + 32) pal pal attr' gen' w16 h16 ngp 0 aM (ablocks B ly S) GPAL) as CALL.
unfold cfg_at, newgif_cfg in CALL. change (w64 A_cgif_newgif) with (Z_to_bv 64 529412) in CALL.
apply CALL; clear CALL.
{ exact HAIc. }
{ exact HPRE1. }
{ rewrite EspX; exact Hsp1al. }
{ rewrite EraX; apply rt_ctx_in; [exact Hra | vm_compute; tauto | vm_compute; tauto]. }
{ rewrite Hfrs3; cbn [length]; clear; lia. }
{ rewrite EspX; pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); rewrite LT; clear - Hsp1 Htop; lia. }
{ apply HRO. eapply arodata_ok_journal; [exact HJ3 | exact HROD]. }
{ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite UF; reflexivity. }
{ exact AF. }
{ exact OcfgX. }
{ exact HNle. }
{ reflexivity. }
{ first [exact HBL | rewrite <- Ha4'; exact HBL | rewrite Ha4'; exact HBL]. }
{ exact HGP. }
{ exact HSNKc. }
{ rewrite Efds. exact HFD0. }
{ exact HAMc. }
{ exact HEVc. }
{ exact HLIVEc. }
{
apply (mok_station MT S S3 T acc (xm_newgif XN ngp) MTL HMOK HMLE); [apply XNpos; clear - Rngp; lia|].
rewrite Hngp in HROOM. pose proof (mo_free_nonneg MT MTL) as Hfn. clear - HROOM Hfn. lia. }
{
intros W4 c4 Hwle4 HAI4 HpostA. unfold tnewgif_postA, apost_base in HpostA.
destruct HpostA as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HP4 & Ha04 & HAM4 & HMLEc & HPerm4 & HSNK4 & Efs4 & Efds4).
eapply (srz_enter tfibsegs W4); [exact HAI4|]. clear HAI4. rewrite Rra.
rewrite EspX in HJc.
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3r HJc
ltac:(replace TNEWGIFX_STK with 18816 by reflexivity; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia)
ltac:(intros a Ha; left; exact Ha)) as HJ4. cbn [app] in HJ4.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 OcfgX AF EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
clear Usp3 Ugp Utp UF. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
assert (Hsub4 : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hx).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HSNK4r : asink_none tfibsegs tfib_K (mrestrict (w_H W4) (ms_mem msX)) mdX) by (eapply (asink_none_imgv B AIL); [exact Himgv | destruct md4; reflexivity | exact HSNK4]) end.
clear HUP.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
clear EspX. rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a08) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of Ra0 with getr ?rg 10 = _ => assert (Ra0v : getr rg 10 = w64 pal) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E191) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly4 (aview tfibsegs (w_H W4) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ4)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ4 as (_ & HLY4 & _ & _ & _ & _ & Hnev4 & _).
assert (HEVd : st_nev S4 < EV_MAX) by (replace YC20.EV_NEWGIF with 12 in Hnev4 by reflexivity; rewrite HEV in Hev; clear - Hnev4 Hev Hk1; lia).
pose proof (mle_station MT S S3 S4 acc (xn_newgif XN ngp) MTL HMLE HMLEc) as HMLE4.
assert (MOKf : mo_ok MT S4 (mo_free MT)).
{ apply (mok_station MT S S4 T (acc + xn_newgif XN ngp) (mo_free MT) MTL HMOK HMLE4); [apply (mo_free_nonneg MT MTL)|].
pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn. try rewrite Hngp in HROOM. clear - HROOM Hxn. lia. }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3 Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (Hpal1 : 4096 <= pal \/ pal = 0) by (destruct HpalU as [(_ & Hp0 & _) | (_ & _ & ((Hbh & _) & _) & _)]; [right; exact Hp0 | left; exact Hbh]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind tfibsegs _ _
(fun W5 c5 => exists ly5 S5 regs5 mem5 md5,
c5 = mkCfg (mkst regs5 (Z_to_bv 64 0x80a08) mem5 (seg_rom tfibsegs)) md5 /\
ajournal tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 mem5 md5 (k + EV_NEWGIF + 1) /\
aregs_preserved (ms_regs msX) regs5 /\ Permutation (ablocks B ly5 S5) (ablocks B ly S) /\ frames S5 = frames S4 /\
mo_le MT S S5 (acc + xn_newgif XN ngp + mo_free MT) /\
asink_none tfibsegs tfib_K (mrestrict (w_H W5) mem5) md5 /\ m_fds md5 = m_fds mdX /\ m_fs md5 = m_fs mdX /\
exists Er : Z -> Prop, acall_kept tfibsegs B ly4 S4 W4 (ms_mem msX) W5 mem5 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a))) end.
{ destruct HpalU as [(Ha4 & Hp0 & Eab3 & _) | (Ha4 & Hp1 & (Hbh1 & Hbh2 & Hb16 & Eab3 & Hawr & Haft) & _)].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree_null04_sub tfibsegs B LAWS tfib_segs_low MT AFREEN4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4)
| ] end.
+ rewrite Ra0v, Hp0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split; [eapply Permutation_trans; [exact HPerm5|]; rewrite <- Eab3; exact HPerm4|]. split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs sink_closed_nil HSNK4r)|].
split; [exact (proj1 (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs))|].
split; [exact (proj2 (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs))|].
exists (fun _ => False). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
repeat split; intros; exact (fun HF : False => HF).
-
assert (Hpt3 : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
pose proof (Hsub4 _ Hpt3) as Hpt4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) (proj1 HJ4) Hpt4) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (sep_block_frame tfibsegs _ LAWS ly4 S4 _ _ _ pal (3 * ngp) 2 fpos (proj1 HJ4) Hpt4 Hfin4) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA4 in HdFP. fold F in HdFP.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) pal (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4 Hpt4)
| ] end.
+ exact Ra0v.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ intros Hin i Hi. exfalso. exact (inFP_nil _ (Haft Hin i Hi)).
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & Ebl4 & Ebl5) & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split.
{ rewrite Ebl5. pose proof (@Permutation_app_inv _ l1 l2 (ablocks B ly S) [] (pal, 3 * ngp)) as HPI. rewrite app_nil_r in HPI. apply HPI. rewrite <- Ebl4.
eapply Permutation_trans; [exact HPerm4|]. rewrite Eab3. apply Permutation_refl. }
split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
assert (Hclf : ~ YI16.sink_open_fp (ablocks_fp [(pal, 3 * ngp)])) by (apply sink_closed_ablocks_fp; constructor; [cbn [fst]; clear - Hbh1; lia | constructor]).
split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs Hclf HSNK4r)|].
split; [exact (proj1 (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclf HJfs))|].
split; [exact (proj2 (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclf HJfs))|].
exists (fun a => pal <= a < pal + req_size (3 * ngp)). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
split; [intros a Ha Hx; clear - Ha Hx HdFP; lia | intros a Ha Hx; clear - Ha Hx Hph_ia C3; unfold SB in *; zone_lia]. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HMLE5 & HSNK5 & Efds5 & Efs5 & Er & HK & HErF & HErLo).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Vra Vs0 Hch1.
pose proof (proj1 HJ5) as HAR5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (Hfin5 : In (2, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (Hfrs5' : frames S5 = [(2, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
reseatL HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| right; unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| left; rewrite EFA4; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar4 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar4 | exact Kuar5 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rebv HS E70 RF B70 B75. pose proof Rres as Rresn.
clear Usp3 Ugp Utp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
2: { lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => lazymatch type of Rresn with ew _ ?ng = _ => hc_atom H ng 0 Rresn ltac:(clear; lia) end). hc_prop Hc. exfalso. apply Hc. reflexivity. }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => lazymatch type of Rresn with ew _ ?ng = _ => hc_atom H ng 0 Rresn ltac:(clear; lia) end). hc_prop Hc. clear Hc.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x9c9cc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HSNK5r : asink_none tfibsegs tfib_K (mrestrict (w_H W5) (ms_mem msX)) mdX) by (eapply (asink_none_imgv B AIL); [exact Himgv0 | destruct md5; reflexivity | exact HSNK5]) end.
clear HUP.
lazymatch type of HJ5 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
clear EspX EraX Es0X.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a80) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W5) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly5 (aview tfibsegs (w_H W5) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ5)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HPREu : afn_pre tfibsegs B AUNLINK_STK ly5 S5 W5 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ eapply (afn_pre_at tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 (ms_mem msX) mdX _ (ms_regs msX) AUNLINK_STK (sp1 - spZ regs));
[ exact HJ5
| rewrite EspX; clear; lia
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| unfold AUNLINK_STK; clear; lia
| unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia
| rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
| rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
| rewrite Es0X, EspX; exact Hch1 ]
| ] end.
apply SRr_ret. intros HAIu. cbn [cfg_model] in HAIu.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- srealizes _ (mkCfg _ ?mdX) (ff_unl _ ?fs0) =>
replace fs0 with (m_fs mdX) by (transitivity (m_fs md5); [destruct md5; reflexivity|]; rewrite Efs5; transitivity (m_fs md4); [destruct md4; reflexivity|]; exact Efs4) end.
unfold ff_unl.
lazymatch goal with |- srealizes _ (mkCfg (mkst ?rg _ ?mm _) ?mdX) (unlink_shape _ ?TA ?TB) =>
pose proof (AUNLINKX W5 ly5 S5 rg mm mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) TA TB HAIu HPREu) as CALL end.
unfold cfg_at in CALL. change (w64 641484) with (Z_to_bv 64 641484) in CALL.
apply CALL; clear CALL.
{ rewrite Ra0. reflexivity. }
{ exact HSNK5r. }
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postA in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & eno & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Heno & Herr).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + EV_NEWGIF + 1 + 0) with (k + EV_NEWGIF + 1) in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin5) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA5 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
clear Kgot4 Kcell4 Kguar4 Kuar4 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseatL HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | rewrite EFA5; fold F; clear; lia | rewrite EFA5; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot5 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell5 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar5 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar5 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv1 | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly5 S5 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs5'. }
{ cbn [c_S]. exact HMLE5. }
{   split; [rewrite HEV; replace EV_NEWGIF with 12 by reflexivity; clear - Hk1; lia|].
split; [cbn [c_T]; pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn; try rewrite Hngp in HROOM; clear - HROOM Hxn; lia|].
split; [cbn [c_ly c_S]; exact HPerm5|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPerm5].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postB in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Hlk).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + EV_NEWGIF + 1 + 0) with (k + EV_NEWGIF + 1) in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin5) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA5 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
clear Kgot4 Kcell4 Kguar4 Kuar4 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseatL HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | rewrite EFA5; fold F; clear; lia | rewrite EFA5; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot5 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell5 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar5 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar5 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv1 | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly5 S5 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs5'. }
{ cbn [c_S]. exact HMLE5. }
{   split; [rewrite HEV; replace EV_NEWGIF with 12 by reflexivity; clear - Hk1; lia|].
split; [cbn [c_T]; pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn; try rewrite Hngp in HROOM; clear - HROOM Hxn; lia|].
split; [cbn [c_ly c_S]; exact HPerm5|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPerm5].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
}
{
intros Hgo Hsg W4 c4 Hwle4 HAI4 HpostB. unfold tnewgif_postB0, apost_base in HpostB.
destruct HpostB as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HP4 & Ha04 & HAM4 & HMLEc & HPerm4 & HSNK4 & Hlk4).
unfold ff_content. rewrite Hsg.
assert (Efs4 : m_fs md4 = fs_set (m_fs (with_vm_backing (m_vm_lazy md3) mat md3)) sink_path (bytes []))
by (eapply ajournal_fs_set; [exact HJc | eapply ajournal_sorted; [exact HJ3 | exact HSORT0] | exact Hlk4]).
eapply (srz_enter tfibsegs W4); [exact HAI4|]. clear HAI4. rewrite Rra.
rewrite EspX in HJc.
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3r HJc
ltac:(replace TNEWGIFX_STK with 18816 by reflexivity; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia)
ltac:(intros a Ha; left; exact Ha)) as HJ4. cbn [app] in HJ4.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 OcfgX AF EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
clear Usp3 Ugp Utp UF. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
assert (Hsub4 : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hx).
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HSNK4r : asink_none tfibsegs tfib_K (mrestrict (w_H W4) (ms_mem msX)) mdX) by (eapply (asink_none_imgv B AIL); [exact Himgv | destruct md4; reflexivity | exact HSNK4]) end.
clear HUP.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
clear EspX. rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a08) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of Ra0 with getr ?rg 10 = _ => assert (Ra0v : getr rg 10 = w64 pal) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E191) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly4 (aview tfibsegs (w_H W4) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ4)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ4 as (_ & HLY4 & _ & _ & _ & _ & Hnev4 & _).
assert (HEVd : st_nev S4 < EV_MAX) by (replace YC20.EV_NEWGIF with 12 in Hnev4 by reflexivity; rewrite HEV in Hev; clear - Hnev4 Hev Hk1; lia).
pose proof (mle_station MT S S3 S4 acc (xn_newgif XN ngp) MTL HMLE HMLEc) as HMLE4.
assert (MOKf : mo_ok MT S4 (mo_free MT)).
{ apply (mok_station MT S S4 T (acc + xn_newgif XN ngp) (mo_free MT) MTL HMOK HMLE4); [apply (mo_free_nonneg MT MTL)|].
pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn. try rewrite Hngp in HROOM. clear - HROOM Hxn. lia. }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3 Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (Hpal1 : 4096 <= pal \/ pal = 0) by (destruct HpalU as [(_ & Hp0 & _) | (_ & _ & ((Hbh & _) & _) & _)]; [right; exact Hp0 | left; exact Hbh]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind tfibsegs _ _
(fun W5 c5 => exists ly5 S5 regs5 mem5 md5,
c5 = mkCfg (mkst regs5 (Z_to_bv 64 0x80a08) mem5 (seg_rom tfibsegs)) md5 /\
ajournal tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 mem5 md5 (k + EV_NEWGIF + 1) /\
aregs_preserved (ms_regs msX) regs5 /\ Permutation (ablocks B ly5 S5) (ablocks B ly S) /\ frames S5 = frames S4 /\
mo_le MT S S5 (acc + xn_newgif XN ngp + mo_free MT) /\
asink_none tfibsegs tfib_K (mrestrict (w_H W5) mem5) md5 /\ m_fds md5 = m_fds mdX /\ m_fs md5 = m_fs mdX /\
exists Er : Z -> Prop, acall_kept tfibsegs B ly4 S4 W4 (ms_mem msX) W5 mem5 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a))) end.
{ destruct HpalU as [(Ha4 & Hp0 & Eab3 & _) | (Ha4 & Hp1 & (Hbh1 & Hbh2 & Hb16 & Eab3 & Hawr & Haft) & _)].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree_null04_sub tfibsegs B LAWS tfib_segs_low MT AFREEN4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4)
| ] end.
+ rewrite Ra0v, Hp0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split; [eapply Permutation_trans; [exact HPerm5|]; rewrite <- Eab3; exact HPerm4|]. split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs sink_closed_nil HSNK4r)|].
split; [exact (proj1 (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs))|].
split; [exact (proj2 (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs))|].
exists (fun _ => False). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
repeat split; intros; exact (fun HF : False => HF).
-
assert (Hpt3 : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
pose proof (Hsub4 _ Hpt3) as Hpt4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) (proj1 HJ4) Hpt4) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (sep_block_frame tfibsegs _ LAWS ly4 S4 _ _ _ pal (3 * ngp) 2 fpos (proj1 HJ4) Hpt4 Hfin4) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA4 in HdFP. fold F in HdFP.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) pal (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4 Hpt4)
| ] end.
+ exact Ra0v.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ intros Hin i Hi. exfalso. exact (inFP_nil _ (Haft Hin i Hi)).
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & Ebl4 & Ebl5) & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split.
{ rewrite Ebl5. pose proof (@Permutation_app_inv _ l1 l2 (ablocks B ly S) [] (pal, 3 * ngp)) as HPI. rewrite app_nil_r in HPI. apply HPI. rewrite <- Ebl4.
eapply Permutation_trans; [exact HPerm4|]. rewrite Eab3. apply Permutation_refl. }
split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
assert (Hclf : ~ YI16.sink_open_fp (ablocks_fp [(pal, 3 * ngp)])) by (apply sink_closed_ablocks_fp; constructor; [cbn [fst]; clear - Hbh1; lia | constructor]).
split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs Hclf HSNK4r)|].
split; [exact (proj1 (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclf HJfs))|].
split; [exact (proj2 (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclf HJfs))|].
exists (fun a => pal <= a < pal + req_size (3 * ngp)). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
split; [intros a Ha Hx; clear - Ha Hx HdFP; lia | intros a Ha Hx; clear - Ha Hx Hph_ia C3; unfold SB in *; zone_lia]. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HMLE5 & HSNK5 & Efds5 & Efs5 & Er & HK & HErF & HErLo).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Vra Vs0 Hch1.
pose proof (proj1 HJ5) as HAR5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (Hfin5 : In (2, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (Hfrs5' : frames S5 = [(2, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
reseatL HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| right; unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| left; rewrite EFA4; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar4 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar4 | exact Kuar5 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rebv HS E70 RF B70 B75. pose proof Rres as Rresn.
clear Usp3 Ugp Utp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
2: { lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => lazymatch type of Rresn with ew _ ?ng = _ => hc_atom H ng 0 Rresn ltac:(clear; lia) end). hc_prop Hc. exfalso. apply Hc. reflexivity. }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => lazymatch type of Rresn with ew _ ?ng = _ => hc_atom H ng 0 Rresn ltac:(clear; lia) end). hc_prop Hc. clear Hc.
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x9c9cc.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HSNK5r : asink_none tfibsegs tfib_K (mrestrict (w_H W5) (ms_mem msX)) mdX) by (eapply (asink_none_imgv B AIL); [exact Himgv0 | destruct md5; reflexivity | exact HSNK5]) end.
clear HUP.
lazymatch type of HJ5 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
clear EspX EraX Es0X.
rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a80) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W5) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly5 (aview tfibsegs (w_H W5) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ5)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HPREu : afn_pre tfibsegs B AUNLINK_STK ly5 S5 W5 (ms_regs msX) (ms_mem msX) mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ eapply (afn_pre_at tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 (ms_mem msX) mdX _ (ms_regs msX) AUNLINK_STK (sp1 - spZ regs));
[ exact HJ5
| rewrite EspX; clear; lia
| rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity
| clear - Hsp1; lia
| unfold AUNLINK_STK; clear; lia
| unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia
| rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
| rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
| rewrite Es0X, EspX; exact Hch1 ]
| ] end.
apply SRr_ret. intros HAIu. cbn [cfg_model] in HAIu.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- srealizes _ (mkCfg _ ?mdX) (ff_unl _ ?fs0) =>
replace fs0 with (m_fs mdX) by (transitivity (m_fs md5); [destruct md5; reflexivity|]; rewrite Efs5; transitivity (m_fs md4); [destruct md4; reflexivity|]; exact Efs4) end.
unfold ff_unl.
lazymatch goal with |- srealizes _ (mkCfg (mkst ?rg _ ?mm _) ?mdX) (unlink_shape _ ?TA ?TB) =>
pose proof (AUNLINKX W5 ly5 S5 rg mm mdX (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) TA TB HAIu HPREu) as CALL end.
unfold cfg_at in CALL. change (w64 641484) with (Z_to_bv 64 641484) in CALL.
apply CALL; clear CALL.
{ rewrite Ra0. reflexivity. }
{ exact HSNK5r. }
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postA in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & eno & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Heno & Herr).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + EV_NEWGIF + 1 + 0) with (k + EV_NEWGIF + 1) in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin5) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA5 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
clear Kgot4 Kcell4 Kguar4 Kuar4 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseatL HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | rewrite EFA5; fold F; clear; lia | rewrite EFA5; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot5 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell5 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar5 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar5 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv1 | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly5 S5 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs5'. }
{ cbn [c_S]. exact HMLE5. }
{   split; [rewrite HEV; replace EV_NEWGIF with 12 by reflexivity; clear - Hk1; lia|].
split; [cbn [c_T]; pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn; try rewrite Hngp in HROOM; clear - HROOM Hxn; lia|].
split; [cbn [c_ly c_S]; exact HPerm5|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPerm5].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
{
intros W6 c6 Hwle6 HAI6 HpostU. unfold aunlink_postB in HpostU.
destruct HpostU as (regs6 & mem6 & md6 & -> & HJu & HP6 & Ha06 & HSNK6 & Efds6 & Efs6 & Hlk).
eapply (srz_enter tfibsegs W6); [exact HAI6|]. clear HAI6. rewrite Rra.
rewrite EspX in HJu.
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HJu
ltac:(unfold AUNLINK_STK; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia) ltac:(intros a Ha; left; exact Ha)) as HJ6. cbn [app] in HJ6.
replace (k + EV_NEWGIF + 1 + 0) with (k + EV_NEWGIF + 1) in HJ6 by (clear; lia).
pose proof (proj1 HJ6) as HAR6.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR6 Hfin5) as (_ & _ & HFpres6 & HFSpres6).
change (fs_frame_bytes 2) with 256 in HFpres6, HFSpres6. change (256 / 8) with 32 in HFSpres6. rewrite !EFA5 in HFpres6, HFSpres6. fold F in HFpres6, HFSpres6.
clear Kgot4 Kcell4 Kguar4 Kuar4 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5. aconstsF HJ6 Kgot6 Kcell6 Kguar6 Kuar6.
reseatL HS HJ6 HP6 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA5, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJu);
[ evalE AG | exact Hfin5 | rewrite EFA5; fold F; clear; lia | rewrite EFA5; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJu | exact HJ6 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJu | exact HJ6 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot5 | exact Kgot6 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell5 | exact Kcell6 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar5 | exact Kguar6 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar5 | exact Kuar6 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RTBspan 0x80878.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) (fun _ _ => _ -> srealizes _ _ (ff_leaf _ ?fsL)) =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HSNKF : asink_none tfibsegs tfib_K (mrestrict (w_H Wg) (ms_mem msF)) mdF) by (eapply (asink_none_imgv B AIL); [exact Himgv1 | destruct md6; reflexivity | exact HSNK6]);
assert (EfsF : m_fs mdF = fsL) by (transitivity (m_fs md6); [destruct md6; reflexivity | exact Efs6]);
assert (PXKH : forall lyq bl (Wq : world tfibsegs) (m m' : word -> option byte) (mdq : Model) matq,
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wq) m' a = aview tfibsegs (w_H Wq) m a) ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m mdq ->
rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL lyq bl Wq m' (with_vm_backing (m_vm_lazy mdq) matq mdq))
by (clear - AIL; intros lyq bl Wq m m' mdq matq Hv (Hsn & Hfs & Hso & Hbl); split; [|split; [destruct mdq; exact Hfs | split; [exact Hso | exact Hbl]]];
eapply (asink_none_imgv B AIL); [exact Hv | destruct mdq; reflexivity | exact Hsn]);
eapply SRr_mono;
[ eapply (rt_XP B MT MTL RTFP TL LAWS ML ASF FFL MTF (rt_PX B (mkRTCX ly S W regs mem md p n fpos sp1 E0 T) fsL) PXKH
(mkRTCX ly S W regs mem md p n fpos sp1 E0 T) Ev _ _ ly5 S5 Wg msF mdF HBASE0)
| ] end end.
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ6. }
{ cbn [c_fpos]. exact Hfrs5'. }
{ cbn [c_S]. exact HMLE5. }
{   split; [rewrite HEV; replace EV_NEWGIF with 12 by reflexivity; clear - Hk1; lia|].
split; [cbn [c_T]; pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn; try rewrite Hngp in HROOM; clear - HROOM Hxn; lia|].
split; [cbn [c_ly c_S]; exact HPerm5|].
split; [exact HSNKF|]. split; [exact EfsF|]. split; [|cbn [c_ly c_S]; exact HPerm5].
rewrite <- EfsF. eapply (ajournal_sorted tfibsegs B); [exact HJ6 | exact HSORT0]. }
{ exact HS. }
cbv beta. intros W7 c7 Hwle7 (ly' & S' & regs' & mem' & md' & k' & -> & HJ7 & Hk7 & HP7 & Ha07 & HPl & HMLE7 & (HSNK7 & Efs7 & Hso7 & HPerm7)) HAI7.
lazymatch goal with |- srealizes _ _ (ff_leaf _ ?fsL) =>
unfold ff_leaf; apply (HLEAF (LL 0 fsL []) W7); cbn [c_W c_ly c_S c_regs c_mem c_md c_p c_n] end.
{ pose proof HJ7 as (_ & _ & _ & Hwle07 & _). exact Hwle07. }
{ exact HAI7. }
exists ly', S', regs', mem', md', k'. split; [reflexivity|].
unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_T] in HJ7, HMLE7, HPerm7.
change ACfn.LLVMF_STK with LLVMF_STK. change ACfn.EV_LIB with EV_LIB. fold RTFP.
split; [exact HJ7|]. split; [exact Hk7|]. split; [exact HP7|]. split; [exact Ha07|].
split; [exact HPerm7|].
split; [exact (ajournal_fds_restored tfibsegs B tfib_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HSNK0 HSNK7)|].
split; [exact Efs7|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hso7|].
split; [exact HSNK7|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 HAM0)|].
split; [rewrite <- HTX; exact HMLE7|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; clear - Hi Hn0; lia|].
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm7|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; clear - Hnpos Heq0; lia | exact Hi].
- apply HnFPs. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & _). clear - Hi Hp4096. lia.
}
}
{
intros Hgo Hsg W4 c4 Hwle4 HAI4 HpostB. unfold tnewgif_postB1, apost_base in HpostB.
destruct HpostB as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & HP4 & res & Ha04 & HAM4 & HMLEc & Hres0 & so & fo & HatO & HwfO & Hfo0 & HcfrO & HcW & HcH & Hcattr & Hccur & Hcih & Hcgen & Hcngp & HPerm4 & HownO & HRELO & HLENO).
unfold ff_content. rewrite Hsg.
set (NO := w16 * h16) in *.
assert (HNO1 : 1 <= NO <= 100000000).
{ unfold g_opens in Hgo. cbn [YO07.g_w YO07.g_h] in Hgo. apply Bool.negb_true_iff in Hgo. apply Bool.orb_false_iff in Hgo. destruct Hgo as [Hw0 Hh0].
apply Z.eqb_neq in Hw0. apply Z.eqb_neq in Hh0. subst NO. clear - Hw0 Hh0 Rw Rh HNle. nia. }
eapply (srz_enter tfibsegs W4); [exact HAI4|]. clear HAI4. rewrite Rra.
rewrite EspX in HJc.
assert (HnFPs : forall a, 1 <= a -> ~ inFP RTFP a) by (intros a Ha (r & [<-|[]] & Hr); cbn in Hr; clear - Ha Hr; lia).
pose proof (ajournal_sub_tok tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3r HJc
ltac:(replace TNEWGIFX_STK with 18816 by reflexivity; rewrite FFS; clear - Hsp1; lia) ltac:(clear - Hsp1; lia)
ltac:(intros a Ha; left; exact Ha)) as HJ4. cbn [app] in HJ4.
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1 OcfgX AF EraX Es0X.
pose proof (proj1 HJ4) as HAR4.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs4 & _). cbn [app] in Hfrs4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(2, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
vkeep Vp (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
vkeep Vn (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
vkeep Vc (w_H W4) mem4 ltac:(pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Hi Hsp1 HSPB C1 FFS; lia).
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_fshadow_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8) _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; clear; lia
| unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF8lo; unfold SB in *; lia | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_frame_sub B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 75%nat F _ _ _ _ _ 2 fpos HJc);
[ evalE AG | exact Hfin3 | rewrite EFA3; fold F; clear; lia | rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha; apply HnFPs; clear - Ha HF4096; lia | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 70%nat); [exact HJc | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_sub tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat); [exact HJc | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
clear Usp3 Ugp Utp UF. rebv HS E70 RF B70 B75.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
assert (Hsub4 : forall x, In x (ablocks B ly3 S3) -> In x (ablocks B ly4 S4))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; apply in_app_iff; right; right; exact Hx).
assert (Hcg4 : forall x, In x (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> In x (ablocks B ly4 S4)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx | [<- | []]]; [left; exact Hx | right; left; reflexivity]. }
reshok HS.
aj_run_tok tfibtbl_lib_ok HS HJ4 SHOK RTBspan.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA4.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img).
cgif_kept_run HFr Hcg4 HJ4 Hfin4 EFA4 AG KA.
unrunRD HFr Zsm Usp B70 Hsp1 UN2. clear_frames.
vkeepUN UN2 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN2.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HRELr : cgif_relA tfibsegs tfib_K (mrestrict (w_H W4) (ms_mem msX)) mdX so fo NO GPAL (gs_new w16 h16 attr' ngp 0 GPAL));
[ eapply (cgif_relA_keptX tfib_K); [| | destruct md4; reflexivity | destruct md4; reflexivity | exact HRELO];
[ intros b sz i Hb Hi; apply (mbyte_of_aview tfibsegs); apply (KA b sz Hb); pose proof (le_req_size sz); clear - Hi H; lia
| intros a Ha; apply (mbyte_of_aview tfibsegs); apply Himgv; exact (proj1 (ail_env _ _ _ AIL a Ha)) ]
| ] end.
clear HUP.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wq ?mq _ _ =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H Wq) mq a = aview tfibsegs (w_H W) mem a)
by (intros a Ha; pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia) end.
clear EspX. rreg HS (@BV 5 1 I) Rra. rreg HS (@BV 5 2 I) Rsp. rreg HS (@BV 5 3 I) Rgp. rreg HS (@BV 5 4 I) Rtp. rreg HS (@BV 5 8 I) Rs0. rreg HS (@BV 5 10 I) Ra0.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x80a08) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
lazymatch type of Ra0 with getr ?rg 10 = _ => assert (Ra0v : getr rg 10 = w64 pal) by (rewrite Ra0; rewrite ?sv_denot_SOff0; ewpeel; exact E191) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly4 (aview tfibsegs (w_H W4) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ4)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ4 as (_ & HLY4 & _ & _ & _ & _ & Hnev4 & _).
assert (HEVd : st_nev S4 < EV_MAX) by (replace YC20.EV_NEWGIF with 12 in Hnev4 by reflexivity; rewrite HEV in Hev; clear - Hnev4 Hev Hk1; lia).
pose proof (mle_station MT S S3 S4 acc (xn_newgif XN ngp) MTL HMLE HMLEc) as HMLE4.
assert (MOKf : mo_ok MT S4 (mo_free MT)).
{ apply (mok_station MT S S4 T (acc + xn_newgif XN ngp) (mo_free MT) MTL HMOK HMLE4); [apply (mo_free_nonneg MT MTL)|].
pose proof (XNle ngp ltac:(clear - Rngp; lia)) as Hxn. try rewrite Hngp in HROOM. clear - HROOM Hxn. lia. }
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 338220 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3 Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (Hpal1 : 4096 <= pal \/ pal = 0) by (destruct HpalU as [(_ & Hp0 & _) | (_ & _ & ((Hbh & _) & _) & _)]; [right; exact Hp0 | left; exact Hbh]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind tfibsegs _ _
(fun W5 c5 => exists ly5 S5 regs5 mem5 md5,
c5 = mkCfg (mkst regs5 (Z_to_bv 64 0x80a08) mem5 (seg_rom tfibsegs)) md5 /\
ajournal tfibsegs B LLVMF_STK (spZ regs) RTFP ly S W mem md [(2, fpos)] ly5 S5 W5 mem5 md5 (k + EV_NEWGIF + 1) /\
aregs_preserved (ms_regs msX) regs5 /\ Permutation (ablocks B ly5 S5) (cgif_blocks res so NO ++ (fo, FILE_BLOCK) :: ablocks B ly S) /\ frames S5 = frames S4 /\
mo_le MT S S5 (acc + xn_newgif XN ngp + mo_free MT) /\
cgif_relA tfibsegs tfib_K (mrestrict (w_H W5) mem5) md5 so fo NO GPAL (gs_new w16 h16 attr' ngp 0 GPAL) /\
exists Er : Z -> Prop, acall_kept tfibsegs B ly4 S4 W4 (ms_mem msX) W5 mem5 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a) /\
(forall b m i, In (b, m) (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> 0 <= i < req_size m -> ~ Er (b + i)))) end.
{ destruct HpalU as [(Ha4 & Hp0 & Eab3 & _) | (Ha4 & Hp1 & (Hbh1 & Hbh2 & Hb16 & Eab3 & Hawr & Haft) & _)].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree_null04_sub tfibsegs B LAWS tfib_segs_low MT AFREEN4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4)
| ] end.
+ rewrite Ra0v, Hp0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split; [eapply Permutation_trans; [exact HPerm5|]; rewrite <- Eab3; exact HPerm4|]. split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
split.
{ destruct (ajournal_nil_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJfs) as [Efds5 Efs5].
eapply (cgif_relA_keptX tfib_K); [| | exact Efds5 | exact Efs5 | exact HRELr].
- intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (proj1 (proj2 HK) b sz i (Hcg4 _ Hb)); [pose proof (le_req_size sz); clear - Hi H; lia | exact (fun HF : False => HF)].
- intros a Ha. apply (mbyte_of_aview tfibsegs). destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). exact (proj1 (proj2 (proj2 HK)) a Hi Hns He). }
exists (fun _ => False). split; [exact HK|].
repeat split; intros; exact (fun HF : False => HF).
-
assert (Hpt3 : In (pal, 3 * ngp) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
pose proof (Hsub4 _ Hpt3) as Hpt4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pal (3 * ngp) (proj1 HJ4) Hpt4) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (sep_block_frame tfibsegs _ LAWS ly4 S4 _ _ _ pal (3 * ngp) 2 fpos (proj1 HJ4) Hpt4 Hfin4) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA4 in HdFP. fold F in HdFP.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (afree04_sub tfibsegs B LAWS tfib_segs_low MT AFREE4 W4 (ms_regs msX) (ms_mem msX) LLVMF_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly4 S4 mdX (k + EV_NEWGIF) pal (3 * ngp) (sp1 - spZ regs) (Z_to_bv 64 0x80a08) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ4 Hpt4)
| ] end.
+ exact Ra0v.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 3%nat) by (clear; lia). rewrite (EE 3%nat (@BV 5 3 I) eq_refl). exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite (AG 4%nat) by (clear; lia). rewrite (EE 4%nat (@BV 5 4 I) eq_refl). exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVd.
+ apply (achain_chain_pre ly4 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x52a6c by (rewrite HBcode; reflexivity). rewrite (tl_universe B TL).
apply (rt_trace_in 0x52a6c 0x80a08); [exact Hra | exact EraX | right; left; split; reflexivity].
+ intros Hin i Hi. exfalso. exact (inFP_nil _ (Haft Hin i Hi)).
+ exact MOKf.
+ cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & Ebl4 & Ebl5) & Hfrs5 & HK & HMLEf & HJfs).
exists ly5, S5, regs5, mem5, md5. split; [reflexivity|]. split; [exact HJ5|]. split; [exact HP5|].
split.
{ rewrite Ebl5. rewrite <- (app_nil_r (cgif_blocks res so NO ++ (fo, FILE_BLOCK) :: ablocks B ly S)).
apply (@Permutation_app_inv _ l1 l2 (cgif_blocks res so NO ++ (fo, FILE_BLOCK) :: ablocks B ly S) [] (pal, 3 * ngp)). rewrite <- Ebl4.
eapply Permutation_trans; [exact HPerm4|]. rewrite Eab3. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl. }
split; [exact Hfrs5|].
split; [exact (mle_station MT S S4 S5 _ _ MTL HMLE4 HMLEf)|].
assert (Hclf : ~ YI16.sink_open_fp (ablocks_fp [(pal, 3 * ngp)])) by (apply sink_closed_ablocks_fp; constructor; [cbn [fst]; clear - Hbh1; lia | constructor]).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia).
assert (HsepP : forall b m i, In (b, m) (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> 0 <= i < req_size m -> ~ (pal <= b + i < pal + req_size (3 * ngp))).
{ intros b m i Hb Hi Hx.
assert (Hne : (b, m) <> (pal, 3 * ngp)).
{ intros Ebm. rewrite Ebm in Hb.
eapply (ablocks_perm_twice B LAWS _ _ _ _ _ (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) (ablocks B ly3 S3) (pal, 3 * ngp) (proj1 HJ4)); [| exact Hb | exact Hpt3].
rewrite <- app_assoc. exact HPerm4. }
pose proof (sep_blocks tfibsegs _ LAWS ly4 S4 _ _ _ b m pal (3 * ngp) (proj1 HJ4) (Hcg4 _ Hb) Hpt4 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hi Hx. lia. }
split.
{ destruct (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hclf HJfs) as [Efds5 Efs5].
eapply (cgif_relA_keptX tfib_K); [| | exact Efds5 | exact Efs5 | exact HRELr].
- intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (proj1 (proj2 HK) b sz i (Hcg4 _ Hb)); [pose proof (le_req_size sz); clear - Hi H; lia | exact (HsepP b sz i Hb ltac:(pose proof (le_req_size sz); clear - Hi H; lia))].
- intros a Ha. apply (mbyte_of_aview tfibsegs). destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & He). exact (proj1 (proj2 (proj2 HK)) a Hi Hns He). }
exists (fun a => pal <= a < pal + req_size (3 * ngp)). split; [exact HK|].
split; [intros a Ha Hx; clear - Ha Hx HdFP; lia|]. split; [intros a Ha Hx; clear - Ha Hx Hph_ia C3; unfold SB in *; zone_lia|]. exact HsepP. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPerm5 & Hfrs5 & HMLE5 & HREL5 & Er & HK & HErF & HErLo & HErB).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Ra0v Vra Vs0 Hch1.
pose proof (proj1 HJ5) as HAR5.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
assert (Hfin5 : In (2, fpos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
assert (Hfrs5' : frames S5 = [(2, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA5 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
vkeep Vp (w_H W5) mem5 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vn (w_H W5) mem5 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
vkeep Vc (w_H W5) mem5 ltac:(apply (proj1 HK); [clear - Hi Hsp1 HSPB C1 FFS; lia | clear - Hi Hsp1; lia]).
reseatL HS HJ5 HP5 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| right; unfold shadow_addr; rewrite EFA4, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hx; exact (HErLo a ltac:(clear - Ha HF8c HF8lo HFceil C1; unfold SB in *; lia) Hx)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalE AG | exact Hfin4
| left; rewrite EFA4; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hx; exact (HErF a ltac:(clear - Ha; lia) Hx)
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ5 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar4 | exact Kguar5 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar4 | exact Kuar5 | clear; lia] ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rebv HS E70 RF B70 B75. pose proof Rres as Rresn.
assert (KF : forall b sz, In (b, sz) (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> blk_kept (w_H W4) (w_H W5) (ms_mem ms0) mem5 b (req_size sz))
by (intros b sz Hb; exact (blk_kept_acall B _ _ _ _ _ _ _ _ _ b sz HK (Hcg4 _ Hb) (fun i Hi => HErB b sz i Hb Hi))).
clear Usp3 Ugp Utp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
assert (Ugp : ew Ev 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
assert (Utp : ew Ev 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)) end.
reshok HS.
srr_branch_tok tfibtbl_lib_ok HS SHOK RTBspan.
assert (Hresrng : 0 <= res < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ res CGIF_SIZE (proj1 HJ4) (Hcg4 _ ltac:(apply in_app_iff; left; apply cgif_blocks_in_g))) as (_ & Hr4096 & Hrceil & _).
pose proof (le_req_size CGIF_SIZE ltac:(unfold CGIF_SIZE; clear; lia)). unfold CGIF_SIZE in *. clear - Hr4096 Hrceil C1 H. lia. }
1: { lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => lazymatch type of Rresn with ew _ ?ng = _ => hc_atom H ng res Rresn ltac:(exact Hresrng) end).
hc_prop Hc. exfalso. exact (Hres0 Hc). }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
assert (Hcg5 : forall x, In x (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> In x (ablocks B ly5 S5))
by (intros x Hx; eapply Permutation_in; [apply Permutation_sym; exact HPerm5|]; apply in_app_iff in Hx; apply in_app_iff; destruct Hx as [Hx|[<-|[]]]; [left; exact Hx | right; left; reflexivity]).
reshok HS.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RTBspan 0x80a0c.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA5.
rename Himgv into HimgvR2.
imgv_run HFr AG ltac:(clear - Hsp1 Hceil Hslo Hstk0 FFS C1 C3 HF8lo HF8hi HF8c HFceil HF4096 HFhigh_img). rename Himgv into HimgvF.
cgif_kept_run HFr Hcg5 HJ5 Hfin5 EFA5 AG KB.
unrunRD HFr Zsm Usp B70 Hsp1 UN3. clear_frames.
vkeepUN UN3 Vp Vn Vc ltac:(first [clear - Hi Hsp1 HSPB C1 FFS; lia | subst Zsm; cbn beta; clear - Hi Hsp1 HFceil Hceil Hslo FFS C1; lia]). clear UN3.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
rreg HS (20%bv : bv 5) R19.
add_atom_win HS 195%nat (Z_to_bv 64 res) E195.
ws_pin HS (20%bv : bv 5) (SOff 195 0) R19 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E195; symmetry; ewpeel; unfold w64 in Rresn; exact Rresn).
ra_join_win HS ss_F 200%nat rt_F_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
eapply SRr_mono;
[ eapply (RFX (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)
(mkRTXC pl aM Kl (YO07.mkG w16 h16 attr' gen' ngp GPAL) (skipn (Z.to_nat cur) (zbytes pl)) res fo NO)
Ev _ _ ly5 S5 Wg msF mdF HBASE0)
| cbv beta; intros W7 c7 _ HP7; unfold PTF, PT, fsFIN, FILE_X in HP7; cbn [x_K c_md x_G x_rest] in HP7; rewrite Efs; exact HP7 ] end end.
{   split; [exact HXB1|]. split; [exact Hcfg|]. split; [exact Hgo|]. split; [exact Hsg|].
split; [reflexivity|]. split; [exact HNO1 | exact Hfo0]. }
{ lazymatch goal with |- rt_E _ ?Ev => idtac end.
repeat (lazymatch goal with |- rt_E _ (havoc _ _ _) => apply rt_E_havoc; [clear; cbn; lia|] | |- rt_E _ (ewset _ _ _) => apply rt_E_ewset; [clear; cbn; lia|] end).
unfold rt_E, rt_F, rt_FL; cbn [c_ly c_fpos c_E0 c_sp1]. split; [assumption|]; repeat (split; [eassumption|]); eassumption. }
{ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos]. exact HJ5. }
{ cbn [c_fpos]. rewrite Hfrs5. exact Hfrs4'. }
{ cbn [c_S]. exact HMLE5. }
{
red. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0 c_T x_pl x_aM x_K x_G x_rest x_gp x_f x_N].
split; [replace EV_NEWGIF with 12 by reflexivity; clear - Hk1; lia|].
split; [unfold ACC_F, RT_NEED1; cbn [x_G YO07.g_ngp]; pose proof (mo_free_nonneg MT MTL) as Hf1; clear - Hacc Hf1; lia|].
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wf) ?msf) =>
assert (KALL : forall b sz, In (b, sz) (cgif_blocks res so NO ++ [(fo, FILE_BLOCK)]) -> blk_kept (w_H W4) (w_H Wf) mem4 (ms_mem msf) b (req_size sz))
by (intros b sz Hb; eapply blk_kept_trans; [exact (KA b sz Hb)|]; eapply blk_kept_trans; [exact (KF b sz Hb) | exact (KB b sz Hb)]) end.
exists so, cur, (gs_new w16 h16 attr' ngp 0 GPAL). cbn [x_gp x_N x_f x_G x_pl x_rest].
split.
{ unfold rt_objX. cbn [c_n c_ly c_S x_gp x_N x_f x_G].
split; [exact E195|]. split; [exact E194|]. split; [exact Hn14|].
split.
{ lazymatch goal with |- xcgif_at _ _ _ _ _ (mrestrict (w_H ?Wf) ?mf) _ _ => apply (xcgif_at_blocks_kept wfn _ _ _ (w_H W4) (w_H Wf) mem4 mf res so NO HatO) end.
intros b sz Hb. apply KALL. apply in_app_iff. left. exact Hb. }
split; [exact HwfO|].
split; [unfold gcfg_of; rewrite HcW, HcH, Hcattr, Hcgen, Hcngp; reflexivity|].
cbn [app]. exact HPerm5. }
split.
{ unfold rt_stm. cbn [c_sp1 c_p c_n]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc | exact Rcur]. }
split.
{ split.
- lazymatch goal with |- cgif_relA _ _ (mrestrict (w_H ?Wf) (ms_mem ?msf)) ?mdf _ _ _ _ _ =>
eapply (cgif_relA_keptX tfib_K); [| | destruct md5; reflexivity | destruct md5; reflexivity | exact HREL5] end.
+ intros b sz i Hb Hi. apply (mbyte_of_aview tfibsegs). apply (KB b sz (Hb)). pose proof (le_req_size sz). clear - Hi H. lia.
+ intros a Ha. apply (mbyte_of_aview tfibsegs). apply HimgvF. exact (proj1 (ail_env _ _ _ AIL a Ha)).
- cbn [YO07.g_gpal]. clear - HLENO. lia. }
unfold LF, FILE_X, ff_file, loop_file. cbn [x_G x_rest x_pl]. rewrite gs0_gs_new. cbn [YO07.g_w YO07.g_h YO07.g_attr YO07.g_ngp YO07.g_gpal]. reflexivity. }
{ exact HS. } }
Qed.
Definition lx_E := lx_E_aux I.
End d.
End c.
