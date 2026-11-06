(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: segment DUP of pj_set's image-B walk (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of
   lib/B/Prog/pj_set_defs.v). lib/B/Prog/pj_set_dup_mid.v walks the cut pjs_DUP (+0xa8) through fuzz_strdup's
   stated text to the state `pjsd_C` at +0xb0; this file walks the straight-line stretch +0xb0 .. +0x1a4 from
   there, proving every UBSan guard and every inline ASan check NOT taken, and ends in pjs_FAILc (+0x7c, the
   strdup refusal) or pjs_TAIL (+0x50, the join), whose segment statements are premises. Only the two stores of the
   stretch change memory; each hands on its memnorm keep (pj_set_dup_step.v pjsd_sd), which the two exits compose
   with the cut's (pjs_invR's last conjunct). The cut is after grow, so the walk's journal is at the re-hiding
   relation WLE' (YA0nH.wle' over preset's zone): the stretch is stepped plainly under YGcfRhLift.ra_rh_of_SRr, the
   two stores update the journal by YCbqG.v ajournal_x_exec_frR at WLE'.
   proves no function (kind: segment lemma).
   Numerals: 48 / 56 (LENGTH: frame, struct); 8 / 24 / 32 / 40 (LENGTH: the struct's field offsets); 7 (LENGTH:
   the 8-byte alignment mask); 60 / 61 / 63 / 64 (LENGTH: shift widths); 2 ^ 54 (LENGTH: the capacity bound);
   pc offsets DERIVED; register numbers 0, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 20 (WORD). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
S1ImgB pj_set_defs pj_set_glue pj_set_steps pj_set_trans pj_set_vis
pj_set_dup_step pj_set_dup_sep pj_set_dup_tree pj_set_dup_mid pj_set_dup_failc pj_set_dup_tailc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfRhLift YSRrG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the arithmetic of the instrumented checks: every register of the stretch is `w64` of a Z ---- *)
Lemma pjsd_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. apply unsigned_lit_small. exact Ha. Qed.

Lemma pjsd_s64 : forall a, 0 <= a < 2 ^ 63 -> bv_signed (w64 a) = a.
Proof.
intros a Ha. unfold w64, bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a (2 ^ 64)) by lia. rewrite (Z.mod_small (a + 2 ^ 63) (2 ^ 64)) by lia. lia.
Qed.

Lemma pjsd_ceq_f : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> c_eq (w64 a) (w64 b) = false.
Proof.
intros a b Ha Hb Hne. unfold c_eq. apply bv_eqb_neq. intros E.
apply (f_equal bv_unsigned) in E. rewrite !pjsd_u64 in E by lia. exact (Hne E).
Qed.

Lemma pjsd_ceq_t : forall a b, a = b -> c_eq (w64 a) (w64 b) = true.
Proof. intros a b ->. unfold c_eq. apply bv_eqb_refl. Qed.

Lemma pjsd_cltu_f : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> b <= a -> c_ltu (w64 a) (w64 b) = false.
Proof.
intros a b Ha Hb Hle. rewrite c_ltu_ltb, !pjsd_u64 by lia. apply Z.ltb_ge. lia.
Qed.

Lemma pjsd_v_addi : forall a imm, 0 <= a < 2 ^ 64 -> v_addi (w64 a) imm = w64 (a + imm).
Proof. intros a imm Ha. unfold v_addi, w64. rewrite pjsd_u64 by lia. reflexivity. Qed.

Lemma pjsd_v_add : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_add (w64 a) (w64 b) = w64 (a + b).
Proof. intros a b Ha Hb. unfold v_add, w64. rewrite !pjsd_u64 by lia. reflexivity. Qed.

Lemma pjsd_v_sub : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_sub (w64 a) (w64 b) = w64 (a - b).
Proof. intros a b Ha Hb. unfold v_sub, w64. rewrite !pjsd_u64 by lia. reflexivity. Qed.

Lemma pjsd_v_xor : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_xor (w64 a) (w64 b) = w64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor, w64. rewrite !pjsd_u64 by lia. reflexivity. Qed.

Lemma pjsd_v_andi : forall a m, 0 <= a < 2 ^ 64 -> 0 <= m < 2 ^ 64 -> v_andi (w64 a) m = w64 (Z.land a m).
Proof.
intros a m Ha Hm. unfold v_andi, w64. rewrite pjsd_u64 by lia.
replace (bv_wrap 64 m) with m by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; lia). reflexivity.
Qed.

Lemma pjsd_v_srli : forall a s, 0 <= a < 2 ^ 64 -> 0 <= s -> v_srli (w64 a) s = w64 (a / 2 ^ s).
Proof.
intros a s Ha Hs. unfold v_srli, w64. rewrite pjsd_u64 by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma pjsd_v_slli : forall a s, 0 <= a < 2 ^ 64 -> 0 <= s -> v_slli (w64 a) s = w64 (a * 2 ^ s).
Proof.
intros a s Ha Hs. unfold v_slli, w64. rewrite pjsd_u64 by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma pjsd_v_srai : forall a s, 0 <= a < 2 ^ 63 -> 0 <= s -> v_srai (w64 a) s = w64 (a / 2 ^ s).
Proof.
intros a s Ha Hs. unfold v_srai, w64. rewrite pjsd_s64 by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma pjsd_v_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (w64 a) (w64 b) = w64 (if a <? b then 1 else 0).
Proof.
intros a b Ha Hb. unfold v_sltu, c_ltu, w64. rewrite c_ltu_ltb, !pjsd_u64 by lia.
destruct (a <? b); reflexivity.
Qed.

Lemma pjsd_v_sltiu : forall a m, 0 <= a < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  v_sltiu (w64 a) m = w64 (if a <? m then 1 else 0).
Proof.
intros a m Ha Hm. unfold v_sltiu, w64. rewrite pjsd_u64 by lia.
replace (bv_wrap 64 m) with m by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; lia).
destruct (a <? m); reflexivity.
Qed.

Lemma pjsd_v_mulh0 : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> a * b < 2 ^ 64 ->
  v_mulh (w64 a) (w64 b) = w64 0.
Proof.
intros a b Ha Hb Hab. unfold v_mulh, w64. rewrite !pjsd_s64 by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma pjsd_land7 : forall a, 0 <= a -> a mod 8 = 0 -> Z.land a 7 = 0.
Proof.
intros a Ha Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact Hm.
Qed.

Lemma pjsd_land7_sum : forall a b, 0 <= a -> 0 <= b -> a mod 8 = 0 -> b mod 8 = 0 -> Z.land (a + b) 7 = 0.
Proof.
intros a b Ha Hb Hma Hmb. apply pjsd_land7; [lia|].
rewrite Z.add_mod by lia. rewrite Hma, Hmb. reflexivity.
Qed.

Section dp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation WLE' := (YA0nH.wle' SEGS RZ).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis VIS : pjs_g_vis B ARx.
(* a block head (8 bytes at a - cf_head) lies outside every block's user bytes: the ledger survives a write to them *)
Hypothesis HWIDE : prh_head_wide.
(* the hull budget at a run position (pj_set_defs.v pjs_g_hull), for fuzz_strdup's call (pj_set_dup_mid.v) *)
Hypothesis HULL : @pjs_g_hull cp.

Lemma pjsd_getr0 : forall (regs : bvmap 5 word), getr regs (0%bv : bv 5) = w64 0.
Proof. reflexivity. Qed.

Ltac pjsd_rg n :=
  match goal with
  | |- context [getr ?rr ?x] =>
      assert_fails (constr_eq x n);
      let H := fresh "Hrg" in
      assert (H : x = n) by (apply bv_eq; vm_compute; reflexivity);
      rewrite H; clear H
  end.

Ltac pjsd_cr := repeat (first
  [ pjsd_rg (0%bv : bv 5) | pjsd_rg (1%bv : bv 5) | pjsd_rg (5%bv : bv 5) | pjsd_rg (9%bv : bv 5)
  | pjsd_rg (10%bv : bv 5) | pjsd_rg (11%bv : bv 5) | pjsd_rg (12%bv : bv 5) | pjsd_rg (13%bv : bv 5)
  | pjsd_rg (14%bv : bv 5) | pjsd_rg (15%bv : bv 5) | pjsd_rg (16%bv : bv 5) | pjsd_rg (17%bv : bv 5)
  | pjsd_rg (20%bv : bv 5) ]).

Ltac pjsd_zz := repeat (match goal with
  | |- context [getr ?rr ?x] =>
      let v := eval vm_compute in (bv_eqb x (0%bv : bv 5)) in
      match v with true => change (getr rr x) with (w64 0) end
  end).

Ltac pjsd_rv :=
  repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

(* materialize the walk's journal at the step's new model, then abstract the model: each step wraps it as
   `with_vm_backing (m_vm_lazy md) X md`, which names md twice, so without the abstraction the term doubles at
   every one of the stretch's sixty steps *)
Ltac pjsd_mat Hs X H :=
  let H' := fresh "HJm" in
  pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARx LAWS Hs WLE'
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X H) as H'; clear H; rename H' into H;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ =>
    let md' := fresh "mdx" in set (md' := m) in *; clearbody md' end.

Theorem pjsd_line : forall CTX0 dd en ly S Hp W regs mem md k,
  pjs_pre B ARx CTX0 dd en -> pjs_seg_fail B ARx CTX0 dd -> pjs_seg_tail B ARx CTX0 dd ->
  pjsd_C B ARx dd en ly S Hp W regs mem md k ->
  YA0nH.SRr' SEGS RZ W (pjs_cfg (PJS_DUP + 8) regs mem md) (pjs_FIN B ARx dd en).
Proof.
intros CTX0 dd en ly S Hp W regs mem md k HPRE HFAIL HTAIL HCUT.
(* the plain stretch, under ra_rh_of_SRr (the cut is at WLE' already) *)
apply YGcfRhLift.ra_rh_of_SRr.
pose proof HPRE as HPRE0.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM0 & _ & _ & _ & _ & _ & _ & HFWIN & HNODE0 & HHDR0 & HCAP & HSLOTO0 & HNODEW0 &
  HSLOTW0 & HWLOW & HDWD & HWF & HAPW & HDEPO & HDEPV & HCSTR0 & HKEPT0 & HKF & HLED0 & HCNT & HKLEN & HGROW & HLIVE &
  _ & _ & _ & _).
pose proof HFPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0) & HROD0 & HSTKHI0 & HRAC0).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop20).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct HCUT as (dup & Lam2 & Lam3 & peak3 & fail3 & ran3 & c & ok3 & Do & Lr & Dold & Dnew & Dr & num3 & str3 &
  kids2 & keys2 & cap2v & HCP).
pose proof HCP as (HINV & HROOM & H9 & Hdup & HLED3 & HOKS3 & HFA3 & Hok3lt & HNI & HpLam & HpLam2 & HBLK3 &
  HpD & HpDo & HoD & HoDo & HNEW & HCASE & Hncap2 & HNODE3 & HHDR3 & HSLOTS & HNODEW3 & HDATA3 & HWAP & HWCEIL & HWPRES &
  _ & _ & _ & _ & HARMD).
pose proof HINV as (HJ & HWIN & Hsp & Hra & Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & H8 & H18 & H20 & HKEPT & HPRES & HROD &
  HMN).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as HFRS. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_pres HJ) as HPRESJ. pose proof (ajxR_stk HJ) as Hast.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
rewrite app_nil_l in HFRS.
pose proof HDATA3 as (_ & HPL & HSLOTW & HCSTR & HKEPTk).
pose proof HPL as (Ho4096 & HatO & HrwO & HamrO & HownO & HraO).
pose proof HrwO as (Ho8 & HrdrwO).
(* ---- the numbers of the stretch ---- *)
assert (HSTKF : STK_pj_set dd <= STK_pj_set dd) by lia.
assert (HoTOP : js_o en + 56 <= kHighMemEnd - 1)
  by (destruct HamrO as [Hx | (Hx1 & Hx2)]; lia).
assert (Hn0 : 0 <= js_n en) by (pose proof HHDR3 as (_ & _ & _ & _ & _ & _ & (Hr & _) & _); lia).
pose proof HSLOTS as (_ & (Hnc & Hcapmax) & _ & Hslotpos).
assert (Hcappos : 0 < cap2v) by lia.
destruct (Hslotpos Hcappos) as (Hkids & Hkeys0). pose proof (Hkeys0 eq_refl) as Hkeys. clear Hkeys0.
assert (HKIDSB : 4096 + cf_head <= kids2 /\ kids2 mod 16 = 0 /\
  kids2 + 56 * cap2v <= YM05.alloc_ceiling).
{ destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
    kids2 (56 * cap2v) (js_most en) (js_own en) HLED3 Hkids) as (Hk0 & Hab & _ & Hmod & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (Hm16 & H40 & Hcl & _).
  pose proof (pjs_req (56 * cap2v + @cf_head cp) ltac:(lia)) as (Rq & _).
  split; [lia|]. split; [lia | lia]. }
assert (HKEYSB : 4096 + cf_head <= keys2 /\ keys2 mod 16 = 0 /\
  keys2 + 8 * cap2v <= YM05.alloc_ceiling).
{ destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
    keys2 (8 * cap2v) (js_most en) (js_own en) HLED3 Hkeys) as (Hk0 & Hab & _ & Hmod & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (Hm16 & H40 & Hcl & _).
  pose proof (pjs_req (8 * cap2v + @cf_head cp) ltac:(lia)) as (Rq & _).
  split; [lia|]. split; [lia | lia]. }
destruct HKIDSB as (Hkids4 & Hkids16 & Hkidscl). destruct HKEYSB as (Hkeys4 & Hkeys16 & Hkeyscl).
assert (HSPHI : YM05.alloc_ceiling <= js_sp0 en) by (unfold js_sp0 in *; lia).
assert (Hkl0 : 0 <= js_klen en) by (unfold js_klen; apply Nat2Z.is_nonneg).
assert (Hdupr : 0 <= dup < 2 ^ 64).
{ destruct HARMD as [(Hd0' & _) | (_ & EL3 & _ & _ & _ & Hdl & _)]; [lia|].
  assert (Hin : In (dup, js_klen en + 1) Lam3) by (rewrite EL3; left; reflexivity).
  destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
    dup (js_klen en + 1) (js_most en) (js_own en) HLED3 Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & Hcl & _).
  assert (Hq0 : 0 <= js_klen en + 1 + cf_head) by lia.
  destruct (pjs_req _ Hq0) as (Rq & _). lia. }
(* the four shadow bytes the stretch reads *)
assert (HRA8 : forall j, 0 <= j -> j + 8 <= 56 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (js_o en + j) 8).
{ intros j Hj1 Hj2. apply (range_addressable_sub _ _ (js_o en) 56); [exact HraO | lia | lia]. }
destruct (pjsd_sh0 W mem (js_o en + 32) (HRA8 32 ltac:(lia) ltac:(lia))
  ltac:(rewrite Z.add_mod by lia; rewrite Ho8; reflexivity)) as (b32 & Hb32r & Hb32).
destruct (pjsd_sh0 W mem (js_o en + 40) (HRA8 40 ltac:(lia) ltac:(lia))
  ltac:(rewrite Z.add_mod by lia; rewrite Ho8; reflexivity)) as (b40 & Hb40r & Hb40).
destruct (pjsd_sh0 W mem (js_o en + 24) (HRA8 24 ltac:(lia) ltac:(lia))
  ltac:(rewrite Z.add_mod by lia; rewrite Ho8; reflexivity)) as (b24 & Hb24r & Hb24).
assert (HRAK : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (keys2 + 8 * js_n en) 8).
{ exact (proj1 (pjs_vis_lam B ARx LAWS ly S Hp W mem md Lam3 peak3
    (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3 (js_most en) (js_own en) keys2 (8 * cap2v) (keys2 + 8 * js_n en) 8
    HARc HLED3 Hkeys ltac:(lia) ltac:(lia) ltac:(lia))). }
destruct (pjsd_sh0 W mem (keys2 + 8 * js_n en) HRAK
  ltac:(rewrite Z.add_mod by lia; replace (keys2 mod 8) with 0 by (symmetry; rewrite (Z.mod_divide keys2 8) by lia;
        apply (Z.divide_trans 8 16); [exists 2; reflexivity | apply Z.mod_divide; lia]);
        rewrite (Z.mul_comm 8 (js_n en)), Z.mod_mul by lia; reflexivity)) as (bK & HbKr & HbK).
(* the three header fields the stretch reads *)
pose proof HHDR3 as (_ & _ & _ & _ & HrdK & HrdY & HrdN & _).
assert (HLDN : exists bs, rdn SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 (js_o en + 40)) 8%nat = Some bs /\
  bytes_le_to_Z bs = bv_unsigned (w64 (js_n en)))
  by (apply pjsd_rd8; [exact HrdN | lia | lia]).
assert (HLDY : exists bs, rdn SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 (js_o en + 32)) 8%nat = Some bs /\
  bytes_le_to_Z bs = bv_unsigned (w64 keys2))
  by (apply pjsd_rd8; [exact HrdY | lia | lia]).
assert (HLDK : exists bs, rdn SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 (js_o en + 24)) 8%nat = Some bs /\
  bytes_le_to_Z bs = bv_unsigned (w64 kids2))
  by (apply pjsd_rd8; [exact HrdK | lia | lia]).
destruct HLDN as (bsN & HbsN & HvN). destruct HLDY as (bsY & HbsY & HvY).
destruct HLDK as (bsK & HbsK & HvK).
(* ---- the bytes of the key array, of the kid array and of the object ---- *)
assert (Hkeys8 : keys2 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hkeys16]]. }
assert (Hkids8 : kids2 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact Hkids16]]. }
assert (Hn8 : (8 * js_n en) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_mul by lia; reflexivity).
assert (HSHB : forall x, 0 <= x -> x <= kHighMemEnd -> 0 <= shadow_addr x < 2 ^ 64).
{ intros x H1 H2. unfold shadow_addr, SHADOW_OFF, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 H1 ltac:(lia)) as Hp'.
  assert (Hq' : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
assert (HKAB : In (keys2 - cf_head, 8 * cap2v + cf_head) (ablocks B ly S)).
{ destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
    keys2 (8 * cap2v) (js_most en) (js_own en) HLED3 Hkeys) as (_ & Hab & _). exact Hab. }
assert (HKIAB : In (kids2 - cf_head, 56 * cap2v + cf_head) (ablocks B ly S)).
{ destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
    kids2 (56 * cap2v) (js_most en) (js_own en) HLED3 Hkids) as (_ & Hab & _). exact Hab. }
assert (HKRQ : req_size (8 * cap2v + cf_head) = 8 * cap2v + cf_head).
{ assert (Hq0 : 0 <= 8 * cap2v + cf_head) by lia. destruct (pjs_req _ Hq0) as (_ & _ & Hq). apply Hq. lia. }
assert (HKIRQ : req_size (56 * cap2v + cf_head) = 56 * cap2v + cf_head).
{ assert (Hq0 : 0 <= 56 * cap2v + cf_head) by lia. destruct (pjs_req _ Hq0) as (_ & _ & Hq). apply Hq. lia. }
assert (HKPR : forall x, keys2 <= x < keys2 + 8 * cap2v -> apresent (w_H W) mem x).
{ intros x Hx. destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc HKAB) as (_ & _ & _ & _ & Hbpo & _).
  exact (proj1 (Hbpo x ltac:(lia))). }
assert (HKIPR : forall x, kids2 <= x < kids2 + 56 * cap2v -> apresent (w_H W) mem x).
{ intros x Hx. destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc HKIAB) as (_ & _ & _ & _ & Hbpo & _).
  exact (proj1 (Hbpo x ltac:(lia))). }
assert (HKH : forall x, keys2 <= x < keys2 + 8 * cap2v -> w_H W (Z_to_bv 64 x) = false)
  by (intros x Hx; exact (proj1 (HKPR x Hx))).
assert (HKWR : forall x, keys2 <= x < keys2 + 8 * cap2v -> writable_at SEGS (mrestrict (w_H W) mem) x)
  by (intros x Hx; exact (apresent_writable SEGS _ _ x (HKPR x Hx))).
assert (HKIMG : forall x, keys2 <= x < keys2 + 8 * cap2v -> ~ in_img SEGS x)
  by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HARc HKAB ltac:(lia))).
assert (HKIIMG : forall x, kids2 <= x < kids2 + 56 * cap2v -> ~ in_img SEGS x)
  by (intros x Hx; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HARc HKIAB ltac:(lia))).
(* the object's own 56 bytes: present, no image byte *)
assert (HOPR : forall x, js_o en <= x < js_o en + 56 -> apresent (w_H W) mem x /\ ~ in_img SEGS x).
{ intros x Hx.
  destruct HatO as [(a0 & kk & Hin & Ha1 & Hk1) | [(b & m & Hin & _ & Hb & Hm) |
    [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
      a0 kk (js_most en) (js_own en) HLED3 Hin) as (Hk0 & Hab & _).
    assert (Hq0 : 0 <= kk + cf_head) by lia. destruct (pjs_req _ Hq0) as (Rq & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc Hab) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo x ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HARc Hab ltac:(lia)).
  - assert (Hq0 : 0 <= m) by (destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hin) as (_ & _ & _ & (Hi1 & _) & _); lia).
    destruct (pjs_req _ Hq0) as (Rq & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hin) as (_ & _ & _ & _ & Hbpo & _).
    split; [exact (proj1 (Hbpo x ltac:(lia)))|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HARc Hin ltac:(lia)).
  - destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HARc Hin) as (_ & _ & Hfpo & _).
    split; [exact (proj1 (Hfpo x ltac:(lia)))|].
    exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HARc Hin ltac:(lia)).
  - unfold js_sp0 in *.
    split; [apply HPRESJ; lia|]. intros Hi. pose proof (Hsegs x Hi). lia. }
assert (HOH : forall x, js_o en <= x < js_o en + 56 -> w_H W (Z_to_bv 64 x) = false)
  by (intros x Hx; exact (proj1 (proj1 (HOPR x Hx)))).
assert (HSHR : forall x, 0 <= x -> x < kHighMemEnd -> kLowMemEnd <= shadow_addr x < kHighShadowEnd).
{ intros x H1 H2. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 H1 ltac:(lia)) as Hp'.
  assert (Hq' : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
assert (HKAPP : in_app (keys2 - cf_head) (req_size (8 * cap2v + cf_head))).
{ destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HARc HKAB) as (_ & _ & _ & Happ & _). exact Happ. }
assert (HKSH : forall p, 0 <= p -> p < kHighMemEnd ->
  ~ (keys2 + 8 * js_n en <= shadow_addr p < keys2 + 8 * js_n en + 8)).
{ intros p H1 H2 Hc. pose proof (HSHR p H1 H2) as Hr. unfold in_app in HKAPP.
  destruct HKAPP as (Ha1 & [Ha2 | (Ha2 & Ha3)]); unfold kLowShadowBeg, kHighMemBeg in *; lia. }
assert (HOSH : forall p, 0 <= p -> p < kHighMemEnd -> ~ (js_o en + 40 <= shadow_addr p < js_o en + 48)).
{ intros p H1 H2 Hc. pose proof (HSHR p H1 H2) as Hr.
  destruct HamrO as [Hx | (Hx1 & Hx2)]; unfold kLowMemEnd, kHighMemBeg, kHighShadowEnd in *; lia. }
unfold pjs_cfg.
pjs_fd (PJS_DUP + 8) HLW8 HDC8.
eapply (pjsd_beq_ft W _ _ _ _ (PJS_DUP + 8) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 12))) HLW8 HDC8).
{ pjsd_cr. pjsd_rv. rewrite H9. apply pjsd_ceq_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X8. pjsd_mat Hsegs X8 HJ.
pjs_fd (PJS_DUP + 12) HLW12 HDC12.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 12) _ _ _ _ (11%bv : bv 5) (w64 dup) (Z_to_bv 64 (BASE + (PJS_DUP + 16))) HLW12 HDC12).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite Hdup, pjsd_v_addi by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X12. pjsd_mat Hsegs X12 HJ.
pjs_fd (PJS_DUP + 16) HLW16 HDC16.
eapply (pjsd_andi W _ _ _ _ (PJS_DUP + 16) _ _ _ _ (10%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 20))) HLW16 HDC16).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_andi _ (bv_signed ?im) = _ => replace (bv_signed im) with 7 by (vm_compute; reflexivity) end. pjsd_rv. rewrite H9, pjsd_v_andi by lia. rewrite pjsd_land7 by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X16. pjsd_mat Hsegs X16 HJ.
pjs_fd (PJS_DUP + 20) HLW20 HDC20.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 20) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 24))) HLW20 HDC20).
{ pjsd_cr. pjsd_rv. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X20. pjsd_mat Hsegs X20 HJ.
pjs_fd (PJS_DUP + 24) HLW24 HDC24.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 24) _ _ _ _ (12%bv : bv 5) (w64 (js_o en + 32)) (Z_to_bv 64 (BASE + (PJS_DUP + 28))) HLW24 HDC24).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 32 by (vm_compute; reflexivity) end. pjsd_rv. rewrite H9, pjsd_v_addi by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X24. pjsd_mat Hsegs X24 HJ.
pjs_fd (PJS_DUP + 28) HLW28 HDC28.
eapply (pjsd_srli W _ _ _ _ (PJS_DUP + 28) _ _ _ _ (10%bv : bv 5) (w64 ((js_o en + 32) / 8)) (Z_to_bv 64 (BASE + (PJS_DUP + 32))) HLW28 HDC28).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 3 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srli by lia. change (2 ^ 3) with 8. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X28. pjsd_mat Hsegs X28 HJ.
pjs_fd (PJS_DUP + 32) HLW32 HDC32.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 32) _ _ _ _ (10%bv : bv 5) (w64 (shadow_addr (js_o en + 32))) (Z_to_bv 64 (BASE + (PJS_DUP + 36))) HLW32 HDC32).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite H20, pjsd_v_add by ((try (unfold SHADOW_OFF)); lia). unfold shadow_addr, SHADOW_OFF. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X32. pjsd_mat Hsegs X32 HJ.
pjs_fd (PJS_DUP + 36) HLW36 HDC36.
eapply (pjsd_lbu W _ _ _ _ (PJS_DUP + 36) _ _ _ _ (10%bv : bv 5) b32 (Z_to_bv 64 (BASE + (PJS_DUP + 40))) HLW36 HDC36).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by (apply HSHB; lia). rewrite Z.add_0_r. exact Hb32r. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X36. pjsd_mat Hsegs X36 HJ.
pjs_fd (PJS_DUP + 40) HLW40 HDC40.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 40) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 44))) HLW40 HDC40).
{ pjsd_cr. pjsd_rv. rewrite Hb32. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X40. pjsd_mat Hsegs X40 HJ.
pjs_fd (PJS_DUP + 44) HLW44 HDC44.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 44) _ _ _ _ (10%bv : bv 5) (w64 (js_o en + 40)) (Z_to_bv 64 (BASE + (PJS_DUP + 48))) HLW44 HDC44).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 40 by (vm_compute; reflexivity) end. pjsd_rv. rewrite H9, pjsd_v_addi by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X44. pjsd_mat Hsegs X44 HJ.
pjs_fd (PJS_DUP + 48) HLW48 HDC48.
eapply (pjsd_srli W _ _ _ _ (PJS_DUP + 48) _ _ _ _ (14%bv : bv 5) (w64 ((js_o en + 40) / 8)) (Z_to_bv 64 (BASE + (PJS_DUP + 52))) HLW48 HDC48).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 3 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srli by lia. change (2 ^ 3) with 8. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X48. pjsd_mat Hsegs X48 HJ.
pjs_fd (PJS_DUP + 52) HLW52 HDC52.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 52) _ _ _ _ (14%bv : bv 5) (w64 (shadow_addr (js_o en + 40))) (Z_to_bv 64 (BASE + (PJS_DUP + 56))) HLW52 HDC52).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite H20, pjsd_v_add by ((try (unfold SHADOW_OFF)); lia). unfold shadow_addr, SHADOW_OFF. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X52. pjsd_mat Hsegs X52 HJ.
pjs_fd (PJS_DUP + 56) HLW56 HDC56.
eapply (pjsd_lbu W _ _ _ _ (PJS_DUP + 56) _ _ _ _ (13%bv : bv 5) b40 (Z_to_bv 64 (BASE + (PJS_DUP + 60))) HLW56 HDC56).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by (apply HSHB; lia). rewrite Z.add_0_r. exact Hb40r. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X56. pjsd_mat Hsegs X56 HJ.
pjs_fd (PJS_DUP + 60) HLW60 HDC60.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 60) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 64))) HLW60 HDC60).
{ pjsd_cr. pjsd_rv. rewrite Hb40. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X60. pjsd_mat Hsegs X60 HJ.
pjs_fd (PJS_DUP + 64) HLW64 HDC64.
eapply (pjsd_ld W _ _ _ _ (PJS_DUP + 64) _ _ _ _ bsN (13%bv : bv 5) (w64 (js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 68))) HLW64 HDC64).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. rewrite Z.add_0_r. exact HbsN. }
{ exact HvN. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X64. pjsd_mat Hsegs X64 HJ.
pjs_fd (PJS_DUP + 68) HLW68 HDC68.
eapply (pjsd_ld W _ _ _ _ (PJS_DUP + 68) _ _ _ _ bsY (16%bv : bv 5) (w64 keys2) (Z_to_bv 64 (BASE + (PJS_DUP + 72))) HLW68 HDC68).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. rewrite Z.add_0_r. exact HbsY. }
{ exact HvY. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X68. pjsd_mat Hsegs X68 HJ.
pjs_fd (PJS_DUP + 72) HLW72 HDC72.
eapply (pjsd_slli W _ _ _ _ (PJS_DUP + 72) _ _ _ _ (15%bv : bv 5) (w64 (8 * js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 76))) HLW72 HDC72).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_slli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 3 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_slli by lia. f_equal; try (change (2 ^ 3) with 8); lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X72. pjsd_mat Hsegs X72 HJ.
pjs_fd (PJS_DUP + 76) HLW76 HDC76.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 76) _ _ _ _ (12%bv : bv 5) (w64 (keys2 + 8 * js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 80))) HLW76 HDC76).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_add by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X76. pjsd_mat Hsegs X76 HJ.
pjs_fd (PJS_DUP + 80) HLW80 HDC80.
eapply (pjsd_sltu W _ _ _ _ (PJS_DUP + 80) _ _ _ _ (17%bv : bv 5) (w64 1) (Z_to_bv 64 (BASE + (PJS_DUP + 84))) HLW80 HDC80).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_sltu by lia. f_equal; replace (0 <? keys2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X80. pjsd_mat Hsegs X80 HJ.
pjs_fd (PJS_DUP + 84) HLW84 HDC84.
eapply (pjsd_sltiu W _ _ _ _ (PJS_DUP + 84) _ _ _ _ (5%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 88))) HLW84 HDC84).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_sltiu _ (bv_signed ?im) = _ => replace (bv_signed im) with 1 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_sltiu by lia. f_equal; replace (keys2 + 8 * js_n en <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X84. pjsd_mat Hsegs X84 HJ.
pjs_fd (PJS_DUP + 88) HLW88 HDC88.
eapply (pjsd_beq_ft W _ _ _ _ (PJS_DUP + 88) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 92))) HLW88 HDC88).
{ pjsd_cr. pjsd_rv. apply pjsd_ceq_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X88. pjsd_mat Hsegs X88 HJ.
pjs_fd (PJS_DUP + 92) HLW92 HDC92.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 92) _ _ _ _ (17%bv : bv 5) (w64 1) (Z_to_bv 64 (BASE + (PJS_DUP + 96))) HLW92 HDC92).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 1 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X92. pjsd_mat Hsegs X92 HJ.
pjs_fd (PJS_DUP + 96) HLW96 HDC96.
eapply (pjsd_slli W _ _ _ _ (PJS_DUP + 96) _ _ _ _ (17%bv : bv 5) (w64 (2 ^ 60)) (Z_to_bv 64 (BASE + (PJS_DUP + 100))) HLW96 HDC96).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_slli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 60 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_slli by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X96. pjsd_mat Hsegs X96 HJ.
pjs_fd (PJS_DUP + 100) HLW100 HDC100.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 100) _ _ _ _ (17%bv : bv 5) (w64 (js_n en + 2 ^ 60)) (Z_to_bv 64 (BASE + (PJS_DUP + 104))) HLW100 HDC100).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_add by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X100. pjsd_mat Hsegs X100 HJ.
pjs_fd (PJS_DUP + 104) HLW104 HDC104.
eapply (pjsd_srli W _ _ _ _ (PJS_DUP + 104) _ _ _ _ (17%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 108))) HLW104 HDC104).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 61 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srli by lia. f_equal; apply Z.div_small; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X104. pjsd_mat Hsegs X104 HJ.
pjs_fd (PJS_DUP + 108) HLW108 HDC108.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 108) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 112))) HLW108 HDC108).
{ pjsd_cr. pjsd_rv. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X108. pjsd_mat Hsegs X108 HJ.
pjs_fd (PJS_DUP + 112) HLW112 HDC112.
eapply (pjsd_bltu_ft W _ _ _ _ (PJS_DUP + 112) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 116))) HLW112 HDC112).
{ pjsd_cr. pjsd_rv. apply pjsd_cltu_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X112. pjsd_mat Hsegs X112 HJ.
pjs_fd (PJS_DUP + 116) HLW116 HDC116.
eapply (pjsd_beq_ft W _ _ _ _ (PJS_DUP + 116) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 120))) HLW116 HDC116).
{ pjsd_cr. pjsd_rv. apply pjsd_ceq_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X116. pjsd_mat Hsegs X116 HJ.
pjs_fd (PJS_DUP + 120) HLW120 HDC120.
eapply (pjsd_andi W _ _ _ _ (PJS_DUP + 120) _ _ _ _ (16%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 124))) HLW120 HDC120).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_andi _ (bv_signed ?im) = _ => replace (bv_signed im) with 7 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_andi by lia. rewrite pjsd_land7_sum by (try exact Hkeys8; try exact Hn8; lia). reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X120. pjsd_mat Hsegs X120 HJ.
pjs_fd (PJS_DUP + 124) HLW124 HDC124.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 124) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 128))) HLW124 HDC124).
{ pjsd_cr. pjsd_rv. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X124. pjsd_mat Hsegs X124 HJ.
pjs_fd (PJS_DUP + 128) HLW128 HDC128.
eapply (pjsd_srli W _ _ _ _ (PJS_DUP + 128) _ _ _ _ (16%bv : bv 5) (w64 ((keys2 + 8 * js_n en) / 8)) (Z_to_bv 64 (BASE + (PJS_DUP + 132))) HLW128 HDC128).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 3 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srli by lia. change (2 ^ 3) with 8. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X128. pjsd_mat Hsegs X128 HJ.
pjs_fd (PJS_DUP + 132) HLW132 HDC132.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 132) _ _ _ _ (16%bv : bv 5) (w64 (shadow_addr (keys2 + 8 * js_n en))) (Z_to_bv 64 (BASE + (PJS_DUP + 136))) HLW132 HDC132).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite H20, pjsd_v_add by ((try (unfold SHADOW_OFF)); lia). unfold shadow_addr, SHADOW_OFF. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X132. pjsd_mat Hsegs X132 HJ.
pjs_fd (PJS_DUP + 136) HLW136 HDC136.
eapply (pjsd_lbu W _ _ _ _ (PJS_DUP + 136) _ _ _ _ (16%bv : bv 5) bK (Z_to_bv 64 (BASE + (PJS_DUP + 140))) HLW136 HDC136).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by (apply HSHB; lia). rewrite Z.add_0_r. exact HbKr. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X136. pjsd_mat Hsegs X136 HJ.
pjs_fd (PJS_DUP + 140) HLW140 HDC140.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 140) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 144))) HLW140 HDC140).
{ pjsd_cr. pjsd_rv. rewrite HbK. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X140. pjsd_mat Hsegs X140 HJ.
pjs_fd (PJS_DUP + 144) HLW144 HDC144.
eapply (pjsd_sd W _ _ _ _ (PJS_DUP + 144) _ _ _ _ (keys2 + 8 * js_n en) (Z_to_bv 64 (BASE + (PJS_DUP + 148))) HLW144 HDC144).
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ lia. }
{ lia. }
{ intros x Hx. apply HKH. lia. }
{ intros x Hx. apply HKWR. lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X144 mem1 HW1 HA1 HM1 HG1 HP1 HQ1 HH1 HN1.
pjsd_mat Hsegs X144 HJ.
assert (HMB1 : forall x, 0 <= x < 2 ^ 64 -> ~ (keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8) ->
  mbyte SEGS (mrestrict (w_H W) mem1) x = mbyte SEGS (mrestrict (w_H W) mem) x).
{ intros x Hx Hn. unfold mbyte.
  rewrite (HM1 (Z_to_bv 64 x) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity. }
assert (Hb24r' : rdn SEGS (mrestrict (w_H W) mem1) (Z_to_bv 64 (shadow_addr (js_o en + 24))) 1%nat = Some [b24]).
{ apply byte1_rdn. rewrite (HMB1 (shadow_addr (js_o en + 24))
    ltac:(apply HSHB; lia) ltac:(apply HKSH; lia)).
  destruct (proj1 (rdn_mbytes SEGS (mrestrict (w_H W) mem) 1%nat (shadow_addr (js_o en + 24)) [b24]) Hb24r)
    as (_ & Hm). pose proof (Hm 0%nat ltac:(lia)) as Hm0. cbn [Z.of_nat nth_error] in Hm0.
  rewrite Z.add_0_r in Hm0. exact Hm0. }
assert (Hb40r' : rdn SEGS (mrestrict (w_H W) mem1) (Z_to_bv 64 (shadow_addr (js_o en + 40))) 1%nat = Some [b40]).
{ apply byte1_rdn. rewrite (HMB1 (shadow_addr (js_o en + 40))
    ltac:(apply HSHB; lia) ltac:(apply HKSH; lia)).
  destruct (proj1 (rdn_mbytes SEGS (mrestrict (w_H W) mem) 1%nat (shadow_addr (js_o en + 40)) [b40]) Hb40r)
    as (_ & Hm). pose proof (Hm 0%nat ltac:(lia)) as Hm0. cbn [Z.of_nat nth_error] in Hm0.
  rewrite Z.add_0_r in Hm0. exact Hm0. }
assert (HKODO : In (keys2, 8 * cap2v) Do).
{ pose proof HNODE3 as HN. cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & nn & ss & kk & yy & n0 & c0 & Hh & _ & _ & _ & _ & Di & EDo & _).
  pose proof HHDR3 as (_ & _ & _ & _ & _ & HY & _ & HC).
  pose proof Hh as (_ & _ & _ & _ & _ & HY' & _ & HC').
  rewrite (pjsdt_u64_uniq SEGS (mrestrict (w_H W) mem) (js_o en + 32) yy keys2 HY' HY) in EDo.
  rewrite (pjsdt_u64_uniq SEGS (mrestrict (w_H W) mem) (js_o en + 48) c0 cap2v HC' HC) in EDo.
  rewrite EDo. replace (cap2v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [app]. right. left. reflexivity. }
assert (HKODJ : forall x, js_o en <= x < js_o en + 56 -> ~ (keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8)).
{ intros x Hx Hc. pose proof HNODE3 as (_ & Hap & _).
  exact (Hap (keys2, 8 * cap2v) x HKODO ltac:(unfold pj_holdsR; cbn [fst snd]; lia) Hx). }
assert (HLDK' : exists bs, rdn SEGS (mrestrict (w_H W) mem1) (Z_to_bv 64 (js_o en + 24)) 8%nat = Some bs /\
  bytes_le_to_Z bs = bv_unsigned (w64 kids2)).
{ apply pjsd_rd8; [|lia|lia]. split; [pose proof HrdK as (Hr & _); exact Hr|].
  intros kk Hk. rewrite (HMB1 (js_o en + 24 + Z.of_nat kk) ltac:(lia)
    ltac:(apply HKODJ; lia)). pose proof HrdK as (_ & Hv). exact (Hv kk Hk). }
destruct HLDK' as (bsK1 & HbsK' & HvK1).
assert (HAWRK : forall a, keys2 + 8 * js_n en <= a < keys2 + 8 * js_n en + 8 ->
  awr_byte (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (ablocks B (js_ly en) (js_S en)) (ablocks B ly S) ly [] a \/
  wr_fp_frame (pjs_FP en) (js_S en) ly a).
{ intros a Ha. left.
  destruct HCASE as [(Hlt & Hc0 & Eki & Eky & Ecap & Edo & Edn) | (Heq & Hc2 & Ecap & Edo & Edn)].
  - right. left. split.
    + assert (HKinD : In (keys2, 8 * cap2v) (js_D en)).
      { rewrite Edn in HpDo. rewrite Edo in HpD. cbn [app] in HpD, HpDo.
        eapply Permutation_in; [exact (Permutation_sym HpD)|].
        eapply Permutation_in; [exact HpDo|]. exact HKODO. }
      exists (keys2 - cf_head, keys2 - cf_head + req_size (8 * cap2v + cf_head)). split.
      * unfold pjs_FP. right. right. unfold ablocks_fp. apply in_map_iff.
        exists (keys2 - cf_head, 8 * cap2v + cf_head). split; [reflexivity|].
        unfold prhPj_hbl. apply in_map_iff. exists (keys2, 8 * cap2v). split; [reflexivity|].
        apply in_or_app. left. exact HKinD.
      * cbn [fst snd]. lia.
    + exists (keys2 - cf_head), (8 * cap2v + cf_head). split; [exact HKAB | lia].
  - right. right. left. exists (keys2 - cf_head), (8 * cap2v + cf_head).
    split; [exact HKAB|]. split; [|lia].
    apply (HNEW keys2 (8 * cap2v)). rewrite Edn. right. left. rewrite Ecap. reflexivity. }
assert (HJ1 := ajournal_x_exec_frR SEGS B PST ARx LAWS Hsegs WLE'
  (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
  (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) []
  ly S Hp W mem _ k mem1 _
  (fun a => keys2 + 8 * js_n en <= a < keys2 + 8 * js_n en + 8)
  HJ HM1 HG1 HH1 (same_but_materialized_refl _) HAWRK).
clear HJ. rename HJ1 into HJ.
destruct HARMD as [(Hdz & EL3 & Ecf & EP3 & Hokf & HPBd) |
  (Hdn & EL3 & EP3 & Hokall3 & HBYT3 & Hdlo & Hdmod & HOdj & HWdj & HPOSd)].
{ (* dup = 0: the chosen failure branches to PJS_FAIL *)
  pjs_fd (PJS_DUP + 148) HLWF HDCF.
  eapply (pjsd_beq_tk W _ _ _ _ (PJS_DUP + 148) _ _ _ _ (Z_to_bv 64 (BASE + PJS_FAIL)) HLWF HDCF).
  { pjsd_cr. pjsd_rv. apply pjsd_ceq_t. exact Hdz. }
  { apply bv_eq. vm_compute. reflexivity. }
  intros XF. pjsd_mat Hsegs XF HJ.
  apply SRr_ret.
  eapply HFAIL; [exact HPRE0|].
  eapply (pjsd_fail_cut B ARx LAWS HWIDE CTX0 dd en ly S Hp W regs mem md k
    dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr num3 str3 kids2 keys2 cap2v
    _ mem1 _ HPRE0 HCP Hdz HA1 HM1 HP1 HN1 HJ).
  - unfold YG0d.spZ in Hsp |- *. pjsd_cr. pjsd_rv. exact Hsp.
  - pjsd_cr. pjsd_rv. exact H8.
  - pjsd_cr. pjsd_rv. exact H18.
  - pjsd_cr. pjsd_rv. exact H20.
  - intros r Hr. pjsd_cr. rewrite !getr_other by pjs_kept_ne. exact (HKEPT r Hr). }
pjs_fd (PJS_DUP + 148) HLW148 HDC148.
eapply (pjsd_beq_ft W _ _ _ _ (PJS_DUP + 148) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 152))) HLW148 HDC148).
{ pjsd_cr. pjsd_rv. apply pjsd_ceq_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X148. pjsd_mat Hsegs X148 HJ.
pjs_fd (PJS_DUP + 152) HLW152 HDC152.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 152) _ _ _ _ (9%bv : bv 5) (w64 (js_o en + 24)) (Z_to_bv 64 (BASE + (PJS_DUP + 156))) HLW152 HDC152).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 24 by (vm_compute; reflexivity) end. pjsd_rv. rewrite H9, pjsd_v_addi by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X152. pjsd_mat Hsegs X152 HJ.
pjs_fd (PJS_DUP + 156) HLW156 HDC156.
eapply (pjsd_srli W _ _ _ _ (PJS_DUP + 156) _ _ _ _ (11%bv : bv 5) (w64 ((js_o en + 24) / 8)) (Z_to_bv 64 (BASE + (PJS_DUP + 160))) HLW156 HDC156).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 3 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srli by lia. change (2 ^ 3) with 8. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X156. pjsd_mat Hsegs X156 HJ.
pjs_fd (PJS_DUP + 160) HLW160 HDC160.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 160) _ _ _ _ (11%bv : bv 5) (w64 (shadow_addr (js_o en + 24))) (Z_to_bv 64 (BASE + (PJS_DUP + 164))) HLW160 HDC160).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite H20, pjsd_v_add by ((try (unfold SHADOW_OFF)); lia). unfold shadow_addr, SHADOW_OFF. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X160. pjsd_mat Hsegs X160 HJ.
pjs_fd (PJS_DUP + 164) HLW164 HDC164.
eapply (pjsd_lbu W _ _ _ _ (PJS_DUP + 164) _ _ _ _ (11%bv : bv 5) b24 (Z_to_bv 64 (BASE + (PJS_DUP + 168))) HLW164 HDC164).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by (apply HSHB; lia). rewrite Z.add_0_r. exact Hb24r'. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X164. pjsd_mat Hsegs X164 HJ.
pjs_fd (PJS_DUP + 168) HLW168 HDC168.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 168) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 172))) HLW168 HDC168).
{ pjsd_cr. pjsd_rv. rewrite Hb24. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X168. pjsd_mat Hsegs X168 HJ.
pjs_fd (PJS_DUP + 172) HLW172 HDC172.
eapply (pjsd_lbu W _ _ _ _ (PJS_DUP + 172) _ _ _ _ (11%bv : bv 5) b40 (Z_to_bv 64 (BASE + (PJS_DUP + 176))) HLW172 HDC172).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by (apply HSHB; lia). rewrite Z.add_0_r. exact Hb40r'. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X172. pjsd_mat Hsegs X172 HJ.
pjs_fd (PJS_DUP + 176) HLW176 HDC176.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 176) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 180))) HLW176 HDC176).
{ pjsd_cr. pjsd_rv. rewrite Hb40. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X176. pjsd_mat Hsegs X176 HJ.
pjs_fd (PJS_DUP + 180) HLW180 HDC180.
eapply (pjsd_ld W _ _ _ _ (PJS_DUP + 180) _ _ _ _ bsK1 (14%bv : bv 5) (w64 kids2) (Z_to_bv 64 (BASE + (PJS_DUP + 184))) HLW180 HDC180).
{ pjsd_cr. lazymatch goal with |- rdn _ _ (v_addi _ (bv_signed ?im)) _ = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. rewrite Z.add_0_r. exact HbsK'. }
{ exact HvK1. }
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X180. pjsd_mat Hsegs X180 HJ.
pjs_fd (PJS_DUP + 184) HLW184 HDC184.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 184) _ _ _ _ (16%bv : bv 5) (w64 (js_n en + 1)) (Z_to_bv 64 (BASE + (PJS_DUP + 188))) HLW184 HDC184).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 1 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X184. pjsd_mat Hsegs X184 HJ.
pjs_fd (PJS_DUP + 188) HLW188 HDC188.
eapply (pjsd_slli W _ _ _ _ (PJS_DUP + 188) _ _ _ _ (12%bv : bv 5) (w64 (js_n en * 2 ^ 6)) (Z_to_bv 64 (BASE + (PJS_DUP + 192))) HLW188 HDC188).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_slli _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 6 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_slli by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X188. pjsd_mat Hsegs X188 HJ.
pjs_fd (PJS_DUP + 192) HLW192 HDC192.
eapply (pjsd_sub W _ _ _ _ (PJS_DUP + 192) _ _ _ _ (12%bv : bv 5) (w64 (56 * js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 196))) HLW192 HDC192).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_sub by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X192. pjsd_mat Hsegs X192 HJ.
pjs_fd (PJS_DUP + 196) HLW196 HDC196.
eapply (pjsd_add W _ _ _ _ (PJS_DUP + 196) _ _ _ _ (11%bv : bv 5) (w64 (kids2 + 56 * js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 200))) HLW196 HDC196).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_add by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X196. pjsd_mat Hsegs X196 HJ.
pjs_fd (PJS_DUP + 200) HLW200 HDC200.
eapply (pjsd_sltu W _ _ _ _ (PJS_DUP + 200) _ _ _ _ (15%bv : bv 5) (w64 1) (Z_to_bv 64 (BASE + (PJS_DUP + 204))) HLW200 HDC200).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_sltu by lia. f_equal; replace (0 <? kids2) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X200. pjsd_mat Hsegs X200 HJ.
pjs_fd (PJS_DUP + 204) HLW204 HDC204.
eapply (pjsd_sltiu W _ _ _ _ (PJS_DUP + 204) _ _ _ _ (17%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 208))) HLW204 HDC204).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_sltiu _ (bv_signed ?im) = _ => replace (bv_signed im) with 1 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_sltiu by lia. f_equal; replace (kids2 + 56 * js_n en <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X204. pjsd_mat Hsegs X204 HJ.
pjs_fd (PJS_DUP + 208) HLW208 HDC208.
eapply (pjsd_sd W _ _ _ _ (PJS_DUP + 208) _ _ _ _ (js_o en + 40) (Z_to_bv 64 (BASE + (PJS_DUP + 212))) HLW208 HDC208).
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ lia. }
{ lia. }
{ intros x Hx. apply HOH. lia. }
{ intros x Hx. exact (apresent_writable SEGS _ _ x (HP1 _ (proj1 (HOPR x ltac:(lia))))). }
{ apply bv_eq. vm_compute. reflexivity. }
intros X208 mem2 HW2 HA2 HM2 HG2 HP2 HQ2 HH2 HN2.
pjsd_mat Hsegs X208 HJ.
assert (HWK : val_mem SEGS (mrestrict (w_H W) mem1) (keys2 + 8 * js_n en) 8 dup).
{ revert HW1. pjsd_cr. pjsd_rv. rewrite pjsd_u64 by lia. exact (fun h => h). }
assert (HWN : val_mem SEGS (mrestrict (w_H W) mem2) (js_o en + 40) 8 (js_n en + 1)).
{ revert HW2. pjsd_cr. pjsd_rv. rewrite pjsd_u64 by lia. exact (fun h => h). }
assert (HAWRO : forall a, js_o en + 40 <= a < js_o en + 40 + 8 ->
  awr_byte (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
    (ablocks B (js_ly en) (js_S en)) (ablocks B ly S) ly [] a \/
  wr_fp_frame (pjs_FP en) (js_S en) ly a).
{ intros a Ha.
  assert (HinFP : inFP (pjs_FP en) a).
  { exists (js_o en, js_o en + 56). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct HatO as [(a0 & kk & Hin & Ha1 & Hk1) | [(b & m & Hin & _ & Hb & Hm) |
    [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - left. right. left. split; [exact HinFP|].
    destruct (prh_ledger_hblock B ly S Hp W mem Lam3 peak3 (js_cnt en + Z.of_nat (Datatypes.S c)) fail3 ran3
      a0 kk (js_most en) (js_own en) HLED3 Hin) as (Hk0 & Hab & _).
    assert (Hq0 : 0 <= kk + cf_head) by lia. destruct (pjs_req _ Hq0) as (Rq & _).
    exists (a0 - cf_head), (kk + cf_head). split; [exact Hab | lia].
  - left. right. left. split; [exact HinFP|].
    assert (Hq0 : 0 <= m)
      by (destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HARc Hin) as (_ & _ & _ & (Hi1 & _) & _); lia).
    destruct (pjs_req _ Hq0) as (Rq & _).
    exists b, m. split; [exact Hin | lia].
  - right. split; [exact HinFP|]. exists cid, pos. split; [rewrite <- HFRS; exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - left. left. unfold js_sp0 in *. lia. }
assert (HJ2 := ajournal_x_exec_frR SEGS B PST ARx LAWS Hsegs WLE'
  (STK_pj_set dd + js_d en) (js_sp0 en + js_d en) (pjs_FP en)
  (js_ly en) (js_S en) (js_Hp en) (js_W en) (js_mem en) (js_md en) []
  ly S Hp W mem1 _ k mem2 _
  (fun a => js_o en + 40 <= a < js_o en + 40 + 8)
  HJ HM2 HG2 HH2 (same_but_materialized_refl _) HAWRO).
clear HJ. rename HJ2 into HJ.
pjs_fd (PJS_DUP + 212) HLW212 HDC212.
eapply (pjsd_beq_ft W _ _ _ _ (PJS_DUP + 212) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 216))) HLW212 HDC212).
{ pjsd_cr. pjsd_rv. apply pjsd_ceq_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X212. pjsd_mat Hsegs X212 HJ.
pjs_fd (PJS_DUP + 216) HLW216 HDC216.
eapply (pjsd_bltu_ft W _ _ _ _ (PJS_DUP + 216) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 220))) HLW216 HDC216).
{ pjsd_cr. pjsd_rv. apply pjsd_cltu_f; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X216. pjsd_mat Hsegs X216 HJ.
pjs_fd (PJS_DUP + 220) HLW220 HDC220.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 220) _ _ _ _ (10%bv : bv 5) (w64 56) (Z_to_bv 64 (BASE + (PJS_DUP + 224))) HLW220 HDC220).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 56 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X220. pjsd_mat Hsegs X220 HJ.
pjs_fd (PJS_DUP + 224) HLW224 HDC224.
eapply (pjsd_mulh W _ _ _ _ (PJS_DUP + 224) _ _ _ _ (10%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 228))) HLW224 HDC224).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_mulh0 by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X224. pjsd_mat Hsegs X224 HJ.
pjs_fd (PJS_DUP + 228) HLW228 HDC228.
eapply (pjsd_srai W _ _ _ _ (PJS_DUP + 228) _ _ _ _ (12%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 232))) HLW228 HDC228).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_srai _ (bv_unsigned ?sh) = _ => replace (bv_unsigned sh) with 63 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_srai by lia. f_equal; apply Z.div_small; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X228. pjsd_mat Hsegs X228 HJ.
pjs_fd (PJS_DUP + 232) HLW232 HDC232.
eapply (pjsd_xor W _ _ _ _ (PJS_DUP + 232) _ _ _ _ (10%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 236))) HLW232 HDC232).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_xor by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X232. pjsd_mat Hsegs X232 HJ.
pjs_fd (PJS_DUP + 236) HLW236 HDC236.
eapply (pjsd_sltu W _ _ _ _ (PJS_DUP + 236) _ _ _ _ (10%bv : bv 5) (w64 0) (Z_to_bv 64 (BASE + (PJS_DUP + 240))) HLW236 HDC236).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. pjsd_rv. rewrite pjsd_v_sltu by lia. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X236. pjsd_mat Hsegs X236 HJ.
pjs_fd (PJS_DUP + 240) HLW240 HDC240.
eapply (pjsd_bne_ft W _ _ _ _ (PJS_DUP + 240) _ _ _ _ (Z_to_bv 64 (BASE + (PJS_DUP + 244))) HLW240 HDC240).
{ pjsd_cr. pjsd_rv. unfold c_eq. apply bv_eqb_refl. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X240. pjsd_mat Hsegs X240 HJ.
pjs_fd (PJS_DUP + 244) HLW244 HDC244.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 244) _ _ _ _ (12%bv : bv 5) (w64 56) (Z_to_bv 64 (BASE + (PJS_DUP + 248))) HLW244 HDC244).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 56 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X244. pjsd_mat Hsegs X244 HJ.
pjs_fd (PJS_DUP + 248) HLW248 HDC248.
eapply (pjsd_addi W _ _ _ _ (PJS_DUP + 248) _ _ _ _ (10%bv : bv 5) (w64 (kids2 + 56 * js_n en)) (Z_to_bv 64 (BASE + (PJS_DUP + 252))) HLW248 HDC248).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
{ pjsd_cr. lazymatch goal with |- v_addi _ (bv_signed ?im) = _ => replace (bv_signed im) with 0 by (vm_compute; reflexivity) end. pjsd_rv. rewrite pjsd_v_addi by lia. f_equal; lia. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X248. pjsd_mat Hsegs X248 HJ.
pjs_fd (PJS_DUP + 252) HLW252 HDC252.
eapply (pjs_step_j W _ _ _ _ (PJS_DUP + 252) _ _ _ (Z_to_bv 64 (BASE + PJS_TAIL)) HLW252 HDC252).
{ vm_compute. reflexivity. }
{ apply bv_eq. vm_compute. reflexivity. }
intros X252. pjsd_mat Hsegs X252 HJ.
assert (HAG2 : forall x, 0 <= x < 2 ^ 64 -> ~ (keys2 + 8 * js_n en <= x < keys2 + 8 * js_n en + 8) ->
  ~ (js_o en + 40 <= x < js_o en + 48) -> aview SEGS (w_H W) mem2 x = aview SEGS (w_H W) mem x).
{ intros x Hx H1 H2. rewrite (HA2 x Hx ltac:(lia)). exact (HA1 x Hx H1). }
assert (HMR2 : forall x : word, ~ (keys2 + 8 * js_n en <= bv_unsigned x < keys2 + 8 * js_n en + 8) ->
  ~ (js_o en + 40 <= bv_unsigned x < js_o en + 48) ->
  mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x).
{ intros x H1 H2. rewrite (HM2 x ltac:(lia)). exact (HM1 x H1). }
assert (HWK2 : val_mem SEGS (mrestrict (w_H W) mem2) (keys2 + 8 * js_n en) 8 dup).
{ intros kk Hk. unfold mbyte.
  assert (Hd2 : ~ (js_o en + 40 <= keys2 + 8 * js_n en + Z.of_nat kk < js_o en + 40 + 8))
    by (intros Hc; exact (HKODJ (keys2 + 8 * js_n en + Z.of_nat kk) ltac:(lia) ltac:(lia))).
  rewrite (HM2 (Z_to_bv 64 (keys2 + 8 * js_n en + Z.of_nat kk))
    ltac:(rewrite unsigned_lit_small by lia; exact Hd2)).
  exact (HWK kk Hk). }
apply SRr_ret.
eapply HTAIL; [exact HPRE0|].
eapply (pjsd_tail_cut B ARx LAWS VIS HWIDE CTX0 dd en ly S Hp W regs mem md k
  dup Lam2 Lam3 peak3 fail3 ran3 c ok3 Do Lr Dold Dnew Dr num3 str3 kids2 keys2 cap2v
  _ mem2 _ HPRE0 HCP Hdn HAG2 HMR2 HWK2 HWN (fun x h => HP2 x (HP1 x h)) (fun h => HN2 (HN1 h)) HJ).
- unfold YG0d.spZ in Hsp |- *. pjsd_cr. pjsd_rv. exact Hsp.
- pjsd_cr. pjsd_rv. exact H8.
- pjsd_cr. pjsd_rv. exact H18.
- pjsd_cr. pjsd_rv. exact H20.
- intros r Hr. pjsd_cr. rewrite !getr_other by pjs_kept_ne. exact (HKEPT r Hr).
- pjsd_cr. pjsd_rv. reflexivity.
- pjsd_cr. pjsd_rv. reflexivity.
Qed.
(* ---- the segment: the call to fuzz_strdup, then the straight line to pjs_FAILc or pjs_TAIL ---- *)
Theorem pjs_seg_dup_holds : forall CTX0 dd,
  pjs_texts B ARx CTX0 dd -> pjs_frame_kept_stmtR B ARx WLE' dd -> pjs_seg_tail B ARx CTX0 dd ->
  pjs_seg_fail B ARx CTX0 dd ->
  pjs_seg_dup B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT KEEP HTAIL HFAIL en ly S Hp W regs mem md k HPRE HCUT.
eapply (YSRrG.SRr'_bind SEGS RZ).
{ exact (pjsd_call B ARx LAWS VIS HULL CTX0 dd en ly S Hp W regs mem md k TXT KEEP HPRE HCUT). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & -> & HC).
exact (pjsd_line CTX0 dd en ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HPRE HFAIL HTAIL HC).
Qed.

End dp.
