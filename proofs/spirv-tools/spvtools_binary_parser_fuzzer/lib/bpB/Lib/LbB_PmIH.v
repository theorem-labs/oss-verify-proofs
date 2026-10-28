(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_Conv LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit LbB_DiagStmt LbB_WoDiagP LbB_PmMagW.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoDiagC LbB_WoDiagC2 LbB_WoDiagH LbB_PmCall.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_TablImg LbB_PmSL LbB_WdIHS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ih_w1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate. Qed.

Lemma ih_fld1_bv : forall m a v v', Z_to_bv 8 v = Z_to_bv 8 v' -> fldA m a 1 v -> fldA m a 1 v'.
Proof. unfold fldA, fld. intros m a v v' E F. rewrite ih_w1 in *. rewrite F, E. reflexivity. Qed.

Lemma ih_mrd_of_rdn1 : forall segs m a b, PropExec.rdn segs m a 1 = Some [b] -> mrd segs m a = Some b.
Proof.
  intros segs m a b R. cbn [PropExec.rdn] in R. unfold mrd.
  destruct (m a) as [b'|]; [injection R as ->; reflexivity|].
  change (BLPropExec.seg_rom segs a) with (PropExec.seg_rom segs a).
  destruct (PropExec.seg_rom segs a) as [b'|]; [injection R as ->; reflexivity | discriminate].
Qed.

Lemma ih_byte_of_u8arr : forall m A (l : list Z) k, u8arr asegs m A (map (Z_to_bv 8) l) -> (k < length l)%nat ->
  fldA m (A + Z.of_nat k) 1 (nth k l 0).
Proof.
  intros m A l k U Hk. destruct U as [(B0 & B1 & B) _].
  pose proof (B k ltac:(rewrite length_map; lia)) as Bk.
  rewrite nth_error_map, (nth_error_nth' l 0 Hk) in Bk. cbn [option_map] in Bk.
  unfold fldA, fld. rewrite ih_w1. exact (rdn1_of_mrd _ _ _ _ Bk).
Qed.

Lemma ih_u8arr_of_bytes : forall m A (l : list Z),
  (forall k, (k < length l)%nat -> fldA m (A + Z.of_nat k) 1 (nth k l 0)) ->
  wr_at asegs m A (Z.of_nat (length l)) -> u8arr asegs m A (map (Z_to_bv 8) l).
Proof.
  intros m A l F W. split; [|rewrite length_map; exact W].
  destruct W as (W0 & W1 & _). split; [exact W0|]. split; [rewrite length_map; exact W1|].
  intros i Hi. rewrite length_map in Hi. pose proof (F i Hi) as Fi. unfold fldA, fld in Fi. rewrite ih_w1 in Fi.
  rewrite nth_error_map, (nth_error_nth' l 0 Hi). cbn [option_map]. exact (ih_mrd_of_rdn1 _ _ _ _ Fi).
Qed.

Lemma ih_wr_mono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (W0 & W1 & W) M. split; [exact W0|]. split; [exact W1|]. intros i Hi. apply M, W, Hi. Qed.

Lemma ih_fld_of_cells4 : forall m a z, rw_cells asegs m a [C4 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 4 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma ih_rdec : forall lo hi k, {lo <= k < hi} + {~ (lo <= k < hi)}.
Proof. intros lo hi k. destruct (Z_le_gt_dec lo k), (Z_lt_ge_dec k hi); [left; lia | right; lia | right; lia | right; lia]. Qed.

Definition ih_g (k : Z) : Z := nth (Z.to_nat k) (wo_sh [20; 21]%nat) 0.
Definition ih_inr (lo hi k : Z) : bool := (lo <=? k) && (k <? hi).
Definition ih_f1 (k : Z) : Z := if ih_inr 28 31 k || ih_inr 44 47 k || ih_inr 158 208 k then 0 else ih_g k.
Definition ih_f2 (k : Z) : Z := if ih_inr 36 39 k then 0 else ih_f1 k.
Definition ih_f3 (k : Z) : Z := if ih_inr 158 208 k then 0 else ih_g k.

Lemma ih_len : length (wo_sh [20; 21]%nat) = 476%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma ih_inr_t : forall lo hi k, lo <= k < hi -> ih_inr lo hi k = true.
Proof. intros lo hi k Hk. unfold ih_inr. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

Lemma ih_inr_f : forall lo hi k, ~ (lo <= k < hi) -> ih_inr lo hi k = false.
Proof. intros lo hi k Hk. unfold ih_inr. destruct (Z.leb_spec lo k), (Z.ltb_spec k hi); cbn; try reflexivity; lia. Qed.

Lemma ih_g_range : forall lo n v, forallb (fun j => ih_g (lo + Z.of_nat j) =? v) (seq 0 n) = true ->
  forall k, lo <= k < lo + Z.of_nat n -> ih_g k = v.
Proof.
  intros lo n v B k Hk. rewrite forallb_forall in B.
  specialize (B (Z.to_nat (k - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in B by lia. replace (lo + (k - lo)) with k in B by lia. apply Z.eqb_eq, B.
Qed.

Lemma ih_g248 : forall k, 28 <= k < 31 \/ 36 <= k < 39 \/ 44 <= k < 47 \/ 158 <= k < 208 -> ih_g k = 248.
Proof.
  intros k [Hk|[Hk|[Hk|Hk]]];
    [apply (ih_g_range 28 3) | apply (ih_g_range 36 3) | apply (ih_g_range 44 3) | apply (ih_g_range 158 50)];
    first [vm_compute; reflexivity | lia].
Qed.

Lemma ih_g0 : forall k, 420 <= k < 428 -> ih_g k = 0.
Proof. intros k Hk. apply (ih_g_range 420 8); [vm_compute; reflexivity | lia]. Qed.

Lemma ih_f1_in : forall k, 28 <= k < 31 \/ 44 <= k < 47 \/ 158 <= k < 208 -> ih_f1 k = 0.
Proof.
  intros k Hk. unfold ih_f1.
  destruct Hk as [Hk|[Hk|Hk]]; rewrite (ih_inr_t _ _ k Hk);
    destruct (ih_inr 28 31 k), (ih_inr 44 47 k), (ih_inr 158 208 k); reflexivity.
Qed.

Lemma ih_f1_out : forall k, ~ (28 <= k < 31 \/ 44 <= k < 47 \/ 158 <= k < 208) -> ih_f1 k = ih_g k.
Proof. intros k N. unfold ih_f1. rewrite !ih_inr_f by lia. reflexivity. Qed.

Lemma ih_f2_in : forall k, 36 <= k < 39 -> ih_f2 k = 0.
Proof. intros k Hk. unfold ih_f2. rewrite ih_inr_t by lia. reflexivity. Qed.

Lemma ih_f2_out : forall k, ~ (36 <= k < 39) -> ih_f2 k = ih_f1 k.
Proof. intros k N. unfold ih_f2. rewrite ih_inr_f by lia. reflexivity. Qed.

Lemma ih_f3_in : forall k, 158 <= k < 208 -> ih_f3 k = 0.
Proof. intros k Hk. unfold ih_f3. rewrite ih_inr_t by lia. reflexivity. Qed.

Lemma ih_f3_out : forall k, ~ (158 <= k < 208) -> ih_f3 k = ih_g k.
Proof. intros k N. unfold ih_f3. rewrite ih_inr_f by lia. reflexivity. Qed.

Lemma ih_f23 : forall k, ~ (28 <= k < 31 \/ 36 <= k < 39 \/ 44 <= k < 47) -> ih_f3 k = ih_f2 k.
Proof.
  intros k N. rewrite ih_f2_out by lia. destruct (ih_rdec 158 208 k) as [W|W].
  - rewrite ih_f3_in, ih_f1_in by lia. reflexivity.
  - rewrite ih_f3_out, ih_f1_out by lia. reflexivity.
Qed.

Lemma ih_cs : forall p n, TablRep.chk_cstr ASEGS tiA p n = true ->
  existsb (fun g => let '(b, sz, _) := g in (b =? p) && (sz =? n + 1)) aglobals = true -> 65600 <= p -> 0 <= n ->
  cstrA p n.
Proof.
  intros p n C G P0 N0. apply existsb_exists in G as ([[b sz] rz] & Hg & E).
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst b sz.
  eapply (cstrA_of p n p (n + 1) rz C Hg); lia.
Qed.

Ltac ih_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac ih_kreg :=
  first
    [ assumption
    | match goal with K : forall r, In r _ -> getr ?R' r = getr ?R r |- getr ?R' ?n = _ =>
        rewrite (K n) by ih_inl; assumption end
    | match goal with Hr : getr ?R' ?n = _ |- getr ?R' ?n = _ =>
        rewrite Hr; apply bv_eq; vm_compute; reflexivity end
    | match goal with K : forall r, In r _ -> getr ?R' r = getr ?R r, Hr : getr ?R ?n = _ |- getr ?R' ?n = _ =>
        rewrite (K n) by ih_inl; rewrite Hr; apply bv_eq; vm_compute; reflexivity end ].

Ltac ih_zn :=
  repeat match goal with |- context [Z.of_nat ?n] =>
    let z := eval vm_compute in (Z.of_nat n) in progress change (Z.of_nat n) with z end.

Ltac ih_lia := unfold sh, ASHADOW_BASE, WO_FLAGP, AINTRIN_STACK, DS_SIZE, DS_ERR_OFF, nsh; cbn [fst snd]; ih_zn; lia.

Ltac ih_wbyte :=
  match goal with
  | |- fldA ?M (sh ?f + ?k) 1 ?v =>
      let N := eval vm_compute in (ASHADOW_BASE + k) in
      replace (sh f + k) with (f / 8 + N) by (unfold sh, ASHADOW_BASE; ring);
      match goal with
      | Hb : fldA M (f / 8 + N) 1 ?v' |- _ =>
          eapply ih_fld1_bv; [| exact Hb]; apply bv_eq; vm_compute; reflexivity
      end
  end.

Ltac ih_enum Hr :=
  lazymatch type of Hr with
  | ?lo <= ?k < ?hi =>
      destruct (Z.eq_dec k lo) as [->|NE];
      [ clear Hr; ih_wbyte
      | let lo' := eval vm_compute in (lo + 1) in
        let Hr' := fresh "Hr" in
        assert (Hr' : lo' <= k < hi) by lia; clear Hr NE;
        lazymatch eval vm_compute in (lo' =? hi) with
        | true => exfalso; lia
        | false => ih_enum Hr'
        end ]
  end.

Ltac ih_dlia := Z.div_mod_to_equations; lia.

Ltac ih_fa := repeat (apply Forall_cons; [cbn [fst snd]; ih_lia |]); apply Forall_nil.

Ltac ih_flw := repeat (apply Forall_cons; [unfold bp_flw; cbn [fst snd]; ih_lia |]); apply Forall_nil.

Ltac ih_wfree := repeat (apply Forall_cons; [unfold wfree; cbv beta iota; first [exact I | unfold sh, ASHADOW_BASE, nsh, DS_SIZE; cbn [fst snd]; ih_dlia] |]); apply Forall_nil.

Section IH.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA.
  Hypothesis HTR : pm_tr_ok H.

  Lemma ih_dtr : ds_tr_ok H.
  Proof. unfold pm_tr_ok, PM_DEL_RAS in HTR. exact (Forall_inv HTR). Qed.

  Section Path.
    Variables (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) (w : piw H) (c0 : parserC)
      (LBs : list block) (s0 : as_St H) (LB0 : list block) (m0 : mem) (XSc0 : list (Z * Z)).
    Hypothesis HP : wpre H e.
    Hypothesis HWL : bp_wl H e ff w.
    Hypothesis HPP : bp_pp H w LB0 LBs m0 c0.
    Hypothesis HI0 : winv H e ff fp XSc0 s0 LB0 m0.
    Hypothesis HMD : mdef m0 (pw_p H w) PARSER_SIZE.
    Hypothesis HAL : PM_RESERVE <= as_AL H s0.
    Hypothesis HPF : bp_pfresh H w s0 LB0 LBs m0 c0.
    Hypothesis HK : bp_kwcf H e ff fp Q mo0.
    Hypothesis HN : w_n e <= 4.
    Hypothesis HW : w_words e <> 0.
    Hypothesis HSL0 : bp_slots H e ff m0.
    Hypothesis HSH0 : bp_shad ff [20; 21]%nat m0.

    Let HH0 : asan_rt_hyps H := rt_bp_base H HHbp.

    Local Abbreviation WSR := (wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0).
    Local Abbreviation LF6 := ((6, ff, fp) :: w_LF e).

    Lemma ih_geo : ff mod 64 = 0 /\ 7278592 <= ff /\ ff + 4096 <= w_lo e /\ w_lo e + 32768 <= wS1 e
      /\ 140735332483072 <= w_lo e /\ wS1 e + 192 <= 2 ^ 47
      /\ (2147450880 + ff / 8 + 512 <= ff \/ ff + 4096 <= 2147450880 + ff / 8)
      /\ 2147450880 + ff / 8 + 512 <= wS1 e - 4096 /\ ff + 4088 <= wS1 e - 4096
      /\ (ff + 4096 <= 2147446784 \/ 17594333495296 <= ff) /\ 0 <= ff / 8 <= 2 ^ 44.
    Proof.
      pose proof (hdr_geo H e ff fp XSc0 s0 LB0 m0 HP HI0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
      pose proof (wframe_bounds H e ff fp XSc0 s0 LB0 m0 HP HI0) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
      unfold sh, ASHADOW_BASE, aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AINTRIN_STACK, WO_FLAGP in *.
      split; [lia|]. do 9 (split; [lia|]). Z.div_mod_to_equations. lia.
    Qed.

    Ltac ih_geo_intro := pose proof ih_geo as (Ga & Gb & Gc & Gd & Ge & Gf & Gg & Gh & Gi & Gj & Gk).

    Local Abbreviation wstart := (w_start H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wchunk := (w_chunk H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wexit := (w_exit H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wgeo := (w_geo H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wobj := (w_obj H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wfldkeep := (w_fld_keep H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).

    Lemma ih_meas : pm_meas_ok (pw_n H w) LBs.
    Proof.
      pose proof HPF as (_ & (HDR & _) & _).
      pose proof HWL as (_ & _ & _ & Wn & _).
      pose proof HPP as (PR & _).
      unfold parser_repA in PR.
      assert (S1 : cell8 ASEGS m0 (pw_p H w + ST_OFF + 8) (st_nwords (pc_state c0))) by (eapply sr_w1; eapply pr_state; exact PR).
      destruct HDR as (Hw & Hn & _). cbn [bp_ste st_nwords] in Hn.
      destruct S1 as [S1 _].
      apply (bp_meas H w LB0 LBs m0 c0 HPP (bp_phc_ste _ _ _ _ (proj1 (proj1 (proj2 HPF))))). lia.
    Qed.

    Local Abbreviation wmemset := (w_memset H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL ih_meas).
    Local Abbreviation wctor := (w_ctor H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL ih_meas).
    Local Abbreviation wcseq := (w_cseq H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL ih_meas).
    Local Abbreviation wnum := (w_num H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL ih_meas).
    Local Abbreviation wdtor := (w_dtor H HHbp ds_repA DSL ih_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL ih_meas).

    Definition ih_IC : Z := st_icount (pc_state c0).

    Lemma ih_par : fldA m0 (ff + 3504) 8 (w_words e) /\ fldA m0 (ff + 3512) 8 (w_n e) /\ fldA m0 (ff + 3536) 8 ih_IC
      /\ fldA m0 (ff + 3464) 8 (ff + 3376) /\ fldA m0 (ff + 3408) 8 0
      /\ 0 <= w_words e < 2 ^ 64 /\ 0 <= w_n e < 2 ^ 64 /\ 0 <= ih_IC < 2 ^ 64.
    Proof.
      pose proof HWL as (Wp & Wc & Ww & Wn & _).
      pose proof HPP as (PR & _ & HC & _).
      pose proof HPF as (_ & (HDR & _) & _ & CZ).
      unfold parser_repA in PR.
      assert (S0 : cell8 ASEGS m0 (pw_p H w + ST_OFF) (st_words (pc_state c0))) by (eapply sr_w0; eapply pr_state; exact PR).
      assert (S1 : cell8 ASEGS m0 (pw_p H w + ST_OFF + 8) (st_nwords (pc_state c0))) by (eapply sr_w1; eapply pr_state; exact PR).
      assert (S4 : cell8 ASEGS m0 (pw_p H w + ST_OFF + 32) (st_icount (pc_state c0))) by (eapply sr_w4; eapply pr_state; exact PR).
      assert (PC : CRep.fld ASEGS m0 (pw_p H w + 8) 8 (pc_cons c0)) by (eapply pr_cons; exact PR).
      destruct HDR as (Hw & Hn & _). cbn [bp_ste st_words st_nwords] in Hw, Hn.
      rewrite Wp in S0, S1, S4, PC. rewrite HC, Wc in PC. rewrite Ww in Hw. rewrite Wn in Hn.
      rewrite Hw in S0. rewrite Hn in S1. rewrite Wc in CZ. unfold ST_OFF in *.
      destruct S0 as [S0r S0], S1 as [S1r S1], S4 as [S4r S4].
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in S0r, S1r, S4r.
      split; [replace (ff + 3504) with (ff + 3456 + 48) by lia; exact S0|].
      split; [replace (ff + 3512) with (ff + 3456 + 48 + 8) by lia; exact S1|].
      split; [replace (ff + 3536) with (ff + 3456 + 48 + 32) by lia; exact S4|].
      split; [replace (ff + 3464) with (ff + 3456 + 8) by lia; exact PC|].
      split; [replace (ff + 3408) with (ff + 3376 + 32) by lia; apply (w_fld_of_cells8 m0 _ 0 CZ); lia|].
      unfold ih_IC. lia.
    Qed.

    Definition ih_shf (m : mem) (f : Z -> Z) : Prop := forall k, 0 <= k < 476 -> fldA m (sh ff + k) 1 (f k).

    Lemma ih_shad_init : forall m, bp_shad ff [20; 21]%nat m -> ih_shf m ih_g.
    Proof.
      intros m S k Hk. unfold bp_shad in S.
      pose proof (ih_byte_of_u8arr m (sh ff) _ (Z.to_nat k) S) as B.
      rewrite ih_len in B. specialize (B ltac:(lia)). rewrite Z2Nat.id in B by lia. exact B.
    Qed.

    Lemma ih_shad_fin : forall m, ih_shf m ih_g -> wr_at asegs m (sh ff) 476 -> bp_shad ff [20; 21]%nat m.
    Proof.
      intros m S W. unfold bp_shad. apply ih_u8arr_of_bytes; [|rewrite ih_len; exact W].
      intros k Hk. rewrite ih_len in Hk. pose proof (S (Z.of_nat k) ltac:(lia)) as B.
      unfold ih_g in B. rewrite Nat2Z.id in B. exact B.
    Qed.

    Lemma ih_shw : forall m, wr_at asegs m (ff / 8 + 2147450880) 512 -> wr_at asegs m (sh ff) 512.
    Proof. intros m W. replace (sh ff) with (ff / 8 + 2147450880) by (unfold sh, ASHADOW_BASE; lia). exact W. Qed.

    Lemma ih_shf_munch : forall m m' W f f', ih_shf m f -> munch W m m' ->
      (forall k, 0 <= k < 476 -> (disjoint_from W (sh ff + k) 1 /\ f' k = f k) \/ fldA m' (sh ff + k) 1 (f' k)) ->
      ih_shf m' f'.
    Proof.
      intros m m' W f f' S MU K k Hk. ih_geo_intro.
      destruct (K k Hk) as [[D E]|F]; [|exact F].
      rewrite E. apply (fld_munch W m m' _ 1 _ (S k Hk) MU D); ih_lia.
    Qed.

    Lemma ih_shf_out : forall m m' W f, ih_shf m f -> munch W m m' ->
      (forall k, 0 <= k < 476 -> disjoint_from W (sh ff + k) 1) -> ih_shf m' f.
    Proof. intros m m' W f S MU D. apply (ih_shf_munch m m' W f f S MU). intros k Hk. left. split; [apply D, Hk | reflexivity]. Qed.

    Lemma ih_shf_keep : forall X m m' f, ih_shf m f -> wxkeep H e ff fp LB0 X m m' ->
      Forall (fun iv : Z * Z => sh ff + 476 <= fst iv \/ snd iv <= sh ff) X -> ih_shf m' f.
    Proof.
      intros X m m' f S K FX k Hk.
      apply (wfldkeep X m m' (sh ff + k) 1 (f k) K); [right; ih_zn; lia | | apply S, Hk].
      eapply Forall_impl; [|exact FX]. intros [lo hi] Hiv. cbn [fst snd] in *. ih_zn. lia.
    Qed.

    Lemma ih_fkeep : forall X m m' a k v, wxkeep H e ff fp LB0 X m m' -> ff <= a -> a + Z.of_nat k <= ff + 4088 ->
      Forall (fun iv : Z * Z => a + Z.of_nat k <= fst iv \/ snd iv <= a) X -> fldA m a k v -> fldA m' a k v.
    Proof. intros X m m' a k v K A0 A1 FX F. exact (wfldkeep X m m' a k v K (or_introl (conj A0 A1)) FX F). Qed.

    Lemma ih_addr : forall m f k n, ih_shf m f -> wr_at asegs m (sh ff) 512 ->
      0 <= k -> 0 < n -> k mod 8 = 0 -> n mod 8 = 0 -> k + n <= 3808 ->
      (forall j, k / 8 <= j < (k + n) / 8 -> f j = 0) -> addressable m (ff + k) n.
    Proof.
      intros m f k n S W K0 N0 K8 N8 KN Z0. ih_geo_intro.
      split; [lia|]. split; [lia|]. split; [ih_dlia|].
      unfold shadow_of. replace (n mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact N8). rewrite app_nil_r.
      replace (repeat (b8 0) (Z.to_nat (n / 8))) with (map (Z_to_bv 8) (repeat 0 (Z.to_nat (n / 8)))) by (rewrite map_repeat; reflexivity).
      apply ih_u8arr_of_bytes.
      - intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat.
        replace (sh (ff + k) + Z.of_nat i) with (sh ff + (k / 8 + Z.of_nat i)) by (unfold sh; ih_dlia).
        pose proof (S (k / 8 + Z.of_nat i) ltac:(ih_dlia)) as B. rewrite (Z0 (k / 8 + Z.of_nat i) ltac:(ih_dlia)) in B. exact B.
      - rewrite repeat_length. replace (sh (ff + k)) with (sh ff + k / 8) by (unfold sh; ih_dlia).
        apply (bp_wr_sub m (sh ff) 512 (k / 8) (Z.of_nat (Z.to_nat (n / 8))) W); ih_dlia.
    Qed.

    Lemma ih_obj : forall m f k n, ih_shf m f -> wr_at asegs m (sh ff) 512 ->
      0 <= k -> 0 < n -> k mod 8 = 0 -> n mod 8 = 0 -> k + n <= 3808 ->
      (forall j, k / 8 <= j < (k + n) / 8 -> f j = 0) ->
      ds_obj H LF6 m (wS1 e) (ff + k) n /\ obj_inframe LF6 (ff + k) n.
    Proof.
      intros m f k n S W K0 N0 K8 N8 KN Z0. ih_geo_intro.
      apply (wobj m k n); [lia | lia | unfold WO_FLAGP; lia | ih_dlia | exact (ih_addr m f k n S W K0 N0 K8 N8 KN Z0)].
    Qed.

    Lemma ih_dsobj : forall m f, ih_shf m f -> wr_at asegs m (sh ff) 512 -> (forall j, 158 <= j < 207 -> f j = 0) ->
      ds_obj H LF6 m (wS1 e) (ff + 1264) DS_SIZE /\ obj_inframe LF6 (ff + 1264) DS_SIZE.
    Proof. intros m f S W Z0. apply (ih_obj m f 1264 392 S W); [lia | lia | ih_dlia | ih_dlia | lia | intros j Hj; apply Z0; ih_dlia]. Qed.

    Lemma ih_sl40 : forall m, bp_slots H e ff m -> fldA m (wS1 e + 40) 8 ASHADOW_BASE.
    Proof.
      intros m (_ & S2 & _). unfold fldA, fld.
      pose proof (rw_cells_read asegs m (wS1 e + 24) _ 16%nat _ S2 eq_refl) as RD.
      replace (wS1 e + 24 + Z.of_nat 16) with (wS1 e + 40) in RD by lia.
      rewrite <- rdn_of_ov. exact RD.
    Qed.

    Lemma ih_pin : forall pc REGS S P spent c, WSR pc REGS S P spent c ->
      exists m XSc s LB, winv H e ff fp XSc s LB m /\ P m /\ WSR pc REGS S (fun m' => m' = m /\ P m') spent c.
    Proof.
      intros pc REGS S P spent c (s & R & F & fc & m & XSc & LB & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
      exists m, XSc, s, LB. split; [exact A6|]. split; [exact A13|].
      exists s, R, F, fc, m, XSc, LB. repeat (split; [assumption|]). split; [split; [reflexivity | exact A13] | exact A14].
    Qed.

    Definition ih_R1 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R2 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3652) /\ getr R 10 = wz (ff + 224) /\ getr R 11 = wz 0 /\ getr R 12 = wz 16
      /\ getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 224) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R3 (R : bvmap 5 word) : Prop := getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 224) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R4 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3732) /\ getr R 10 = wz (ff + 1264) /\ getr R 11 = wz (ff + 224)
      /\ getr R 12 = wz (ff + 3376) /\ getr R 13 = wz (ff + 288) /\ getr R 14 = wz ((-4) mod 2 ^ 64)
      /\ getr R 15 = wz (ff + 352) /\ getr R 18 = wz (ff + 3456) /\ getr R 25 = wz (ff + 1264)
      /\ getr R 26 = wz (ff + 288) /\ getr R 27 = wz (ff + 352) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R5 (R : bvmap 5 word) : Prop :=
      getr R 18 = wz (ff + 3456) /\ getr R 25 = wz (ff + 1264) /\ getr R 26 = wz (ff + 288) /\ getr R 27 = wz (ff + 352) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R6 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3848) /\ getr R 10 = wz (ff + 1264) /\ getr R 11 = wz 147776 /\ getr R 12 = wz 35
      /\ getr R 18 = wz (ff + 3456) /\ getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R7 (R : bvmap 5 word) : Prop :=
      getr R 18 = wz (ff + 3456) /\ getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R8 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3860) /\ getr R 10 = wz (ff + 1264) /\ getr R 11 = wz (w_n e)
      /\ getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R9 (R : bvmap 5 word) : Prop := getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R10 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3880) /\ getr R 10 = wz (ff + 1264) /\ getr R 11 = wz 147872 /\ getr R 12 = wz 18
      /\ getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R12 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3892) /\ getr R 10 = wz (ff + 1264) /\ getr R 11 = wz (sx32 5)
      /\ getr R 21 = wz (-8) /\ getr R 25 = wz (ff + 1264) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R14 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (960452 + 3904) /\ getr R 10 = wz (ff + 1264) /\ getr R 21 = wz (-8) /\ getr R 24 = wz (-4) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R15 (R : bvmap 5 word) : Prop := getr R 21 = wz (-8) /\ getr R 24 = wz (-4) /\ getr R 22 = wz (ff + 3504).
    Definition ih_R16 (R : bvmap 5 word) : Prop := getr R 24 = wz (-4) /\ getr R 22 = wz (ff + 3504).

    Definition ih_P0 (m : mem) : Prop :=
      ih_shf m ih_g /\ fldA m (ff + 3504) 8 (w_words e) /\ fldA m (ff + 3512) 8 (w_n e)
      /\ fldA m (ff + 3536) 8 ih_IC /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3408) 8 0.
    Definition ih_P1 (m : mem) : Prop :=
      ih_shf m ih_g /\ fldA m (ff + 3512) 8 (w_n e) /\ fldA m (ff + 3536) 8 ih_IC
      /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3408) 8 0.
    Definition ih_P2 (m : mem) : Prop :=
      ih_shf m ih_f1 /\ fldA m (ff + 3512) 8 (w_n e) /\ fldA m (ff + 3536) 8 ih_IC
      /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3408) 8 0.
    Definition ih_P3 (m : mem) : Prop := ih_P2 m /\ fldA m (ff + 224) 8 0 /\ fldA m (ff + 232) 8 0.
    Definition ih_P4 (m : mem) : Prop :=
      ih_shf m ih_f2 /\ fldA m (ff + 3512) 8 (w_n e) /\ fldA m (ff + 3408) 8 0 /\ fldA m (ff + 224) 8 0
      /\ fldA m (ff + 232) 8 0 /\ fldA m (ff + 240) 8 ih_IC /\ fldA m (ff + 288) 2 0 /\ fldA m (ff + 352) 2 0.
    Definition ih_P5 (m : mem) : Prop :=
      ih_shf m ih_f2 /\ fldA m (ff + 3512) 8 (w_n e) /\ fldA m (ff + 288) 2 0 /\ fldA m (ff + 352) 2 0.
    Definition ih_P6 (m : mem) : Prop := ih_shf m ih_f3 /\ fldA m (ff + 3512) 8 (w_n e).
    Definition ih_P8 (m : mem) : Prop := ih_shf m ih_f3.
    Definition ih_P16 (m : mem) : Prop := ih_shf m ih_g /\ wr_at asegs m (sh ff) 476.

    Lemma ih_s16 : forall c, WSR BP_WCF ih_R16 None ih_P16 5888 c -> as_SR H Q c.
    Proof.
      intros c Hc.
      apply (wexit Q BP_WCF ih_R16 (fun R => getr R 22 = wz (ff + 3504)) ih_P16 5888 c [20; 21]%nat (bp_slots H) (-4) Hc).
      - unfold PM_RESERVE. lia.
      - exact HPF.
      - intros m [S W]. exact (ih_shad_fin m S W).
      - intros m SL _. exact SL.
      - intros R (R24 & R22). split; [exact R22 | exact R24].
      - lia.
      - exact HK.
    Qed.

    Lemma ih_s15 : forall c, WSR (960452 + 3904) ih_R15 None ih_P8 5888 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3904) BP_WCF ih_R15 ih_R16 None ih_P8 ih_P16 5888 c Hc); [|exact ih_s16].
      intros R F fc m XSc s LB (R21 & R24 & R22) RC S HI HSL HSE. ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_ih8_ea7c4 R F fc m ff (wS1 e) ASHADOW_BASE) as (R' & M' & RUN & MU & WM & POST).
      { unfold wd_ih8_pre. split; [exact R21|]. split; [exact C19|]. split; [exact C9|]. split; [exact GW2|].
        split; [exact (ih_sl40 m HSL)|]. unfold ASHADOW_BASE. lia. }
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST.
      split; [ih_flw|]. split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R16; split; ih_kreg|].
      split.
      - apply (ih_shf_munch m M' _ ih_f3 ih_g S MU). intros k Hk.
        destruct (ih_rdec 158 208 k) as [Wr|N1]; [right; ih_enum Wr|].
        left. split; [cbn [disjoint_from]; ih_lia | symmetry; apply ih_f3_out; exact N1].
      - replace (sh ff) with (ff / 8 + 2147450880 + 0) by (unfold sh, ASHADOW_BASE; lia).
        apply (bp_wr_sub M' _ 512 0 476); [exact (ih_wr_mono m M' _ _ GW2 WM) | lia | lia | lia].
    Qed.
    Lemma ih_s14 : forall c, WSR ADS_DTOR ih_R14 (Some (ff + 1264, -4, 101)) ih_P8 5888 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply ih_shw in GW2.
      apply (wdtor HDTOR Q ih_R14 ih_R15 (fun m' => m' = m /\ ih_P8 m') ih_P8 5888 c (960452 + 3904) (ff + 1264) (-4) 101 Hc').
      - intros R (R1 & R10 & _). split; assumption.
      - reflexivity.
      - lia.
      - unfold PM_RESERVE. lia.
      - unfold PO_PF. apply in_or_app. left. ih_inl.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S'). apply (ih_dsobj m ih_f3 S' GW2). intros j Hj. apply ih_f3_in. lia.
      - intros R R' (_ & _ & R21 & R24 & R22) K. unfold ih_R15. repeat split; ih_kreg.
      - intros m1 m' (-> & S') KX. apply (ih_shf_keep _ m m' ih_f3 S' KX). ih_fa.
      - exact ih_s15.
    Qed.

    Lemma ih_s13 : forall c, WSR (960452 + 3892) ih_R9 (Some (ff + 1264, -4, 101)) ih_P8 5888 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3892) ADS_DTOR ih_R9 ih_R14 _ ih_P8 ih_P8 5888 c Hc); [|exact ih_s14].
      intros R F fc m XSc s LB (R21 & R25 & R22) RC S HI HSL HSE. ih_geo_intro.
      destruct HSE as (DB & DS & _ & _).
      pose proof (dla_err _ _ DSL _ _ _ _ _ _ DS) as ERR.
      apply ih_fld_of_cells4 in ERR; [|ih_lia].
      destruct (wd_ih7_ea7c4 R F fc m ff) as (R' & M' & RUN & EM & POST).
      { unfold wd_ih7_pre. split; [exact R25|]. split; [|lia].
        replace (ff + 1624) with (ff + 1264 + DS_ERR_OFF) by (unfold DS_ERR_OFF; lia). exact ERR. }
      subst M'. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R14; repeat split; ih_kreg|]. exact S.
    Qed.

    Lemma ih_s12 : forall c, WSR APUT_U32 ih_R12 (Some (ff + 1264, -4, 77)) ih_P8 3888 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply ih_shw in GW2.
      apply (wnum APUT_U32 0 (2 ^ 32) sx32 HU32 Q ih_R12 ih_R9 (fun m' => m' = m /\ ih_P8 m') ih_P8 3888 c
               (960452 + 3892) (ff + 1264) (-4) 77 5 Hc').
      - intros R (R1 & R10 & R11 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold ds_cost, PM_RESERVE. lia.
      - lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S'). apply (ih_dsobj m ih_f3 S' GW2). intros j Hj. apply ih_f3_in. lia.
      - lia.
      - intros R R' (_ & _ & _ & R21 & R25 & R22) K K10. unfold ih_R9. repeat split; ih_kreg.
      - intros m1 m' (-> & S') KX. apply (ih_shf_keep _ m m' ih_f3 S' KX).
        unfold RtB_Td.ATDLOC; ih_fa.
      - exact ih_s13.
    Qed.

    Lemma ih_s11 : forall c, WSR (960452 + 3880) ih_R9 (Some (ff + 1264, -4, 77)) ih_P8 3888 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3880) APUT_U32 ih_R9 ih_R12 _ ih_P8 ih_P8 3888 c Hc); [|exact ih_s12].
      intros R F fc m XSc s LB (R21 & R25 & R22) RC S HI HSL HSE. ih_geo_intro.
      destruct (wd_ih6_ea7c4 R F fc m ff) as (R' & M' & RUN & EM & POST).
      { unfold wd_ih6_pre. split; [exact R25 | lia]. }
      subst M'. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R12; repeat split; ih_kreg|]. exact S.
    Qed.

    Lemma ih_s10 : forall c, WSR APUT_CSEQ ih_R10 (Some (ff + 1264, -4, 59)) ih_P8 2272 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply ih_shw in GW2.
      assert (CS : cstrA 147872 18) by (apply ih_cs; [vm_compute; reflexivity | vm_compute; reflexivity | lia | lia]).
      destruct (cstrA_img 147872 18 m0 CS (winv_mi H e ff fp XSc0 s0 LB0 m0 HI0)) as (I1 & I2 & I3 & I4 & I5).
      apply (wcseq HCSEQ Q ih_R10 ih_R9 (fun m' => m' = m /\ ih_P8 m') ih_P8 2272 c (960452 + 3880) (ff + 1264) (-4) 59 147872 18 Hc').
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold ds_cost, PM_RESERVE. lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S'). apply (ih_dsobj m ih_f3 S' GW2). intros j Hj. apply ih_f3_in. lia.
      - exact I3.
      - exact I1.
      - exact I2.
      - exact I4.
      - exact I5.
      - lia.
      - intros R R' (_ & _ & _ & _ & R21 & R25 & R22) K K10. unfold ih_R9. repeat split; ih_kreg.
      - intros m1 m' (-> & S') KX. apply (ih_shf_keep _ m m' ih_f3 S' KX). ih_fa.
      - exact ih_s11.
    Qed.

    Lemma ih_s9 : forall c, WSR (960452 + 3860) ih_R9 (Some (ff + 1264, -4, 59)) ih_P8 2272 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3860) APUT_CSEQ ih_R9 ih_R10 _ ih_P8 ih_P8 2272 c Hc); [|exact ih_s10].
      intros R F fc m XSc s LB (R21 & R25 & R22) RC S HI HSL HSE. ih_geo_intro.
      destruct (wd_ih5_ea7c4 R F fc m ff) as (R' & M' & RUN & EM & POST).
      { unfold wd_ih5_pre. split; [exact R25 | lia]. }
      subst M'. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R10; repeat split; ih_kreg|]. exact S.
    Qed.

    Lemma ih_s8 : forall c, WSR APUT_U64 ih_R8 (Some (ff + 1264, -4, 35)) ih_P8 944 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply ih_shw in GW2.
      pose proof ih_par as (_ & _ & _ & _ & _ & _ & PN & _).
      apply (wnum APUT_U64 0 (2 ^ 64) (fun x => x) HU64 Q ih_R8 ih_R9 (fun m' => m' = m /\ ih_P8 m') ih_P8 944 c
               (960452 + 3860) (ff + 1264) (-4) 35 (w_n e) Hc').
      - intros R (R1 & R10 & R11 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold ds_cost, PM_RESERVE. lia.
      - lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S'). apply (ih_dsobj m ih_f3 S' GW2). intros j Hj. apply ih_f3_in. lia.
      - lia.
      - intros R R' (_ & _ & _ & R21 & R25 & R22) K K10. unfold ih_R9. repeat split; ih_kreg.
      - intros m1 m' (-> & S') KX. apply (ih_shf_keep _ m m' ih_f3 S' KX).
        unfold RtB_Td.ATDLOC; ih_fa.
      - exact ih_s9.
    Qed.

    Lemma ih_s7 : forall c, WSR (960452 + 3848) ih_R7 (Some (ff + 1264, -4, 35)) ih_P6 944 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3848) APUT_U64 ih_R7 ih_R8 _ ih_P6 ih_P8 944 c Hc); [|exact ih_s8].
      intros R F fc m XSc s LB (R18 & R21 & R25 & R22) RC (S & F12) HI HSL HSE. ih_geo_intro.
      pose proof ih_par as (_ & _ & _ & _ & _ & _ & PN & _).
      destruct (wd_ih4_ea7c4 R F fc m ff (w_n e)) as (R' & M' & RUN & EM & POST).
      { unfold wd_ih4_pre. split; [exact R18|]. split; [exact R25|]. split; [exact F12|]. lia. }
      subst M'. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R8; repeat split; ih_kreg|]. exact S.
    Qed.

    Lemma ih_s6 : forall c, WSR APUT_CSEQ ih_R6 (Some (ff + 1264, -4, 0)) ih_P6 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply ih_shw in GW2.
      assert (CS : cstrA 147776 35) by (apply ih_cs; [vm_compute; reflexivity | vm_compute; reflexivity | lia | lia]).
      destruct (cstrA_img 147776 35 m0 CS (winv_mi H e ff fp XSc0 s0 LB0 m0 HI0)) as (I1 & I2 & I3 & I4 & I5).
      apply (wcseq HCSEQ Q ih_R6 ih_R7 (fun m' => m' = m /\ ih_P6 m') ih_P6 0 c (960452 + 3848) (ff + 1264) (-4) 0 147776 35 Hc').
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold ds_cost, PM_RESERVE. lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S' & _). apply (ih_dsobj m ih_f3 S' GW2). intros j Hj. apply ih_f3_in. lia.
      - exact I3.
      - exact I1.
      - exact I2.
      - exact I4.
      - exact I5.
      - lia.
      - intros R R' (_ & _ & _ & _ & R18 & R21 & R25 & R22) K K10. unfold ih_R7. repeat split; ih_kreg.
      - intros m1 m' (-> & S' & F12) KX. split.
        + apply (ih_shf_keep _ m m' ih_f3 S' KX). ih_fa.
        + apply (ih_fkeep _ m m' _ _ _ KX); [lia | ih_zn; lia | ih_fa | exact F12].
      - exact ih_s7.
    Qed.

    Lemma ih_s5 : forall c, WSR (960452 + 3732) ih_R5 (Some (ff + 1264, -4, 0)) ih_P5 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3732) APUT_CSEQ ih_R5 ih_R6 _ ih_P5 ih_P6 0 c Hc); [|exact ih_s6].
      intros R F fc m XSc s LB (R18 & R25 & R26 & R27 & R22) RC (S & F12 & F88 & F52) HI HSL HSE. ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_ih3_ea7c4 R F fc m ff) as (R' & M' & RUN & MU & WM & POST).
      { unfold wd_ih3_pre. split; [exact R27|]. split; [exact R26|]. split; [exact C19|]. split; [exact R25|].
        split; [exact (proj1 (fld2_split01 m (ff + 352) 0 ltac:(lia) ltac:(lia) (or_introl eq_refl) F52))|].
        split; [exact (proj1 (fld2_split01 m (ff + 288) 0 ltac:(lia) ltac:(lia) (or_introl eq_refl) F88))|].
        split; [exact GW2 | lia]. }
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST.
      split; [ih_flw|]. split; [ih_wfree|].
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R6; repeat split; ih_kreg|].
      split.
      - apply (ih_shf_munch m M' _ ih_f2 ih_f3 S MU). intros k Hk.
        destruct (ih_rdec 28 31 k) as [Wr|N1]; [right; rewrite ih_f3_out, ih_g248 by lia; ih_enum Wr|].
        destruct (ih_rdec 36 39 k) as [Wr|N2]; [right; rewrite ih_f3_out, ih_g248 by lia; ih_enum Wr|].
        destruct (ih_rdec 44 47 k) as [Wr|N3]; [right; rewrite ih_f3_out, ih_g248 by lia; ih_enum Wr|].
        left. split; [cbn [disjoint_from]; ih_lia | apply ih_f23; lia].
      - apply (fld_munch _ m M' _ 8 _ F12 MU); cbn [disjoint_from]; ih_lia.
    Qed.

    Lemma ih_s4 : forall c, WSR ADS_CTOR ih_R4 None ih_P4 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & Pm & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _). apply ih_shw in GW2.
      destruct (w_junk H e ff fp XSc s LB m (ff + 290) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J1 & HJ1).
      destruct (w_junk H e ff fp XSc s LB m (ff + 354) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J2 & HJ2).
      apply (wctor HCTOR Q ih_R4 ih_R5 (fun m' => m' = m /\ ih_P4 m') ih_P5 0 c
               (960452 + 3732) (ff + 1264) (ff + 224) (ff + 3376) (ff + 288) (ff + 352) (-4) Hc').
      - intros R (R1 & R10 & R11 & R12 & R13 & R14 & R15 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold PM_RESERVE. lia.
      - lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S & F12 & F08 & F24 & F32 & F40 & F88 & F52).
        assert (Z28 : forall j, 28 <= j < 31 -> ih_f2 j = 0) by (intros j Hj; rewrite ih_f2_out, ih_f1_in by lia; reflexivity).
        assert (Z36 : forall j, 36 <= j < 39 -> ih_f2 j = 0) by (intros j Hj; apply ih_f2_in; lia).
        assert (Z44 : forall j, 44 <= j < 47 -> ih_f2 j = 0) by (intros j Hj; rewrite ih_f2_out, ih_f1_in by lia; reflexivity).
        assert (Z158 : forall j, 158 <= j < 207 -> ih_f2 j = 0) by (intros j Hj; rewrite ih_f2_out, ih_f1_in by lia; reflexivity).
        assert (Z422 : forall j, 422 <= j < 428 -> ih_f2 j = 0) by (intros j Hj; rewrite ih_f2_out, ih_f1_out, ih_g0 by lia; reflexivity).
        exists [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 ih_IC], J1, J2.
        pose proof ih_par as (_ & _ & _ & _ & _ & _ & _ & PIC).
        split; [exact (proj1 (ih_dsobj m ih_f2 S GW2 Z158))|].
        split; [exact (bp_wr_sub m ff 4096 1264 392 GW1 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (proj2 (ih_dsobj m ih_f2 S GW2 Z158))|].
        split; [apply (proj1 (ih_obj m ih_f2 224 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z28; ih_dlia)))|].
        split; [apply (w_u64arr3 m (ff + 224) 0 0 ih_IC);
                [exact F24
                |replace (ff + 224 + 8) with (ff + 232) by lia; exact F32
                |replace (ff + 224 + 16) with (ff + 240) by lia; exact F40
                |exact (bp_wr_sub m ff 4096 224 24 GW1 ltac:(lia) ltac:(lia) ltac:(lia))
                |lia | lia | lia]|].
        split; [reflexivity|].
        split; [apply (proj2 (ih_obj m ih_f2 224 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z28; ih_dlia)))|].
        split; [apply (proj1 (ih_obj m ih_f2 288 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z36; ih_dlia)))|].
        split; [apply (w_str m (ff + 288) J1 F88 (bp_wr_sub m ff 4096 288 2 GW1 ltac:(lia) ltac:(lia) ltac:(lia)));
                replace (ff + 288 + 2) with (ff + 290) by lia; exact HJ1|].
        split; [apply (proj2 (ih_obj m ih_f2 288 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z36; ih_dlia)))|].
        split; [apply (proj1 (ih_obj m ih_f2 352 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z44; ih_dlia)))|].
        split; [apply (w_str m (ff + 352) J2 F52 (bp_wr_sub m ff 4096 352 2 GW1 ltac:(lia) ltac:(lia) ltac:(lia)));
                replace (ff + 352 + 2) with (ff + 354) by lia; exact HJ2|].
        split; [apply (proj2 (ih_obj m ih_f2 352 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z44; ih_dlia)))|].
        split; [apply (proj1 (ih_obj m ih_f2 3376 48 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z422; ih_dlia)))|].
        split; [apply (w_cells8_of_fld m (ff + 3376 + 32) 0);
                [replace (ff + 3376 + 32) with (ff + 3408) by lia; exact F08
                |replace (ff + 3376 + 32) with (ff + 3408) by lia; exact (bp_wr_sub m ff 4096 3408 8 GW1 ltac:(lia) ltac:(lia) ltac:(lia))]|].
        intros a Ha. unfold DS_SIZE in Ha. lia.
      - intros R R' (_ & _ & _ & _ & _ & _ & _ & R18 & R25 & R26 & R27 & R22) K. unfold ih_R5. repeat split; ih_kreg.
      - intros m1 m' (-> & S & F12 & F08 & F24 & F32 & F40 & F88 & F52) KX.
        split; [apply (ih_shf_keep _ m m' ih_f2 S KX); ih_fa|].
        split; [apply (ih_fkeep _ m m' _ _ _ KX); [lia | ih_zn; lia | ih_fa | exact F12]|].
        split; [apply (ih_fkeep _ m m' _ _ _ KX); [lia | ih_zn; lia | ih_fa | exact F88]|].
        apply (ih_fkeep _ m m' _ _ _ KX); [lia | ih_zn; lia | ih_fa | exact F52].
      - exact ih_s5.
    Qed.

    Lemma ih_s3 : forall c, WSR (960452 + 3652) ih_R3 None ih_P3 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3652) ADS_CTOR ih_R3 ih_R4 None ih_P3 ih_P4 0 c Hc); [|exact ih_s4].
      intros R F fc m XSc s LB (R18 & R24 & R22) RC ((S & F12 & F36 & F64 & F08) & F24 & F32) HI HSL HSE. ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _).
      pose proof ih_par as (_ & _ & _ & _ & _ & _ & _ & PIC).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_ih2_ea7c4 R F fc m ff (ff + 3376) ih_IC) as (R' & M' & RUN & MU & WM & POST).
      { unfold wd_ih2_pre. split; [exact R18|]. split; [exact R24|]. split; [exact C20|]. split; [exact C19|].
        split; [exact F36|]. split; [exact F64|]. split; [exact GW1|]. split; [exact GW2|].
        split; [lia|]. split; [lia|]. split; [ih_dlia|]. lia. }
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST.
      split; [ih_flw|]. split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R4; repeat split; ih_kreg|].
      split.
      - apply (ih_shf_munch m M' _ ih_f1 ih_f2 S MU). intros k Hk.
        destruct (ih_rdec 36 39 k) as [Wr|N1]; [right; rewrite ih_f2_in by lia; ih_enum Wr|].
        left. split; [cbn [disjoint_from]; ih_lia | apply ih_f2_out; exact N1].
      - split; [apply (fld_munch _ m M' _ 8 _ F12 MU); cbn [disjoint_from]; ih_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F08 MU); cbn [disjoint_from]; ih_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F24 MU); cbn [disjoint_from]; ih_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F32 MU); cbn [disjoint_from]; ih_lia|].
        split; [assumption|]. split; assumption.
    Qed.

    Lemma ih_s2 : forall c, WSR AASAN_MEMSET ih_R2 None ih_P2 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (ih_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & Pm & Hc'). ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _). apply ih_shw in GW2.
      destruct (w_junk H e ff fp XSc s LB m (ff + 224) 16 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J & HJ).
      apply (wmemset Q ih_R2 ih_R3 None (fun m' => m' = m /\ ih_P2 m') ih_P3 0 c (960452 + 3652) (ff + 224) 0 16 J Hc').
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - unfold bp_flw. cbn [fst snd]. ih_lia.
      - exact I.
      - lia.
      - lia.
      - unfold WO_FLAGP. lia.
      - exact I.
      - intros m' (-> & S & _). split; [exact HJ|]. split.
        + apply w_acc; [|lia]. apply (ih_addr m ih_f1 224 16 S GW2); try lia.
          all: try ih_dlia.
          intros j Hj. apply ih_f1_in. ih_dlia.
        + exact (w_shvis H HH0 e ff fp XSc s LB m (ff + 224) 16 HP HI ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros R R' (_ & _ & _ & _ & R18 & R24 & R22) K. unfold ih_R3. repeat split; ih_kreg.
      - intros m1 m' (-> & S & F12 & F36 & F64 & F08) MU WM CZ.
        split; [split|].
        + apply (ih_shf_out m m' _ ih_f1 S MU). intros k Hk. cbn [disjoint_from]. ih_lia.
        + split; [apply (fld_munch _ m m' _ 8 _ F12 MU); cbn [disjoint_from]; ih_lia|].
          split; [apply (fld_munch _ m m' _ 8 _ F36 MU); cbn [disjoint_from]; ih_lia|].
          split; [apply (fld_munch _ m m' _ 8 _ F64 MU); cbn [disjoint_from]; ih_lia|].
          apply (fld_munch _ m m' _ 8 _ F08 MU); cbn [disjoint_from]; ih_lia.
        + split.
          * pose proof (w_zero_fld m' (ff + 224) (Z.to_nat 16) 0 CZ ltac:(lia) ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
          * pose proof (w_zero_fld m' (ff + 224) (Z.to_nat 16) 8 CZ ltac:(lia) ltac:(lia)) as Z8.
            replace (ff + 232) with (ff + 224 + 8) by lia. exact Z8.
      - exact ih_s3.
    Qed.

    Lemma ih_s1 : forall c, WSR (960452 + 3408) ih_R1 None ih_P1 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (960452 + 3408) AASAN_MEMSET ih_R1 ih_R2 None ih_P1 ih_P2 0 c Hc); [|exact ih_s2].
      intros R F fc m XSc s LB (R18 & R22) RC (S & F12 & F36 & F64 & F08) HI HSL HSE. ih_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_ih1_ea7c4 R F fc m ff) as (R' & M' & RUN & MU & WM & POST).
      { unfold wd_ih1_pre. split; [exact C20|]. split; [exact C19|]. split; [exact GW2 | lia]. }
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST.
      split; [ih_flw|]. split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R2, ih_R1 in *; repeat split; ih_kreg|].
      split.
      - apply (ih_shf_munch m M' _ ih_g ih_f1 S MU). intros k Hk.
        destruct (ih_rdec 28 31 k) as [Wr|N1]; [right; rewrite ih_f1_in by lia; ih_enum Wr|].
        destruct (ih_rdec 44 47 k) as [Wr|N2]; [right; rewrite ih_f1_in by lia; ih_enum Wr|].
        destruct (ih_rdec 158 208 k) as [Wr|N3]; [right; rewrite ih_f1_in by lia; ih_enum Wr|].
        left. split; [cbn [disjoint_from]; ih_lia | apply ih_f1_out; lia].
      - split; [apply (fld_munch _ m M' _ 8 _ F12 MU); cbn [disjoint_from]; ih_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F36 MU); cbn [disjoint_from]; ih_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F64 MU); cbn [disjoint_from]; ih_lia|].
        apply (fld_munch _ m M' _ 8 _ F08 MU); cbn [disjoint_from]; ih_lia.
    Qed.

    Lemma ih_s0 : forall c, WSR BP_HDR (bp_r480 ff) None ih_P0 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q BP_HDR (960452 + 3408) (bp_r480 ff) ih_R1 None ih_P0 ih_P1 0 c Hc); [|exact ih_s1].
      intros R F fc m XSc s LB (R18 & R21 & R22 & _) RC (S & F04 & F12 & F36 & F64 & F08) HI HSL HSE. ih_geo_intro.
      pose proof ih_par as (_ & _ & _ & _ & _ & PW & PN & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (wd_ih0_ea7c4 R F fc m ff (wS1 e) ASHADOW_BASE (w_words e) (w_n e)) as (R' & M' & RUN & EM & POST).
      { unfold wd_ih0_pre. split; [exact R18|]. split; [exact R22|]. split; [exact C9|]. split; [exact F04|].
        split; [exact F12|]. split; [exact (ih_sl40 m HSL)|]. unfold ASHADOW_BASE. lia. }
      { exact HW. }
      subst M'. decompose [and] POST. clear POST.
      exists R', m, []. split; [exact RUN|]. split; [apply munch_refl|]. split; [intros x Hx; exact Hx|].
      split; [apply Forall_nil|]. split; [apply Forall_nil|].
      split; [unfold bp_rc; repeat split; ih_kreg|]. split; [unfold ih_R1; split; ih_kreg|].
      split; [exact S|]. split; [exact F12|]. split; [exact F36|]. split; [exact F64 | exact F08].
    Qed.

    Lemma ih_start : forall msF mo R F fc,
      as_VIS H s0 msF = MS R F (Z_to_bv 64 BP_HDR) fc None m0 (seg_rom asegs) -> rfull R -> frm_zero fc ->
      as_AKREL H s0 (mkCfg msF mo) -> as_MPRES H mo0 mo -> bp_rc H e ff R -> bp_r480 ff R ->
      as_SR H Q (mkCfg msF mo).
    Proof.
      intros msF mo R F fc HV HRF HFZ HAK HMP HRC HRG.
      pose proof ih_par as (F04 & F12 & F36 & F64 & F08 & _).
      apply (wstart Q msF mo R F fc BP_HDR (bp_r480 ff) ih_P0 HV HRF HFZ HAK HMP HSL0 HRC HRG); [|exact ih_s0].
      split; [exact (ih_shad_init m0 HSH0)|]. split; [exact F04|]. split; [exact F12|].
      split; [exact F36|]. split; [exact F64 | exact F08].
    Qed.
  End Path.

  Lemma pm_ih : forall e ff fp Q mo0, w_words e <> 0 -> w_n e <= 4 -> bp_kwcf H e ff fp Q mo0 -> bp_khdr H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 HW HN HK s LB LBs m mo msF R F fc XSc w c HV HRF HFZ HAK HMP HP HI HSL HSH HRC HRG HWL HPF.
    pose proof (proj1 HPF) as HPP.
    pose proof (bp_pp_mdef H w LB LBs m c (proj1 HPF)) as HMD.
    pose proof (bp_al_res H w s _ (proj1 (proj2 (proj2 HPF)))) as HAL.
    eapply ih_start; eassumption.
  Qed.
End IH.
