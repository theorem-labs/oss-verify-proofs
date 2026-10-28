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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_TablImg LbB_PmSL LbB_PmBMT LbB_PmBMRS LbB_PmBMT2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma bt_w1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate. Qed.

Lemma bt_fld1_bv : forall m a v v', Z_to_bv 8 v = Z_to_bv 8 v' -> fldA m a 1 v -> fldA m a 1 v'.
Proof. unfold fldA, fld. intros m a v v' E F. rewrite bt_w1 in *. rewrite F, E. reflexivity. Qed.

Lemma bt_mrd_of_rdn1 : forall segs m a b, PropExec.rdn segs m a 1 = Some [b] -> mrd segs m a = Some b.
Proof.
  intros segs m a b R. cbn [PropExec.rdn] in R. unfold mrd.
  destruct (m a) as [b'|]; [injection R as ->; reflexivity|].
  change (BLPropExec.seg_rom segs a) with (PropExec.seg_rom segs a).
  destruct (PropExec.seg_rom segs a) as [b'|]; [injection R as ->; reflexivity | discriminate].
Qed.

Lemma bt_byte_of_u8arr : forall m A (l : list Z) k, u8arr asegs m A (map (Z_to_bv 8) l) -> (k < length l)%nat ->
  fldA m (A + Z.of_nat k) 1 (nth k l 0).
Proof.
  intros m A l k U Hk. destruct U as [(B0 & B1 & B) _].
  pose proof (B k ltac:(rewrite length_map; lia)) as Bk.
  rewrite nth_error_map, (nth_error_nth' l 0 Hk) in Bk. cbn [option_map] in Bk.
  unfold fldA, fld. rewrite bt_w1. exact (rdn1_of_mrd _ _ _ _ Bk).
Qed.

Lemma bt_u8arr_of_bytes : forall m A (l : list Z),
  (forall k, (k < length l)%nat -> fldA m (A + Z.of_nat k) 1 (nth k l 0)) ->
  wr_at asegs m A (Z.of_nat (length l)) -> u8arr asegs m A (map (Z_to_bv 8) l).
Proof.
  intros m A l F W. split; [|rewrite length_map; exact W].
  destruct W as (W0 & W1 & _). split; [exact W0|]. split; [rewrite length_map; exact W1|].
  intros i Hi. rewrite length_map in Hi. pose proof (F i Hi) as Fi. unfold fldA, fld in Fi. rewrite bt_w1 in Fi.
  rewrite nth_error_map, (nth_error_nth' l 0 Hi). cbn [option_map]. exact (bt_mrd_of_rdn1 _ _ _ _ Fi).
Qed.

Lemma bt_wr_mono : forall m m' a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (W0 & W1 & W) M. split; [exact W0|]. split; [exact W1|]. intros i Hi. apply M, W, Hi. Qed.

Lemma bt_fld_of_cells4 : forall m a z, rw_cells asegs m a [C4 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 4 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Lemma bt_rdec : forall lo hi k, {lo <= k < hi} + {~ (lo <= k < hi)}.
Proof. intros lo hi k. destruct (Z_le_gt_dec lo k), (Z_lt_ge_dec k hi); [left; lia | right; lia | right; lia | right; lia]. Qed.

Definition bt_g (k : Z) : Z := nth (Z.to_nat k) (wo_sh [14; 20; 21]%nat) 0.
Definition bt_inr (lo hi k : Z) : bool := (lo <=? k) && (k <? hi).
Definition bt_f1 (k : Z) : Z := if bt_inr 52 55 k || bt_inr 68 71 k || bt_inr 220 270 k then 0 else bt_g k.
Definition bt_f2 (k : Z) : Z := if bt_inr 60 63 k then 0 else bt_f1 k.
Definition bt_f3 (k : Z) : Z := if bt_inr 220 270 k then 0 else bt_g k.

Lemma bt_len : length (wo_sh [14; 20; 21]%nat) = 476%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma bt_inr_t : forall lo hi k, lo <= k < hi -> bt_inr lo hi k = true.
Proof. intros lo hi k Hk. unfold bt_inr. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.

Lemma bt_inr_f : forall lo hi k, ~ (lo <= k < hi) -> bt_inr lo hi k = false.
Proof. intros lo hi k Hk. unfold bt_inr. destruct (Z.leb_spec lo k), (Z.ltb_spec k hi); cbn; try reflexivity; lia. Qed.

Lemma bt_g_range : forall lo n v, forallb (fun j => bt_g (lo + Z.of_nat j) =? v) (seq 0 n) = true ->
  forall k, lo <= k < lo + Z.of_nat n -> bt_g k = v.
Proof.
  intros lo n v B k Hk. rewrite forallb_forall in B.
  specialize (B (Z.to_nat (k - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in B by lia. replace (lo + (k - lo)) with k in B by lia. apply Z.eqb_eq, B.
Qed.

Lemma bt_g248 : forall k, 52 <= k < 55 \/ 60 <= k < 63 \/ 68 <= k < 71 \/ 220 <= k < 270 -> bt_g k = 248.
Proof.
  intros k [Hk|[Hk|[Hk|Hk]]];
    [apply (bt_g_range 52 3) | apply (bt_g_range 60 3) | apply (bt_g_range 68 3) | apply (bt_g_range 220 50)];
    first [vm_compute; reflexivity | lia].
Qed.

Lemma bt_g0 : forall k, 420 <= k < 428 -> bt_g k = 0.
Proof. intros k Hk. apply (bt_g_range 420 8); [vm_compute; reflexivity | lia]. Qed.

Lemma bt_f1_in : forall k, 52 <= k < 55 \/ 68 <= k < 71 \/ 220 <= k < 270 -> bt_f1 k = 0.
Proof.
  intros k Hk. unfold bt_f1.
  destruct Hk as [Hk|[Hk|Hk]]; rewrite (bt_inr_t _ _ k Hk);
    destruct (bt_inr 52 55 k), (bt_inr 68 71 k), (bt_inr 220 270 k); reflexivity.
Qed.

Lemma bt_f1_out : forall k, ~ (52 <= k < 55 \/ 68 <= k < 71 \/ 220 <= k < 270) -> bt_f1 k = bt_g k.
Proof. intros k N. unfold bt_f1. rewrite !bt_inr_f by lia. reflexivity. Qed.

Lemma bt_f2_in : forall k, 60 <= k < 63 -> bt_f2 k = 0.
Proof. intros k Hk. unfold bt_f2. rewrite bt_inr_t by lia. reflexivity. Qed.

Lemma bt_f2_out : forall k, ~ (60 <= k < 63) -> bt_f2 k = bt_f1 k.
Proof. intros k N. unfold bt_f2. rewrite bt_inr_f by lia. reflexivity. Qed.

Lemma bt_f3_in : forall k, 220 <= k < 270 -> bt_f3 k = 0.
Proof. intros k Hk. unfold bt_f3. rewrite bt_inr_t by lia. reflexivity. Qed.

Lemma bt_f3_out : forall k, ~ (220 <= k < 270) -> bt_f3 k = bt_g k.
Proof. intros k N. unfold bt_f3. rewrite bt_inr_f by lia. reflexivity. Qed.

Lemma bt_f23 : forall k, ~ (52 <= k < 55 \/ 60 <= k < 63 \/ 68 <= k < 71) -> bt_f3 k = bt_f2 k.
Proof.
  intros k N. rewrite bt_f2_out by lia. destruct (bt_rdec 220 270 k) as [W|W].
  - rewrite bt_f3_in, bt_f1_in by lia. reflexivity.
  - rewrite bt_f3_out, bt_f1_out by lia. reflexivity.
Qed.

Lemma bt_cs : forall p n, TablRep.chk_cstr ASEGS tiA p n = true ->
  existsb (fun g => let '(b, sz, _) := g in (b =? p) && (sz =? n + 1)) aglobals = true -> 65600 <= p -> 0 <= n ->
  cstrA p n.
Proof.
  intros p n C G P0 N0. apply existsb_exists in G as ([[b sz] rz] & Hg & E).
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst b sz.
  eapply (cstrA_of p n p (n + 1) rz C Hg); lia.
Qed.

Ltac bt_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac bt_kreg :=
  first
    [ assumption
    | match goal with K : forall r, In r _ -> getr ?R' r = getr ?R r |- getr ?R' ?n = _ =>
        rewrite (K n) by bt_inl; assumption end
    | match goal with Hr : getr ?R' ?n = _ |- getr ?R' ?n = _ =>
        rewrite Hr; apply bv_eq; vm_compute; reflexivity end
    | match goal with K : forall r, In r _ -> getr ?R' r = getr ?R r, Hr : getr ?R ?n = _ |- getr ?R' ?n = _ =>
        rewrite (K n) by bt_inl; rewrite Hr; apply bv_eq; vm_compute; reflexivity end ].

Ltac bt_zn :=
  repeat match goal with |- context [Z.of_nat ?n] =>
    let z := eval vm_compute in (Z.of_nat n) in progress change (Z.of_nat n) with z end.

Ltac bt_lia := unfold sh, ASHADOW_BASE, WO_FLAGP, AINTRIN_STACK, DS_SIZE, DS_ERR_OFF, nsh; cbn [fst snd]; bt_zn; lia.

Ltac bt_wbyte :=
  match goal with
  | |- fldA ?M (sh ?f + ?k) 1 ?v =>
      let N := eval vm_compute in (ASHADOW_BASE + k) in
      replace (sh f + k) with (f / 8 + N) by (unfold sh, ASHADOW_BASE; ring);
      match goal with
      | Hb : fldA M (f / 8 + N) 1 ?v' |- _ =>
          eapply bt_fld1_bv; [| exact Hb]; apply bv_eq; vm_compute; reflexivity
      end
  end.

Ltac bt_enum Hr :=
  lazymatch type of Hr with
  | ?lo <= ?k < ?hi =>
      destruct (Z.eq_dec k lo) as [->|NE];
      [ clear Hr; bt_wbyte
      | let lo' := eval vm_compute in (lo + 1) in
        let Hr' := fresh "Hr" in
        assert (Hr' : lo' <= k < hi) by lia; clear Hr NE;
        lazymatch eval vm_compute in (lo' =? hi) with
        | true => exfalso; lia
        | false => bt_enum Hr'
        end ]
  end.

Ltac bt_dlia := Z.div_mod_to_equations; lia.

Ltac bt_fa := repeat (apply Forall_cons; [cbn [fst snd]; bt_lia |]); apply Forall_nil.

Ltac bt_flw := repeat (apply Forall_cons; [unfold bp_flw; cbn [fst snd]; bt_lia |]); apply Forall_nil.

Ltac bt_wfree := repeat (apply Forall_cons; [unfold wfree; cbv beta iota; first [exact I | unfold sh, ASHADOW_BASE, nsh, DS_SIZE; cbn [fst snd]; bt_dlia] |]); apply Forall_nil.

Section BT.
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
  Hypothesis HTR : pm_tr_ok H.

  Lemma bt_dtr : ds_tr_ok H.
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
    Hypothesis HK : bp_kmagf H e ff fp Q mo0.
    Hypothesis HN : 5 <= w_n e.
    Hypothesis HW : w_words e <> 0.
    Hypothesis HSL0 : bp_slots H e ff m0.
    Hypothesis HSH0 : bp_shad ff [14; 20; 21]%nat m0.

    Let HH0 : asan_rt_hyps H := rt_bp_base H HHbp.

    Local Abbreviation WSR := (wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0).
    Local Abbreviation LF6 := ((6, ff, fp) :: w_LF e).

    Lemma bt_geo : ff mod 64 = 0 /\ 7278592 <= ff /\ ff + 4096 <= w_lo e /\ w_lo e + 32768 <= wS1 e
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

    Ltac bt_geo_intro := pose proof bt_geo as (Ga & Gb & Gc & Gd & Ge & Gf & Gg & Gh & Gi & Gj & Gk).

    Lemma bt_q32 : 32 * (ff / 32) = ff.
    Proof. pose proof bt_geo as (Ga & _). bt_dlia. Qed.

    Lemma bt_q8 : 4 * (ff / 32) = ff / 8.
    Proof. pose proof bt_geo as (Ga & _). bt_dlia. Qed.

    Lemma bt_sp : 2 ^ 45 + 16 <= wS1 e <= 2 ^ 47 /\ wS1 e mod 16 = 0.
    Proof. pose proof (wS1_facts H e HP) as (W1 & W2 & W3 & W4 & W5 & W6). bt_geo_intro. split; [lia | bt_dlia]. Qed.

    Local Abbreviation wstart := (w_start H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wchunk := (w_chunk H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wexit := (w_exit H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wgeo := (w_geo H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wobj := (w_obj H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).
    Local Abbreviation wfldkeep := (w_fld_keep H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL).

    Lemma bt_meas : pm_meas_ok (pw_n H w) LBs.
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

    Local Abbreviation wmemset := (w_memset H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL bt_meas).
    Local Abbreviation wctor := (w_ctor H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL bt_meas).
    Local Abbreviation wcseq := (w_cseq H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL bt_meas).
    Local Abbreviation wnum := (w_num H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL bt_meas).
    Local Abbreviation wdtor := (w_dtor H HHbp ds_repA DSL bt_dtr e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL bt_meas).

    Definition bt_IC : Z := st_icount (pc_state c0).

    Lemma bt_par : fldA m0 (ff + 3504) 8 (w_words e) /\ fldA m0 (ff + 3512) 8 (w_n e) /\ fldA m0 (ff + 3536) 8 bt_IC
      /\ fldA m0 (ff + 3464) 8 (ff + 3376) /\ fldA m0 (ff + 3408) 8 0
      /\ 0 <= w_words e < 2 ^ 64 /\ 0 <= w_n e < 2 ^ 64 /\ 0 <= bt_IC < 2 ^ 64.
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
      unfold bt_IC. lia.
    Qed.

    Definition bt_shf (m : mem) (f : Z -> Z) : Prop := forall k, 0 <= k < 476 -> fldA m (sh ff + k) 1 (f k).

    Lemma bt_shad_init : forall m, bp_shad ff [14; 20; 21]%nat m -> bt_shf m bt_g.
    Proof.
      intros m S k Hk. unfold bp_shad in S.
      pose proof (bt_byte_of_u8arr m (sh ff) _ (Z.to_nat k) S) as B.
      rewrite bt_len in B. specialize (B ltac:(lia)). rewrite Z2Nat.id in B by lia. exact B.
    Qed.

    Lemma bt_shad_fin : forall m, bt_shf m bt_g -> wr_at asegs m (sh ff) 476 -> bp_shad ff [14; 20; 21]%nat m.
    Proof.
      intros m S W. unfold bp_shad. apply bt_u8arr_of_bytes; [|rewrite bt_len; exact W].
      intros k Hk. rewrite bt_len in Hk. pose proof (S (Z.of_nat k) ltac:(lia)) as B.
      unfold bt_g in B. rewrite Nat2Z.id in B. exact B.
    Qed.

    Lemma bt_shw : forall m, wr_at asegs m (ff / 8 + 2147450880) 512 -> wr_at asegs m (sh ff) 512.
    Proof. intros m W. replace (sh ff) with (ff / 8 + 2147450880) by (unfold sh, ASHADOW_BASE; lia). exact W. Qed.

    Lemma bt_shf_munch : forall m m' W f f', bt_shf m f -> munch W m m' ->
      (forall k, 0 <= k < 476 -> (disjoint_from W (sh ff + k) 1 /\ f' k = f k) \/ fldA m' (sh ff + k) 1 (f' k)) ->
      bt_shf m' f'.
    Proof.
      intros m m' W f f' S MU K k Hk. bt_geo_intro.
      destruct (K k Hk) as [[D E]|F]; [|exact F].
      rewrite E. apply (fld_munch W m m' _ 1 _ (S k Hk) MU D); bt_lia.
    Qed.

    Lemma bt_shf_out : forall m m' W f, bt_shf m f -> munch W m m' ->
      (forall k, 0 <= k < 476 -> disjoint_from W (sh ff + k) 1) -> bt_shf m' f.
    Proof. intros m m' W f S MU D. apply (bt_shf_munch m m' W f f S MU). intros k Hk. left. split; [apply D, Hk | reflexivity]. Qed.

    Lemma bt_shf_keep : forall X m m' f, bt_shf m f -> wxkeep H e ff fp LB0 X m m' ->
      Forall (fun iv : Z * Z => sh ff + 476 <= fst iv \/ snd iv <= sh ff) X -> bt_shf m' f.
    Proof.
      intros X m m' f S K FX k Hk.
      apply (wfldkeep X m m' (sh ff + k) 1 (f k) K); [right; bt_zn; lia | | apply S, Hk].
      eapply Forall_impl; [|exact FX]. intros [lo hi] Hiv. cbn [fst snd] in *. bt_zn. lia.
    Qed.

    Lemma bt_fkeep : forall X m m' a k v, wxkeep H e ff fp LB0 X m m' -> ff <= a -> a + Z.of_nat k <= ff + 4088 ->
      Forall (fun iv : Z * Z => a + Z.of_nat k <= fst iv \/ snd iv <= a) X -> fldA m a k v -> fldA m' a k v.
    Proof. intros X m m' a k v K A0 A1 FX F. exact (wfldkeep X m m' a k v K (or_introl (conj A0 A1)) FX F). Qed.

    Lemma bt_addr : forall m f k n, bt_shf m f -> wr_at asegs m (sh ff) 512 ->
      0 <= k -> 0 < n -> k mod 8 = 0 -> n mod 8 = 0 -> k + n <= 3808 ->
      (forall j, k / 8 <= j < (k + n) / 8 -> f j = 0) -> addressable m (ff + k) n.
    Proof.
      intros m f k n S W K0 N0 K8 N8 KN Z0. bt_geo_intro.
      split; [lia|]. split; [lia|]. split; [bt_dlia|].
      unfold shadow_of. replace (n mod 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact N8). rewrite app_nil_r.
      replace (repeat (b8 0) (Z.to_nat (n / 8))) with (map (Z_to_bv 8) (repeat 0 (Z.to_nat (n / 8)))) by (rewrite map_repeat; reflexivity).
      apply bt_u8arr_of_bytes.
      - intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat.
        replace (sh (ff + k) + Z.of_nat i) with (sh ff + (k / 8 + Z.of_nat i)) by (unfold sh; bt_dlia).
        pose proof (S (k / 8 + Z.of_nat i) ltac:(bt_dlia)) as B. rewrite (Z0 (k / 8 + Z.of_nat i) ltac:(bt_dlia)) in B. exact B.
      - rewrite repeat_length. replace (sh (ff + k)) with (sh ff + k / 8) by (unfold sh; bt_dlia).
        apply (bp_wr_sub m (sh ff) 512 (k / 8) (Z.of_nat (Z.to_nat (n / 8))) W); bt_dlia.
    Qed.

    Lemma bt_obj : forall m f k n, bt_shf m f -> wr_at asegs m (sh ff) 512 ->
      0 <= k -> 0 < n -> k mod 8 = 0 -> n mod 8 = 0 -> k + n <= 3808 ->
      (forall j, k / 8 <= j < (k + n) / 8 -> f j = 0) ->
      ds_obj H LF6 m (wS1 e) (ff + k) n /\ obj_inframe LF6 (ff + k) n.
    Proof.
      intros m f k n S W K0 N0 K8 N8 KN Z0. bt_geo_intro.
      apply (wobj m k n); [lia | lia | unfold WO_FLAGP; lia | bt_dlia | exact (bt_addr m f k n S W K0 N0 K8 N8 KN Z0)].
    Qed.

    Lemma bt_dsobj : forall m f, bt_shf m f -> wr_at asegs m (sh ff) 512 -> (forall j, 220 <= j < 269 -> f j = 0) ->
      ds_obj H LF6 m (wS1 e) (ff + 1760) DS_SIZE /\ obj_inframe LF6 (ff + 1760) DS_SIZE.
    Proof. intros m f S W Z0. apply (bt_obj m f 1760 392 S W); [lia | lia | bt_dlia | bt_dlia | lia | intros j Hj; apply Z0; bt_dlia]. Qed.

    Lemma bt_sl40 : forall m, bp_slots H e ff m -> fldA m (wS1 e + 40) 8 ASHADOW_BASE.
    Proof.
      intros m (_ & S2 & _). unfold fldA, fld.
      pose proof (rw_cells_read asegs m (wS1 e + 24) _ 16%nat _ S2 eq_refl) as RD.
      replace (wS1 e + 24 + Z.of_nat 16) with (wS1 e + 40) in RD by lia.
      rewrite <- rdn_of_ov. exact RD.
    Qed.

    Lemma bt_pin : forall pc REGS S P spent c, WSR pc REGS S P spent c ->
      exists m XSc s LB, winv H e ff fp XSc s LB m /\ P m /\ WSR pc REGS S (fun m' => m' = m /\ P m') spent c.
    Proof.
      intros pc REGS S P spent c (s & R & F & fc & m & XSc & LB & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
      exists m, XSc, s, LB. split; [exact A6|]. split; [exact A13|].
      exists s, R, F, fc, m, XSc, LB. repeat (split; [assumption|]). split; [split; [reflexivity | exact A13] | exact A14].
    Qed.


    Lemma bt_wsr_weak : forall pc REGS S (P P' : mem -> Prop) spent c,
      (forall m XSc s LB, winv H e ff fp XSc s LB m -> P m -> P' m) ->
      WSR pc REGS S P spent c -> WSR pc REGS S P' spent c.
    Proof.
      intros pc REGS S P P' spent c K (s & R & F & fc & m & XSc & LB & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
      exists s, R, F, fc, m, XSc, LB. repeat (split; [assumption|]). split; [exact (K m XSc s LB A6 A13) | exact A14].
    Qed.

    Definition bt_h (k : Z) : Z := nth (Z.to_nat k) (wo_sh [14; 15; 20; 21]%nat) 0.

    Lemma bt_f3h : forall k, 0 <= k < 476 -> bt_f3 k = bt_h k.
    Proof.
      intros k Hk.
      assert (C : forallb (fun j => bt_f3 (Z.of_nat j) =? bt_h (Z.of_nat j)) (seq 0 476) = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in C. specialize (C (Z.to_nat k) ltac:(apply in_seq; lia)).
      rewrite Z2Nat.id in C by lia. apply Z.eqb_eq in C. exact C.
    Qed.

    Lemma bt_shad_mid : forall m, bt_shf m bt_f3 -> wr_at asegs m (sh ff) 476 -> bp_shad ff [14; 15; 20; 21]%nat m.
    Proof.
      intros m S W. unfold bp_shad.
      assert (L2 : length (wo_sh [14; 15; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
      apply bt_u8arr_of_bytes; [|rewrite L2; exact W].
      intros k Hk. rewrite L2 in Hk. pose proof (S (Z.of_nat k) ltac:(lia)) as B.
      rewrite bt_f3h in B by lia. unfold bt_h in B. rewrite Nat2Z.id in B. exact B.
    Qed.

    Definition bt_R2 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 5056) /\ getr R 10 = wz (ff + 416) /\ getr R 11 = wz 0 /\ getr R 12 = wz 16
      /\ getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 416) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
    Definition bt_R3 (R : bvmap 5 word) : Prop :=
      getr R 18 = wz (ff + 3456) /\ getr R 24 = wz (ff + 416) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
    Definition bt_R4 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz (0xea7c4 + 5136) /\ getr R 10 = wz (ff + 1760) /\ getr R 11 = wz (ff + 416)
      /\ getr R 12 = wz (ff + 3376) /\ getr R 13 = wz (ff + 480) /\ getr R 14 = wz ((-4) mod 2 ^ 64)
      /\ getr R 15 = wz (ff + 544) /\ getr R 18 = wz (ff + 1760) /\ getr R 25 = wz (ff + 480)
      /\ getr R 26 = wz (ff + 544) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
    Definition bt_R5 (R : bvmap 5 word) : Prop :=
      getr R 18 = wz (ff + 1760) /\ getr R 25 = wz (ff + 480) /\ getr R 26 = wz (ff + 544)
      /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.
    Definition bt_R6 (R : bvmap 5 word) : Prop :=
      getr R 1 = wz BM_MID /\ getr R 10 = wz (ff + 1760) /\ getr R 11 = wz 147936 /\ getr R 12 = wz 29
      /\ getr R 18 = wz (ff + 1760) /\ getr R 22 = wz (ff + 3504) /\ getr R 27 = wz ASHADOW_BASE.

    Definition bt_P0 (m : mem) : Prop :=
      bt_shf m bt_g /\ fldA m (ff + 3536) 8 bt_IC /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3408) 8 0.
    Definition bt_P1 (m : mem) : Prop :=
      bt_shf m bt_f1 /\ fldA m (ff + 3536) 8 bt_IC /\ fldA m (ff + 3464) 8 (ff + 3376) /\ fldA m (ff + 3408) 8 0.
    Definition bt_P2 (m : mem) : Prop := bt_P1 m /\ fldA m (ff + 416) 8 0 /\ fldA m (ff + 424) 8 0.
    Definition bt_P3 (m : mem) : Prop :=
      bt_shf m bt_f2 /\ fldA m (ff + 3408) 8 0 /\ fldA m (ff + 416) 8 0
      /\ fldA m (ff + 424) 8 0 /\ fldA m (ff + 432) 8 bt_IC /\ fldA m (ff + 480) 2 0 /\ fldA m (ff + 544) 2 0.
    Definition bt_P4 (m : mem) : Prop := bt_shf m bt_f2 /\ fldA m (ff + 480) 2 0 /\ fldA m (ff + 544) 2 0.
    Definition bt_P5 (m : mem) : Prop := bt_shf m bt_f3.

    Ltac bt_r19 :=
      match goal with Hr : getr ?R' 19 = wz (ff / 8 + ASHADOW_BASE) |- _ =>
        assert (getr R' 19 = wz (sh ff)) by (rewrite Hr; f_equal; unfold sh; lia); clear Hr end.

    Ltac bt_pre := pose proof bt_sp as (SP1 & SP2); pose proof bt_q32 as QF; repeat split;
      match goal with
      | |- context [_ mod _] => first [exact SP2 | clear - QF; Z.div_mod_to_equations; lia]
      | _ => lia
      end.

    Lemma bt_s6 : forall c, WSR APUT_CSEQ bt_R6 (Some (ff + 1760, -4, 0)) bt_P5 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (bt_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & S & Hc'). bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _). apply bt_shw in GW2.
      assert (CS : cstrA 147936 29) by (apply bt_cs; [vm_compute; reflexivity | vm_compute; reflexivity | lia | lia]).
      destruct (cstrA_img 147936 29 m0 CS (winv_mi H e ff fp XSc0 s0 LB0 m0 HI0)) as (I1 & I2 & I3 & I4 & I5).
      apply (wcseq HCSEQ Q bt_R6 (bm_mid_regs ff) (fun m' => m' = m /\ bt_P5 m') bt_P5 0 c BM_MID (ff + 1760) (-4) 0 147936 29 Hc').
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - unfold BM_MID. lia.
      - unfold ds_cost, PM_RESERVE. lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S'). apply (bt_dsobj m bt_f3 S' GW2). intros j Hj. apply bt_f3_in. lia.
      - exact I3.
      - exact I1.
      - exact I2.
      - exact I4.
      - exact I5.
      - lia.
      - intros R R' (_ & _ & _ & _ & R18 & R22 & R27) K K10. unfold bm_mid_regs.
        split; [|split]; (eapply eq_trans; [apply K; bt_inl|]); assumption.
      - intros m1 m' (-> & S') KX. apply (bt_shf_keep _ m m' bt_f3 S' KX). bt_fa.
      - intros c' Hc2.
        apply (pm_bm_t2 H HHbp ds_repA DSL bt_dtr HCSEQ HU32 HDTOR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL
                 bt_meas HPF HW HN Q HK (0 + 29) (0 + ds_cost (0 + 29)) c').
        + apply (bt_wsr_weak _ _ _ bt_P5 _ _ _); [|exact Hc2].
          intros m2 XSc2 s2 LB2 HI2 S2.
          pose proof (wgeo XSc2 s2 LB2 m2 HI2) as (_ & GW3 & _). apply bt_shw in GW3.
          split; [apply bt_shad_mid; [exact S2 | apply (wr_at_sub asegs m2 (sh ff) 512 (sh ff) 476 GW3); lia]|].
          apply (bt_dsobj m2 bt_f3 S2 GW3). intros j Hj. apply bt_f3_in. lia.
        + unfold bm_mid_ok, ds_cost, PM_RESERVE. lia.
    Qed.

    Lemma bt_s5 : forall c, WSR (0xea7c4 + 5136) bt_R5 (Some (ff + 1760, -4, 0)) bt_P4 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (0xea7c4 + 5136) APUT_CSEQ bt_R5 bt_R6 _ bt_P4 bt_P5 0 c Hc); [|exact bt_s6].
      intros R F fc m XSc s LB (R18 & R25 & R26 & R22 & R27) RC (S & F88 & F52) HI HSL HSE. bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (_ & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_ts_bp R F fc m (ff / 32) (wS1 e)) as (R' & M' & RUN & MU & WM & POST).
      { unfold bmR_ts_pre. rewrite bt_q8, bt_q32.
        split; [exact C2|]. split; [exact R18|]. split; [rewrite C19; f_equal; unfold sh; lia|]. split; [exact C20|].
        split; [exact R25|]. split; [exact R26|].
        split; [exact (proj1 (fld2_split01 m (ff + 544) 0 ltac:(lia) ltac:(lia) (or_introl eq_refl) F52))|].
        split; [exact (proj1 (fld2_split01 m (ff + 480) 0 ltac:(lia) ltac:(lia) (or_introl eq_refl) F88))|].
        split; [apply (wr_at_sub asegs m _ 512 _ _ GW2); lia|].
        bt_pre. }
      rewrite ?bt_q8 in POST. rewrite ?bt_q32 in POST. rewrite ?bt_q8 in MU. rewrite ?bt_q32 in MU.
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST. bt_r19.
      split; [bt_flw|]. split; [bt_wfree|].
      split; [unfold bp_rc; repeat split; bt_kreg|]. split; [unfold bt_R6; repeat split; bt_kreg|].
      apply (bt_shf_munch m M' _ bt_f2 bt_f3 S MU). intros k Hk.
      destruct (bt_rdec 52 55 k) as [Wr|N1]; [right; rewrite bt_f3_out, bt_g248 by lia; bt_enum Wr|].
      destruct (bt_rdec 60 63 k) as [Wr|N2]; [right; rewrite bt_f3_out, bt_g248 by lia; bt_enum Wr|].
      destruct (bt_rdec 68 71 k) as [Wr|N3]; [right; rewrite bt_f3_out, bt_g248 by lia; bt_enum Wr|].
      left. split; [cbn [disjoint_from]; bt_lia | apply bt_f23; lia].
    Qed.

    Lemma bt_s4 : forall c, WSR ADS_CTOR bt_R4 None bt_P3 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (bt_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & Pm & Hc'). bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _). apply bt_shw in GW2.
      destruct (w_junk H e ff fp XSc s LB m (ff + 482) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J1 & HJ1).
      destruct (w_junk H e ff fp XSc s LB m (ff + 546) 22 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J2 & HJ2).
      apply (wctor HCTOR Q bt_R4 bt_R5 (fun m' => m' = m /\ bt_P3 m') bt_P4 0 c
               (0xea7c4 + 5136) (ff + 1760) (ff + 416) (ff + 3376) (ff + 480) (ff + 544) (-4) Hc').
      - intros R (R1 & R10 & R11 & R12 & R13 & R14 & R15 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - unfold PM_RESERVE. lia.
      - lia.
      - lia.
      - unfold DS_SIZE. lia.
      - intros m' (-> & S & F08 & F24 & F32 & F40 & F88 & F52).
        assert (Z52 : forall j, 52 <= j < 55 -> bt_f2 j = 0) by (intros j Hj; rewrite bt_f2_out, bt_f1_in by lia; reflexivity).
        assert (Z60 : forall j, 60 <= j < 63 -> bt_f2 j = 0) by (intros j Hj; apply bt_f2_in; lia).
        assert (Z68 : forall j, 68 <= j < 71 -> bt_f2 j = 0) by (intros j Hj; rewrite bt_f2_out, bt_f1_in by lia; reflexivity).
        assert (Z220 : forall j, 220 <= j < 269 -> bt_f2 j = 0) by (intros j Hj; rewrite bt_f2_out, bt_f1_in by lia; reflexivity).
        assert (Z422 : forall j, 422 <= j < 428 -> bt_f2 j = 0) by (intros j Hj; rewrite bt_f2_out, bt_f1_out, bt_g0 by lia; reflexivity).
        exists [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 bt_IC], J1, J2.
        pose proof bt_par as (_ & _ & _ & _ & _ & _ & _ & PIC).
        split; [exact (proj1 (bt_dsobj m bt_f2 S GW2 Z220))|].
        split; [exact (bp_wr_sub m ff 4096 1760 392 GW1 ltac:(lia) ltac:(lia) ltac:(lia))|].
        split; [exact (proj2 (bt_dsobj m bt_f2 S GW2 Z220))|].
        split; [apply (proj1 (bt_obj m bt_f2 416 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z52; bt_dlia)))|].
        split; [apply (w_u64arr3 m (ff + 416) 0 0 bt_IC);
                [exact F24
                |replace (ff + 416 + 8) with (ff + 424) by lia; exact F32
                |replace (ff + 416 + 16) with (ff + 432) by lia; exact F40
                |exact (bp_wr_sub m ff 4096 416 24 GW1 ltac:(lia) ltac:(lia) ltac:(lia))
                |lia | lia | lia]|].
        split; [reflexivity|].
        split; [apply (proj2 (bt_obj m bt_f2 416 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z52; bt_dlia)))|].
        split; [apply (proj1 (bt_obj m bt_f2 480 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z60; bt_dlia)))|].
        split; [apply (w_str m (ff + 480) J1 F88 (bp_wr_sub m ff 4096 480 2 GW1 ltac:(lia) ltac:(lia) ltac:(lia)));
                replace (ff + 480 + 2) with (ff + 482) by lia; exact HJ1|].
        split; [apply (proj2 (bt_obj m bt_f2 480 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z60; bt_dlia)))|].
        split; [apply (proj1 (bt_obj m bt_f2 544 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z68; bt_dlia)))|].
        split; [apply (w_str m (ff + 544) J2 F52 (bp_wr_sub m ff 4096 544 2 GW1 ltac:(lia) ltac:(lia) ltac:(lia)));
                replace (ff + 544 + 2) with (ff + 546) by lia; exact HJ2|].
        split; [apply (proj2 (bt_obj m bt_f2 544 24 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z68; bt_dlia)))|].
        split; [apply (proj1 (bt_obj m bt_f2 3376 48 S GW2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(intros j Hj; apply Z422; bt_dlia)))|].
        split; [apply (w_cells8_of_fld m (ff + 3376 + 32) 0);
                [replace (ff + 3376 + 32) with (ff + 3408) by lia; exact F08
                |replace (ff + 3376 + 32) with (ff + 3408) by lia; exact (bp_wr_sub m ff 4096 3408 8 GW1 ltac:(lia) ltac:(lia) ltac:(lia))]|].
        intros a Ha. unfold DS_SIZE in Ha. lia.
      - intros R R' (_ & _ & _ & _ & _ & _ & _ & R18 & R25 & R26 & R22 & R27) K. unfold bt_R5. repeat split; bt_kreg.
      - intros m1 m' (-> & S & F08 & F24 & F32 & F40 & F88 & F52) KX.
        split; [apply (bt_shf_keep _ m m' bt_f2 S KX); bt_fa|].
        split; [apply (bt_fkeep _ m m' _ _ _ KX); [lia | bt_zn; lia | bt_fa | exact F88]|].
        apply (bt_fkeep _ m m' _ _ _ KX); [lia | bt_zn; lia | bt_fa | exact F52].
      - exact bt_s5.
    Qed.

    Lemma bt_s3 : forall c, WSR (0xea7c4 + 5056) bt_R3 None bt_P2 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q (0xea7c4 + 5056) ADS_CTOR bt_R3 bt_R4 None bt_P2 bt_P3 0 c Hc); [|exact bt_s4].
      intros R F fc m XSc s LB (R18 & R24 & R22 & R27) RC ((S & F36 & F64 & F08) & F24 & F32) HI HSL HSE. bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _).
      pose proof bt_par as (_ & _ & _ & _ & _ & _ & _ & PIC).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_tc_bp R F fc m (ff / 32) (wS1 e) bt_IC (ff + 3376)) as (R' & M' & RUN & MU & WM & POST).
      { unfold bmR_tc_pre. rewrite bt_q8, bt_q32.
        split; [exact C2|]. split; [exact R18|]. split; [rewrite C19; f_equal; unfold sh; lia|]. split; [exact C20|].
        split; [exact R24|]. split; [exact F36|]. split; [exact F64|].
        split; [apply (wr_at_sub asegs m ff 4096 _ _ GW1); lia|].
        split; [apply (wr_at_sub asegs m _ 512 _ _ GW2); lia|].
        split; [apply (wr_at_sub asegs m ff 4096 _ _ GW1); lia|].
        split; [apply (wr_at_sub asegs m ff 4096 _ _ GW1); lia|].
        bt_pre. }
      rewrite ?bt_q8 in POST. rewrite ?bt_q32 in POST. rewrite ?bt_q8 in MU. rewrite ?bt_q32 in MU.
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST. bt_r19.
      split; [bt_flw|]. split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; bt_kreg|]. split; [unfold bt_R4; repeat split; bt_kreg|].
      split.
      - apply (bt_shf_munch m M' _ bt_f1 bt_f2 S MU). intros k Hk.
        destruct (bt_rdec 60 63 k) as [Wr|N1]; [right; rewrite bt_f2_in by lia; bt_enum Wr|].
        left. split; [cbn [disjoint_from]; bt_lia | apply bt_f2_out; exact N1].
      - split; [apply (fld_munch _ m M' _ 8 _ F08 MU); cbn [disjoint_from]; bt_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F24 MU); cbn [disjoint_from]; bt_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F32 MU); cbn [disjoint_from]; bt_lia|].
        split; [assumption|]. split; assumption.
    Qed.

    Lemma bt_s2 : forall c, WSR AASAN_MEMSET bt_R2 None bt_P1 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. destruct (bt_pin _ _ _ _ _ _ Hc) as (m & XSc & s & LB & HI & Pm & Hc'). bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _). apply bt_shw in GW2.
      destruct (w_junk H e ff fp XSc s LB m (ff + 416) 16 HP HI ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(lia)) as (J & HJ).
      apply (wmemset Q bt_R2 bt_R3 None (fun m' => m' = m /\ bt_P1 m') bt_P2 0 c (0xea7c4 + 5056) (ff + 416) 0 16 J Hc').
      - intros R (R1 & R10 & R11 & R12 & _). repeat split; assumption.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - unfold bp_flw. cbn [fst snd]. bt_lia.
      - exact I.
      - lia.
      - lia.
      - unfold WO_FLAGP. lia.
      - exact I.
      - intros m' (-> & S & _). split; [exact HJ|]. split.
        + apply w_acc; [|lia]. apply (bt_addr m bt_f1 416 16 S GW2); try lia.
          all: try bt_dlia.
          intros j Hj. apply bt_f1_in. bt_dlia.
        + exact (w_shvis H HH0 e ff fp XSc s LB m (ff + 416) 16 HP HI ltac:(lia) ltac:(lia) ltac:(lia)).
      - intros R R' (_ & _ & _ & _ & R18 & R24 & R22 & R27) K. unfold bt_R3. repeat split; bt_kreg.
      - intros m1 m' (-> & S & F36 & F64 & F08) MU WM CZ.
        split; [split|].
        + apply (bt_shf_out m m' _ bt_f1 S MU). intros k Hk. cbn [disjoint_from]. bt_lia.
        + split; [apply (fld_munch _ m m' _ 8 _ F36 MU); cbn [disjoint_from]; bt_lia|].
          split; [apply (fld_munch _ m m' _ 8 _ F64 MU); cbn [disjoint_from]; bt_lia|].
          apply (fld_munch _ m m' _ 8 _ F08 MU); cbn [disjoint_from]; bt_lia.
        + split.
          * pose proof (w_zero_fld m' (ff + 416) (Z.to_nat 16) 0 CZ ltac:(lia) ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
          * pose proof (w_zero_fld m' (ff + 416) (Z.to_nat 16) 8 CZ ltac:(lia) ltac:(lia)) as Z8.
            replace (ff + 424) with (ff + 416 + 8) by lia. exact Z8.
      - exact bt_s3.
    Qed.

    Lemma bt_s1 : forall c, WSR BM_TAIL (bm_rtail ff) None bt_P0 0 c -> as_SR H Q c.
    Proof.
      intros c Hc. apply (wchunk Q BM_TAIL AASAN_MEMSET (bm_rtail ff) bt_R2 None bt_P0 bt_P1 0 c Hc); [|exact bt_s2].
      intros R F fc m XSc s LB (R18 & R22 & R27) RC (S & F36 & F64 & F08) HI HSL HSE. bt_geo_intro.
      pose proof (wgeo XSc s LB m HI) as (GW1 & GW2 & _).
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct (bmR_p_bp R F fc m (ff / 32) (wS1 e)) as (R' & M' & RUN & MU & WM & POST).
      { unfold bmR_p_pre. rewrite bt_q8, bt_q32.
        split; [exact C2|]. split; [rewrite C19; f_equal; unfold sh; lia|]. split; [exact C20|].
        split; [apply (wr_at_sub asegs m _ 512 _ _ GW2); lia|].
        bt_pre. }
      rewrite ?bt_q8 in POST. rewrite ?bt_q32 in POST. rewrite ?bt_q8 in MU. rewrite ?bt_q32 in MU.
      exists R', M'. eexists. split; [exact RUN|]. split; [exact MU|]. split; [exact WM|].
      decompose [and] POST. clear POST. bt_r19.
      split; [bt_flw|]. split; [apply Forall_forall; intros; exact I|].
      split; [unfold bp_rc; repeat split; bt_kreg|]. split; [unfold bt_R2; repeat split; bt_kreg|].
      split.
      - apply (bt_shf_munch m M' _ bt_g bt_f1 S MU). intros k Hk.
        destruct (bt_rdec 52 55 k) as [Wr|N1]; [right; rewrite bt_f1_in by lia; bt_enum Wr|].
        destruct (bt_rdec 68 71 k) as [Wr|N2]; [right; rewrite bt_f1_in by lia; bt_enum Wr|].
        destruct (bt_rdec 220 270 k) as [Wr|N3]; [right; rewrite bt_f1_in by lia; bt_enum Wr|].
        left. split; [cbn [disjoint_from]; bt_lia | apply bt_f1_out; lia].
      - split; [apply (fld_munch _ m M' _ 8 _ F36 MU); cbn [disjoint_from]; bt_lia|].
        split; [apply (fld_munch _ m M' _ 8 _ F64 MU); cbn [disjoint_from]; bt_lia|].
        apply (fld_munch _ m M' _ 8 _ F08 MU); cbn [disjoint_from]; bt_lia.
    Qed.

    Lemma bt_start : forall msF mo R F fc,
      as_VIS H s0 msF = MS R F (Z_to_bv 64 BM_TAIL) fc None m0 (seg_rom asegs) -> rfull R -> frm_zero fc ->
      as_AKREL H s0 (mkCfg msF mo) -> as_MPRES H mo0 mo -> bp_rc H e ff R -> bm_rtail ff R ->
      as_SR H Q (mkCfg msF mo).
    Proof.
      intros msF mo R F fc HV HRF HFZ HAK HMP HRC HRG.
      pose proof bt_par as (_ & _ & F36 & F64 & F08 & _).
      apply (wstart Q msF mo R F fc BM_TAIL (bm_rtail ff) bt_P0 HV HRF HFZ HAK HMP HSL0 HRC HRG); [|exact bt_s1].
      split; [exact (bt_shad_init m0 HSH0)|]. split; [exact F36|]. split; [exact F64 | exact F08].
    Qed.
  End Path.

  Lemma pm_bm_tail : forall e ff fp Q mo0, bp_kmagf H e ff fp Q mo0 -> bm_tail_at H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 HK s LB LBs m mo msF R F fc XSc w c HV HRF HFZ HAK HMP HP HI HSL HSH HRC HRG HWL (HPF & HW & HN).
    pose proof (proj1 HPF) as HPP.
    pose proof (bp_pp_mdef H w LB LBs m c (proj1 HPF)) as HMD.
    pose proof (bp_al_res H w s _ (proj1 (proj2 (proj2 HPF)))) as HAL.
    eapply bt_start; eassumption.
  Qed.
End BT.
