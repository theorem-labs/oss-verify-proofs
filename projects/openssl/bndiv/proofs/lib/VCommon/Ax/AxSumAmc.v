(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxWordsInt AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanWEntry AsanSWord AsanSMiz AsanSRipA AsanSMat AsanSRipC AsanWMemcpy AsanWMemcpyF1 AsanWMemcpyF3 AsanWMat AsanWMcM3 AsanWAmc1 AsanWAmc3 AsanWAmc6 AxSum AxTabs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr AxSumMem AxSumRip2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition len_lo (s : store) (k : Z) : Z :=
  match lrange s (lvar (lenvar k) 1) with Some (lo, _) => Z.max lo 0 | None => 0 end.

Definition amc_op_ok (segs : list Segment) (s : store) (am : amodel) (mem : list region) (v : xv) (ts : terms) (o : w64) (n : Z) : bool :=
  let f := (wS o, ts) in
  (* [comment removed for export] *)
  (match str_k s v with
   | Some k => (n <=? len_lo s k + 1) &&& lr_in s f 0 9223372036854775808 &&& eb_sh_ok s am mem
   | None => false
   end)
  ||| (rbetween 2 s f 0 (140737488355328 - n)
       &&& ((n <=? 64) ||| rbetween 2 s f 17594333495296 (140737488355328 - n - 8) ||| rbetween 2 s f 0 (2147450880 - n - 8))
       &&& ((n =? 0)
            ||| (rprove_q 2 s (lsub f (0, sp_terms)) 56 &&& eb_sh_ok s am mem)
            ||| (rbetween 2 s f 56 (140737488355328 - n - 56) &&& sh_zero segs s mem ts (wS o - 56) (n + 112)))).

Lemma div8_sub56 (x : Z) : (x - 56) / 8 = x / 8 - 7.
Proof. replace (x - 56) with (x + (-7) * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

Lemma div8_add56 (x : Z) : (x + 56) / 8 = x / 8 + 7.
Proof. replace (x + 56) with (x + 7 * 8) by ring. rewrite Z.div_add by lia. ring. Qed.

Lemma amc_op_ok_sound (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (s : store) (am : amodel) (model : Model) (A : list region)
    (m : word -> option byte) (v : xv) (a : word) (ts : terms) (o : w64) (n : Z) :
  segs_low segs -> sat ρ s -> MR segs fs0 ρ am model -> atop_is_sp am = true -> RMem segs ρ A m -> hs_ok ρ A m ->
  eb_facts ρ -> 0 <= n -> xv_val ρ v a -> xaddr v = Some (ts, o) ->
  amc_op_ok segs s am A v ts o n = true ->
  let x := bv_unsigned a in
  x = leval ρ (wS o, ts) /\ 0 <= x /\ x + n <= 2 ^ 47 /\
  (65 <= n -> x + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= x \/ x + n + 8 <= 0x7fff8000)) /\
  (1 <= n -> forall q, 0x7fff8000 + x / 8 - 7 <= q <= 0x7fff8000 + (x + n - 1) / 8 + 7 -> 0x7fff8000 <= q < 0x10007fff8000 ->
     bat segs m (Z_to_bv 64 q) = Some (Z_to_bv 8 0)).
Proof.
  intros Hlow Hs Hmod Eat HM Hhs HF Hn Hv Ea H x. unfold amc_op_ok in H. cbv zeta in H.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2).
  assert (Hsp : sp_window_lo <= sp_val ρ <= sp_window_hi) by (unfold sp_window_lo, sp_window_hi in *; lia).
  unfold sp_window_lo, sp_window_hi in Hs1, Hs2.
  assert (Hebz : eb_sh_ok s am A = true -> sp_val ρ + 56 <= x -> forall q, 0x7fff8000 + x / 8 - 7 <= q -> q < 0x10007fff8000 ->
            bat segs m (Z_to_bv 64 q) = Some (Z_to_bv 8 0)).
  { intros Heb Hx q Hq1' Hq2. apply (eb_sh_zero segs fs0 ρ s am model A m Hlow Hs Hmod Eat HM Hhs Hsp Heb). split; [|unfold hs_hi; lia].
    assert ((sp_val ρ + 56) / 8 <= x / 8) by (apply Z.div_le_mono; lia). rewrite div8_add56 in H0. lia. }
  apply lor_true in H as [H|H].
  - (* [comment removed for export] *)
    destruct (str_k s v) as [k|] eqn:Ek; [|discriminate]. apply land_true in H as [H Heb]. apply land_true in H as [Hnk Hlr].
    apply Z.leb_le in Hnk. pose proof (lr_in_sound ρ s _ _ _ Hs Hlr) as Hlv.
    destruct (str_k_sound ρ s v a k Hs HF Hv Ek) as [Hk Hxa]. fold x in Hxa.
    assert (Hlo : len_lo s k <= ρ (lenvar k)).
    { unfold len_lo. destruct (lrange s (lvar (lenvar k) 1)) as [[lo hi]|] eqn:El.
      - pose proof (lrange_sound ρ s _ Hs _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X.
        assert (0 <= ρ (lenvar k)) by (destruct Hk as [->|[-> H2]]; [lia | destruct (Hq1 H2); lia]). lia.
      - destruct Hk as [->|[-> H2]]; [lia | destruct (Hq1 H2); lia]. }
    assert (Hlk : str_addr ρ k + ρ (lenvar k) + 1 <= sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q /\ sp_val ρ + 184 <= str_addr ρ k).
    { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
    destruct Hlk as [Hlk1 Hlk2].
    assert (Exl : x = leval ρ (wS o, ts)).
    { unfold x. rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o), Zplus_mod_idemp_r.
      replace (teval ρ ts + wS o) with (leval ρ (wS o, ts)) by (unfold leval; cbn [fst snd]; ring). apply Z.mod_small. unfold FastWord.two64. lia. }
    split; [exact Exl|]. split; [lia|]. split; [lia|]. split; [intros _; split; [lia | left; lia]|].
    intros H1 q Hq Hqr. apply (Hebz Heb); lia.
  - apply land_true in H as [H Hsh]. apply land_true in H as [Hr Hbig].
    pose proof (rbetween_sound ρ s 2 _ _ _ Hs Hr) as Hx.
    assert (Exl : x = leval ρ (wS o, ts)) by (apply (addr_form_val' ρ v a ts o (140737488355328 - n) Hv Ea Hx); unfold FastWord.two64; lia).
    rewrite <- Exl in Hx.
    split; [exact Exl|]. split; [lia|]. split; [lia|]. split.
    + intros H65. apply lor_true in Hbig as [Hbig|Hbig]; [apply lor_true in Hbig as [Hbig|Hbig]|].
      * apply Z.leb_le in Hbig. lia.
      * pose proof (rbetween_sound ρ s 2 _ _ _ Hs Hbig) as X. rewrite <- Exl in X. lia.
      * pose proof (rbetween_sound ρ s 2 _ _ _ Hs Hbig) as X. rewrite <- Exl in X. lia.
    + intros H1 q Hq Hqr. apply lor_true in Hsh as [Hsh|Hsh]; [apply lor_true in Hsh as [Hsh|Hsh]|].
      * apply Z.eqb_eq in Hsh. lia.
      * apply land_true in Hsh as [Hab Heb]. pose proof (rprove_q_sound ρ s 2 _ _ Hs Hab) as X. rewrite leval_lsub, <- Exl in X.
        assert (Esp : leval ρ (0, sp_terms) = sp_val ρ) by (unfold leval, sp_val; cbn [fst snd]; ring). rewrite Esp in X.
        apply (Hebz Heb); lia.
      * apply land_true in Hsh as [Hr56 Hz]. pose proof (rbetween_sound ρ s 2 _ _ _ Hs Hr56) as X. rewrite <- Exl in X.
        assert (Ex : x = teval ρ ts + wS o) by (rewrite Exl; unfold leval; cbn [fst snd]; ring).
        apply (sh_zero_sound segs ρ s A m ts (wS o - 56) (n + 112) Hlow Hs HM Hhs Hz); [lia | lia | lia|].
        replace (teval ρ ts + (wS o - 56)) with (x - 56) by lia. replace (x - 56 + (n + 112) - 1) with (x + n - 1 + 56) by lia.
        rewrite div8_sub56, div8_add56. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amc_mem (segs : list Segment) (s : store) (A : list region) (d sv fr : xv) (n : Z) : option (list region) :=
  match a_store segs A fr (repeat BT 2232) with
  | Some M1 =>
      if n =? 0 then Some M1 else
      match mc_load segs s A sv (Z.to_nat n) with
      | Some l => a_store4 segs s M1 d l
      | None => None
      end
  | None => None
  end.

Section AmcMem.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

Lemma amc_mem_sound (ρ : valuation) (s : store) (A M : list region) (m : word -> option byte) (d sv fr : xv) (dst src frw : bv 64) (n : Z) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ d dst -> xv_val ρ sv src -> xaddr sv <> None -> xv_val ρ fr frw ->
  amc_mem segs s A d sv fr n = Some M -> 0 <= n < 1000 -> bv_unsigned dst + n <= 2 ^ 64 ->
  hs_hi <= bv_unsigned frw -> bv_unsigned frw + 2232 <= 2 ^ 64 ->
  exists bs, rdn segs m src (Z.to_nat n) = Some bs /\ store_ok segs m frw 2232 = true /\ store_ok segs m dst (Z.to_nat n) = true /\
    forall mf m' : word -> option byte,
      (forall x : word, ~ (bv_unsigned frw <= bv_unsigned x < bv_unsigned frw + 2232) -> mf x = m x) -> mem_grows m mf ->
      copied m' mf (bv_unsigned dst) n bs ->
      RMem segs ρ M m' /\ hs_ok ρ M m' /\ Forall2 same_fields A M /\ store_ok segs mf dst (Z.to_nat n) = true.
Proof.
  intros Hs HM Hhs Hvd Hvs Hx Hvf H Hn Hd64 Hfr0 Hfr64. unfold amc_mem in H.
  destruct (a_store segs A fr (repeat BT 2232)) as [M1|] eqn:E1; [|discriminate].
  assert (Hsf1 : Forall2 same_fields A M1) by exact (a_store_fields segs A M1 _ _ E1).
  (* [comment removed for export] *)
  assert (Hokf : store_ok segs m frw 2232 = true).
  { pose proof (a_store_sound_gen segs ρ A M1 m m fr frw (repeat BT 2232) HM Hvf
                  ltac:(rewrite repeat_length; lia) ltac:(rewrite repeat_length; lia) E1 ltac:(intros; reflexivity)) as X.
    rewrite repeat_length in X. apply X. intros i Hi. right. split; [reflexivity | apply nth_repeat]. }
  (* [comment removed for export] *)
  assert (HF : forall mf : word -> option byte,
            (forall x : word, ~ (bv_unsigned frw <= bv_unsigned x < bv_unsigned frw + 2232) -> mf x = m x) -> mem_grows m mf ->
            RMem segs ρ M1 mf /\ hs_ok ρ M1 mf).
  { intros mf Hout Hg. split.
    - apply (a_store_BT_havoc segs ρ A M1 m mf fr frw 2232 HM Hvf ltac:(lia) ltac:(lia) E1); [|exact Hg].
      intros x Hx0. apply Hout. change (Z.of_nat 2232) with 2232 in Hx0. exact Hx0.
    - apply (hs_ok_out ρ A M1 m mf Hsf1); [|exact Hhs]. intros z Hz. apply Hout.
      unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in *. rewrite u_wz by lia. lia. }
  destruct (Z.eqb_spec n 0) as [->|Hnz].
  - injection H as <-. exists []. split; [reflexivity|]. split; [exact Hokf|]. split; [reflexivity|].
    intros mf m' Hout Hg Hcp. destruct (HF mf Hout Hg) as [R1 R2].
    assert (Hpw : forall x, m' x = mf x) by (intros x; apply (proj2 (Hcp x)); lia).
    split; [exact (RMem_pw segs ρ M1 mf m' Hpw R1)|]. split; [exact (hs_ok_pw ρ M1 mf m' Hpw R2)|]. split; [exact Hsf1 | reflexivity].
  - destruct (mc_load segs s A sv (Z.to_nat n)) as [l|] eqn:El; [|discriminate].
    assert (Hnn : (1 <= Z.to_nat n < 1000)%nat) by lia.
    destruct (mc_load_sound segs Hlow ρ s A m sv src (Z.to_nat n) l Hs HM Hhs Hvs Hx Hnn El) as [bs [Hrd HF2]].
    pose proof (rdn_length segs m (Z.to_nat n) src bs Hrd) as Hlb. pose proof (Forall2_length HF2) as Hll.
    assert (Hl1 : (1 <= length l < 1000)%nat) by lia.
    exists bs. split; [exact Hrd|]. split; [exact Hokf|].
    destruct (HF m ltac:(intros; reflexivity) (mem_grows_refl m)) as [R1 R2].
    destruct (a_store4_sound segs ρ s M1 M m d dst l bs Hlow Hs R1 R2 Hvd Hl1 HF2 H) as (Hok & _ & _).
    split; [rewrite <- Hlb, <- Hll; exact Hok|].
    intros mf m' Hout Hg Hcp. destruct (HF mf Hout Hg) as [R1' R2'].
    destruct (a_store4_sound segs ρ s M1 M mf d dst l bs Hlow Hs R1' R2' Hvd Hl1 HF2 H) as (Hok' & HM' & Hhs').
    assert (Hpw : forall x, m' x = write_to_mem mf dst bs x).
    { apply copied_write; [lia|]. replace (Z.of_nat (length bs)) with n by lia. exact Hcp. }
    split; [exact (RMem_pw segs ρ M _ m' Hpw HM')|]. split; [exact (hs_ok_pw ρ M _ m' Hpw Hhs')|].
    split; [|rewrite <- Hlb, <- Hll; exact Hok'].
    pose proof (a_store4_fields segs s M1 M d l H) as Hsf2.
    clear - Hsf1 Hsf2. revert M Hsf2. induction Hsf1 as [|R R1 A' M1' HR _ IH]; intros M Hsf2; inversion Hsf2; subst; constructor.
    + destruct HR as (a1 & a2 & a3 & a4 & a5). destruct H1 as (b1 & b2 & b3 & b4 & b5). unfold same_fields. repeat split; congruence.
    + apply IH. assumption.
Qed.

End AmcMem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition amc_code_ok (segs : list Segment) (b rb gI gK gR : Z) : bool :=
  words_ok_f segs b AMC_WORDS &&& pair_ok_f segs b 0x34 13 13 gI &&& pair_ok_f segs b 0x74 13 13 gK
  &&& pair_ok_f segs b 0xbc 13 13 gK &&& pair_ok_f segs b 0xf4 13 13 gR
  &&& jal_ok_f segs b 0x3ac 1 rb &&& jal_ok_f segs b 0x4a8 1 rb.

Lemma amc_code_sound (segs : list Segment) (b rb gI gK gR : Z) : amc_code_ok segs b rb gI gK gR = true ->
  AmcCode segs b gI gK gR /\ jal_ok segs b 0x3ac 1 rb = true /\ jal_ok segs b 0x4a8 1 rb = true.
Proof.
  unfold amc_code_ok. rewrite !pair_ok_f_eq, !jal_ok_f_eq. intros H. apply land_true in H as [H J2]. apply land_true in H as [H J1].
  apply land_true in H as [H H5]. apply land_true in H as [H H4]. apply land_true in H as [H H3].
  apply land_true in H as [H1 H2]. apply words_ok_f_eq in H1. split; [constructor; assumption | split; assumption].
Qed.

Lemma rip_code_sound (segs : list Segment) (b mz gK gMB gME gHE : Z) : rip_code_ok segs b mz gK gMB gME gHE = true -> RipCode segs b mz gK gMB gME gHE.
Proof.
  unfold rip_code_ok. intros Hcode.
  apply land_true in Hcode as [Hcode HJz]. apply land_true in Hcode as [Hcode HPb8]. apply land_true in Hcode as [Hcode HP9c]. apply land_true in Hcode as [Hcode HP94].
  apply land_true in Hcode as [Hcode HP70]. apply land_true in Hcode as [Hcode HP54]. apply land_true in Hcode as [Hcode HP4c].
  apply land_true in Hcode as [Hcode HP2c]. apply land_true in Hcode as [Hcode HPh44]. apply land_true in Hcode as [Hcode HPh28].
  apply land_true in Hcode as [Hcode HPh20]. apply land_true in Hcode as [Hcode HPh0]. apply land_true in Hcode as [Hcode HWz].
  apply land_true in Hcode as [HW HWh]. constructor; assumption.
Qed.

(* [comment removed for export] *)
Definition byte_nz (segs : list Segment) (mem : list region) (a : Z) : bool :=
  match a_load segs mem (XL (wofZ a)) 1 with
  | Some [BL c] => negb (c =? 0)%uint63
  | _ => false
  end.

Lemma byte_nz_sound (segs : list Segment) (ρ : valuation) (A : list region) (m : word -> option byte) (a : Z) :
  RMem segs ρ A m -> 0 <= a < 2 ^ 64 -> byte_nz segs A a = true ->
  exists vI : byte, bat segs m (Z_to_bv 64 a) = Some vI /\ bv_unsigned vI <> 0.
Proof.
  intros HM Ha H. unfold byte_nz in H. destruct (a_load segs A (XL (wofZ a)) 1) as [[|[c| |] [|]]|] eqn:El; try discriminate.
  assert (Hv : xv_val ρ (XL (wofZ a)) (Z_to_bv 64 a)) by (cbn [xv_val]; rewrite wZ_wofZ, Z_to_bv_unsigned; reflexivity).
  destruct (a_load_sound segs ρ A m _ _ 1 _ HM Hv ltac:(lia) El) as [bs [Hrd HF]].
  inversion HF as [|x y l0 r0 X0 HF0]; subst. inversion HF0; subst. exists y. split.
  - cbn [rdn] in Hrd. unfold bat. destruct (match m (Z_to_bv 64 a) with Some b0 => Some b0 | None => seg_rom segs (Z_to_bv 64 a) end); [|discriminate].
    injection Hrd as ->. reflexivity.
  - unfold xb_bv in X0. cbn [xb_z] in X0. rewrite X0. apply negb_true_iff in H. intros E. apply Uint63.eqb_false_spec in H. apply H.
    apply to_Z_inj. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Definition frame_off (s : store) (f : lin) (o n : Z) : bool :=
  let a := lsub (o - 2232, sp_terms) f in let b := lsub f (o, sp_terms) in
  lr_ge s a n ||| lr_ge s b 0 ||| rprove_q 2 s a n ||| rprove_q 2 s b 0.

Lemma frame_off_sound (ρ : valuation) (s : store) (f : lin) (o n : Z) : sat ρ s -> frame_off s f o n = true ->
  leval ρ f + n <= sp_val ρ + o - 2232 \/ sp_val ρ + o <= leval ρ f.
Proof.
  intros Hs H. unfold frame_off in H. cbv zeta in H.
  assert (E : forall c, leval ρ (c, sp_terms) = sp_val ρ + c) by (intros c; unfold leval, sp_val; cbn [fst snd]; ring).
  apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]|]|].
  - pose proof (lr_ge_sound ρ s _ _ Hs H) as X. rewrite leval_lsub, E in X. left. lia.
  - pose proof (lr_ge_sound ρ s _ _ Hs H) as X. rewrite leval_lsub, E in X. right. lia.
  - pose proof (rprove_q_sound ρ s 2 _ _ Hs H) as X. rewrite leval_lsub, E in X. left. lia.
  - pose proof (rprove_q_sound ρ s 2 _ _ Hs H) as X. rewrite leval_lsub, E in X. right. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sum_amc_g (ckA : (list Segment -> Z -> Z -> Z -> Z -> Z -> bool)) (ckR : (list Segment -> Z -> Z -> Z -> Z -> Z -> Z -> bool)) (ckM : (list Segment -> Z -> bool)) (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  let s := a_facts A in
  let mem := a_mem A in
  let d := aget (a_regs A) 10%uint63 in
  let sv := aget (a_regs A) 11%uint63 in
  match amc_params T b with
  | None => None
  | Some (rb, gI, aI, gR, e) =>
  match rip_params T rb, xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, aget (a_regs A) 2%uint63,
        xaddr d, xaddr sv, find_entry mem with
  | Some (mz, gK, gMB, gME, gHE, aK, aMB, aME, aHE), Some n, XL r, XS ts o, Some (td, od), Some (tsr, osr), Some ph =>
      if (0 <=? n) &&& (n <? 1000) &&& teqb ts sp_terms &&& (- 8388608 + 2232 <=? wS o) &&& (wS o <=? 0)
         &&& pc_ok r &&& atop_is_sp (a_model A) &&& (a_budget A + 4096 * amc_pages n <=? LIM)
         &&& ckA segs b rb gI gK gR &&& ckR segs rb mz gK gMB gME gHE &&& ckM segs e
         &&& globals_ok segs mem gK gMB gME gHE aK aMB aME aHE
         &&& cell_lit segs mem gI aI &&& cell_lit segs mem gR e &&& byte_nz segs mem aI
         &&& in_seg segs gI &&& in_seg segs gR &&& in_segn segs aI 1
         &&& amc_op_ok segs s (a_model A) mem d td od n &&& amc_op_ok segs s (a_model A) mem sv tsr osr n
         &&& disj_ok s (wS od, td) (wS osr, tsr) n
         &&& frame_off s (wS od, td) (wS o) n &&& frame_off s (wS osr, tsr) (wS o) n then
        match amc_mem segs s mem d sv (XS sp_terms (wofZ (wS o - 2232))) n with
        | Some mem' =>
            Some [AS r (clob MCF_CLOB' (a_regs A)) (resv_drop (a_resv A)) mem' s (a_model A) (a_budget A + 4096 * amc_pages n) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _, _, _, _ => None
  end
  end.

Definition sum_amc (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_amc_g amc_code_ok rip_code_okf mc_code_ok T segs LIM A.

(* [comment removed for export] *)
Definition amc_ck (T : img_tabs) (segs : list Segment) (b : Z) : bool :=
  match amc_params T b with
  | None => false
  | Some (rb, gI, aI, gR, e) =>
  match rip_params T rb with
  | Some (mz, gK, gMB, gME, gHE, _, _, _, _) =>
      amc_code_ok segs b rb gI gK gR &&& rip_code_okf segs rb mz gK gMB gME gHE &&& mc_code_ok segs e
  | None => false
  end
  end.

Definition ck_true5 (_ : list Segment) (_ _ _ _ _ : Z) : bool := true.

Lemma sum_amc_g_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  amc_ck T segs (wZ (a_pc A)) = true -> sum_amc_g ck_true5 ck_true6 ck_true1 T segs LIM A = Some l -> sum_amc T segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_amc, sum_amc_g in *. cbv zeta in *. unfold amc_ck in Hck. unfold ck_true5, ck_true6, ck_true1 in H.
  destruct (amc_params T (wZ (a_pc A))) as [[[[[rb gI] aI] gR] e]|]; [|exact H].
  destruct (rip_params T rb) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|]; [|exact H].
  apply land_true in Hck as [Hck H3]. apply land_true in Hck as [H1 H2]. rewrite H1, H2, H3. exact H.
Qed.

Section AmcSound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_amc_sound (A : AST) (l : list AST) : sum_amc T segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_amc, sum_amc_g in Hs. cbv zeta in Hs.
  destruct (amc_params T (wZ (a_pc A))) as [[[[[rb gI] aI] gR] e]|] eqn:Ep; [|discriminate].
  destruct (rip_params T rb) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|] eqn:Epr; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (aget (a_regs A) 2%uint63) as [| ts o | | | |] eqn:E2; try discriminate.
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[td od]|] eqn:Ed; [|discriminate].
  destruct (xaddr (aget (a_regs A) 11%uint63)) as [[tsr osr]|] eqn:Esr; [|discriminate].
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (0 <=? n) eqn:En0; [|discriminate]. apply Z.leb_le in En0.
  destruct (n <? 1000) eqn:En1; [|discriminate]. apply Z.ltb_lt in En1.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 + 2232 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (a_budget A + 4096 * amc_pages n <=? LIM) eqn:Hbud; [|discriminate]. apply Z.leb_le in Hbud.
  destruct (amc_code_ok segs (wZ (a_pc A)) rb gI gK gR) eqn:Hca; [|discriminate].
  destruct (rip_code_okf segs rb mz gK gMB gME gHE) eqn:Hcr; [|discriminate]. apply rip_code_okf_ok in Hcr.
  destruct (mc_code_ok segs e) eqn:Hcm; [|discriminate].
  destruct (globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE) eqn:Hglob; [|discriminate].
  destruct (cell_lit segs (a_mem A) gI aI) eqn:HcI; [|discriminate].
  destruct (cell_lit segs (a_mem A) gR e) eqn:HcR; [|discriminate].
  destruct (byte_nz segs (a_mem A) aI) eqn:Hnz; [|discriminate].
  destruct (in_seg segs gI) eqn:HsI; [|discriminate].
  destruct (in_seg segs gR) eqn:HsR; [|discriminate].
  destruct (in_segn segs aI 1) eqn:HsaI; [|discriminate].
  destruct (amc_op_ok segs (a_facts A) (a_model A) (a_mem A) (aget (a_regs A) 10%uint63) td od n) eqn:Hopd; [|discriminate].
  destruct (amc_op_ok segs (a_facts A) (a_model A) (a_mem A) (aget (a_regs A) 11%uint63) tsr osr n) eqn:Hops; [|discriminate].
  destruct (disj_ok (a_facts A) (wS od, td) (wS osr, tsr) n) eqn:Hdj; [|discriminate].
  destruct (frame_off (a_facts A) (wS od, td) (wS o) n) eqn:Hfd; [|discriminate].
  destruct (frame_off (a_facts A) (wS osr, tsr) (wS o) n) eqn:Hfs; [|discriminate].
  destruct (amc_mem segs (a_facts A) (a_mem A) (aget (a_regs A) 10%uint63) (aget (a_regs A) 11%uint63) (XS sp_terms (wofZ (wS o - 2232))) n)
    as [mem'|] eqn:Emem; [|discriminate].
  injection Hs as <-.
  unfold globals_ok in Hglob.
  apply andb_prop in Hglob as [Hglob Hins]. apply andb_prop in Hglob as [Hglob C8]. apply andb_prop in Hglob as [Hglob C7].
  apply andb_prop in Hglob as [Hglob C6]. apply andb_prop in Hglob as [Hglob C5]. apply andb_prop in Hglob as [Hglob C4].
  apply andb_prop in Hglob as [Hglob C3]. apply andb_prop in Hglob as [C1 C2].
  rewrite forallb_forall in Hins.
  destruct (amc_params_ok T HT _ _ _ _ _ _ Ep) as (Hb & He & HgI & HaI & HgR).
  pose proof (rip_params_40 T HT _ _ _ _ _ _ _ _ _ _ Epr) as Hg40.
  pose proof (proj2 (rip_params_ok T HT _ _ _ _ _ _ _ _ _ _ Epr)) as Hrb.
  destruct (amc_code_sound segs _ rb gI gK gR Hca) as (HcA & HJ1 & HJ2).
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hbd Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb]. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & _ & Hs2).
  assert (Hspw : sp_window_lo <= sp_val ρ <= sp_window_hi) by (unfold sp_window_lo, sp_window_hi in *; lia).
  unfold sp_window_lo, sp_window_hi in Hs1, Hs2.
  pose proof (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat) as Hatop.
  (* [comment removed for export] *)
  set (dst := rg ms 10%bv). set (src := rg ms 11%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 10%uint63) dst) by exact (Hregs 10%bv).
  assert (Hvs : xv_val ρ (aget (a_regs A) 11%uint63) src) by exact (Hregs 11%bv).
  pose proof (reg_lit ρ _ ms 12%bv 12%uint63 n Hregs eq_refl E12) as Hcnt.
  destruct (amc_op_ok_sound segs fs0 ρ _ _ model _ (ms_mem ms) _ dst td od n Hlow Hsat Hmod Eat Hmem Hhs HF En0 Hvd Ed Hopd) as (Hdv & Hd0 & Hd1 & Hd65 & Hdsh).
  destruct (amc_op_ok_sound segs fs0 ρ _ _ model _ (ms_mem ms) _ src tsr osr n Hlow Hsat Hmod Eat Hmem Hhs HF En0 Hvs Esr Hops) as (Hsv & Hs0 & Hs1' & Hs65 & Hssh).
  pose proof (disj_ok_sound ρ _ _ _ n Hsat Hdj) as Hdisj. rewrite <- Hdv, <- Hsv in Hdisj.
  pose proof (frame_off_sound ρ _ _ _ n Hsat Hfd) as Hfrd. rewrite <- Hdv in Hfrd.
  pose proof (frame_off_sound ρ _ _ _ n Hsat Hfs) as Hfrs. rewrite <- Hsv in Hfrs.
  assert (Hxs : xaddr (aget (a_regs A) 11%uint63) <> None) by (rewrite Esr; discriminate).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec r Epc) as [Hr4 Hr26].
  assert (HSP : bv_unsigned (rg ms 2%bv) = sp_val ρ + wS o).
  { change 2%uint63 with (ri 2%bv) in E2. rewrite (reg_form ρ _ ms 2%bv _ _ Hregs E2). unfold smod.
    change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r. apply Z.mod_small. unfold FastWord.two64. lia. }
  set (SP := sp_val ρ + wS o) in *.
  set (frw := Z_to_bv 64 (SP - 2232)).
  assert (Hfu : bv_unsigned frw = SP - 2232) by (apply u_wz; unfold SP; lia).
  assert (Hvf : xv_val ρ (XS sp_terms (wofZ (wS o - 2232))) frw).
  { cbn [xv_val]. rewrite Hfu. unfold smod. change (teval ρ sp_terms) with (sp_val ρ). rewrite wZ_wofZ, Zplus_mod_idemp_r.
    symmetry. replace (sp_val ρ + (wS o - 2232)) with (SP - 2232) by (unfold SP; ring). apply Z.mod_small. unfold FastWord.two64, SP. lia. }
  destruct (amc_mem_sound segs Hlow ρ _ _ mem' (ms_mem ms) _ _ _ dst src frw n Hsat Hmem Hhs Hvd Hvs Hxs Hvf Emem ltac:(lia) ltac:(lia)
              ltac:(rewrite Hfu; unfold hs_hi, SP; lia) ltac:(rewrite Hfu; unfold SP; lia))
    as (bs & Hrd & Hokf & Hokd & Hpost).
  (* [comment removed for export] *)
  assert (Hgl : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> 0 <= a /\ a + 8 <= ls_beg).
  { intros a Hin. pose proof (Hins a Hin) as X. unfold in_seg in X. apply existsb_exists in X as [sg [HIns Hcs]].
    apply andb_prop in Hcs as [Cs1 Cs2]. apply Z.leb_le in Cs1. apply Z.leb_le in Cs2. pose proof (Hlow sg HIns). lia. }
  assert (Hcl : forall a v, 0 <= a < 2 ^ 40 -> cell_lit segs (a_mem A) a v = true -> cell8 segs (ms_mem ms) a v).
  { intros a v Ha Hc. apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) a v Hmem); [lia | exact Hc]. }
  assert (Hnl8 : forall a, in_seg segs a = true -> no_lazy model a (a + 8))
    by (intros a Hin; exact (no_lazy_img segs Hlow model a 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) Hin)).
  destruct (byte_nz_sound segs ρ (a_mem A) (ms_mem ms) aI Hmem ltac:(lia) Hnz) as [vI [HvI HvI0]].
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  assert (Esrc : src = Z_to_bv 64 (bv_unsigned src)) by (apply word_lit_w; reflexivity).
  apply (amc_sum segs cfg b gI aI gK aK gMB aMB gME aME gHE aHE gR e rb mz HcA
           (rip_code_sound segs rb mz gK gMB gME gHE Hcr) HJ1 HJ2 Hrb (mc_code_sound segs e Hcm) Hb He
           ltac:(destruct Hg40 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8); repeat split; lia)
           ms model (KT ρ o') SP (bv_unsigned dst) (bv_unsigned src) n bs vI Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - apply word_lit_w. exact HSP.
  - exact Edst.
  - exact Esrc.
  - apply word_lit_w. exact Hcnt.
  - unfold SP. lia.
  - exact Hokf.
  - apply (no_lazy_above segs fs0 ρ (a_model A) model _ _ Hmod). rewrite Hatop. unfold SP. lia.
  - lia.
  - exact Hd0.
  - exact Hs0.
  - exact Hd1.
  - exact Hs1'.
  - intros H65. split; [exact (Hs65 H65) | exact (Hd65 H65)].
  - lia.
  - exact Hfrd.
  - exact Hfrs.
  - rewrite <- Esrc. exact Hrd.
  - rewrite <- Edst. exact Hokd.
  - exact (Hcl gI aI HgI HcI).
  - exact HvI.
  - exact HvI0.
  - exact (Hcl gR e HgR HcR).
  - destruct Hg40 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold globals. repeat split; apply Hcl; assumption.
  - unfold globals_nl. repeat split; apply Hnl8; apply Hins; cbn; tauto.
  - exact (Hnl8 gI HsI).
  - exact (no_lazy_imgn segs Hlow model aI 1 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) HsaI).
  - exact (Hnl8 gR HsR).
  - exact Hssh.
  - exact Hdsh.
  - destruct Hbd as [Hb1 Hb2]. rewrite Hb2. lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - (* [comment removed for export] *)
    intros ms' model' HMC [mf [Hmf1 [Hmf2 Hcp]]] Hpc' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMC as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused].
    destruct (Hpost mf (ms_mem ms') ltac:(intros x Hx; apply Hmf1; rewrite Hfu in Hx; lia) Hmf2 Hcp) as (Hmem' & Hhs' & Hsf & Hokd').
    assert (Hfrm : forall x : word, ~ (SP - 2232 <= bv_unsigned x < SP) -> mf x = ms_mem ms x) by exact Hmf1.
    (* [comment removed for export] *)
    assert (Hcov1 : mem_cov segs model mf).
    { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (SP - 2232)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) SP) as [L2|L2]].
      - rewrite Hfrm in Hx by lia. exact (Hcov x Hx).
      - right. left. rewrite Hatop. unfold SP in *. lia.
      - rewrite Hfrm in Hx by lia. exact (Hcov x Hx). }
    assert (Hna1 : na_ok segs ρ (a_mem A) model mf).
    { destruct Hnaok as [N1 [N2 N3]]. split; [|split; [exact N2 | exact N3]]. intros x Hx Hna.
      destruct (Z_lt_le_dec (bv_unsigned x) (SP - 2232)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) SP) as [L2|L2]].
      - rewrite Hfrm in Hx by lia. exact (N1 x Hx Hna).
      - destruct (mr_na_maps segs fs0 ρ _ _ Hmod _ Hna) as [p [Hp Hpz]].
        pose proof (mr_top segs fs0 ρ _ _ Hmod p Hp) as Htp. rewrite Hatop in Htp. unfold SP in *. lia.
      - rewrite Hfrm in Hx by lia. exact (N1 x Hx Hna). }
    assert (Hcpo : forall x : word, ~ (bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + Z.of_nat (Z.to_nat n)) -> ms_mem ms' x = mf x).
    { intros x Hx. apply (proj2 (Hcp x)). lia. }
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model' HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. apply word_lit_w. exact Hra.
    + exact Epc.
    + exact P1.
    + apply (RRegs_clob ρ (a_regs A) ms ms' MCF_CLOB' Hregs); [rewrite <- MCF_CLOB_eq; exact P6 | exact MCF_CLOB'_nz].
    + destruct (a_resv A); cbn [resv_drop RResv] in *; try exact I. destruct P5 as [X|X]; rewrite X; [exact Hres | reflexivity].
    + exact P2.
    + exact Hmem'.
    + exact Hhs'.
    + apply (mem_cov_range segs model mf (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hcov1 ltac:(lia) ltac:(unfold AxAcct.two64; lia)); [|exact Hcpo].
      unfold wz. rewrite <- Edst. exact Hokd'.
    + exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      apply (na_ok_range segs ρ (a_mem A) model mf (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hna1 ltac:(lia) ltac:(unfold AxAcct.two64; lia)); [|exact Hcpo].
      unfold wz. rewrite <- Edst. exact Hokd'.
    + reflexivity.
    + exact Hsat.
    + right. exists pages. split; [exact Em'|]. destruct Hbd as [Hb1 Hb2]. lia.
Qed.

End AmcSound.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
