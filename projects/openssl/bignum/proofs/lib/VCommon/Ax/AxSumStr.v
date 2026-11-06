(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxWordsInt AxAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanSStrlen AsanWEntry AsanWEb AsanWEbLoad AxSum AsanSWord AsanSMiz AsanSRipA AsanSMat AsanSRipC AxTabs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel AxSumLibc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition str_k (s : store) (v : xv) : option Z :=
  match v with
  | XS ts o =>
      if same_addr s ts o (sp_terms ++ t_ae) (wofZ 184) then Some 0
      else if same_addr s ts o (sp_terms ++ t_ae0) (wofZ 185) &&& argc_ge2 s then Some 1
      else None
  | _ => None
  end.

Definition str_addr (ρ : valuation) (k : Z) : Z :=
  sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + (if k =? 0 then 0 else ρ (lenvar 0) + 1).

Lemma argc_ge2_sound (ρ : valuation) (s : store) : sat ρ s -> argc_ge2 s = true -> 2 <= ρ v_argc.
Proof.
  intros Hs H. unfold argc_ge2 in H. destruct (lrange s (lvar v_argc 1)) as [[lo hi]|] eqn:E; [|discriminate].
  apply Z.leb_le in H. pose proof (lrange_sound ρ s _ Hs _ E) as X. cbn [fst snd] in X.
  unfold leval, lvar in X. cbn [fst snd teval] in X. lia.
Qed.

Lemma total_first2' (L : list (list byte)) : (2 <= length L)%nat ->
  Z.of_nat (length (nth 0 L [])) + 1 + Z.of_nat (length (nth 1 L [])) + 1 <= total_arg_bytes L.
Proof.
  intros H. destruct L as [|a [|c L]]; cbn [length] in H; try lia. unfold total_arg_bytes; cbn [fold_right nth].
  pose proof (total_arg_bytes_nonneg L) as X. unfold total_arg_bytes in X. lia.
Qed.

Lemma eb_layout (ρ : valuation) : eb_facts ρ ->
  sp_window_lo <= sp_val ρ /\ 1 <= ρ v_argc <= 1024 /\ 0 <= ρ v_envc <= 256 /\ 0 <= ρ (lenvar 0) <= 131071 /\
  ρ (lenvar 0) + 1 <= 8 * ρ v_q /\
  (2 <= ρ v_argc -> 0 <= ρ (lenvar 1) <= 131071 /\ ρ (lenvar 0) + 1 + ρ (lenvar 1) + 1 <= 8 * ρ v_q) /\
  sp_val ρ + 200 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q <= sp_window_hi.
Proof.
  intros HF. pose proof (eb_span (mkPhdrInfo 0 0 0) ρ HF) as (Hs1 & Hs2 & _).
  pose proof HF as (Hargc & Henvc & Hstr & _ & Hta & Hte & Hq & _).
  destruct (Hstr 0 ltac:(lia)) as [Hl0 _].
  pose proof (len_k ρ HF 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0.
  pose proof (len_av ρ HF) as Lav. pose proof (total_arg_bytes_nonneg (dec_envp ρ)) as Hte0.
  pose proof (Z.div_mod (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)) as Hm.
  assert (H1 : ρ (lenvar 0) + 1 <= ρ v_ta).
  { rewrite Hta, <- L0. destruct (dec_argv ρ) as [|a0 r] eqn:Ed; [cbn in Lav; lia|].
    cbn [nth]. unfold total_arg_bytes. cbn [fold_right]. pose proof (total_arg_bytes_nonneg r) as X. unfold total_arg_bytes in X. lia. }
  split; [exact Hs1|]. split; [exact Hargc|]. split; [exact Henvc|]. split; [exact Hl0|]. split; [lia|]. split; [|lia].
  intros H2. destruct (Hstr 1 ltac:(lia)) as [Hl1 _]. split; [exact Hl1|].
  pose proof (len_k ρ HF 1 ltac:(lia)) as L1. change (Z.to_nat 1) with 1%nat in L1.
  pose proof (total_first2' (dec_argv ρ) ltac:(lia)) as X. rewrite L0, L1, <- Hta in X. lia.
Qed.

Lemma eb_cstr (segs : list Segment) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (nR : Z) (off : Z) (bs : list byte) :
  eb_rel ph ρ m (sp_val ρ) nR -> 0 <= off -> off + Z.of_nat (length bs) + 1 <= Z.of_nat (length (eb_image ph ρ)) ->
  (forall j, 0 <= j <= Z.of_nat (length bs) ->
     nth (Z.to_nat (off + j)) (eb_image ph ρ) (Z_to_bv 8 0) = nth (Z.to_nat j) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) ->
  nul_free bs -> cstr segs m (Z_to_bv 64 (sp_val ρ + off)) bs.
Proof.
  intros Heb Hoff Hlen Hnth Hnf. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_span ph ρ HF) as (Hs1 & Hs2 & HL). unfold sp_window_lo, sp_window_hi in *.
  split; [|exact Hnf].
  replace (S (length bs)) with (length (bs ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn [length]; lia).
  apply rdn_of_nth; [lia | rewrite length_app; cbn [length]; lia |].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  pose proof (eb_rel_byte ph ρ m _ _ Heb (off + Z.of_nat j) ltac:(lia)) as Hbyte.
  replace (sp_val ρ + (off + Z.of_nat j)) with (sp_val ρ + off + Z.of_nat j) in Hbyte by lia.
  rewrite Hbyte, (Hnth (Z.of_nat j) ltac:(lia)), Nat2Z.id. reflexivity.
Qed.

Lemma eb_argvk (segs : list Segment) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (nR : Z) (k : Z) :
  eb_rel ph ρ m (sp_val ρ) nR -> (k = 0 \/ (k = 1 /\ 2 <= ρ v_argc)) ->
  let bs := nth (Z.to_nat k) (dec_argv ρ) [] in
  cstr segs m (Z_to_bv 64 (str_addr ρ k)) bs /\ Z.of_nat (length bs) = ρ (lenvar k).
Proof.
  intros Heb Hk bs. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). pose proof (eb_span ph ρ HF) as (_ & _ & HL).
  pose proof HF as (_ & _ & Hstr & _).
  assert (Hkr : 0 <= k < ρ v_argc) by (destruct Hk as [->|[-> H2]]; lia).
  assert (Hlen : Z.of_nat (length bs) = ρ (lenvar k)) by exact (len_k ρ HF k Hkr).
  destruct (Hstr k Hkr) as [Hlk Hbk].
  split; [|exact Hlen].
  assert (Hnf : nul_free bs).
  { intros x Hx. apply (In_nth _ _ (Z_to_bv 8 0)) in Hx as [j [Hj <-]].
    pose proof (nth_k ρ HF k (Z.of_nat j) Hkr ltac:(lia)) as Hn. rewrite Nat2Z.id in Hn. fold bs in Hn. rewrite Hn.
    destruct (Hbk (Z.of_nat j) ltac:(lia)) as [B1 B2]. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; lia). lia. }
  assert (Hnthk : forall j, 0 <= j <= Z.of_nat (length bs) ->
            (if j <? ρ (lenvar k) then Z_to_bv 8 (ρ (strvar k j)) else Z_to_bv 8 0) = nth (Z.to_nat j) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
  { intros j Hj. destruct (Z.ltb_spec j (ρ (lenvar k))) as [L|L].
    - rewrite app_nth1 by lia. symmetry. exact (nth_k ρ HF k j Hkr ltac:(lia)).
    - rewrite app_nth2 by lia. replace (Z.to_nat j - length bs)%nat with 0%nat by lia. reflexivity. }
  unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb].
  - replace (sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 0) with (sp_val ρ + (184 + 8 * ρ v_argc + 8 * ρ v_envc)) by lia.
    apply (eb_cstr segs ph ρ m nR _ bs Heb); [lia | lia | | exact Hnf].
    intros j Hj. rewrite (R5_str0 ph ρ HF j ltac:(lia)). exact (Hnthk j Hj).
  - destruct (Hq1 H2) as [Hl1 Hq1'].
    replace (sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + (ρ (lenvar 0) + 1)) with (sp_val ρ + (184 + 8 * ρ v_argc + 8 * ρ v_envc + ρ (lenvar 0) + 1)) by lia.
    apply (eb_cstr segs ph ρ m nR _ bs Heb); [lia | lia | | exact Hnf].
    intros j Hj. rewrite (R5_str1 ph ρ HF H2 j ltac:(lia)). exact (Hnthk j Hj).
Qed.

Lemma str_k_sound (ρ : valuation) (s : store) (v : xv) (a : word) (k : Z) :
  sat ρ s -> eb_facts ρ -> xv_val ρ v a -> str_k s v = Some k ->
  (k = 0 \/ (k = 1 /\ 2 <= ρ v_argc)) /\ bv_unsigned a = str_addr ρ k.
Proof.
  intros Hs HF Hv H. unfold str_k in H. destruct v as [| ts o | | | |]; try discriminate. cbn [xv_val] in Hv.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  destruct (same_addr s ts o (sp_terms ++ t_ae) (wofZ 184)) eqn:E0.
  - injection H as <-. split; [left; reflexivity|].
    rewrite Hv, (same_addr_sound ρ s _ _ _ _ Hs E0). unfold smod, str_addr. rewrite teval_app. fold (sp_val ρ). unfold t_ae. cbn [teval Z.eqb].
    rewrite wZ_wofZ. rewrite (Z.mod_small 184) by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia.
  - destruct (same_addr s ts o (sp_terms ++ t_ae0) (wofZ 185)) eqn:E1; [|discriminate].
    destruct (argc_ge2 s) eqn:E2; [|discriminate]. injection H as <-.
    pose proof (argc_ge2_sound ρ s Hs E2) as H2.
    split; [right; split; [reflexivity | exact H2]|]. destruct (Hq1 H2) as [Hl1 Hq1'].
    rewrite Hv, (same_addr_sound ρ s _ _ _ _ Hs E1). unfold smod, str_addr. rewrite teval_app. fold (sp_val ρ). unfold t_ae0. cbn [teval].
    rewrite wZ_wofZ. rewrite (Z.mod_small 185) by (unfold two64; lia).
    change (1 =? 0) with false. cbv iota. rewrite Z.mod_small by (unfold two64; lia). lia.
Qed.

Definition str_load (s : store) (v : xv) (n : nat) : option (list xb) :=
  match str_k s v with
  | Some k =>
      match lrange s (lvar (lenvar k) 1) with
      | Some (lo, _) => if Z.of_nat n <=? lo then Some (map (fun j => BF [(strvar k (Z.of_nat j), 1)] w_zero 0) (seq 0 n)) else None
      | None => None
      end
  | None => None
  end.

Lemma str_load_sound (segs : list Segment) (ph : PhdrInfo) (ρ : valuation) (s : store) (m : word -> option byte) (nR : Z)
    (v : xv) (a : word) (n : nat) (l : list xb) :
  sat ρ s -> eb_rel ph ρ m (sp_val ρ) nR -> xv_val ρ v a -> str_load s v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs Heb Hv H. unfold str_load in H. destruct (str_k s v) as [k|] eqn:Ek; [|discriminate].
  destruct (lrange s (lvar (lenvar k) 1)) as [[lo hi]|] eqn:El; [|discriminate].
  destruct (Z.of_nat n <=? lo) eqn:En; [|discriminate]. injection H as <-. apply Z.leb_le in En.
  pose proof (lrange_sound ρ s _ Hs _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X.
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  destruct (str_k_sound ρ s v a k Hs HF Hv Ek) as [Hk Ha].
  destruct (eb_argvk segs ph ρ m nR k Heb Hk) as [[Hrd _] Hlen]. set (bs := nth (Z.to_nat k) (dec_argv ρ) []) in *.
  assert (Ea : a = Z_to_bv 64 (str_addr ρ k)) by (apply word_lit_w; exact Ha).
  assert (Hkr : 0 <= k < ρ v_argc).
  { pose proof (eb_layout ρ HF) as (_ & Hargc & _). destruct Hk as [->|[-> H2]]; lia. }
  exists (firstn n bs). split.
  - rewrite Ea. pose proof (rdn_firstn' segs m _ _ _ n Hrd ltac:(lia)) as Y. rewrite firstn_app in Y.
    replace (n - length bs)%nat with 0%nat in Y by lia. rewrite firstn_O, app_nil_r in Y. exact Y.
  - assert (G : forall i, (i <= n)%nat -> Forall2 (xb_bv ρ) (map (fun j => BF [(strvar k (Z.of_nat j), 1)] w_zero 0) (seq (n - i) i)) (firstn i (skipn (n - i) bs))).
    { induction i as [|i IH]; intros Hi; [constructor|].
      replace (n - S i)%nat with (n - S i)%nat by reflexivity. cbn [seq map].
      assert (Hlt : (n - S i < length bs)%nat) by lia.
      rewrite (skipn_nth_cons (n - S i) bs (Z_to_bv 8 0) Hlt). cbn [firstn]. constructor.
      - unfold xb_bv. cbn [xb_z]. unfold smod, ExBytes.zbyte. cbn [teval]. change (wZ w_zero) with 0. change (2 ^ (8 * Z.of_nat 0)) with 1.
        rewrite Z.div_1_r. pose proof (nth_k ρ HF k (Z.of_nat (n - S i)) Hkr ltac:(lia)) as Hn. rewrite Nat2Z.id in Hn. fold bs in Hn. rewrite Hn.
        rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        replace (1 * ρ (strvar k (Z.of_nat (n - S i))) + 0 + 0) with (ρ (strvar k (Z.of_nat (n - S i)))) by ring.
        unfold two64. change 18446744073709551616 with (256 * 72057594037927936).
        rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_mod. lia.
      - replace (S (n - S i)) with (n - i)%nat by lia. apply IH. lia. }
    specialize (G n (le_n n)). rewrite Nat.sub_diag in G. exact G.
Qed.

Definition t_len (k : Z) : terms := [(lenvar k, 1)].

Definition sum_strlen (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  match str_k (a_facts A) (aget (a_regs A) 10%uint63), aget (a_regs A) 1%uint63, find_entry (a_mem A) with
  | Some k, XL r, Some ph =>
      if words_ok_f segs b STRLEN_WORDS &&& pc_ok r &&& atop_is_sp (a_model A)
      then Some [AS r (aset (aset (aset (a_regs A) 10%uint63 (XS (t_len k) w_zero)) 11%uint63 (XS (t_len k) (wofZ 1))) 12%uint63 (XL w_zero))
                    (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A + 1)]
      else None
  | _, _, _ => None
  end.

Section StrlenSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_strlen_sound (A : AST) (l : list AST) : sum_strlen segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_strlen in Hs.
  destruct (str_k (a_facts A) (aget (a_regs A) 10%uint63)) as [k|] eqn:Ek; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A)) STRLEN_WORDS) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  set (s := rg ms 10%bv).
  destruct (str_k_sound ρ (a_facts A) _ s k Hsat HF (Hregs 10%bv) Ek) as [Hk Hsa].
  destruct (eb_argvk segs ph ρ (ms_mem ms) nR k Heb Hk) as [Hcstr Hlen]. set (bs := nth (Z.to_nat k) (dec_argv ρ) []) in *.
  assert (Es : s = Z_to_bv 64 (str_addr ρ k)) by (apply word_lit_w; exact Hsa).
  assert (Hlk : 0 <= ρ (lenvar k) /\ str_addr ρ k + ρ (lenvar k) + 1 <= sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q
                /\ sp_val ρ <= str_addr ρ k).
  { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
  destruct Hlk as (Hlk0 & Hlk1 & Hlk2).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec r Epc) as [Hr4 Hr26].
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).
  apply (strlen_sum segs cfg b HW ms model (KT ρ o') s bs Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - rewrite Es. exact Hcstr.
  - rewrite Hsa, Hlen. lia.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop, Hsa. lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - intros ms' (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hpc' H10' H11' H12'.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model) _ o' Ho).
    assert (Hlv : forall c, 0 <= c <= 1 -> smod ρ (t_len k) (wofZ c) = ρ (lenvar k) + c).
    { intros c Hc. unfold smod, t_len. cbn [teval]. rewrite wZ_wofZ. rewrite (Z.mod_small c) by (unfold two64; lia).
      rewrite Z.mod_small by (unfold two64; lia). lia. }
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. apply word_lit_w. exact Hra.
    + exact Epc.
    + exact F1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' [10%bv; 11%bv; 12%bv] Hregs F7).
      * intros r0 Hr0. change 12%uint63 with (ri 12%bv). change 11%uint63 with (ri 11%bv). change 10%uint63 with (ri 10%bv).
        rewrite aget_aset_other by (intros E; apply Hr0; right; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr0; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr0; left; apply bv_eq; exact E). reflexivity.
      * intros r0 [<-|[<-|[<-|[]]]]; change 12%uint63 with (ri 12%bv); change 11%uint63 with (ri 11%bv); change 10%uint63 with (ri 10%bv).
        -- rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_other by (vm_compute; discriminate).
           rewrite aget_aset_same by (vm_compute; discriminate). cbn [xv_val]. rewrite H10'. change w_zero with (wofZ 0).
           rewrite (Hlv 0 ltac:(lia)). rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
        -- rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_same by (vm_compute; discriminate).
           cbn [xv_val]. rewrite H11'. rewrite (Hlv 1 ltac:(lia)).
           rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
        -- rewrite aget_aset_same by (vm_compute; discriminate). cbn [xv_val]. rewrite H12'. reflexivity.
    + rewrite F5. exact Hres.
    + exact F2.
    + rewrite F6. exact Hmem.
    + rewrite F6. exact Hhs.
    + rewrite F6. exact Hcov.
    + exact Hcomp.
    + rewrite F6. exact Hnaok.
    + reflexivity.
    + exact Hsat.
    + left. split; [reflexivity | lia].
Qed.

End StrlenSound.

Definition sp8_terms : terms := [(v_x0, 2); (v_x1, 8); (v_x2, 512); (v_x3, 4096)].

Lemma sp8_val (ρ : valuation) : sp_val ρ = 8 * teval ρ sp8_terms.
Proof. unfold sp_val, sp_terms, sp8_terms. cbn [teval]. ring. Qed.

Definition grant_comp (am : amodel) (R : region) : bool :=
  match rg_ts R with
  | [(g, c)] =>
      (c =? 512) &&& (wZ (rg_bo R) =? 2147450880) &&&
      lexists (fun e => match ae_base e with
                        | (b0, [(g', c')]) => (b0 =? 0) &&& (g' =? g)%uint63 &&& (c' =? 4096) &&& (8 * to_Z (rg_n R) <=? ae_size e)
                        | _ => false
                        end) (am_maps am)
  | _ => false
  end.

Definition sh_below (s : store) (am : amodel) (R : region) : bool :=
  negb (is_shadow R) ||| grant_comp am R
  ||| rbetween 2 s (lsub (2147450880, sp8_terms) (wS (rg_bo R) + to_Z (rg_n R), rg_ts R)) 0 4611686018427387904.

Definition eb_sh_ok (s : store) (am : amodel) (A : list region) : bool := lforall (sh_below s am) A &&& hs_witness s A.

Lemma grant_comp_sound (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (am : amodel) (model : Model) (R : region) :
  MR segs fs0 ρ am model -> atop_is_sp am = true -> sp_window_lo <= sp_val ρ <= sp_window_hi -> grant_comp am R = true ->
  forall z, 2147450880 + sp_val ρ / 8 <= z -> ~ in_rg ρ R z.
Proof.
  intros Hmod Eat Hsp H z Hz Hc. unfold grant_comp in H. destruct (rg_ts R) as [|[g c] [|]] eqn:Ets; try discriminate.
  apply land_true in H as [H He]. apply land_true in H as [Hc512 Hbo]. apply Z.eqb_eq in Hc512. apply Z.eqb_eq in Hbo. subst c.
  apply lexists_exists in He as [e [HIn He]]. destruct (ae_base e) as [b0 [|[g' c'] [|]]] eqn:Eb; try discriminate.
  apply land_true in He as [He Hsz]. apply land_true in He as [He Hc']. apply land_true in He as [Hb0 Hg].
  apply Z.eqb_eq in Hb0. apply Uint63.eqb_spec in Hg. apply Z.eqb_eq in Hc'. apply Z.leb_le in Hsz. subst b0 g' c'.
  pose proof (MR_ent segs fs0 ρ am model e Hmod HIn) as Hok. pose proof Hok as (Ho1 & Ho2 & Ho3).
  pose proof (mr_top segs fs0 ρ am model Hmod _ (MR_ent_in segs fs0 ρ am model e Hmod HIn)) as Htop.
  rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok), (atop_is_sp_sound segs fs0 ρ am model Hmod Eat) in Htop.
  rewrite Eb in Ho1, Ho3, Htop. unfold leval in Ho1, Ho3, Htop. cbn [fst snd teval] in Ho1, Ho3, Htop.
  unfold in_rg, rbase, smod in Hc. rewrite Ets, Hbo in Hc. cbn [teval] in Hc.
  pose proof (to_Z_bounded (rg_n R)) as Hnb. unfold sp_window_lo, sp_window_hi in Hsp. unfold AxAcct.two64 in *.
  rewrite Z.mod_small in Hc by lia.
  rewrite (sp8_val ρ) in Hz, Htop, Hsp. rewrite Z.mul_comm, Z.div_mul in Hz by lia. lia.
Qed.

Lemma sh_below_sound (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (s : store) (am : amodel) (model : Model) (R : region) :
  sat ρ s -> MR segs fs0 ρ am model -> atop_is_sp am = true -> region_wf ρ R -> sp_window_lo <= sp_val ρ <= sp_window_hi ->
  sh_below s am R = true -> is_shadow R = true ->
  forall z, 2147450880 + sp_val ρ / 8 <= z < hs_hi -> ~ in_rg ρ R z.
Proof.
  intros Hs Hmod Eat Hwf Hsp H Hsh z Hz Hc. unfold sh_below in H. rewrite Hsh in H. cbn [negb] in H.
  apply lor_true in H as [H|H]; [exact (grant_comp_sound segs fs0 ρ am model R Hmod Eat Hsp H z ltac:(lia) Hc)|].
  pose proof (rbetween_sound ρ s 2 _ _ _ Hs H) as Hr. rewrite leval_lsub in Hr.
  unfold leval in Hr. cbn [fst snd] in Hr. set (T := teval ρ sp8_terms) in *.
  assert (E8 : sp_val ρ / 8 = T) by (rewrite (sp8_val ρ); fold T; rewrite Z.mul_comm; apply Z.div_mul; lia). rewrite E8 in Hz.
  rewrite (sp8_val ρ) in Hsp. fold T in Hsp.
  destruct Hwf as [W1 [W2 _]]. unfold in_rg in Hc.
  set (L := wS (rg_bo R) + teval ρ (rg_ts R)) in *.
  assert (Eb : rbase ρ R = L mod two64).
  { unfold rbase, smod, L. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r. f_equal. ring. }
  pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in Hnb.
  unfold hs_hi, two64, sp_window_lo, sp_window_hi in *.
  destruct (Z_lt_le_dec L 0) as [Hneg|Hnn].
  - rewrite <- (Z.mod_unique L 18446744073709551616 (-1) (L + 18446744073709551616)) in Eb by lia. lia.
  - rewrite Z.mod_small in Eb by lia. lia.
Qed.

Lemma eb_sh_zero (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (s : store) (am : amodel) (model : Model) (A : list region)
    (m : word -> option byte) :
  segs_low segs -> sat ρ s -> MR segs fs0 ρ am model -> atop_is_sp am = true -> RMem segs ρ A m -> hs_ok ρ A m ->
  sp_window_lo <= sp_val ρ <= sp_window_hi -> eb_sh_ok s am A = true ->
  forall q, 2147450880 + sp_val ρ / 8 <= q < hs_hi -> bat segs m (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Proof.
  intros Hlow Hs Hmod Eat HM Hhs Hsp H q Hq. unfold eb_sh_ok in H. apply land_true in H as [Hall Hwit].
  pose proof (hs_mapped segs ρ s A m Hlow Hs HM Hhs Hwit) as Hmap.
  assert (Hq0 : hs_beg <= q).
  { assert (sp_window_lo / 8 <= sp_val ρ / 8) by (apply Z.div_le_mono; lia). unfold sp_window_lo, hs_beg in *.
    change (140735340871680 / 8) with 17591917608960 in *. lia. }
  destruct (hs_old_of_wit ρ s A m Hwit Hhs) as [_ [P2 _]].
  destruct (P2 q ltac:(right; lia)) as [X|X].
  - intros R HIn Hsh. destruct HM as [Hok _].
    exact (sh_below_sound segs fs0 ρ s am model R Hs Hmod Eat (regions_ok_in ρ A R Hok HIn) Hsp (lforall_forall _ _ Hall R HIn) Hsh q Hq).
  - exfalso. exact (Hmap q ltac:(lia) X).
  - unfold bat. unfold wz in X. rewrite X. reflexivity.
Qed.

Definition rip_code_ok (segs : list Segment) (b z gK gMB gME gHE : Z) : bool :=
  words_ok segs b RIP_WORDS &&& words_ok segs (b - 0x48c) HLP_WORDS &&& words_ok segs z MIZ_WORDS
  &&& pair_ok segs (b - 0x48c) 0x0 11 11 gK &&& pair_ok segs (b - 0x48c) 0x20 13 13 gMB
  &&& pair_ok segs (b - 0x48c) 0x28 14 14 gME &&& pair_ok segs (b - 0x48c) 0x44 14 14 gHE
  &&& pair_ok segs b 0x2c 10 21 gK &&& pair_ok segs b 0x4c 13 13 gMB &&& pair_ok segs b 0x54 14 14 gME
  &&& pair_ok segs b 0x70 14 14 gHE &&& pair_ok segs b 0x94 12 12 gMB &&& pair_ok segs b 0x9c 13 13 gME
  &&& pair_ok segs b 0xb8 13 13 gHE &&& jal_ok segs b 0x170 1 z.

Definition rip_code_okf (segs : list Segment) (b z gK gMB gME gHE : Z) : bool :=
  words_ok_f segs b RIP_WORDS &&& words_ok_f segs (b - 0x48c) HLP_WORDS &&& words_ok_f segs z MIZ_WORDS
  &&& pair_ok_f segs (b - 0x48c) 0x0 11 11 gK &&& pair_ok_f segs (b - 0x48c) 0x20 13 13 gMB
  &&& pair_ok_f segs (b - 0x48c) 0x28 14 14 gME &&& pair_ok_f segs (b - 0x48c) 0x44 14 14 gHE
  &&& pair_ok_f segs b 0x2c 10 21 gK &&& pair_ok_f segs b 0x4c 13 13 gMB &&& pair_ok_f segs b 0x54 14 14 gME
  &&& pair_ok_f segs b 0x70 14 14 gHE &&& pair_ok_f segs b 0x94 12 12 gMB &&& pair_ok_f segs b 0x9c 13 13 gME
  &&& pair_ok_f segs b 0xb8 13 13 gHE &&& jal_ok_f segs b 0x170 1 z.

Lemma rip_code_okf_ok (segs : list Segment) (b z gK gMB gME gHE : Z) : rip_code_okf segs b z gK gMB gME gHE = true -> rip_code_ok segs b z gK gMB gME gHE = true.
Proof.
  unfold rip_code_okf, rip_code_ok. rewrite !pair_ok_f_eq, jal_ok_f_eq. intros H.
  apply land_true in H as [H J1]. apply land_true in H as [H P11]. apply land_true in H as [H P10]. apply land_true in H as [H P9]. apply land_true in H as [H P8].
  apply land_true in H as [H P7]. apply land_true in H as [H P6]. apply land_true in H as [H P5]. apply land_true in H as [H P4].
  apply land_true in H as [H P3]. apply land_true in H as [H P2]. apply land_true in H as [H P1]. apply land_true in H as [H W3].
  apply land_true in H as [W1 W2]. apply words_ok_f_eq in W1. apply words_ok_f_eq in W2. apply words_ok_f_eq in W3.
  rewrite W1, W2, W3, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, P11, J1. reflexivity.
Qed.

Definition globals_ok (segs : list Segment) (mem : list region) (gK gMB gME gHE aK aMB aME aHE : Z) : bool :=
  cell_lit segs mem gK aK &&& cell_lit segs mem aK 0x7fff8000 &&& cell_lit segs mem gMB aMB &&& cell_lit segs mem aMB 0
  &&& cell_lit segs mem gME aME &&& cell_lit segs mem aME 0 &&& cell_lit segs mem gHE aHE &&& cell_lit segs mem aHE 0x7fffffffffff
  &&& forallb (in_seg segs) [gK; aK; gMB; aMB; gME; aME; gHE; aHE].

Definition RCLOB : list reg := [5%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv].

Definition rip_regs (regs : aregs) : aregs := aset (clob RCLOB regs) 10%uint63 (XL w_zero).

Definition len_hi (s : store) (k : Z) : Z :=
  match lrange s (lvar (lenvar k) 1) with Some (_, h) => Z.min h 131071 | None => 131071 end.

Definition sum_rip_g (ckR : (list Segment -> Z -> Z -> Z -> Z -> Z -> Z -> bool)) (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  let s := a_facts A in
  match rip_params T b, str_k s (aget (a_regs A) 10%uint63), aget (a_regs A) 11%uint63, aget (a_regs A) 1%uint63,
        aget (a_regs A) 2%uint63, find_entry (a_mem A) with
  | Some (mz, gK, gMB, gME, gHE, aK, aMB, aME, aHE), Some k, XS tn on, XL r, XS ts o, Some ph =>
      let hi := len_hi s k in
      if teqb tn (t_len k) &&& (wZ on =? 1) &&& teqb ts sp_terms &&& (- 8388608 + 72 <=? wS o) &&& (wS o <=? 0)
         &&& pc_ok r &&& atop_is_sp (a_model A) &&& (a_budget A + 4096 * (hi + 3) <=? LIM)
         &&& ckR segs b mz gK gMB gME gHE &&& globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE
         &&& eb_sh_ok s (a_model A) (a_mem A) then
        match a_store segs (a_mem A) (XS sp_terms (wofZ (wS o - 72))) (repeat BT 72) with
        | Some mem' =>
            Some [AS r (rip_regs (a_regs A)) (resv_drop (a_resv A)) mem' s (a_model A) (a_budget A + 4096 * (hi + 3)) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _, _, _ => None
  end.

Definition sum_rip (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_rip_g rip_code_okf T segs LIM A.

Definition rip_ck (T : img_tabs) (segs : list Segment) (b : Z) : bool :=
  match rip_params T b with Some (mz, gK, gMB, gME, gHE, _, _, _, _) => rip_code_okf segs b mz gK gMB gME gHE | None => false end.

Definition ck_true6 (_ : list Segment) (_ _ _ _ _ _ : Z) : bool := true.
Definition ck_true1 (_ : list Segment) (_ : Z) : bool := true.

Lemma sum_rip_g_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  rip_ck T segs (wZ (a_pc A)) = true -> sum_rip_g ck_true6 T segs LIM A = Some l -> sum_rip T segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_rip, sum_rip_g in *. cbv zeta in *. unfold rip_ck in Hck. unfold ck_true6 in H.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|]; [|exact H]. rewrite Hck. exact H.
Qed.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RipSound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_rip_sound (A : AST) (l : list AST) : sum_rip T segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_rip, sum_rip_g in Hs.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|] eqn:Ep; [|discriminate].
  destruct (str_k (a_facts A) (aget (a_regs A) 10%uint63)) as [k|] eqn:Ek; [|discriminate].
  destruct (aget (a_regs A) 11%uint63) as [| tn on | | | |] eqn:E11; try discriminate.
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (aget (a_regs A) 2%uint63) as [| ts o | | | |] eqn:E2; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  cbv zeta in Hs.
  destruct (teqb tn (t_len k)) eqn:Etn; [|discriminate]. apply teqb_eq in Etn. subst tn.
  destruct (wZ on =? 1) eqn:Eon; [|discriminate]. apply Z.eqb_eq in Eon.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 + 72 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (a_budget A + 4096 * (len_hi (a_facts A) k + 3) <=? LIM) eqn:Hbud; [|discriminate]. apply Z.leb_le in Hbud.
  destruct (rip_code_okf segs (wZ (a_pc A)) mz gK gMB gME gHE) eqn:Hcode; [|discriminate]. apply rip_code_okf_ok in Hcode.
  destruct (globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE) eqn:Hglob; [|discriminate].
  destruct (eb_sh_ok (a_facts A) (a_model A) (a_mem A)) eqn:Hsh; [|discriminate].
  destruct (a_store segs (a_mem A) (XS sp_terms (wofZ (wS o - 72))) (repeat BT 72)) as [mem'|] eqn:Est; [|discriminate].
  injection Hs as <-.
  unfold rip_code_ok in Hcode.
  apply andb_prop in Hcode as [Hcode HJz]. apply andb_prop in Hcode as [Hcode HPb8]. apply andb_prop in Hcode as [Hcode HP9c]. apply andb_prop in Hcode as [Hcode HP94].
  apply andb_prop in Hcode as [Hcode HP70]. apply andb_prop in Hcode as [Hcode HP54]. apply andb_prop in Hcode as [Hcode HP4c].
  apply andb_prop in Hcode as [Hcode HP2c]. apply andb_prop in Hcode as [Hcode HPh44]. apply andb_prop in Hcode as [Hcode HPh28].
  apply andb_prop in Hcode as [Hcode HPh20]. apply andb_prop in Hcode as [Hcode HPh0]. apply andb_prop in Hcode as [Hcode HWz].
  apply andb_prop in Hcode as [HW HWh].
  unfold globals_ok in Hglob.
  apply andb_prop in Hglob as [Hglob Hins]. apply andb_prop in Hglob as [Hglob C8]. apply andb_prop in Hglob as [Hglob C7].
  apply andb_prop in Hglob as [Hglob C6]. apply andb_prop in Hglob as [Hglob C5]. apply andb_prop in Hglob as [Hglob C4].
  apply andb_prop in Hglob as [Hglob C3]. apply andb_prop in Hglob as [C1 C2].
  rewrite forallb_forall in Hins.
  destruct (rip_params_ok T HT _ _ _ _ _ _ _ _ _ _ Ep) as [Hgb Hb8].
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  set (beg := rg ms 10%bv).
  destruct (str_k_sound ρ (a_facts A) _ beg k Hsat HF (Hregs 10%bv) Ek) as [Hk Hbeg].
  assert (Hlk : 0 <= ρ (lenvar k) <= 131071 /\ str_addr ρ k + ρ (lenvar k) + 1 <= sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q
                /\ sp_val ρ <= str_addr ρ k).
  { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
  destruct Hlk as (Hlk0 & Hlk1 & Hlk2).
  assert (Hhi : ρ (lenvar k) <= len_hi (a_facts A) k).
  { unfold len_hi. destruct (lrange (a_facts A) (lvar (lenvar k) 1)) as [[lo h]|] eqn:El; [|lia].
    pose proof (lrange_sound ρ _ _ Hsat _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X. lia. }
  set (n := ρ (lenvar k) + 1).
  assert (H11 : rg ms 11%bv = Z_to_bv 64 n).
  { apply word_lit_w. change 11%uint63 with (ri 11%bv) in E11. rewrite (reg_form ρ _ ms 11%bv _ _ Hregs E11).
    unfold smod, t_len. cbn [teval]. rewrite Eon. unfold n. rewrite Z.mod_small by (unfold two64; lia). lia. }
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec r Epc) as [Hr4 Hr26].
  assert (HSP : bv_unsigned (rg ms 2%bv) = sp_val ρ + wS o).
  { change 2%uint63 with (ri 2%bv) in E2. rewrite (reg_form ρ _ ms 2%bv _ _ Hregs E2). unfold smod.
    change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r. apply Z.mod_small. unfold two64. lia. }
  set (SP := bv_unsigned (rg ms 2%bv)) in *.
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).

  assert (Hv72 : xv_val ρ (XS sp_terms (wofZ (wS o - 72))) (Z_to_bv 64 (SP - 72))).
  { cbn [xv_val]. rewrite Z_to_bv_unsigned. unfold bv_wrap, smod. change (bv_modulus 64) with two64.
    change (teval ρ sp_terms) with (sp_val ρ). rewrite wZ_wofZ, Zplus_mod_idemp_r. rewrite HSP. f_equal. lia. }
  destruct (a_store_sound segs ρ (a_mem A) mem' (ms_mem ms) _ _ (repeat BT 72) (repeat (Z_to_bv 8 0) 72) Hmem Hv72
              ltac:(rewrite repeat_length; lia) ltac:(repeat constructor) Est) as [Hok72 _].
  rewrite repeat_length in Hok72.

  assert (Hgl : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> 0 <= a /\ a + 8 <= ls_beg).
  { intros a Hin. pose proof (Hins a Hin) as X. unfold in_seg in X. apply existsb_exists in X as [sg [HIns Hcs]].
    apply andb_prop in Hcs as [Cs1 Cs2]. apply Z.leb_le in Cs1. apply Z.leb_le in Cs2. pose proof (Hlow sg HIns). lia. }
  assert (Hd8 : 0x7fff8000 + (bv_unsigned beg + n - 1) / 8 < hs_hi).
  { assert ((bv_unsigned beg + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold hs_hi. lia. }
  apply (rip_sum segs cfg b mz gK gMB gME gHE aK aMB aME aHE HW HWh HWz HJz HPh0 HPh20 HPh28 HPh44 HP2c HP4c HP54 HP70 HP94 HP9c HPb8 Hgb Hb8
           ms model (KT ρ o') beg n Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - exact H11.
  - unfold n. lia.
  - unfold n. lia.
  - left. lia.
  - destruct Hmem as [Hok HRR].
    assert (Hc : forall a v, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> cell_lit segs (a_mem A) a v = true -> cell8 segs (ms_mem ms) a v).
    { intros a v Hin Hcl. destruct (Hgl a Hin). apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) a v (conj Hok HRR)); [unfold ls_beg in *; lia | exact Hcl]. }
    unfold globals. repeat split; apply Hc; first [assumption | cbn; tauto].
  - assert (Hn : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> no_lazy model a (a + 8))
      by (intros a Hin; exact (no_lazy_img segs Hlow model a 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) (Hins a Hin))).
    unfold globals_nl. repeat split; apply Hn; cbn; tauto.
  - intros q Hq.
    apply (eb_sh_zero segs fs0 ρ (a_facts A) (a_model A) model (a_mem A) (ms_mem ms) Hlow Hsat Hmod Eat Hmem Hhs ltac:(unfold sp_window_lo, sp_window_hi; lia) Hsh).
    assert (sp_val ρ / 8 <= bv_unsigned beg / 8) by (apply Z.div_le_mono; lia). lia.
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. unfold n. lia.
  - lia.
  - exact Hok72.
  - apply (no_lazy_above segs fs0 ρ (a_model A) model _ _ Hmod). rewrite Hatop. lia.
  - right. unfold hs_hi in Hd8. lia.
  - intros a Hin. left. destruct (Hgl a Hin). unfold ls_beg in *. lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  -
    intros ms' model' HRP Hpc' H10' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    pose proof HRP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct Hmat as [[pages Em'] Hused].
    assert (Hsf : Forall2 same_fields (a_mem A) mem') by exact (a_store_fields segs (a_mem A) mem' _ _ Est).
    assert (Hfr : forall x : word, ~ (bv_unsigned (Z_to_bv 64 (SP - 72)) <= bv_unsigned x < bv_unsigned (Z_to_bv 64 (SP - 72)) + Z.of_nat 72) ->
              ms_mem ms' x = ms_mem ms x).
    { intros x Hx. apply P7. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. change (bv_modulus 64) with (2 ^ 64) in Hx.
      rewrite Z.mod_small in Hx by lia. lia. }
    assert (Hss' : forall z, in_ss z -> ms_mem ms' (wz z) = ms_mem ms (wz z)).
    { intros z Hz. apply P7. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hz. rewrite u_wz by lia. lia. }
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model' HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. apply word_lit_w. exact Hra.
    + exact Epc.
    + exact P1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' AsanSRipA.HCLOB Hregs P6).
      * intros r0 Hr0. destruct (Z.eq_dec (bv_unsigned r0) 0) as [E0|E0]; [apply aget_zero; exact E0|].
        unfold rip_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset, (proj2 (Z.eqb_neq _ _) E0).
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { exfalso. apply Hr0. right. left. apply bv_eq. exact E10. }
        apply clob_out; [|exact E0]. intros X. apply Hr0. unfold RCLOB in X. unfold AsanSRipA.HCLOB. cbn [In] in *.
        destruct X as [X|X]; [left; exact X | right; right; exact X].
      * intros r0 Hr0. unfold rip_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset.
        destruct (Z.eqb_spec (bv_unsigned r0) 0) as [E0|E0].
        { exfalso. unfold AsanSRipA.HCLOB in Hr0. cbn [In] in Hr0.
          destruct Hr0 as [X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]; rewrite <- X in E0; vm_compute in E0; discriminate E0. }
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { assert (r0 = 10%bv) by (apply bv_eq; symmetry; exact E10). subst r0. cbn [xv_val]. rewrite H10'. reflexivity. }
        rewrite (clob_in' RCLOB (a_regs A) r0); [exact I| |exact E0].
        unfold AsanSRipA.HCLOB in Hr0. unfold RCLOB. cbn [In] in *. destruct Hr0 as [<-|[<-|Hr0]]; [tauto | exfalso; apply E10; reflexivity | tauto].
    + destruct (a_resv A); cbn [resv_drop RResv] in *; try exact I. destruct P5 as [X|X]; rewrite X; [exact Hres | reflexivity].
    + exact P2.
    + exact (a_store_BT_havoc segs ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms') _ _ 72 Hmem Hv72 ltac:(lia) ltac:(lia) Est Hfr P8).
    + exact (hs_ok_out ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms') Hsf Hss' Hhs).
    + intros x Hx.
      destruct (Z_lt_le_dec (bv_unsigned x) (SP - 72)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) SP) as [L2|L2]].
      * rewrite P7 in Hx by lia. exact (Hcov x Hx).
      * right. left. rewrite Hatop. lia.
      * rewrite P7 in Hx by lia. exact (Hcov x Hx).
    + exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      destruct Hnaok as [N1 [N2 N3]]. split; [|split; [exact N2 | exact N3]].
      intros x Hx Hna.
      destruct (Z_lt_le_dec (bv_unsigned x) (SP - 72)) as [L1|L1]; [|destruct (Z_lt_le_dec (bv_unsigned x) SP) as [L2|L2]].
      * rewrite P7 in Hx by lia. exact (N1 x Hx Hna).
      * destruct (mr_na_maps segs fs0 ρ _ _ Hmod _ Hna) as [p [Hp Hpz]].
        pose proof (mr_top segs fs0 ρ _ _ Hmod p Hp) as Htp. rewrite Hatop in Htp. lia.
      * rewrite P7 in Hx by lia. exact (N1 x Hx Hna).
    + reflexivity.
    + exact Hsat.
    + right. exists pages. split; [exact Em'|]. unfold n in Hused. destruct Hb as [Hb1 Hb2]. lia.
Qed.

End RipSound.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
