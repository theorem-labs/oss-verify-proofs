(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanSLibc AsanWEntry AsanWEb AsanWEbLoad AxSum.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma eb_of_R (segs : list Segment) (ρ : valuation) (A : list region) (m : word -> option byte) (ph : PhdrInfo) :
  RMem segs ρ A m -> find_entry A = Some ph -> exists nR, eb_rel ph ρ m (sp_val ρ) nR.
Proof.
  intros [_ HR] Hf. destruct (find_entry_spec A ph Hf) as [R [HIn Hk]].
  rewrite Forall_forall in HR. specialize (HR R HIn). unfold RRegion in HR. rewrite Hk in HR.
  exists (to_Z (rg_n R)). pose proof (eb_rel_base ph ρ m _ _ HR) as Eb. rewrite Eb in HR. exact HR.
Qed.

Lemma no_lazy_above (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (am : amodel) (model : Model) (lo hi : Z) :
  MR segs fs0 ρ am model -> alloc_top (m_vmmaps model) <= lo -> no_lazy model lo hi.
Proof. intros HM Hlo. exact (no_lazy_above_atop model lo hi (mr_lazy segs fs0 ρ am model HM) Hlo). Qed.

Definition atop_is_sp (am : amodel) : bool := teqb (snd (am_atop am)) sp_terms &&& (fst (am_atop am) =? - 8388608).

Lemma atop_is_sp_sound (segs : list Segment) (fs0 : Fs.Fs) (ρ : valuation) (am : amodel) (model : Model) :
  MR segs fs0 ρ am model -> atop_is_sp am = true -> alloc_top (m_vmmaps model) = sp_val ρ - 8388608.
Proof.
  intros HM H. unfold atop_is_sp in H. destruct (teqb (snd (am_atop am)) sp_terms) eqn:E1; [|discriminate].
  apply teqb_eq in E1. apply Z.eqb_eq in H. rewrite (mr_atop segs fs0 ρ am model HM).
  destruct (am_atop am) as [c t]. cbn [fst snd] in *. subst c t. unfold leval. cbn [fst snd]. fold (sp_val ρ). lia.
Qed.

Lemma wbv_wofZ (z : Z) : 0 <= z < 2 ^ 64 -> wbv (wofZ z) = Z_to_bv 64 z.
Proof. intros H. unfold wbv. rewrite wZ_wofZ. f_equal. apply Z.mod_small. unfold two64. exact H. Qed.

Lemma pre_le_tab (j : nat) (L : list (list byte)) : (pre j L <= total_arg_bytes_nat L)%nat.
Proof.
  unfold pre. revert j. induction L as [|a L IH]; intros [|j]; cbn [firstn total_arg_bytes_nat fold_right]; try lia.
  specialize (IH j). unfold total_arg_bytes_nat in IH. lia.
Qed.

Lemma eb_span (ph : PhdrInfo) (ρ : valuation) : eb_facts ρ ->
  sp_window_lo <= sp_val ρ /\ sp_val ρ + (184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q + 16) <= sp_window_hi
  /\ Z.of_nat (length (eb_image ph ρ)) = 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q + 16.
Proof.
  intros HF. pose proof (R7_length ph ρ HF) as HL. pose proof (R7_length (mkPhdrInfo 0 0 0) ρ HF) as HL0.
  destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2). rewrite HL0 in H2.
  split; [exact H1|]. split; [lia | lia].
Qed.

Definition t_a : terms := [(v_argc, 8)].

Definition sum_envp (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  match aget (a_regs A) 9%uint63, find_entry (a_mem A) with
  | XS ts o, Some ph =>
      if words_ok_f segs b ENVP_WORDS &&& same_addr (a_facts A) ts o (sp_terms ++ t_a) (wofZ 16) &&& pc_ok (wofZ (b + 12))
         &&& atop_is_sp (a_model A)
      then Some [AS (wofZ (b + 12)) (aset (aset (a_regs A) 9%uint63 (XS (sp_terms ++ t_ae) (wofZ 24))) 10%uint63 (XL w_zero))
                    (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A + 1)]
      else None
  | _, _ => None
  end.

Section EnvpSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_envp_sound (A : AST) (l : list AST) : sum_envp segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_envp in Hs.
  destruct (aget (a_regs A) 9%uint63) as [| ts o | | | |] eqn:E9; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A)) ENVP_WORDS) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (same_addr (a_facts A) ts o (sp_terms ++ t_a) (wofZ 16)) eqn:Ets; [|discriminate].
  destruct (pc_ok (wofZ (wZ (a_pc A) + 12))) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF. pose proof (eb_span ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & _). unfold sp_window_lo, sp_window_hi in *.
  assert (Hq0 : 0 <= ρ v_q) by (destruct HF as (_ & _ & _ & _ & Hta & Hte & Hq & _); rewrite Hq, Hta, Hte;
    pose proof (total_arg_bytes_nonneg (dec_argv ρ)); pose proof (total_arg_bytes_nonneg (dec_envp ρ)); apply Z.div_pos; lia).
  set (p := rg ms 9%bv).
  assert (Hp : bv_unsigned p = sp_val ρ + 16 + 8 * ρ v_argc).
  { pose proof (Hregs 9%bv) as H9. change (ri 9%bv) with 9%uint63 in H9. rewrite E9 in H9. cbn [xv_val] in H9. fold p in H9.
    rewrite H9, (same_addr_sound ρ _ _ _ _ _ Hsat Ets). unfold smod. rewrite teval_app. fold (sp_val ρ). unfold t_a. cbn [teval].
    rewrite wZ_wofZ, (Z.mod_small 16) by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia. }
  set (k := Z.to_nat (ρ v_envc)).
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).
  apply (envp_sum segs cfg b HW ms model (KT ρ o') p k Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - intros j Hj.
    assert (Ea : bv_unsigned (p + Z_to_bv 64 (8 * Z.of_nat j))%bv = sp_val ρ + (16 + 8 * ρ v_argc + 8 * Z.of_nat j)).
    { rewrite bv_add_unsigned, Hp, Z_to_bv_unsigned. rewrite (bv_wrap_small 64 (8 * Z.of_nat j)) by (change (bv_modulus 64) with (2 ^ 64); lia).
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia. }
    pose proof (rd_block segs ph ρ (ms_mem ms) nR 8 (16 + 8 * ρ v_argc + 8 * Z.of_nat j) _ Heb ltac:(lia) ltac:(lia) Ea) as Hrd.
    replace (Z.to_nat (16 + 8 * ρ v_argc + 8 * Z.of_nat j)) with (16 + 8 * Z.to_nat (ρ v_argc) + 8 * j)%nat in Hrd by lia.
    destruct (Nat.eqb_spec j k) as [Ejk|Ejk].
    + subst j. unfold k in Hrd. rewrite (R3_null ph ρ HF) in Hrd. eexists. split; [exact Hrd|].
      rewrite bytes_le_n_to_le_8. reflexivity.
    + rewrite (R3_envp ph ρ HF j ltac:(lia)) in Hrd. eexists. split; [exact Hrd|].
      rewrite bytes_le_n_to_le_8. apply Z.eqb_neq. rewrite Z_to_bv_unsigned.
      pose proof (Nat2Z.is_nonneg (pre j (dec_envp ρ))) as Hpre.
      assert (Hta : 0 <= ρ v_ta) by (destruct HF as (_ & _ & _ & _ & Hta & _); rewrite Hta; apply total_arg_bytes_nonneg).
      assert (Hpre2 : ρ v_ta + Z.of_nat (pre j (dec_envp ρ)) <= 8 * ρ v_q).
      { destruct HF as (_ & _ & _ & _ & Hta' & Hte' & Hq' & _).
        assert (Z.of_nat (pre j (dec_envp ρ)) <= ρ v_te).
        { rewrite Hte'. rewrite total_arg_bytes_Z. apply Nat2Z.inj_le. apply pre_le_tab. }
        rewrite Hq'. pose proof (Z.div_mod (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)). lia. }
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - rewrite Hp. unfold k. lia.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop, Hp. lia.
  - intros ms' (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hpc' H9' H10'.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model) _ o' Ho).
    assert (Hb12 : 0 <= b + 12 < 2 ^ 64) by (pose proof (wZ_range (a_pc A)); unfold b, two64 in *; lia).
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. rewrite wbv_wofZ by exact Hb12. reflexivity.
    + exact Epc.
    + exact F1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' [9%bv; 10%bv] Hregs F7).
      * intros r Hr. change 10%uint63 with (ri 10%bv). change 9%uint63 with (ri 9%bv).
        rewrite aget_aset_other by (intros E; apply Hr; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr; left; apply bv_eq; exact E). reflexivity.
      * intros r [<-|[<-|[]]].
        -- change 10%uint63 with (ri 10%bv). change 9%uint63 with (ri 9%bv).
           rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_same by (vm_compute; discriminate).
           cbn [xv_val]. rewrite H9'. rewrite bv_add_unsigned, Hp, Z_to_bv_unsigned.
           unfold smod. change ((v_x0, 16) :: (v_x1, 64) :: (v_x2, 4096) :: (v_x3, 32768) :: t_ae) with (sp_terms ++ t_ae).
           rewrite teval_app. fold (sp_val ρ). unfold t_ae. cbn [teval]. rewrite wZ_wofZ.
           rewrite (bv_wrap_small 64 (8 * Z.of_nat (S k))) by (change (bv_modulus 64) with (2 ^ 64); unfold k; lia).
           unfold bv_wrap. change (bv_modulus 64) with two64. rewrite (Z.mod_small 24) by (unfold two64; lia). f_equal. unfold k. lia.
        -- change 10%uint63 with (ri 10%bv). rewrite aget_aset_same by (vm_compute; discriminate). cbn [xv_val]. rewrite H10'. reflexivity.
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

End EnvpSound.

Lemma rdn_of_nth (segs : list Segment) (m : word -> option byte) : forall (l : list byte) (a : Z),
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> m (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j l (Z_to_bv 8 0))) ->
  rdn segs m (Z_to_bv 64 a) (length l) = Some l.
Proof.
  induction l as [|x l IH]; intros a Ha Hn H; [reflexivity|]. cbn [length rdn] in *.
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth] in H0. rewrite H0.
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (symmetry; apply (wz_succ a)).
  rewrite (IH (a + 1)) by (try lia; intros j Hj; specialize (H (S j) ltac:(lia)); cbn [nth] in H;
    replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia; exact H).
  reflexivity.
Qed.

Lemma eb_argv0 (segs : list Segment) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (nR : Z) :
  eb_rel ph ρ m (sp_val ρ) nR ->
  let bs := nth 0 (dec_argv ρ) [] in
  cstr segs m (Z_to_bv 64 (sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc)) bs /\ Z.of_nat (length bs) = ρ (lenvar 0)
  /\ ρ (lenvar 0) + 1 <= 8 * ρ v_q.
Proof.
  intros Heb bs. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF. pose proof (eb_span ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & Hstr & _). destruct (Hstr 0 ltac:(lia)) as [Hl0 Hb0].
  assert (Hq : ρ (lenvar 0) + 1 <= 8 * ρ v_q).
  { pose proof HF as (_ & _ & _ & _ & Hta & Hte & Hq' & _).
    assert (ρ (lenvar 0) + 1 <= ρ v_ta).
    { rewrite Hta. pose proof (len_k ρ HF 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0. rewrite <- L0.
      destruct (dec_argv ρ) as [|a0 r] eqn:Ed; [exfalso; pose proof (len_av ρ HF) as X; rewrite Ed in X; cbn in X; lia|].
      cbn [nth]. unfold total_arg_bytes. cbn [fold_right]. pose proof (total_arg_bytes_nonneg r) as X. unfold total_arg_bytes in X. lia. }
    pose proof (total_arg_bytes_nonneg (dec_envp ρ)). rewrite Hq'.
    pose proof (Z.div_mod (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ρ v_ta + ρ v_te + 7) 8 ltac:(lia)). lia. }
  assert (Hlen : Z.of_nat (length bs) = ρ (lenvar 0)) by (exact (len_k ρ HF 0 ltac:(lia))).
  unfold sp_window_lo, sp_window_hi in *.
  split; [|split; [exact Hlen | exact Hq]]. split.
  - replace (S (length bs)) with (length (bs ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn [length]; lia).
    apply rdn_of_nth; [lia | rewrite length_app; cbn [length]; lia |].
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (eb_rel_byte ph ρ m _ _ Heb (184 + 8 * ρ v_argc + 8 * ρ v_envc + Z.of_nat j) ltac:(lia)) as Hbyte.
    replace (sp_val ρ + (184 + 8 * ρ v_argc + 8 * ρ v_envc + Z.of_nat j)) with (sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + Z.of_nat j) in Hbyte by lia.
    rewrite Hbyte. f_equal. rewrite (R5_str0 ph ρ HF (Z.of_nat j) ltac:(lia)).
    destruct (Z.ltb_spec (Z.of_nat j) (ρ (lenvar 0))) as [L|L].
    + rewrite app_nth1 by lia. pose proof (nth_k ρ HF 0 (Z.of_nat j) ltac:(lia) ltac:(lia)) as Hn.
      change (Z.to_nat 0) with 0%nat in Hn. rewrite Nat2Z.id in Hn. symmetry. exact Hn.
    + rewrite app_nth2 by lia. replace (j - length bs)%nat with 0%nat by lia. reflexivity.
  - intros x Hx. apply (In_nth _ _ (Z_to_bv 8 0)) in Hx as [j [Hj <-]].
    pose proof (nth_k ρ HF 0 (Z.of_nat j) ltac:(lia) ltac:(lia)) as Hn. change (Z.to_nat 0) with 0%nat in Hn. rewrite Nat2Z.id in Hn.
    fold bs in Hn. rewrite Hn. destruct (Hb0 (Z.of_nat j) ltac:(lia)) as [B1 B2].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; lia). lia.
Qed.

Definition resv_drop (r : rsv) : rsv := match r with RNone => RNone | _ => RUnk end.

Definition sum_prog (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) - 8 in
  match aget (a_regs A) 10%uint63, aget (a_regs A) 11%uint63, aget (a_regs A) 12%uint63, find_entry (a_mem A) with
  | XL c, XS ts o, XL sl, Some ph =>
      if words_ok_f segs b PROG_WORDS &&& same_addr (a_facts A) ts o (sp_terms ++ t_ae) (wofZ 185) &&& (wZ sl =? 47) &&& pc_ok (wofZ (b + 20))
         &&& atop_is_sp (a_model A) &&& in_seg segs (wZ c) &&& (0 <=? b)
      then match a_store segs (a_mem A) (XL c) (repeat BT 8) with
           | Some mem' =>
               Some [AS (wofZ (b + 20)) (aset (aset (a_regs A) 11%uint63 (XS (sp_terms ++ t_ae0) (wofZ 185))) 13%uint63 (XL w_zero))
                        (resv_drop (a_resv A)) mem' (a_facts A) (a_model A) (a_budget A) (a_steps A + 1)]
           | None => None
           end
      else None
  | _, _, _, _ => None
  end.

Section ProgSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_prog_sound (A : AST) (l : list AST) : sum_prog segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_prog in Hs.
  destruct (aget (a_regs A) 10%uint63) as [c| | | | |] eqn:E10; try discriminate.
  destruct (aget (a_regs A) 11%uint63) as [| ts o | | | |] eqn:E11; try discriminate.
  destruct (aget (a_regs A) 12%uint63) as [sl| | | | |] eqn:E12; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A) - 8) PROG_WORDS) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (same_addr (a_facts A) ts o (sp_terms ++ t_ae) (wofZ 185)) eqn:Ets; [|discriminate].
  destruct (wZ sl =? 47) eqn:Esl; [|discriminate]. apply Z.eqb_eq in Esl.
  destruct (pc_ok (wofZ (wZ (a_pc A) - 8 + 20))) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (in_seg segs (wZ c)) eqn:Eseg; [|discriminate].
  destruct (0 <=? wZ (a_pc A) - 8) eqn:Eb0; [|discriminate]. apply Z.leb_le in Eb0.
  destruct (a_store segs (a_mem A) (XL c) (repeat BT 8)) as [mem'|] eqn:Est; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A) - 8) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF. pose proof (eb_span ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & _). unfold sp_window_lo, sp_window_hi in *.
  destruct (eb_argv0 segs ph ρ (ms_mem ms) nR Heb) as (Hcstr & Hlen & Hq0). set (bs := nth 0 (dec_argv ρ) []) in *.
  assert (Hl0 : 0 <= ρ (lenvar 0)) by lia.
  set (PN := sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc) in *.
  set (pn := Z_to_bv 64 PN) in *.
  assert (Hupn : bv_unsigned pn = PN) by (unfold pn; rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); unfold PN; lia).
  set (cell := rg ms 10%bv).
  assert (Hcell : bv_unsigned cell = wZ c) by (pose proof (Hregs 10%bv) as X; change (ri 10%bv) with 10%uint63 in X; rewrite E10 in X; exact X).
  assert (Hcs : 0 <= wZ c /\ wZ c + 8 <= ls_beg).
  { unfold in_seg in Eseg. apply existsb_exists in Eseg as [sg [HIn Hc]]. apply andb_prop in Hc as [C1 C2].
    apply Z.leb_le in C1. apply Z.leb_le in C2. pose proof (Hlow sg HIn). lia. }
  unfold ls_beg in Hcs.
  assert (H11 : rg ms 11%bv = (pn + Z_to_bv 64 1)%bv).
  { apply bv_eq. pose proof (Hregs 11%bv) as X. change (ri 11%bv) with 11%uint63 in X. rewrite E11 in X. cbn [xv_val] in X. rewrite X.
    rewrite (same_addr_sound ρ _ _ _ _ _ Hsat Ets). unfold smod. rewrite teval_app. fold (sp_val ρ). unfold t_ae. cbn [teval].
    rewrite wZ_wofZ, (Z.mod_small 185) by (unfold two64; lia).
    rewrite bv_add_unsigned, Hupn. change (bv_unsigned (Z_to_bv 64 1)) with 1.
    rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold PN; lia).
    rewrite Z.mod_small by (unfold two64, PN; lia). unfold PN. lia. }
  assert (H12 : rg ms 12%bv = Z_to_bv 64 47).
  { apply word_lit_w. pose proof (Hregs 12%bv) as X. change (ri 12%bv) with 12%uint63 in X. rewrite E12 in X. cbn [xv_val] in X. rewrite X. exact Esl. }
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).
  assert (Hvc : xv_val ρ (XL c) cell) by exact Hcell.

  assert (Hst : forall m', (forall x : word, ~ (bv_unsigned cell <= bv_unsigned x < bv_unsigned cell + 8) -> m' x = ms_mem ms x) ->
            mem_grows (ms_mem ms) m' -> RMem segs ρ mem' m').
  { intros m' Hfr Hg. apply (a_store_BT_havoc segs ρ (a_mem A) mem' (ms_mem ms) m' (XL c) cell 8 Hmem Hvc ltac:(lia) ltac:(lia) Est); assumption. }
  assert (Hok8 : store_ok segs (ms_mem ms) cell 8 = true).
  { pose proof (a_store_sound_gen segs ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms) (XL c) cell (repeat BT 8) Hmem Hvc
                  ltac:(rewrite repeat_length; lia) ltac:(rewrite repeat_length; lia) Est ltac:(intros; reflexivity)) as X.
    rewrite repeat_length in X. apply X. intros i Hi. right. split; [reflexivity | apply nth_repeat]. }
  assert (Hsf : Forall2 same_fields (a_mem A) mem') by exact (a_store_fields segs _ _ _ _ Est).
  apply (prog_sum segs cfg b HW ms model (KT ρ o') pn cell bs Hsvc).
  - rewrite Hpc. unfold wbv, pcw. f_equal. unfold b. lia.
  - exact Hh.
  - reflexivity.
  - exact H11.
  - exact H12.
  - exact Hcstr.
  - rewrite Hupn. unfold PN. lia.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop, Hupn. unfold PN. lia.
  - exact Hok8.
  - rewrite Hcell. lia.
  - rewrite Hcell. exact (no_lazy_img segs Hlow model (wZ c) 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) Eseg).
  - left. rewrite Hcell, Hupn. unfold PN. lia.
  - intros ms' (F1 & F2 & F3 & F4 & F5 & F6) Hpc' H11' H13' Hm'.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model) _ o' Ho).
    assert (Hb20 : 0 <= b + 20 < 2 ^ 64) by (pose proof (wZ_range (a_pc A)); unfold b, two64 in *; lia).

    assert (Hmem' : RMem segs ρ mem' (ms_mem ms') /\ hs_ok ρ mem' (ms_mem ms') /\ mem_cov segs model (ms_mem ms')
                    /\ na_ok segs ρ mem' model (ms_mem ms')).
    { unfold prog_mem in Hm'. destruct (pn_off bs =? 0)%nat.
      - split; [apply (RMem_pw segs ρ mem' (ms_mem ms) _ Hm'); apply Hst; [intros; reflexivity | apply mem_grows_refl]|].
        split; [apply (hs_ok_pw ρ mem' (ms_mem ms) _ Hm'); exact (hs_ok_geom ρ _ _ _ Hsf Hhs)|].
        split; [exact (mem_cov_pw segs model _ _ Hm' Hcov)|].
        apply (na_ok_pw segs ρ mem' model (ms_mem ms) _ Hm'). exact (na_ok_geom segs ρ _ _ model _ Hsf Hnaok).
      - set (w := store_bytes SZ8 (pn + Z_to_bv 64 (Z.of_nat (pn_off bs)))%bv) in *.
        assert (Hlw : length w = 8%nat) by reflexivity.
        assert (Hout : forall x : word, ~ (bv_unsigned cell <= bv_unsigned x < bv_unsigned cell + 8) -> write_to_mem (ms_mem ms) cell w x = ms_mem ms x).
        { intros x Hx. apply write_outside; rewrite Hlw; [rewrite Hcell; unfold two64; lia | exact Hx]. }
        split; [apply (RMem_pw segs ρ mem' (write_to_mem (ms_mem ms) cell w) _ Hm'); apply Hst; [exact Hout | apply write_to_mem_grows]|].
        split.
        { apply (hs_ok_pw ρ mem' (write_to_mem (ms_mem ms) cell w) _ Hm'). apply (hs_ok_out ρ (a_mem A) mem' (ms_mem ms) _ Hsf); [|exact Hhs].
          intros z Hz. apply Hout. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hz. rewrite u_wz by lia. rewrite Hcell. lia. }
        split; [apply (mem_cov_pw segs model (write_to_mem (ms_mem ms) cell w) _ Hm'); apply mem_cov_write; [exact Hcov | rewrite Hlw; exact Hok8]|].
        apply (na_ok_pw segs ρ mem' model (write_to_mem (ms_mem ms) cell w) _ Hm'). apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
        apply na_ok_write; [exact Hnaok | rewrite Hlw; exact Hok8]. }
    destruct Hmem' as (M1 & M2 & M3 & M4).
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. rewrite wbv_wofZ by exact Hb20. reflexivity.
    + exact Epc.
    + exact F1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' [11%bv; 13%bv] Hregs F6).
      * intros r Hr. change 13%uint63 with (ri 13%bv). change 11%uint63 with (ri 11%bv).
        rewrite aget_aset_other by (intros E; apply Hr; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr; left; apply bv_eq; exact E). reflexivity.
      * intros r [<-|[<-|[]]].
        -- change 13%uint63 with (ri 13%bv). change 11%uint63 with (ri 11%bv).
           rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_same by (vm_compute; discriminate).
           cbn [xv_val]. rewrite H11'. rewrite bv_add_unsigned, Hupn, Z_to_bv_unsigned.
           unfold smod. change ((v_x0, 16) :: (v_x1, 64) :: (v_x2, 4096) :: (v_x3, 32768) :: t_ae0) with (sp_terms ++ t_ae0).
           rewrite teval_app. fold (sp_val ρ). unfold t_ae0. cbn [teval]. rewrite wZ_wofZ.
           rewrite (bv_wrap_small 64 (Z.of_nat (length bs) + 1)) by (change (bv_modulus 64) with (2 ^ 64); lia).
           unfold bv_wrap. change (bv_modulus 64) with two64. rewrite (Z.mod_small 185) by (unfold two64; lia). f_equal. unfold PN. lia.
        -- change 13%uint63 with (ri 13%bv). rewrite aget_aset_same by (vm_compute; discriminate). cbn [xv_val]. rewrite H13'. reflexivity.
    + destruct (a_resv A); cbn [resv_drop RResv] in *; try exact I. destruct F5 as [X|X]; rewrite X; [exact Hres | reflexivity].
    + exact F2.
    + exact M1.
    + exact M2.
    + exact M3.
    + exact (comp_inv_geom segs ρ _ _ model Hsf Hcomp).
    + exact M4.
    + reflexivity.
    + exact Hsat.
    + left. split; [reflexivity | lia].
Qed.

End ProgSound.
