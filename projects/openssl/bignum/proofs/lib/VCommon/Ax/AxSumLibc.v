(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reserved ledger, the CONFIG_RSEQ flag and the new auxv layout). *)

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

Lemma eb_of_R (segs : list Segment) (ρ : valuation) (A : list region) (m : word -> option byte) (r : bool) (ph : PhdrInfo) :
  RMem segs ρ A m -> find_entry A = Some (r, ph) -> exists nR, eb_rel r ph ρ m (sp_val ρ) nR.
Proof.
  intros [_ HR] Hf. destruct (find_entry_spec A r ph Hf) as [R [HIn Hk]].
  rewrite Forall_forall in HR. specialize (HR R HIn). unfold RRegion in HR. rewrite Hk in HR.
  exists (to_Z (rg_n R)). pose proof (eb_rel_base r ph ρ m _ _ HR) as Eb. rewrite Eb in HR. exact HR.
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

Lemma eb_span (r : bool) (ph : PhdrInfo) (ρ : valuation) : eb_facts r ρ ->
  sp_window_lo <= sp_val ρ /\ sp_val ρ + (AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + ρ v_ta + ρ v_te + ρ v_xl + 9) <= sp_window_hi
  /\ Z.of_nat (length (eb_image r ph ρ)) = AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + ρ v_ta + ρ v_te + ρ v_xl + 9.
Proof.
  (* TWO corrections here, both measured.
     (1) `facts_win r (mkPhdrInfo 0 0 0) ρ HF` WAS on the next line.  bndiv writes `_`
         and lets Coq infer; bignum's facts_win does not determine it
         ("Cannot infer this placeholder of type
         PhdrInfo"), so the argument is named, and the name that makes HL and H2 speak
         about the same PhdrInfo is this lemma's own ph.
     (2) THE lia FAILURE ITSELF was not the PhdrInfo: it survived the ph fix
         (still at this line).  `unfold dec_top, str_off`
         leaves H2 carrying `24 + Z.of_nat (auxv_size r)` while the GOAL carries
         `AUX_OFF r`, and AUX_OFF is a Definition (AsanWEbLoad.v:33), so lia sees two
         unrelated atoms and cannot find the witness.  Unfolding it in the goal makes
         both sides the same term.  Nothing about the auxv size is assumed: AUX_OFF is
         `24 + Z.of_nat (auxv_size r)` whatever auxv_size is at this revision. *)
  intros HF. pose proof (R7_length r ph ρ HF) as HL. pose proof (facts_win r ph ρ HF) as [H1 H2].
  unfold dec_top, str_off in H2. unfold AUX_OFF in *. split; [exact H1|]. split; [lia | lia].
Qed.

Definition t_a : terms := [(v_argc, 8)].

Definition sum_envp (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  match aget (a_regs A) 9%uint63, find_entry (a_mem A) with
  | XS ts o, Some (r, ph) =>
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
  destruct (find_entry (a_mem A)) as [[r ph]|] eqn:Efe; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A)) ENVP_WORDS) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (same_addr (a_facts A) ts o (sp_terms ++ t_a) (wofZ 16)) eqn:Ets; [|discriminate].
  destruct (pc_ok (wofZ (wZ (a_pc A) + 12))) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) r ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts r ph ρ _ _ _ Heb) as HF. pose proof (eb_span r ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & _). unfold sp_window_lo, sp_window_hi in *.
  assert (Hq0 : 0 <= ρ v_te /\ 0 <= ρ v_xl /\ 0 <= ρ v_g).
  (* `(mkPhdrInfo 0 0 0)` WAS in all three PhdrInfo slots on this line, and in every
     other call of an AsanWEb section lemma below.  Each one makes the fact speak about
     a different PhdrInfo from the one HF, HL and the goal are about, which is what the
     lia failures measured (in one round at :58, then
     in the next at :65 once the first was fixed).  The argument that
     makes them agree is this proof's own ph, bound at :102-103. *)
  { pose proof (facts_xl r ph ρ HF). pose proof (facts_g r ph ρ HF). pose proof (facts_par r ph ρ HF).
    destruct HF as (_ & _ & _ & _ & _ & Hte & _). rewrite Hte. pose proof (total_arg_bytes_nonneg (dec_envp ρ)).
    pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia. }
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
    (* `rd_block segs ph ρ …` WAS here and put ph in the rseq flag's slot: rd_block is
       `forall segs (r : bool) ph ρ …` (AsanWEbLoad.v:513), so the call was one argument
       short.  Measured as `The term "ph" has type "PhdrInfo" while it is expected to
       have type "bool"`.  The next line's
       `R3_null r ph ρ HF` already passes both in that order. *)
    (* The SECOND side condition is rd_block's
       `z0 + Z.of_nat n <= Z.of_nat (length (eb_image r ph ρ))`, and HL gives that length
       as `AUX_OFF r + 8*argc + 8*envc + g + ta + te + xl + 9`.  Unfolding AUX_OFF is
       necessary and was not sufficient: it is a Definition (AsanWEbLoad.v:33), so lia
       saw an atom it knew no sign for and reported "Cannot find witness"
       (at chars 116-119); unfolded it reads
       `24 + Z.of_nat (auxv_size r)`, whose sign lia then has for free.  TWO linear
       facts were still missing and the same failure stayed at chars 137-140
       (measured on the farm): (a) j's bound against envc, which Hj carries in
       nat against the `set` variable k, invisible to lia until k is unfolded, and
       (b) the sign of `ρ v_ta`, which Hq0 does not cover -- it gives only te, xl and g.
       Both are derived here, by this file's own idioms (k is unfolded the same way at
       :150, and Hta0 is the assert this proof already makes at :155). *)
    assert (Hta0 : 0 <= ρ v_ta) by (destruct HF as (_ & _ & _ & _ & Hta & _); rewrite Hta; apply total_arg_bytes_nonneg).
    assert (Hjz : 8 * Z.of_nat j <= 8 * ρ v_envc) by (unfold k in Hj; lia).
    pose proof (rd_block segs r ph ρ (ms_mem ms) nR 8 (16 + 8 * ρ v_argc + 8 * Z.of_nat j) _ Heb ltac:(lia) ltac:(unfold AUX_OFF in *; lia) Ea) as Hrd.
    replace (Z.to_nat (16 + 8 * ρ v_argc + 8 * Z.of_nat j)) with (16 + 8 * Z.to_nat (ρ v_argc) + 8 * j)%nat in Hrd by lia.
    destruct (Nat.eqb_spec j k) as [Ejk|Ejk].
    + subst j. unfold k in Hrd. rewrite (R3_null r ph ρ HF) in Hrd. eexists. split; [exact Hrd|].
      rewrite bytes_le_n_to_le_8. reflexivity.
    + rewrite (R3_envp r ph ρ HF j ltac:(lia)) in Hrd. eexists. split; [exact Hrd|].
      rewrite bytes_le_n_to_le_8. apply Z.eqb_neq. rewrite Z_to_bv_unsigned.
      pose proof (Nat2Z.is_nonneg (pre j (dec_envp ρ))) as Hpre.
      assert (Hta : 0 <= ρ v_ta) by (destruct HF as (_ & _ & _ & _ & Hta & _); rewrite Hta; apply total_arg_bytes_nonneg).
      assert (Hpre2 : ρ v_ta + Z.of_nat (pre j (dec_envp ρ)) <= ρ v_ta + ρ v_te).
      { destruct HF as (_ & _ & _ & _ & Hta' & Hte' & _).
        assert (Z.of_nat (pre j (dec_envp ρ)) <= ρ v_te).
        { rewrite Hte'. rewrite total_arg_bytes_Z. apply Nat2Z.inj_le. apply pre_le_tab. }
        lia. }
      (* AUX_OFF again, from the other side.  R3_envp's address is
         `sp_val ρ + SO + ρ v_ta + Z.of_nat (pre j ev)` and SO is AsanWEb.v:528's
         `Let SO : Z := 24 + Z.of_nat (auxv_size r) + 8*argc + 8*envc + g`, i.e. the
         UNFOLDED form, while Hs2 from eb_span carries the folded `AUX_OFF r`.  The two
         are the same number and lia saw two atoms: "Cannot find witness" at chars
         70-73, the `by` side condition of bv_wrap_small.
         Unfolding AUX_OFF is what makes Hs1/Hs2 bound this address; the remaining
         facts (Hpre, Hta, Hpre2, Hq0, Hargc, Henvc) are already in scope. *)
      rewrite bv_wrap_small by (unfold AUX_OFF in *; change (bv_modulus 64) with (2 ^ 64); lia). lia.
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
      (* `intros r Hr` and `intros r [...]` WERE here.  At this revision rkind's KEntry
         carries a leading rseq flag (AxMem.v:30-35), so `destruct (find_entry ...) as
         [[r ph]|]` at :101 binds `r` in this proof's context and Coq refuses the
         shadowing: "r is already used" (:190 chars
         15-16).  The binder is a register and is never used by name here; renaming it
         is the whole change. *)
      * intros rr Hr. change 10%uint63 with (ri 10%bv). change 9%uint63 with (ri 9%bv).
        rewrite aget_aset_other by (intros E; apply Hr; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr; left; apply bv_eq; exact E). reflexivity.
      * intros rr [<-|[<-|[]]].
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

Lemma eb_argv0 (segs : list Segment) (r : bool) (ph : PhdrInfo) (ρ : valuation) (m : word -> option byte) (nR : Z) :
  eb_rel r ph ρ m (sp_val ρ) nR ->
  let bs := nth 0 (dec_argv ρ) [] in
  cstr segs m (Z_to_bv 64 (sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g)) bs /\ Z.of_nat (length bs) = ρ (lenvar 0)
  /\ ρ (lenvar 0) + 1 <= ρ v_ta.
Proof.
  intros Heb bs. pose proof (eb_rel_facts r ph ρ _ _ _ Heb) as HF. pose proof (eb_span r ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & Hstr & _). destruct (Hstr 0 ltac:(lia)) as [Hl0 Hb0].
  assert (Hq : ρ (lenvar 0) + 1 <= ρ v_ta).
  { pose proof HF as (_ & _ & _ & _ & Hta & Hte & _).
    assert (ρ (lenvar 0) + 1 <= ρ v_ta).
    { rewrite Hta. pose proof (len_k r ph ρ HF 0 ltac:(lia)) as L0. change (Z.to_nat 0) with 0%nat in L0. rewrite <- L0.
      (* `a0 r` WAS the pattern: the rseq flag `r` from find_entry shadows here too.
         Measured on the farm, chars 37-38. *)
      destruct (dec_argv ρ) as [|a0 av'] eqn:Ed; [exfalso; pose proof (len_av r ph ρ HF) as X; rewrite Ed in X; cbn in X; lia|].
      cbn [nth]. unfold total_arg_bytes. cbn [fold_right]. pose proof (total_arg_bytes_nonneg av') as X. unfold total_arg_bytes in X. lia. }
    lia. }
  assert (Hlen : Z.of_nat (length bs) = ρ (lenvar 0)) by (exact (len_k r ph ρ HF 0 ltac:(lia))).
  (* rdn_of_nth's `0 <= a` is over sp_val + AUX_OFF r + 8*argc + 8*envc + g, and the
     sign of `ρ v_g` is the one summand this proof never put in context: HF is
     destructed here only as (Hargc & Henvc & Hstr & _).  Derived the way
     sum_envp_sound's Hq0 derives it at :118-120, from facts_g and facts_par with
     mod_pos_bound; nothing new is assumed. *)
  assert (Hg0 : 0 <= ρ v_g).
  { pose proof (facts_g r ph ρ HF). pose proof (facts_par r ph ρ HF).
    pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia. }
  (* The SECOND side condition, `a + length (bs ++ [0]) <= 2 ^ 64`, travels through
     Hs2's `... + ta + te + xl + 9 <= sp_window_hi` with Hq (lenvar 0 + 1 <= ta), so
     it needs te and xl non-negative as well -- the same three summands Hq0 supplies
     in sum_envp_sound and that this proof's `(Hargc & Henvc & Hstr & _)` drops.
     Measured at chars 105-108. *)
  assert (Hte0 : 0 <= ρ v_te)
    by (pose proof HF as (_ & _ & _ & _ & _ & Hte & _); rewrite Hte; apply total_arg_bytes_nonneg).
  assert (Hxl0 : 0 <= ρ v_xl) by (pose proof (facts_xl r ph ρ HF); lia).
  unfold sp_window_lo, sp_window_hi in *.
  split; [|split; [exact Hlen | exact Hq]]. split.
  - replace (S (length bs)) with (length (bs ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn [length]; lia).
    (* Both of rdn_of_nth's arithmetic side conditions are over
       `sp_val ρ + AUX_OFF r + 8*argc + 8*envc + g`, which HL and Hs2 bound using the
       Definition AUX_OFF: lia sees an atom and says "Cannot find witness"
       (one farm round at the first, the next after it, with the
       sign of v_g still missing).  The unfold is scoped to these two subgoals because
       Hbyte below is built with AUX_OFF folded and `rewrite Hbyte` has to match. *)
    apply rdn_of_nth; [unfold AUX_OFF in *; lia | rewrite length_app; cbn [length]; unfold AUX_OFF in *; lia |].
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    (* Every remaining side condition of this proof is an offset bound against the
       eb_image length, which HL states with the Definition AUX_OFF, so each one needs
       the same unfold; they are strengthened together rather than one farm round at a
       time.  Each unfold is scoped to its own side goal, so the MAIN goal keeps
       AUX_OFF folded and `rewrite Hbyte` below still matches
       (a farm round named :280 chars 116-119). *)
    pose proof (eb_rel_byte ph ρ m _ _ Heb (AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + Z.of_nat j) ltac:(unfold AUX_OFF in *; lia)) as Hbyte.
    replace (sp_val ρ + (AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + Z.of_nat j)) with (sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + Z.of_nat j) in Hbyte by lia.
    (* R5_str0's left-hand side indexes eb_image with AsanWEb's Let SO (:528), i.e.
       `24 + Z.of_nat (auxv_size r) + ...` ALREADY UNFOLDED, while the goal carries
       AUX_OFF folded: "Found no subterm matching" with exactly that index printed
       (:288 chars 28-101).  Hbyte has been consumed by
       the rewrite above, so the goal can be unfolded here without breaking it. *)
    rewrite Hbyte. f_equal. unfold AUX_OFF in *.
    rewrite (R5_str0 r ph ρ HF (Z.of_nat j) ltac:(lia)).
    destruct (Z.ltb_spec (Z.of_nat j) (ρ (lenvar 0))) as [L|L].
    + rewrite app_nth1 by lia. pose proof (nth_k r ph ρ HF 0 (Z.of_nat j) ltac:(unfold AUX_OFF in *; lia) ltac:(unfold AUX_OFF in *; lia)) as Hn.
      change (Z.to_nat 0) with 0%nat in Hn. rewrite Nat2Z.id in Hn. symmetry. exact Hn.
    + rewrite app_nth2 by lia. replace (j - length bs)%nat with 0%nat by lia. reflexivity.
  - intros x Hx. apply (In_nth _ _ (Z_to_bv 8 0)) in Hx as [j [Hj <-]].
    pose proof (nth_k r ph ρ HF 0 (Z.of_nat j) ltac:(unfold AUX_OFF in *; lia) ltac:(unfold AUX_OFF in *; lia)) as Hn. change (Z.to_nat 0) with 0%nat in Hn. rewrite Nat2Z.id in Hn.
    fold bs in Hn. rewrite Hn. destruct (Hb0 (Z.of_nat j) ltac:(lia)) as [B1 B2].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 8) with 256; lia). lia.
Qed.

Definition resv_drop (r : rsv) : rsv := match r with RNone => RNone | _ => RUnk end.

Definition sum_prog (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) - 8 in
  match aget (a_regs A) 10%uint63, aget (a_regs A) 11%uint63, aget (a_regs A) 12%uint63, find_entry (a_mem A) with
  | XL c, XS ts o, XL sl, Some (r, ph) =>
      if words_ok_f segs b PROG_WORDS &&& same_addr (a_facts A) ts o (sp_terms ++ t_aeg) (wofZ (AUX_OFF r + 1)) &&& (wZ sl =? 47) &&& pc_ok (wofZ (b + 20))
         &&& atop_is_sp (a_model A) &&& in_seg segs (wZ c) &&& (0 <=? b)
      then match a_store segs (a_mem A) (XL c) (repeat BT 8) with
           | Some mem' =>
               Some [AS (wofZ (b + 20)) (aset (aset (a_regs A) 11%uint63 (XS (sp_terms ++ t_aeg0) (wofZ (AUX_OFF r + 1)))) 13%uint63 (XL w_zero))
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
(* NEW, as in AxDisp's Main section: no_lazy_img gained this discriminant
   (AxSum.v:216) when segments_reserved began filtering seg_kernel_map
   (LPS@75d69e00 Run.v:253-254).  Without it a farm round reports
   `"model" has type "Model"` at :423 below, the round's sole error. *)
Hypothesis Hnk : forallb (fun s => negb (seg_kernel_map s)) segs = true.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_prog_sound (A : AST) (l : list AST) : sum_prog segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_prog in Hs.
  destruct (aget (a_regs A) 10%uint63) as [c| | | | |] eqn:E10; try discriminate.
  destruct (aget (a_regs A) 11%uint63) as [| ts o | | | |] eqn:E11; try discriminate.
  destruct (aget (a_regs A) 12%uint63) as [sl| | | | |] eqn:E12; try discriminate.
  destruct (find_entry (a_mem A)) as [[r ph]|] eqn:Efe; [|discriminate].
  destruct (words_ok_f segs (wZ (a_pc A) - 8) PROG_WORDS) eqn:HW; [|discriminate]. apply words_ok_f_eq in HW.
  destruct (same_addr (a_facts A) ts o (sp_terms ++ t_aeg) (wofZ (AUX_OFF r + 1))) eqn:Ets; [|discriminate].
  destruct (wZ sl =? 47) eqn:Esl; [|discriminate]. apply Z.eqb_eq in Esl.
  destruct (pc_ok (wofZ (wZ (a_pc A) - 8 + 20))) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (in_seg segs (wZ c)) eqn:Eseg; [|discriminate].
  destruct (0 <=? wZ (a_pc A) - 8) eqn:Eb0; [|discriminate]. apply Z.leb_le in Eb0.
  destruct (a_store segs (a_mem A) (XL c) (repeat BT 8)) as [mem'|] eqn:Est; [|discriminate]. injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A) - 8) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) r ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts r ph ρ _ _ _ Heb) as HF. pose proof (eb_span r ph ρ HF) as (Hs1 & Hs2 & HL).
  pose proof HF as (Hargc & Henvc & _). unfold sp_window_lo, sp_window_hi in *.
  (* This proof bounds addresses of the form sp_val + AUX_OFF r + 8*argc + 8*envc + g
     against Hs1/Hs2, and its `(Hargc & Henvc & _)` above leaves lia without the sign
     of four of those summands and without any sign for AUX_OFF, which is a Definition
     and therefore an atom: "Cannot find witness" at :357 chars 149-152
     (measured on the farm).  Giving lia the ATOM'S SIGN is enough here and is
     better than unfolding, because Hs1/Hs2/HL all speak in AUX_OFF and the rewrites
     further down match the folded form.  Nothing about the auxv size is assumed:
     AUX_OFF is 24 + Z.of_nat (auxv_size r) whatever auxv_size is. *)
  assert (HA0 : 0 <= AUX_OFF r) by (unfold AUX_OFF; lia).
  assert (Hg0 : 0 <= ρ v_g).
  { pose proof (facts_g r ph ρ HF). pose proof (facts_par r ph ρ HF).
    pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia. }
  assert (Hta0 : 0 <= ρ v_ta)
    by (pose proof HF as (_ & _ & _ & _ & Hta & _); rewrite Hta; apply total_arg_bytes_nonneg).
  assert (Hte0 : 0 <= ρ v_te)
    by (pose proof HF as (_ & _ & _ & _ & _ & Hte & _); rewrite Hte; apply total_arg_bytes_nonneg).
  assert (Hxl0 : 0 <= ρ v_xl) by (pose proof (facts_xl r ph ρ HF); lia).
  destruct (eb_argv0 segs r ph ρ (ms_mem ms) nR Heb) as (Hcstr & Hlen & Hq0). set (bs := nth 0 (dec_argv ρ) []) in *.
  assert (Hl0 : 0 <= ρ (lenvar 0)) by lia.
  set (PN := sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g) in *.
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
    rewrite (same_addr_sound ρ _ _ _ _ _ Hsat Ets). unfold smod. rewrite teval_app. fold (sp_val ρ). unfold t_aeg. cbn [teval].
    (* `(Z.mod_small 489)` WAS here.  489 is `AUX_OFF r + 1` for the OLD ten-pair auxv
       table (24 + 464 + 1); at this revision the auxv size depends on the launch's
       rseq flag, and sum_prog's own check at :341 already writes the offset
       parametrically as `wofZ (AUX_OFF r + 1)`, so the goal carries that term and the
       literal matches nothing: "Found no subterm matching 489 mod ?M"
       (:384 chars 4-61).  Naming the same parametric
       term REMOVES a pin rather than adding one; no auxv size is assumed, and HA0
       above is what discharges the side condition. *)
    (* `unfold AUX_OFF` gives lia only `0 <= Z.of_nat (auxv_size r)` and no UPPER bound,
       so `AUX_OFF r + 1 < two64` is still out of reach: "Cannot find witness" at chars
       78-81.  AUX_OFF_rng (AsanWEbLoad.v:35) is the
       bound, and is what AxSumStr's already-ported sibling branch uses. *)
    rewrite wZ_wofZ, (Z.mod_small (AUX_OFF r + 1)) by (pose proof (AUX_OFF_rng r); unfold two64; lia).
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
  - rewrite Hcell. exact (no_lazy_img segs Hlow Hnk model (wZ c) 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) Eseg).
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
      (* Same rseq shadowing as at :196; the binder is a register, never used by name. *)
      * intros rr Hr. change 13%uint63 with (ri 13%bv). change 11%uint63 with (ri 11%bv).
        rewrite aget_aset_other by (intros E; apply Hr; right; left; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply Hr; left; apply bv_eq; exact E). reflexivity.
      * intros rr [<-|[<-|[]]].
        -- change 13%uint63 with (ri 13%bv). change 11%uint63 with (ri 11%bv).
           rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_same by (vm_compute; discriminate).
           cbn [xv_val]. rewrite H11'. rewrite bv_add_unsigned, Hupn, Z_to_bv_unsigned.
           unfold smod. change ((v_x0, 16) :: (v_x1, 64) :: (v_x2, 4096) :: (v_x3, 32768) :: t_aeg0) with (sp_terms ++ t_aeg0).
           rewrite teval_app. fold (sp_val ρ). unfold t_aeg0. cbn [teval]. rewrite wZ_wofZ.
           rewrite (bv_wrap_small 64 (Z.of_nat (length bs) + 1)) by (change (bv_modulus 64) with (2 ^ 64); lia).
           (* Second `(Z.mod_small 489)` of this proof; same pin, same parametric cure
              as :392, discharged from HA0 and AUX_OFF's own body. *)
           unfold bv_wrap. change (bv_modulus 64) with two64. rewrite (Z.mod_small (AUX_OFF r + 1)) by (pose proof (AUX_OFF_rng r); unfold two64; lia). f_equal. unfold PN. lia.
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
