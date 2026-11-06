(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require SeqExec.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep BootLayout.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie AxTabs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLin AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoinSound AxRunSound AxAcct AxGrant AsanWLazy AsanWBase AsanSBase AsanWMemcpy AsanWMemcpyF1 AsanWMemcpyF3 AxSum AxEntryRel AxEntryAg AsanSWord AsanSRipA AsanSMat AsanSRipC AxScan AxForget AxRel AxLazy AsanWMat AsanWMcM3 AxRng.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr AxSumMem AxSumRip2.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxChain.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition src_in (A : list region) (v : xv) (n : Z) : bool :=
  match xaddr v with
  | Some (ts, o) => match find_reg A ts o (of_Z n) 0 with
                    | Some _ => true
                    | None => has_mark A &&& (wZ o + n <? 9223372036854775808) &&& chain_ge (length A) ts A (wZ o) (wZ o + n)
                    end
  | None => false
  end.

Section Src.
Variable segs : list Segment.

Lemma rdn_exists (m : word -> option byte) : forall (k : nat) (a : Z),
  (forall j, (j < k)%nat -> exists b, rv segs m (wz (a + Z.of_nat j)) = Some b) -> exists bs, rdn segs m (wz a) k = Some bs.
Proof.
  induction k as [|k IH]; intros a H; [exists []; reflexivity|].
  destruct (H 0%nat ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
  destruct (IH (a + 1) ltac:(intros j Hj; destruct (H (S j) ltac:(lia)) as [b' Hb']; exists b'; replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia; exact Hb'))
    as [bs Hbs].
  exists (b :: bs). cbn [rdn]. unfold rv in Hb. rewrite Hb. rewrite wz_succ, Hbs. reflexivity.
Qed.

Lemma src_in_rdn (ρ : valuation) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (nhi : Z) :
  RMem segs ρ A m -> xv_val ρ v a -> 1 <= nhi < 2 ^ 40 -> src_in A v nhi = true ->
  forall k, 0 <= k <= nhi -> exists bs, rdn segs m a (Z.to_nat k) = Some bs.
Proof.
  intros [Hok HR] Hv Hn H k Hk. unfold src_in in H. destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z nhi) 0) as [[[i R] x]|] eqn:Ef.
  2: { (* [comment removed for export] *)
    apply land_true in H as [H Hch]. apply land_true in H as [_ H63]. apply Z.ltb_lt in H63.
    assert (Hav : bv_unsigned a = smod ρ ts o).
    { destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
      - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
      - exact Hv. }
    replace a with (wz (bv_unsigned a)) by (apply bv_eq; rewrite u_wz; [reflexivity | pose proof (bv_unsigned_in_range 64 a) as X; change (bv_modulus 64) with 18446744073709551616 in X; lia]).
    apply rdn_exists. intros j Hj.
    destruct (chain_ge_cover _ _ _ _ _ Hch (wZ o + Z.of_nat j) ltac:(pose proof (wZ_range o); lia)) as [R' (HR' & Ets & Hw & Hk')].
    pose proof (regions_ok_in ρ A R' Hok HR') as Hwf'. pose proof (proj1 (Forall_forall _ _) HR R' HR') as HRR'.
    rewrite (RRegion_ne segs ρ m R' (anon_not_entry R' Hk')) in HRR'.
    set (y := wZ o + Z.of_nat j - wZ (rg_bo R')) in *.
    pose proof Hwf' as [Hw1 [H47' _]]. pose proof (wZ_range o) as Hor. pose proof (wZ_range (rg_bo R')) as Hbr.
    assert (Hyz : to_Z (of_Z y) = y) by (apply phi_of_Z_n; unfold y; lia).
    destruct (HRR' (of_Z y) ltac:(rewrite Hyz; unfold y; lia)) as [[b [Hb _]] _]. rewrite Hyz in Hb. exists b.
    replace (wz (bv_unsigned a + Z.of_nat j)) with (wz (rbase ρ R' + y)); [exact Hb|].
    apply bv_eq. unfold wz. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
    rewrite Hav. unfold rbase, smod. rewrite Ets. unfold y.
    rewrite Zplus_mod_idemp_l. rewrite (Zplus_mod_idemp_l (teval ρ ts + wZ o)). f_equal. lia. }
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  pose proof (roff_ne R ts o _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R Hne0) in HRR.
  assert (Hav : bv_unsigned a = smod ρ ts o).
  { destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
    - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
    - exact Hv. }
  assert (Hnz : to_Z (of_Z nhi) = nhi) by (apply phi_of_Z_n; lia).
  destruct (roff_addr ρ R ts o (of_Z nhi) x a ltac:(rewrite Hnz; lia) Hwf Hav Hr) as [Eaddr Hfit]. rewrite Hnz in Hfit.
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  pose proof Hwf as [Hw1 [H47 _]]. pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hsr. fold (rbase ρ R) in Hsr.
  assert (Ha : a = wz (rbase ρ R + to_Z x)) by (apply bv_eq; rewrite u_wz; [lia | unfold two64 in *; lia]). rewrite Ha.
  apply rdn_exists. intros j Hj.
  assert (Hjx : to_Z (of_Z (to_Z x + Z.of_nat j)) = to_Z x + Z.of_nat j) by (apply phi_of_Z_n; lia).
  destruct (HRR (of_Z (to_Z x + Z.of_nat j)) ltac:(rewrite Hjx; lia)) as [[b [Hb _]] _]. rewrite Hjx, Z.add_assoc in Hb.
  exists b. exact Hb.
Qed.

End Src.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_BT (x : xb) : bool := match x with BT => true | _ => false end.

Definition mcb_mem (segs : list Segment) (s : store) (A : list region) (d sv : xv) (nlo nhi : Z) : option (list region) :=
  if nhi =? 0 then Some A else
  match a_forget segs A d nhi with
  | Some M1 =>
      if 2 <=? nlo then
        match a_load4 segs s A sv 2 with
        | Some [x0; x1] => if negb (is_BT x0 && is_BT x1) then a_store segs M1 d [x0; x1] else Some M1
        | _ => Some M1
        end
      else Some M1
  | None => None
  end.

Definition sum_memcpy_big_g (ckM : (list Segment -> Z -> bool)) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let e := wZ (a_pc A) in
  let s := a_facts A in
  let d := aget (a_regs A) 10%uint63 in
  let sv := aget (a_regs A) 11%uint63 in
  match xrange s (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, xaddr d, xaddr sv with
  | Some (nlo, nhi), XL r, Some (td, od), Some (tsr, osr) =>
      if (0 <=? nlo) &&& (0 <=? nhi) &&& (nhi <=? 67108864) &&& ckM segs e &&& (wZ r mod 4 =? 0) &&& (wZ r <? 2 ^ 26)
         &&& rbetween 2 s (wS od, td) 0 (2 ^ 47 - nhi) &&& rbetween 2 s (wS osr, tsr) 0 (2 ^ 47 - nhi)
         &&& disj_ok s (wS od, td) (wS osr, tsr) nhi &&& ((nhi =? 0) ||| src_in (a_mem A) sv nhi)
         &&& (a_budget A + 4096 * mc_pages nhi <=? LIM) then
        match mcb_mem segs s (a_mem A) d sv nlo nhi with
        | Some mem' => Some [AS (wofZ (wZ r)) (clob MCF_CLOB' (a_regs A)) (match a_resv A with RNone => RNone | _ => RUnk end)
                                mem' s (a_model A) (a_budget A + 4096 * mc_pages nhi) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _ => None
  end.

Definition sum_memcpy_big (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_memcpy_big_g mc_code_ok segs LIM A.

Lemma sum_memcpy_big_g_ck (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  mc_code_ok segs (wZ (a_pc A)) = true -> sum_memcpy_big_g ck_true1 segs LIM A = Some l -> sum_memcpy_big segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_memcpy_big, sum_memcpy_big_g in *. cbv zeta in *. unfold ck_true1 in H. rewrite Hck. exact H.
Qed.

Section McbSound.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

Lemma copied_grows (m' m : word -> option byte) (lo k : Z) (bs : list byte) : copied m' m lo k bs -> mem_grows m m'.
Proof.
  intros H y Hy. destruct (H y) as [H1 H2].
  destruct (Z_lt_le_dec (bv_unsigned y) lo) as [L|L]; [rewrite (H2 ltac:(lia)); exact Hy|].
  destruct (Z_lt_le_dec (bv_unsigned y) (lo + k)) as [L2|L2]; [rewrite (H1 ltac:(lia)); discriminate | rewrite (H2 ltac:(lia)); exact Hy].
Qed.

Lemma mcb_mem_sound (ρ : valuation) (s : store) (A M : list region) (m m' : word -> option byte) (d sv : xv) (dst src : bv 64)
    (nlo nhi n : Z) (bs : list byte) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ d dst -> xv_val ρ sv src ->
  mcb_mem segs s A d sv nlo nhi = Some M -> nlo <= n <= nhi -> 0 <= n -> bv_unsigned dst + nhi <= two64 ->
  rdn segs m src (Z.to_nat n) = Some bs -> copied m' m (bv_unsigned dst) n bs ->
  RMem segs ρ M m' /\ ((nhi = 0 /\ M = A) \/ exists M1, a_forget segs A d nhi = Some M1 /\ Forall2 same_fields M1 M).
Proof.
  intros Hs HM Hhs Hvd Hvs H Hn Hn0 Hd64 Hrd Hcp. unfold mcb_mem in H.
  destruct (nhi =? 0) eqn:Enz.
  { (* [comment removed for export] *)
    apply Z.eqb_eq in Enz. injection H as <-. split; [|left; split; [exact Enz | reflexivity]].
    apply (RMem_pw segs ρ A m m'); [|exact HM]. intros x. apply (proj2 (Hcp x)). lia. }
  destruct (a_forget segs A d nhi) as [M1|] eqn:Ef; [|discriminate].
  assert (HM1 : RMem segs ρ M1 m').
  { apply (a_forget_sound segs ρ A M1 m m' d dst nhi HM Hvd Ef); [|exact (copied_grows m' m _ _ _ Hcp)].
    intros x Hx. apply (proj2 (Hcp x)). lia. }
  destruct (2 <=? nlo) eqn:E2.
  - apply Z.leb_le in E2.
    destruct (a_load4 segs s A sv 2) as [[|x0 [|x1 [|x2 r]]]|] eqn:El;
      try (injection H as <-; split; [exact HM1 | right; exists M1; split; [reflexivity | apply Forall2_same_refl]]).
    destruct (negb (is_BT x0 && is_BT x1)) eqn:Enb; [|injection H as <-; split; [exact HM1 | right; exists M1; split; [reflexivity | apply Forall2_same_refl]]].
    destruct (a_load4_sound segs ρ s A m sv src 2 [x0; x1] Hlow Hs HM Hhs Hvs ltac:(lia) El) as [bs2 [Hrd2 HF2]].
    pose proof (SeqExec.rdn_firstn segs m (Z.to_nat n) src bs 2 Hrd ltac:(lia)) as Hrd2'. rewrite Hrd2 in Hrd2'. injection Hrd2' as Ebs2.
    pose proof (Forall2_length HF2) as Hl2. cbn [length] in Hl2.
    assert (Hbl : (2 <= length bs)%nat) by (pose proof (rdn_length segs m (Z.to_nat n) src bs Hrd); lia).
    split; [|right; exists M1; split; [reflexivity | exact (a_store_fields segs _ _ _ _ H)]].
    refine (proj2 (a_store_gen_sound segs ρ M1 M m' m' d dst [x0; x1] HM1 Hvd ltac:(cbn; lia) ltac:(cbn; lia) H _ _)).
    + intros x _. reflexivity.
    + intros i Hi. cbn [length] in Hi. left. exists (nth i bs (Z_to_bv 8 0)). split.
      * destruct (Hcp (wz (bv_unsigned dst + Z.of_nat i))) as [X1 _].
        pose proof (bvu_range dst). rewrite X1 by (rewrite u_wz by (unfold two64 in *; lia); lia).
        rewrite u_wz by (unfold two64 in *; lia). replace (Z.to_nat (bv_unsigned dst + Z.of_nat i - bv_unsigned dst)) with i by lia. reflexivity.
      * subst bs2. destruct bs as [|b0 [|b1 bs']]; try (cbn in Hbl; lia). cbn [firstn] in HF2.
        apply Forall2_cons_iff in HF2 as [Hx0 HF2']. apply Forall2_cons_iff in HF2' as [Hx1 _].
        destruct i as [|[|i]]; [exact Hx0 | exact Hx1 | lia].
  - injection H as <-. split; [exact HM1 | right; exists M1; split; [reflexivity | apply Forall2_same_refl]].
Qed.

End McbSound.

Section MemcpyBigSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Lemma addr_form_val (ρ : valuation) (v : xv) (a : bv 64) (ts : terms) (o : w64) (B : Z) :
  xv_val ρ v a -> xaddr v = Some (ts, o) -> 0 <= leval ρ (wS o, ts) <= B -> B < two64 -> bv_unsigned a = leval ρ (wS o, ts).
Proof.
  intros Hv Ea Hr HB. rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r.
  replace (teval ρ ts + wS o) with (leval ρ (wS o, ts)) by (unfold leval; cbn [fst snd]; ring). apply Z.mod_small. lia.
Qed.

Lemma mc_pages_mono (n m : Z) : 0 <= n <= m -> mc_pages n <= mc_pages m.
Proof. intros H. unfold mc_pages. assert (n / 4096 <= m / 4096) by (apply Z.div_le_mono; lia). lia. Qed.

Theorem sum_memcpy_big_sound (A : AST) (l : list AST) : sum_memcpy_big segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho.
  unfold sum_memcpy_big, sum_memcpy_big_g in Hs.
  destruct (xrange (a_facts A) (aget (a_regs A) 12%uint63)) as [[nlo nhi]|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[td od]|] eqn:Ed; [|discriminate].
  destruct (xaddr (aget (a_regs A) 11%uint63)) as [[tsr osr]|] eqn:Esr; [|discriminate].
  match type of Hs with context [if ?c then _ else _] => destruct c eqn:Ec; [|discriminate] end.
  destruct (mcb_mem segs (a_facts A) (a_mem A) (aget (a_regs A) 10%uint63) (aget (a_regs A) 11%uint63) nlo nhi) as [mem'|] eqn:Emc;
    [|discriminate].
  injection Hs as <-.
  rewrite ?land_eq in Ec.
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Ec Hsrc]. apply andb_prop in Ec as [Ec Hdj]. apply andb_prop in Ec as [Ec Hrs].
  apply andb_prop in Ec as [Ec Hrd].
  apply andb_prop in Ec as [Ec Hr26]. apply andb_prop in Ec as [Ec Hr4]. apply andb_prop in Ec as [Ec Hcode].
  apply andb_prop in Ec as [Ec Hn64]. apply andb_prop in Ec as [Hn0 Hn1].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn1. apply Z.leb_le in Hn64. apply Z.ltb_lt in Hr26. apply Z.eqb_eq in Hr4. apply Z.leb_le in Hbud.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (e := wZ (a_pc A)) in *.
  set (dst := rg ms 10%bv). set (src := rg ms 11%bv). set (cnt := rg ms 12%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 10%uint63) dst) by exact (Hregs 10%bv).
  assert (Hvs : xv_val ρ (aget (a_regs A) 11%uint63) src) by exact (Hregs 11%bv).
  pose proof (xrange_sound ρ _ _ cnt Hsat (Hregs 12%bv) _ E12) as Hcr. cbn [fst snd] in Hcr.
  set (n := bv_unsigned cnt) in *.
  pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - nhi) Hsat Hrd) as Hrdv. pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - nhi) Hsat Hrs) as Hrsv.
  assert (Hdv : bv_unsigned dst = leval ρ (wS od, td)) by (apply (addr_form_val ρ _ dst td od (2 ^ 47 - nhi) Hvd Ed); [lia | unfold two64; lia]).
  assert (Hsv : bv_unsigned src = leval ρ (wS osr, tsr)) by (apply (addr_form_val ρ _ src tsr osr (2 ^ 47 - nhi) Hvs Esr); [lia | unfold two64; lia]).
  pose proof (disj_ok_sound ρ _ _ _ nhi Hsat Hdj) as Hdisj. rewrite <- Hdv, <- Hsv in Hdisj.
  assert (Hrdx : exists bs, rdn segs (ms_mem ms) src (Z.to_nat n) = Some bs).
  { destruct (nhi =? 0) eqn:Ez.
    - apply Z.eqb_eq in Ez. replace (Z.to_nat n) with O by lia. exists []. reflexivity.
    - exact (src_in_rdn segs ρ (a_mem A) (ms_mem ms) _ src nhi Hmem Hvs ltac:(lia) Hsrc n ltac:(lia)). }
  destruct Hrdx as [bs Hrd0].
  (* [comment removed for export] *)
  assert (Hdstok : store_ok segs (ms_mem ms) dst (Z.to_nat nhi) = true
                   /\ (hs_old ρ (a_mem A) (ms_mem ms) -> forall z, in_ss z -> ~ (bv_unsigned dst <= z < bv_unsigned dst + nhi))).
  { destruct (nhi =? 0) eqn:Ez.
    - apply Z.eqb_eq in Ez. rewrite Ez. split; [reflexivity | intros _ z _ X; lia].
    - assert (Ef0 : exists M1, a_forget segs (a_mem A) (aget (a_regs A) 10%uint63) nhi = Some M1).
      { unfold mcb_mem in Emc. rewrite Ez in Emc. destruct (a_forget segs (a_mem A) (aget (a_regs A) 10%uint63) nhi) as [M1|]; [exists M1; reflexivity | discriminate]. }
      destruct Ef0 as [M1 Ef].
      destruct (a_forget_range segs ρ (a_mem A) M1 (ms_mem ms) _ dst nhi Hmem Hvd Ef) as (RD & HRD & HRDs & HRD1 & HRD2 & Hstd & Hnr).
      split; [exact Hstd|]. intros Hold z Hz Hin. apply (proj1 Hold RD HRD HRDs z); [unfold in_rg; lia | exact Hz]. }
  destruct Hdstok as [Hstd Hss0].
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  pose proof (wZ_range r) as Hrr.
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  assert (Esrc : src = Z_to_bv 64 (bv_unsigned src)) by (apply word_lit_w; reflexivity).
  assert (Hok : store_ok segs (ms_mem ms) dst (Z.to_nat n) = true) by (apply (store_ok_le segs _ _ (Z.to_nat nhi)); [lia | exact Hstd]).
  pose proof (mc_pages_mono n nhi ltac:(lia)) as Hmp.
  apply (memcpy_sum_mat segs cfg e (mc_code_sound segs e Hcode) ms model (KT ρ o') (bv_unsigned dst) (bv_unsigned src) n bs Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - exact Edst.
  - exact Esrc.
  - apply word_lit_w. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite <- Esrc. exact Hrd0.
  - rewrite <- Edst. exact Hok.
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. unfold page_size. lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - (* [comment removed for export] *)
    intros ms' model' HMC Hcp Hpc' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMC as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused]. subst model'.
    destruct (model_backing_fields model pages) as [MH ML].
    assert (Er : wZ (wofZ (wZ r)) = wZ r) by (rewrite wZ_wofZ; apply Z.mod_small; exact Hrr).
    destruct (mcb_mem_sound segs Hlow ρ _ _ _ (ms_mem ms) (ms_mem ms') _ _ dst src nlo nhi n bs Hsat Hmem Hhs Hvd Hvs Emc ltac:(lia) ltac:(lia)
                ltac:(unfold two64; lia) Hrd0 Hcp) as [Hmem' Hor].
    assert (Hss : hs_old ρ (a_mem A) (ms_mem ms) -> forall z, in_ss z -> ms_mem ms' (wz z) = ms_mem ms (wz z)).
    { intros Hold z Hz. apply (proj2 (Hcp (wz z))).
      assert (Hz64 : 0 <= z < two64) by (unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia).
      rewrite u_wz by (unfold two64 in *; lia). intros Hin. apply (Hss0 Hold z Hz). lia. }
    assert (Hgeo : hs_ok ρ mem' (ms_mem ms') /\ comp_inv segs ρ mem' model /\ (na_ok segs ρ (a_mem A) model (ms_mem ms') -> na_ok segs ρ mem' model (ms_mem ms'))).
    { destruct Hor as [[_ ->]|[M1 [Ef Hsf]]].
      - split; [exact (hs_ok_out' ρ (a_mem A) (a_mem A) (ms_mem ms) (ms_mem ms') (Forall2_same_refl _) Hss Hhs)|]. split; [exact Hcomp | intros X; exact X].
      - split; [exact (hs_ok_geom ρ M1 mem' _ Hsf (hs_ok_forget' segs ρ (a_mem A) M1 (ms_mem ms) (ms_mem ms') _ nhi Hmem Ef Hss Hhs))|].
        split; [exact (comp_inv_geom segs ρ M1 mem' model Hsf (comp_inv_forget segs ρ (a_mem A) M1 model _ nhi Ef Hcomp))|].
        intros X. apply (na_ok_geom segs ρ M1 mem' model _ Hsf). exact (na_ok_forget segs ρ (a_mem A) M1 model _ _ nhi Ef X). }
    destruct Hgeo as (Hhs' & Hcomp' & Hna').
    constructor; cbn [cfg_ms cfg_model a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. rewrite Er. apply word_lit_w. exact Hra.
    + rewrite Er. split; lia.
    + exact P1.
    + apply (RRegs_clob ρ (a_regs A) ms ms' MCF_CLOB' Hregs); [rewrite <- MCF_CLOB_eq; exact P6|].
      intros r0 Hr0. unfold MCF_CLOB' in Hr0. cbn [In] in Hr0.
      destruct Hr0 as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]]]; rewrite <- X; vm_compute; discriminate.
    + destruct (a_resv A); cbn [RResv] in *; try exact I. destruct P5 as [X|X]; rewrite X; [exact Hres | reflexivity].
    + rewrite P2. exact Hrom.
    + exact Hmem'.
    + exact (MR_mat segs fs0 ρ (a_model A) model pages Hmod).
    + rewrite MH. exact Hh.
    + destruct Hb as [Hb1 Hb2]. split; [unfold page_size in Hused; lia | rewrite ML; exact Hb2].
    + exact Hsat.
    + exact Hhs'.
    + apply mem_cov_backing.
      apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hcov ltac:(lia) ltac:(unfold two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hcp x)). lia.
    + apply comp_inv_backing. exact Hcomp'.
    + apply na_ok_backing. apply Hna'.
      apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hnaok ltac:(lia) ltac:(unfold two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hcp x)). lia.
Qed.

End MemcpyBigSound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cell_zero_rng (c : cell) (lo hi : Z) : bool :=
  if (hi <? 0) ||| (7 <? lo) then true   (* [comment removed for export] *)
  else forallb (fun i => if (lo <=? Z.of_nat i) && (Z.of_nat i <=? hi) then xb_is0 (cbyte c i) else true) (seq 0 8).

Lemma cell_zero_rng_byte (c : cell) (lo hi : Z) (i : nat) :
  cell_zero_rng c lo hi = true -> (i < 8)%nat -> lo <= Z.of_nat i <= hi -> cbyte c i = BL 0%uint63.
Proof.
  intros H Hi Hr. unfold cell_zero_rng in H.
  replace ((hi <? 0) ||| (7 <? lo)) with false in H
    by (symmetry; destruct (Z.ltb_spec hi 0); [lia|]; destruct (Z.ltb_spec 7 lo); [lia | reflexivity]).
  rewrite forallb_forall in H. pose proof (H i ltac:(apply in_seq; lia)) as Y.
  replace ((lo <=? Z.of_nat i) && (Z.of_nat i <=? hi)) with true in Y
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  destruct (cbyte c i) as [b| |]; cbn [xb_is0] in Y; try discriminate. apply Uint63.eqb_spec in Y. subst b. reflexivity.
Qed.

Definition sh_zero_big (s : store) (mem : list region) (ts : terms) (o nhi : Z) : bool :=
  let f0 := o / 8 in
  let f1 := (o + nhi - 1) / 8 in
  let L := f1 - f0 + 1 in
  tdiv8_ok ts && (1 <=? L) && (L <? 1099511627776) &&
  match find_reg mem (tdiv8 ts) (wofZ (0x7fff8000 + f0)) (of_Z L) 0 with
  | Some (_, R, x) => is_shadow R && rng_all (fun k c => cell_zero_rng c (to_Z x - 8 * k) (to_Z x + L - 1 - 8 * k)) (rg_d R) (rg_cells R)
                                             (to_Z x / 8) ((to_Z x + L - 1) / 8)
  | None => false
  end.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma sh_zero_big_sound (segs : list Segment) (ρ : valuation) (s : store) (A : list region) (m : word -> option byte)
    (ts : terms) (o nhi n : Z) :
  RMem segs ρ A m -> sh_zero_big s A ts o nhi = true ->
  0 <= teval ρ ts + o -> teval ρ ts + o + nhi <= 2 ^ 47 -> 1 <= n <= nhi ->
  forall q, 0x7fff8000 + (teval ρ ts + o) / 8 <= q <= 0x7fff8000 + (teval ρ ts + o + n - 1) / 8 ->
    bat segs m (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Proof.
  intros [Hok HR] H Hb0 Hb1 Hn q Hq. unfold sh_zero_big in H. cbv zeta in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H HL2]. apply andb_prop in H as [Ht HL1].
  apply Z.leb_le in HL1. apply Z.ltb_lt in HL2.
  set (L := (o + nhi - 1) / 8 - o / 8 + 1) in *.
  destruct (find_reg A (tdiv8 ts) (wofZ (0x7fff8000 + o / 8)) (of_Z L) 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  apply andb_prop in Hf as [Hsh Hall].
  destruct (find_reg_spec A _ _ _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf. pose proof (Forall_nth _ A i R HR Hi) as HRR.
  pose proof (roff_ne R _ _ _ x Hr) as Hne0. rewrite (RRegion_ne segs ρ m R Hne0) in HRR.
  rewrite (teval_tdiv8 ρ ts Ht) in *. set (T := teval ρ (tdiv8 ts)) in *.
  assert (E0 : (8 * T + o) / 8 = T + o / 8) by (replace (8 * T + o) with (o + T * 8) by ring; rewrite Z.div_add by lia; ring).
  assert (E1 : (8 * T + o + n - 1) / 8 = T + (o + n - 1) / 8).
  { replace (8 * T + o + n - 1) with ((o + n - 1) + T * 8) by ring. rewrite Z.div_add by lia. ring. }
  assert (E1' : (8 * T + o + nhi - 1) / 8 = T + (o + nhi - 1) / 8).
  { replace (8 * T + o + nhi - 1) with ((o + nhi - 1) + T * 8) by ring. rewrite Z.div_add by lia. ring. }
  rewrite E0, E1 in Hq.
  assert (Hbeg8 : 0 <= T + o / 8) by (rewrite <- E0; apply Z.div_pos; lia).
  assert (Hend8 : T + (o + nhi - 1) / 8 < 2 ^ 44) by (rewrite <- E1'; apply Z.div_lt_upper_bound; lia).
  assert (Hmono : (o + n - 1) / 8 <= (o + nhi - 1) / 8) by (apply Z.div_le_mono; lia).
  set (a0 := Z_to_bv 64 (0x7fff8000 + (T + o / 8))).
  assert (Ha0 : bv_unsigned a0 = 0x7fff8000 + (T + o / 8)) by (apply u_wz; lia).
  assert (Hav : bv_unsigned a0 = smod ρ (tdiv8 ts) (wofZ (0x7fff8000 + o / 8))).
  { rewrite Ha0. unfold smod. fold T. rewrite wZ_wofZ, Zplus_mod_idemp_r. rewrite Z.mod_small by (unfold two64; lia). ring. }
  assert (HLz : to_Z (of_Z L) = L) by (apply phi_of_Z_n; lia).
  destruct (roff_addr ρ R _ _ (of_Z L) x a0 ltac:(rewrite HLz; lia) Hwf Hav Hr) as [Eaddr Hfit]. rewrite HLz in Hfit.
  pose proof Hwf as [Hw1 [H47 [Hd [Hd44 _]]]].
  pose proof (to_Z_bounded x) as Hxb. change wB with (2^63) in Hxb.
  assert (Hdq : 0 <= q - bv_unsigned a0 <= L - 1) by lia.
  set (y := of_Z (to_Z x + (q - bv_unsigned a0))).
  assert (Hy : to_Z y = to_Z x + (q - bv_unsigned a0)) by (apply phi_of_Z_n; lia).
  assert (HyN : to_Z y < to_Z (rg_n R)) by lia.
  destruct (HRR y HyN) as [[b [Hb Hab]] _].
  assert (Eq : rbase ρ R + to_Z y = q) by lia. rewrite Eq in Hb. unfold bat. unfold rv in Hb. unfold wz in Hb. rewrite Hb.
  f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0.
  unfold rbyte, get_cell_opt in Hab. destruct (iget (rg_d R) (rg_cells R) (y >> 3)%uint63) as [c|] eqn:Ec.
  - pose proof (key_small R y Hd HyN) as Hks.
    assert (Hkr : to_Z x / 8 <= to_Z (y >> 3)%uint63 <= (to_Z x + L - 1) / 8).
    { rewrite phi_lsr3. split; apply Z.div_le_mono; clear -Hy Hdq; lia. }
    pose proof (rng_all_iget _ (rg_d R) (rg_cells R) _ _ (y >> 3)%uint63 c Hall Hkr Hks Ec) as Hc.
    rewrite phi_lsr3 in Hks, Hc.
    assert (Hy0 : 0 <= to_Z y / 8) by (apply Z.div_pos; [clear -Hy Hdq Hxb; lia | clear; lia]).
    assert (Hym : 0 <= to_Z y mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Eyd : to_Z y = 8 * (to_Z y / 8) + to_Z y mod 8) by (apply Z.div_mod; lia).
    rewrite (cell_zero_rng_byte c _ _ _ Hc) in Hab; [exact Hab | rewrite i2n_land7, phi_land7; clear -Hym; lia |].
    rewrite i2n_land7, phi_land7, Z2Nat.id by (clear -Hym; lia).
    clear -Hy Hdq Eyd Hym. lia.
  - unfold default_byte in Hab. unfold is_shadow in Hsh. destruct (rg_kind R); try discriminate. exact Hab.
Qed.

Definition sum_rip_big_g (ckR : (list Segment -> Z -> Z -> Z -> Z -> Z -> Z -> bool)) (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  let s := a_facts A in
  match rip_params T b, xaddr (aget (a_regs A) 10%uint63), xrange s (aget (a_regs A) 11%uint63), aget (a_regs A) 1%uint63,
        aget (a_regs A) 2%uint63, find_entry (a_mem A) with
  | Some (mz, gK, gMB, gME, gHE, aK, aMB, aME, aHE), Some (tb, ob), Some (nlo, nhi), XL r, XS ts o, Some ph =>
      if (1 <=? nlo) &&& (nhi <=? 67108864) &&& teqb ts sp_terms &&& (- 8388608 + 72 <=? wS o) &&& (wS o <=? 0)
         &&& pc_ok r &&& atop_is_sp (a_model A) &&& (a_budget A + 4096 * rpg nhi <=? LIM)
         &&& in_app_mem s (wS ob, tb) nhi
         &&& ckR segs b mz gK gMB gME gHE &&& globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE
         &&& sh_zero_big s (a_mem A) tb (wS ob) nhi then
        match a_store segs (a_mem A) (XS sp_terms (wofZ (wS o - 72))) (repeat BT 72) with
        | Some mem' =>
            Some [AS r (rip_regs (a_regs A)) (resv_drop (a_resv A)) mem' s (a_model A) (a_budget A + 4096 * rpg nhi) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _, _, _ => None
  end.

Definition sum_rip_big (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_rip_big_g rip_code_okf T segs LIM A.

Lemma sum_rip_big_g_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  rip_ck T segs (wZ (a_pc A)) = true -> sum_rip_big_g ck_true6 T segs LIM A = Some l -> sum_rip_big T segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_rip_big, sum_rip_big_g in *. cbv zeta in *. unfold rip_ck in Hck. unfold ck_true6 in H.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|]; [|exact H]. rewrite Hck. exact H.
Qed.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RipBig.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_rip_big_sound (A : AST) (l : list AST) : sum_rip_big T segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_rip_big, sum_rip_big_g in Hs.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|] eqn:Ep; [|discriminate].
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[tb ob]|] eqn:Eb10; [|discriminate].
  destruct (xrange (a_facts A) (aget (a_regs A) 11%uint63)) as [[nlo nhi]|] eqn:E11; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (aget (a_regs A) 2%uint63) as [| ts o | | | |] eqn:E2; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  cbv zeta in Hs.
  destruct (1 <=? nlo) eqn:En1; [|discriminate]. apply Z.leb_le in En1.
  destruct (nhi <=? 67108864) eqn:En2; [|discriminate]. apply Z.leb_le in En2.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 + 72 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (a_budget A + 4096 * rpg nhi <=? LIM) eqn:Hbud; [|discriminate]. apply Z.leb_le in Hbud.
  destruct (in_app_mem (a_facts A) (wS ob, tb) nhi) eqn:Ern;
    [|discriminate].
  destruct (rip_code_okf segs (wZ (a_pc A)) mz gK gMB gME gHE) eqn:Hcode; [|discriminate]. apply rip_code_okf_ok in Hcode.
  destruct (globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE) eqn:Hglob; [|discriminate].
  destruct (sh_zero_big (a_facts A) (a_mem A) tb (wS ob) nhi) eqn:Hsh; [|discriminate].
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
  set (beg := rg ms 10%bv).
  pose proof (xrange_sound ρ _ _ (rg ms 11%bv) Hsat (Hregs 11%bv) _ E11) as Hcr. cbn [fst snd] in Hcr.
  set (n := bv_unsigned (rg ms 11%bv)) in *.
  (* [comment removed for export] *)
  assert (Hbv : bv_unsigned beg = smod ρ tb ob).
  { apply (xaddr_val ρ (aget (a_regs A) 10%uint63) beg tb ob); [|exact Eb10]. exact (Hregs 10%bv). }
  set (F := leval ρ (wS ob, tb)) in *.
  assert (HF : (0x10007fff8000 <= F /\ F + nhi + 8 <= 2 ^ 47) \/ (0 <= F /\ F + nhi + 8 <= 0x7fff8000)).
  { pose proof (in_app_mem_sound ρ _ _ _ Hsat Ern) as X. fold F in X. lia. }
  assert (HFe : F = teval ρ tb + wS ob) by (unfold F, leval; cbn [fst snd]; ring).
  assert (Hbeg : bv_unsigned beg = F).
  { rewrite Hbv. unfold smod. rewrite <- (wS_mod ob). rewrite Zplus_mod_idemp_r. rewrite <- HFe.
    apply Z.mod_small. unfold two64. lia. }
  assert (H11 : rg ms 11%bv = Z_to_bv 64 n) by (apply word_lit_w; reflexivity).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec r Epc) as [Hr4 Hr26].
  (* [comment removed for export] *)
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HFE.
  pose proof (eb_layout ρ HFE) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
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
  assert (Hrpg : rpg n <= rpg nhi) by (unfold rpg; assert (n / 8 <= nhi / 8) by (apply Z.div_le_mono; lia); lia).
  apply (rip_sum_tight segs cfg b mz gK gMB gME gHE aK aMB aME aHE HW HWh HWz HJz HPh0 HPh20 HPh28 HPh44 HP2c HP4c HP54 HP70 HP94 HP9c HPb8 Hgb Hb8
           ms model (KT ρ o') beg n Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - exact H11.
  - lia.
  - lia.
  - rewrite Hbeg. destruct HF as [X|X]; [left|right]; lia.
  - destruct Hmem as [Hok HRR].
    assert (Hc : forall a v, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> cell_lit segs (a_mem A) a v = true -> cell8 segs (ms_mem ms) a v).
    { intros a v Hin Hcl. destruct (Hgl a Hin). apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) a v (conj Hok HRR)); [unfold ls_beg in *; lia | exact Hcl]. }
    unfold globals. repeat split; apply Hc; first [assumption | cbn; tauto].
  - assert (Hn : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> no_lazy model a (a + 8))
      by (intros a Hin; exact (no_lazy_img segs Hlow model a 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) (Hins a Hin))).
    unfold globals_nl. repeat split; apply Hn; cbn; tauto.
  - intros q Hq. rewrite Hbeg, HFe in Hq.
    exact (sh_zero_big_sound segs ρ (a_facts A) (a_mem A) (ms_mem ms) tb (wS ob) nhi n Hmem Hsh ltac:(lia) ltac:(lia) ltac:(lia) q Hq).
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. pose proof Hrpg. lia.
  - lia.
  - exact Hok72.
  - apply (no_lazy_above segs fs0 ρ (a_model A) model _ _ Hmod). rewrite Hatop. lia.
  - right. unfold hs_hi in Hd8. lia.
  - intros a Hin. left. destruct (Hgl a Hin). unfold ls_beg in *. lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - (* [comment removed for export] *)
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
    + right. exists pages. split; [exact Em'|]. destruct Hb as [Hb1 Hb2]. lia.
Qed.

End RipBig.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
