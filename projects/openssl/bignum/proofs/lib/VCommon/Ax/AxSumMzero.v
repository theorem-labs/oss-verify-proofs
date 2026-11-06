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
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoinSound AsanWLazy AsanWAcc AsanWBase AsanSMat AsanWMat AsanWMemset AsanWMsM AsanSMzero AxSum.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition mz_code_ok (segs : list Segment) (e : Z) : bool :=
  words_ok_f segs e MZ_WORDS &&& (0 <=? e) &&& (e + 32 <=? 140737488355328) &&& (e mod 4 =? 0).

Lemma mz_code_sound (segs : list Segment) (e : Z) : mz_code_ok segs e = true -> MZCode segs e.
Proof.
  unfold mz_code_ok. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.eqb_eq in H4. apply words_ok_f_eq in H1. constructor; [exact H1 | repeat split; assumption].
Qed.

Definition MZ_CLOB : list reg := [11%bv; 14%bv].

Lemma MZ_CLOB_out (r : reg) : ~ In r MZ_CLOB -> r <> 11%bv /\ r <> 14%bv.
Proof.
  intros H. unfold MZ_CLOB in H. cbn [In] in H. split; intros ->; apply H.
  - left. apply bv_eq. reflexivity.
  - right. left. apply bv_eq. reflexivity.
Qed.

Lemma mz_addr_val (ρ : valuation) (v : xv) (a : bv 64) (ts : terms) (o : w64) (B : Z) :
  xv_val ρ v a -> xaddr v = Some (ts, o) -> 0 <= leval ρ (wS o, ts) <= B -> B < FastWord.two64 -> bv_unsigned a = leval ρ (wS o, ts).
Proof.
  intros Hv Ea Hr HB. rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r.
  replace (teval ρ ts + wS o) with (leval ρ (wS o, ts)) by (unfold leval; cbn [fst snd]; ring). apply Z.mod_small. lia.
Qed.

Definition sum_mzero (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let e := wZ (a_pc A) in
  let s := a_facts A in
  let m := a_regs A in
  match aget m 12%uint63, aget m 13%uint63, aget m 14%uint63, xaddr (aget m 11%uint63) with
  | XL z, XL t, XL c, Some (ts, o) =>
      if w_eqb z w_zero &&& (wZ t =? 31) &&& (32 <=? wZ c) &&& (wZ c <? 1099511627776) &&& mz_code_ok segs e
         &&& pc_ok (wofZ (e + 28)) then
        let n := 32 * (wZ c / 32) in
        if a_budget A + 4096 * ms_pages n <=? LIM then
          match a_zfill s (a_mem A) ts o n with
          | Some mem' => Some [AS (wofZ (e + 28))
                                  (aset (aset m 11%uint63 (a_add s (aget m 11%uint63) (XL (wofZ n)))) 14%uint63 (XL (wofZ (wZ c - n))))
                                  (match a_resv A with RNone => RNone | _ => RUnk end) mem' s (a_model A)
                                  (a_budget A + 4096 * ms_pages n) (a_steps A + 1)]
          | None => None
          end
        else None
      else None
  | _, _, _, _ => None
  end.

Section MzeroSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_mzero_sound (A : AST) (l : list AST) : sum_mzero segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho.
  unfold sum_mzero in Hs.
  destruct (aget (a_regs A) 12%uint63) as [z| | | | |] eqn:E12; try discriminate.
  destruct (aget (a_regs A) 13%uint63) as [t| | | | |] eqn:E13; try discriminate.
  destruct (aget (a_regs A) 14%uint63) as [c| | | | |] eqn:E14; try discriminate.
  destruct (xaddr (aget (a_regs A) 11%uint63)) as [[ts o]|] eqn:Ed; [|discriminate].
  match type of Hs with context [if ?c then _ else _] => destruct c eqn:Ec; [|discriminate] end.
  set (n := 32 * (wZ c / 32)) in *.
  destruct (a_budget A + 4096 * ms_pages n <=? LIM) eqn:Hbud; [|discriminate]. apply Z.leb_le in Hbud.
  destruct (a_zfill (a_facts A) (a_mem A) ts o n) as [mem'|] eqn:Ezf; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Ec as [Ec Hpcok]. apply andb_prop in Ec as [Ec Hcode]. apply andb_prop in Ec as [Ec Hc1].
  apply andb_prop in Ec as [Ec Hc0]. apply andb_prop in Ec as [Hz Ht].
  rewrite w_eqb_spec in Hz. apply Z.eqb_eq in Hz. change (wZ w_zero) with 0 in Hz.
  apply Z.eqb_eq in Ht. apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (e := wZ (a_pc A)) in *. set (dst := rg ms 11%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 11%uint63) dst) by exact (Hregs 11%bv).
  assert (H12 : bv_unsigned (rg ms 12%bv) = 0) by (specialize (Hregs 12%bv); change (ri 12%bv) with 12%uint63 in Hregs; rewrite E12 in Hregs; cbn [xv_val] in Hregs; lia).
  assert (H13 : bv_unsigned (rg ms 13%bv) = 31) by (specialize (Hregs 13%bv); change (ri 13%bv) with 13%uint63 in Hregs; rewrite E13 in Hregs; cbn [xv_val] in Hregs; lia).
  assert (H14 : bv_unsigned (rg ms 14%bv) = wZ c) by (specialize (Hregs 14%bv); change (ri 14%bv) with 14%uint63 in Hregs; rewrite E14 in Hregs; exact Hregs).
  destruct (a_zfill_sound segs ρ _ _ mem' (ms_mem ms) (ms_mem ms) ts o n Hlow Hsat Hmem Hhs Ezf) as (Hf0 & Hf1 & Hn0 & Hok & _).
  set (f := leval ρ (wS o, ts)) in *.
  assert (Hdv : bv_unsigned dst = f).
  { apply (mz_addr_val ρ _ dst ts o hs_hi Hvd Ed); [unfold f, hs_beg, hs_hi in *; lia | unfold hs_hi, FastWord.two64; lia]. }
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  assert (Hcr : 32 <= wZ c < 2 ^ 63) by lia.
  pose proof (mz_n_facts (wZ c) Hcr) as [Hcn Hn32]. fold n in Hcn, Hn32.
  apply (mzero_loop_sum_mat segs cfg e (mz_code_sound segs e Hcode) ms model (KT ρ o') (bv_unsigned dst) (wZ c) 0 Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - exact Edst.
  - apply word_lit_w. exact H12.
  - apply word_lit_w. exact H13.
  - apply word_lit_w. exact H14.
  - lia.
  - rewrite Hdv. unfold hs_beg in Hf0. lia.
  - exact Hcr.
  - fold n. rewrite Hdv. unfold hs_hi in Hf1. lia.
  - fold n. rewrite Hdv. exact Hok.
  - fold n. destruct Hb as [Hb1 Hb2]. rewrite Hb2. unfold page_size. lia.
  - fold n. intros ms' model' HMZ Hfill Hpc' G11 G14 Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMZ as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused]. subst model'.
    destruct (model_backing_fields model pages) as [MH ML].
    assert (He28 : 0 <= e + 28 < 2 ^ 64) by (pose proof (wZ_range (a_pc A)); unfold e, FastWord.two64 in *; lia).
    destruct (a_zfill_sound segs ρ _ _ mem' (ms_mem ms) (ms_mem ms') ts o n Hlow Hsat Hmem Hhs Ezf) as (_ & _ & _ & _ & X).
    fold f in X. rewrite Hdv in Hfill.
    destruct X as (Hmem' & Hhs' & Hsf).
    { intros y Hy. exact (proj1 (Hfill y) Hy). }
    { intros y Hy. exact (proj2 (Hfill y) Hy). }
    constructor; cbn [cfg_ms cfg_model a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv, pcw. rewrite wZ_wofZ. rewrite Z.mod_small by (unfold FastWord.two64; lia). reflexivity.
    + apply pc_ok_spec. exact Hpcok.
    + exact P1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' MZ_CLOB Hregs).
      * intros r Hr. destruct (MZ_CLOB_out r Hr) as [N1 N2]. exact (P6 r N1 N2).
      * intros r Hr. destruct (MZ_CLOB_out r Hr) as [N1 N2]. change 14%uint63 with (ri 14%bv). change 11%uint63 with (ri 11%bv).
        rewrite aget_aset_other by (intros E; apply N2; symmetry; apply bv_eq; exact E).
        rewrite aget_aset_other by (intros E; apply N1; symmetry; apply bv_eq; exact E). reflexivity.
      * intros r [<-|[<-|[]]].
        -- change 14%uint63 with (ri 14%bv). change 11%uint63 with (ri 11%bv).
           rewrite aget_aset_other by (vm_compute; discriminate). rewrite aget_aset_same by (vm_compute; discriminate).
           replace (rg ms' 11%bv) with (bv_add dst (Z_to_bv 64 n)).
           2:{ rewrite G11. rewrite Edst at 1. rewrite zw_add. reflexivity. }
           apply (a_add_sound ρ (a_facts A) _ _ dst (Z_to_bv 64 n) Hsat); [exact Hvd|].
           apply XL_val. unfold wbv. rewrite wZ_wofZ. rewrite Z.mod_small by (unfold FastWord.two64; lia). reflexivity.
        -- change 14%uint63 with (ri 14%bv). rewrite aget_aset_same by (vm_compute; discriminate).
           rewrite G14.
           apply XL_val. unfold wbv. rewrite wZ_wofZ. rewrite Z.mod_small by (unfold FastWord.two64; lia). reflexivity.
    + destruct (a_resv A); cbn [RResv] in *; try exact I. destruct P5 as [Y|Y]; rewrite Y; [exact Hres | reflexivity].
    + rewrite P2. exact Hrom.
    + exact Hmem'.
    + exact (MR_mat segs fs0 ρ (a_model A) model pages Hmod).
    + rewrite MH. exact Hh.
    + destruct Hb as [Hb1 Hb2]. split; [unfold page_size in Hused; lia | rewrite ML; exact Hb2].
    + exact Hsat.
    + exact Hhs'.
    + apply mem_cov_backing.
      apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') f (Z.to_nat n) Hcov ltac:(unfold hs_beg in *; lia) ltac:(unfold hs_hi, AxAcct.two64 in *; lia)).
      * exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
    + apply comp_inv_backing. exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply na_ok_backing. apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') f (Z.to_nat n) Hnaok ltac:(unfold hs_beg in *; lia) ltac:(unfold hs_hi, AxAcct.two64 in *; lia)).
      * exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
Qed.

End MzeroSound.
