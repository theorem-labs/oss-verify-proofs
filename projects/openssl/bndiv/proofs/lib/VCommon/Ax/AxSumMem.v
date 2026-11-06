(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxSys AxJoinSound AsanWLazy AsanWBase AsanWMemcpy AsanWMemcpyF1 AsanWMemcpyF3 AsanSMat AsanWMat AsanWMcM3 AsanWMemset AsanWMsM AxSum.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MCF_CLOB' : list reg :=
  [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 7; Z_to_bv 5 28; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 14; Z_to_bv 5 15;
   Z_to_bv 5 16; Z_to_bv 5 17].

Lemma MCF_CLOB_eq : MCF_CLOB = MCF_CLOB'.
Proof. unfold MCF_CLOB, MCF_CLOB'. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

Lemma MCF_CLOB'_nz (r : reg) : In r MCF_CLOB' -> bv_unsigned r <> 0.
Proof.
  intros H. unfold MCF_CLOB' in H. cbn [In] in H.
  destruct H as [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]]]; rewrite <- X; vm_compute; discriminate.
Qed.

(* [comment removed for export] *)
Definition mc_code_ok (segs : list Segment) (e : Z) : bool :=
  words_ok_f segs e MC_WORDS &&& words_ok_f segs e MCF_WORDS &&& (0 <=? e) &&& (e + 1028 <=? 140737488355328) &&& (e mod 4 =? 0).

Lemma mc_code_sound (segs : list Segment) (e : Z) : mc_code_ok segs e = true -> MCFCode segs e.
Proof.
  unfold mc_code_ok. intros H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.eqb_eq in H5.
  apply words_ok_f_eq in H1. apply words_ok_f_eq in H2.
  constructor; [constructor; [exact H1 | repeat split; [exact H3 | exact H4 | exact H5]] | exact H2].
Qed.

(* [comment removed for export] *)
Definition disj_ok (s : store) (f g : lin) (n : Z) : bool :=
  let a := lsub f g in let b := lsub g f in
  lr_ge s a n ||| lr_ge s b n ||| hole_far s a n ||| hole_far s b n ||| rprove_q 2 s a n ||| rprove_q 2 s b n.

Lemma disj_ok_sound (ρ : valuation) (s : store) (f g : lin) (n : Z) :
  sat ρ s -> disj_ok s f g n = true -> leval ρ g + n <= leval ρ f \/ leval ρ f + n <= leval ρ g.
Proof.
  intros Hs H. unfold disj_ok in H. cbv zeta in H.
  apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]; [apply lor_true in H as [H|H]; [apply lor_true in H as [H|H];
    [apply lor_true in H as [H|H]|]|]|]|].
  - pose proof (lr_ge_sound ρ s _ _ Hs H) as X. rewrite leval_lsub in X. left. lia.
  - pose proof (lr_ge_sound ρ s _ _ Hs H) as X. rewrite leval_lsub in X. right. lia.
  - pose proof (hole_far_sound ρ s _ _ Hs H) as X. rewrite leval_lsub in X. lia.
  - pose proof (hole_far_sound ρ s _ _ Hs H) as X. rewrite leval_lsub in X. lia.
  - pose proof (rprove_q_sound ρ s 2 _ _ Hs H) as X. rewrite leval_lsub in X. left. lia.
  - pose proof (rprove_q_sound ρ s 2 _ _ Hs H) as X. rewrite leval_lsub in X. right. lia.
Qed.

(* [comment removed for export] *)
Lemma addr_form_val' (ρ : valuation) (v : xv) (a : bv 64) (ts : terms) (o : w64) (B : Z) :
  xv_val ρ v a -> xaddr v = Some (ts, o) -> 0 <= leval ρ (wS o, ts) <= B -> B < FastWord.two64 -> bv_unsigned a = leval ρ (wS o, ts).
Proof.
  intros Hv Ea Hr HB. rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r.
  replace (teval ρ ts + wS o) with (leval ρ (wS o, ts)) by (unfold leval; cbn [fst snd]; ring). apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xv_off (v : xv) (j : Z) : xv :=
  match v with
  | XL x => XL (w_add x (wofZ j))
  | XS ts o => XS ts (w_add o (wofZ j))
  | _ => XT
  end.

Lemma xv_off_sound (ρ : valuation) (v : xv) (a : bv 64) (j : Z) :
  xv_val ρ v a -> xaddr v <> None -> xv_val ρ (xv_off v j) (Z_to_bv 64 (bv_unsigned a + j)).
Proof.
  intros Hv Hx. destruct v as [x|ts o| | | |]; cbn [xaddr] in Hx; try (exfalso; apply Hx; reflexivity); cbn [xv_off xv_val] in *.
  - rewrite Z_to_bv_unsigned, wZ_add, wZ_wofZ, Hv. unfold bv_wrap. change (bv_modulus 64) with FastWord.two64.
    symmetry. apply Zplus_mod_idemp_r.
  - rewrite Z_to_bv_unsigned, Hv. unfold smod, bv_wrap. change (bv_modulus 64) with FastWord.two64. rewrite wZ_add, wZ_wofZ.
    rewrite Zplus_mod_idemp_l. rewrite (Z.add_mod_idemp_r (wZ o) j) by (unfold FastWord.two64; lia).
    rewrite Zplus_mod_idemp_r. f_equal. ring.
Qed.

Section Load.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

Fixpoint load_bw (s : store) (A : list region) (v : xv) (j : Z) (k : nat) : option (list xb) :=
  match k with
  | O => Some []
  | S k' => match a_load4 segs s A (xv_off v j) 1, load_bw s A v (j + 1) k' with
            | Some [x], Some l => Some (x :: l)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Definition mc_load (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match (match find_entry A with Some _ => str_load s v n | None => None end) with
  | Some l => Some l
  | None =>
      match a_load4 segs s A v n with
      | Some l => Some l
      | None => load_bw s A v 0 n
      end
  end.

Lemma load_bw_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> xaddr v <> None ->
  forall (k : nat) (j : Z) (l : list xb), load_bw s A v j k = Some l ->
  exists bs, rdn segs m (Z_to_bv 64 (bv_unsigned a + j)) k = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hhs Hv Hx. induction k as [|k IH]; intros j l H; cbn [load_bw] in H.
  - injection H as <-. exists []. split; [reflexivity | constructor].
  - destruct (a_load4 segs s A (xv_off v j) 1) as [[|x [|x' r]]|] eqn:E1; try discriminate H.
    destruct (load_bw s A v (j + 1) k) as [l'|] eqn:E2; [|discriminate H]. injection H as <-.
    destruct (a_load4_sound segs ρ s A m _ _ 1 [x] Hlow Hs HM Hhs (xv_off_sound ρ v a j Hv Hx) ltac:(lia) E1) as [b1 [Hr1 HF1]].
    destruct (IH (j + 1) l' E2) as [bs [Hr HF]].
    rewrite (rdn_cons' segs m _ 0) in Hr1. destruct (rv segs m (Z_to_bv 64 (bv_unsigned a + j))) as [b|] eqn:Eb; [|discriminate Hr1].
    cbn [rdn] in Hr1. injection Hr1 as <-.
    exists (b :: bs). split.
    + rewrite rdn_cons', Eb. replace (Z_to_bv 64 (bv_unsigned a + j) + 1)%bv with (Z_to_bv 64 (bv_unsigned a + (j + 1))).
      * rewrite Hr. reflexivity.
      * apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_unsigned 1%bv) with 1.
        rewrite Zplus_mod_idemp_l. f_equal. lia.
    + constructor; [|exact HF]. inversion HF1; subst. assumption.
Qed.

Lemma mc_load_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> xaddr v <> None -> (1 <= n < 1000)%nat -> mc_load s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hhs Hv Hx Hn H. unfold mc_load in H.
  destruct (match find_entry A with Some _ => str_load s v n | None => None end) as [l1|] eqn:E1.
  { injection H as <-. destruct (find_entry A) as [ph|] eqn:Efe; [|discriminate].
    destruct (eb_of_R segs ρ A m ph HM Efe) as [nR Heb]. exact (str_load_sound segs ph ρ s m nR v a n l1 Hs Heb Hv E1). }
  destruct (a_load4 segs s A v n) as [l0|] eqn:E.
  - injection H as <-. exact (a_load4_sound segs ρ s A m v a n l0 Hlow Hs HM Hhs Hv Hn E).
  - destruct (load_bw_sound ρ s A m v a Hs HM Hhs Hv Hx n 0 l H) as [bs [Hr HF]]. exists bs. split; [|exact HF].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hr. exact Hr.
Qed.

End Load.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mc_mem (segs : list Segment) (s : store) (A : list region) (d sv : xv) (n : Z) : option (list region) :=
  if n =? 0 then Some A else
  match mc_load segs s A sv (Z.to_nat n) with
  | Some l => a_store4 segs s A d l
  | None => None
  end.

Definition sum_memcpy_g (ckM : (list Segment -> Z -> bool)) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let e := wZ (a_pc A) in
  let s := a_facts A in
  let d := aget (a_regs A) 10%uint63 in
  let sv := aget (a_regs A) 11%uint63 in
  match xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, xaddr d, xaddr sv with
  | Some n, XL r, Some (td, od), Some (tsr, osr) =>
      if (0 <=? n) &&& (n <? 1000) &&& ckM segs e &&& (wZ r mod 4 =? 0) &&& (wZ r <? 2 ^ 26)
         &&& rbetween 2 s (wS od, td) 0 (2 ^ 47 - n) &&& rbetween 2 s (wS osr, tsr) 0 (2 ^ 47 - n)
         &&& disj_ok s (wS od, td) (wS osr, tsr) n &&& (a_budget A + 4096 * mc_pages n <=? LIM) then
        match mc_mem segs s (a_mem A) d sv n with
        | Some mem' => Some [AS (wofZ (wZ r)) (clob MCF_CLOB' (a_regs A)) (match a_resv A with RNone => RNone | _ => RUnk end)
                                mem' s (a_model A) (a_budget A + 4096 * mc_pages n) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _ => None
  end.

Definition sum_memcpy (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_memcpy_g mc_code_ok segs LIM A.

Lemma sum_memcpy_g_ck (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  mc_code_ok segs (wZ (a_pc A)) = true -> sum_memcpy_g ck_true1 segs LIM A = Some l -> sum_memcpy segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_memcpy, sum_memcpy_g in *. cbv zeta in *. unfold ck_true1 in H. rewrite Hck. exact H.
Qed.

Section McSound.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

(* [comment removed for export] *)
Lemma copied_write (m m' : word -> option byte) (dst : bv 64) (bs : list byte) :
  bv_unsigned dst + Z.of_nat (length bs) <= 2 ^ 64 -> copied m' m (bv_unsigned dst) (Z.of_nat (length bs)) bs ->
  forall x, m' x = write_to_mem m dst bs x.
Proof.
  intros H64 Hcp x. pose proof (bvu_range dst) as Hd.
  pose proof (write_to_mem_spec bs m (bv_unsigned dst) x ltac:(lia) H64) as W. unfold wz in W. rewrite Z_to_bv_bv_unsigned in W.
  rewrite W. destruct (Hcp x) as [C1 C2].
  destruct ((bv_unsigned dst <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned dst + Z.of_nat (length bs))) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite C1 by lia.
    symmetry. apply nth_error_nth'. lia.
  - apply C2. intros [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. rewrite X1, X2 in E. discriminate E.
Qed.

Lemma mc_mem_sound (ρ : valuation) (s : store) (A M : list region) (m m' : word -> option byte) (d sv : xv) (dst src : bv 64)
    (n : Z) (bs : list byte) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ d dst -> xv_val ρ sv src -> xaddr sv <> None ->
  mc_mem segs s A d sv n = Some M -> 0 <= n < 1000 -> bv_unsigned dst + n <= 2 ^ 64 ->
  rdn segs m src (Z.to_nat n) = Some bs -> copied m' m (bv_unsigned dst) n bs ->
  RMem segs ρ M m' /\ hs_ok ρ M m' /\ Forall2 same_fields A M /\ store_ok segs m dst (Z.to_nat n) = true.
Proof.
  intros Hs HM Hhs Hvd Hvs Hx H Hn Hd64 Hrd Hcp. unfold mc_mem in H. destruct (n =? 0) eqn:Enz.
  - apply Z.eqb_eq in Enz. injection H as <-. subst n.
    assert (Hpw : forall x, m' x = m x) by (intros x; apply (proj2 (Hcp x)); lia).
    split; [exact (RMem_pw segs ρ A m m' Hpw HM)|]. split; [exact (hs_ok_pw ρ A m m' Hpw Hhs)|].
    split; [apply Forall2_same_refl | reflexivity].
  - apply Z.eqb_neq in Enz. destruct (mc_load segs s A sv (Z.to_nat n)) as [l|] eqn:El; [|discriminate H].
    destruct (mc_load_sound segs Hlow ρ s A m sv src (Z.to_nat n) l Hs HM Hhs Hvs Hx ltac:(lia) El) as [bs' [Hrd' HF]].
    rewrite Hrd in Hrd'. injection Hrd' as <-.
    pose proof (rdn_length segs m (Z.to_nat n) src bs Hrd) as Hlb. pose proof (Forall2_length HF) as Hll.
    destruct (a_store4_sound segs ρ s A M m d dst l bs Hlow Hs HM Hhs Hvd ltac:(lia) HF H) as (Hok & HM' & Hhs').
    assert (Hpw : forall x, m' x = write_to_mem m dst bs x).
    { apply copied_write; [lia|]. replace (Z.of_nat (length bs)) with n by lia. exact Hcp. }
    split; [exact (RMem_pw segs ρ M _ m' Hpw HM')|]. split; [exact (hs_ok_pw ρ M _ m' Hpw Hhs')|].
    split; [exact (a_store4_fields segs s A M d l H)|]. rewrite <- Hlb, <- Hll. exact Hok.
Qed.

End McSound.

Section MemcpySound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_memcpy_sound (A : AST) (l : list AST) : sum_memcpy segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho.
  unfold sum_memcpy, sum_memcpy_g in Hs.
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[td od]|] eqn:Ed; [|discriminate].
  destruct (xaddr (aget (a_regs A) 11%uint63)) as [[tsr osr]|] eqn:Esr; [|discriminate].
  match type of Hs with context [if ?c then _ else _] => destruct c eqn:Ec; [|discriminate] end.
  destruct (mc_mem segs (a_facts A) (a_mem A) (aget (a_regs A) 10%uint63) (aget (a_regs A) 11%uint63) n) as [mem'|] eqn:Emc; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Ec Hdj]. apply andb_prop in Ec as [Ec Hrs]. apply andb_prop in Ec as [Ec Hrd].
  apply andb_prop in Ec as [Ec Hr26]. apply andb_prop in Ec as [Ec Hr4]. apply andb_prop in Ec as [Ec Hcode].
  apply andb_prop in Ec as [Hn0 Hn1].
  apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. apply Z.ltb_lt in Hr26. apply Z.eqb_eq in Hr4. apply Z.leb_le in Hbud.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (e := wZ (a_pc A)) in *.
  set (dst := rg ms 10%bv). set (src := rg ms 11%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 10%uint63) dst) by exact (Hregs 10%bv).
  assert (Hvs : xv_val ρ (aget (a_regs A) 11%uint63) src) by exact (Hregs 11%bv).
  pose proof (reg_lit ρ _ ms 12%bv 12%uint63 n Hregs eq_refl E12) as Hcnt.
  pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - n) Hsat Hrd) as Hrdv. pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - n) Hsat Hrs) as Hrsv.
  assert (Hdv : bv_unsigned dst = leval ρ (wS od, td)) by (apply (addr_form_val' ρ _ dst td od (2 ^ 47 - n) Hvd Ed); [lia | unfold FastWord.two64; lia]).
  assert (Hsv : bv_unsigned src = leval ρ (wS osr, tsr)) by (apply (addr_form_val' ρ _ src tsr osr (2 ^ 47 - n) Hvs Esr); [lia | unfold FastWord.two64; lia]).
  pose proof (disj_ok_sound ρ _ _ _ n Hsat Hdj) as Hdisj. rewrite <- Hdv, <- Hsv in Hdisj.
  assert (Hxs : xaddr (aget (a_regs A) 11%uint63) <> None) by (rewrite Esr; discriminate).
  (* [comment removed for export] *)
  assert (Hrdx : exists bs, rdn segs (ms_mem ms) src (Z.to_nat n) = Some bs).
  { destruct (Z.eq_dec n 0) as [->|Hnz]; [exists []; reflexivity|].
    unfold mc_mem in Emc. rewrite (proj2 (Z.eqb_neq n 0) Hnz) in Emc.
    destruct (mc_load segs (a_facts A) (a_mem A) (aget (a_regs A) 11%uint63) (Z.to_nat n)) as [l0|] eqn:El; [|discriminate Emc].
    destruct (mc_load_sound segs Hlow ρ _ _ (ms_mem ms) _ src (Z.to_nat n) l0 Hsat Hmem Hhs Hvs Hxs ltac:(lia) El) as [bs [Hr _]].
    exists bs. exact Hr. }
  destruct Hrdx as [bs Hrd0].
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  pose proof (wZ_range r) as Hrr.
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  assert (Esrc : src = Z_to_bv 64 (bv_unsigned src)) by (apply word_lit_w; reflexivity).
  (* [comment removed for export] *)
  assert (Hok : store_ok segs (ms_mem ms) dst (Z.to_nat n) = true).
  { destruct (Z.eq_dec n 0) as [->|Hnz]; [reflexivity|].
    unfold mc_mem in Emc. rewrite (proj2 (Z.eqb_neq n 0) Hnz) in Emc.
    destruct (mc_load segs (a_facts A) (a_mem A) (aget (a_regs A) 11%uint63) (Z.to_nat n)) as [l0|] eqn:El; [|discriminate Emc].
    destruct (mc_load_sound segs Hlow ρ _ _ (ms_mem ms) _ src (Z.to_nat n) l0 Hsat Hmem Hhs Hvs Hxs ltac:(lia) El) as [bs' [Hr' HF]].
    pose proof (rdn_length segs _ _ _ _ Hr') as Hlb. pose proof (Forall2_length HF) as Hll.
    destruct (a_store4_sound segs ρ _ _ mem' (ms_mem ms) _ dst l0 bs' Hlow Hsat Hmem Hhs Hvd ltac:(lia) HF Emc) as (X & _ & _).
    rewrite <- Hlb, <- Hll. exact X. }
  apply (memcpy_sum_mat segs cfg e (mc_code_sound segs e Hcode) ms model (KT ρ o') (bv_unsigned dst) (bv_unsigned src) n bs Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - exact Edst.
  - exact Esrc.
  - apply word_lit_w. exact Hcnt.
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
  - intros ms' model' HMC Hcp Hpc' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMC as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused]. subst model'.
    destruct (model_backing_fields model pages) as [MH ML].
    assert (Er : wZ (wofZ (wZ r)) = wZ r) by (rewrite wZ_wofZ; apply Z.mod_small; exact Hrr).
    destruct (mc_mem_sound segs Hlow ρ _ _ _ (ms_mem ms) (ms_mem ms') _ _ dst src n bs Hsat Hmem Hhs Hvd Hvs Hxs Emc ltac:(lia) ltac:(lia) Hrd0 Hcp)
      as (Hmem' & Hhs' & Hsf & _).
    constructor; cbn [cfg_ms cfg_model a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. rewrite Er. apply word_lit_w. exact Hra.
    + rewrite Er. split; lia.
    + exact P1.
    + apply (RRegs_clob ρ (a_regs A) ms ms' MCF_CLOB' Hregs); [rewrite <- MCF_CLOB_eq; exact P6 | exact MCF_CLOB'_nz].
    + destruct (a_resv A); cbn [RResv] in *; try exact I. destruct P5 as [X|X]; rewrite X; [exact Hres | reflexivity].
    + rewrite P2. exact Hrom.
    + exact Hmem'.
    + exact (MR_mat segs fs0 ρ (a_model A) model pages Hmod).
    + rewrite MH. exact Hh.
    + destruct Hb as [Hb1 Hb2]. split; [unfold page_size in Hused; lia | rewrite ML; exact Hb2].
    + exact Hsat.
    + exact Hhs'.
    + apply mem_cov_backing.
      apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hcov ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hcp x)). lia.
    + apply comp_inv_backing. exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply na_ok_backing. apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hnaok ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hcp x)). lia.
Qed.

End MemcpySound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_code_ok (segs : list Segment) (e : Z) : bool :=
  words_ok_f segs e MS_WORDS &&& (0 <=? e) &&& (e + 96 <=? 140737488355328) &&& (e mod 4 =? 0).

Lemma ms_code_sound (segs : list Segment) (e : Z) : ms_code_ok segs e = true -> MSCode segs e.
Proof.
  unfold ms_code_ok. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.eqb_eq in H4. apply words_ok_f_eq in H1. constructor; [exact H1 | repeat split; assumption].
Qed.

(* [comment removed for export] *)
Definition MS_CLOB' : list reg := [Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13].

Lemma MS_CLOB'_nz (r : reg) : In r MS_CLOB' -> bv_unsigned r <> 0.
Proof. intros H. unfold MS_CLOB' in H. cbn [In] in H. destruct H as [X|[X|[X|[]]]]; rewrite <- X; vm_compute; discriminate. Qed.

Lemma MS_CLOB'_out (r : reg) : ~ In r MS_CLOB' -> r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv.
Proof.
  intros H. unfold MS_CLOB' in H. cbn [In] in H. repeat split; intros ->; apply H.
  - left. apply bv_eq. reflexivity.
  - right. left. apply bv_eq. reflexivity.
  - right. right. left. apply bv_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition mset_mem (segs : list Segment) (s : store) (A : list region) (d : xv) (c n : Z) : option (list region) :=
  if n =? 0 then Some A else
  if n <? 1000 then a_store4 segs s A d (repeat (BL (of_Z c)) (Z.to_nat n)) else None.

Definition sum_memset (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let e := wZ (a_pc A) in
  let s := a_facts A in
  let d := aget (a_regs A) 10%uint63 in
  match xlit (aget (a_regs A) 11%uint63), xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, xaddr d with
  | Some c, Some n, XL r, Some (td, od) =>
      if (0 <=? c) &&& (c <? 256) &&& (0 <=? n) &&& (n <? 70368744177664) &&& ms_code_ok segs e &&& (wZ r mod 4 =? 0) &&& (wZ r <? 2 ^ 26)
         &&& rbetween 2 s (wS od, td) 0 (2 ^ 47 - n) &&& (a_budget A + 4096 * ms_pages n <=? LIM) then
        match mset_mem segs s (a_mem A) d c n with
        | Some mem' => Some [AS (wofZ (wZ r)) (clob MS_CLOB' (a_regs A)) (match a_resv A with RNone => RNone | _ => RUnk end)
                                mem' s (a_model A) (a_budget A + 4096 * ms_pages n) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _ => None
  end.

Section MsSound.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

Lemma filled_write (m m' : word -> option byte) (dst : bv 64) (n : nat) (v : byte) :
  bv_unsigned dst + Z.of_nat n <= 2 ^ 64 -> filled m' m (bv_unsigned dst) (bv_unsigned dst + Z.of_nat n) v ->
  forall x, m' x = write_to_mem m dst (repeat v n) x.
Proof.
  intros H64 Hf x. pose proof (bvu_range dst) as Hd.
  pose proof (write_to_mem_spec (repeat v n) m (bv_unsigned dst) x ltac:(lia) ltac:(rewrite repeat_length; exact H64)) as W.
  unfold wz in W. rewrite Z_to_bv_bv_unsigned, repeat_length in W. rewrite W. destruct (Hf x) as [C1 C2].
  destruct ((bv_unsigned dst <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned dst + Z.of_nat n)) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite C1 by lia. symmetry.
    rewrite (nth_error_nth' _ v) by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
  - apply C2. intros [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. rewrite X1, X2 in E. discriminate E.
Qed.

Lemma mset_mem_sound (ρ : valuation) (s : store) (A M : list region) (m m' : word -> option byte) (d : xv) (dst : bv 64) (c n : Z) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ d dst -> 0 <= c < 256 -> 0 <= n -> bv_unsigned dst + n <= 2 ^ 64 ->
  mset_mem segs s A d c n = Some M ->
  store_ok segs m dst (Z.to_nat n) = true /\
  (filled m' m (bv_unsigned dst) (bv_unsigned dst + n) (Z_to_bv 8 c) -> RMem segs ρ M m' /\ hs_ok ρ M m' /\ Forall2 same_fields A M).
Proof.
  intros Hs HM Hhs Hvd Hc Hn Hd64 H. unfold mset_mem in H. destruct (n =? 0) eqn:Enz.
  - apply Z.eqb_eq in Enz. injection H as <-. subst n. split; [reflexivity|]. intros Hf.
    assert (Hpw : forall x, m' x = m x) by (intros x; apply (proj2 (Hf x)); lia).
    split; [exact (RMem_pw segs ρ A m m' Hpw HM)|]. split; [exact (hs_ok_pw ρ A m m' Hpw Hhs) | apply Forall2_same_refl].
  - apply Z.eqb_neq in Enz. destruct (n <? 1000) eqn:En; [|discriminate H]. apply Z.ltb_lt in En.
    assert (HF : forall k : nat, Forall2 (xb_bv ρ) (repeat (BL (of_Z c)) k) (repeat (Z_to_bv 8 c) k)).
    { induction k as [|k IH]; cbn [repeat]; [constructor|]. constructor; [|exact IH]. unfold xb_bv. cbn [xb_z].
      rewrite Z_to_bv_unsigned, of_Z_spec. unfold bv_wrap. change (bv_modulus 8) with 256. change wB with (2 ^ 63).
      rewrite !Z.mod_small by lia. reflexivity. }
    assert (Hlen : (1 <= length (repeat (BL (of_Z c)) (Z.to_nat n)) < 1000)%nat) by (rewrite repeat_length; lia).
    destruct (a_store4_sound segs ρ s A M m d dst _ _ Hlow Hs HM Hhs Hvd Hlen (HF _) H) as (Hok & HM' & Hhs').
    rewrite repeat_length in Hok. split; [exact Hok|]. intros Hf.
    assert (Hpw : forall x, m' x = write_to_mem m dst (repeat (Z_to_bv 8 c) (Z.to_nat n)) x).
    { apply filled_write; [lia|]. rewrite Z2Nat.id by lia. exact Hf. }
    split; [exact (RMem_pw segs ρ M _ m' Hpw HM')|]. split; [exact (hs_ok_pw ρ M _ m' Hpw Hhs')|].
    exact (a_store4_fields segs s A M d _ H).
Qed.

End MsSound.

Section MemsetSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_memset_sound (A : AST) (l : list AST) : sum_memset segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho.
  unfold sum_memset in Hs.
  destruct (xlit (aget (a_regs A) 11%uint63)) as [c|] eqn:E11; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[td od]|] eqn:Ed; [|discriminate].
  match type of Hs with context [if ?c then _ else _] => destruct c eqn:Ec; [|discriminate] end.
  destruct (mset_mem segs (a_facts A) (a_mem A) (aget (a_regs A) 10%uint63) c n) as [mem'|] eqn:Emc; [|discriminate].
  injection Hs as <-.
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Ec Hrd].
  apply andb_prop in Ec as [Ec Hr26]. apply andb_prop in Ec as [Ec Hr4]. apply andb_prop in Ec as [Ec Hcode].
  apply andb_prop in Ec as [Ec Hn1]. apply andb_prop in Ec as [Ec Hn0]. apply andb_prop in Ec as [Hc0 Hc1].
  apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc1. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. apply Z.ltb_lt in Hr26. apply Z.eqb_eq in Hr4.
  apply Z.leb_le in Hbud.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (e := wZ (a_pc A)) in *. set (dst := rg ms 10%bv).
  assert (Hvd : xv_val ρ (aget (a_regs A) 10%uint63) dst) by exact (Hregs 10%bv).
  pose proof (reg_lit ρ _ ms 11%bv 11%uint63 c Hregs eq_refl E11) as Hcv.
  pose proof (reg_lit ρ _ ms 12%bv 12%uint63 n Hregs eq_refl E12) as Hcnt.
  pose proof (rbetween_sound ρ _ 2 _ 0 (2 ^ 47 - n) Hsat Hrd) as Hrdv.
  assert (Hdv : bv_unsigned dst = leval ρ (wS od, td)) by (apply (addr_form_val' ρ _ dst td od (2 ^ 47 - n) Hvd Ed); [lia | unfold FastWord.two64; lia]).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  pose proof (wZ_range r) as Hrr.
  assert (Edst : dst = Z_to_bv 64 (bv_unsigned dst)) by (apply word_lit_w; reflexivity).
  destruct (mset_mem_sound segs Hlow ρ _ _ mem' (ms_mem ms) (ms_mem ms) _ dst c n Hsat Hmem Hhs Hvd ltac:(lia) Hn0 ltac:(lia) Emc) as [Hok _].
  apply (internal_memset_sum_mat segs cfg e (ms_code_sound segs e Hcode) ms model (KT ρ o') (bv_unsigned dst) n (rg ms 11%bv) Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - exact Edst.
  - reflexivity.
  - apply word_lit_w. exact Hcnt.
  - rewrite Hcv. exact Hc1.
  - lia.
  - lia.
  - lia.
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - rewrite <- Edst. exact Hok.
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. unfold page_size. lia.
  - intros ms' model' HMS Hfill Hpc' Hmat.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model') _ o' Ho).
    destruct HMS as [P1 P2 P3 P4 P5 P6].
    destruct Hmat as [[pages Em'] Hused]. subst model'.
    destruct (model_backing_fields model pages) as [MH ML].
    assert (Er : wZ (wofZ (wZ r)) = wZ r) by (rewrite wZ_wofZ; apply Z.mod_small; exact Hrr).
    rewrite Hcv in Hfill.
    destruct (mset_mem_sound segs Hlow ρ _ _ mem' (ms_mem ms) (ms_mem ms') _ dst c n Hsat Hmem Hhs Hvd ltac:(lia) Hn0 ltac:(lia) Emc) as [_ X].
    destruct (X Hfill) as (Hmem' & Hhs' & Hsf).
    constructor; cbn [cfg_ms cfg_model a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. rewrite Er. apply word_lit_w. exact Hra.
    + rewrite Er. split; lia.
    + exact P1.
    + apply (RRegs_clob ρ (a_regs A) ms ms' MS_CLOB' Hregs); [|exact MS_CLOB'_nz].
      intros r0 Hr0. destruct (MS_CLOB'_out r0 Hr0) as (N1 & N2 & N3). exact (P6 r0 N1 N2 N3).
    + destruct (a_resv A); cbn [RResv] in *; try exact I. destruct P5 as [Y|Y]; rewrite Y; [exact Hres | reflexivity].
    + rewrite P2. exact Hrom.
    + exact Hmem'.
    + exact (MR_mat segs fs0 ρ (a_model A) model pages Hmod).
    + rewrite MH. exact Hh.
    + destruct Hb as [Hb1 Hb2]. split; [unfold page_size in Hused; lia | rewrite ML; exact Hb2].
    + exact Hsat.
    + exact Hhs'.
    + apply mem_cov_backing.
      apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hcov ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
    + apply comp_inv_backing. exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
    + apply na_ok_backing. apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
      apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') (bv_unsigned dst) (Z.to_nat n) Hnaok ltac:(lia) ltac:(unfold AxAcct.two64; lia)).
      * unfold wz. rewrite <- Edst. exact Hok.
      * intros x Hx. apply (proj2 (Hfill x)). lia.
Qed.

End MemsetSound.
