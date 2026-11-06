(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanWEntry AsanWEb AsanWEbLoad AxSum AsanSWord AsanSMemchr AsanSRipA AsanSCode AxWordsInt AxTabs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chr_code_ok (segs : list Segment) (b cM cH : Z) : bool :=
  words_ok_f segs b MEMCHR_WORDS &&& pair_ok_f segs b 0x58 13 13 cM &&& pair_ok_f segs b 0x60 14 14 cH.

(* [comment removed for export] *)
Definition CHR_CLOB : list reg := [5%bv; 10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv].

(* [comment removed for export] *)
Definition strend (k : Z) : xv :=
  if k =? 0 then XS (sp_terms ++ t_ae0) (wofZ 184) else XS (sp_terms ++ t_ae01) (wofZ 185).

Definition chr_regs (regs : aregs) (k : Z) : aregs := aset (clob CHR_CLOB regs) 10%uint63 (strend k).

Definition sum_memchr (T : img_tabs) (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  match memchr_params T b, str_k (a_facts A) (aget (a_regs A) 10%uint63), xlit (aget (a_regs A) 11%uint63),
        xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63, find_entry (a_mem A) with
  | Some (cM, cH), Some k, Some c, Some n, XL r, Some ph =>
      if (c =? 0) &&& (131079 <=? n) &&& chr_code_ok segs b cM cH &&& pc_ok r &&& atop_is_sp (a_model A)
         &&& cell_lit segs (a_mem A) cM Mc &&& cell_lit segs (a_mem A) cH Hc &&& in_seg segs cM &&& in_seg segs cH
      then Some [AS r (chr_regs (a_regs A) k) (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A + 1)]
      else None
  | _, _, _, _, _, _ => None
  end.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ChrSound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

(* [comment removed for export] *)
Lemma memchr_sum_p (b cM cH : Z) :
  0 <= cM < 2 ^ 40 -> 0 <= cH < 2 ^ 40 -> chr_code_ok segs b cM cH = true ->
  forall (ms : machine_state) (model : Model) (Ts : TSet) (s : word) (bs : list byte) (n : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10%bv = s -> rg ms 11%bv = w0 -> rg ms 12%bv = Z_to_bv 64 n ->
  cstr segs (ms_mem ms) s bs ->
  (forall j, (Z.of_nat (length bs) < j < WE s bs)%Z -> exists x, bat segs (ms_mem ms) (s + Z_to_bv 64 j)%bv = Some x) ->
  (bv_unsigned s + WE s bs <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + WE s bs) ->
  (Z.of_nat (length bs) + 8 <= n < 2 ^ 64)%Z ->
  cell8 segs (ms_mem ms) cM Mc -> cell8 segs (ms_mem ms) cH Hc ->
  no_lazy model cM (cM + 8) -> no_lazy model cH (cH + 8) ->
  (bv_unsigned (rg ms 1%bv) mod 2 = 0)%Z ->
  (forall ms', FR MCLOB ms ms' -> ms_pc_val ms' = rg ms 1%bv -> rg ms' 10%bv = (s + Z_to_bv 64 (Z.of_nat (length bs)))%bv ->
     realizes_cfg segs cfg (mkCfg ms' model) Ts) ->
  realizes_cfg segs cfg (mkCfg ms model) Ts.
Proof.
  intros HcMr HcHr Hc. unfold chr_code_ok in Hc. rewrite !pair_ok_f_eq in Hc.
  apply land_true in Hc as [Hc HPH]. apply land_true in Hc as [HW HPM]. apply words_ok_f_eq in HW.
  exact (memchr_sum_ck segs cfg b cM cH HW HPM HPH HcMr HcHr).
Qed.

Theorem sum_memchr_sound (A : AST) (l : list AST) : sum_memchr T segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_memchr in Hs.
  destruct (memchr_params T (wZ (a_pc A))) as [[cM cH]|] eqn:Ep; [|discriminate].
  destruct (str_k (a_facts A) (aget (a_regs A) 10%uint63)) as [k|] eqn:Ek; [|discriminate].
  destruct (xlit (aget (a_regs A) 11%uint63)) as [c|] eqn:E11; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (c =? 0) eqn:Ec0; [|discriminate]. apply Z.eqb_eq in Ec0. subst c.
  destruct (131079 <=? n) eqn:En; [|discriminate]. apply Z.leb_le in En.
  destruct (chr_code_ok segs (wZ (a_pc A)) cM cH) eqn:Hcode; [|discriminate].
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (cell_lit segs (a_mem A) cM Mc) eqn:CM; [|discriminate].
  destruct (cell_lit segs (a_mem A) cH Hc) eqn:CH; [|discriminate].
  destruct (in_seg segs cM) eqn:IM; [|discriminate].
  destruct (in_seg segs cH) eqn:IH; [|discriminate].
  injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (memchr_params_rng T HT _ _ _ Ep) as [HcMr HcHr].
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  set (s := rg ms 10%bv).
  destruct (str_k_sound ρ (a_facts A) _ s k Hsat HF (Hregs 10%bv) Ek) as [Hk Hsa].
  destruct (eb_argvk segs ph ρ (ms_mem ms) nR k Heb Hk) as [Hcstr Hlen]. set (bs := nth (Z.to_nat k) (dec_argv ρ) []) in *.
  assert (Es : s = Z_to_bv 64 (str_addr ρ k)) by (apply word_lit_w; exact Hsa).
  assert (Hlk : 0 <= ρ (lenvar k) <= 131071 /\ str_addr ρ k + ρ (lenvar k) + 1 <= sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q
                /\ sp_val ρ + 184 <= str_addr ρ k).
  { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
  destruct Hlk as (Hlk0 & Hlk1 & Hlk2).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ r) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec r Epc) as [Hr4 Hr26].
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).
  (* [comment removed for export] *)
  set (SE := sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q) in *.
  assert (Hsp16 : sp_val ρ mod 8 = 0) by (rewrite (sp8_val ρ), Z.mul_comm; apply Z.mod_mul; lia).
  assert (HSE8 : SE mod 8 = 0).
  { unfold SE. replace (sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q) with (sp_val ρ + (23 + ρ v_argc + ρ v_envc + ρ v_q) * 8) by ring.
    rewrite Z.mod_add by lia. exact Hsp16. }
  assert (HWE : bv_unsigned s + WE s bs <= SE).
  { unfold WE. rewrite Hsa, Hlen. set (e := str_addr ρ k + ρ (lenvar k)) in *.
    assert (He : e < SE) by (unfold e; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod SE 8 ltac:(lia)) as D3. rewrite HSE8 in D3.
    assert (e / 8 < SE / 8) by lia. lia. }
  assert (HWE0 : Z.of_nat (length bs) < WE s bs).
  { unfold WE. rewrite Hsa, Hlen. set (e := str_addr ρ k + ρ (lenvar k)) in *.
    pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as D2. lia. }
  pose proof (AsanWEbLoad.cl_len ph ρ HF) as HBlen.
  pose proof (reg_lit ρ (a_regs A) ms 11%bv 11%uint63 _ Hregs eq_refl E11) as H11v.
  pose proof (reg_lit ρ (a_regs A) ms 12%bv 12%uint63 _ Hregs eq_refl E12) as H12v.
  apply (memchr_sum_p (wZ (a_pc A)) cM cH HcMr HcHr Hcode ms model (KT ρ o') s bs n Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - apply word_lit_w. rewrite H11v. reflexivity.
  - apply word_lit_w. exact H12v.
  - rewrite Es. exact Hcstr.
  - intros j Hj. fold SE in HWE.
    assert (Hz : 0 <= bv_unsigned s + j - sp_val ρ < Z.of_nat (length (eb_image ph ρ))) by (rewrite HBlen; unfold SE in HWE; lia).
    pose proof (eb_rel_byte ph ρ (ms_mem ms) _ _ Heb _ Hz) as Hbyte.
    exists (nth (Z.to_nat (bv_unsigned s + j - sp_val ρ)) (eb_image ph ρ) (Z_to_bv 8 0)). unfold bat.
    replace (s + Z_to_bv 64 j)%bv with (Z_to_bv 64 (sp_val ρ + (bv_unsigned s + j - sp_val ρ))); [rewrite Hbyte; reflexivity|].
    apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small j) by (unfold SE in HWE; lia). f_equal. ring.
  - unfold SE in HWE. lia.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop, Hsa. lia.
  - rewrite Hlen. pose proof (wZ_range (match aget (a_regs A) 12%uint63 with XL x => x | _ => w_zero end)) as Hnr.
    split; [lia|]. unfold xlit in E12. destruct (aget (a_regs A) 12%uint63) as [x| | | | |]; try discriminate E12.
    injection E12 as <-. pose proof (wZ_range x) as X. unfold two64 in X. lia.
  - apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) cM Mc Hmem); [lia | exact CM].
  - apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) cH Hc Hmem); [lia | exact CH].
  - exact (no_lazy_img segs Hlow model cM 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) IM).
  - exact (no_lazy_img segs Hlow model cH 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) IH).
  - rewrite Hra. rewrite (Z.div_mod (wZ r) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ r / 4)) with ((wZ r / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - intros ms' (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hpc' H10'.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model) _ o' Ho).
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. apply word_lit_w. exact Hra.
    + exact Epc.
    + exact F1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' MCLOB Hregs F7).
      * intros r0 Hr0. destruct (Z.eq_dec (bv_unsigned r0) 0) as [E0|E0]; [apply aget_zero; exact E0|].
        unfold chr_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset, (proj2 (Z.eqb_neq _ _) E0).
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { exfalso. apply Hr0. right. left. apply bv_eq. exact E10. }
        apply clob_out; [|exact E0]. intros X. apply Hr0. exact X.
      * intros r0 Hr0. unfold chr_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset.
        destruct (Z.eqb_spec (bv_unsigned r0) 0) as [E0|E0].
        { exfalso. unfold MCLOB in Hr0. cbn [In] in Hr0.
          destruct Hr0 as [X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]; rewrite <- X in E0; vm_compute in E0; discriminate E0. }
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { assert (r0 = 10%bv) by (apply bv_eq; symmetry; exact E10). subst r0. rewrite H10'.
          assert (Hv : bv_unsigned (s + Z_to_bv 64 (Z.of_nat (length bs)))%bv = str_addr ρ k + ρ (lenvar k)).
          { rewrite bv_add_unsigned, Hsa, Z_to_bv_unsigned, Hlen. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
            rewrite (Z.mod_small (ρ (lenvar k))) by lia. apply Z.mod_small. lia. }
          unfold strend. destruct Hk as [->|[-> H2]]; cbn [Z.eqb xv_val]; rewrite Hv; unfold smod, str_addr; rewrite teval_app;
            fold (sp_val ρ); [unfold t_ae0 | unfold t_ae01]; cbn [teval Z.eqb]; rewrite wZ_wofZ;
            [rewrite (Z.mod_small 184) by (unfold two64; lia) | rewrite (Z.mod_small 185) by (unfold two64; lia)].
          - rewrite Z.mod_small by (unfold two64; lia). lia.
          - destruct (Hq1 H2) as [Hl1 Hq1']. rewrite Z.mod_small by (unfold two64; lia). lia. }
        rewrite (clob_in' CHR_CLOB (a_regs A) r0); [exact I| exact Hr0 |exact E0].
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

End ChrSound.
