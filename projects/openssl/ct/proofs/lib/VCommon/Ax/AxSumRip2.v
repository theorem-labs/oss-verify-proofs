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
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanWEntry AxSum AsanSWord AsanSMiz AsanSRipA AsanSMat AsanSRipC AxTabs.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition xb_is_zero (x : xb) : bool := match x with BL c => (c =? 0)%uint63 | _ => false end.

(* [comment removed for export] *)
Definition mk_addr (ts : terms) (w : w64) : xv := match ts with [] => XL w | _ => XS ts w end.

Lemma mk_addr_val (ρ : valuation) (ts : terms) (w : w64) (a : bv 64) : bv_unsigned a = smod ρ ts w -> xv_val ρ (mk_addr ts w) a.
Proof.
  intros H. unfold mk_addr. destruct ts as [|t r]; [|exact H].
  cbn [xv_val]. rewrite H. unfold smod. cbn [teval]. rewrite Z.add_0_l. apply Z.mod_small. apply wZ_range.
Qed.

Definition sh_zero (segs : list Segment) (s : store) (mem : list region) (ts : terms) (o n : Z) : bool :=
  let f0 := o / 8 in
  let L := (o + n - 1) / 8 - f0 + 1 in
  tdiv8_ok ts &&& (1 <=? L) &&& (L <? 1000) &&&
  match a_load4 segs s mem (mk_addr (tdiv8 ts) (wofZ (0x7fff8000 + f0))) (Z.to_nat L) with
  | Some l => forallb xb_is_zero l
  | None => false
  end.

Lemma sh_zero_sound (segs : list Segment) (ρ : valuation) (s : store) (A : list region) (m : word -> option byte)
    (ts : terms) (o n : Z) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> sh_zero segs s A ts o n = true ->
  0 <= teval ρ ts + o -> teval ρ ts + o + n <= 2 ^ 47 -> 1 <= n ->
  forall q, 0x7fff8000 + (teval ρ ts + o) / 8 <= q <= 0x7fff8000 + (teval ρ ts + o + n - 1) / 8 ->
    bat segs m (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Proof.
  intros Hlow Hs HM Hhs H Hb0 Hb1 Hn q Hq. unfold sh_zero in H. cbv zeta in H.
  apply land_true in H as [H Hl]. apply land_true in H as [H HL2]. apply land_true in H as [Ht HL1].
  apply Z.leb_le in HL1. apply Z.ltb_lt in HL2.
  set (L := (o + n - 1) / 8 - o / 8 + 1) in *.
  destruct (a_load4 segs s A (mk_addr (tdiv8 ts) (wofZ (0x7fff8000 + o / 8))) (Z.to_nat L)) as [l|] eqn:El; [|discriminate].
  rewrite (teval_tdiv8 ρ ts Ht) in *. set (T := teval ρ (tdiv8 ts)) in *.
  assert (E0 : (8 * T + o) / 8 = T + o / 8) by (replace (8 * T + o) with (o + T * 8) by ring; rewrite Z.div_add by lia; ring).
  assert (E1 : (8 * T + o + n - 1) / 8 = T + (o + n - 1) / 8).
  { replace (8 * T + o + n - 1) with ((o + n - 1) + T * 8) by ring. rewrite Z.div_add by lia. ring. }
  rewrite E0, E1 in Hq.
  assert (Hbeg8 : 0 <= T + o / 8) by (rewrite <- E0; apply Z.div_pos; lia).
  assert (Hend8 : T + (o + n - 1) / 8 < 2 ^ 44) by (rewrite <- E1; apply Z.div_lt_upper_bound; lia).
  set (a0 := Z_to_bv 64 (0x7fff8000 + (T + o / 8))).
  assert (Ha0 : bv_unsigned a0 = 0x7fff8000 + (T + o / 8)) by (apply u_wz; lia).
  assert (Hav : bv_unsigned a0 = smod ρ (tdiv8 ts) (wofZ (0x7fff8000 + o / 8))).
  { rewrite Ha0. unfold smod. fold T. rewrite wZ_wofZ, Zplus_mod_idemp_r. rewrite Z.mod_small by (unfold two64; lia). ring. }
  destruct (a_load4_sound segs ρ s A m _ a0 (Z.to_nat L) l Hlow Hs HM Hhs (mk_addr_val ρ _ _ a0 Hav) ltac:(lia) El) as [bs [Hrd Hf2]].
  set (j := Z.to_nat (q - bv_unsigned a0)).
  assert (Hj : (j < Z.to_nat L)%nat) by (unfold j; lia).
  pose proof (bat_of_rdn segs m _ a0 bs j Hrd Hj) as Hbat.
  assert (Eq : (a0 + Z_to_bv 64 (Z.of_nat j))%bv = Z_to_bv 64 q).
  { apply bv_eq. rewrite bv_add_unsigned, Ha0, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    unfold j. rewrite Ha0. rewrite Z2Nat.id by lia. rewrite (Z.mod_small (q - _)) by lia.
    f_equal. ring. }
  rewrite Eq in Hbat. rewrite Hbat. f_equal.
  pose proof (Forall2_length Hf2) as Hlen. pose proof (a_load4_length segs s A _ _ l El) as Hll.
  assert (Hjl : (j < length l)%nat) by lia.
  rewrite forallb_forall in Hl.
  pose proof (Hl (nth j l BT) (nth_In l BT Hjl)) as Hz.
  assert (Hnth : xb_bv ρ (nth j l BT) (nth j bs (Z_to_bv 8 0))).
  { assert (G : forall k, (k < length l)%nat -> xb_bv ρ (nth k l BT) (nth k bs (Z_to_bv 8 0))).
    { clear -Hf2. induction Hf2 as [|x b l' bs' Hxb Hr IH]; intros k Hk; [cbn in Hk; lia|].
      destruct k as [|k]; [exact Hxb|]. cbn [nth]. apply IH. cbn [length] in Hk. lia. }
    exact (G j Hjl). }
  destruct (nth j l BT) as [c| |]; try discriminate Hz. cbn [xb_is_zero] in Hz. apply Uint63.eqb_spec in Hz. subst c.
  unfold xb_bv, xb_z in Hnth. apply bv_eq. rewrite Hnth. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sum_rip2_g (ckR : (list Segment -> Z -> Z -> Z -> Z -> Z -> Z -> bool)) (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  let s := a_facts A in
  match rip_params T b, xaddr (aget (a_regs A) 10%uint63), xlit (aget (a_regs A) 11%uint63), aget (a_regs A) 1%uint63,
        aget (a_regs A) 2%uint63, find_entry (a_mem A) with
  | Some (mz, gK, gMB, gME, gHE, aK, aMB, aME, aHE), Some (tb, ob), Some n, XL r, XS ts o, Some ph =>
      if (1 <=? n) &&& (n <? 7000) &&& teqb ts sp_terms &&& (- 8388608 + 72 <=? wS o) &&& (wS o <=? 0)
         &&& pc_ok r &&& atop_is_sp (a_model A) &&& (a_budget A + 4096 * rpg n <=? LIM)
         &&& in_app_mem s (wS ob, tb) n
         &&& ckR segs b mz gK gMB gME gHE &&& globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE
         &&& sh_zero segs s (a_mem A) tb (wS ob) n then
        match a_store segs (a_mem A) (XS sp_terms (wofZ (wS o - 72))) (repeat BT 72) with
        | Some mem' =>
            Some [AS r (rip_regs (a_regs A)) (resv_drop (a_resv A)) mem' s (a_model A) (a_budget A + 4096 * rpg n) (a_steps A + 1)]
        | None => None
        end
      else None
  | _, _, _, _, _, _ => None
  end.

Definition sum_rip2 (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) : option (list AST) :=
  sum_rip2_g rip_code_okf T segs LIM A.

Lemma sum_rip2_g_ck (T : img_tabs) (segs : list Segment) (LIM : Z) (A : AST) (l : list AST) :
  rip_ck T segs (wZ (a_pc A)) = true -> sum_rip2_g ck_true6 T segs LIM A = Some l -> sum_rip2 T segs LIM A = Some l.
Proof.
  intros Hck H. unfold sum_rip2, sum_rip2_g in *. cbv zeta in *. unfold rip_ck in Hck. unfold ck_true6 in H.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|]; [|exact H]. rewrite Hck. exact H.
Qed.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Rip2Sound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_rip2_sound (A : AST) (l : list AST) : sum_rip2 T segs LIM A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_rip2, sum_rip2_g in Hs.
  destruct (rip_params T (wZ (a_pc A))) as [[[[[[[[[mz gK] gMB] gME] gHE] aK] aMB] aME] aHE]|] eqn:Ep; [|discriminate].
  destruct (xaddr (aget (a_regs A) 10%uint63)) as [[tb ob]|] eqn:Eb10; [|discriminate].
  destruct (xlit (aget (a_regs A) 11%uint63)) as [n|] eqn:E11; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [r| | | | |] eqn:E1; try discriminate.
  destruct (aget (a_regs A) 2%uint63) as [| ts o | | | |] eqn:E2; try discriminate.
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  cbv zeta in Hs.
  destruct (1 <=? n) eqn:En1; [|discriminate]. apply Z.leb_le in En1.
  destruct (n <? 7000) eqn:En2; [|discriminate]. apply Z.ltb_lt in En2.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 + 72 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct (pc_ok r) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (a_budget A + 4096 * rpg n <=? LIM) eqn:Hbud; [|discriminate]. apply Z.leb_le in Hbud.
  destruct (in_app_mem (a_facts A) (wS ob, tb) n) eqn:Ern;
    [|discriminate].
  destruct (rip_code_okf segs (wZ (a_pc A)) mz gK gMB gME gHE) eqn:Hcode; [|discriminate]. apply rip_code_okf_ok in Hcode.
  destruct (globals_ok segs (a_mem A) gK gMB gME gHE aK aMB aME aHE) eqn:Hglob; [|discriminate].
  destruct (sh_zero segs (a_facts A) (a_mem A) tb (wS ob) n) eqn:Hsh; [|discriminate].
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
  (* [comment removed for export] *)
  assert (Hbv : bv_unsigned beg = smod ρ tb ob).
  { apply (xaddr_val ρ (aget (a_regs A) 10%uint63) beg tb ob); [|exact Eb10]. exact (Hregs 10%bv). }
  set (F := leval ρ (wS ob, tb)) in *.
  assert (HF : (0x10007fff8000 <= F /\ F + n + 8 <= 2 ^ 47) \/ (0 <= F /\ F + n + 8 <= 0x7fff8000)).
  { pose proof (in_app_mem_sound ρ _ _ _ Hsat Ern) as X. fold F in X. lia. }
  assert (HFe : F = teval ρ tb + wS ob) by (unfold F, leval; cbn [fst snd]; ring).
  assert (Hbeg : bv_unsigned beg = F).
  { rewrite Hbv. unfold smod. rewrite <- (wS_mod ob). rewrite Zplus_mod_idemp_r. rewrite <- HFe.
    apply Z.mod_small. unfold two64. lia. }
  assert (H11 : rg ms 11%bv = Z_to_bv 64 n).
  { apply word_lit_w. exact (reg_lit ρ (a_regs A) ms 11%bv 11%uint63 n Hregs eq_refl E11). }
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
    exact (sh_zero_sound segs ρ (a_facts A) (a_mem A) (ms_mem ms) tb (wS ob) n Hlow Hsat Hmem Hhs Hsh ltac:(lia) ltac:(lia) En1 q Hq).
  - destruct Hb as [Hb1 Hb2]. rewrite Hb2. lia.
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

End Rip2Sound.
