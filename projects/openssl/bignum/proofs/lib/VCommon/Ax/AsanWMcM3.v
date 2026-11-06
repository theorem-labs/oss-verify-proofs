(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep AsanWMemcpyF1 AsanWMemcpyF2 AsanWMemcpyF3 AsanSMat AsanWMat AsanWMcM0 AsanWMcM1 AsanWMcM2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Set Default Proof Using "All".

Section MCFM.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HF : MCFCode segs e.

Section LoopM.
Variable model0 : Model.
Variable K : TSet.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Let L : list word := range_pages src (Z.to_nat n) ++ range_pages dst (Z.to_nat n).
Hypothesis Hbud : (vm_backing_used model0 + Z.of_nat (length L) * page_size <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms' m', MCRc MCF_CLOB ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> matin model0 m' L -> realizes_cfg segs cfg (mkCfg ms' m') K.

Let HC : MCCode segs e := mcf_al segs e HF.
Let AL120 := al120m segs cfg e HC MCF_CLOB HCLF HCL1F model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let src_rdM := src_rdM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let sok_subM := sok_subM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let copied_stM := copied_stM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let len1M := len1M segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let fs_eqM := fs_eqM segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let b16m := b16m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let tl60m := tl60m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let PR1m := PR1m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let PR2m := PR2m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
Let PR3m := PR3m segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.

Let mhaltF := mhaltF segs cfg e HF model0 K ms0 dst src n bs Hh0 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.

Local Ltac mnext := let m' := fresh "mdl" in let H' := fresh "Hmn" in intros m' H';
  repeat match goal with
         | H : matin model0 ?x L |- _ => lazymatch x with m' => fail | _ => clear H end
         | H : m_halted ?x = None |- _ => lazymatch x with m' => fail | model0 => fail | _ => clear H end
         end;
  let Hm := fresh "Hm" in rename H' into Hm; let Hh := fresh "Hhm" in pose proof (mhaltF m' Hm) as Hh.

Local Ltac rdS Hf := cbn [msz_n]; eapply src_rdM; [exact Hf | lia | lia | lia].
Local Ltac inS := cbn [msz_n]; apply incl_appl; apply range_pages_incl; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                   rewrite ?Z2Nat.id by lia; lia.
Local Ltac inD := cbn [msz_n]; apply incl_appr; apply range_pages_incl; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                   rewrite ?Z2Nat.id by lia; lia.
Local Ltac okS Hf := cbn [msz_n]; eapply sok_subM; [exact Hf | lia | lia].
Local Ltac upd Hf c DT :=
  match goal with |- realizes_cfg _ _ (mkCfg (setx _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?data)) _) _ =>
    let Hf' := fresh "Hf" in
    pose proof (copied_stM m _ a data c Hf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(DT)) as Hf'; clear Hf; rename Hf' into Hf
  end.
Local Ltac ld F D Hf :=
  eapply (xs_ld_in segs cfg model0 _ L); [ exact Hh0 | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | memX
                                          | rdS Hf | inS | exact Hbud | pcX | resvX | ]; mnext.
Local Ltac st F D Hf c DT :=
  eapply (xs_st_in segs cfg model0 _ L); [ exact Hh0 | assumption | svcX | ftacX F | ecX | exact D | regX | addrX | regX | memX
                                          | okS Hf | inD | exact Hbud | pcX | resvX | ]; mnext; upd Hf c DT.
Local Ltac dt1 := rewrite store1_load1 by (apply len1M; lia); apply fs_eqM; lia.
Local Ltac ai F D := wr wacc_OpImm F D valX.
Local Ltac regZ := rgn; rwregsX; first [ reflexivity | f_equal; lia ].
Local Ltac bnorm Hb := unfold w0 in Hb;
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lia;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb;
  first [ apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb | apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb | idtac ].
Local Ltac valA := rgn; rwregsX; rewrite alu_andi_z by (lits; lia); lits; reflexivity.
Local Ltac cpX Hf := rewrite ?mem_setx;
  lazymatch type of Hf with copied _ _ _ ?k1 _ =>
    lazymatch goal with |- copied _ _ _ ?k2 _ => replace k2 with k1 by lia; exact Hf end end.
Local Ltac FFx o := exact (o segs cfg e HF).

Lemma m74m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x74 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 15 = Z_to_bv 64 (Z.land (dst + k) 3) -> (32 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 H15 Hnk Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (dst + k) ltac:(lia)).
  ld (FF_74 segs cfg e HF) DW_0005a703 Hf.
  ai (FF_78 segs cfg e HF) DW_00300813.
  wb2 (FF_7c segs cfg e HF) DW_11078e63; intros Hb; bnorm Hb.
  - apply (PR1m _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
    rgn. rwregsX. rewrite lw_LWv. reflexivity.
  - ai (FF_80 segs cfg e HF) DW_00200813.
    wb2 (FF_84 segs cfg e HF) DW_19079c63; intros Hb'; bnorm Hb'.
    + apply (PR3m _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
      rgn. rwregsX. rewrite lw_LWv. reflexivity.
    + apply (PR2m _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
      rgn. rwregsX. rewrite lw_LWv. reflexivity.
Qed.

Lemma mis50m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x50 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 15 = Z_to_bv 64 (Z.land (dst + k) 3) -> (0 <= k <= n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 H15 Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  ai (FF_50 segs cfg e HF) DW_02000713.
  wb2 (FF_54 segs cfg e HF) DW_02e67063; intros Hb; bnorm Hb.
  - apply (m74m _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | lia | lia | cpX Hf ].
  - ai (FF_58 segs cfg e HF) DW_01000713.
    wb2 (FF_5c segs cfg e HF) DW_24e67863; intros Hb'; bnorm Hb'.
    + apply (b16m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | cpX Hf ].
    + apply (tl60m _ k (n - k) _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | | cpX Hf ].
      rewrite c16s by lia. lia.
Qed.

Lemma d48m : forall S k m, matin model0 m L -> MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x48 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (0 <= k <= n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  intros S k m Hm HS Hpc H11 H13 H12 Hk Hf. pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (dst + k) ltac:(lia)).
  wr wacc_OpImm (FF_48 segs cfg e HF) DW_0036f793 valA.
  wb2 (FF_4c segs cfg e HF) DW_0c078a63; intros Hb; bnorm Hb.
  - apply (AL120 _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - apply (mis50m _ k _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

Lemma al18m : forall (d : nat) S k m, matin model0 m L -> (n - k < Z.of_nat d)%Z ->
  MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x18 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = Z_to_bv 64 (src + k + 1) -> rg S 15 = Z_to_bv 64 1 -> (0 <= k < n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> realizes_cfg segs cfg (mkCfg S m) K.
Proof.
  induction d as [|d IH]; intros S k m Hm Hd HS Hpc H11 H13 H12 H14 H15 Hk Hf; [lia|].
  pose proof (mhaltF m Hm) as Hhm. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (src + k + 1) ltac:(lia)).
  ld (FF_18 segs cfg e HF) DW_0005c883 Hf.
  ai (FF_1c segs cfg e HF) DW_00060813. ai (FF_20 segs cfg e HF) DW_00158593.
  wr wacc_OpImm (FF_24 segs cfg e HF) DW_00377293 valA.
  st (FF_28 segs cfg e HF) DW_01168023 Hf 1%nat dt1.
  ai (FF_2c segs cfg e HF) DW_00168693. ai (FF_30 segs cfg e HF) DW_fff60613.
  wb2 (FF_34 segs cfg e HF) DW_00028a63; intros Hb; bnorm Hb.
  - apply (d48m _ (k + 1)%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - ai (FF_38 segs cfg e HF) DW_00170713.
    wb2 (FF_3c segs cfg e HF) DW_fcf81ee3; intros Hb'; bnorm Hb'.
    + apply (IH _ (k + 1)%Z _ Hm); [ lia | mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | regZ | lia | cpX Hf ].
    + wj (FF_40 segs cfg e HF) DW_0080006f.
      apply (d48m _ (k + 1)%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

Lemma mcf_entrym :
  ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw e 0 ->
  rg ms0 10 = Z_to_bv 64 dst -> rg ms0 11 = Z_to_bv 64 src -> rg ms0 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg ms0 model0) K.
Proof.
  intros Hsvc Hpc H10 H11 H12. pose proof (MCR_refl MCF_CLOB ms0 Hsvc) as HS.
  pose proof (matin_refl model0 L) as Hm. pose proof Hh0 as Hhm.
  pose proof (land3_small src Hs0). pose proof (land3_small dst Hd0).
  assert (Hf : copied (ms_mem ms0) (ms_mem ms0) dst 0 bs) by apply copied_refl.
  wr wacc_OpImm (FC_0 segs e HC) DC_0 valA.
  wb2 (FC_4 segs e HC) DC_4; intros Hb; bnorm Hb.
  -
    ai (FC_114 segs e HC) DC_114.
    wr wacc_OpImm (FC_118 segs e HC) DC_118 valA.
    wb2 (FC_11c segs e HC) DC_11c; intros Hb'; bnorm Hb'.
    + apply (mis50m _ 0%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | cpX Hf ].
      rgn. rwregsX. rewrite Z.add_0_r. reflexivity.
    + apply (AL120 _ 0%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - wb2 (FF_8 segs cfg e HF) DW_02060e63; intros Hb'; bnorm Hb'.
    +
      ai (FF_44 segs cfg e HF) DW_00050693.
      apply (d48m _ 0%Z _ Hm); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
    + ai (FF_c segs cfg e HF) DW_00158713. ai (FF_10 segs cfg e HF) DW_00100793. ai (FF_14 segs cfg e HF) DW_00050693.
      apply (al18m (Z.to_nat n + 1) _ 0%Z _ Hm); [ lia | mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

End LoopM.
End MCFM.

Definition mc_pages (n : Z) : Z := (2 * (n / 4096 + 2))%Z.

Lemma mc_pages_L : forall src dst n, (0 <= src)%Z -> (0 <= dst)%Z -> (0 <= n)%Z ->
  (src + n <= 2 ^ 47)%Z -> (dst + n <= 2 ^ 47)%Z ->
  (Z.of_nat (length (range_pages src (Z.to_nat n) ++ range_pages dst (Z.to_nat n))) <= mc_pages n)%Z.
Proof.
  intros src dst n Hs Hd Hn Hsn Hdn. rewrite length_app, Nat2Z.inj_add. unfold mc_pages.
  pose proof (range_pages_length src (Z.to_nat n) Hs ltac:(lia)) as H1.
  pose proof (range_pages_length dst (Z.to_nat n) Hd ltac:(lia)) as H2.
  rewrite Z2Nat.id in H1, H2 by lia. lia.
Qed.

Theorem memcpy_sum_mat : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MCFCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst src n : Z) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (0 <= dst)%Z -> (0 <= src)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  (src + n <= dst \/ dst + n <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  (vm_backing_used model + mc_pages n * page_size <= vm_limit (m_vmmaps model))%Z ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms' model', MCRc MCF_CLOB ms ms' -> copied (ms_mem ms') (ms_mem ms) dst n bs ->
     ms_pc_val ms' = rg ms 1 -> mat_of model model' (mc_pages n) -> realizes_cfg segs cfg (mkCfg ms' model') K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HF ms model K dst src n bs Hsvc Hpc Hh H10 H11 H12 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud Hra HK.
  pose proof (mc_pages_L src dst n Hs0 Hd0 Hn Hsn Hdn) as HL.
  assert (Hbud' : (vm_backing_used model + Z.of_nat (length (range_pages src (Z.to_nat n) ++ range_pages dst (Z.to_nat n)))
                     * page_size <= vm_limit (m_vmmaps model))%Z) by (unfold page_size in *; lia).
  refine (mcf_entrym segs cfg e HF model K ms dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hbud' Hra _
           Hsvc Hpc H10 H11 H12).
  intros ms' m' HS Hf Hp Hm. apply HK; [exact HS | exact Hf | exact Hp |].
  eapply mat_of_mono; [exact (matin_mat_of _ _ _ Hm) | exact HL].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
