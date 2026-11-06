(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep AsanWMemcpyF1 AsanWMemcpyF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Set Default Proof Using "All".

Lemma land3_small : forall a, (0 <= a)%Z -> (0 <= Z.land a 3 < 4)%Z.
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. apply Z.mod_pos_bound. lia. Qed.

Section MCF.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HF : MCFCode segs e.

Section Loop.
Variable model : Model.
Variable J : machine_state -> Prop.   (* [comment removed for export] *)
Hypothesis J_acc : forall ms ms' acc, ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh : m_halted model = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Hypothesis Hnls : no_lazy model src (src + n).
Hypothesis Hnld : no_lazy model dst (dst + n).
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms', MCRc MCF_CLOB ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> J ms'.

Let HC : MCCode segs e := mcf_al segs e HF.
Let AL120 := al120 segs e HC MCF_CLOB HCLF HCL1F model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok
             Hnls Hnld Hra HK.
Let src_rdF := src_rdF segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let sok_subF := sok_subF segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let copied_st := copied_st segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let len1F := len1F segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let fs_eq := fs_eq segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let b16 := b16 segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let tl60 := tl60 segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let PR1 := PR1 segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let PR2 := PR2 segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
Let PR3 := PR3 segs cfg e HF model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.

Local Ltac rdS Hf := cbn [msz_n]; eapply src_rdF; [exact Hf | lia | lia | lia].
Local Ltac acS NL := cbn [msz_n]; apply acc_ok_one; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                     [lia | eapply no_lazy_sub; [exact NL | lia | lia]].
Local Ltac okS Hf := cbn [msz_n]; eapply sok_subF; [exact Hf | lia | lia].
Local Ltac upd Hf c DT :=
  match goal with |- J (setx _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?data)) =>
    let Hf' := fresh "Hf" in
    pose proof (copied_st m _ a data c Hf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(DT)) as Hf'; clear Hf; rename Hf' into Hf
  end.
Local Ltac ld F D Hf := jl F D ltac:(rdS Hf) ltac:(acS Hnls).
Local Ltac st F D Hf c DT := js F D regX ltac:(okS Hf) ltac:(acS Hnld); upd Hf c DT.
Local Ltac dt1 := rewrite store1_load1 by (apply len1F; lia); apply fs_eq; lia.
Local Ltac ai F D := jr wacc_OpImm F D valX.
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

(* [comment removed for export] *)
Lemma m74 : forall S k, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x74 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 15 = Z_to_bv 64 (Z.land (dst + k) 3) -> (32 <= n - k)%Z -> (0 <= k)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k HS Hpc H11 H13 H12 H15 Hnk Hk Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (dst + k) ltac:(lia)).
  ld (FF_74 segs cfg e HF) DW_0005a703 Hf.
  ai (FF_78 segs cfg e HF) DW_00300813.
  jb2 (FF_7c segs cfg e HF) DW_11078e63; intros Hb; bnorm Hb.
  - apply (PR1 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
    rgn. rwregsX. rewrite lw_LWv. reflexivity.
  - ai (FF_80 segs cfg e HF) DW_00200813.
    jb2 (FF_84 segs cfg e HF) DW_19079c63; intros Hb'; bnorm Hb'.
    + apply (PR3 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
      rgn. rwregsX. rewrite lw_LWv. reflexivity.
    + apply (PR2 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | lia | cpX Hf ].
      rgn. rwregsX. rewrite lw_LWv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mis50 : forall S k, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x50 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 15 = Z_to_bv 64 (Z.land (dst + k) 3) -> (0 <= k <= n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k HS Hpc H11 H13 H12 H15 Hk Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  ai (FF_50 segs cfg e HF) DW_02000713.
  jb2 (FF_54 segs cfg e HF) DW_02e67063; intros Hb; bnorm Hb.
  - apply (m74 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | lia | lia | cpX Hf ].
  - ai (FF_58 segs cfg e HF) DW_01000713.
    jb2 (FF_5c segs cfg e HF) DW_24e67863; intros Hb'; bnorm Hb'.
    + apply (b16 _ k (n - k)); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | cpX Hf ].
    + apply (tl60 _ k (n - k)); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | | cpX Hf ].
      rewrite c16s by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma d48 : forall S k, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x48 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  (0 <= k <= n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k HS Hpc H11 H13 H12 Hk Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (dst + k) ltac:(lia)).
  jr wacc_OpImm (FF_48 segs cfg e HF) DW_0036f793 valA.
  jb2 (FF_4c segs cfg e HF) DW_0c078a63; intros Hb; bnorm Hb.
  - apply (AL120 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - apply (mis50 _ k); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

(* [comment removed for export] *)
Lemma al18 : forall (d : nat) S k, (n - k < Z.of_nat d)%Z ->
  MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x18 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 (n - k) ->
  rg S 14 = Z_to_bv 64 (src + k + 1) -> rg S 15 = Z_to_bv 64 1 -> (0 <= k < n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  induction d as [|d IH]; intros S k Hd HS Hpc H11 H13 H12 H14 H15 Hk Hf; [lia|].
  pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (land3_small (src + k + 1) ltac:(lia)).
  ld (FF_18 segs cfg e HF) DW_0005c883 Hf.
  ai (FF_1c segs cfg e HF) DW_00060813. ai (FF_20 segs cfg e HF) DW_00158593.
  jr wacc_OpImm (FF_24 segs cfg e HF) DW_00377293 valA.
  st (FF_28 segs cfg e HF) DW_01168023 Hf 1%nat dt1.
  ai (FF_2c segs cfg e HF) DW_00168693. ai (FF_30 segs cfg e HF) DW_fff60613.
  jb2 (FF_34 segs cfg e HF) DW_00028a63; intros Hb; bnorm Hb.
  - apply (d48 _ (k + 1)%Z); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - ai (FF_38 segs cfg e HF) DW_00170713.
    jb2 (FF_3c segs cfg e HF) DW_fcf81ee3; intros Hb'; bnorm Hb'.
    + apply (IH _ (k + 1)%Z); [ lia | mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | regZ | lia | cpX Hf ].
    + jj (FF_40 segs cfg e HF) DW_0080006f.
      apply (d48 _ (k + 1)%Z); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

(* [comment removed for export] *)
Lemma mcf_entry :
  ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw e 0 ->
  rg ms0 10 = Z_to_bv 64 dst -> rg ms0 11 = Z_to_bv 64 src -> rg ms0 12 = Z_to_bv 64 n ->
  J ms0.
Proof.
  intros Hsvc Hpc H10 H11 H12. pose proof (MCR_refl MCF_CLOB ms0 Hsvc) as HS.
  pose proof (land3_small src Hs0). pose proof (land3_small dst Hd0).
  assert (Hf : copied (ms_mem ms0) (ms_mem ms0) dst 0 bs) by apply copied_refl.
  jr wacc_OpImm (FC_0 segs e HC) DC_0 valA.
  jb2 (FC_4 segs e HC) DC_4; intros Hb; bnorm Hb.
  - (* [comment removed for export] *)
    ai (FC_114 segs e HC) DC_114.
    jr wacc_OpImm (FC_118 segs e HC) DC_118 valA.
    jb2 (FC_11c segs e HC) DC_11c; intros Hb'; bnorm Hb'.
    + apply (mis50 _ 0%Z); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | | lia | cpX Hf ].
      rgn. rwregsX. rewrite Z.add_0_r. reflexivity.
    + apply (AL120 _ 0%Z); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
  - jb2 (FF_8 segs cfg e HF) DW_02060e63; intros Hb'; bnorm Hb'.
    + (* [comment removed for export] *)
      ai (FF_44 segs cfg e HF) DW_00050693.
      apply (d48 _ 0%Z); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | cpX Hf ].
    + ai (FF_c segs cfg e HF) DW_00158713. ai (FF_10 segs cfg e HF) DW_00100793. ai (FF_14 segs cfg e HF) DW_00050693.
      apply (al18 (Z.to_nat n + 1) _ 0%Z); [ lia | mcf_chain HS | reflexivity | regZ | regZ | regZ | regZ | regZ | lia | cpX Hf ].
Qed.

End Loop.
End MCF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem memcpy_sum_J : forall (segs : list Segment) (e : Z), MCFCode segs e ->
  forall (model : Model) (J : machine_state -> Prop),
  (forall ms ms' acc, ms_svc_pending ms = None ->
     step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms) ->
  forall (ms : machine_state) (dst src n : Z) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (0 <= dst)%Z -> (0 <= src)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  (src + n <= dst \/ dst + n <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  no_lazy model src (src + n) -> no_lazy model dst (dst + n) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', MCRc MCF_CLOB ms ms' -> copied (ms_mem ms') (ms_mem ms) dst n bs ->
     ms_pc_val ms' = rg ms 1 -> J ms') ->
  J ms.
Proof.
  intros segs e HF model J J_acc ms dst src n bs Hsvc Hpc Hh H10 H11 H12 Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK.
  exact (mcf_entry segs (mkSpuriousCfg false false false false false false) e HF model J J_acc ms dst src n bs
           Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok Hnls Hnld Hra HK Hsvc Hpc H10 H11 H12).
Qed.

Theorem memcpy_sum : forall (segs : list Segment) (cfg : SpuriousCfg) (e : Z), MCFCode segs e ->
  forall (ms : machine_state) (model : Model) (K : TSet) (dst src n : Z) (bs : list byte),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw e 0 -> m_halted model = None ->
  rg ms 10 = Z_to_bv 64 dst -> rg ms 11 = Z_to_bv 64 src -> rg ms 12 = Z_to_bv 64 n ->
  (0 <= dst)%Z -> (0 <= src)%Z -> (0 <= n)%Z -> (dst + n <= 2 ^ 47)%Z -> (src + n <= 2 ^ 47)%Z ->
  (src + n <= dst \/ dst + n <= src)%Z ->
  rdn segs (ms_mem ms) (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
  store_ok segs (ms_mem ms) (Z_to_bv 64 dst) (Z.to_nat n) = true ->
  no_lazy model src (src + n) -> no_lazy model dst (dst + n) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', MCRc MCF_CLOB ms ms' -> copied (ms_mem ms') (ms_mem ms) dst n bs ->
     ms_pc_val ms' = rg ms 1 -> realizes_cfg segs cfg (mkCfg ms' model) K) ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros segs cfg e HF ms model K dst src n bs Hsvc Hpc Hh.
  exact (memcpy_sum_J segs e HF model (fun S => realizes_cfg segs cfg (mkCfg S model) K)
           (fun ms0 ms' acc => rzc_acc segs cfg ms0 model ms' acc K Hh) ms dst src n bs Hsvc Hpc Hh).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
