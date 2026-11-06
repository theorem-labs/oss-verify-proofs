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
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep AsanWMemcpyF1 AsanWMemcpyF2.
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
Variable J : machine_state -> Prop.
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

End Loop.
End MCF.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
