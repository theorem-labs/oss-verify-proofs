(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatSim StoreOk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import NodesCfg.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxHoBuild FxHandoff2 FxRun FxLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrGen BrDress.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common Require Import HoBridge.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Img.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsExit Require Import FePcs FeDefs FeLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fe_written (sp z : Z) : Prop :=
  (sp - FE_STK <= z < sp) \/ In (z / 4096) FE_WR_PAGES \/ (FE_SH_LO <= z < FE_SH_HI).

(* [comment removed for export] *)
Definition fe_rho (sp : Z) (R : bvmap 5 word) (t : int) : word :=
  if (t =? 2)%uint63 then Z_to_bv 64 (sp - FE_STK)
  else if ((100 <=? t) && (t <? 132))%uint63 then getr R (Z_to_bv 5 (to_Z t - 100))
  else Z_to_bv 64 0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FE.
  Variables (R : bvmap 5 word) (M : word -> option byte) (sp : Z).
  #[local] Notation RSEGS := ASEGS (only parsing).
  #[local] Notation rho := (fe_rho sp R).
  #[local] Notation ms := (mkst R (Z_to_bv 64 FE_ENTRY) M (seg_rom ASEGS)).

  Hypothesis Hra  : getr R 1 = Z_to_bv 64 FE_RET.
  Hypothesis Hsp  : getr R 2 = Z_to_bv 64 sp.
  Hypothesis Ha0  : getr R 10 = Z_to_bv 64 FE_GLB.
  Hypothesis Ha1  : getr R 11 = Z_to_bv 64 FE_NGLB.
  Hypothesis Hsp16 : sp mod 16 = 0.
  Hypothesis Hsplo : FE_SPLO <= sp - FE_STK.
  Hypothesis Hsphi : sp <= FE_SPHI.
  Hypothesis Hclear : forall lo hi i, In (lo, hi) FE_CLEAR -> lo <= i < hi -> M (Z_to_bv 64 i) = None.
  Hypothesis Hcells : forall a n v, In (a, n, v) FE_CELLS -> rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
  Hypothesis Hstk : forall i, 0 <= i < FE_STK -> store_ok RSEGS M (Z_to_bv 64 (sp - FE_STK + i)) 1 = true.
  Hypothesis Hsh  : forall i, 0 <= i < FE_SH_HI - FE_SH_LO -> store_ok RSEGS M (Z_to_bv 64 (FE_SH_LO + i)) 1 = true.

  Lemma rho0 : rho 0%uint63 = Z_to_bv 64 0. Proof. reflexivity. Qed.
  Lemma rho_sp : rho T_SP = Z_to_bv 64 (sp - FE_STK). Proof. reflexivity. Qed.
  Lemma rho_sh : rho T_SH = Z_to_bv 64 0. Proof. reflexivity. Qed.
  Lemma rho_reg : forall r, 1 <= r <= 31 -> rho (T_REG r) = getr R (Z_to_bv 5 r).
  Proof.
    intros r Hr. unfold fe_rho, T_REG. rewrite HoBridge.to_Z_ioz by lia.
    replace ((ioz (100 + r) =? 2)%uint63) with false.
    2:{ symmetry. apply Uint63.eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite HoBridge.to_Z_ioz in E by lia. cbn in E. lia. }
    replace ((100 <=? ioz (100 + r))%uint63 && (ioz (100 + r) <? 132)%uint63) with true.
    2:{ symmetry. apply andb_true_iff. split; [apply Uint63.leb_spec | apply Uint63.ltb_spec]; rewrite HoBridge.to_Z_ioz by lia; cbn; lia. }
    f_equal. f_equal. lia.
  Qed.
  Lemma treg_lt : forall r, 1 <= r <= 31 -> to_Z (T_REG r) < 2 ^ 60.
  Proof. intros r Hr. unfold T_REG. rewrite HoBridge.to_Z_ioz by lia. lia. Qed.

  (* [comment removed for export] *)
  Lemma fe_hholds : Forall (hholds RSEGS rho ms) fe_facts.
  Proof.
    unfold fe_facts. pose proof FE_SPLO as dummy. unfold FE_SPLO, FE_SPHI, FE_STK in Hsplo, Hsphi, Hstk.
    repeat (apply Forall_app; split).
    - (* [comment removed for export] *)
      unfold fe_regs_opaque. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as (r & <- & Hr).
      assert (Hr31 : 1 <= r <= 31) by (cbn [In] in Hr; lia).
      rewrite <- (ireg_ioz r) by lia.
      apply (hreg_opaque_ok RSEGS rho R _ M); [apply treg_lt; exact Hr31 | apply rho_reg; exact Hr31].
    - (* [comment removed for export] *)
      unfold fe_regs. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
      + apply (hreg_ok RSEGS rho R _ M (1%bv : bv 5) 0%uint63 0 FE_RET FE_RET rho0); [reflexivity | lia | exact Hra].
      + apply (hreg_ok RSEGS rho R _ M (2%bv : bv 5) T_SP (sp - 512) FE_STK sp rho_sp); [reflexivity | unfold FE_STK; lia | exact Hsp].
      + apply (hreg_ok RSEGS rho R _ M (10%bv : bv 5) 0%uint63 0 FE_GLB FE_GLB rho0); [reflexivity | lia | exact Ha0].
      + apply (hreg_ok RSEGS rho R _ M (11%bv : bv 5) 0%uint63 0 FE_NGLB FE_NGLB rho0); [reflexivity | lia | exact Ha1].
    - (* [comment removed for export] *)
      unfold fe_clear. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as ([lo hi] & <- & Hin). cbn [fst snd].
      assert (Hb : 0 <= lo < 2 ^ 63 /\ 0 <= hi < 2 ^ 63).
      { unfold FE_CLEAR in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
      apply (hclear_ok RSEGS rho R _ M); [lia | lia |]. intros i Hi. exact (Hclear lo hi i Hin Hi).
    - (* [comment removed for export] *)
      unfold fe_cells. apply Forall_forall. intros f Hf. apply in_map_iff in Hf as ([[a n] v] & <- & Hin).
      assert (Hb : 0 <= a < 2 ^ 63 /\ (n <= 8)%nat /\ 0 <= v < 2 ^ 64).
      { unfold FE_CELLS in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <- <-; (split; [lia | split; [cbn; lia | lia]]). }
      apply (hcell_ok RSEGS rho R _ M 0%uint63 0 a a n v rho0); [lia | lia | tauto | lia |]. exact (Hcells a n v Hin).
    - (* [comment removed for export] *)
      unfold fe_geom. unfold FE_SH_LO, FE_SH_HI, FE_STK. repeat (apply Forall_cons; [ | ]); try apply Forall_nil.
      + apply (hregion_ok RSEGS rho R _ M T_SP (sp - 512)); [exact rho_sp | reflexivity | lia | lia | lia | lia | lia | lia |].
        change (2 ^ 4) with 16. rewrite <- Zminus_mod_idemp_l, Hsp16. reflexivity.
      + apply (hwr_ok_store RSEGS rho R _ M T_SP (sp - 512) (sp - 512)); [exact rho_sp | lia | lia | lia |].
        intros i Hi. apply Hstk. lia.
      + apply (hregion_ok RSEGS rho R _ M T_SH 0); [exact rho_sh | reflexivity | lia | lia | lia | lia | lia | lia | reflexivity].
      + apply (hwr_ok_store RSEGS rho R _ M T_SH 0 0x7fffa000); [exact rho_sh | lia | lia | lia |].
        intros i Hi. apply (Hsh i). unfold FE_SH_LO, FE_SH_HI. lia.
      + apply (hdisj_ok RSEGS rho R _ M 0%uint63 0 _ _ T_SP (sp - 512)); [exact rho0 | exact rho_sp | lia | lia | lia | lia | lia | lia | lia].
      + apply (hdisj_ok RSEGS rho R _ M 0%uint63 0 _ _ T_SH 0); [exact rho0 | exact rho_sh | lia | lia | lia | lia | lia | lia | lia].
      + apply (hdisj_ok RSEGS rho R _ M T_SH 0 _ _ T_SP (sp - 512)); [exact rho_sh | exact rho_sp | lia | lia | lia | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma claimed_start : forall x, claimed_wr IM rho (f_mem (state_of fe_desc)) x -> fe_written sp (bv_unsigned x).
  Proof.
    intros x Hc.
    destruct (wr_pages_sound ASEGS IM (mk_fimage_ok ASEGS IM IM_eq) rho fe_desc FE_WR_PAGES x rho0 fe_wr_ok Hc) as (r & Hr & Hcase).
    change (In r [RD 0%uint63 (ioz 0x10000) (ioz 0xc04000) 0%uint63 None fe_rw_pages;
                  RD T_SP 0%uint63 (ioz FE_STK) 4%uint63 (Some PKUnk) [];
                  RD T_SH (ioz FE_SH_LO) (ioz FE_SH_HI) 12%uint63 (Some PKUnk) []]) in Hr.
    cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]].
    - destruct Hcase as [[_ Hw] | [Hne _]]; [right; left; exact Hw|]. exfalso. apply Hne. reflexivity.
    - destruct Hcase as [[Ht _] | [_ (z & Hz & Hlo & ->)]].
      { exfalso. apply (f_equal to_Z) in Ht. cbn in Ht. discriminate Ht. }
      cbn [rd_len rd_tag rd_lo rd_pages] in Hz, Hlo |- *. rewrite HoBridge.to_Z_ioz in Hz by (unfold FE_STK; lia).
      left. unfold adr. rewrite rho_sp, bv_add_Z, u64z by (unfold FE_SPLO, FE_SPHI, FE_STK in *; lia). unfold FE_STK in *. lia.
    - destruct Hcase as [[Ht _] | [_ (z & Hz & Hlo & ->)]].
      { exfalso. apply (f_equal to_Z) in Ht. cbn in Ht. discriminate Ht. }
      cbn [rd_len rd_tag rd_lo rd_pages] in Hz, Hlo |- *. specialize (Hlo eq_refl).
      rewrite HoBridge.to_Z_ioz in Hz by (unfold FE_SH_HI; lia). rewrite HoBridge.to_Z_ioz in Hlo by (unfold FE_SH_LO; lia).
      right. right. unfold adr. rewrite rho_sh, bv_add_Z, u64z by (unfold FE_SH_LO, FE_SH_HI in *; lia). unfold FE_SH_LO, FE_SH_HI in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fe_run : exists R' M',
    msteps RSEGS ms (mkst R' (Z_to_bv 64 FE_RET) M' (seg_rom ASEGS))
    /\ getr R' 2 = Z_to_bv 64 sp
    /\ (forall r, In r FE_SAVED -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
    /\ (forall x : word, ~ fe_written sp (bv_unsigned x) -> M' x = M x)
    /\ mem_grows M M'.
  Proof.
    destruct (fx_block_sound ASEGS IM (mk_fimage_ok ASEGS IM IM_eq) (mk_fimage_wr_ok ASEGS IM IM_eq) fe_code
                (build_code_ok ASEGS fe_pcs fe_code fe_code_eq)
                fe_facts fe_desc fe_dress (ioz FE_RET) 20%nat rho ms FE_SAVED FE_STEPS FE_RET (FV T_SP (w_of_Z FE_STK))
                (map (fun r => FV (T_REG r) w_zero) FE_SAVED)
                ltac:(lia) fe_check fe_summary_ok rho0 fe_hholds)
      as (ms' & Hsteps & Hpc' & Hsvc' & Hresv' & Hfregs & Hfcsr & Hrom & Hsp' & Hsaved & Hfr & Hgrow).
    - unfold fe_dress. constructor; [|constructor]. cbn [ditem_ok]. rewrite rho_sh. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      split; [cbn; lia | exact I].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct ms' as [R' FR' pc' svc' resv' fcsr' M' rom'].
      cbn [ms_pc_val ms_svc_pending ms_resv ms_fregs ms_fcsr ms_rom ms_mem mkst] in Hpc', Hsvc', Hresv', Hfregs, Hfcsr, Hrom, Hfr, Hgrow, Hsteps.
      subst pc' svc' resv' FR' fcsr' rom'.
      exists R', M'. split; [exact Hsteps|]. split; [|split; [|split]].
      + rewrite rget_core_regs in Hsp'. cbn [ms_regs] in Hsp'. rewrite Hsp'.
        rewrite (dv_tag rho T_SP (sp - FE_STK) FE_STK ltac:(reflexivity) rho_sp). f_equal. lia.
      + intros r0 Hr0.
        assert (Hr31 : 1 <= r0 <= 31) by (unfold FE_SAVED in Hr0; cbn [In] in Hr0; lia).
        apply In_nth_error in Hr0 as (i & Hi).
        pose proof (Hsaved i r0 (FV (T_REG r0) w_zero) Hi ltac:(rewrite nth_error_map, Hi; reflexivity) ltac:(lia)) as Hv.
        rewrite rget_core_regs in Hv. cbn [ms_regs] in Hv. rewrite Hv.
        rewrite (dv_opaque rho (T_REG r0) (treg_lt r0 Hr31)). apply rho_reg. exact Hr31.
      + intros x Hx. apply Hfr. intros Hc. exact (Hx (claimed_start x Hc)).
      + exact Hgrow.
  Qed.
End FE.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
