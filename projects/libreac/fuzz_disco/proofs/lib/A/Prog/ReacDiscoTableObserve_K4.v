(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 111 of its 146 lines of code are new or changed and 34 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X ReacDiscoTableObserve_K6.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma seg_K4 : forall c, SegK5 B c -> SegK4 B c.
Proof.
intros c HK5 regs1 m1 md1 r HP HM H18 H19 H12 Hfd.
remember (RDO.kE (tT c) (tG c) (tnow c) r) as Tc eqn:HTc.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
pose proof (tm_Tl _ _ _ _ _ _ HM) as HTcl.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
destruct Hfd as (Hrn & Hm & Hb).
assert (Hr8 : 0 <= r < 8) by lia.
assert (LG4 : length (DTC.sub (tG c) 20 4) = 4%nat) by (apply length_sub_le; lia).
assert (LE48 : length (DTC.sub Tc (48 * r) 48) = 48%nat) by (apply length_sub_le; lia).
assert (B8 : base_val (tobs_env c regs1 Tc r) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM). apply unsigned_lit_small. lia. }
assert (B19 : base_val (tobs_env c regs1 Tc r) (Some 19%nat) = tt c + 48 * r).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl), H19. apply unsigned_lit_small. lia. }
pose proof (tobs_env_img c regs1 Tc r) as HEI.
assert (H18' : YK11.getr regs1 18 = w64 (ts c - 0)) by (rewrite H18; f_equal; lia).
destruct (tobs_enter B c regs1 m1 md1 Tc 0x5358 true r 0 HP HM (or_introl eq_refl) H18' (fun _ => conj Hr8 H19))
  as [HS SHOK].
pose proof HS as HS0.
unfold cfgB.
paj_run_tok RUN HS HJ SHOK TBspan; [t456_awr B c HP B8 B19 Hr8 0 r |].
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg ?ms0 ?md0) _ =>
  assert (HM1 : tobs_m B c regs1 (ms_mem ms0) md0 Tc)
    by t456_mid B LAWS c regs1 Tc r HP HM B8 B19 Hr8 HS HFr HG HJ (ms_mem ms0) md0 end.
clear HF HFr HG.
destruct (TM.stage_reads (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr8) as (_ & _ & _ & _ & _ & _ & S7 & _ & _).
rewrite <- HTc in S7.
psrr_branch_tok RUN BR HS SHOK TBspan.
- rewrite branch_geu_U, !t456_U_sx in Hc.
  rewrite (t456_dw_ent _ 2 20 Tc r) in Hc by (first [reflexivity | exact HTcl | lia]).
  rewrite (t456_dw _ 1 20 (tG c)) in Hc by reflexivity.
  rewrite t456_ltu in Hc by apply RDO.u32_range. rewrite S7 in Hc. apply negb_true_iff in Hc.
  assert (HcC : RDO.cC (tT c) (tG c) r = false) by exact Hc.
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x539c; [t456_awr B c HP B8 B19 Hr8 0 r |].
  rewrite ?wvb_collapse in HJ.
  prreg HS (18%bv : bv 5) G18r. prreg HS (19%bv : bv 5) G19r. prreg HS (12%bv : bv 5) G12r.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rg _ ?mm _) ?md) _ =>
    assert (HM2 : tobs_m B c rg mm md Tc) by t456_same B LAWS c regs1 Tc r HP HM1 B8 B19 Hr8 HS HS0 HFr HG HJ rg mm md;
    assert (HkF : RDO.kF (tT c) (tG c) (tnow c) r = Tc) by (unfold RDO.kF; rewrite HcC, <- HTc; reflexivity);
    rewrite <- HkF in HM2;
    apply (HK5 rg mm md r HP HM2);
    [ rewrite G18r, (tobs_env_reg c regs1 Tc r 18 18%bv eq_refl), H18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
    | rewrite G19r, (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl); exact H19
    | rewrite G12r, (tobs_env_reg c regs1 Tc r 12 12%bv eq_refl), H12; unfold tf5; rewrite HcC, orb_false_r; reflexivity
    | exact (conj Hrn (conj Hm Hb)) ]
  end.
- rewrite branch_geu_U, !t456_U_sx in Hc.
  rewrite (t456_dw_ent _ 2 20 Tc r) in Hc by (first [reflexivity | exact HTcl | lia]).
  rewrite (t456_dw _ 1 20 (tG c)) in Hc by reflexivity.
  rewrite t456_ltu in Hc by apply RDO.u32_range. rewrite S7 in Hc. apply negb_false_iff in Hc.
  assert (HcC : RDO.cC (tT c) (tG c) r = true) by exact Hc.
  assert (HLf : DTC.sub (DTC.upd Tc (48 * r + 20) (DTC.sub (tG c) 20 4)) (48 * r) 48 =
    DTC.upd (DTC.sub Tc (48 * r) 48) 20 (DTC.sub (tG c) 20 4))
    by exact (TM.ent_upd Tc (DTC.sub (tG c) 20 4) r 20 HTcl Hr8 ltac:(lia) ltac:(rewrite LG4; lia)).
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x539c; [t456_awr B c HP B8 B19 Hr8 0 r |].
  rewrite ?wvb_collapse in HJ.
  prreg HS (18%bv : bv 5) G18r. prreg HS (19%bv : bv 5) G19r. prreg HS (12%bv : bv 5) G12r.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Rh; cbn [ms_mem restrict] in Rh.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as Re; cbn [ms_mem restrict] in Re.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rg _ ?mm _) ?md) _ =>
  lazymatch type of HFr with frame_of ?E1 _ _ _ =>
  lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
    assert (HM2 : tobs_m B c rg mm md (DTC.upd Tc (48 * r + 20) (DTC.sub (tG c) 20 4)));
    [ apply (t456_exit B LAWS c regs1 _ _ Tc E1 E2 0 r rg mm md _ HP HM1 ltac:(t456_bv B8) ltac:(t456_bv B19) Hr8
        HFr HG HJ Rh ltac:(t456_bv B8) eq_refl);
      [ rewrite RDO.upd_len; [exact HTcl | lia | rewrite HTcl, LG4; lia]
      | intros i Hi Hn; apply TM.upd_nth_out; [lia | rewrite HTcl, LG4; lia | lia | rewrite LG4; lia]
      | rewrite HLf; apply (region_bytes E2 _ 19 0 48 0 48 _ (tt c + 48 * r) _ Re ltac:(t456_bv B19) ltac:(vm_compute; reflexivity));
        repeat apply Forall_cons; try apply Forall_nil;
        first
        [ apply (t456_cv_in _ _ _ _ 20 (DTC.sub (tG c) 20 4));
          [ lia | rewrite LG4, LE48; lia | lia | rewrite LG4; cbn [Z.of_N]; lia
          | intros i Hi; cbn [Z.of_N] in Hi; rewrite (t456_cbyte_sx _ _ 1 20 i (tG c)) by (first [reflexivity | lia | rewrite HGl; lia]);
            rewrite nth_error_sub by lia; f_equal; lia ]
        | apply (t456_cd_out _ _ _ (DTC.sub Tc (48 * r) 48));
          [ reflexivity | lia | lia | rewrite LG4, LE48; lia | intros k Hk; rewrite LG4; lia ] ]
      | t456_regs HS HS0 ]
    | ];
    assert (HkF : RDO.kF (tT c) (tG c) (tnow c) r = DTC.upd Tc (48 * r + 20) (DTC.sub (tG c) 20 4))
      by (unfold RDO.kF; rewrite HcC, <- HTc; reflexivity);
    rewrite <- HkF in HM2;
    apply (HK5 rg mm md r HP HM2);
    [ rewrite G18r, (tobs_env_reg c regs1 Tc r 18 18%bv eq_refl), H18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
    | rewrite G19r, (tobs_env_reg c regs1 Tc r 19 19%bv eq_refl); exact H19
    | unfold tf5; rewrite HcC, orb_true_r; exact G12r
    | exact (conj Hrn (conj Hm Hb)) ]
  end end end.
Qed.
End h.
End f.
End d.
