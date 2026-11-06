(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 154 of its 189 lines of code are new or changed and 34 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_K0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module DT := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table.
Module FM := OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib.Mem.
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
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Ltac k1_chain FR MG HJ :=
  match goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    tryif constr_eq HFr FR then fail else
  match goal with HG : mem_grows _ _ |- _ =>
    tryif constr_eq HG MG then fail else
  let FR' := fresh "FR'" in let MG' := fresh "MG'" in
  pose proof (tk_frame_step 64 _ _ _ _ _ _ _ FR HFr) as FR';
  specialize (FR' ltac:(tk_agree) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
  pose proof (mem_grows_trans _ _ _ MG HG) as MG';
  clear FR MG HFr HG; rename FR' into FR; rename MG' into MG
  end end;
  repeat match goal with H : frame_of _ _ (ms_mem _) (ms_mem _) |- _ => clear H end;
  repeat rewrite wvb_collapse in HJ.
Ltac k1_run c regs1 Tk r HP B8 B19 Hr HS HJ SHOK FR MG :=
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x52c8;
  [ apply (tk_awr B c (tobs_env c regs1 Tk r) _ _ r HP); [tk_agree | vm_compute; reflexivity | exact B8 | exact B19 | exact Hr]
  | k1_chain FR MG HJ ].
Ltac k1_split HS SHOK := psrr_branch_tok RUN BR HS SHOK TBspan.
Ltac k1_cv Hc c r Tk HTk Hr SR :=
  rewrite ?(tk_dG (tG c)) in Hc by reflexivity;
  rewrite ?(tk_dE Tk r) in Hc by first [reflexivity | exact HTk | exact Hr | lia];
  rewrite ?SR in Hc;
  cbn [sv_denot branch_taken] in Hc;
  rewrite ?RDO.eqb_u8, ?RDO.eqb_u8_0 in Hc;
  rewrite ?negb_true_iff, ?negb_false_iff in Hc.
Ltac k1_cg c Tk r Ef :=
  first
  [ apply cagree_cdata; [lia|]; intros ? ?;
    change (ed Ef 2) with (TM.ent Tk r); tk_nth; tk_close
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len Z.of_N] in Hii |- *;
    cbn [sv_denot];
    rewrite tk_byte_data by (first [lia | simpl; lia | change (ed Ef 1) with (tG c); simpl; lia]);
    change (ed Ef 1) with (tG c); tk_nth; rewrite nth_error_sub by lia; tk_close
  | let ii := fresh "ii" in let Hii := fresh "Hii" in
    intros ii Hii; cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len Z.of_N] in Hii |- *;
    assert (ii = 0) by lia; subst ii;
    cbn [sv_denot]; tk_nth; vm_compute; reflexivity ].
Ltac k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0 L HcD HS HJ FR MG :=
  let HL := fresh "HL" in
  assert (HL : TM.ent (RDO.kC (tT c) (tG c) (tnow c) r) r = L)
    by (rewrite (TM.ent_kC _ _ _ _ HTl HGl Hr), HcD; reflexivity);
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf) =>
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdf) _ =>
  let rg := eval vm_compute in (nth_error (ss_mem ssf) 2) in
  lazymatch rg with Some (YP09.mkRegion _ _ _ _ _ ?cs) =>
  let HCG := fresh "HCG" in let HM2 := fresh "HM2" in let HRK := fresh "HRK" in
  assert (HCG : Forall (cagree Ef (tt c + 48 * r) 0 L) cs)
    by (repeat apply Forall_cons; try apply Forall_nil; k1_cg c (RDO.kB (tT c) (tG c) (tnow c) r) r Ef);
  destruct (tk_exit B LAWS c regs1 m1 md1 (RDO.kB (tT c) (tG c) (tnow c) r) r msf mdf Ef ssf cs
    (RDO.kC (tT c) (tG c) (tnow c) r) L HP HM Hr H19 HS
    ltac:(tk_agree) FR MG HJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    LC Hout HL HCG ltac:(vm_compute; reflexivity)) as [HM2 HRK];
  pmkst HS;
  apply (HK _ _ _ r HP HM2);
  [ etransitivity; [exact (HRK 18 ltac:(cbn; tauto)) | exact H18]
  | etransitivity; [exact (HRK 19 ltac:(cbn; tauto)) | exact H19]
  | unfold tf2; rewrite HcD;
    first
    [ rewrite orb_true_r; rewrite (tk_reg_lit _ _ _ _ 12 1 HS ltac:(vm_compute; reflexivity)); reflexivity
    | rewrite orb_false_r; rewrite <- H12;
      eapply (tk_reg_same c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r _ _ _ _ 12 HS HR0);
      [ vm_compute; reflexivity | vm_compute; reflexivity | tk_agree ] ]
  | exact Hf ]
  end end end.
Lemma seg_K1 : forall c, SegK2 B c -> SegK1 B c.
Proof.
intros c HK regs1 m1 md1 r HP HM H18 H19 H12 Hf.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
pose proof (tp_Tl _ _ HP) as HTl. pose proof (tp_Gl _ _ HP) as HGl.
assert (Hr : 0 <= r < 8) by (destruct Hf as (Hr & _); lia).
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
destruct (TM.stage_len (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (LA & LB & LC & _).
destruct (TM.stage_reads (tT c) (tG c) (tow c) (tnow c) r HTl HGl Hr) as (_ & SR12 & SR13 & SR14 & _).
pose proof (tk_b8 B c regs1 m1 md1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP HM) as B8.
pose proof (tk_b19 B c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP Hr H19) as B19.
pose proof (tobs_env_img c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r) as HEI.
pose proof (tobs_regs_ok c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r (tm_s0 _ _ _ _ _ _ HM) (tm_s5 _ _ _ _ _ _ HM)
  (tm_s6 _ _ _ _ _ _ HM) (tm_s8 _ _ _ _ _ _ HM) ltac:(lia) ltac:(lia)) as HR0.
assert (Hout : forall i, 0 <= i < 400 -> ~ (48 * r <= i < 48 * r + 48) ->
  nth_error (RDO.kC (tT c) (tG c) (tnow c) r) (Z.to_nat i) = nth_error (RDO.kB (tT c) (tG c) (tnow c) r) (Z.to_nat i)).
{ intros i Hi He. destruct (TM.stage_out (tT c) (tG c) (tow c) (tnow c) r i HTl HGl Hr Hi He) as (_ & OB & OC & _).
  rewrite OB, OC. reflexivity. }
destruct (tobs_enter B c regs1 m1 md1 (RDO.kB (tT c) (tG c) (tnow c) r) 0x51b4 true r 0 HP HM ltac:(left; reflexivity)
  ltac:(rewrite H18; f_equal; lia) ltac:(intros _; split; [exact Hr | exact H19])) as [HS SHOK].
unfold cfgB.
paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x52c8.
{ exact (tobs_awr B c _ true 0 r HP B8 ltac:(intros _; split; [exact B19 | exact Hr])). }
rename HFr into FR. rename HG into MG. clear HF.
k1_split HS SHOK.
- k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR12.
  assert (HcD : RDO.cD (tT c) (tG c) r = false) by (unfold RDO.cD, DTC.s_hd; rewrite Hc; reflexivity).
  k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
  k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0
    (TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r) HcD HS HJ FR MG.
- k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR12. rename Hc into HcA.
  k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
  k1_split HS SHOK.
  + k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR12.
    assert (HcD : RDO.cD (tT c) (tG c) r = true) by (unfold RDO.cD, DTC.s_hd, DTC.hd_of; rewrite HcA, Hc; reflexivity).
    k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
    k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0
      (DTC.upd (DTC.upd (DTC.upd (TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r) 12 [Z_to_bv 8 1]) 13 (DTC.sub (tG c) 13 1)) 14 (DTC.sub (tG c) 14 1))
      HcD HS HJ FR MG.
  + k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR12. rename Hc into HcB.
    k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
    k1_split HS SHOK.
    * k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR13.
      assert (HcD : RDO.cD (tT c) (tG c) r = true)
        by (unfold RDO.cD, DTC.s_hd, DTC.hd_of, DTC.din_of, DTC.s_din; rewrite HcA, HcB, Hc; reflexivity).
      k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
      k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0
        (DTC.upd (DTC.upd (DTC.upd (TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r) 12 [Z_to_bv 8 1]) 13 (DTC.sub (tG c) 13 1)) 14 (DTC.sub (tG c) 14 1))
        HcD HS HJ FR MG.
    * k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR13. rename Hc into HcC.
      k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
      k1_split HS SHOK.
      -- k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR14.
         assert (HcD : RDO.cD (tT c) (tG c) r = false)
           by (unfold RDO.cD, DTC.s_hd, DTC.hd_of, DTC.din_of, DTC.s_din, DTC.dout_of, DTC.s_dout; rewrite HcA, HcB, HcC, Hc; reflexivity).
         k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
         k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0
           (TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r) HcD HS HJ FR MG.
      -- k1_cv Hc c r (RDO.kB (tT c) (tG c) (tnow c) r) LB Hr SR14.
         assert (HcD : RDO.cD (tT c) (tG c) r = true)
           by (unfold RDO.cD, DTC.s_hd, DTC.hd_of, DTC.din_of, DTC.s_din, DTC.dout_of, DTC.s_dout; rewrite HcA, HcB, HcC, Hc; reflexivity).
         k1_run c regs1 (RDO.kB (tT c) (tG c) (tnow c) r) r HP B8 B19 Hr HS HJ SHOK FR MG.
         k1_fin c regs1 m1 md1 r HK HP HM Hf H18 H19 H12 HTl HGl Hr LC Hout HR0
           (DTC.upd (DTC.upd (DTC.upd (TM.ent (RDO.kB (tT c) (tG c) (tnow c) r) r) 12 [Z_to_bv 8 1]) 13 (DTC.sub (tG c) 13 1)) 14 (DTC.sub (tG c) 14 1))
           HcD HS HJ FR MG.
Qed.
End h.
End f.
End d.
