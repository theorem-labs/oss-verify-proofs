(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3B AxSymExec3Sound HeapIface HeapIfaceA FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PTB.
Definition mem := (word -> option byte).

Section K.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable IC : PMLA.consts.

Record preR (WFin : PML.pstate -> Prop) (BBin : PML.pstate -> Z -> Prop) (PAin : mem -> Z -> PML.pstate -> Prop) (scr : Z) (uar : bool)
             (Args : bvmap 5 word -> mem -> list (Z * Z) -> Z -> Z -> Z -> PML.pstate -> Prop)
             (LBo : list (Z * Z)) (FF : list fframe) (cr : credit) (sp P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate) (R : bvmap 5 word) (M : mem) : Prop := PRE {
  pr_args : Args R M LBo P V E ps;
  pr_al : uar = true -> sp mod 32 = 0;
  pr_stksh : PMSA.stksh ar M sp scr;
  pr_pa : PAin M P ps;
  pr_sh : PMSA.parser_sh M ps;
  pr_wf : WFin ps;
  pr_win : PMSA.win_okA M LBo ps;
  pr_bb : BBin ps B;
  pr_vis : PMSA.vis_at L IC M V;
  pr_ec : PMSA.ec_at L IC M E 0;
  pr_ls : PMSA.ls_ok L IC g M;
  pr_g : g <> PML.LS0;
  pr_cred : PMLA.pcredit_xA L cr ps kx bx;
  pr_oP : PMSA.fobj M FF P 272;
  pr_oV : PMSA.fobj M FF V 48;
  pr_oE : PMSA.fobj M FF E 16;
  pr_ap1 : PMLA.apart P 272 V 48;
  pr_ap2 : PMLA.apart P 272 E 16;
  pr_ap3 : PMLA.apart V 48 E 16 }.

Lemma pre_intro : forall WFin BBin PAin scr uar Args LBo FF cr sp P V E B kx bx g ps R M,
  preR WFin BBin PAin scr uar Args LBo FF cr sp P V E B kx bx g ps R M ->
  Args R M LBo P V E ps /\ (uar = true -> sp mod 32 = 0) /\ PMSA.stksh ar M sp scr /\
  PAin M P ps /\ PMSA.parser_sh M ps /\ WFin ps /\ PMSA.win_okA M LBo ps /\ BBin ps B /\ PMSA.vis_at L IC M V /\ PMSA.ec_at L IC M E 0 /\ PMSA.ls_ok L IC g M /\ g <> PML.LS0 /\
  PMLA.pcredit_xA L cr ps kx bx /\ PMSA.fobj M FF P 272 /\ PMSA.fobj M FF V 48 /\ PMSA.fobj M FF E 16 /\
  PMLA.apart P 272 V 48 /\ PMLA.apart P 272 E 16 /\ PMLA.apart V 48 E 16.
Proof.
  intros WFin BBin PAin scr uar Args LBo FF cr sp P V E B kx bx g ps R M [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19]. repeat (split; [assumption|]). assumption.
Qed.

Record postR (PAout : PML.pstate -> mem -> Z -> PML.pstate -> Prop) (Rel : PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop)
              (LBo : list (Z * Z)) (P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate)
              (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
              (ps' : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop := POST {
  po_pa : PAout ps M' P ps';
  po_sh : PMSA.parser_sh M' ps';
  po_wf : PMCUR.wf_c ps';
  po_win : PMSA.win_okA M' LBo ps';
  po_bb : PML.buf_bound ps' B;
  po_ec : PMSA.ec_at L IC M' E code;
  po_more : code <> 0 -> PML.ps_more ps' = false;
  po_ls : PMSA.ls_ok L IC g' M';
  po_g : g' = g \/ (g' = PML.regJ g /\ code <> 0);
  po_LB : LB' = PML.ps_blocks ps' ++ LBo;
  po_LBk : LBk = LBo;
  po_W : W = PMSA.W_parAc IC P V E;
  po_cred : PMLA.pcredit_xA L cr' ps' kx bx;
  po_rel : Rel ps ps' code R';
  po_cur : PMCUR.cur_post (hl_segs L) ps ps' code M' V }.

Lemma post_elim : forall PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W,
  (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      PAout ps M' P ps' /\ PMSA.parser_sh M' ps' /\ PMCUR.wf_c ps' /\ PMSA.win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ PMSA.ec_at L IC M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
      PMSA.ls_ok L IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = LBo /\ W = PMSA.W_parAc IC P V E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R' /\
      PMCUR.cur_post (hl_segs L) ps ps' code M' V) ->
  exists ps' code g', postR PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W ps' code g'.
Proof.
  intros PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W (ps' & code & g' & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
  exists ps', code, g'. constructor; assumption.
Qed.

Record postkR (PAout : PML.pstate -> mem -> Z -> PML.pstate -> Prop) (Rel : PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop)
               (LBo : list (Z * Z)) (P V E B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate)
               (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
               (ps' : PML.pstate) (code : Z) (g' : PML.ls_state) : Prop := POSTK {
  pk_pa : PAout ps M' P ps';
  pk_sh : PMSA.parser_sh M' ps';
  pk_wf : PMCUR.wf_c ps';
  pk_win : PMSA.win_okA M' LBo ps';
  pk_bb : PML.buf_bound ps' B;
  pk_ec : PMSA.ec_at L IC M' E code;
  pk_more : code <> 0 -> PML.ps_more ps' = false;
  pk_ls : PMSA.ls_ok L IC g' M';
  pk_g : g' = g \/ (g' = PML.regJ g /\ code <> 0);
  pk_LB : LB' = PML.ps_blocks ps' ++ LBo;
  pk_LBk : LBk = PML.ps_blocks ps ++ LBo;
  pk_W : W = PMLA.W_parA IC P E;
  pk_cred : PMLA.pcredit_xA L cr' ps' kx bx;
  pk_rel : Rel ps ps' code R';
  pk_blocks : PML.ps_blocks ps' = PML.ps_blocks ps }.

Lemma post_elimk : forall PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W,
  (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      PAout ps M' P ps' /\ PMSA.parser_sh M' ps' /\ PMCUR.wf_c ps' /\ PMSA.win_okA M' LBo ps' /\ PML.buf_bound ps' B /\ PMSA.ec_at L IC M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
      PMSA.ls_ok L IC g' M' /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\
      LB' = PML.ps_blocks ps' ++ LBo /\ LBk = PML.ps_blocks ps ++ LBo /\ W = PMLA.W_parA IC P E /\ PMLA.pcredit_xA L cr' ps' kx bx /\ Rel ps ps' code R' /\
      PML.ps_blocks ps' = PML.ps_blocks ps) ->
  exists ps' code g', postkR PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W ps' code g'.
Proof.
  intros PAout Rel LBo P V E B kx bx g ps R' M' LB' cr' LBk W (ps' & code & g' & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15).
  exists ps', code, g'. constructor; assumption.
Qed.

Section PA.
Variable M : mem. Variable P : Z. Variable ps : PML.pstate.
Hypothesis H : PMLA.parser_at (hl_segs L) IC M P ps.
Let u64 := PMLA.u64 (hl_segs L). Let u32 := PMLA.u32 (hl_segs L). Let u8 := PMLA.u8 (hl_segs L).
Lemma pa_vt : u64 M P (PMLA.VT_PARSER IC). Proof. exact (proj1 H). Qed.
Lemma pa_maxdepth : u32 M (P + 8) 1024. Proof. exact (proj1 (proj2 H)). Qed.
Lemma pa_func : u64 M (P + 96) (PMLA.VT_FUNC IC). Proof. do 12 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_errh : u64 M (P + 128) (P + 96). Proof. do 13 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_level : u32 M (P + 144) (PML.ps_level ps). Proof. do 14 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_win : match PML.ps_win ps with None => u64 M (P + 192) 0 /\ u64 M (P + 200) 0 | Some (p, e) => u64 M (P + 200) p /\ u64 M (P + 192) e /\ p <= e end.
Proof. do 15 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_win_some : forall p e, PML.ps_win ps = Some (p, e) -> u64 M (P + 200) p /\ u64 M (P + 192) e /\ p <= e.
Proof. intros p e Hw. pose proof pa_win as X. rewrite Hw in X. exact X. Qed.
Lemma pa_st : u8 M (P + 208) (PML.ps_st ps). Proof. do 16 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_sst : u8 M (P + 209) (PML.ps_sst ps). Proof. do 17 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_nst : u8 M (P + 210) (PML.ps_nst ps). Proof. do 18 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_more : u8 M (P + 211) (PML.b2z (PML.ps_more ps)). Proof. do 19 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_done : u8 M (P + 212) (PML.b2z (PML.ps_done ps)). Proof. do 20 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_buf : PMLA.str_at (hl_segs L) M (P + 224) (PML.SLong (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps)). Proof. do 23 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_bcap : 264 <= PML.ps_bcap ps. Proof. do 24 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_sb : u64 M (P + 248) (PML.ps_sb ps). Proof. do 25 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_send : u64 M (P + 256) (PML.ps_sb ps + Z.of_nat (length (PML.ps_stack ps))). Proof. do 26 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_scap : u64 M (P + 264) (PML.ps_sb ps + PML.ps_scap ps). Proof. do 27 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_stack : L5.bytes_at (hl_segs L) M (PML.ps_sb ps) (PML.ps_stack ps). Proof. do 28 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_slen : Z.of_nat (length (PML.ps_stack ps)) <= PML.ps_scap ps. Proof. do 29 (apply proj2 in H). exact (proj1 H). Qed.
Lemma pa_def : L5.defined M P 272. Proof. do 30 (apply proj2 in H). exact H. Qed.
End PA.
End K.
End PTB.
