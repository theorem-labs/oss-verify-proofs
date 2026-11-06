(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt):
     0x8d2e8  li a0,1; bgeu a0,s7, 0x8d68c             at most two words: the shared refusal stub 0x8d68c (vr_pr)
     0x8d2f0  li a0,3; ld s3,40(s1); bne s5,a0, 0x8d348  three words: `li s9,0; li s10,0; j 0x8d454`, the add tail
                                                         (verbs_receive_s07g.v legT, no placement, no client)
     0x8d348  li a0,-24; bgeu s3,a0 (UBSan, refuted); ld s10,24(s3); strcmp(tok[3], "own" 0x228a0),
              strcmp(tok[3], "default" 0x228c0), strncmp(tok[3], "pool:" 0x228e0, 5), each `beqz a0, 0x8d3c8`
              (legP here; a Theorem Labs lane's contracts through verbs_receive_s07i.v's cmp07 / ncmp07), then
              verbs_receive_s07h.v's legDp (a placement) or legDn (none).
   Every path from four words on ends at the join JB 0x8d4d0 (vr_hd) or, when the client index is past ntok, at the
   refusal stub 0x8d4c4 (vr_pr). sup_add reaches the printf wrappers (statement pass 4: FP-existential post), so
   vr_s07 is stated with vr_segF: the stub 0x8d68c is reached at the entry FP state, JB and 0x8d4c4 at the FP state
   the leg's printf-reaching callee returned at. The B twin of lib/A/Prog/verbs_receive_s07.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c sup_resp_c record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07e verbs_receive_s07f
verbs_receive_s07g verbs_receive_s07h verbs_receive_s07i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

Lemma addm2_07 : forall u wi, PV.add_m atoi_a [u; wi] = PV.SAdd u (atoi_a wi) None None.
Proof. reflexivity. Qed.

(* the registers of a list that a run kept, besides those it set *)
Lemma rv_kept07 : forall (regs regs' : bvmap 5 word) l zs, vr_rv regs l ->
(forall r, In r zs -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
forallb (fun rv => existsb (Z.eqb (fst rv)) zs) l = true -> vr_rv regs' l.
Proof.
intros regs regs' l zs H K Hl. apply rv_intro07. intros r v Hin.
rewrite forallb_forall in Hl. pose proof (Hl _ Hin) as Hz. cbn [fst] in Hz.
apply existsb_exists in Hz as (z & Hz & Hzr). apply Z.eqb_eq in Hzr. subst z.
rewrite (K r Hz). exact (rv_get07 regs l r v H Hin).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TSUP_ADD : forall fx0 : YK11.FPState, @tsup_add_spec fx0 rc SK PI B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, @tdescriptors_add_spec fx0 rc SK PI B MT.
Hypothesis STRCMP : forall fx0 : YK11.FPState,
  RtString.astrcmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState,
  RtString.astrncmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis AATOI : forall fx0 : YK11.FPState,
  RtNumber.aatoi_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis SHOK : vr_shadow_ok B.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.
Let CMP := cmp07 B MT (STRCMP fx) TL SHOK BLKT ROA RRO RECC PROGU.
Let NCMP := ncmp07 B MT (STRNCMP fx) TL SHOK BLKT ROA RRO RECC PROGU.
Let LEGT := legT B MT (TSUP_ADD fx) TSUP_REPLY_CODE TDESCRIPTORS_ADD (AATOI fx) HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.
Let LEGDP := legDp B MT (TSUP_ADD fx) TSUP_REPLY_CODE TDESCRIPTORS_ADD (AATOI fx) HB TL MTL SIGP BLKT ROA
  RRO RPG RECC PROGU.
Let LEGDN := legDn B MT (TSUP_ADD fx) TSUP_REPLY_CODE TDESCRIPTORS_ADD (AATOI fx) HB TL MTL SIGP BLKT ROA
  RRO RPG RECC PROGU.

(* the shared refusal stub at 0x8d68c, the step being reject; B has NOT reloaded tok there, so vr_rl_pr's base *)
Lemma pr07 : forall e W pos F q c tp lyc Sc regs mem md k nm,
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
Verbs.toks (e_D e) <> [] ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
vr_pr B MT e 0x8d68c W (cfg_at SEGS (vr_pc 0x8d68c) regs mem md).
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm Hvh Hk1 Hne Hcore Hline Hcopy.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regs, mem, md, k, nm.
split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hvh|]. split; [exact Hne|].
split; [change (vr_pr_ntok 0x8d68c (length (Verbs.toks (e_D e)))) with (1 <= length (Verbs.toks (e_D e)))%nat;
  destruct (Verbs.toks (e_D e)); [congruence | cbn [length]; lia]|].
split; [|split; [exact Hline | exact Hcopy]].
replace (vr_rl_pr e F q c 0x8d68c (-902)) with
  [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
destruct Hcore as (H1 & H2 & H3 & H4 & H5).
split; [exact H1|]. split; [rewrite Hk1; unfold EV_SUP_RESP, EV_XMALLOC; lia|]. split; [exact H3|].
split; [unfold VR_NM_PR, VR_NM_PRE in *; lia | exact H5].
Qed.

Ltac inzs07 := reflexivity.

(* the placement test, 0x8d348 (at least four words) *)
Lemma legP : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: x :: rest ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
   (25, vr_ntok (e_D e)); (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 28184)) memc (seg_rom SEGS)) mdc)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
     (vr_atpr (fx := fq) B MT 0x8d4c4 e W' cf' \/ vr_athd (fx := fq) B MT 0x8d4d0 e W' cf')).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest Hent Htk Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & VOBJS & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (HF_bounds07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as HFb.
pose proof HFb as [HFlo HFhi].
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
destruct tp as [|t0 [|t1 [|t2 [|t3 tp']]]]; cbn [length] in Hlen; try lia.
assert (Hjp : nth_error (t0 :: t1 :: t2 :: t3 :: tp') 3 = Some t3) by reflexivity.
assert (Hjw : nth_error (PV.toks (e_D e)) 3 = Some x) by (rewrite Htk; reflexivity).
set (rl1 := [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
  (25, vr_ntok (e_D e)); (26, t3); (27, shadow_addr F + 4)]).
assert (Hcs1 : cs07 rl1) by (unfold cs07, rl1; cs07_tac).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regsc _ 19 _ Hrv); cbn; tauto).
pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28184 [t1; t2; t3]
  Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19
  ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
  ltac:(cbn; lia)) as HS.
remember (E07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as HAE. rewrite <- HE in HAE.
assert (X36 : ew E 36 = Z_to_bv 64 t3) by (rewrite HE; apply (E07_ext _ _ _ _ 4); [lia | reflexivity]).
assert (EE19 : ew E 19 = Z_to_bv 64 (F + 32)) by (rewrite HE, (E07_reg _ _ _ _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
clear HE.
(* 0x8d348: li a0,-24; bgeu s3,a0 (UBSan on tok + 24) *)
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V0 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_geu_U, (U_atom E 19 _ EE19) in Hc by lia.
  match type of Hc with context [U E (SLit ?z)] =>
    replace (U E (SLit z)) with (2 ^ 64 - 24) in Hc by (vm_compute; reflexivity) end.
  apply negb_true_iff, Z.ltb_ge in Hc. lia. }
clear Hc.
(* 0x8d350: ld s10,24(s3); auipc a0; addi a1,a0,...; mv a0,s10; jal wrapper_strcmp *)
paj_run_shc RUNP RUNC HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
{ intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V0 a Ha). }
clear HF HFr HG.
prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11. prreg HS (Z_to_bv 5 26) Q26.
rewrite X36 in Q10, Q26.
objval07 Q11 E HEI VOBJS.
pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27] HS HAE
  ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
pmkst HS.
assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ rl1)).
{ rv07 Hrv KR regsc. }
destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms0) memc (ms_mem ms0)
  mdc mdv0 Hcore Hline Hcopy HJ V Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
eapply (CMP e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc W (ms_regs ms0) (ms_mem ms0) mdv0 k nm rl1 _ t3 x 0x228a0
  PV.Lit.place_own _ Hent Hc1 Hl1 Hcp1 Hcs1 Q1).
- lia.
- reflexivity.
- exact Q10.
- exact Q11.
- exact Hjp.
- exact Hjw.
- exact lit07_own.
- (* after strcmp(tok[3], "own"), 0x8d364: beqz a0, 0x8d3c8 *)
  intros regs2 mem2 md2 Hc2 Hl2 Hcp2 HQ.
  pose proof Hc2 as (HJ2 & _ & _ & _ & _ & Hrv2 & _).
  assert (R19b : getr regs2 (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regs2 _ 19 _ Hrv2); unfold rl1; cbn; tauto).
  pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28212 [t1; t2; t3]
    Hc2 Hcp2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19b
    ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
    ltac:(cbn; lia)) as HS2.
  remember (E07 regs2 (shadow_addr F + 4) F [t1; t2; t3]) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply E07_env).
  pose proof (env_agree07 regs2 (shadow_addr F + 4) F [t1; t2; t3]) as HAE2. rewrite <- HE2 in HAE2.
  assert (EE2 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E2 nn = getr regs2 rr)
    by (intros nn rr Hnn; rewrite HE2; apply E07_reg; exact Hnn).
  clear HE2.
  psrr_branch_pi RUNP BR HS2.
  + (* tok[3] is "own": a placement *)
    rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    pose proof (proj1 HQ (reg0_07 E2 _ (EE2 10%nat (Z_to_bv 5 10) eq_refl) Hc)) as Hx.
    assert (Hpl : PV.is_placement_m x = true) by (rewrite Hx; vm_compute; reflexivity).
    paj_run_to_sh RUNTOP HS2 HJ2 (AF_verbs_receive + (0x8d3c8 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W mem2 a)
      by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
    clear HF HFr HG.
    pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
      ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
    pose proof (rv_kept07 regs2 (ms_regs ms1) _ _ Hrv2 KR2 ltac:(inzs07)) as Hrv3.
    destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs2 (ms_regs ms1) mem2
      (ms_mem ms1) md2 mdv1 Hc2 Hl2 Hcp2 HJ2 V2 Hrv3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
      as (Hc3 & Hl3 & Hcp3).
    pmkst HS2.
    exact (LEGDP e W pos F q c _ lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi x rest t3 Hent Htk Hpl Hjp
      Hc3 Hl3 Hcp3).
  + (* not "own": 0x8d368 auipc a0; addi a1,a0,...; mv a0,s10; jal wrapper_strcmp *)
    rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    assert (Hx1 : x <> PV.Lit.place_own)
      by (intros E0; exact (regn0_07 E2 _ (EE2 10%nat (Z_to_bv 5 10) eq_refl) Hc (proj2 HQ E0))).
    clear Hc.
    paj_run_shc RUNP RUNC HS2 HJ2.
    { awr07. }
    mdv_set.
    assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W mem2 a)
      by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
    clear HF HFr HG.
    prreg HS2 (Z_to_bv 5 1) Q1b. prreg HS2 (Z_to_bv 5 10) Q10b. prreg HS2 (Z_to_bv 5 11) Q11b.
    rewrite (EE2 26%nat (Z_to_bv 5 26) eq_refl), (rv_get07 regs2 _ 26 t3 Hrv2 ltac:(unfold rl1; cbn; tauto)) in Q10b.
    objval07 Q11b E2 HEI2 VOBJS.
    pose proof (kept_regs07 E2 _ _ regs2 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS2 HAE2
      ltac:(vm_compute; reflexivity)) as KR2. cbn [ms_regs restrict] in KR2.
    pmkst HS2.
    pose proof (rv_kept07 regs2 (ms_regs ms1) _ _ Hrv2 KR2 ltac:(inzs07)) as Hrv3.
    destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs2 (ms_regs ms1) mem2
      (ms_mem ms1) md2 mdv1 Hc2 Hl2 Hcp2 HJ2 V2 Hrv3 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
      as (Hc3 & Hl3 & Hcp3).
    eapply (CMP e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc W (ms_regs ms1) (ms_mem ms1) mdv1 k nm rl1 _ t3 x 0x228c0
      PV.Lit.place_default _ Hent Hc3 Hl3 Hcp3 Hcs1 Q1b).
    * lia.
    * reflexivity.
    * exact Q10b.
    * exact Q11b.
    * exact Hjp.
    * exact Hjw.
    * exact lit07_default.
    * (* after strcmp(tok[3], "default"), 0x8d378: beqz a0, 0x8d3c8 *)
      intros regs3 mem3 md3 Hc4 Hl4 Hcp4 HQ3.
      pose proof Hc4 as (HJ4 & _ & _ & _ & _ & Hrv4 & _).
      assert (R19c : getr regs3 (Z_to_bv 5 19) = w64 (F + 32))
        by (apply (rv_get07 regs3 _ 19 _ Hrv4); unfold rl1; cbn; tauto).
      pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28232 [t1; t2; t3]
        Hc4 Hcp4 ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19c
        ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
        ltac:(cbn; lia)) as HS3.
      remember (E07 regs3 (shadow_addr F + 4) F [t1; t2; t3]) as E3 eqn:HE3.
      assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply E07_env).
      pose proof (env_agree07 regs3 (shadow_addr F + 4) F [t1; t2; t3]) as HAE3. rewrite <- HE3 in HAE3.
      assert (EE3 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E3 nn = getr regs3 rr)
        by (intros nn rr Hnn; rewrite HE3; apply E07_reg; exact Hnn).
      clear HE3.
      psrr_branch_pi RUNP BR HS3.
      -- (* tok[3] is "default": a placement *)
         rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
         pose proof (proj1 HQ3 (reg0_07 E3 _ (EE3 10%nat (Z_to_bv 5 10) eq_refl) Hc)) as Hx.
         assert (Hpl : PV.is_placement_m x = true) by (rewrite Hx; vm_compute; reflexivity).
         paj_run_to_sh RUNTOP HS3 HJ4 (AF_verbs_receive + (0x8d3c8 - 0x8ce4c)).
         { awr07. }
         mdv_set.
         assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms2) a = rdW W mem3 a)
           by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
         clear HF HFr HG.
         pose proof (kept_regs07 E3 _ _ regs3 _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] HS3 HAE3
           ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
         pose proof (rv_kept07 regs3 (ms_regs ms2) _ _ Hrv4 KR3 ltac:(inzs07)) as Hrv5.
         destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs3 (ms_regs ms2) mem3
           (ms_mem ms2) md3 mdv2 Hc4 Hl4 Hcp4 HJ4 V3 Hrv5 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
           as (Hc5 & Hl5 & Hcp5).
         pmkst HS3.
         exact (LEGDP e W pos F q c _ lyc Sc (ms_regs ms2) (ms_mem ms2) mdv2 k nm u wi x rest t3 Hent Htk Hpl Hjp
           Hc5 Hl5 Hcp5).
      -- (* not "default": 0x8d37c auipc a0; addi a1,a0,...; li a2,5; mv a0,s10; jal wrapper_strncmp *)
         rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
         assert (Hx2 : x <> PV.Lit.place_default)
           by (intros E0; exact (regn0_07 E3 _ (EE3 10%nat (Z_to_bv 5 10) eq_refl) Hc (proj2 HQ3 E0))).
         clear Hc.
         paj_run_shc RUNP RUNC HS3 HJ4.
         { awr07. }
         mdv_set.
         assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms2) a = rdW W mem3 a)
           by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
         clear HF HFr HG.
         prreg HS3 (Z_to_bv 5 1) Q1c. prreg HS3 (Z_to_bv 5 10) Q10c. prreg HS3 (Z_to_bv 5 11) Q11c.
         prreg HS3 (Z_to_bv 5 12) Q12c.
         rewrite (EE3 26%nat (Z_to_bv 5 26) eq_refl), (rv_get07 regs3 _ 26 t3 Hrv4 ltac:(unfold rl1; cbn; tauto)) in Q10c.
         objval07 Q11c E3 HEI3 VOBJS.
         assert (Q12' : getr (ms_regs ms2) (Z_to_bv 5 12) = w64 5)
           by (refine (eq_trans Q12c _); apply bv_eq; vm_compute; reflexivity).
         pose proof (kept_regs07 E3 _ _ regs3 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS3 HAE3
           ltac:(vm_compute; reflexivity)) as KR3. cbn [ms_regs restrict] in KR3.
         pmkst HS3.
         pose proof (rv_kept07 regs3 (ms_regs ms2) _ _ Hrv4 KR3 ltac:(inzs07)) as Hrv5.
         destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs3 (ms_regs ms2) mem3
           (ms_mem ms2) md3 mdv2 Hc4 Hl4 Hcp4 HJ4 V3 Hrv5 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
           as (Hc5 & Hl5 & Hcp5).
         eapply (NCMP e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc W (ms_regs ms2) (ms_mem ms2) mdv2 k nm rl1 _ t3 x
           0x228e0 PV.Lit.place_pool_prefix _ Hent Hc5 Hl5 Hcp5 Hcs1 Q1c).
         ++ lia.
         ++ reflexivity.
         ++ exact Q10c.
         ++ exact Q11c.
         ++ exact Q12'.
         ++ exact Hjp.
         ++ exact Hjw.
         ++ exact lit07_pool.
         ++ vm_compute. lia.
         ++ (* after strncmp(tok[3], "pool:", 5), 0x8d390: beqz a0, 0x8d3c8 *)
            intros regs4 mem4 md4 Hc6 Hl6 Hcp6 HQ4.
            destruct (add_prefix07 x) as (v & Hv & Hvr & Hvp).
            pose proof Hc6 as (HJ6 & _ & _ & _ & _ & Hrv6 & _).
            assert (R19d : getr regs4 (Z_to_bv 5 19) = w64 (F + 32))
              by (apply (rv_get07 regs4 _ 19 _ Hrv6); unfold rl1; cbn; tauto).
            pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28256
              [t1; t2; t3] Hc6 Hcp6 ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19d
              ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
              ltac:(cbn; lia)) as HS4.
            remember (E07 regs4 (shadow_addr F + 4) F [t1; t2; t3]) as E4 eqn:HE4.
            assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply E07_env).
            pose proof (env_agree07 regs4 (shadow_addr F + 4) F [t1; t2; t3]) as HAE4. rewrite <- HE4 in HAE4.
            assert (EE4 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E4 nn = getr regs4 rr)
              by (intros nn rr Hnn; rewrite HE4; apply E07_reg; exact Hnn).
            clear HE4.
            psrr_branch_pi RUNP BR HS4.
            ** (* tok[3] starts with "pool:": a placement *)
               rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
               pose proof (proj1 HQ4 (reg0_07 E4 _ (EE4 10%nat (Z_to_bv 5 10) eq_refl) Hc)) as Hs.
               rewrite Hs in Hv. injection Hv as <-.
               assert (Hpl : PV.is_placement_m x = true)
                 by (unfold PV.is_placement_m; rewrite <- Hvp, Z.eqb_refl, orb_true_r; reflexivity).
               paj_run_to_sh RUNTOP HS4 HJ6 (AF_verbs_receive + (0x8d3c8 - 0x8ce4c)).
               { awr07. }
               mdv_set.
               assert (V4 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W mem4 a)
                 by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
               clear HF HFr HG.
               pose proof (kept_regs07 E4 _ _ regs4 _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] HS4 HAE4
                 ltac:(vm_compute; reflexivity)) as KR4. cbn [ms_regs restrict] in KR4.
               pose proof (rv_kept07 regs4 (ms_regs ms3) _ _ Hrv6 KR4 ltac:(inzs07)) as Hrv7.
               destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs4 (ms_regs ms3)
                 mem4 (ms_mem ms3) md4 mdv3 Hc6 Hl6 Hcp6 HJ6 V4 Hrv7 ltac:(left; reflexivity)
                 ltac:(right; left; reflexivity) HDn) as (Hc7 & Hl7 & Hcp7).
               pmkst HS4.
               exact (LEGDP e W pos F q c _ lyc Sc (ms_regs ms3) (ms_mem ms3) mdv3 k nm u wi x rest t3 Hent Htk Hpl Hjp
                 Hc7 Hl7 Hcp7).
            ** (* no placement: 0x8d394 *)
               rewrite branch_eq_U, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
               pose proof (regn0_07 E4 _ (EE4 10%nat (Z_to_bv 5 10) eq_refl) Hc) as Hne0.
               assert (Hv0 : v <> 0) by (intros ->; exact (Hne0 (proj2 HQ4 Hv))).
               assert (Hnp : PV.is_placement_m x = false).
               { unfold PV.is_placement_m. rewrite (list_eqb_false07 _ _ Hx1), (list_eqb_false07 _ _ Hx2), <- Hvp.
                 apply Z.eqb_neq in Hv0. rewrite Hv0. reflexivity. }
               paj_run_to_sh RUNTOP HS4 HJ6 (AF_verbs_receive + (0x8d394 - 0x8ce4c)).
               { awr07. }
               mdv_set.
               assert (V4 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W mem4 a)
                 by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
               clear HF HFr HG.
               pose proof (kept_regs07 E4 _ _ regs4 _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 27] HS4 HAE4
                 ltac:(vm_compute; reflexivity)) as KR4. cbn [ms_regs restrict] in KR4.
               assert (Hrv7 : vr_rv (ms_regs ms3)
                 (vr_base B e ++ [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
                   (25, vr_ntok (e_D e)); (27, shadow_addr F + 4)])).
               { refine (rv_kept07 regs4 (ms_regs ms3)
                   (vr_base B e ++ [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
                     (25, vr_ntok (e_D e)); (27, shadow_addr F + 4)]) _ _ KR4 ltac:(inzs07)).
                 apply (rv_sub07 _ _ _ Hrv6). intros y Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
                   [left; exact Hy | right]. unfold rl1. cbn in Hy |- *. tauto. }
               destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regs4 (ms_regs ms3)
                 mem4 (ms_mem ms3) md4 mdv3 Hc6 Hl6 Hcp6 HJ6 V4 Hrv7 ltac:(left; reflexivity)
                 ltac:(right; left; reflexivity) HDn) as (Hc7 & Hl7 & Hcp7).
               pmkst HS4.
               exact (LEGDN e W pos F q c _ lyc Sc (ms_regs ms3) (ms_mem ms3) mdv3 k nm u wi x rest Hent Htk Hnp
                 Hc7 Hl7 Hcp7).
Qed.

Lemma vr_s07 : vr_s07_stmt B MT.
Proof.
intros e W cf Hent Hrt.
destruct Hrt as (pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hroute & Hne & Hcore & Hline & Hcopy).
destruct (route_add _ Hroute Hne) as (args & Htk).
unfold vr_rl_rt in Hcore. cbv zeta in Hcore. cbn [app] in Hcore.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (HF_bounds07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as HFb.
pose proof HFb as [HFlo HFhi].
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (S (length args))) by (unfold vr_ntok; rewrite Htk; reflexivity).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (toks_le_64 (e_D e)); lia).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 21 _ Hrv); cbn; tauto).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 F) by (apply (rv_get07 regsc _ 22 _ Hrv); cbn; tauto).
assert (R23 : getr regsc (Z_to_bv 5 23) = w64 (vr_ntok (e_D e) - 1)) by (apply (rv_get07 regsc _ 23 _ Hrv); cbn; tauto).
assert (R25 : getr regsc (Z_to_bv 5 25) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 25 _ Hrv); cbn; tauto).
cbn [vr_route_pc].
replace (vr_pc 0x8d2e8) with (BASE + 28088) by (unfold vr_pc, AF_verbs_receive; lia).
unfold cfg_at, w64.
pose proof (seed_core_e B MT e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28088 Hcore) as HS.
remember (E07 regsc (shadow_addr F + 4) F []) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc (shadow_addr F + 4) F []) as HAE. rewrite <- HE in HAE.
assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regsc rr)
  by (intros nn rr Hnn; rewrite HE; apply E07_reg; exact Hnn).
assert (X32 : ew E 32 = Z_to_bv 64 (shadow_addr F + 4)) by (rewrite HE; apply (E07_ext _ _ _ _ 0); [lia | reflexivity]).
assert (X33 : ew E 33 = Z_to_bv 64 (F + 32)) by (rewrite HE; apply (E07_ext _ _ _ _ 1); [lia | reflexivity]).
clear HE.
(* 0x8d2e8: li a0,1; bgeu a0,s7, 0x8d68c *)
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* at most two words: the shared refusal stub 0x8d68c *)
  rewrite branch_geu_U, U_lit, (U_atom E 23 (vr_ntok (e_D e) - 1)) in Hc
    by (try (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; reflexivity); lia).
  apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hrej : PV.add_m atoi_a args = PV.reject) by (apply add_short; lia).
  assert (EH : vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false))
    by (unfold vr_h; rewrite (st_add _ _ Htk), Hrej; reflexivity).
  assert (EK : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP)
    by (unfold vr_k1; rewrite (evr_add _ _ _ Htk), Hrej; reflexivity).
  paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d68c - 0x8ce4c)).
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 21; 22; 24; 27] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (Hrv1 : vr_rv (ms_regs ms0)
    (vr_base B e ++ [(18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])).
  { rv07 Hrv KR regsc. }
  destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms0) memc (ms_mem ms0) mdc mdv0
    Hcore Hline Hcopy HJ V2 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
  pmkst HS.
  apply SRr_ret. exists fx. split; [apply fxrel_refl|]. unfold vrF_or, vr_or, vrF_pr. left. unfold vr_atpr.
  replace (BASE + (AF_verbs_receive + (0x8d68c - 0x8ce4c))) with (vr_pc 0x8d68c) by (unfold vr_pc; lia).
  exact (pr07 e W pos F q c tp lyc Sc (ms_regs ms0) (ms_mem ms0) mdv0 k nm EH EK Hne Hc1 Hl1 Hcp1).
- (* three words or more: 0x8d2f0 li a0,3; ld s3,40(s1); bne s5,a0, 0x8d348 *)
  rewrite branch_geu_U, U_lit, (U_atom E 23 (vr_ntok (e_D e) - 1)) in Hc
    by (try (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl), R23; reflexivity); lia).
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hnt3.
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* four words or more: the placement test 0x8d348 *)
    rewrite branch_ne_U, U_lit, (U_atom E 21 (vr_ntok (e_D e))) in Hc
      by (try (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity); lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    destruct args as [|u [|wi [|x rest]]]; cbn [length] in Hnt; try lia.
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d348 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 19) T19. rewrite X33 in T19.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms1)
      (vr_base B e ++ [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
        (25, vr_ntok (e_D e)); (27, shadow_addr F + 4)])).
    { rv07 Hrv KR regsc. }
    destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc (ms_mem ms1) mdc mdv1
      Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    eapply SRr_mono.
    { exact (legP e W pos F q c tp lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi x rest Hent Htk Hc1 Hl1 Hcp1). }
    intros W' c' _ (fq & Hr & H). exists fq. split; [exact Hr|]. unfold vrF_or, vr_or.
    destruct H as [H|H]; right; [left; exact H | right; exact H].
  + (* three words: `li s9,0; li s10,0; j 0x8d454` *)
    rewrite branch_ne_U, U_lit, (U_atom E 21 (vr_ntok (e_D e))) in Hc
      by (try (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity); lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    destruct args as [|u [|wi [|x rest]]]; cbn [length] in Hnt; try lia.
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d454 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 19) T19. prreg HS (Z_to_bv 5 25) T25. prreg HS (Z_to_bv 5 26) T26.
    rewrite X33 in T19.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 22; 24] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms1)
      (vr_base B e ++ [(18, q); (19, F + 32); (22, F); (25, 0); (26, 0)])).
    { rv07 Hrv KR regsc. }
    destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc (ms_mem ms1) mdc mdv1
      Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + (AF_verbs_receive + (0x8d454 - 0x8ce4c))) with (vr_pc 0x8d454) by (unfold vr_pc; lia).
    eapply SRr_mono.
    { exact (LEGT e W pos F q c tp lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi [] None None 0 0 Hent Htk
        (addm2_07 u wi) (or_introl (conj eq_refl eq_refl)) (or_introl (conj eq_refl eq_refl)) Hc1 Hl1 Hcp1). }
    intros W' c' _ (fq & Hr & H). exists fq. split; [exact Hr|]. unfold vrF_or, vr_or. right. right. exact H.
Qed.

End e.
End f.
End d.
