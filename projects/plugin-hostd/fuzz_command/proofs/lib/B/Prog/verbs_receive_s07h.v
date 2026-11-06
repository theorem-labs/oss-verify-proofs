(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, B 0x8d2e8) of the walk of verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): the client decision
   after the placement test. B merges A's two arms into one block at 0x8d3c8-0x8d3f4:
   legDp, 0x8d3c8 (tok[3] is a placement, s10 = tok[3]): the UBSan check `li a0,-24; beq s3,a0, 0x8d938` (refuted:
   s3 = tok = F+32), `li a0,4; bltu s7,a0, 0x8d450` (four words: no client, `li s9,0; j 0x8d454`), else the shared
   index block;
   legDn, 0x8d394 (tok[3] is no placement): `li s10,0; li a0,3; j 0x8d3d8`, the shared index block;
   the index block 0x8d3d8-0x8d3f4: `slli a1,a0,3; not a2,s3; bltu a2,a1, 0x8d938` (UBSan, refuted), `addi a0,a0,1;
   bltu a0,s9, 0x8d4c4` (the index is past ntok: the refusal stub, which B reaches with tok reloaded), else
   `add a1,s3,a1; ld s9,0(a1); j 0x8d454` (the client word) and the add tail (verbs_receive_s07g.v legT).
   The B twin of lib/A/Prog/verbs_receive_s07h.v; A's legR (the refusal inside the arm) has no B counterpart: B
   leaves at the refusal stub 0x8d4c4, which is S29's. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c sup_resp_c record_c arg_s_c xmalloc_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07e verbs_receive_s07f
verbs_receive_s07g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* the model's add step for the word counts the code tells apart *)
Lemma addm3_07 : forall u wi x, PV.add_m atoi_a [u; wi; x] =
  if PV.is_placement_m x then PV.SAdd u (atoi_a wi) (Some x) None else PV.SAdd u (atoi_a wi) None (Some x).
Proof. reflexivity. Qed.
Lemma addm4_07 : forall u wi x y, PV.add_m atoi_a [u; wi; x; y] =
  if PV.is_placement_m x then PV.SAdd u (atoi_a wi) (Some x) (Some y) else PV.reject.
Proof. reflexivity. Qed.
Lemma addm5_07 : forall u wi x y z r, PV.add_m atoi_a (u :: wi :: x :: y :: z :: r) = PV.reject.
Proof. reflexivity. Qed.

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
Hypothesis TSUP_ADD : tsup_add_spec B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, @tdescriptors_add_spec fx0 rc SK PI B MT.
Hypothesis AATOI : RtNumber.aatoi_realizes SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let RUN07 := run07 B MT TL ROA RRO RECC PROGU.
Let LEGT := legT B MT TSUP_ADD TSUP_REPLY_CODE TDESCRIPTORS_ADD AATOI HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.

(* the refusal stub 0x8d4c4 (S29's): B reaches it with tok reloaded in s3, so vr_rl_pr carries (19, F + 32) *)
Lemma pr07c4 : forall e W pos F q c tp lyc Sc regs mem md k nm,
vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false) ->
vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP ->
(2 <= length (PV.toks (e_D e)))%nat ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
vr_pr B MT e 0x8d4c4 W (cfg_at SEGS (vr_pc 0x8d4c4) regs mem md).
Proof.
intros e W pos F q c tp lyc Sc regs mem md k nm Hvh Hk1 Hnt Hcore Hline Hcopy.
exists (-902), (e_R e), (e_O e), pos, F, q, c, tp, lyc, Sc, regs, mem, md, k, nm.
split; [reflexivity|]. split; [intros _; reflexivity|]. split; [lia|]. split; [exact Hvh|].
split; [destruct (PV.toks (e_D e)); [cbn [length] in Hnt; lia | discriminate]|].
split; [unfold vr_pr_ntok; cbn; exact Hnt|].
split; [|split; [exact Hline | exact Hcopy]].
replace (vr_rl_pr e F q c 0x8d4c4 (-902)) with
  [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)] by reflexivity.
destruct Hcore as (H1 & H2 & H3 & H4 & H5).
split; [exact H1|]. split; [rewrite Hk1; unfold EV_SUP_RESP, EV_XMALLOC; lia|]. split; [exact H3|].
split; [unfold VR_NM_PR, VR_NM_PRE in *; lia | exact H5].
Qed.

(* Each arm runs the shared index block 0x8d3d8-0x8d3f4 itself, entered with a0 = j (4 after a placement, 3 without
   one) and s10 = the placement pointer or 0: it ends at the add tail 0x8d454 with s9 = tok[j] (the client), or at
   the refusal stub 0x8d4c4 when j + 1 < ntok. *)

Lemma legDp : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest t3,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: x :: rest -> PV.is_placement_m x = true -> nth_error tp 3 = Some t3 ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
   (25, vr_ntok (e_D e)); (26, t3); (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 28312)) memc (seg_rom SEGS)) mdc)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
     (vr_atpr (fx := fq) B MT 0x8d4c4 e W' cf' \/ vr_athd (fx := fq) B MT 0x8d4d0 e W' cf')).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest t3 Hent Htk Hpl Ht3 Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HF_bounds07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as HFb.
pose proof HFb as [HFlo HFhi].
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (4 + length rest)) by (unfold vr_ntok; rewrite Htk; cbn [length]; lia).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (toks_le_64 (e_D e)); lia).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regsc _ 19 _ Hrv); cbn; tauto).
assert (R23 : getr regsc (Z_to_bv 5 23) = w64 (vr_ntok (e_D e) - 1)) by (apply (rv_get07 regsc _ 23 _ Hrv); cbn; tauto).
assert (R25 : getr regsc (Z_to_bv 5 25) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 25 _ Hrv); cbn; tauto).
destruct tp as [|t0 [|t1 [|t2 [|t3b tp']]]]; cbn [length] in Hlen; try lia.
assert (Ht3b : t3b = t3) by (cbn in Ht3; injection Ht3; auto). subst t3b.
destruct rest as [|y rest'].
- (* four words: no client (`li s9,0; j 0x8d454`) *)
  cbn [length] in Hnt.
  pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28312
    [t1; t2; t3] Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19
    ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
    ltac:(cbn; lia)) as HS.
  remember (E07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
  pose proof (env_agree07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as HAE. rewrite <- HE in HAE.
  assert (EE19 : ew E 19 = Z_to_bv 64 (F + 32)) by (rewrite HE, (E07_reg _ _ _ _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
  assert (EE23 : ew E 23 = Z_to_bv 64 (vr_ntok (e_D e) - 1))
    by (rewrite HE, (E07_reg _ _ _ _ 23 (Z_to_bv 5 23) eq_refl); exact R23).
  clear HE.
  (* 0x8d3c8: li a0,-24; beq s3,a0 (UBSan) *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  { exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_eq_U, (U_atom E 19 _ EE19) in Hc by lia.
  match type of Hc with context [U E (SLit ?z)] =>
    replace (U E (SLit z)) with (2 ^ 64 - 24) in Hc by (vm_compute; reflexivity) end.
  apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* 0x8d3d0: li a0,4; bltu s7,a0 (four words: no client) *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* ntok - 1 < 4: `li s9,0; j 0x8d454` *)
    clear Hc.
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d454 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 25) T25.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms1)
      (vr_base B e ++ [(18, q); (19, F + 32); (22, F); (25, 0); (26, t3)])).
    { rv07 Hrv KR regsc. }
    destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc
      (ms_mem ms1) mdc mdv1 Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
      as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + (AF_verbs_receive + (0x8d454 - 0x8ce4c))) with (vr_pc 0x8d454) by (unfold vr_pc; lia).
    eapply SRr_mono.
    { exact (LEGT e W pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi [x]
        (Some x) None t3 0 Hent Htk ltac:(rewrite addm3_07, Hpl; reflexivity)
        ltac:(right; exists 3%nat, x; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
        ltac:(left; split; reflexivity) Hc1 Hl1 Hcp1). }
    intros W' c' _ (fq & Hfx & H). exists fq. split; [exact Hfx | right; exact H].
  + exfalso. rewrite branch_ltu_U, U_lit, (U_atom E 23 (vr_ntok (e_D e) - 1) EE23 ltac:(lia)) in Hc by lia.
    apply Z.ltb_ge in Hc. lia.
- (* five words or more: the index block with j = 4 *)
  cbn [length] in Hnt.
  destruct tp' as [|t4 tp'']; cbn [length] in Hlen; try lia.
  pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: t4 :: tp'') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28312
    [t1; t2; t3; t4] Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19
    ltac:(intros [|[|[|[|i]]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | exact Hi | destruct i; discriminate])
    ltac:(cbn; lia)) as HS.
  remember (E07 regsc (shadow_addr F + 4) F [t1; t2; t3; t4]) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
  pose proof (env_agree07 regsc (shadow_addr F + 4) F [t1; t2; t3; t4]) as HAE. rewrite <- HE in HAE.
  assert (EE19 : ew E 19 = Z_to_bv 64 (F + 32)) by (rewrite HE, (E07_reg _ _ _ _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
  assert (EE23 : ew E 23 = Z_to_bv 64 (vr_ntok (e_D e) - 1))
    by (rewrite HE, (E07_reg _ _ _ _ 23 (Z_to_bv 5 23) eq_refl); exact R23).
  assert (EE25 : ew E 25 = Z_to_bv 64 (vr_ntok (e_D e)))
    by (rewrite HE, (E07_reg _ _ _ _ 25 (Z_to_bv 5 25) eq_refl); exact R25).
  assert (X37 : ew E 37 = Z_to_bv 64 t4) by (rewrite HE; apply (E07_ext _ _ _ _ 5); [lia | reflexivity]).
  clear HE.
  (* 0x8d3c8: li a0,-24; beq s3,a0 (UBSan) *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  { exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_eq_U, (U_atom E 19 _ EE19) in Hc by lia.
  match type of Hc with context [U E (SLit ?z)] =>
    replace (U E (SLit z)) with (2 ^ 64 - 24) in Hc by (vm_compute; reflexivity) end.
  apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* 0x8d3d0: li a0,4; bltu s7,a0 *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ltu_U, U_lit, (U_atom E 23 (vr_ntok (e_D e) - 1) EE23 ltac:(lia)) in Hc by lia.
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* 0x8d3d8: slli a1,a0,3; not a2,s3; bltu a2,a1 (UBSan) *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  { exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_ltu_U in Hc.
  first [ rewrite (U_not07 E 19 _ EE19) in Hc by lia | rewrite (YI08.U_not E 19 _ EE19) in Hc by lia ].
  first [ match type of Hc with context [U E (SLit ?z)] =>
            replace (U E (SLit z)) with 32 in Hc by (vm_compute; reflexivity) end
        | match type of Hc with context [U E (SAlu ?op (SLit ?x) (SLit ?y))] =>
            replace (U E (SAlu op (SLit x) (SLit y))) with 32 in Hc by (vm_compute; reflexivity) end ].
  apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* 0x8d3e4: addi a0,a0,1; bltu a0,s9 *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V4 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms2) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V3 a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* 5 < ntok: six words or more, the refusal stub 0x8d4c4 *)
    rewrite branch_ltu_U, U_SLit, (U_atom E 25 (vr_ntok (e_D e)) EE25 ltac:(lia)) in Hc.
    change (zcanon 5) with 5 in Hc. apply Z.ltb_lt in Hc.
    destruct rest' as [|z rest'']; [cbn [length] in Hnt; lia|].
    assert (Hrej : PV.add_m atoi_a (u :: wi :: x :: y :: z :: rest'') = PV.reject) by apply addm5_07.
    assert (EH : vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false))
      by (unfold vr_h; rewrite (st_add _ _ Htk), Hrej; reflexivity).
    assert (EK : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP)
      by (unfold vr_k1; rewrite (evr_add _ _ _ Htk), Hrej; reflexivity).
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d4c4 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V5 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V4 a Ha). }
    clear HF HFr HG.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 27] HS HAE
      ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms3) (vr_base B e ++
      [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])).
    { rv07 Hrv KR regsc. }
    destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: t4 :: tp'') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms3) memc
      (ms_mem ms3) mdc mdv3 Hcore Hline Hcopy HJ V5 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
      as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    apply SRr_ret. exists fx. split; [apply fxrel_refl|]. left. unfold vr_atpr.
    replace (BASE + (AF_verbs_receive + (0x8d4c4 - 0x8ce4c))) with (vr_pc 0x8d4c4) by (unfold vr_pc; lia).
    exact (pr07c4 e W pos F q c (t0 :: t1 :: t2 :: t3 :: t4 :: tp'') lyc Sc (ms_regs ms3) (ms_mem ms3) mdv3 k nm
      EH EK ltac:(rewrite Htk; cbn [length]; lia) Hc1 Hl1 Hcp1).
  + (* ntok <= 5: five words, the client tok[4] *)
    rewrite branch_ltu_U, U_SLit, (U_atom E 25 (vr_ntok (e_D e)) EE25 ltac:(lia)) in Hc.
    change (zcanon 5) with 5 in Hc. apply Z.ltb_ge in Hc.
    destruct rest' as [|z rest'']; [|cbn [length] in Hnt; lia].
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d454 - 0x8ce4c)).
    { awr07. }
    mdv_set.
    assert (V5 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms3) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V4 a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 25) T25. rewrite X37 in T25.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms3)
      (vr_base B e ++ [(18, q); (19, F + 32); (22, F); (25, t4); (26, t3)])).
    { rv07 Hrv KR regsc. }
    destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: t4 :: tp'') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms3) memc
      (ms_mem ms3) mdc mdv3 Hcore Hline Hcopy HJ V5 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
      as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + (AF_verbs_receive + (0x8d454 - 0x8ce4c))) with (vr_pc 0x8d454) by (unfold vr_pc; lia).
    eapply SRr_mono.
    { exact (LEGT e W pos F q c (t0 :: t1 :: t2 :: t3 :: t4 :: tp'') lyc Sc (ms_regs ms3) (ms_mem ms3) mdv3 k nm u wi
        [x; y] (Some x) (Some y) t3 t4 Hent Htk ltac:(rewrite addm4_07, Hpl; reflexivity)
        ltac:(right; exists 3%nat, x; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
        ltac:(right; exists 4%nat, y; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
        Hc1 Hl1 Hcp1). }
    intros W' c' _ (fq & Hfx & H). exists fq. split; [exact Hfx | right; exact H].
Qed.

Lemma legDn : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: x :: rest -> PV.is_placement_m x = false ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, F + 32); (21, vr_ntok (e_D e)); (22, F); (23, vr_ntok (e_D e) - 1);
   (25, vr_ntok (e_D e)); (27, shadow_addr F + 4)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 28260)) memc (seg_rom SEGS)) mdc)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
     (vr_atpr (fx := fq) B MT 0x8d4c4 e W' cf' \/ vr_athd (fx := fq) B MT 0x8d4d0 e W' cf')).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest Hent Htk Hnp Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (HF_bounds07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore) as HFb.
pose proof HFb as [HFlo HFhi].
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (4 + length rest)) by (unfold vr_ntok; rewrite Htk; cbn [length]; lia).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (toks_le_64 (e_D e)); lia).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 (F + 32)) by (apply (rv_get07 regsc _ 19 _ Hrv); cbn; tauto).
assert (R25 : getr regsc (Z_to_bv 5 25) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 25 _ Hrv); cbn; tauto).
destruct tp as [|t0 [|t1 [|t2 [|t3 tp']]]]; cbn [length] in Hlen; try lia.
(* 0x8d394: li s10,0; li a0,3; j 0x8d3d8; slli a1,a0,3; not a2,s3; bltu a2,a1 (UBSan) *)
pose proof (seed_core B MT e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 28260
  [t1; t2; t3] Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R19
  ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
  ltac:(cbn; lia)) as HS.
remember (E07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc (shadow_addr F + 4) F [t1; t2; t3]) as HAE. rewrite <- HE in HAE.
assert (EE19 : ew E 19 = Z_to_bv 64 (F + 32)) by (rewrite HE, (E07_reg _ _ _ _ 19 (Z_to_bv 5 19) eq_refl); exact R19).
assert (EE25 : ew E 25 = Z_to_bv 64 (vr_ntok (e_D e)))
  by (rewrite HE, (E07_reg _ _ _ _ 25 (Z_to_bv 5 25) eq_refl); exact R25).
assert (X36 : ew E 36 = Z_to_bv 64 t3) by (rewrite HE; apply (E07_ext _ _ _ _ 4); [lia | reflexivity]).
clear HE.
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. pose proof HFb as [HFlo0 HFhi0]. pose proof asan_consts as (CC0 & _).
  rewrite branch_ltu_U in Hc.
  first [ rewrite (U_not07 E 19 _ EE19) in Hc by lia | rewrite (YI08.U_not E 19 _ EE19) in Hc by lia ].
  first [ match type of Hc with context [U E (SLit ?z)] =>
            replace (U E (SLit z)) with 24 in Hc by (vm_compute; reflexivity) end
        | match type of Hc with context [U E (SAlu ?op (SLit ?x) (SLit ?y))] =>
            replace (U E (SAlu op (SLit x) (SLit y))) with 24 in Hc by (vm_compute; reflexivity) end ].
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x8d3e4: addi a0,a0,1; bltu a0,s9 *)
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
{ intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* 4 < ntok: five words or more, the refusal stub 0x8d4c4 *)
  rewrite branch_ltu_U, U_SLit, (U_atom E 25 (vr_ntok (e_D e)) EE25 ltac:(lia)) in Hc.
  change (zcanon 4) with 4 in Hc. apply Z.ltb_lt in Hc.
  destruct rest as [|y rest']; [cbn [length] in Hnt; lia|].
  assert (Hrej : PV.add_m atoi_a (u :: wi :: x :: y :: rest') = PV.reject).
  { destruct rest' as [|z rest'']; [rewrite addm4_07, Hnp; reflexivity | apply addm5_07]. }
  assert (EH : vr_h (e_R e) (e_D e) = (e_R e, resp (-902), false))
    by (unfold vr_h; rewrite (st_add _ _ Htk), Hrej; reflexivity).
  assert (EK : vr_k1 (e_R e) (e_D e) = 2 + EV_SUP_RESP)
    by (unfold vr_k1; rewrite (evr_add _ _ _ Htk), Hrej; reflexivity).
  paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d4c4 - 0x8ce4c)).
  { awr07. }
  mdv_set.
  assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
  clear HF HFr HG.
  pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
  assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++
    [(19, F + 32); (18, q); (21, vr_ntok (e_D e)); (22, F); (27, shadow_addr F + 4)])).
  { rv07 Hrv KR regsc. }
  destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc
    (ms_mem ms1) mdc mdv1 Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
    as (Hc1 & Hl1 & Hcp1).
  pmkst HS.
  apply SRr_ret. exists fx. split; [apply fxrel_refl|]. left. unfold vr_atpr.
  replace (BASE + (AF_verbs_receive + (0x8d4c4 - 0x8ce4c))) with (vr_pc 0x8d4c4) by (unfold vr_pc; lia).
  exact (pr07c4 e W pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm
    EH EK ltac:(rewrite Htk; cbn [length]; lia) Hc1 Hl1 Hcp1).
- (* ntok <= 4: four words, the client tok[3] *)
  rewrite branch_ltu_U, U_SLit, (U_atom E 25 (vr_ntok (e_D e)) EE25 ltac:(lia)) in Hc.
  change (zcanon 4) with 4 in Hc. apply Z.ltb_ge in Hc.
  destruct rest as [|y rest']; [|cbn [length] in Hnt; lia].
  paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d454 - 0x8ce4c)).
  { awr07. }
  mdv_set.
  assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
  clear HF HFr HG.
  prreg HS (Z_to_bv 5 25) T25. prreg HS (Z_to_bv 5 26) T26. rewrite X36 in T25.
  pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22; 24] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (Hrv1 : vr_rv (ms_regs ms1)
    (vr_base B e ++ [(18, q); (19, F + 32); (22, F); (25, t3); (26, 0)])).
  { rv07 Hrv KR regsc. }
  destruct (RUN07 e pos F q c (t0 :: t1 :: t2 :: t3 :: tp') _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc
    (ms_mem ms1) mdc mdv1 Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn)
    as (Hc1 & Hl1 & Hcp1).
  pmkst HS.
  replace (BASE + (AF_verbs_receive + (0x8d454 - 0x8ce4c))) with (vr_pc 0x8d454) by (unfold vr_pc; lia).
  eapply SRr_mono.
  { exact (LEGT e W pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi [x]
      None (Some x) 0 t3 Hent Htk ltac:(rewrite addm3_07, Hnp; reflexivity)
      ltac:(left; split; reflexivity)
      ltac:(right; exists 3%nat, x; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
      Hc1 Hl1 Hcp1). }
  intros W' c' _ (fq & Hfx & H). exists fq. split; [exact Hfx | right; exact H].
Qed.

End e.
End f.
End d.
