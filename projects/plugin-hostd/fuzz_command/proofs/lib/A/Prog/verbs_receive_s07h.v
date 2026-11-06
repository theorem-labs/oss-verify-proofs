(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S07 (route add, 0x8d8fc) of the walk of verbs_receive on the ASan build
   of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v, vr_s07_stmt): the client decision after the
   placement test.
   legDp, 0x8d9c4 (tok[3] is a placement, s10 = tok[3]): `li a0,4; bltu s11,a0,0x8da5c` (four words: no client,
   `li s9,0; j 0x8da70`), else `addi a1,a0,1; bgeu a1,s9,0x8da64` (five words: the client tok[4],
   `slli a0,a0,3; add a0,s6,a0; ld s9,0(a0)`), else the refusal 0x8d9d4.
   legDn, 0x8d98c (tok[3] is no placement): `li s10,0; li a0,3; j 0x8d9cc; addi a1,a0,1; bgeu a1,s9,0x8da64` (four
   words: the client tok[3]), else the refusal 0x8d9d4.
   The add tail (verbs_receive_s07g.v legT) or the refusal (verbs_receive_s07d.v legR) then reach JB 0x8dae4, at the
   FP state their printf-reaching callee (sup_add, sup_resp) returned at (hdF07). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_add_c sup_add_c sup_reply_code_c sup_resp_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c verbs_receive_s07d verbs_receive_s07e verbs_receive_s07f
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
Hypothesis TSUP_RESP : tsup_resp_spec B MT.
Hypothesis TSUP_ADD : tsup_add_spec B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, @tdescriptors_add_spec fx0 rc SK PI B MT.
Hypothesis AATOI : RtNumber.aatoi_realizes SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis HB : AF0m.CmdBSyms B.
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
Let LEGR := legR B MT TSUP_RESP HB TL MTL SIGP ROA RRO RPG RECC PROGU.
Let LEGT := legT B MT TSUP_ADD TSUP_REPLY_CODE TDESCRIPTORS_ADD AATOI HB TL MTL SIGP BLKT ROA RRO RPG RECC PROGU.

Lemma legDp : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest t3,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: x :: rest -> PV.is_placement_m x = true -> nth_error tp 3 = Some t3 ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, c); (22, F + 32); (25, vr_ntok (e_D e)); (26, t3); (27, vr_ntok (e_D e) - 1)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 29920)) memc (seg_rom SEGS)) mdc) (hdF07 B MT 0x8dae4 e).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest t3 Hent Htk Hpl Ht3 Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (4 + length rest)) by (unfold vr_ntok; rewrite Htk; cbn [length]; lia).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (toks_le_64 (e_D e)); lia).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regsc _ 22 _ Hrv); cbn; tauto).
assert (R25 : getr regsc (Z_to_bv 5 25) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 25 _ Hrv); cbn; tauto).
assert (R27 : getr regsc (Z_to_bv 5 27) = w64 (vr_ntok (e_D e) - 1)) by (apply (rv_get07 regsc _ 27 _ Hrv); cbn; tauto).
destruct rest as [|y rest'].
- (* four words: no client *)
  cbn [length] in Hnt.
  pose proof (seed_core B MT e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 29920 []
    Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R22
    ltac:(intros [|i] p0 Hi; discriminate) ltac:(cbn; lia)) as HS.
  remember (E07 regsc q (shadow_addr F + 4) F c []) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
  pose proof (env_agree07 regsc q (shadow_addr F + 4) F c []) as HAE. rewrite <- HE in HAE.
  assert (EE27 : ew E 27 = getr regsc (Z_to_bv 5 27)) by (rewrite HE; apply E07_reg; reflexivity).
  clear HE.
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* s11 < 4: `li s9,0; j 0x8da70` *)
    clear Hc.
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8da70 - 0x8d480)).
    { awr07. }
    mdv_set.
    assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 25) T25.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ [(18, q); (19, c); (22, F + 32); (25, 0); (26, t3)])).
    { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
      - unfold vr_base in Hin. cbn in Hin.
        destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
      - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          first [exact T25 | rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto]. }
    destruct (RUN07 e pos F q c tp _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms0) memc (ms_mem ms0) mdc mdv0
      Hcore Hline Hcopy HJ V2 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + 30092) with (vr_pc 0x8da70) by (unfold vr_pc, AF_verbs_receive; lia).
    exact (LEGT e W pos F q c tp lyc Sc (ms_regs ms0) (ms_mem ms0) mdv0 k nm u wi [x] (Some x) None t3 0 Hent Htk
      ltac:(rewrite addm3_07, Hpl; reflexivity)
      ltac:(right; exists 3%nat, x; split; [reflexivity | split; [exact Ht3 | rewrite Htk; reflexivity]])
      ltac:(left; split; reflexivity) Hc1 Hl1 Hcp1).
  + exfalso. rewrite branch_ltu_U, U_lit, (U_atom E 27 (vr_ntok (e_D e) - 1)) in Hc
      by (try (rewrite EE27, R27; reflexivity); lia).
    apply Z.ltb_ge in Hc. lia.
- (* five words or more *)
  cbn [length] in Hnt.
  destruct tp as [|t0 [|t1 [|t2 [|t3' [|t4 tp']]]]]; cbn [length] in Hlen; try lia.
  cbn in Ht3. injection Ht3 as <-.
  pose proof (seed_core B MT e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 29920 [t1; t2; t3'; t4]
    Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R22
    ltac:(intros [|[|[|[|i]]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | exact Hi | destruct i; discriminate])
    ltac:(cbn; lia)) as HS.
  remember (E07 regsc q (shadow_addr F + 4) F c [t1; t2; t3'; t4]) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
  pose proof (env_agree07 regsc q (shadow_addr F + 4) F c [t1; t2; t3'; t4]) as HAE. rewrite <- HE in HAE.
  assert (EE27 : ew E 27 = getr regsc (Z_to_bv 5 27)) by (rewrite HE; apply E07_reg; reflexivity).
  assert (EE25 : ew E 25 = getr regsc (Z_to_bv 5 25)) by (rewrite HE; apply E07_reg; reflexivity).
  assert (X39 : ew E 39 = Z_to_bv 64 t4) by (rewrite HE; apply (E07_ext _ _ _ _ _ _ 7); [lia | reflexivity]).
  clear HE.
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
    by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ltu_U, U_lit, (U_atom E 27 (vr_ntok (e_D e) - 1)) in Hc
      by (try (rewrite EE27, R27; reflexivity); lia).
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* 0x8d9cc: addi a1,a0,1; bgeu a1,s9,0x8da64 *)
  paj_run_sh RUNP HS HJ.
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  + (* five words: the client tok[4] *)
    rewrite branch_geu_U, U_lit, (U_atom E 25 (vr_ntok (e_D e))) in Hc by (try (rewrite EE25, R25; reflexivity); lia).
    apply negb_true_iff, Z.ltb_ge in Hc.
    destruct rest' as [|z rest'']; [|cbn [length] in Hnt; lia].
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8da70 - 0x8d480)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    prreg HS (Z_to_bv 5 25) T25. rewrite X39 in T25.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22; 26] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ [(18, q); (19, c); (22, F + 32); (25, t4); (26, t3')])).
    { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
      - unfold vr_base in Hin. cbn in Hin.
        destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
      - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          first [exact T25 | rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto]. }
    destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc (ms_mem ms1) mdc mdv1
      Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + 30092) with (vr_pc 0x8da70) by (unfold vr_pc, AF_verbs_receive; lia).
    exact (LEGT e W pos F q c (t0 :: t1 :: t2 :: t3' :: t4 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm u wi [x; y]
      (Some x) (Some y) t3' t4 Hent Htk
      ltac:(rewrite addm4_07, Hpl; reflexivity)
      ltac:(right; exists 3%nat, x; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
      ltac:(right; exists 4%nat, y; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
      Hc1 Hl1 Hcp1).
  + (* six words or more: the refusal *)
    rewrite branch_geu_U, U_lit, (U_atom E 25 (vr_ntok (e_D e))) in Hc by (try (rewrite EE25, R25; reflexivity); lia).
    apply negb_false_iff, Z.ltb_lt in Hc.
    destruct rest' as [|z rest'']; [cbn [length] in Hnt; lia|].
    paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d9d4 - 0x8d480)).
    { awr07. }
    mdv_set.
    assert (V3 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
    { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V2 a Ha). }
    clear HF HFr HG.
    pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (Hrv1 : vr_rv (ms_regs ms1) (vr_base B e ++ [(18, q); (19, c); (22, F + 32)])).
    { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
      - unfold vr_base in Hin. cbn in Hin.
        destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
          (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
      - cbn in Hin. destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-;
          (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto). }
    destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms1) memc (ms_mem ms1) mdc mdv1
      Hcore Hline Hcopy HJ V3 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
    pmkst HS.
    replace (BASE + 29936) with (vr_pc 0x8d9d4) by (unfold vr_pc, AF_verbs_receive; lia).
    exact (LEGR e W pos F q c (t0 :: t1 :: t2 :: t3' :: t4 :: tp') lyc Sc (ms_regs ms1) (ms_mem ms1) mdv1 k nm
      (u :: wi :: x :: y :: z :: rest'') Hent Htk
      (addm5_07 u wi x y z rest'') ltac:(cbn [length]; lia) Hc1 Hl1 Hcp1).
Qed.

Lemma legDn : forall e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest,
vr_ent B MT e ->
PV.toks (e_D e) = PV.Lit.verb_add :: u :: wi :: x :: rest -> PV.is_placement_m x = false ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(18, q); (19, c); (22, F + 32); (25, vr_ntok (e_D e))]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 29864)) memc (seg_rom SEGS)) mdc) (hdF07 B MT 0x8dae4 e).
Proof.
intros e W pos F q c tp lyc Sc regsc memc mdc k nm u wi x rest Hent Htk Hnp Hcore Hline Hcopy.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & HDn & _).
pose proof Hcore as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof (core_regs07 B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcore)
  as (R2 & R3 & R4 & R8 & R9 & Hspz & Hs0 & Ho16 & Hs1 & Hceil & H47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hcopy as (_ & (_ & Hlen & _ & _)).
rewrite Htk in Hlen. cbn [length] in Hlen.
assert (Hnt : vr_ntok (e_D e) = Z.of_nat (4 + length rest)) by (unfold vr_ntok; rewrite Htk; cbn [length]; lia).
assert (Hnt64 : vr_ntok (e_D e) <= 64) by (unfold vr_ntok; pose proof (toks_le_64 (e_D e)); lia).
assert (R22 : getr regsc (Z_to_bv 5 22) = w64 (F + 32)) by (apply (rv_get07 regsc _ 22 _ Hrv); cbn; tauto).
assert (R25 : getr regsc (Z_to_bv 5 25) = w64 (vr_ntok (e_D e))) by (apply (rv_get07 regsc _ 25 _ Hrv); cbn; tauto).
destruct tp as [|t0 [|t1 [|t2 [|t3 tp']]]]; cbn [length] in Hlen; try lia.
(* 0x8d98c: li s10,0; li a0,3; j 0x8d9cc; addi a1,a0,1; bgeu a1,s9,0x8da64 *)
pose proof (seed_core B MT e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 29864 [t1; t2; t3]
  Hcore Hcopy ltac:(left; reflexivity) ltac:(right; left; reflexivity) R22
  ltac:(intros [|[|[|i]]] p0 Hi; cbn in Hi |- *; [exact Hi | exact Hi | exact Hi | destruct i; discriminate])
  ltac:(cbn; lia)) as HS.
remember (E07 regsc q (shadow_addr F + 4) F c [t1; t2; t3]) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply E07_env).
pose proof (env_agree07 regsc q (shadow_addr F + 4) F c [t1; t2; t3]) as HAE. rewrite <- HE in HAE.
assert (EE25 : ew E 25 = getr regsc (Z_to_bv 5 25)) by (rewrite HE; apply E07_reg; reflexivity).
assert (X38 : ew E 38 = Z_to_bv 64 t3) by (rewrite HE; apply (E07_ext _ _ _ _ _ _ 6); [lia | reflexivity]).
clear HE.
paj_run_sh RUNP HS HJ.
{ awr07. }
mdv_set.
assert (V : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W memc a)
  by (intros a Ha; exact (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha)).
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* four words: the client tok[3] *)
  rewrite branch_geu_U, U_lit, (U_atom E 25 (vr_ntok (e_D e))) in Hc by (try (rewrite EE25, R25; reflexivity); lia).
  apply negb_true_iff, Z.ltb_ge in Hc.
  destruct rest as [|y rest']; [|cbn [length] in Hnt; lia].
  paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8da70 - 0x8d480)).
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  prreg HS (Z_to_bv 5 25) T25. prreg HS (Z_to_bv 5 26) T26. rewrite X38 in T25.
  pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ [(18, q); (19, c); (22, F + 32); (25, t3); (26, 0)])).
  { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
    - unfold vr_base in Hin. cbn in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
        (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
    - cbn in Hin. destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
        first [exact T25 | exact T26 | rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto]. }
  destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms0) memc (ms_mem ms0) mdc mdv0
    Hcore Hline Hcopy HJ V2 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
  pmkst HS.
  replace (BASE + 30092) with (vr_pc 0x8da70) by (unfold vr_pc, AF_verbs_receive; lia).
  exact (LEGT e W pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc (ms_regs ms0) (ms_mem ms0) mdv0 k nm u wi [x] None (Some x)
    0 t3 Hent Htk
    ltac:(rewrite addm3_07, Hnp; reflexivity)
    ltac:(left; split; reflexivity)
    ltac:(right; exists 3%nat, x; split; [reflexivity | split; [reflexivity | rewrite Htk; reflexivity]])
    Hc1 Hl1 Hcp1).
- (* five words or more: the refusal *)
  rewrite branch_geu_U, U_lit, (U_atom E 25 (vr_ntok (e_D e))) in Hc by (try (rewrite EE25, R25; reflexivity); lia).
  apply negb_false_iff, Z.ltb_lt in Hc.
  destruct rest as [|y rest']; [cbn [length] in Hnt; lia|].
  paj_run_to_sh RUNTOP HS HJ (AF_verbs_receive + (0x8d9d4 - 0x8d480)).
  { awr07. }
  mdv_set.
  assert (V2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W memc a).
  { intros a Ha. rewrite (ro_frame_view _ _ _ _ _ HFr ltac:(roF) a Ha). exact (V a Ha). }
  clear HF HFr HG.
  pose proof (kept_regs07 E _ _ regsc _ [2; 3; 4; 8; 9; 18; 19; 22] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (Hrv1 : vr_rv (ms_regs ms0) (vr_base B e ++ [(18, q); (19, c); (22, F + 32)])).
  { apply rv_intro07. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
    - unfold vr_base in Hin. cbn in Hin.
      destruct Hin as [E1|[E1|[E1|[E1|[E1|[]]]]]]; injection E1 as <- <-;
        (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto).
    - cbn in Hin. destruct Hin as [E1|[E1|[E1|[]]]]; injection E1 as <- <-;
        (rewrite KR by (cbn; tauto); apply (rv_get07 regsc _ _ _ Hrv); cbn; tauto). }
  destruct (RUN07 e pos F q c _ _ _ _ _ _ _ _ _ _ _ _ _ W regsc (ms_regs ms0) memc (ms_mem ms0) mdc mdv0
    Hcore Hline Hcopy HJ V2 Hrv1 ltac:(left; reflexivity) ltac:(right; left; reflexivity) HDn) as (Hc1 & Hl1 & Hcp1).
  pmkst HS.
  replace (BASE + 29936) with (vr_pc 0x8d9d4) by (unfold vr_pc, AF_verbs_receive; lia).
  assert (Hrej : PV.add_m atoi_a (u :: wi :: x :: y :: rest') = PV.reject).
  { destruct rest' as [|z rest'']; [rewrite addm4_07, Hnp; reflexivity | apply addm5_07]. }
  exact (LEGR e W pos F q c (t0 :: t1 :: t2 :: t3 :: tp') lyc Sc (ms_regs ms0) (ms_mem ms0) mdv0 k nm
    (u :: wi :: x :: y :: rest') Hent Htk
    Hrej ltac:(cbn [length]; lia) Hc1 Hl1 Hcp1).
Qed.

End e.
End f.
End d.
