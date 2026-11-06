(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 1428 of its 1523 lines of code are new or changed and 2594 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/talk_take.v; 428 of its 512 lines of code are new or changed and 1439 lines of the source are left out. *)
(* talk on image A: the attribute loop of the first RTM_NEWLINK, the piece TK_ATTR of lib/A/Prog/talk_defs.v, and
   its step TK_A598 (listing (internal path) (internal record, sha256 5526460cb5be), +0x30c ..
   +0x3f4 and +0x598 .. +0x5ac). One turn at (a, al) of chunk c (b = g + 4096 c), the attributes acc seen so far:
   - ta_at, +0x30c: `add a0, s4, s11`, a0 = b + a; the run stops at +0x310 (fresh state tk_ss_at);
   - ta_af, +0x310 (fresh state tk_ss_af: the attribute's four bytes at b + a are the atoms 49 .. 52, the spilled
     words are the frame region tk_frs, the SH entry tk_SH_af covers every instrumented check):
       l < 4 or al < l: +0xb4 with a1 = 0 (the walk's answer is acc);
       type 18 (IFLA_LINKINFO), l >= 8: s8 = a + 4, s9 = l - 4, the inner loop +0x3f8 (TK_KIND);
       type 18, l < 8: +0x598 (the inner walk of fewer than 4 bytes finds nothing);
       type 20 (IFLA_IFALIAS), the spilled alias flag clear: +0x3a0, take_text into the alias buffer (TK_TAKE_AL);
       type 20, the flag set (no alias buffer): +0x598, the alias text found but stored nowhere;
       another type: +0x598;
     s5 = l on every path;
   - ta_as, +0x598 (fresh state tk_ss_as): s5 := (l + 3) & 0x1fffc = NL_ALIGN(l), s6 -= it, s11 += it; `blt s6, 4`:
     +0x2a0 / +0xb4 with a1 = 0, else +0x30c, the next turn. This is TK_A598, proved from the next turn.
   The runs write no byte (every region is read only). The Post at +0xb4 goes through talk_ret.v tk_post_of: the
   code is talk_rc_model = 0 and the attributes are the walk's answer, attr_scan from (a, al) (talk_spec.v
   as_short .. as_other).
   tk_attr_ok: induction on the fuel of attr_scan.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec talk_ret talk_mkit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the registers of the attribute stage that a run keeps: the journal's sp, gp, tp, s0, s1, s4, s7 and the stage's
   constants s3, a5, a6, a7 (ta_kr), and s6, s11 (ta_k) *)
Definition ta_kr : list (bv 5 * sv) :=
  [(2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0); (9%bv, SOff 9 0); (20%bv, SOff 20 0);
   (23%bv, SOff 23 0)] ++ tk_ov_at.
Definition ta_k : list (bv 5 * sv) := ta_kr ++ [(22%bv, SOff 22 0); (27%bv, SOff 27 0)].

(* the unsigned value of a symbolic value whose atoms lie below the runner's fresh atoms *)
Lemma tq_U_agree : forall E E' v, YP06.env_agree 512 E E' -> sv_atoms_lt 512 v = true -> U E' v = U E v.
Proof. intros E E' v HA Hv. unfold U. rewrite (YP06.sv_denot_agree 512 E E' v HA Hv). reflexivity. Qed.

Lemma tq_S_agree : forall E E' v, YP06.env_agree 512 E E' -> sv_atoms_lt 512 v = true -> Sg E' v = Sg E v.
Proof. intros E E' v HA Hv. unfold Sg. rewrite (YP06.sv_denot_agree 512 E E' v HA Hv). reflexivity. Qed.

Lemma tq_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' -> rs_read_only rs = true -> m' = m.
Proof. intros E rs m m' HF Hro. exact (frame_of_read_only E rs m m' Hro HF). Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation kbs := (tc_kbs c).
#[local] Notation mbs := (tc_mbs c).

(* ---- the registers a run keeps ------------------------------------------------------------------------------------ *)
Lemma ta_kr_ok : forall regs xs b a al, tk_rat regs b a al ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) ta_kr.
Proof.
  intros regs xs b a al HRAT. unfold ta_kr. apply Forall_app. split; [|exact (tk_ov_at_ok c regs xs b a al HRAT)].
  repeat (apply Forall_cons; [cbn [fst snd]; apply tq_den_reg; [lia | reflexivity] |]). apply Forall_nil.
Qed.

Lemma ta_k_ok : forall regs xs b a al, tk_rat regs b a al ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) ta_k.
Proof.
  intros regs xs b a al HRAT. unfold ta_k. apply Forall_app. split; [exact (ta_kr_ok regs xs b a al HRAT)|].
  repeat (apply Forall_cons; [cbn [fst snd]; apply tq_den_reg; [lia | reflexivity] |]). apply Forall_nil.
Qed.

Lemma ta_kr_keep : forall regs regs2, Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) ta_kr ->
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  (tk_rs0 c regs -> tk_rs0 c regs2) /\ getr regs2 20 = getr regs 20 /\
  getr regs2 19 = getr regs 19 /\ getr regs2 15 = getr regs 15 /\ getr regs2 16 = getr regs 16 /\
  getr regs2 17 = getr regs 17.
Proof.
  intros regs regs2 HF. unfold ta_kr, tk_ov_at in HF. cbn [app] in HF.
  apply Forall_cons_iff in HF as [K2 HF]. apply Forall_cons_iff in HF as [K3 HF].
  apply Forall_cons_iff in HF as [K4 HF]. apply Forall_cons_iff in HF as [K8 HF].
  apply Forall_cons_iff in HF as [K9 HF]. apply Forall_cons_iff in HF as [K20 HF].
  apply Forall_cons_iff in HF as [K23 HF]. apply Forall_cons_iff in HF as [K19 HF].
  apply Forall_cons_iff in HF as [K15 HF]. apply Forall_cons_iff in HF as [K16 HF].
  apply Forall_cons_iff in HF as [K17 _]. cbn [fst] in *.
  unfold tk_rs0. rewrite K8, K9, K23. intuition.
Qed.

Lemma ta_k_keep : forall regs regs2 b a al, Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) ta_k ->
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  (tk_rs0 c regs -> tk_rs0 c regs2) /\ (tk_rat regs b a al -> tk_rat regs2 b a al).
Proof.
  intros regs regs2 b a al HF. unfold ta_k in HF. apply Forall_app in HF as [HF1 HF2].
  destruct (ta_kr_keep regs regs2 HF1) as (K2 & K3 & K4 & K0 & K20 & K19 & K15 & K16 & K17).
  apply Forall_cons_iff in HF2 as [K22 HF2]. apply Forall_cons_iff in HF2 as [K27 _]. cbn [fst] in *.
  refine (conj K2 (conj K3 (conj K4 (conj K0 _)))).
  unfold tk_rat. rewrite K20, K27, K22, K19, K15, K16, K17. exact (fun H => H).
Qed.

(* the invariant at the end of a run that wrote no byte, the memory as at the fresh state *)
Lemma ta_inv : forall regs mem md regs2 md2,
  tk_inv SK B c regs mem md ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  tk_inv SK B c regs2 mem md2.
Proof.
  intros regs mem md regs2 md2 HI HJ Hfd Hfs K2 K3 K4.
  apply (tk_inv_step SK B c HC regs mem md regs2 mem md2 (fun _ => False) HI HJ Hfd Hfs);
    [intros a _ _; reflexivity | intros a [] | intros a Hp; exact Hp | exact K2 | exact K3 | exact K4].
Qed.

Lemma ta_post : forall regs mem md xs E' ss ms md2 b a al,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs b a al ->
  st_ok_pi SEGS VAL E' ss (restrict (w_H W) ms) -> YP06.env_agree 512 (tk_E c regs xs) E' ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) ta_k = true ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  tk_inv SK B c (ms_regs ms) mem md2 /\ tk_rs0 c (ms_regs ms) /\ tk_rat (ms_regs ms) b a al.
Proof.
  intros regs mem md xs E' ss ms md2 b a al HI H0 HRAT HS HAG Hck HJ Hfd Hfs.
  pose proof (tq_keep_regs (w_H W) (tk_E c regs xs) E' ss ms regs ta_k HS HAG (ta_k_ok regs xs b a al HRAT) Hck) as KR.
  destruct (ta_k_keep regs (ms_regs ms) b a al KR) as (K2 & K3 & K4 & K0 & KT).
  exact (conj (ta_inv regs mem md (ms_regs ms) md2 HI HJ Hfd Hfs K2 K3 K4) (conj (K0 H0) (KT HRAT))).
Qed.

(* the buffers when the alias flag is set (no alias buffer): an alias text is stored nowhere *)
Lemma ta_bufs_alias : forall mem ak aa s, tk_flag (tk_ad c) (tk_an c) <> 0 ->
  tk_bufs c mem (Attrs ak aa) -> tk_bufs c mem (Attrs ak (Some s)).
Proof.
  intros mem ak aa s Hf (B1 & B2 & B3 & B4 & B5 & B6).
  assert (Hz : tk_ad c = 0 \/ tk_an c = 0).
  { revert Hf. unfold tk_flag. destruct (Z.eqb_spec (tk_ad c) 0) as [E1|E1]; [intros _; left; exact E1|].
    destruct (Z.eqb_spec (tk_an c) 0) as [E2|E2]; [intros _; right; exact E2|]. cbn [orb]. intros Hf.
    exfalso. apply Hf. reflexivity. }
  refine (conj B1 (conj B2 (conj B3 (conj _ (conj B5 _))))).
  - intros pay _ H0 H1. exfalso. destruct Hz; lia.
  - intros Hn. discriminate Hn.
Qed.

Lemma ta_flag0 : tk_flag (tk_ad c) (tk_an c) = 0 -> tk_ad c <> 0 /\ tk_an c <> 0.
Proof.
  unfold tk_flag. destruct (Z.eqb_spec (tk_ad c) 0), (Z.eqb_spec (tk_an c) 0); cbn [orb]; intros H;
    try discriminate H. split; assumption.
Qed.

Lemma ta_flag_rng : 0 <= tk_flag (tk_ad c) (tk_an c) <= 1.
Proof. unfold tk_flag. destruct ((tk_ad c =? 0) || (tk_an c =? 0)); lia. Qed.

(* ---- the tactics of the runs ------------------------------------------------------------------------------------- *)
(* the write permission of a run whose regions are read only *)
Ltac ta_awr :=
  let x := fresh "x" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (rr & Hin & Hx); vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; exfalso; clear - Hx; lia | ]);
  destruct Hin.
(* the agreement of the environment a run ends in with the fresh state's E0 below the fresh atoms *)
Ltac ta_ag E0 HAG :=
  try clear HAG;
  lazymatch goal with HS : st_ok_pi _ _ ?E' _ _ |- _ => assert (HAG : YP06.env_agree 512 E0 E') by tq_agree end.
(* the memory a later run ends in is the fresh state's *)
Ltac ta_mem Hm HF HFr HG :=
  let Hm' := fresh "Hm" in
  pose proof (tq_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm';
  rewrite Hm in Hm'; clear Hm HF HFr HG; rename Hm' into Hm.
(* name the machine state and the model a run ends in; the memory is the fresh state's *)
Ltac ta_end md Hm HJ msF md2 Hfd Hfs :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end;
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ msF) |- _ => pmkst HS end;
  rewrite Hm in HJ |- *;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end;
  assert (Hfd : m_fds md2 = m_fds md) by (unfold md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity);
  assert (Hfs : m_fs md2 = m_fs md) by (unfold md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

(* ---- +0x30c: `add a0, s4, s11` ---------------------------------------------------------------------------------- *)
Lemma ta_at : forall ci a al regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al ->
  0 <= ci < tk_nch c -> 0 <= a -> 0 <= al -> a + al <= Z.of_nat (length (tk_ck c ci)) ->
  (forall regs2 md2, tk_inv SK B c regs2 mem md2 -> tk_rs0 c regs2 -> tk_rat regs2 (tk_b ci) a al ->
     getr regs2 10 = w64 (tk_b ci + a) -> tk_goal SK B c (cfg_of regs2 (BASE + TP_AF) mem md2)) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_AT) mem md).
Proof.
  intros ci a al regs mem md HI H0 HRAT Hci Ha Hal Hlen K.
  destruct (tq_ck SK B c HC ci Hci) as (Lck & Lmax & Nch).
  pose proof H0 as (_ & _ & H23).
  pose proof HRAT as (H20 & H27 & _).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof (tk_st_ok SK B LV c HC regs mem md [] TP_AT tk_ov_at [] [] HI H23 (tk_ov_at_ok c regs [] (tk_b ci) a al HRAT)
    eq_refl (Forall_nil _) I I) as HS.
  pose proof (tk_E_env c regs []) as HEI.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs []) (mrestrict (w_H W) mem)) by constructor.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  assert (U27 : U (tk_E c regs []) (SOff 27 0) = a)
    by (apply (tk_U_reg c regs [] 27 27%bv); [lia | reflexivity | exact H27 | unfold NL_CHUNK_MAX in *; lia]).
  assert (U20 : U (tk_E c regs []) (SOff 20 0) = tk_b ci)
    by (apply (tk_U_reg c regs [] 20 20%bv);
        [lia | reflexivity | exact H20 | unfold tk_b, LA_G_NL, NL_CHUNK_MAX, NL_CHUNKS in *; lia]).
  unfold tk_goal in *.
  (* +0x30c: a0 := s4 + s11; the run stops at +0x310 *)
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AF.
  - intros x (r & Hin & _). unfold tk_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin.
  - lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
    assert (Hm : ms_mem ms1 = mem) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
    rewrite Hm in HJ. pmkst HS. rewrite Hm.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    assert (Hfd : m_fds md2 = m_fds md) by (unfold md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
    assert (Hfs : m_fs md2 = m_fs md) by (unfold md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).
    destruct (ta_post regs mem md [] _ _ ms1 md2 (tk_b ci) a al HI H0 HRAT HS ltac:(tq_agree)
      ltac:(vm_compute; reflexivity) HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
    tq_rreg HS (10%bv : bv 5) R10.
    apply K; [exact HI2 | exact H02 | exact HRAT2 |].
    rewrite R10. apply tk_den_of_U. apply (tq_U_add _ _ _ (tk_b ci) a U20 U27).
    unfold tk_b, LA_G_NL, NL_CHUNK_MAX, NL_CHUNKS in *. lia.
Qed.

(* ---- +0x598: the step to the next attribute, from the next turn ----------------------------------------------------- *)
Lemma ta_as : forall ci a al l acc f,
  (forall a' al' acc' regs mem md, tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a' al' ->
     tk_amem c mem (tk_b ci) acc' -> talk_rc_model (tk_K0 c) = 0 ->
     talk_attrs (tk_K0 c) = attr_scan f (tk_ck c ci) a' al' acc' -> 0 <= ci < tk_nch c -> 0 <= a' ->
     a' + al' <= Z.of_nat (length (tk_ck c ci)) -> 4 <= al' < Z.of_nat f ->
     tk_goal SK B c (cfg_of regs (BASE + TP_AT) mem md)) ->
  TK_RET SK B c ->
  talk_rc_model (tk_K0 c) = 0 ->
  talk_attrs (tk_K0 c) = attr_scan f (tk_ck c ci) (a + nl_align l) (al - nl_align l) acc ->
  0 <= ci < tk_nch c -> 0 <= a -> 4 <= l <= al -> a + al <= Z.of_nat (length (tk_ck c ci)) -> al < Z.of_nat f + 1 ->
  TK_A598 SK B c ci a al l acc.
Proof.
  intros ci a al l acc f IH HRET Hrc Hat Hci Ha Hl Hlen Hf regs mem md HI H0 HRAT H21 HAM.
  destruct (tq_ck SK B c HC ci Hci) as (Lck & Lmax & Nch).
  pose proof H0 as (_ & _ & H23).
  pose proof HRAT as (H20 & H27 & H22 & _).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof HAM as ((mb & Hmb & Hres) & HB & HSP).
  assert (CM : NL_CHUNK_MAX = 4096) by reflexivity.
  pose proof (tw_align_range l ltac:(lia)) as Ral.
  pose proof (tk_st_ok SK B LV c HC regs mem md [] TP_AS tk_ov_at [] [] HI H23 (tk_ov_at_ok c regs [] (tk_b ci) a al HRAT)
    eq_refl (Forall_nil _) I I) as HS.
  pose proof (tk_E_env c regs []) as HEI.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs []) (mrestrict (w_H W) mem)) by constructor.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E21 : ew (tk_E c regs []) 21 = Z_to_bv 64 l)
    by (rewrite (tk_E_reg c regs [] 21 21%bv) by (lia || reflexivity); exact H21).
  assert (E22 : ew (tk_E c regs []) 22 = Z_to_bv 64 al)
    by (rewrite (tk_E_reg c regs [] 22 22%bv) by (lia || reflexivity); exact H22).
  assert (E27 : ew (tk_E c regs []) 27 = Z_to_bv 64 a)
    by (rewrite (tk_E_reg c regs [] 27 27%bv) by (lia || reflexivity); exact H27).
  assert (UA : U (tk_E c regs []) (SAlu ALU_AND (SOff 21 3) (SLit 131068)) = nl_align l)
    by (apply (tq_U_land _ 21 l E21); lia).
  assert (S6 : Sg (tk_E c regs []) (SAlu ALU_SUB (SOff 22 0) (SAlu ALU_AND (SOff 21 3) (SLit 131068))) = al - nl_align l).
  { apply tq_Sg; [|lia]. rewrite U_SAlu, UA, (U_atom _ 22 al E22) by lia. cbn [zalu_raw]. reflexivity. }
  unfold tk_goal in *.
  (* +0x598 .. +0x5a8: s5 := NL_ALIGN(l), s6 -= s5, s11 += s5; stop at `blt s6, 4` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [intros x (r & Hin & _); unfold tk_ss in Hin; cbn [ss_mem In] in Hin; destruct Hin |].
  pose proof (tq_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite tq_br_lt, S6, (tq_Sg _ (SLit 4) 4 (U_SLit _ 4) ltac:(lia)) in Hc.
  - (* al - NL_ALIGN(l) < 4: +0x2a0, a1 = 0, +0xb4 *)
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [intros x (r & Hin & _); vm_compute in Hin; destruct Hin |].
    ta_mem Hm HF HFr HG.
    ta_end md Hm HJ msF md2 Hfd Hfs.
    pose proof (tq_keep_regs (w_H W) (tk_E c regs []) (tk_E c regs []) _ msF regs ta_kr HS ltac:(tq_agree)
      (ta_kr_ok regs [] (tk_b ci) a al HRAT) ltac:(vm_compute; reflexivity)) as KR.
    destruct (ta_kr_keep regs (ms_regs msF) KR) as (K2 & K3 & K4 & K0 & _).
    tq_rreg HS (11%bv : bv 5) R11.
    apply (HRET (ms_regs msF) mem md2 (ta_inv regs mem md (ms_regs msF) md2 HI HJ Hfd Hfs K2 K3 K4)
      (proj2 (proj2 (K0 H0)))).
    intros regs2 H10.
    apply (tk_post_of SK B c HC mem 0 acc mb Hmb Hres (eq_sym Hrc));
      [rewrite Hat; symmetry; apply as_short; lia | exact HB | rewrite H10, R11; reflexivity].
  - (* al - NL_ALIGN(l) >= 4: the next attribute, +0x30c *)
    apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AT; [intros x (r & Hin & _); vm_compute in Hin; destruct Hin |].
    ta_mem Hm HF HFr HG.
    ta_end md Hm HJ msF md2 Hfd Hfs.
    pose proof (tq_keep_regs (w_H W) (tk_E c regs []) (tk_E c regs []) _ msF regs ta_kr HS ltac:(tq_agree)
      (ta_kr_ok regs [] (tk_b ci) a al HRAT) ltac:(vm_compute; reflexivity)) as KR.
    destruct (ta_kr_keep regs (ms_regs msF) KR) as (K2 & K3 & K4 & K0 & K20 & K19 & K15 & K16 & K17).
    tq_rreg HS (22%bv : bv 5) R22. tq_rreg HS (27%bv : bv 5) R27.
    apply (IH (a + nl_align l) (al - nl_align l) acc (ms_regs msF) mem md2
      (ta_inv regs mem md (ms_regs msF) md2 HI HJ Hfd Hfs K2 K3 K4) (K0 H0)); try assumption.
    + unfold tk_rat. rewrite K20, K19, K15, K16, K17. pose proof HRAT as (R20 & _ & _ & R19 & R15 & R16 & R17).
      refine (conj R20 (conj _ (conj _ (conj R19 (conj R15 (conj R16 R17)))))).
      * rewrite R27. apply tk_den_of_U. rewrite Z.add_comm. apply (tq_U_add _ _ _ (nl_align l) a UA).
        -- apply (U_atom _ 27 a E27). lia.
        -- lia.
      * rewrite R22. apply tq_den_U. rewrite U_SAlu, UA, (U_atom _ 22 al E22) by lia; reflexivity.
    + lia.
    + lia.
    + lia.
Qed.
(* ---- +0x310: one attribute ---------------------------------------------------------------------------------------- *)
Lemma ta_af : forall ci a al acc f regs mem md,
  TK_RET SK B c -> TK_KIND SK B c -> TK_TAKE_AL SK B c ->
  (forall l acc', talk_attrs (tk_K0 c) = attr_scan f (tk_ck c ci) (a + nl_align l) (al - nl_align l) acc' ->
     4 <= l <= al -> TK_A598 SK B c ci a al l acc') ->
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al -> getr regs 10 = w64 (tk_b ci + a) ->
  tk_amem c mem (tk_b ci) acc ->
  talk_rc_model (tk_K0 c) = 0 -> talk_attrs (tk_K0 c) = attr_scan (S f) (tk_ck c ci) a al acc ->
  0 <= ci < tk_nch c -> 0 <= a -> a + al <= Z.of_nat (length (tk_ck c ci)) -> 4 <= al < Z.of_nat (S f) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_AF) mem md).
Proof.
  intros ci a al acc f regs mem md HRET HKIND HTAKE HAS HI H0 HRAT H10 HAM Hrc Hat Hci Ha Hlen Hal.
  destruct (tq_ck SK B c HC ci Hci) as (Lck & Lmax & Nch).
  pose proof H0 as (H8 & H9 & H23).
  pose proof HRAT as (H20 & H27 & H22 & H19 & H15 & H16 & H17).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof HAM as ((mb & Hmb & Hres) & HB & HSP).
  assert (CG : LA_G_NL = 0x5dcac0) by reflexivity. assert (CM : NL_CHUNK_MAX = 4096) by reflexivity.
  assert (CL : NK_CHUNK_LEN = 262144) by reflexivity. assert (CN : NL_CHUNKS = 64) by reflexivity.
  assert (CS : NK_N_CHUNKS = 262656) by reflexivity.
  assert (Hal' : 4 <= al < Z.of_nat f + 1) by (rewrite Nat2Z.inj_succ in Hal; lia). clear Hal.
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  assert (Rb : LA_G_NL <= tk_b ci /\ tk_b ci + 4096 <= LA_G_NL + NK_CHUNK_LEN) by (unfold tk_b; lia).
  (* the attribute's four bytes at b + a *)
  destruct (tq_byte SK B c HC regs mem md ci a HI Hci ltac:(lia)) as (b0 & N0 & M0).
  destruct (tq_byte SK B c HC regs mem md ci (a + 1) HI Hci ltac:(lia)) as (b1 & N1 & M1).
  destruct (tq_byte SK B c HC regs mem md ci (a + 2) HI Hci ltac:(lia)) as (b2 & N2 & M2).
  destruct (tq_byte SK B c HC regs mem md ci (a + 2 + 1) HI Hci ltac:(lia)) as (b3 & N3 & M3).
  pose proof (tw_byte_range b0) as Rb0. pose proof (tw_byte_range b1) as Rb1.
  pose proof (tw_byte_range b2) as Rb2. pose proof (tw_byte_range b3) as Rb3.
  remember (rd16 (tk_ck c ci) a) as l eqn:El.
  remember (rd16 (tk_ck c ci) (a + 2)) as ty eqn:Ety.
  assert (Hl : l = bz b0 + 256 * bz b1) by (rewrite El; exact (tw_rd16_bytes _ a b0 b1 Ha N0 N1)).
  assert (Hty : ty = bz b2 + 256 * bz b3) by (rewrite Ety; exact (tw_rd16_bytes _ (a + 2) b2 b3 ltac:(lia) N2 N3)).
  set (xs := [w64 (bz b0); w64 (bz b1); w64 (bz b2); w64 (bz b3)]).
  (* the atoms of the fresh state *)
  assert (E49 : ew (tk_E c regs xs) 49 = Z_to_bv 64 (bz b0)) by exact (tk_E_xs c regs xs 0 ltac:(lia)).
  assert (E50 : ew (tk_E c regs xs) 50 = Z_to_bv 64 (bz b1)) by exact (tk_E_xs c regs xs 1 ltac:(lia)).
  assert (E51 : ew (tk_E c regs xs) 51 = Z_to_bv 64 (bz b2)) by exact (tk_E_xs c regs xs 2 ltac:(lia)).
  assert (E52 : ew (tk_E c regs xs) 52 = Z_to_bv 64 (bz b3)) by exact (tk_E_xs c regs xs 3 ltac:(lia)).
  assert (E46 : ew (tk_E c regs xs) 46 = Z_to_bv 64 (tk_flag (tk_ad c) (tk_an c)))
    by exact (tk_E_ext c regs xs 14 ltac:(lia)).
  assert (E10 : ew (tk_E c regs xs) 10 = Z_to_bv 64 (tk_b ci + a))
    by (rewrite (tk_E_reg c regs xs 10 10%bv) by (lia || reflexivity); exact H10).
  assert (E22 : ew (tk_E c regs xs) 22 = Z_to_bv 64 al)
    by (rewrite (tk_E_reg c regs xs 22 22%bv) by (lia || reflexivity); exact H22).
  assert (E27 : ew (tk_E c regs xs) 27 = Z_to_bv 64 a)
    by (rewrite (tk_E_reg c regs xs 27 27%bv) by (lia || reflexivity); exact H27).
  assert (E23 : ew (tk_E c regs xs) 23 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (tk_E_reg c regs xs 23 23%bv) by (lia || reflexivity); exact H23).
  assert (U10 : U (tk_E c regs xs) (SOff 10 0) = tk_b ci + a) by (apply U_atom; [exact E10 | lia]).
  assert (U10b : bv_unsigned (ew (tk_E c regs xs) 10) = tk_b ci + a)
    by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew (tk_E c regs xs) 2) = tk_sp c - 144)
    by (pose proof (tk_base_sp SK B c HC regs mem md xs HI) as Hb; cbn [base_val] in Hb; exact Hb).
  assert (Ul : U (tk_E c regs xs) (SAlu ALU_OR (SAlu ALU_SLL (SOff 50 0) (SLit 8)) (SOff 49 0)) = l).
  { rewrite Hl. apply tq_U_join2; [apply (U_atom _ 50 _ E50); lia | apply (U_atom _ 49 _ E49); lia | lia | lia]. }
  assert (Uty : U (tk_E c regs xs) (SAlu ALU_OR (SAlu ALU_SLL (SOff 52 0) (SLit 8)) (SOff 51 0)) = ty).
  { rewrite Hty. apply tq_U_join2; [apply (U_atom _ 52 _ E52); lia | apply (U_atom _ 51 _ E51); lia | lia | lia]. }
  assert (U22 : U (tk_E c regs xs) (SOff 22 0) = al) by (apply U_atom; [exact E22 | lia]).
  assert (U46 : U (tk_E c regs xs) (SOff 46 0) = tk_flag (tk_ad c) (tk_an c))
    by (apply U_atom; [exact E46 | pose proof ta_flag_rng; lia]).
  (* THE FRESH STATE tk_ss_af *)
  assert (HS : st_ok_pi SEGS VAL (tk_E c regs xs) tk_ss_af
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_AF)) mem (seg_rom SEGS)))).
  { apply (tk_st_ok SK B LV c HC regs mem md xs); [exact HI | exact H23 | exact (tk_ov_at_ok c regs xs (tk_b ci) a al HRAT)
      | vm_compute; reflexivity | | | ].
    - apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs (tk_b ci) HI HSP H20 ltac:(lia) ltac:(lia)) |].
      apply Forall_cons; [|apply Forall_nil].
      unfold tk_R4, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10b. split; [lia|]. split; [lia|]. split; [intros o Ho'; lia|].
      repeat apply Forall_cons; try apply Forall_nil; unfold tk_ch.
      + apply (chunk_ok_val SEGS _ _ _ 0 1 (SOff 49 0) (bz b0) (tq_den0 _ 49 _ E49 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        rewrite Z.add_0_r. exact (tq_val1 _ _ _ M0).
      + apply (chunk_ok_val SEGS _ _ _ 1 1 (SOff 50 0) (bz b1) (tq_den0 _ 50 _ E50 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        rewrite <- Z.add_assoc. exact (tq_val1 _ _ _ M1).
      + apply (chunk_ok_val SEGS _ _ _ 2 1 (SOff 51 0) (bz b2) (tq_den0 _ 51 _ E51 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        rewrite <- Z.add_assoc. exact (tq_val1 _ _ _ M2).
      + apply (chunk_ok_val SEGS _ _ _ 3 1 (SOff 52 0) (bz b3) (tq_den0 _ 52 _ E52 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        replace (tk_b ci + a + 3) with (tk_b ci + (a + 2 + 1)) by lia. exact (tq_val1 _ _ _ M3).
    - apply pairwise_disjoint_of_extents. unfold tk_frs, tk_R4, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U10b.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - unfold tk_bfacts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10b, E49, E50, E51, E52, !unsigned_lit_small by lia.
      rewrite Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
  (* its shadow entry: the 8 bytes from b + a are addressable *)
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_af (tk_E c regs xs) (mrestrict (w_H W) mem)).
  { unfold tk_SH_af. apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok (tk_E c regs xs) (rdW W mem) 10 0 8 (tk_b ci + a)).
    - unfold tk_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
    - exact U10.
    - lia.
    - left. unfold kLowMemEnd. lia.
    - rewrite Z.add_0_r, Z.sub_0_r. apply (tq_ra SK B c HC regs mem md); [exact HI | lia | unfold tk_b in *; lia | lia]. }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  destruct acc as [ak aa].
  unfold tk_goal.
  (* +0x310 .. +0x348: the two checks, the length l; stop at `bltu l, 4` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |].
  pose proof (tq_ro _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hm. clear HF HFr HG.
  ta_ag (tk_E c regs xs) HAG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_ltu_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc by reflexivity; rewrite Ul, U_lit in Hc by lia.
  { (* l < 4: +0xb4 with a1 = 0 *)
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
    ta_end md Hm HJ msF md2 Hfd Hfs.
    destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs) as (HI2 & H02 & _).
    tq_rreg HS (11%bv : bv 5) R11.
    apply (HRET (ms_regs msF) mem md2 HI2 (proj2 (proj2 H02))). intros regs2 H10'.
    apply (tk_post_of SK B c HC mem 0 (Attrs ak aa) mb Hmb Hres (eq_sym Hrc));
      [ | exact HB | rewrite H10', R11; reflexivity].
    rewrite Hat. symmetry. apply as_stop; [lia | left; rewrite <- El; exact Hc]. }
  apply Z.ltb_ge in Hc.
  (* +0x34c: `bltu al, l` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_ltu_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc0 by reflexivity; rewrite U22, Ul in Hc0.
  { (* al < l: +0xb4 with a1 = 0 *)
    apply Z.ltb_lt in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
    ta_end md Hm HJ msF md2 Hfd Hfs.
    destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs) as (HI2 & H02 & _).
    tq_rreg HS (11%bv : bv 5) R11.
    apply (HRET (ms_regs msF) mem md2 HI2 (proj2 (proj2 H02))). intros regs2 H10'.
    apply (tk_post_of SK B c HC mem 0 (Attrs ak aa) mb Hmb Hres (eq_sym Hrc));
      [ | exact HB | rewrite H10', R11; reflexivity].
    rewrite Hat. symmetry. apply as_stop; [lia | right; rewrite <- El; exact Hc0]. }
  apply Z.ltb_ge in Hc0.
  (* +0x350 .. +0x38c: the two checks of the type; `beq type, 18` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc1 by reflexivity; rewrite Uty, U_lit in Hc1 by lia.
  { (* IFLA_LINKINFO: +0x3e8 `bltu l, 8` *)
    apply Z.eqb_eq in Hc1.
    assert (HLK : attr_scan (S f) (tk_ck c ci) a al (Attrs ak aa) =
                  attr_scan f (tk_ck c ci) (a + nl_align l) (al - nl_align l)
                    (Attrs (kind_scan f (tk_ck c ci) (a + 4) (l - 4) ak) aa))
      by (rewrite El; apply as_link; lia).
    paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
    psrr_branch_tok RUN BR HS SHOK tk_span;
      rewrite branch_ltu_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc2 by reflexivity; rewrite Ul, U_lit in Hc2 by lia.
    - (* l < 8: the inner walk finds nothing, +0x598 *)
      apply Z.ltb_lt in Hc2.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
      ta_end md Hm HJ msF md2 Hfd Hfs.
      destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
        HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
      tq_rreg HS (21%bv : bv 5) R21.
      apply (HAS l (Attrs ak aa) ltac:(rewrite Hat, HLK, (ks_short f (tk_ck c ci) (a + 4) (l - 4) ak) by lia; reflexivity)
        ltac:(lia) (ms_regs msF) mem md2 HI2 H02 HRAT2); [|exact HAM].
      rewrite R21. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity. exact Ul.
    - (* l >= 8: s8 = a + 4, s9 = l - 4, the inner loop +0x3f8 *)
      apply Z.ltb_ge in Hc2.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KH; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
      ta_end md Hm HJ msF md2 Hfd Hfs.
      destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
        HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
      tq_rreg HS (21%bv : bv 5) R21. tq_rreg HS (24%bv : bv 5) R24. tq_rreg HS (25%bv : bv 5) R25.
      apply (HKIND ci a al l aa (a + 4) (l - 4) ak f (HAS l _ ltac:(rewrite Hat; exact HLK) ltac:(lia))
        (ms_regs msF) mem md2 HI2 H02 HRAT2).
      + rewrite R21. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity. exact Ul.
      + rewrite R24, (YP06.sv_denot_agree 512 _ _ _ HAG) by reflexivity. exact (tq_den_off _ 27 a 4 E27 ltac:(lia)).
      + rewrite R25. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity.
        apply (tq_U_addk _ _ l (-4) Ul). lia.
      + exact HAM.
      + exact Hci.
      + lia.
      + lia.
      + lia. }
  apply Z.eqb_neq in Hc1.
  (* +0x390: `bne type, 20` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_ne_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc2 by reflexivity; rewrite Uty, U_lit in Hc2 by lia.
  - (* another type: +0x598 *)
    apply negb_true_iff, Z.eqb_neq in Hc2.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
    ta_end md Hm HJ msF md2 Hfd Hfs.
    destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
    tq_rreg HS (21%bv : bv 5) R21.
    apply (HAS l (Attrs ak aa) ltac:(rewrite Hat, El; apply as_other; lia) ltac:(lia) (ms_regs msF) mem md2 HI2 H02 HRAT2);
      [|exact HAM].
    rewrite R21. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity. exact Ul.
  - (* IFLA_IFALIAS: +0x398 the spilled alias flag, `bnez` *)
    apply negb_false_iff, Z.eqb_eq in Hc2.
    assert (HAL : attr_scan (S f) (tk_ck c ci) a al (Attrs ak aa) =
                  attr_scan f (tk_ck c ci) (a + nl_align l) (al - nl_align l)
                    (Attrs ak (Some (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))))
      by (rewrite El; apply as_alias; lia).
    paj_run_tok RUN HS HJ SHOK tk_span; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
    psrr_branch_tok RUN BR HS SHOK tk_span;
      rewrite branch_ne_U, !(tq_U_agree (tk_E c regs xs) _ _ HAG) in Hc3 by reflexivity; rewrite U46, U_lit in Hc3 by lia.
    + (* the flag set (no alias buffer): +0x598 *)
      apply negb_true_iff, Z.eqb_neq in Hc3.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
      ta_end md Hm HJ msF md2 Hfd Hfs.
      destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
        HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
      tq_rreg HS (21%bv : bv 5) R21.
      apply (HAS l (Attrs ak (Some (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) ltac:(rewrite Hat; exact HAL)
        ltac:(lia) (ms_regs msF) mem md2 HI2 H02 HRAT2).
      * rewrite R21. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity. exact Ul.
      * exact (conj (ex_intro _ mb (conj Hmb Hres)) (conj (ta_bufs_alias mem ak aa _ Hc3 HB) HSP)).
    + (* the flag clear: take_text into the alias buffer, +0x3a0 *)
      apply negb_false_iff, Z.eqb_eq in Hc3.
      destruct (ta_flag0 Hc3) as (Had & Han).
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_TA; [ta_awr |]. ta_mem Hm HF HFr HG. ta_ag (tk_E c regs xs) HAG.
      ta_end md Hm HJ msF md2 Hfd Hfs.
      destruct (ta_post regs mem md xs _ _ msF md2 (tk_b ci) a al HI H0 HRAT HS HAG ltac:(vm_compute; reflexivity)
        HJ Hfd Hfs) as (HI2 & H02 & HRAT2).
      tq_rreg HS (21%bv : bv 5) R21.
      apply (HTAKE ci a al l (Attrs ak aa) (HAS l _ ltac:(rewrite Hat; exact HAL) ltac:(lia))
        (ms_regs msF) mem md2 HI2 H02 HRAT2).
      * rewrite R21. apply tk_den_of_U. rewrite (tq_U_agree (tk_E c regs xs) _ _ HAG) by reflexivity. exact Ul.
      * exact HAM.
      * exact Had.
      * exact Han.
      * exact Hci.
      * exact Ha.
      * lia.
      * exact Hlen.
Qed.

(* THE PIECE: the attribute loop, by induction on the fuel of attr_scan *)
Lemma tk_attr_ok : TK_RET SK B c -> TK_KIND SK B c -> TK_TAKE_AL SK B c -> TK_ATTR SK B c.
Proof.
  intros HRET HKIND HTAKE ci a al acc fu. revert a al acc.
  induction fu as [|f IH]; intros a al acc regs mem md HI H0 HRAT HAM Hrc Hat Hci Ha Hlen Hal.
  { cbn [Z.of_nat] in Hal. lia. }
  apply (ta_at ci a al regs mem md HI H0 HRAT Hci Ha ltac:(lia) Hlen).
  intros regs2 md2 HI2 H02 HRAT2 H10.
  apply (ta_af ci a al acc f regs2 mem md2 HRET HKIND HTAKE); try assumption.
  intros l acc' Hs Hl.
  apply (ta_as ci a al l acc' f IH HRET Hrc Hs Hci Ha Hl Hlen). rewrite Nat2Z.inj_succ in Hal. lia.
Qed.

End w.
