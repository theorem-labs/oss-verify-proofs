(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 1428 of its 1523 lines of code are new or changed and 2594 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/talk_take.v; 576 of its 663 lines of code are new or changed and 1436 lines of the source are left out. *)
(* talk on image A: the message loop of one chunk, the piece TK_MSG of lib/A/Prog/talk_defs.v (listing
   (internal path) (internal record, sha256 5526460cb5be), +0x204 .. +0x308 and the NLMSG_ERROR
   arm +0x5ec .. +0x648). One turn at (off, left) of chunk c (b = g + 4096 c):
   - tm_ms, +0x204: `add a1, s4, t2`, a1 = b + off; the run stops at +0x208 (fresh state tk_ss_ms);
   - tm_mf, +0x208 (fresh state tk_ss_mf: the message's length ml at b + off, its type at + 4 and the four bytes of
     an NLMSG_ERROR code at + 16 are the atoms 49 .. 54, the SH entry tk_SH_mf covers every instrumented check):
       ml < 16 or left < ml: +0x1e0, the next chunk (TK_NXT (c + 1)), the chunk's walk answers nothing;
       type 16 (RTM_NEWLINK), ml < 36: +0xb4 with a1 = 0;
       type 16, ml >= 36: the five spilled words (alias_n - 1, the alias flag, b + 4, kind_n - 1, the kind flag) into
         [sp, sp + 40), s11 = off + 32, s6 = ml - 32, then +0x30c, the attribute loop (TK_ATTR);
       type 2 (NLMSG_ERROR): +0xb4 with a1 = -5 (ml < 36), the int32 code (code <= 0) or 1000000 (code > 0);
       another type: off += NL_ALIGN(ml), left -= NL_ALIGN(ml), then +0x204 (left >= 16) or +0x1e0.
   Every exit to +0xb4 builds the Post through talk_ret.v tk_post_of with the chunk loop's answer (talk_spec.v
   cls_hit, mres_main); the chunk walk itself is msg_scan from (off, left) (talk_spec.v ms_short .. ms_other).
   tk_msg_ok: induction on the fuel of msg_scan.
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

(* the registers of the message stage that stay the atoms of themselves *)
Definition tm_kb : list (bv 5 * sv) :=
  [(2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 8 0); (9%bv, SOff 9 0); (20%bv, SOff 20 0);
   (23%bv, SOff 23 0)].
Definition tm_kc : list (bv 5 * sv) := [(10%bv, SOff 10 0); (18%bv, SOff 18 0); (19%bv, SOff 19 0)] ++ tk_ov_ch.
Definition tm_kt : list (bv 5 * sv) := [(7%bv, SOff 7 0); (28%bv, SOff 28 0)].

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
Lemma tm_kb_ok : forall regs xs, Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) tm_kb.
Proof.
  intros regs xs. unfold tm_kb.
  repeat (apply Forall_cons; [cbn [fst snd]; apply tq_den_reg; [lia | reflexivity] |]). apply Forall_nil.
Qed.

Lemma tm_kt_ok : forall regs xs, Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) tm_kt.
Proof.
  intros regs xs. unfold tm_kt.
  repeat (apply Forall_cons; [cbn [fst snd]; apply tq_den_reg; [lia | reflexivity] |]). apply Forall_nil.
Qed.

Lemma tm_kc_ok : forall regs xs, tk_rch c regs -> getr regs 23 = w64 SHADOW_OFF ->
  Forall (fun p => sv_denot (tk_E c regs xs) (snd p) = getr regs (fst p)) tm_kc.
Proof.
  intros regs xs HR H23. unfold tm_kc. apply Forall_app. split; [|exact (tk_ov_ch_ok SK B LV c HC regs xs HR H23)].
  repeat (apply Forall_cons; [cbn [fst snd]; apply tq_den_reg; [lia | reflexivity] |]). apply Forall_nil.
Qed.

Lemma tm_kb_keep : forall regs regs2, Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) tm_kb ->
  getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
  (tk_rs0 c regs -> tk_rs0 c regs2) /\ getr regs2 20 = getr regs 20.
Proof.
  intros regs regs2 HF. unfold tm_kb in HF.
  apply Forall_cons_iff in HF as [K2 HF]. apply Forall_cons_iff in HF as [K3 HF].
  apply Forall_cons_iff in HF as [K4 HF]. apply Forall_cons_iff in HF as [K8 HF].
  apply Forall_cons_iff in HF as [K9 HF]. apply Forall_cons_iff in HF as [K20 HF].
  apply Forall_cons_iff in HF as [K23 _]. cbn [fst] in *.
  unfold tk_rs0. rewrite K8, K9, K23. intuition.
Qed.

Lemma tm_kc_keep : forall regs regs2, Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) tm_kc ->
  (tk_rsn c regs -> tk_rsn c regs2) /\ (tk_rch c regs -> tk_rch c regs2).
Proof.
  intros regs regs2 HF. unfold tm_kc, tk_ov_ch in HF. cbn [app] in HF.
  apply Forall_cons_iff in HF as [K10 HF]. apply Forall_cons_iff in HF as [K18 HF].
  apply Forall_cons_iff in HF as [K19 HF]. apply Forall_cons_iff in HF as [K13 HF].
  apply Forall_cons_iff in HF as [K14 HF]. apply Forall_cons_iff in HF as [K15 HF].
  apply Forall_cons_iff in HF as [K16 HF]. apply Forall_cons_iff in HF as [K17 HF].
  apply Forall_cons_iff in HF as [K6 _]. cbn [fst] in *.
  unfold tk_rsn, tk_rch. rewrite K10, K18, K19, K13, K14, K15, K16, K17, K6. intuition.
Qed.

Lemma tm_kt_keep : forall regs regs2, Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) tm_kt ->
  getr regs2 7 = getr regs 7 /\ getr regs2 28 = getr regs 28.
Proof.
  intros regs regs2 HF. unfold tm_kt in HF.
  apply Forall_cons_iff in HF as [K7 HF]. apply Forall_cons_iff in HF as [K28 _]. cbn [fst] in *. auto.
Qed.

(* ---- the state at the end of a run that wrote only the spill area [sp, sp + 40) ------------------------------------- *)
Lemma tm_post : forall regs mem md regs2 mem2 md2,
  tk_inv SK B c regs mem md ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem2 md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - 144 <= a < tk_sp c - 104) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  Forall (fun p => getr regs2 (fst p) = getr regs (fst p)) tm_kb ->
  tk_inv SK B c regs2 mem2 md2 /\ (tk_rs0 c regs -> tk_rs0 c regs2) /\ getr regs2 20 = getr regs 20 /\
  (forall j, tk_cmem c mem j -> tk_cmem c mem2 j) /\ (forall acc, tk_bufs c mem acc -> tk_bufs c mem2 acc) /\
  (forall mb, amodel_at SEGS (rdW W mem) (tk_m c) mb -> amodel_at SEGS (rdW W mem2) (tk_m c) mb).
Proof.
  intros regs mem md regs2 mem2 md2 HI HJ Hfd Hfs KP PR KR.
  destruct (tm_kb_keep regs regs2 KR) as (K2 & K3 & K4 & K0 & K20).
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - TALK_AK <= a < tk_sp c) ->
                 aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hf. apply KP; [exact Ha|]. intros Hz. apply Hf. unfold TALK_AK, TALK_AFRAME, ESTACK. lia. }
  destruct (tq_keep SK B c HC mem mem2 KF PR) as (KM & KB).
  split; [|split; [exact K0 | split; [exact K20 | split; [|split; [exact KB | exact KM]]]]].
  - apply (tk_inv_step SK B c HC regs mem md regs2 mem2 md2 (fun a => tk_sp c - 144 <= a < tk_sp c - 104) HI HJ Hfd Hfs KP);
      [ intros a Ha; left; unfold TALK_AK, TALK_AFRAME, ESTACK; lia | exact PR | exact K2 | exact K3 | exact K4 ].
  - intros j. exact (tq_keep_cmem SK B c HC mem mem2 j KF PR).
Qed.

(* ---- the exits ------------------------------------------------------------------------------------------------------- *)
(* +0x1e0: the chunk's walk answers nothing, the next chunk *)
Lemma tm_nxt : forall ci regs mem md,
  TK_NXT SK B c (ci + 1) -> tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  chunk_walk (tk_ck c ci) = NlNone -> tk_goal SK B c (cfg_of regs (BASE + TP_NX) mem md).
Proof.
  intros ci regs mem md HN HI H0 H1 H2 HCM HB HM HCL Hci Hw.
  apply (HN regs mem md HI H0 H1 H2 HCM HB HM); [exact (cls_miss mbs kbs ci HCL Hci Hw) | lia].
Qed.

(* +0xb4 with the code an NLMSG_ERROR or a short RTM_NEWLINK answers *)
Lemma tm_ret : forall ci regs mem md cd,
  TK_RET SK B c -> tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  msg_ret (chunk_walk (tk_ck c ci)) cd -> getr regs 11 = w64 cd ->
  tk_goal SK B c (cfg_of regs (BASE + TP_RT) mem md).
Proof.
  intros ci regs mem md cd HRET HI H23 HCM HB HM HCL Hci HR H11.
  change (tk_ck c ci) with (nk_chunk kbs ci) in HR.
  destruct HCM as (mb & Hm & Ho & Hn). destruct HM as (M1 & M2).
  pose proof (msg_ret_some _ _ HR) as Hv.
  pose proof (cls_hit mbs kbs ci HCL Hci Hv) as HL.
  destruct (mres_main mbs kbs (tc_req c) mb _ _ M1 M2 HL Ho ltac:(rewrite Hn; lia)) as (Hres & Hrc & Hat).
  assert (Hrc' : talk_rc_model (tk_K0 c) = cd /\ talk_attrs (tk_K0 c) = no_attrs).
  { unfold tk_K0. rewrite Hrc, Hat.
    destruct HR as [(E1 & E2) | [(code & E1 & E2) | (E1 & E2)]]; rewrite E1; cbn [tw_rc tw_at];
      (split; [rewrite E2; reflexivity | reflexivity]). }
  destruct Hrc' as (Hr1 & Ha1).
  apply (HRET regs mem md HI H23). intros regs2 H10.
  apply (tk_post_of SK B c HC mem cd no_attrs mb Hm Hres (eq_sym Hr1) (eq_sym Ha1) HB regs2).
  rewrite H10. exact H11.
Qed.

(* +0x30c: the first RTM_NEWLINK of ml >= 36, its attributes at off + 32 *)
Lemma tm_attr : forall ci off ml f regs mem md,
  TK_ATTR SK B c -> tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) (off + 32) (ml - 32) ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_spilled c mem (tk_b ci) -> tk_main c -> tk_clr c ci ->
  0 <= ci < tk_nch c ->
  chunk_walk (tk_ck c ci) = NlLink (attr_scan f (tk_ck c ci) (off + 32) (ml - 32) no_attrs) ->
  0 <= off -> off + ml <= Z.of_nat (length (tk_ck c ci)) -> 36 <= ml -> ml - 32 < Z.of_nat f ->
  tk_goal SK B c (cfg_of regs (BASE + TP_AT) mem md).
Proof.
  intros ci off ml f regs mem md HATTR HI H0 HRAT HCM HB HSP HM HCL Hci Hw Ho Hml H36 Hf.
  change (tk_ck c ci) with (nk_chunk kbs ci) in Hw.
  destruct HCM as (mb & Hm & Ho' & Hn). destruct HM as (M1 & M2).
  assert (Hv : chunk_walk (nk_chunk kbs ci) <> NlNone) by (rewrite Hw; discriminate).
  pose proof (cls_hit mbs kbs ci HCL Hci Hv) as HL.
  destruct (mres_main mbs kbs (tc_req c) mb _ _ M1 M2 HL Ho' ltac:(rewrite Hn; lia)) as (Hres & Hrc & Hat).
  rewrite Hw in Hrc, Hat. cbn [tw_rc tw_at] in Hrc, Hat.
  apply (HATTR ci (off + 32) (ml - 32) no_attrs f regs mem md HI H0 HRAT);
    [ | exact Hrc | exact Hat | exact Hci | lia | lia | lia].
  exact (conj (ex_intro _ mb (conj Hm Hres)) (conj HB HSP)).
Qed.

(* ---- +0x204: `add a1, s4, t2` ------------------------------------------------------------------------------------ *)
Lemma tm_ms : forall ci off regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs ->
  getr regs 20 = w64 (tk_b ci) -> getr regs 7 = w64 off -> 0 <= ci < tk_nch c -> 0 <= off <= NL_CHUNK_MAX ->
  (forall regs2 md2, tk_inv SK B c regs2 mem md2 -> tk_rs0 c regs2 -> tk_rsn c regs2 -> tk_rch c regs2 ->
     getr regs2 20 = getr regs 20 -> getr regs2 7 = getr regs 7 -> getr regs2 28 = getr regs 28 ->
     getr regs2 11 = w64 (tk_b ci + off) -> tk_goal SK B c (cfg_of regs2 (BASE + TP_MF) mem md2)) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_MS) mem md).
Proof.
  intros ci off regs mem md HI H0 HN HR H20 H7 Hci Ho K.
  destruct (tq_ck SK B c HC ci Hci) as (_ & _ & Nch).
  pose proof H0 as (_ & _ & H23).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof (tk_ov_ch_ok SK B LV c HC regs [] HR H23) as HOV.
  pose proof (tk_st_ok SK B LV c HC regs mem md [] TP_MS tk_ov_ch [] [] HI H23 HOV eq_refl (Forall_nil _) I I) as HS.
  pose proof (tk_E_env c regs []) as HEI.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs []) (mrestrict (w_H W) mem)) by constructor.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  assert (U7 : U (tk_E c regs []) (SOff 7 0) = off)
    by (apply (tk_U_reg c regs [] 7 7%bv); [lia | reflexivity | exact H7 | unfold NL_CHUNK_MAX in *; lia]).
  assert (U20 : U (tk_E c regs []) (SOff 20 0) = tk_b ci)
    by (apply (tk_U_reg c regs [] 20 20%bv); [lia | reflexivity | exact H20 | unfold tk_b, LA_G_NL, NL_CHUNK_MAX, NL_CHUNKS in *; lia]).
  unfold tk_goal in *.
  (* +0x204: a1 := s4 + t2; the run stops at +0x208 *)
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_MF.
  - intros a (r & Hin & _). destruct Hin.
  - lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
    assert (Hm : ms_mem ms1 = mem) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
    rewrite Hm in HJ. pmkst HS. rewrite Hm.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    pose proof (tq_keep_regs (w_H W) (tk_E c regs []) (tk_E c regs []) _ ms1 regs (tm_kb ++ tm_kc ++ tm_kt) HS
      ltac:(tq_agree)
      (proj2 (Forall_app _ _ _) (conj (tm_kb_ok regs []) (proj2 (Forall_app _ _ _) (conj (tm_kc_ok regs [] HR H23)
         (tm_kt_ok regs [])))))
      ltac:(vm_compute; reflexivity)) as KR.
    apply Forall_app in KR as [KRb KR]. apply Forall_app in KR as [KRc KRt].
    destruct (tm_kb_keep regs (ms_regs ms1) KRb) as (K2 & K3 & K4 & K0 & K20).
    destruct (tm_kc_keep regs (ms_regs ms1) KRc) as (KN & KC).
    destruct (tm_kt_keep regs (ms_regs ms1) KRt) as (K7 & K28).
    tq_rreg HS (11%bv : bv 5) R11.
    assert (A11 : getr (ms_regs ms1) 11 = w64 (tk_b ci + off)).
    { rewrite R11. apply tk_den_of_U. rewrite Z.add_comm.
      apply (tq_U_add _ _ _ off (tk_b ci) U7 U20). unfold tk_b, LA_G_NL, NL_CHUNK_MAX, NL_CHUNKS in *. lia. }
    assert (HI2 : tk_inv SK B c (ms_regs ms1) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros a _ _. reflexivity.
      - intros a [].
      - intros a Hp. exact Hp.
      - exact K2.
      - exact K3.
      - exact K4. }
    apply K; [exact HI2 | exact (K0 H0) | exact (KN HN) | exact (KC HR) | exact K20 | exact K7 | exact K28 | exact A11].
Qed.

(* ---- the exits at the machine state a run of tk_ss_mf ends in (no fresh atom, the environment is the fresh
   state's; the run wrote only the spill area) ------------------------------------------------------------------------ *)
Lemma tm_x1 : forall ci regs mem md xs ss ms md2,
  TK_NXT SK B c (ci + 1) -> tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  st_ok_pi SEGS VAL (tk_E c regs xs) ss (restrict (w_H W) ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) (tm_kb ++ tm_kc) = true ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W (ms_mem ms) md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - 144 <= a < tk_sp c - 104) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
  chunk_walk (tk_ck c ci) = NlNone ->
  tk_goal SK B c (cfg_of (ms_regs ms) (BASE + TP_NX) (ms_mem ms) md2).
Proof.
  intros ci regs mem md xs ss ms md2 HNXT HI H0 HN HR HCM HB HM HCL Hci HS Hck HJ Hfd Hfs KP PR Hw.
  pose proof H0 as (_ & _ & H23).
  pose proof (tq_keep_regs (w_H W) (tk_E c regs xs) (tk_E c regs xs) ss ms regs (tm_kb ++ tm_kc) HS ltac:(tq_agree)
    (proj2 (Forall_app _ _ _) (conj (tm_kb_ok regs xs) (tm_kc_ok regs xs HR H23))) Hck) as KR.
  apply Forall_app in KR as [KRb KRc].
  destruct (tm_post regs mem md (ms_regs ms) (ms_mem ms) md2 HI HJ Hfd Hfs KP PR KRb) as (HI2 & K0 & _ & KCM & KB & _).
  destruct (tm_kc_keep regs (ms_regs ms) KRc) as (KN & KC).
  exact (tm_nxt ci (ms_regs ms) (ms_mem ms) md2 HNXT HI2 (K0 H0) (KN HN) (KC HR) (KCM _ HCM) (KB _ HB) HM HCL Hci Hw).
Qed.

Lemma tm_x2 : forall ci regs mem md xs ss ms md2 cd,
  TK_RET SK B c -> tk_inv SK B c regs mem md -> tk_rs0 c regs ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  st_ok_pi SEGS VAL (tk_E c regs xs) ss (restrict (w_H W) ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) tm_kb = true ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W (ms_mem ms) md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - 144 <= a < tk_sp c - 104) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
  msg_ret (chunk_walk (tk_ck c ci)) cd -> getr (ms_regs ms) 11 = w64 cd ->
  tk_goal SK B c (cfg_of (ms_regs ms) (BASE + TP_RT) (ms_mem ms) md2).
Proof.
  intros ci regs mem md xs ss ms md2 cd HRET HI H0 HCM HB HM HCL Hci HS Hck HJ Hfd Hfs KP PR HR H11.
  pose proof (tq_keep_regs (w_H W) (tk_E c regs xs) (tk_E c regs xs) ss ms regs tm_kb HS ltac:(tq_agree)
    (tm_kb_ok regs xs) Hck) as KRb.
  destruct (tm_post regs mem md (ms_regs ms) (ms_mem ms) md2 HI HJ Hfd Hfs KP PR KRb) as (HI2 & K0 & _ & KCM & KB & _).
  exact (tm_ret ci (ms_regs ms) (ms_mem ms) md2 cd HRET HI2 (proj2 (proj2 (K0 H0))) (KCM _ HCM) (KB _ HB) HM HCL Hci
    HR H11).
Qed.

Lemma tm_x3 : forall ci off ml f regs mem md xs ss ms md2,
  TK_ATTR SK B c -> tk_inv SK B c regs mem md -> tk_rs0 c regs -> getr regs 20 = w64 (tk_b ci) ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  st_ok_pi SEGS VAL (tk_E c regs xs) ss (restrict (w_H W) ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) tm_kb = true ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W (ms_mem ms) md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - 144 <= a < tk_sp c - 104) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
  getr (ms_regs ms) 27 = w64 (off + 32) -> getr (ms_regs ms) 22 = w64 (ml - 32) ->
  getr (ms_regs ms) 19 = w64 0x1fffc -> getr (ms_regs ms) 15 = w64 4 -> getr (ms_regs ms) 16 = w64 1 ->
  getr (ms_regs ms) 17 = w64 3 -> tk_spilled c (ms_mem ms) (tk_b ci) ->
  chunk_walk (tk_ck c ci) = NlLink (attr_scan f (tk_ck c ci) (off + 32) (ml - 32) no_attrs) ->
  0 <= off -> off + ml <= Z.of_nat (length (tk_ck c ci)) -> 36 <= ml -> ml - 32 < Z.of_nat f ->
  tk_goal SK B c (cfg_of (ms_regs ms) (BASE + TP_AT) (ms_mem ms) md2).
Proof.
  intros ci off ml f regs mem md xs ss ms md2 HATTR HI H0 H20 HCM HB HM HCL Hci HS Hck HJ Hfd Hfs KP PR
    R27 R22 R19 R15 R16 R17 HSP Hw Ho Hml H36 Hf.
  pose proof (tq_keep_regs (w_H W) (tk_E c regs xs) (tk_E c regs xs) ss ms regs tm_kb HS ltac:(tq_agree)
    (tm_kb_ok regs xs) Hck) as KRb.
  destruct (tm_post regs mem md (ms_regs ms) (ms_mem ms) md2 HI HJ Hfd Hfs KP PR KRb)
    as (HI2 & K0 & K20 & KCM & KB & _).
  apply (tm_attr ci off ml f (ms_regs ms) (ms_mem ms) md2 HATTR HI2 (K0 H0)); try assumption.
  - unfold tk_rat. rewrite K20. exact (conj H20 (conj R27 (conj R22 (conj R19 (conj R15 (conj R16 R17)))))).
  - exact (KCM _ HCM).
  - exact (KB _ HB).
Qed.

Lemma tm_xm : forall ci off' left' f regs mem md xs ss ms md2,
  (forall off' left' regs' mem' md', tk_inv SK B c regs' mem' md' -> tk_rs0 c regs' -> tk_rsn c regs' ->
     tk_rch c regs' -> getr regs' 20 = w64 (tk_b ci) -> getr regs' 7 = w64 off' -> getr regs' 28 = w64 left' ->
     tk_cmem c mem' (ci + 1) -> tk_bufs c mem' no_attrs ->
     chunk_walk (tk_ck c ci) = msg_scan f (tk_ck c ci) off' left' ->
     0 <= off' -> off' + left' = Z.of_nat (length (tk_ck c ci)) -> 16 <= left' < Z.of_nat f ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_MS) mem' md')) ->
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs -> getr regs 20 = w64 (tk_b ci) ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs ->
  st_ok_pi SEGS VAL (tk_E c regs xs) ss (restrict (w_H W) ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p) && sv_atoms_lt 512 (snd p)) (tm_kb ++ tm_kc) = true ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W (ms_mem ms) md2 (tc_k c) ->
  m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp c - 144 <= a < tk_sp c - 104) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
  getr (ms_regs ms) 7 = w64 off' -> getr (ms_regs ms) 28 = w64 left' ->
  chunk_walk (tk_ck c ci) = msg_scan f (tk_ck c ci) off' left' ->
  0 <= off' -> off' + left' = Z.of_nat (length (tk_ck c ci)) -> 16 <= left' < Z.of_nat f ->
  tk_goal SK B c (cfg_of (ms_regs ms) (BASE + TP_MS) (ms_mem ms) md2).
Proof.
  intros ci off' left' f regs mem md xs ss ms md2 IH HI H0 HN HR H20 HCM HB HS Hck HJ Hfd Hfs KP PR R7 R28 Hw Ho HL Hl.
  pose proof H0 as (_ & _ & H23).
  pose proof (tq_keep_regs (w_H W) (tk_E c regs xs) (tk_E c regs xs) ss ms regs (tm_kb ++ tm_kc) HS ltac:(tq_agree)
    (proj2 (Forall_app _ _ _) (conj (tm_kb_ok regs xs) (tm_kc_ok regs xs HR H23))) Hck) as KR.
  apply Forall_app in KR as [KRb KRc].
  destruct (tm_post regs mem md (ms_regs ms) (ms_mem ms) md2 HI HJ Hfd Hfs KP PR KRb)
    as (HI2 & K0 & K20 & KCM & KB & _).
  destruct (tm_kc_keep regs (ms_regs ms) KRc) as (KN & KC).
  apply (IH off' left' (ms_regs ms) (ms_mem ms) md2 HI2 (K0 H0) (KN HN) (KC HR) ltac:(rewrite K20; exact H20) R7 R28
    (KCM _ HCM) (KB _ HB) Hw Ho HL Hl).
Qed.

(* ---- the tactics of the run of tk_ss_mf ------------------------------------------------------------------------------ *)
(* the write permission of a run whose only write window is the spill area [sp, sp + 40): stack bytes of the frame *)
Ltac tm_awr U2 Hlo Hhi :=
  let x := fresh "x" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (rr & Hin & Hx); vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
      first [ exfalso; clear - Hx; lia
            | rewrite U2 in Hx; left; split; [unfold awr_byte; left |];
              clear - Hx Hlo Hhi; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia ] | ]);
  destruct Hin.
(* each write window of such a run lies in [sp, sp + 40) *)
Ltac tm_win U2 :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros bb wlo whi x Hin Hx; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
    [ injection Hq as <- <- <-; cbn [base_val] in Hx; cbv beta;
      first [ exfalso; clear - Hx; lia | rewrite U2 in Hx; clear - Hx; lia ] | ]);
  destruct Hin.
(* fold a run's frame into the bytes kept since the fresh state (KP) and the presence kept (PR) *)
Ltac tm_acc U2 KP PR HF HFr HG :=
  let UN := fresh "UN" in
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => tk_sp c - 144 <= a < tk_sp c - 104) HFr
    ltac:(tm_win U2)) as UN;
  let KP' := fresh "KP" in let PR' := fresh "PR" in
  pose proof (fun a Ha Hz => eq_trans (UN a Ha Hz) (KP a Ha Hz)) as KP';
  pose proof (fun a Hp => apresent_grows (w_H W) _ _ a HG (PR a Hp)) as PR';
  clear KP PR UN HF HFr HG; rename KP' into KP; rename PR' into PR.
(* name the machine state and the model a run ends in *)
Ltac tm_end md msF md2 Hfd Hfs :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end;
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ msF) |- _ => pmkst HS end;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end;
  assert (Hfd : m_fds md2 = m_fds md) by (unfold md2; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity);
  assert (Hfs : m_fs md2 = m_fs md) by (unfold md2; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).

(* ---- +0x208: one message ------------------------------------------------------------------------------------------- *)
Lemma tm_mf : forall ci off left f regs mem md,
  TK_RET SK B c -> TK_ATTR SK B c -> TK_NXT SK B c (ci + 1) ->
  (forall off' left' regs' mem' md', tk_inv SK B c regs' mem' md' -> tk_rs0 c regs' -> tk_rsn c regs' ->
     tk_rch c regs' -> getr regs' 20 = w64 (tk_b ci) -> getr regs' 7 = w64 off' -> getr regs' 28 = w64 left' ->
     tk_cmem c mem' (ci + 1) -> tk_bufs c mem' no_attrs ->
     chunk_walk (tk_ck c ci) = msg_scan f (tk_ck c ci) off' left' ->
     0 <= off' -> off' + left' = Z.of_nat (length (tk_ck c ci)) -> 16 <= left' < Z.of_nat f ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_MS) mem' md')) ->
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs ->
  getr regs 20 = w64 (tk_b ci) -> getr regs 7 = w64 off -> getr regs 28 = w64 left ->
  getr regs 11 = w64 (tk_b ci + off) ->
  tk_cmem c mem (ci + 1) -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  chunk_walk (tk_ck c ci) = msg_scan (S f) (tk_ck c ci) off left ->
  0 <= off -> off + left = Z.of_nat (length (tk_ck c ci)) -> 16 <= left < Z.of_nat (S f) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_MF) mem md).
Proof.
  intros ci off left f regs mem md HRET HATTR HNXT IH HI H0 HN HR H20 H7 H28 H11 HCM HB HM HCL Hci HW Ho HL Hlf.
  destruct (tq_ck SK B c HC ci Hci) as (Lck & Lmax & Nch).
  pose proof H0 as (H8 & H9 & H23).
  pose proof HN as (H18 & H19).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  destruct (tk_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  assert (Hfl : 16 <= left < Z.of_nat f + 1) by (rewrite Nat2Z.inj_succ in Hlf; lia). clear Hlf.
  assert (CG : LA_G_NL = 0x5dcac0) by reflexivity. assert (CM : NL_CHUNK_MAX = 4096) by reflexivity.
  assert (CL : NK_CHUNK_LEN = 262144) by reflexivity. assert (CN : NL_CHUNKS = 64) by reflexivity.
  assert (Rb : LA_G_NL <= tk_b ci /\ tk_b ci + 4096 <= LA_G_NL + NK_CHUNK_LEN)
    by (unfold tk_b, NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN in *; lia).
  assert (Rad : 0 <= tk_ad c < 2 ^ 64) by exact (tk_aarg_rng c 5).
  assert (Ran : 0 <= tk_an c < 2 ^ 64) by exact (tk_aarg_rng c 6).
  assert (Rkd : 0 <= tk_kd c < 2 ^ 64) by exact (tk_aarg_rng c 3).
  assert (Rkn : 0 <= tk_kn c < 2 ^ 64) by exact (tk_aarg_rng c 4).
  remember (rd32 (tk_ck c ci) off) as ml eqn:Eml.
  remember (rd16 (tk_ck c ci) (off + 4)) as ty eqn:Ety.
  assert (Rml : 0 <= ml < 2 ^ 32) by (subst ml; apply tw_rd32_range; lia).
  assert (Rty : 0 <= ty < 2 ^ 16) by (subst ty; apply tw_rd16_range; lia).
  (* the four bytes at off + 16 (an NLMSG_ERROR code when ml >= 20) *)
  destruct (tq_gbyte SK B c HC regs mem md (4096 * ci + (off + 16)) HI
    ltac:(unfold NK_SIZE, NL_CHUNK_MAX, NL_CHUNKS in *; lia)) as (e0 & Ge0 & Me0).
  destruct (tq_gbyte SK B c HC regs mem md (4096 * ci + (off + 16 + 1)) HI
    ltac:(unfold NK_SIZE, NL_CHUNK_MAX, NL_CHUNKS in *; lia)) as (e1 & Ge1 & Me1).
  destruct (tq_gbyte SK B c HC regs mem md (4096 * ci + (off + 16 + 2)) HI
    ltac:(unfold NK_SIZE, NL_CHUNK_MAX, NL_CHUNKS in *; lia)) as (e2 & Ge2 & Me2).
  destruct (tq_gbyte SK B c HC regs mem md (4096 * ci + (off + 16 + 3)) HI
    ltac:(unfold NK_SIZE, NL_CHUNK_MAX, NL_CHUNKS in *; lia)) as (e3 & Ge3 & Me3).
  pose proof (tw_byte_range e0) as Re0. pose proof (tw_byte_range e1) as Re1.
  pose proof (tw_byte_range e2) as Re2. pose proof (tw_byte_range e3) as Re3.
  set (xs := [w64 ml; w64 ty; w64 (bz e0); w64 (bz e1); w64 (bz e2); w64 (bz e3)]).
  (* the atoms of the fresh state *)
  assert (E49 : ew (tk_E c regs xs) 49 = Z_to_bv 64 ml) by exact (tk_E_xs c regs xs 0 ltac:(lia)).
  assert (E50 : ew (tk_E c regs xs) 50 = Z_to_bv 64 ty) by exact (tk_E_xs c regs xs 1 ltac:(lia)).
  assert (E51 : ew (tk_E c regs xs) 51 = Z_to_bv 64 (bz e0)) by exact (tk_E_xs c regs xs 2 ltac:(lia)).
  assert (E52 : ew (tk_E c regs xs) 52 = Z_to_bv 64 (bz e1)) by exact (tk_E_xs c regs xs 3 ltac:(lia)).
  assert (E53 : ew (tk_E c regs xs) 53 = Z_to_bv 64 (bz e2)) by exact (tk_E_xs c regs xs 4 ltac:(lia)).
  assert (E54 : ew (tk_E c regs xs) 54 = Z_to_bv 64 (bz e3)) by exact (tk_E_xs c regs xs 5 ltac:(lia)).
  assert (E7 : ew (tk_E c regs xs) 7 = Z_to_bv 64 off)
    by (rewrite (tk_E_reg c regs xs 7 7%bv) by (lia || reflexivity); exact H7).
  assert (E28 : ew (tk_E c regs xs) 28 = Z_to_bv 64 left)
    by (rewrite (tk_E_reg c regs xs 28 28%bv) by (lia || reflexivity); exact H28).
  assert (E20 : ew (tk_E c regs xs) 20 = Z_to_bv 64 (tk_b ci))
    by (rewrite (tk_E_reg c regs xs 20 20%bv) by (lia || reflexivity); exact H20).
  assert (E11 : ew (tk_E c regs xs) 11 = Z_to_bv 64 (tk_b ci + off))
    by (rewrite (tk_E_reg c regs xs 11 11%bv) by (lia || reflexivity); exact H11).
  assert (E23 : ew (tk_E c regs xs) 23 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (tk_E_reg c regs xs 23 23%bv) by (lia || reflexivity); exact H23).
  assert (E8 : ew (tk_E c regs xs) 8 = Z_to_bv 64 (tk_ad c))
    by (rewrite (tk_E_reg c regs xs 8 8%bv) by (lia || reflexivity); exact H8).
  assert (E9 : ew (tk_E c regs xs) 9 = Z_to_bv 64 (tk_kd c))
    by (rewrite (tk_E_reg c regs xs 9 9%bv) by (lia || reflexivity); exact H9).
  assert (E18 : ew (tk_E c regs xs) 18 = Z_to_bv 64 (tk_an c))
    by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  assert (E19 : ew (tk_E c regs xs) 19 = Z_to_bv 64 (tk_kn c))
    by (rewrite (tk_E_reg c regs xs 19 19%bv) by (lia || reflexivity); exact H19).
  assert (U49 : U (tk_E c regs xs) (SOff 49 0) = ml) by (apply U_atom; [exact E49 | lia]).
  assert (U50 : U (tk_E c regs xs) (SOff 50 0) = ty) by (apply U_atom; [exact E50 | lia]).
  assert (U28 : U (tk_E c regs xs) (SOff 28 0) = left)
    by (apply U_atom; [exact E28 | unfold NL_CHUNK_MAX in *; lia]).
  assert (U7 : U (tk_E c regs xs) (SOff 7 0) = off)
    by (apply U_atom; [exact E7 | unfold NL_CHUNK_MAX in *; lia]).
  assert (U11 : U (tk_E c regs xs) (SOff 11 0) = tk_b ci + off)
    by (apply U_atom; [exact E11 | unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX in *; lia]).
  assert (U11b : bv_unsigned (ew (tk_E c regs xs) 11) = tk_b ci + off)
    by (rewrite E11; apply unsigned_lit_small; unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX in *; lia).
  assert (U2 : bv_unsigned (ew (tk_E c regs xs) 2) = tk_sp c - 144)
    by (pose proof (tk_base_sp SK B c HC regs mem md xs HI) as Hb; cbn [base_val] in Hb; exact Hb).
  (* THE FRESH STATE tk_ss_mf *)
  assert (HS : st_ok_pi SEGS VAL (tk_E c regs xs) tk_ss_mf
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_MF)) mem (seg_rom SEGS)))).
  { apply (tk_st_ok SK B LV c HC regs mem md xs); [exact HI | exact H23 | exact (tk_ov_ch_ok SK B LV c HC regs xs HR H23)
      | vm_compute; reflexivity | | | ].
    - apply Forall_cons; [exact (tk_frw_ok SK B c HC regs mem md xs HI) |]. apply Forall_cons; [|apply Forall_nil].
      unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U11b. split; [lia|]. split; [unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX in *; lia|].
      split; [intros o Ho'; lia|].
      repeat apply Forall_cons; try apply Forall_nil; unfold tk_ch.
      + apply (chunk_ok_val SEGS _ _ _ 0 4 (SOff 49 0) ml (tq_den0 _ 49 ml E49 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia |].
        rewrite Eml, Z.add_0_r. exact (tq_val_ck SK B c HC regs mem md ci off 4 HI Hci Ho ltac:(lia)).
      + apply (chunk_ok_val SEGS _ _ _ 4 2 (SOff 50 0) ty (tq_den0 _ 50 ty E50 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16); lia | lia |].
        rewrite Ety, <- Z.add_assoc. exact (tq_val_ck SK B c HC regs mem md ci (off + 4) 2 HI Hci ltac:(lia) ltac:(lia)).
      + apply (chunk_ok_val SEGS _ _ _ 16 1 (SOff 51 0) (bz e0) (tq_den0 _ 51 (bz e0) E51 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        replace (tk_b ci + off + 16) with (LA_G_NL + (4096 * ci + (off + 16))) by (unfold tk_b, NL_CHUNK_MAX; lia).
        exact (tq_val1 _ _ _ Me0).
      + apply (chunk_ok_val SEGS _ _ _ 17 1 (SOff 52 0) (bz e1) (tq_den0 _ 52 (bz e1) E52 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        replace (tk_b ci + off + 17) with (LA_G_NL + (4096 * ci + (off + 16 + 1))) by (unfold tk_b, NL_CHUNK_MAX; lia).
        exact (tq_val1 _ _ _ Me1).
      + apply (chunk_ok_val SEGS _ _ _ 18 1 (SOff 53 0) (bz e2) (tq_den0 _ 53 (bz e2) E53 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        replace (tk_b ci + off + 18) with (LA_G_NL + (4096 * ci + (off + 16 + 2))) by (unfold tk_b, NL_CHUNK_MAX; lia).
        exact (tq_val1 _ _ _ Me2).
      + apply (chunk_ok_val SEGS _ _ _ 19 1 (SOff 54 0) (bz e3) (tq_den0 _ 54 (bz e3) E54 ltac:(lia)));
          [change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        replace (tk_b ci + off + 19) with (LA_G_NL + (4096 * ci + (off + 16 + 3))) by (unfold tk_b, NL_CHUNK_MAX; lia).
        exact (tq_val1 _ _ _ Me3).
    - apply pairwise_disjoint_of_extents. unfold tk_frw, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U11b.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX in *. repeat split; lia.
    - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U11b, E49, E50, E51, E52, E53, E54, !unsigned_lit_small by lia.
      rewrite Z.pow_0_r, !Z.mod_1_r. unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX in *. repeat split; lia. }
  (* its shadow entry: the 32 bytes from b + off are addressable *)
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_mf (tk_E c regs xs) (mrestrict (w_H W) mem)).
  { unfold tk_SH_mf. apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok (tk_E c regs xs) (rdW W mem) 11 0 32 (tk_b ci + off)).
    - unfold tk_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
    - exact U11.
    - lia.
    - left. unfold LA_G_NL, NK_CHUNK_LEN, NL_CHUNK_MAX, kLowMemEnd in *. lia.
    - rewrite Z.add_0_r, Z.sub_0_r. apply (tq_ra SK B c HC regs mem md); [exact HI | lia | | lia].
      unfold LA_G_NL, NK_CHUNK_LEN, NK_N_CHUNKS, NL_CHUNK_MAX in *. lia. }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  pose proof (fun a (_ : 0 <= a < 2 ^ 64) (_ : ~ (tk_sp c - 144 <= a < tk_sp c - 104)) =>
    eq_refl (aview SEGS (w_H W) mem a)) as KP.
  pose proof (fun a (Hp : apresent (w_H W) mem a) => Hp) as PR.
  (* the spec's step at this message *)
  assert (HV : chunk_walk (tk_ck c ci) = msg_scan (S f) (tk_ck c ci) off left) by exact HW. clear HW.
  unfold tk_goal.
  (* +0x208 .. +0x21c: the check of b + off, lwu ml; stop at `bltu ml, 16` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_ltu_U, U49, U_lit in Hc by lia.
  { (* ml < 16: +0x1e0 *)
    apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_NX; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    tm_end md msF md2 Hfd Hfs.
    apply (tm_x1 ci regs mem md xs _ msF md2 HNXT HI H0 HN HR HCM HB HM HCL Hci HS ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs KP PR).
    rewrite HV. apply ms_bad; [lia | left; rewrite <- Eml; exact Hc]. }
  apply Z.ltb_ge in Hc.
  (* +0x220: `bltu left, ml` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_ltu_U, U28, U49 in Hc0.
  { (* left < ml: +0x1e0 *)
    apply Z.ltb_lt in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_NX; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    tm_end md msF md2 Hfd Hfs.
    apply (tm_x1 ci regs mem md xs _ msF md2 HNXT HI H0 HN HR HCM HB HM HCL Hci HS ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs KP PR).
    rewrite HV. apply ms_bad; [lia | right; rewrite <- Eml; exact Hc0]. }
  apply Z.ltb_ge in Hc0.
  (* +0x224 .. +0x23c: the check of b + off + 4, lhu type; `beq type, 16` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_eq_U, U50, U_lit in Hc1 by lia.
  { (* RTM_NEWLINK: +0x298 `bgeu ml, 36` *)
    apply Z.eqb_eq in Hc1.
    assert (HL16 : msg_scan (S f) (tk_ck c ci) off left = NlLink (attr_scan f (tk_ck c ci) (off + 32) (ml - 32) no_attrs))
      by (rewrite Eml; apply ms_link; lia).
    paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_geu_U, U49, U_lit in Hc2 by lia.
    - (* ml >= 36: the five spilled words, +0x30c *)
      apply negb_true_iff, Z.ltb_ge in Hc2.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AT; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
      tm_end md msF md2 Hfd Hfs.
      lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
        let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
        lazymatch r with Some ?R => pose proof (tq_region _ ss _ 0 R HS ltac:(vm_compute; reflexivity)) as HR0 end end.
      cbn [ms_mem restrict] in HR0.
      assert (HSP : tk_spilled c (ms_mem msF) (tk_b ci)).
      { unfold tk_spilled, tk_spill_vals. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          (eapply tq_spill_word; [exact HR0 | exact U2 | repeat (first [left; reflexivity | right]) | ]).
        - exact (tq_den_off _ 18 (tk_an c) (-1) E18 Ran).
        - apply tk_den_of_U, tq_U_flag; [apply (U_atom _ 8 _ E8 Rad) | apply (U_atom _ 18 _ E18 Ran)].
        - exact (tq_den_off _ 20 (tk_b ci) 4 E20 ltac:(unfold LA_G_NL, NK_CHUNK_LEN in *; lia)).
        - exact (tq_den_off _ 19 (tk_kn c) (-1) E19 Rkn).
        - apply tk_den_of_U, tq_U_flag; [apply (U_atom _ 9 _ E9 Rkd) | apply (U_atom _ 19 _ E19 Rkn)]. }
      tq_rreg HS (27%bv : bv 5) R27. tq_rreg HS (22%bv : bv 5) R22. tq_rreg HS (19%bv : bv 5) R19.
      tq_rreg HS (15%bv : bv 5) R15. tq_rreg HS (16%bv : bv 5) R16. tq_rreg HS (17%bv : bv 5) R17.
      apply (tm_x3 ci off ml f regs mem md xs _ msF md2 HATTR HI H0 H20 HCM HB HM HCL Hci HS
        ltac:(vm_compute; reflexivity) HJ Hfd Hfs KP PR).
      + rewrite R27. exact (tq_den_off _ 7 off 32 E7 ltac:(unfold NL_CHUNK_MAX in *; lia)).
      + rewrite R22. exact (tq_den_off _ 49 ml (-32) E49 ltac:(lia)).
      + rewrite R19; reflexivity.
      + rewrite R15; reflexivity.
      + rewrite R16; reflexivity.
      + rewrite R17; reflexivity.
      + exact HSP.
      + rewrite HV. exact HL16.
      + exact Ho.
      + lia.
      + exact Hc2.
      + lia.
    - (* ml < 36: +0x2a0, a1 = 0, +0xb4 *)
      apply negb_false_iff, Z.ltb_lt in Hc2.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
      tm_end md msF md2 Hfd Hfs.
      tq_rreg HS (11%bv : bv 5) R11.
      apply (tm_x2 ci regs mem md xs _ msF md2 0 HRET HI H0 HCM HB HM HCL Hci HS ltac:(vm_compute; reflexivity)
        HJ Hfd Hfs KP PR); [|rewrite R11; reflexivity].
      unfold msg_ret. right; right. split; [|reflexivity]. rewrite HV, HL16. f_equal. apply as_short. lia. }
  apply Z.eqb_neq in Hc1.
  (* +0x240: `beq type, 2` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_eq_U, U50, U_lit in Hc2 by lia.
  { (* NLMSG_ERROR: +0x2a8 `bgeu ml, 36` *)
    apply Z.eqb_eq in Hc2.
    paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tk_span; rewrite branch_geu_U, U49, U_lit in Hc3 by lia.
    - (* ml >= 36: the int32 code at off + 16 (+0x5ec .. +0x638), `blez code` *)
      apply negb_true_iff, Z.ltb_ge in Hc3.
      remember (rd32s (tk_ck c ci) (off + 16)) as cd eqn:Erc.
      assert (HE : msg_scan (S f) (tk_ck c ci) off left = NlErr cd) by (rewrite Erc; apply ms_err; lia).
      rewrite <- (nk_chunk_nth kbs ci (off + 16) ltac:(lia) ltac:(lia)) in Ge0.
      rewrite <- (nk_chunk_nth kbs ci (off + 16 + 1) ltac:(lia) ltac:(lia)) in Ge1.
      rewrite <- (nk_chunk_nth kbs ci (off + 16 + 2) ltac:(lia) ltac:(lia)) in Ge2.
      rewrite <- (nk_chunk_nth kbs ci (off + 16 + 3) ltac:(lia) ltac:(lia)) in Ge3.
      assert (Hcode : cd = bz e0 + 256 * bz e1 + 65536 * bz e2 + 16777216 * sbz e3)
        by (rewrite Erc; exact (tw_rd32s_bytes (tk_ck c ci) (off + 16) e0 e1 e2 e3 ltac:(lia) Ge0 Ge1 Ge2 Ge3)).
      assert (Rrc : - 2 ^ 31 <= cd < 2 ^ 31) by (rewrite Erc; apply tw_rd32s_range; lia).
      assert (Ucode : U (tk_E c regs xs)
          (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt true 8 (SOff 54 0)) (SLit 24)) (SAlu ALU_SLL (SOff 53 0) (SLit 16)))
                       (SAlu ALU_OR (SAlu ALU_SLL (SOff 52 0) (SLit 8)) (SOff 51 0))) = cd mod 2 ^ 64)
        by (rewrite (tq_U_code _ e0 e1 e2 e3 E51 E52 E53 E54), Hcode; reflexivity).
      paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
      psrr_branch_tok RUN BR HS SHOK tk_span;
        rewrite tq_br_ge, (tq_Sg _ (SLit 0) 0 (U_SLit _ 0) ltac:(lia)), (tq_Sg _ _ cd Ucode ltac:(lia)) in Hc4.
      + (* code <= 0: a1 = code *)
        apply negb_true_iff, Z.ltb_ge in Hc4.
        paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
        tm_end md msF md2 Hfd Hfs.
        tq_rreg HS (11%bv : bv 5) R11.
        apply (tm_x2 ci regs mem md xs _ msF md2 cd HRET HI H0 HCM HB HM HCL Hci HS ltac:(vm_compute; reflexivity)
          HJ Hfd Hfs KP PR); [|rewrite R11; exact (tq_den_U _ _ cd Ucode)].
        unfold msg_ret. right; left. exists cd. split; [rewrite HV; exact HE | symmetry; apply tw_norm_nonpos; lia].
      + (* code > 0: a1 = 1000000 *)
        apply negb_false_iff, Z.ltb_lt in Hc4.
        paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
        tm_end md msF md2 Hfd Hfs.
        tq_rreg HS (11%bv : bv 5) R11.
        apply (tm_x2 ci regs mem md xs _ msF md2 1000000 HRET HI H0 HCM HB HM HCL Hci HS
          ltac:(vm_compute; reflexivity) HJ Hfd Hfs KP PR); [|rewrite R11; reflexivity].
        unfold msg_ret. right; left. exists cd. split; [rewrite HV; exact HE | symmetry; apply tw_norm_pos; lia].
    - (* ml < 36: a1 = -5 *)
      apply negb_false_iff, Z.ltb_lt in Hc3.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
      tm_end md msF md2 Hfd Hfs.
      tq_rreg HS (11%bv : bv 5) R11.
      apply (tm_x2 ci regs mem md xs _ msF md2 (- E_IO) HRET HI H0 HCM HB HM HCL Hci HS
        ltac:(vm_compute; reflexivity) HJ Hfd Hfs KP PR); [|rewrite R11; apply tq_den_U; rewrite U_SLit; reflexivity].
      unfold msg_ret. left. split; [|reflexivity]. rewrite HV. apply ms_short_err; rewrite <- ?Eml, <- ?Ety; lia. }
  apply Z.eqb_neq in Hc2.
  (* another type: +0x244 .. +0x258, off += NL_ALIGN(ml), left -= NL_ALIGN(ml), `bge left, 16` *)
  assert (HO : msg_scan (S f) (tk_ck c ci) off left = msg_scan f (tk_ck c ci) (off + nl_align ml) (left - nl_align ml))
    by (rewrite Eml; apply ms_other; rewrite <- ?Eml, <- ?Ety; lia).
  pose proof (tw_align_range ml ltac:(lia)) as Ral.
  assert (Sl : Sg (tk_E c regs xs) (SAlu ALU_SUB (SOff 28 0) (SAlu ALU_SLL (SAluw ALU_SRL (SOff 49 3) (SLit 2)) (SLit 2)))
               = left - nl_align ml)
    by (apply (tq_S_sub_align _ 49 28 ml left E49 E28); unfold NL_CHUNK_MAX in *; lia).
  paj_run_tok RUN HS HJ SHOK tk_span; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span; rewrite tq_br_ge, Sl, (tq_Sg _ (SLit 16) 16 (U_SLit _ 16) ltac:(lia)) in Hc3.
  - (* left' >= 16: the next message, +0x204 *)
    apply negb_true_iff, Z.ltb_ge in Hc3.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_MS; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    tm_end md msF md2 Hfd Hfs.
    tq_rreg HS (7%bv : bv 5) R7. tq_rreg HS (28%bv : bv 5) R28.
    apply (tm_xm ci (off + nl_align ml) (left - nl_align ml) f regs mem md xs _ msF md2 IH HI H0 HN HR H20 HCM HB HS
      ltac:(vm_compute; reflexivity) HJ Hfd Hfs KP PR).
    + rewrite R7. apply tk_den_of_U.
      apply (tq_U_add _ _ _ off (nl_align ml) U7 (tq_U_align _ 49 ml E49 ltac:(unfold NL_CHUNK_MAX in *; lia))).
      unfold NL_CHUNK_MAX in *. lia.
    + rewrite R28. apply tq_den_U. apply (tq_U_sub_align _ 49 28 ml left E49 E28); unfold NL_CHUNK_MAX in *; lia.
    + rewrite HV; exact HO.
    + lia.
    + lia.
    + lia.
  - (* left' < 16: the chunk's walk answers nothing, +0x1e0 *)
    apply negb_false_iff, Z.ltb_lt in Hc3.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_NX; [tm_awr U2 Hlo Hhi |]. tm_acc U2 KP PR HF HFr HG.
    tm_end md msF md2 Hfd Hfs.
    apply (tm_x1 ci regs mem md xs _ msF md2 HNXT HI H0 HN HR HCM HB HM HCL Hci HS ltac:(vm_compute; reflexivity)
      HJ Hfd Hfs KP PR).
    rewrite HV, HO. apply ms_short. lia.
Qed.

(* THE PIECE: the message loop, by induction on the fuel of msg_scan *)
Lemma tk_msg_ok : TK_RET SK B c -> TK_ATTR SK B c -> TK_MSG SK B c.
Proof.
  intros HRET HATTR ci off left fu HNXT. revert off left.
  induction fu as [|f IH]; intros off left regs mem md HI H0 HN HR H20 H7 H28 HCM HB HM HCL Hci HW Ho HL Hlf.
  { cbn [Z.of_nat] in Hlf. lia. }
  destruct (tq_ck SK B c HC ci Hci) as (Lck & Lmax & Nch).
  apply (tm_ms ci off regs mem md HI H0 HN HR H20 H7 Hci ltac:(unfold NL_CHUNK_MAX in *; lia)).
  intros regs2 md2 HI2 H02 HN2 HR2 K20 K7 K28 H11.
  apply (tm_mf ci off left f regs2 mem md2 HRET HATTR HNXT); try assumption.
  - intros off' left' regs' mem' md' HI' H0' HN' HR' H20' H7' H28' HCM' HB' HW' Ho' HL' Hl'.
    exact (IH off' left' regs' mem' md' HI' H0' HN' HR' H20' H7' H28' HCM' HB' HM HCL Hci HW' Ho' HL' Hl').
  - rewrite K20. exact H20.
  - rewrite K7. exact H7.
  - rewrite K28. exact H28.
Qed.

End w.
