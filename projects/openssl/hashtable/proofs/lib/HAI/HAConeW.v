(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HACheck0 HACheck1 HAArg HAChain HAUsageDefs HAOpenDefs HADirDefs HAHdrDefs
  C2A0Lit S6EndA0 C3A0Lit FEEndA0 C4A0Lit FEEndOA0 C5A0Lit FEEndDA0 C6A0Lit FEEndHA0 C2A2Lit S6EndA2 C3A2Lit FEEndA2 C4A2Lit FEEndOA2 C5A2Lit FEEndDA2 C6A2Lit FEEndHA2 C2A3Lit S6EndA3 C3A3Lit FEEndA3 C4A3Lit FEEndOA3 C5A3Lit FEEndDA3 C6A3Lit FEEndHA3 C2A1Lit S6EndA1 C3A1Lit FEEndA1 C4A1Lit FEEndOA1 C5A1Lit FEEndDA1 C6A1Lit FEEndHA1 C2B0Lit S6EndB0 C3B0Lit FEEndB0 C4B0Lit FEEndOB0 C5B0Lit FEEndDB0 C6B0Lit FEEndHB0 C2B2Lit S6EndB2 C3B2Lit FEEndB2 C4B2Lit FEEndOB2 C5B2Lit FEEndDB2 C6B2Lit FEEndHB2 C2B3Lit S6EndB3 C3B3Lit FEEndB3 C4B3Lit FEEndOB3 C5B3Lit FEEndDB3 C6B3Lit FEEndHB3 C2B1Lit S6EndB1 C3B1Lit FEEndB1 C4B1Lit FEEndOB1 C5B1Lit FEEndDB1 C6B1Lit FEEndHB1 HAUsageLeaf HAOpen HADir HAHdr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma T_usage_die : forall a fs, T_usage a fs = t_die (msg_usage a) fs.
Proof. intros a fs. unfold T_usage, t_die, W, usage_bytes, msg_usage, exit_code. reflexivity. Qed.
Lemma T_cannot_die : forall p fs, T_cannot p fs = t_die (msg_cannot_open p) fs.
Proof. intros p fs. unfold T_cannot, t_die, W, cannot_bytes, msg_cannot_open, exit_code. reflexivity. Qed.
Lemma T_readerr_die : forall p fs, T_readerr p fs = t_die (msg_read_error p) fs.
Proof. intros p fs. unfold T_readerr, t_die, W, readerr_bytes, msg_read_error, exit_code. reflexivity. Qed.
Lemma T_short_die : forall fs, T_lit short_lit fs = t_die msg_short fs.
Proof. intros fs. unfold T_lit, t_die, W, exit_code. reflexivity. Qed.
Lemma T_overrun_die : forall fs, T_lit overrun_lit fs = t_die msg_overrun fs.
Proof. intros fs. unfold T_lit, t_die, W, exit_code. reflexivity. Qed.

Lemma path_eqb_false_neq : forall p q, path_eqb p q = false -> p <> q.
Proof.
  intros p q H ->. assert (HT : path_eqb q q = true).
  { destruct (path_eqb q q) eqn:E; [reflexivity|]. exfalso.
    destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) q q) as [_|Hn]; [|exact (Hn eq_refl)].
    unfold path_eqb in E. revert E. induction q as [|x q IH]; cbn; [discriminate|]. rewrite bv_eqb_refl. exact IH. }
  rewrite HT in H. discriminate H.
Qed.

Section Cone.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable lim : Z.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InStreams.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk HASEGS brk0.
  Hypothesis Hlim : (AsanInit.LIMIT <= lim)%Z.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  (* [comment removed for export] *)
  Hypothesis H_S6_A0 : FXHOLE c2a0_hs10 s6enda0.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.   Hypothesis H_FEO_A0 : FXHOLE c4a0_hs21 feendoa0.
  Hypothesis H_FED_A0 : FXHOLE c5a0_hs23 feendda0.   Hypothesis H_FEH_A0 : FXHOLE c6a0_hs24 feendha0.
  Hypothesis H_S6_A2 : FXHOLE c2a2_hs10 s6enda2.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.   Hypothesis H_FEO_A2 : FXHOLE c4a2_hs21 feendoa2.
  Hypothesis H_FED_A2 : FXHOLE c5a2_hs23 feendda2.   Hypothesis H_FEH_A2 : FXHOLE c6a2_hs24 feendha2.
  Hypothesis H_S6_A3 : FXHOLE c2a3_hs10 s6enda3.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.   Hypothesis H_FEO_A3 : FXHOLE c4a3_hs21 feendoa3.
  Hypothesis H_FED_A3 : FXHOLE c5a3_hs23 feendda3.   Hypothesis H_FEH_A3 : FXHOLE c6a3_hs24 feendha3.
  Hypothesis H_S6_A1 : FXHOLE c2a1_hs10 s6enda1.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.   Hypothesis H_FEO_A1 : FXHOLE c4a1_hs21 feendoa1.
  Hypothesis H_FED_A1 : FXHOLE c5a1_hs23 feendda1.   Hypothesis H_FEH_A1 : FXHOLE c6a1_hs24 feendha1.
  Hypothesis H_S6_B0 : FXHOLE c2b0_hs10 s6endb0.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.   Hypothesis H_FEO_B0 : FXHOLE c4b0_hs21 feendob0.
  Hypothesis H_FED_B0 : FXHOLE c5b0_hs23 feenddb0.   Hypothesis H_FEH_B0 : FXHOLE c6b0_hs24 feendhb0.
  Hypothesis H_S6_B2 : FXHOLE c2b2_hs10 s6endb2.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.   Hypothesis H_FEO_B2 : FXHOLE c4b2_hs21 feendob2.
  Hypothesis H_FED_B2 : FXHOLE c5b2_hs23 feenddb2.   Hypothesis H_FEH_B2 : FXHOLE c6b2_hs24 feendhb2.
  Hypothesis H_S6_B3 : FXHOLE c2b3_hs10 s6endb3.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.   Hypothesis H_FEO_B3 : FXHOLE c4b3_hs21 feendob3.
  Hypothesis H_FED_B3 : FXHOLE c5b3_hs23 feenddb3.   Hypothesis H_FEH_B3 : FXHOLE c6b3_hs24 feendhb3.
  Hypothesis H_S6_B1 : FXHOLE c2b1_hs10 s6endb1.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.   Hypothesis H_FEO_B1 : FXHOLE c4b1_hs21 feendob1.
  Hypothesis H_FED_B1 : FXHOLE c5b1_hs23 feenddb1.   Hypothesis H_FEH_B1 : FXHOLE c6b1_hs24 feendhb1.

  #[local] Notation INIT := (init_config HASEGS Asan.M.init_pc HAPH sp brk0 mbase rdraw lim (inp argv envp fs stdin uid gid hw groups net nofile sigmask)).   (* [comment removed for export] *)

  Lemma cone_usage : length argv <> 2%nat -> crz HASEGS INIT (t_die (msg_usage (hd [] argv)) fs).
  Proof.
    intros Hn. replace (hd [] argv) with (nth 0 argv []) by (destruct argv; reflexivity). rewrite <- T_usage_die.
    eapply usage_leaf; diet_eassumption.
  Qed.

  Lemma tl_facts : forall a0 p, argv = [a0; p] -> path_has_slash p = false /\ path_eqb p dotdot_path = false.
  Proof. intros a0 p EA. pose proof Hva as (_ & _ & _ & _ & Htl). rewrite EA in Htl. cbn [tl] in Htl. inversion Htl as [|? ? HH _]; subst. exact HH. Qed.

  Theorem ha_cone : drv_verdict argv fs = true ->
    (forall path data, drv_classify argv fs = DcFile path data -> Z.of_nat (length data) < MAX_INPUT) ->
    crz HASEGS INIT (spec argv fs).
  Proof.
    intros Hv Hsmall. unfold spec. unfold drv_verdict in Hv.
    destruct (drv_classify argv fs) as [|path|path|path data] eqn:EC.
    - (* [comment removed for export] *)
      apply cone_usage. intros H2. clear Hv Hsmall.
      destruct argv as [|a [|p [|q r]]]; try discriminate H2. cbn [drv_classify] in EC.
      repeat match type of EC with context [if ?b then _ else _] => destruct b end; try destruct (fs_lookup fs p); discriminate EC.
    - (* [comment removed for export] *)
      destruct (drv_classify_DcNoOpen_inv _ _ _ EC) as (a0 & EA & Hc).
      assert (Hargc : length argv = 2%nat) by (rewrite EA; reflexivity). assert (Hp : nth 1 argv [] = path) by (rewrite EA; reflexivity).
      destruct (tl_facts a0 path EA) as [Hsl Hdd].
      rewrite <- T_cannot_die, <- Hp. eapply open_leaf; try diet_eassumption. rewrite Hp.
      destruct Hc as [H4|[[_ H0]|(Hl & Hne & Hnd & HL)]]; [left; exact H4 | right; left; exact H0 | right; right].
      repeat split; try assumption; [|lia]. unfold path_is_dirref. rewrite Hdd.
      destruct (path_eqb path dot_path) eqn:Ed; [|reflexivity]. exfalso. apply Hnd.
      destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) path dot_path) as [E|Hn]; [exact E | rewrite (path_eqb_neq _ _ Hn) in Ed; discriminate Ed].
    - (* [comment removed for export] *)
      destruct (drv_classify_DcDir_inv _ _ _ EC) as (a0 & EA & Hdot).
      assert (Hargc : length argv = 2%nat) by (rewrite EA; reflexivity). assert (Hp : nth 1 argv [] = path) by (rewrite EA; reflexivity).
      rewrite <- T_cannot_die. unfold t_opened_dir. rewrite <- T_readerr_die. change (t_alt2 (T_cannot path fs) (T_readerr path fs)) with (T_dir path fs).
      rewrite <- Hp. eapply dir_leaf; try diet_eassumption. rewrite Hp, Hdot. reflexivity.
    - (* [comment removed for export] *)
      destruct (drv_classify_DcFile_inv _ _ _ _ EC) as (a0 & EA & Hl & Hne & Hnd & HL).
      assert (Hargc : length argv = 2%nat) by (rewrite EA; reflexivity). assert (Hp : nth 1 argv [] = path) by (rewrite EA; reflexivity).
      destruct (tl_facts a0 path EA) as [Hsl Hdd].
      assert (Hndr : path_is_dirref path = false).
      { unfold path_is_dirref. rewrite Hdd. destruct (path_eqb path dot_path) eqn:Ed; [|reflexivity]. exfalso. apply Hnd.
        destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) path dot_path) as [E|Hn]; [exact E | rewrite (path_eqb_neq _ _ Hn) in Ed; discriminate Ed]. }
      pose proof (Hsmall path data eq_refl) as Hlt.
      unfold t_opened. rewrite (t_body_pre_target data fs Hv). unfold t_body_pre.
      destruct (MAX_INPUT <=? Z.of_nat (length data)) eqn:EM; [apply Z.leb_le in EM; lia|].
      unfold body_pre_target in Hv. rewrite EM in Hv. cbn [orb] in Hv. unfold MAX_INPUT in Hlt.
      destruct (length data <? HDR_MIN)%nat eqn:ES.
      + apply Nat.ltb_lt in ES. unfold HDR_MIN in ES.
        rewrite <- T_cannot_die, <- T_short_die. change (t_alt2 (T_cannot path fs) (T_lit short_lit fs)) with (T_hdr short_lit path fs).
        rewrite <- Hp. eapply (hdr_short_leaf sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc data);
          try diet_eassumption; try (rewrite Hp; assumption); [rewrite Hp; lia | unfold flen; lia].
      + cbn [orb] in Hv. apply Nat.ltb_lt in Hv. apply Nat.ltb_ge in ES. unfold HDR_MIN in ES, Hv.
        rewrite <- T_cannot_die, <- T_overrun_die. change (t_alt2 (T_cannot path fs) (T_lit overrun_lit fs)) with (T_hdr overrun_lit path fs).
        rewrite <- Hp. eapply (hdr_overrun_leaf sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc data);
          try diet_eassumption; try (rewrite Hp; assumption); [rewrite Hp; lia | unfold flen; lia |].
        unfold ION.room, ION.flenZ, ION.cfglen, ION.hbyte. unfold config_len, cfg_word, byte_at in Hv.
        pose proof (Z.mod_pos_bound (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) 32768 ltac:(lia)). lia.
  Qed.
End Cone.
