(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound HBPlanImage HBAtable HBOpenDefs HBHdrDefs HBFullDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HBConeW HBConeWClosed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Lemma T_refused_die : forall fs, T_lit refused_lit fs = t_die msg_refused fs.
Proof. intros fs. unfold T_lit, t_die, W, exit_code. reflexivity. Qed.

(* [comment removed for export] *)
Lemma file_path_facts : forall argv fs path data, valid_argv argv -> drv_classify argv fs = DcFile path data ->
  length argv = 2%nat /\ nth 1 argv [] = path /\ path <> [] /\ path_has_slash path = false /\ path_is_dirref path = false
  /\ (length path <= 4095)%nat /\ fs_lookup fs path = Some data.
Proof.
  intros argv fs path data Hva EC.
  destruct (drv_classify_DcFile_inv _ _ _ _ EC) as (a0 & EA & Hl & Hne & Hnd & HL).
  assert (Htl : path_has_slash path = false /\ path_eqb path dotdot_path = false).
  { pose proof Hva as (_ & _ & _ & _ & Htl). rewrite EA in Htl. cbn [tl] in Htl. inversion Htl as [|? ? HH _]; subst. exact HH. }
  destruct Htl as [Hsl Hdd].
  repeat split; try assumption; try (rewrite EA; reflexivity); [|lia].
  unfold path_is_dirref. rewrite Hdd. destruct (path_eqb path dot_path) eqn:Ed; [|reflexivity]. exfalso. apply Hnd.
  destruct (list_eq_dec (fun a b : byte => bv_eq_dec _ a b) path dot_path) as [E|Hn]; [exact E | rewrite (path_eqb_neq _ _ Hn) in Ed; discriminate Ed].
Qed.

Theorem ha_full :
  file_leaf_stmt K0 T_file -> file_leaf_stmt KGE1 T_file -> file_leaf_stmt REFUSED T_refused -> ha_full_stmt t_target_ht.
Proof.
  intros L0 LK LR lim Hlim sp brk mbase rnd i Hsp Hbrk Hmb Hfit Hvi.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct i as [argv envp ifs sin0 uid gid groups net nofile sigmask hw abt vasz urnd tmp].
  destruct Hvi as (Hva & Hve & Hfs & _ & (Huid & Hgid) & Hnof & Hsig & Hhw & Habt & Hvas & _).   (* [comment removed for export] *)
  cbn [in_argv in_envp in_uid in_gid in_abort_terminal in_va_size] in *. subst abt vasz.
  set (i0 := mkProcInput_full argv envp ifs sin0 uid gid groups net nofile sigmask hw false Sv48 urnd tmp) in *.
  set (fs := in_fs i0) in *. set (sin := mkInStreams sin0 urnd).
  rewrite (init_config_inp_of _ _ _ _ _ _ _ _ i0 eq_refl eq_refl).
  change (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk mbase rnd lim _)
    with (INITA sp rnd brk mbase lim argv envp fs sin uid gid hw groups net nofile sigmask).
  clearbody fs.
  destruct (drv_verdict argv fs) eqn:Hv.
  - (* [comment removed for export] *)
    rewrite (spec_g_acc t_target_ht _ _ Hv).
    destruct (drv_classify argv fs) as [|p|p|p data] eqn:EC.
    + apply (HBConeWClosed.haw_cone_closed sp rnd brk mbase lim argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hv).
      intros path d E. rewrite EC in E. discriminate E.
    + apply (HBConeWClosed.haw_cone_closed sp rnd brk mbase lim argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hv).
      intros path d E. rewrite EC in E. discriminate E.
    + apply (HBConeWClosed.haw_cone_closed sp rnd brk mbase lim argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hv).
      intros path d E. rewrite EC in E. discriminate E.
    + destruct (Z_lt_ge_dec (Z.of_nat (length data)) MAX_INPUT) as [Hlt|Hge].
      * apply (HBConeWClosed.haw_cone_closed sp rnd brk mbase lim argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hv).
        intros path d E. rewrite EC in E. injection E as <- <-. exact Hlt.
      * (* [comment removed for export] *)
        destruct (file_path_facts argv fs p data Hva EC) as (Hargc & Hp & Hne & Hsl & Hdr & Hln & HL).
        assert (Hb : body_pre_target data = true) by (unfold drv_verdict in Hv; rewrite EC in Hv; exact Hv).
        unfold spec. rewrite EC. unfold t_opened. rewrite (t_body_pre_target data fs Hb). unfold t_body_pre.
        rewrite (proj2 (Z.leb_le MAX_INPUT (Z.of_nat (length data)))) by lia.
        rewrite <- HBConeW.T_cannot_die, <- T_refused_die.
        change (t_alt2 (T_cannot p fs) (T_lit refused_lit fs)) with (T_refused p data fs). rewrite <- Hp.
        apply (LR lim Hlim sp rnd brk mbase argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc data);
          rewrite ?Hp; try assumption.
        unfold REFUSED, flen. unfold MAX_INPUT in Hge. lia.
  - (* [comment removed for export] *)
    unfold drv_verdict in Hv. destruct (drv_classify argv fs) as [|p|p|p data] eqn:EC; try discriminate Hv.
    destruct (file_path_facts argv fs p data Hva EC) as (Hargc & Hp & Hne & Hsl & Hdr & Hln & HL).
    rewrite (spec_g_file t_target_ht argv fs p data EC Hv). rewrite <- HBConeW.T_cannot_die.
    change (t_alt2 (T_cannot p fs) (t_target_ht data fs)) with (T_file p data fs). rewrite <- Hp.
    unfold body_pre_target in Hv. apply orb_false_iff in Hv as [Hv H3]. apply orb_false_iff in Hv as [H1 H2].
    apply Z.leb_gt in H1. apply Nat.ltb_ge in H2. apply Nat.ltb_ge in H3. unfold MAX_INPUT in H1. unfold HDR_MIN in H2, H3.
    assert (Hfl : flen data = Z.of_nat (length data)) by (unfold flen; lia).
    destruct (Z_le_gt_dec (Z.of_nat (length data)) 65535) as [Hk0|Hk1].
    + apply (L0 lim Hlim sp rnd brk mbase argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc data);
        rewrite ?Hp; try assumption.
      unfold K0. rewrite Hfl. split; [lia|].
      unfold ION.room, ION.flenZ, ION.cfglen, ION.hbyte. unfold config_len, cfg_word, byte_at in H3.
      pose proof (Z.mod_pos_bound (bv_unsigned (nth 0 data (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 data (Z_to_bv 8 0))) 32768 ltac:(lia)). lia.
    + apply (LK lim Hlim sp rnd brk mbase argv envp fs sin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc data);
        rewrite ?Hp; try assumption.
      unfold KGE1. rewrite Hfl. lia.
Qed.
