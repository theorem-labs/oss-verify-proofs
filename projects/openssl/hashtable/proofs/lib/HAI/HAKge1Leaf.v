(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Namei.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ClaVerdict Spec SpecGen HTSpec ShapeLaws.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HAPlanImage HAAtable HAChain HACheckG HAParity HAJoin HATgtGlue HAOpenDefs HAHdrDefs HAFullDefs.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import C1Thm HAKge1 HAKge1A0 HAKge1A2 HAKge1A3 HAKge1A1 HAKge1B0 HAKge1B2 HAKge1B3 HAKge1B1.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.hashtable.lib.HAX Require S6HoleKA0 FeHoleA0 FeHoleOA0 S6HoleKA2 FeHoleA2 FeHoleOA2 S6HoleKA3 FeHoleA3 FeHoleOA3 S6HoleKA1 FeHoleA1 FeHoleOA1 S6HoleKB0 FeHoleB0 FeHoleOB0 S6HoleKB2 FeHoleB2 FeHoleOB2 S6HoleKB3 FeHoleB3 FeHoleOB3 S6HoleKB1 FeHoleB1 FeHoleOB1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hfi_stmt (fi_start : Z -> acs) : Prop :=
  forall sp rdraw brk0 argv envp fs uid hw, valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen (content_of argv fs) <= 2 ^ (16 + k) - 1 ->
  piece (SINVm HAPH sp rdraw brk0 argv envp uid hw (content_of argv fs)) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs (fi_start k) TTK.

(* [comment removed for export] *)
Lemma kclass : forall n, 65536 <= n <= 2 ^ 26 - 1 -> exists k, 1 <= k <= 10 /\ 2 ^ (15 + k) <= n <= 2 ^ (16 + k) - 1.
Proof.
  intros n Hn. change (2 ^ 26) with 67108864 in Hn.
  destruct (Z_lt_ge_dec n 131072); [exists 1; cbn; lia|]. destruct (Z_lt_ge_dec n 262144); [exists 2; cbn; lia|].
  destruct (Z_lt_ge_dec n 524288); [exists 3; cbn; lia|]. destruct (Z_lt_ge_dec n 1048576); [exists 4; cbn; lia|].
  destruct (Z_lt_ge_dec n 2097152); [exists 5; cbn; lia|]. destruct (Z_lt_ge_dec n 4194304); [exists 6; cbn; lia|].
  destruct (Z_lt_ge_dec n 8388608); [exists 7; cbn; lia|]. destruct (Z_lt_ge_dec n 16777216); [exists 8; cbn; lia|].
  destruct (Z_lt_ge_dec n 33554432); [exists 9; cbn; lia|]. exists 10; cbn; lia.
Qed.

Section Leaf.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable lim : Z.
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
  Let argv1 := nth 1 argv [].
  Hypothesis Hargc : length argv = 2%nat.
  Variable cont : list byte.
  Hypothesis Hne : argv1 <> [].
  Hypothesis Hsl : path_has_slash argv1 = false.
  Hypothesis Hdr : path_is_dirref argv1 = false.
  Hypothesis Hln : (length argv1 <= 4095)%nat.
  Hypothesis Hlk : fs_lookup fs argv1 = Some cont.
  Hypothesis HK : KGE1 cont.
  Lemma c_cont : c = cont.
  Proof. subst c argv1. destruct argv as [|a0 [|p [|q r]]]; try discriminate Hargc. cbn in Hlk |- *. rewrite Hlk. reflexivity. Qed.
  Lemma HF_c : 65536 <= flen c <= 2 ^ 26 - 1. Proof. rewrite c_cont. exact HK. Qed.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation PIECE := (piece SV (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) fs).
  Hypothesis HFI_A0 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1A0.fi_start_a0 k) TTK.
  Hypothesis HFI_A2 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1A2.fi_start_a2 k) TTK.
  Hypothesis HFI_A3 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1A3.fi_start_a3 k) TTK.
  Hypothesis HFI_A1 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1A1.fi_start_a1 k) TTK.
  Hypothesis HFI_B0 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1B0.fi_start_b0 k) TTK.
  Hypothesis HFI_B2 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1B2.fi_start_b2 k) TTK.
  Hypothesis HFI_B3 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1B3.fi_start_b3 k) TTK.
  Hypothesis HFI_B1 : forall k, 1 <= k <= 10 -> 2 ^ (15 + k) <= flen c <= 2 ^ (16 + k) - 1 -> PIECE (HAKge1B1.fi_start_b1 k) TTK.
  Lemma sv_init : SV (reblob (E0 HAPH sp rdraw brk0 argv envp uid hw) argv c) (FULL0 HAPH sp rdraw argv envp uid hw).
  Proof.
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.
  Theorem kge1_leaf_sec : crz HASEGS (INITA sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask) (T_file argv1 cont fs).
  Proof.
    destruct (kclass (flen cont) HK) as (k & Hk & HFk).
    pose proof (HAKge1.kge1_leaf sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk
                  (S6HoleKA0.s6_hole_ka0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA0.fe_hole_a0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA0.fe_hole_oa0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKA2.s6_hole_ka2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA2.fe_hole_a2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA2.fe_hole_oa2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKA3.s6_hole_ka3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA3.fe_hole_a3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA3.fe_hole_oa3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKA1.s6_hole_ka1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleA1.fe_hole_a1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOA1.fe_hole_oa1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKB0.s6_hole_kb0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB0.fe_hole_b0 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB0.fe_hole_ob0 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKB2.s6_hole_kb2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB2.fe_hole_b2 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB2.fe_hole_ob2 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKB3.s6_hole_kb3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB3.fe_hole_b3 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB3.fe_hole_ob3 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  (S6HoleKB1.s6_hole_kb1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleB1.fe_hole_b1 sp rdraw brk0 argv envp fs uid hw Hsp Hva) (FeHoleOB1.fe_hole_ob1 sp rdraw brk0 argv envp fs uid hw Hsp Hva)
                  TTK TTK_agree TTK_nil
                  HFI_A0 HFI_A2 HFI_A3 HFI_A1 HFI_B0 HFI_B2 HFI_B3 HFI_B1
                  k Hk HFk) as RZ.
    eapply crz_conseq; [exact RZ|]. unfold T_file. apply t_alt2_congr_r. rewrite <- c_cont.
    exact (ttk_target HAPH sp rdraw brk0 argv envp uid hw c _ _ fs sv_init HF_c).
  Qed.
End Leaf.

Theorem kge1_leaf_glue : hfi_stmt HAKge1A0.fi_start_a0 -> hfi_stmt HAKge1A2.fi_start_a2 -> hfi_stmt HAKge1A3.fi_start_a3 -> hfi_stmt HAKge1A1.fi_start_a1 -> hfi_stmt HAKge1B0.fi_start_b0 -> hfi_stmt HAKge1B2.fi_start_b2 -> hfi_stmt HAKge1B3.fi_start_b3 -> hfi_stmt HAKge1B1.fi_start_b1 -> file_leaf_stmt KGE1 T_file.
Proof.
  intros FA0 FA2 FA3 FA1 FB0 FB2 FB3 FB1 lim Hlim sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HK.
  exact (kge1_leaf_sec sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid Hargc cont Hne Hsl Hdr Hln Hlk HK
           (FA0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FA2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FA3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FA1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FB0 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FB2 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FB3 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit) (FB1 sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit)).
Qed.
