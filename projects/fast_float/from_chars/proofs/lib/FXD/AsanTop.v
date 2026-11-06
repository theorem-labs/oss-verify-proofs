(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open Namei.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec RefLayout ShapeSet RealizesCfg RealizesAbort AsanAcct FxLin FxCore FxSound FxMem FxSubst FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChain FxWvC FxChMain FxChEntM.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChRecont.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChRecont.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanStartCert OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanStartAll OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanFinAB OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanFinEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanRdErr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanUsageT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCoNFT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanLeafEntryT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanLeafEntryT.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTop0.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTBridge AsanTop0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanRdErr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanUsageT.AsanUsage OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCoNFT.AsanCoNFDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanLeafEntryT.AsanCoNFThmT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanLeafEntryT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTop0.AsanStartAg OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTBridge OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTop0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma FRZ0_M1 : sm_frz M1 = FRZ0. Proof. vm_compute. reflexivity. Qed.

Section Top.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hfs : sc_fs cfg = true.

(* [comment removed for export] *)
Definition at_main (sp brk0 mb : word) (draw : EntryDraw) (inp : ProcInput) (T : TSet) : Prop :=
  forall mem0 E ms model, agree 17 (E0 sp brk0 draw inp) E ->
  DEN ASEGS LIM (model0 sp brk0 mb LIM inp) mem0 E TMAIN MMAIN ms model -> HA E MMAIN AMAIN mem0 ->
  frz_keep E (m0 sp draw inp) mem0 -> realizes_cfg ASEGS cfg (mkCfg ms model) T.
Hypothesis H_file : forall sp brk0 mb draw inp data, valid_sp sp -> valid_brk ASEGS brk0 -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> length (in_argv inp) = 2%nat ->
  (length (nth 1 (in_argv inp) []) < 4096)%nat -> path_eqb (nth 1 (in_argv inp) []) [] = false ->
  path_is_dirref (nth 1 (in_argv inp) []) = false -> fs_lookup (in_fs inp) (nth 1 (in_argv inp) []) = Some data ->
  at_main sp brk0 mb draw inp (t_alt2 (t_die (msg_cannot_open (nth 1 (in_argv inp) [])) (in_fs inp)) (t_body data (in_fs inp))).

(* [comment removed for export] *)
#[using="Hoff Hfs H_file"] Theorem main_spec : forall sp brk0 mb draw inp, valid_sp sp -> valid_brk ASEGS brk0 -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
  main_ok cfg sp brk0 mb draw inp (spec (in_argv inp) (in_fs inp)).
Proof. LiaFast.lf_pins (fun (Hoff Hfs H_file : LiaFast.U) => LiaFast.u0).
  intros sp brk0 mb draw inp Hsp Hbrk Hfit Hva Hve Hvfs mem0 E ms model Hag Hd HA Hfk.
  pose proof (ofs_b sp inp Hsp Hfit Hva Hve) as (O1 & O2 & O3 & O4 & O5).
  assert (HC : OFS sp <= OFS sp <= OFS sp) by lia.
  assert (Hsame : forall p, In p (sm_frz M1) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) ->
                    mem0 (Z_to_bv 64 w) = m0 sp draw inp (Z_to_bv 64 w)) by (rewrite FRZ0_M1; exact Hfk).
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [H2|H2].
  - assert (Hex : exists a0 p, in_argv inp = [a0; p]).
    { destruct (in_argv inp) as [|a0 [|p [|a2 r]]]; cbn [length] in H2; try lia. exists a0, p. reflexivity. }
    destruct Hex as (a0 & p & Hav).
    rewrite Hav. cbn [spec].
    assert (Hp1 : nth 1 (in_argv inp) [] = p) by (rewrite Hav; reflexivity).
    assert (Hsl : path_has_slash p = false).
    { destruct Hva as (_ & _ & _ & _ & Htl). rewrite Hav in Htl. cbn [tl] in Htl. apply Forall_cons_iff in Htl as [[X _] _]. exact X. }
    (* [comment removed for export] *)
    assert (NF : nf_case (in_fs inp) p -> realizes_cfg ASEGS cfg (mkCfg ms model) (t_die (msg_cannot_open p) (in_fs inp))).
    { intros Hc. rewrite <- Hp1 in Hc |- *.
      exact (nf_entryT cfg Hoff Hfs sp brk0 mb draw inp Hsp Hfit Hva Hve (OFS sp) (OFS sp) HC mem0 E ms model Hag Hd HA Hsame
               ltac:(rewrite Hav; reflexivity) Hc). }
    destruct (4096 <=? length p)%nat eqn:Hl.
    + apply NF. right. right. apply Nat.leb_le. exact Hl.
    + apply Nat.leb_gt in Hl.
      destruct (path_eqb p []) eqn:He.
      * apply NF. right. left. destruct p; [reflexivity | cbn in He; discriminate].
      * destruct (path_is_dirref p) eqn:Hdr.
        -- assert (Hdd : path_eqb p dotdot_path = false).
           { destruct Hva as (_ & _ & _ & _ & Htl). rewrite Hav in Htl. cbn [tl] in Htl. apply Forall_cons_iff in Htl as [[_ X] _]. exact X. }
           pose proof (dirref_dot p Hdr Hdd) as Hp.
           rewrite <- Hp1.
           exact (dirref_entryT cfg Hoff Hfs sp brk0 mb draw inp Hsp Hfit Hva Hve (OFS sp) (OFS sp) HC mem0 E ms model Hag Hd HA Hsame
                    ltac:(rewrite Hav; reflexivity) ltac:(rewrite Hp1; exact Hp)).
        -- destruct (fs_lookup (in_fs inp) p) as [data|] eqn:Hlk.
           ++ rewrite <- Hp1.
              exact (H_file sp brk0 mb draw inp data Hsp Hbrk Hfit Hva Hve Hvfs ltac:(rewrite Hav; reflexivity) ltac:(rewrite Hp1; exact Hl)
                       ltac:(rewrite Hp1; exact He) ltac:(rewrite Hp1; exact Hdr) ltac:(rewrite Hp1; exact Hlk) mem0 E ms model Hag Hd HA Hfk).
           ++ apply NF. left. repeat split; assumption.
  - assert (Hsp' : spec (in_argv inp) (in_fs inp) = t_die (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
    { unfold spec. destruct (in_argv inp) as [|a0 [|a1 [|a2 r]]]; cbn in H2 |- *; try reflexivity. exfalso. exact (H2 eq_refl). }
    rewrite Hsp'.
    exact (usage_entryT cfg Hoff Hfs sp brk0 mb draw inp Hsp Hfit Hva Hve (OFS sp) (OFS sp) HC mem0 E ms model Hag Hd HA Hsame H2).
Qed.

(* [comment removed for export] *)
#[using="Hoff Hfs H_file"] Theorem asan_realizes : image_realizes_cfg_e cfg ASEGS Asan.M.init_pc APH LIM (fun inp => spec (in_argv inp) (in_fs inp)).
Proof. LiaFast.lf_pins (fun (Hoff Hfs H_file : LiaFast.U) => LiaFast.u0).
  intros sp brk0 mb rnd inp Hven Hinp.
  destruct Hinp as (Hva & Hve & Hvfs & Hrel & Hcr & _ & _ & _ & Hsv & _).
  apply (valid_entry_sv48 _ _ _ Hsv) in Hven. destruct Hven as (Hsp & Hbrk & Hmb & Hfit).
  destruct Hcr as [Hid _].
  apply (asan_from_main cfg Hoff sp brk0 mb rnd inp _ Hsp Hbrk Hfit Hva Hve Hid).
  exact (main_spec sp brk0 mb rnd inp Hsp Hbrk Hfit Hva Hve Hvfs).
Qed.
End Top.
