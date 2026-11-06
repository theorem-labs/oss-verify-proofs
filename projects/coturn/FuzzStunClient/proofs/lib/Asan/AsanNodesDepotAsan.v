(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 DepotInvG AxPriv AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesDepot AsanNodesDepotSoundG AsanPlanImages SumsAsanSpecs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import ImgZero AsanDepotMem AsanDepotInv AsanDepotSpec AsanDepotImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2 AX2S AP APS APSX.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma asan_depot_inv_iff : forall B P ncap fcap k m,
  depot_invG ASEGS DEPOT SSB IMGHI B P ncap fcap k m <-> depot_inv B P ncap fcap k m.
Proof.
  intros B P ncap fcap k m. unfold depot_invG, depot_inv. split.
  - intros ([n tf st tab lnk hsh] & C & G & Hk & Hn & Htf & Hst & OB & OP).
    exists (AsanDepotInv.DS n tf st tab lnk hsh). cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st d_n d_tf d_st] in *.
    destruct C as (Ctab & Cn & Cmap & Cnodes & Ctf & CP & Cst & Cr).
    cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st DepotInvG.d_tab DepotInvG.d_lnk DepotInvG.d_hsh] in *.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
    split; [|split; [unfold depot_geom; repeat split; assumption || lia | repeat split; assumption]].
    unfold depot_cells. cbn [d_n d_tf d_st d_tab d_lnk d_hsh].
    split; [exact Ctab|]. split; [exact Cn|]. split; [exact Cmap|]. split; [exact Cnodes|]. split; [exact Ctf|]. split; [exact CP|]. split; [exact Cst|]. exact Cr.
  - intros ([n tf st tab lnk hsh] & C & G & Hk & Hn & Htf & Hst & OB & OP).
    exists (DepotInvG.DS n tf st tab lnk hsh). cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st d_n d_tf d_st] in *.
    destruct C as (Ctab & Cn & Cmap & Cnodes & Ctf & CP & Cst & Cr).
    cbn [d_n d_tf d_st d_tab d_lnk d_hsh] in *.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    split; [|split; [unfold depot_geomG; repeat split; assumption || lia | repeat split; assumption]].
    unfold depot_cellsG. cbn [DepotInvG.d_n DepotInvG.d_tf DepotInvG.d_st DepotInvG.d_tab DepotInvG.d_lnk DepotInvG.d_hsh].
    split; [exact Ctab|]. split; [exact Cn|]. split; [exact Cmap|]. split; [exact Cnodes|]. split; [exact Ctf|]. split; [exact CP|]. split; [exact Cst|]. exact Cr.
Qed.

Lemma asan_put_spec : put_specG ASEGS DEPOT SSB IMGHI.
Proof.
  intros mem rom usp T w size tag bs ret B P ncap fcap k regs HI Hk Husp1 Husp2 Hstk HT1 HT2 HTrd HTstk Hw Hsz Htg HBstk HPstk HBT HPT Hret H1 H2 H10 H11.
  apply asan_depot_inv_iff in HI.
  destruct (put_spec mem rom usp T w size tag bs ret B P ncap fcap k regs HI Hk Husp1 Husp2 Hstk HT1 HT2 HTrd HTstk Hw Hsz Htg HBstk HPstk HBT HPT Hret H1 H2 H10 H11)
    as (regs' & mem' & id & RUN & HI' & R10 & Hid & R2 & R1 & RR & FR & GR).
  exists regs', mem', id. split; [|split; [apply asan_depot_inv_iff; exact HI' | repeat (split; [assumption|]); exact GR]].
  match type of RUN with msteps _ (mkst _ ?pp _ _) _ => replace (Z_to_bv 64 (DPN.put_entry_of IMGHI)) with pp by (apply bv_eq; reflexivity) end.
  exact RUN.
Qed.


Section AsanNode.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis nx0_ge7 : APS.nx0_ok nx0.
Variable FS0 : Fs.Fs.

Theorem asan_dpn_ext_sound : ext_stmt ASEGS ASAN nx0 LIMIT (DPN.xn ASEGS nx0 DEPOT SSB IMGHI) SINV argH FS0.
Proof.
  eapply (dpn_xn_sound ASEGS ASAN nx0 LIMIT); try eassumption;
    first [ exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_segs_wr | exact asan_tab_img_zero
          | exact asan_put_spec | lia | idtac ].
Qed.
End AsanNode.
