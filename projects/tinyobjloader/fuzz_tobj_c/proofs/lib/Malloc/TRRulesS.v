(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "@Corelib.Init.Logic"; "and"; "False"; "True"; "eq"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@Corelib.Init.Datatypes"; "list"; "fst"; "prod"; "pair"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesS.AngelicS"; "roomwS"; "jroomS"; "posts_roomS"; "TR_angS"; "proomS"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "w_cfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "ok_frameJ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "implJ"; "tr_rules"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract ContractDrv VmRoom RoomS TRRulesK HeapS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundR SymFrame SymSummary SymCall SymEntail SymHeap Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section AngelicS.
Variable segs : list Segment.
Variable Kc : ltac2:(tb__ "0|0|
S9S15A1S14OF_;F_;").
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S21Vsegs;Vok;VKc;A3").

Definition roomwS (X : Z) : assn := ltac2:(tb__ "0|0|
S16S19S1fS18R1A1A1VX;A2Lw;").

Definition TR_angS (k : Z) (P Q : assn) : Prop := ltac2:(tb__ "0|1|
S2S1cZ0M0Vk;A2S1eS1cG0R1A2S17Vsegs;Vok;S16S2VP;R1A1SeS1dR3Vk;A2R1A2A2Lw;S16S2VQ;R1A1SeR3R1A2A2Lw;A4F_;Fr;A2").

Definition jroomS (J : jpred) (X : Z) : jpred := ltac2:(tb__ "0|0|
S1S9S15A1S14S2VJ;R3R2R1A3S19R1VX;A2A2Lmd;Ltr;Lrho;").
Definition proomS (JL : jpost) (X : Z) : jpost := ltac2:(tb__ "0|0|
S1S1S9S15A1S14S2VJL;R4R3R2R1A4S19R1VX;A2A2Lmd;Ltr;LrhoL;Lrho0;").
Definition posts_roomS (Posts : list (sstate * jpost)) (X : Z) : list (sstate * jpost) := ltac2:(tb__ "0|1|
S13SbS0S7A2M0G0G0ScS0S7SaS0S7R1A3S12SdS0S7R1A3VX;A2A4Lp;VPosts;A4").

Lemma SPJ_roomS (J : jpred) S rho X w : ltac2:(tb__ "0|0|
S6S2S1aVsegs;VJ;VS;Vrho;Vw;A5SeVX;Vw;A2A2S1aVsegs;SfVJ;VX;A2VS;Vrho;Vw;A5A2").
Proof using . unfold SPJ, jroomS, roomwS. tauto. Qed.

Lemma posts_roomS_fst Posts X : ltac2:(tb__ "0|2|
S5S9S0A1S13SbS0S7A2M0S0SaS0S7A2M1S10VPosts;VX;A2A4S13G0S0G1VPosts;A4A3").
Proof using . unfold posts_roomS. rewrite map_map. reflexivity. Qed.

Lemma LQP_roomS n rho Posts X w : ltac2:(tb__ "0|0|
S2S8Vsegs;Vn;Vrho;VPosts;Vw;A5SeVX;Vw;A2A2S8Vsegs;Vn;Vrho;S10VPosts;VX;A2Vw;A5F_;").
Proof using .
  intros [(L & JL & rho' & Hin & Hag & Hsm & HJ) HR]. exists L, (proomS JL X), rho'.
  split; [apply in_map_iff; exists (L, JL); split; [reflexivity | exact Hin]|].
  split; [exact Hag|]. split; [exact Hsm|]. split; [exact HJ | exact HR].
Qed.

Lemma okJ_ofS (J : jpred) X : ltac2:(tb__ "0|1|
S22VKc;VJ;A2S2S1bVsegs;Vok;SfVJ;VX;A2M0A3S20Vsegs;Vok;G0A3A2F_;").
Proof using HS.
  intros HJ. destruct HS as (F1 & F2 & _). split.
  - intros rho tr ms md ms' [Hj _]. exact (F1 tr ms md ms' (HJ rho tr md Hj)).
  - intros rho tr ms md x8 [Hj _]. exact (F2 tr ms md x8 (HJ rho tr md Hj)).
Qed.

Theorem tr_rules_angelicS : ltac2:(tb__ "0|0|
S23Vsegs;VKc;S3S4S11A5").
Proof using HS.
  constructor.
  -   intros k P P' Q HP [Hk H]. split; [exact Hk|]. intros r Hr.
    eapply triple_pre; [|exact (H r Hr)]. intros w [A B]. split; [apply HP; exact A | exact B].
  -   intros k P Q Q' HQ [Hk H]. split; [exact Hk|]. intros r Hr.
    eapply triple_post; [|exact (H r Hr)]. intros w [A B]. split; [apply HQ; exact A | exact B].
  -   intros k k' P Q Hkk [Hk H]. split; [lia|]. intros r Hr.
    eapply triple_pre; [|exact (H r Hr)]. intros w [A B]. split; [exact A|].
    eapply vm_roomS_mono; [|exact B]. lia.
  -   intros k P Q Hk HPQ. split; [exact Hk|]. intros r Hr. apply triple_skip.
    intros w [A B]. split; [apply HPQ; exact A|]. eapply vm_roomS_mono; [|exact B]. lia.
  -   intros k1 k2 P R Q [Hk1 H1] [Hk2 H2]. split; [lia|]. intros r Hr.
    eapply triple_seq; [|exact (H2 r Hr)].
    eapply triple_pre; [|exact (H1 (r + k2) ltac:(lia))]. intros w [A B]. split; [exact A|].
    replace (r + k2 + k1) with (r + (k1 + k2)) by lia. exact B.
  -   intros k P Q Hk H. split; [exact Hk|]. intros r Hr n Hg w [Hw HRw].
    destruct (H w Hw) as (P' & HP' & [_ HT]). exact (HT r Hr n Hg w (conj HP' HRw)).
  -
    intros k fuel cuts K S leaves rho Q Hk Hrun Hlen HK Hc. split; [exact Hk|]. intros r Hr.
    eapply triple_pre with (P := SP segs (fun tr md => K tr md /\ vm_roomS md (r + k)) S rho).
    { intros w [[Hsm HKw] HR]. split; [exact Hsm|]. split; [exact HKw | exact HR]. }
    apply (run_tr segs ok fuel cuts S leaves _ rho _ Hrun Hlen).
    + intros tr ms md ms' [Hk' _]. exact (proj1 HS tr ms md ms' (HK tr md Hk')).
    + intros Lf rho' Hin Hag. destruct (Hc Lf rho' Hin Hag) as [_ HT].
      eapply triple_pre; [|exact (HT r Hr)]. intros w [Hsm [HKw HR]]. split; [split; [exact Hsm | exact HKw] | exact HR].
  -
    intros kc k2 J Jp Cl Pre sb R Posts Q rho Hk2 He Hchk Hsum Hin Hout.
    pose proof (proj1 (Hsum rho)) as Hkc. split; [lia|]. intros r Hr.
    eapply triple_pre with (P := SPJ segs (jroomS J (r + k2 + kc)) Cl rho).
    { intros w [A B]. apply (proj1 (SPJ_roomS _ _ _ _ _)). split; [exact A|]. replace (r + k2 + kc) with (r + (kc + k2)) by lia. exact B. }
    apply (call_soundP segs ok (jroomS J (r + k2 + kc)) (jroomS Jp (r + k2 + kc)) Cl Pre sb R (posts_roomS Posts (r + k2))
             (fun w => Q w /\ roomwS r w) rho He).
    + rewrite posts_roomS_fst. exact Hchk.
    + intros rho1. destruct (Hsum rho1) as [_ HT].
      eapply triple_pre; [|eapply triple_post; [|exact (HT (r + k2) ltac:(lia))]].
      * intros w Hw. exact (proj2 (SPJ_roomS _ _ _ _ _) Hw).
      * intros w Hw. apply LQP_roomS. exact Hw.
    + intros tr ms md Hsm [HJ HR]. split; [exact (Hin tr ms md Hsm HJ) | exact HR].
    + intros L JL' tr ms md rhoL tr' ms' md' HinL Hsm [HJ HR] Hag HsmL HJL'.
      apply in_map_iff in HinL as ([L0 JL0] & E & HinL). cbn [fst snd] in E.
      injection E as EL EJ. subst L0. subst JL'. destruct HJL' as [HJL HRL].
      destruct (Hout L JL0 tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag HsmL HJL) as [HI HC].
      split; [exact HI|]. intros rho' Hlink. destruct (HC rho' Hlink) as [_ HT].
      eapply triple_pre; [|exact (HT r Hr)].
      intros w [HsmW [HJw HRw]]. split; [split; [exact HsmW | exact HJw] | exact HRw].
  -
    intros k kf ko J Jf Jo S rho Q HJ Hi H17 HP _ Hok Hko Hk H32. specialize (Hok I).
    pose proof (FreeGap.page_round_up_Z_ge (bv_unsigned (eval rho (reg_sv S 11)))) as Hge.
    pose proof (urange (eval rho (reg_sv S 11))) as Hu.
    assert (Hn0 : 0 <= mmap_nZ (eval rho (reg_sv S 11))) by (unfold mmap_nZ; lia).
    split; [lia|]. intros r Hr.
    set (len := eval rho (reg_sv S 11)) in *.
    destruct (okJ_ofS J (r + k) HJ) as [OF OP].
    eapply triple_pre with (P := SPJ segs (jroomS J (r + k)) S rho).
    { intros w Hw. apply (proj1 (SPJ_roomS _ _ _ _ _)). exact Hw. }
    eapply triple_seq.
    + apply triple1_triple.
      apply (triple1_mmap_rwJ_forced segs ok (jroomS J (r + k)) (fun _ _ _ => False) (fun a => jroomS (Jo a) (r + ko)) S rho OF OP Hi H17).
      intros tr ms md Hsp [HJx HR].
      destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
      destruct (HP tr ms md Hsp HJx) as (Hlen & Hmod & Hnr & _ & Hall).
      assert (Hpos : 0 < bv_unsigned (ms_gpr ms 1)).
      { pose proof (urange (ms_gpr ms 1)) as U.
        destruct (Z.eq_dec (bv_unsigned (ms_gpr ms 1)) 0) as [E|NE]; [|lia].
        exfalso. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
      rewrite G1 in *.
      split; [exact Hlen|]. split; [exact Hmod|]. split; [exact Hnr|]. split.
      *   intros Hrf. exact (vm_roomS_rw_refused_False md (r + k) len (ms_gpr ms 3) HR Hpos ltac:(lia) Hnr Hrf).
      * intros a Hpl. destruct (Hall a Hpl) as (Hdisj & Hnro & HJo).
        split; [exact Hdisj|]. split; [exact Hnro|]. split; [exact HJo|].
        eapply vm_roomS_mono; [|exact (vm_roomS_grant_rw md (r + k) len a (ms_gpr ms 0) (ms_gpr ms 3) HR Hpos ltac:(lia) Hpl)]. lia.
    + apply triple_disj.
      * apply triple_skip. intros w [_ F]. exact (False_ind _ F).
      * apply triple_ex. intros a. destruct (Hok a) as [_ HT].
        eapply triple_pre; [|exact (HT r Hr)]. intros w Hw. exact (proj2 (SPJ_roomS _ _ _ _ _) Hw).
Qed.
End AngelicS.
