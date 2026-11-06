(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "w_cfg"; "@Corelib.Init.Datatypes"; "list"; "fst"; "prod"; "pair"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "@Corelib.Init.Logic"; "and"; "True"; "False"; "eq"; "iff"; "or"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK.Angelic"; "roomw"; "posts_room"; "TR_ang"; "jroom"; "proom"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "vm_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "implJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "ok_frameJ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "ok_pframeJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "ok_sideK"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract ContractDrv VmRoom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundR SymFrame SymSummary SymCall SymEntail SymHeap Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section TRR.
Variable segs : list Segment.
Variable Kc : ltac2:(tb__ "0|0|
S5S13A1S12OF_;F_;").

Variables RF GF : Prop.

Definition implK (K : list event -> Model -> Prop) : Prop := ltac2:(tb__ "0|0|
S5S13A1S12VK;R2R1A2VKc;R3R2A2F_;Fmd;Ftr;").
Definition implJ (J : jpred) : Prop := ltac2:(tb__ "0|0|
SbS5S13A1S12VJ;R3R2R1A3VKc;R3R2A2F_;Fmd;Ftr;Frho;").

Record tr_rules (TR : Z -> assn -> assn -> Prop) : Prop := mkTRR {
  trr_pre : forall k (P P' Q : assn), (forall w, P' w -> P w) -> TR k P Q -> TR k P' Q;
  trr_post : forall k (P Q Q' : assn), (forall w, Q w -> Q' w) -> TR k P Q -> TR k P Q';
  trr_mono : forall k k' (P Q : assn), k <= k' -> TR k P Q -> TR k' P Q;
  trr_skip : forall k (P Q : assn), 0 <= k -> (forall w, P w -> Q w) -> TR k P Q;
  trr_seq : forall k1 k2 (P R Q : assn), TR k1 P R -> TR k2 R Q -> TR (k1 + k2) P Q;
  trr_inhP : forall k (P Q : assn), 0 <= k -> (forall w, P w -> exists P' : assn, P' w /\ TR k P' Q) -> TR k P Q;
  trr_run : forall k fuel cuts K S leaves rho (Q : assn),
      0 <= k ->
      sym_run segs fuel cuts S true = Some leaves -> ss_lenient S = false -> implK K ->
      (forall Lf rho', In Lf leaves -> agree_below (ss_next S) rho rho' -> TR k (SP segs K (lf_state Lf) rho') Q) ->
      TR k (SP segs K S rho) Q;
  trr_callP : forall kc k2 (J Jp : jpred) (Cl Pre : sstate) sb R (Posts : list (sstate * jpost)) (Q : assn) rho,
      0 <= k2 ->
      entails_fr Cl Pre sb = Some R ->
      call_checkP Cl Pre sb R (map fst Posts) = true ->
      (forall rho1, TR kc (SPJ segs Jp Pre rho1) (LQP segs (ss_next Pre) rho1 Posts)) ->
      (forall tr ms md, smatch segs rho Cl (tr, mkCfg ms md) -> J rho tr md ->
         Jp (rho_sub (rho_absorb rho R ms) sb) tr md) ->
      (forall L JL tr ms md rhoL tr' ms' md', In (L, JL) Posts ->
         smatch segs rho Cl (tr, mkCfg ms md) -> J rho tr md ->
         agree_vals (ss_next Pre) (rho_sub (rho_absorb rho R ms) sb) rhoL ->
         smatch segs rhoL L (tr', mkCfg ms' md') ->
         JL (rho_sub (rho_absorb rho R ms) sb) rhoL tr' md' ->
         import_okP rho ms R sb Pre L rhoL
         /\ forall rho', call_linkP rho ms R sb Pre Cl L rho' rhoL ->
              TR k2 (SPJ segs (J_ofP JL (rho_sub (rho_absorb rho R ms) sb) rhoL)
                        (import_post sb (ss_next Pre) L (ss_next Cl) R) rho') Q) ->
      TR (kc + k2) (SPJ segs J Cl rho) Q;

  trr_mmap_rw : forall k kf ko (J Jf : jpred) (Jo : word -> jpred) S rho (Q : assn),
      implJ J ->
      instr_at segs (ss_pc S) = Some Ecall ->
      reg_sv S 17 = SLit 222 ->
      (forall tr ms md, smatch_pending segs rho S (tr, mkCfg ms md) -> J rho tr md ->
         ms_gpr ms 1 <> Z_to_bv 64 0
         /\ mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true
         /\ mmap_noreserve_b (ms_gpr ms 3) = false
         /\ Jf rho tr md
         /\ forall a, mmap_place_ok (ms_gpr ms 0) (ms_gpr ms 3) md (ms_gpr ms 1) a ->
              (forall o, In o (ss_objs S) ->
                 ranges_disjoint (obj_range rho o) (bv_unsigned a, bv_unsigned a + mmap_nZ (ms_gpr ms 1)))
              /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + mmap_nZ (ms_gpr ms 1) -> ro_addr segs x = false)
              /\ Jo a (rho_after_zero rho (ss_next S) a a (mmap_n (ms_gpr ms 1))) tr
                      (with_vmmaps (mmap_rw_vm (m_vmmaps md) (ms_gpr ms 1) a) md)) ->
      (RF -> TR kf (SPJ segs Jf (S_ret_lit S enomem_ret) rho) Q) ->
      (GF -> forall a, TR ko (SPJ segs (Jo a) (S_ret_fresh S) (rho_after_zero rho (ss_next S) a a (mmap_n (eval rho (reg_sv S 11))))) Q) ->
      0 <= ko -> mmap_nZ (eval rho (reg_sv S 11)) + ko <= k ->
      mmap_nZ (eval rho (reg_sv S 11)) <= 2 ^ 32 ->
      TR k (SPJ segs J S rho) Q
}.

Lemma trr_ex TR (R : tr_rules TR) : forall k (A : Type) (P : A -> assn) (Q : assn),
  0 <= k -> (forall x, TR k (P x) Q) -> TR k (fun w => exists x, P x w) Q.
Proof using . intros k A P Q Hk H. apply (trr_inhP TR R); [exact Hk|]. intros w [x Hx]. exists (P x). split; [exact Hx | exact (H x)]. Qed.
Lemma trr_inh TR (R : tr_rules TR) : ltac2:(tb__ "0|0|
S14S0S0S17Z0R3A2S1R4R1A1VTR;R6R5R4A3F_;Fw;VTR;R5R4R3A3F_;F_;FQ;FP;Fk;").
Proof using . intros k P Q Hk H. apply (trr_inhP TR R); [exact Hk|]. intros w Hw. exists P. split; [exact Hw | exact (H w Hw)]. Qed.
Lemma trr_disj TR (R : tr_rules TR) : ltac2:(tb__ "0|0|
S14S0S0S0S17Z0R4A2VTR;R5R4R2A3VTR;R6R4R3A3VTR;R7S1S11R7R1A1R6R1A1A2Lw;R4A3F_;F_;F_;FQ;FP2;FP1;Fk;").
Proof using .
  intros k P1 P2 Q Hk H1 H2. apply (trr_inhP TR R); [exact Hk|]. intros w [Hw|Hw]; [exists P1 | exists P2]; split; assumption.
Qed.
Lemma trr_false TR (R : tr_rules TR) : ltac2:(tb__ "0|0|
S14S0S0S17Z0R3A2S1R4R1A1SeF_;Fw;VTR;R5R4R3A3F_;F_;FQ;FP;Fk;").
Proof using . intros k P Q Hk H. apply (trr_skip TR R); [exact Hk|]. intros w Hw. exfalso. exact (H w Hw). Qed.

Lemma trr_seq0 TR (R : tr_rules TR) : ltac2:(tb__ "0|0|
S14S0S0S0VTR;R4R3R2A3VTR;Z0R3R2A3VTR;R6R5R3A3F_;F_;FQ;FQ1;FP;Fk;").
Proof using . intros k P Q1 Q H1 H2. replace k with (k + 0) by lia. exact (trr_seq TR R k 0 P Q1 Q H1 H2). Qed.
End TRR.

Arguments trr_pre {segs Kc RF GF TR} _ {k}.
Arguments trr_post {segs Kc RF GF TR} _ {k}.
Arguments trr_mono {segs Kc RF GF TR} _.
Arguments trr_skip {segs Kc RF GF TR} _.
Arguments trr_seq {segs Kc RF GF TR} _.
Arguments trr_inhP {segs Kc RF GF TR} _.
Arguments trr_run {segs Kc RF GF TR} _.
Arguments trr_callP {segs Kc RF GF TR} _.
Arguments trr_mmap_rw {segs Kc RF GF TR} _.
Arguments trr_ex {segs Kc RF GF TR} _.
Arguments trr_inh {segs Kc RF GF TR} _.
Arguments trr_disj {segs Kc RF GF TR} _.
Arguments trr_false {segs Kc RF GF TR} _.
Arguments trr_seq0 {segs Kc RF GF TR} _.

Section Triple.
Variable segs : list Segment.
Variable Kc : ltac2:(tb__ "0|0|
S5S13A1S12OF_;F_;").
Variable ok : world -> Prop.
Hypothesis HS : ltac2:(tb__ "0|0|
S26Vsegs;Vok;VKc;A3").

Lemma okJ_of (J : jpred) : ltac2:(tb__ "0|0|
S21VKc;VJ;A2ScS23Vsegs;Vok;VJ;A3S25Vsegs;Vok;VJ;A3A2F_;").
Proof using HS.
  intros HJ. destruct HS as (F1 & F2 & _). split.
  - intros rho tr ms md ms' Hj. exact (F1 tr ms md ms' (HJ rho tr md Hj)).
  - intros rho tr ms md x8 Hj. exact (F2 tr ms md x8 (HJ rho tr md Hj)).
Qed.

Theorem tr_rules_triple : ltac2:(tb__ "0|0|
S20Vsegs;VKc;SdSdS14S3Vsegs;Vok;A2L_;A5").
Proof using HS.
  constructor.
  - intros _. exact (triple_pre segs ok).
  - intros _. exact (triple_post segs ok).
  - intros k k' P Q _ H. exact H.
  - intros k P Q _. exact (triple_skip segs ok P Q).
  - intros k1 k2 P R Q. exact (@triple_seq segs ok P R Q).
  - intros k P Q _ H n Hg w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT n Hg w HP').
  - intros k fuel cuts K S leaves rho Q _ Hrun Hlen HK Hc.
    apply (run_tr segs ok fuel cuts S leaves K rho Q Hrun Hlen); [|exact Hc].
    intros tr ms md ms' Hk. exact (proj1 HS tr ms md ms' (HK tr md Hk)).
  - intros kc k2 J Jp Cl Pre sb R Posts Q rho _. exact (call_soundP segs ok J Jp Cl Pre sb R Posts Q rho).
  - intros k kf ko J Jf Jo S rho Q HJ Hi H17 HP Hfail Hok _ _ _.
    destruct (okJ_of J HJ) as [OF OP].
    eapply triple_seq; [apply triple1_triple; exact (triple1_mmap_rwJ segs ok J Jf Jo S rho OF OP Hi H17 HP)|].
    apply triple_disj; [exact (Hfail I)|]. apply triple_ex. exact (Hok I).
Qed.
End Triple.

Section Fair.
Variable segs : list Segment.
Variable Kc : ltac2:(tb__ "0|0|
S5S13A1S12OF_;F_;").

Theorem tr_rules_etriple_any : ltac2:(tb__ "0|0|
S20Vsegs;VKc;SdSdS14S2Vsegs;A1L_;A5").
Proof using .
  constructor.
  - intros _. exact (etriple_pre segs).
  - intros _. exact (etriple_post segs).
  - intros k k' P Q _ H. exact H.
  - intros k P Q _. exact (etriple_skip segs P Q).
  - intros k1 k2 P R Q. exact (@etriple_seq segs P R Q).
  - intros k P Q _ H w Hw. destruct (H w Hw) as (P' & HP' & HT). exact (HT w HP').
  - intros k fuel cuts K S leaves rho Q _ Hrun Hlen _ Hc. exact (erun_tr segs fuel cuts S leaves K rho Q Hrun Hlen Hc).
  - intros kc k2 J Jp Cl Pre sb R Posts Q rho _. exact (call_completeP segs J Jp Cl Pre sb R Posts Q rho).
  - intros k kf ko J Jf Jo S rho Q _ Hi H17 HP Hfail Hok _ _ _.
    eapply etriple_seq.
    + apply (etriple_mmap_rw_anyJ segs J Jf Jo S rho Hi H17).
      intros tr ms md Hsp Hj. destruct (HP tr ms md Hsp Hj) as (A1 & A2 & A3 & A4 & A5).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [intros _; exact A4 | exact A5].
    + intros w [Hw | [a Hw]]; [exact (Hfail I w Hw) | exact (Hok I a w Hw)].
Qed.

Definition tr_rules_etriple := tr_rules_etriple_any.
End Fair.

Section Angelic.
Variable segs : list Segment.
Variable Kc : ltac2:(tb__ "0|0|
S5S13A1S12OF_;F_;").

Definition roomw (X : Z) : assn := ltac2:(tb__ "0|0|
S1S1fS24S4R1A1A1VX;A2Lw;").

Definition TR_ang (k : Z) (P Q : assn) : Prop := ltac2:(tb__ "0|1|
ScS17Z0M0Vk;A2S14S17G0R1A2S2Vsegs;S1ScVP;R1A1S19S18R3Vk;A2R1A2A2Lw;S1ScVQ;R1A1S19R3R1A2A2Lw;A3F_;Fr;A2").

Definition jroom (J : jpred) (X : Z) : jpred := ltac2:(tb__ "0|0|
SbS5S13A1S12ScVJ;R3R2R1A3S1fR1VX;A2A2Lmd;Ltr;Lrho;").
Definition proom (JL : jpost) (X : Z) : jpost := ltac2:(tb__ "0|0|
SbSbS5S13A1S12ScVJL;R4R3R2R1A4S1fR1VX;A2A2Lmd;Ltr;LrhoL;Lrho0;").
Definition posts_room (Posts : list (sstate * jpost)) (X : Z) : list (sstate * jpost) := ltac2:(tb__ "0|1|
S1eS7SaS15A2M0G0G0S8SaS15S6SaS15R1A3S1dS9SaS15R1A3VX;A2A4Lp;VPosts;A4").

Lemma SPJ_room (J : jpred) S rho X w : ltac2:(tb__ "0|0|
S10ScS22Vsegs;VJ;VS;Vrho;Vw;A5S19VX;Vw;A2A2S22Vsegs;S1cVJ;VX;A2VS;Vrho;Vw;A5A2").
Proof using . unfold SPJ, jroom, roomw. tauto. Qed.

Lemma posts_room_fst Posts X : ltac2:(tb__ "0|2|
SfS5SaA1S1eS7SaS15A2M0SaS6SaS15A2M1S1aVPosts;VX;A2A4S1eG0SaG1VPosts;A4A3").
Proof using . unfold posts_room. rewrite map_map. reflexivity. Qed.

Lemma LQP_room n rho Posts X w : ltac2:(tb__ "0|0|
ScS16Vsegs;Vn;Vrho;VPosts;Vw;A5S19VX;Vw;A2A2S16Vsegs;Vn;Vrho;S1aVPosts;VX;A2Vw;A5F_;").
Proof using .
  intros [(L & JL & rho' & Hin & Hag & Hsm & HJ) HR]. exists L, (proom JL X), rho'.
  split; [apply in_map_iff; exists (L, JL); split; [reflexivity | exact Hin]|].
  split; [exact Hag|]. split; [exact Hsm|]. split; [exact HJ | exact HR].
Qed.

Theorem tr_rules_angelic : ltac2:(tb__ "0|0|
S20Vsegs;VKc;SeSdS1bA5").
Proof using .
  constructor.
  -   intros k P P' Q HP [Hk H]. split; [exact Hk|]. intros r Hr.
    eapply etriple_pre; [|exact (H r Hr)]. intros w [A B]. split; [apply HP; exact A | exact B].
  -   intros k P Q Q' HQ [Hk H]. split; [exact Hk|]. intros r Hr.
    eapply etriple_post; [|exact (H r Hr)]. intros w [A B]. split; [apply HQ; exact A | exact B].
  -   intros k k' P Q Hkk [Hk H]. split; [lia|]. intros r Hr.
    eapply etriple_pre; [|exact (H r Hr)]. intros w [A B]. split; [exact A|].
    eapply vm_room_mono; [|exact B]. lia.
  -   intros k P Q Hk HPQ. split; [exact Hk|]. intros r Hr. apply etriple_skip.
    intros w [A B]. split; [apply HPQ; exact A|]. eapply vm_room_mono; [|exact B]. lia.
  -   intros k1 k2 P R Q [Hk1 H1] [Hk2 H2]. split; [lia|]. intros r Hr.
    eapply etriple_seq; [|exact (H2 r Hr)].
    eapply etriple_pre; [|exact (H1 (r + k2) ltac:(lia))]. intros w [A B]. split; [exact A|].
    replace (r + k2 + k1) with (r + (k1 + k2)) by lia. exact B.
  -   intros k P Q Hk H. split; [exact Hk|]. intros r Hr w [Hw HRw].
    destruct (H w Hw) as (P' & HP' & [_ HT]). exact (HT r Hr w (conj HP' HRw)).
  -
    intros k fuel cuts K S leaves rho Q Hk Hrun Hlen _ Hc. split; [exact Hk|]. intros r Hr.
    eapply etriple_pre with (P := SP segs (fun tr md => K tr md /\ vm_room md (r + k)) S rho).
    { intros w [[Hsm HK] HR]. split; [exact Hsm|]. split; [exact HK | exact HR]. }
    apply (erun_tr segs fuel cuts S leaves _ rho _ Hrun Hlen).
    intros Lf rho' Hin Hag. destruct (Hc Lf rho' Hin Hag) as [_ HT].
    eapply etriple_pre; [|exact (HT r Hr)]. intros w [Hsm [HK HR]]. split; [split; [exact Hsm | exact HK] | exact HR].
  -
    intros kc k2 J Jp Cl Pre sb R Posts Q rho Hk2 He Hchk Hsum Hin Hout.
    pose proof (proj1 (Hsum rho)) as Hkc. split; [lia|]. intros r Hr.
    eapply etriple_pre with (P := SPJ segs (jroom J (r + k2 + kc)) Cl rho).
    { intros w [A B]. apply (proj1 (SPJ_room _ _ _ _ _)). split; [exact A|]. replace (r + k2 + kc) with (r + (kc + k2)) by lia. exact B. }
    apply (call_completeP segs (jroom J (r + k2 + kc)) (jroom Jp (r + k2 + kc)) Cl Pre sb R (posts_room Posts (r + k2))
             (fun w => Q w /\ roomw r w) rho He).
    + rewrite posts_room_fst. exact Hchk.
    + intros rho1. destruct (Hsum rho1) as [_ HT].
      eapply etriple_pre; [|eapply etriple_post; [|exact (HT (r + k2) ltac:(lia))]].
      * intros w Hw. exact (proj2 (SPJ_room _ _ _ _ _) Hw).
      * intros w Hw. apply LQP_room. exact Hw.
    + intros tr ms md Hsm [HJ HR]. split; [exact (Hin tr ms md Hsm HJ) | exact HR].
    + intros L JL' tr ms md rhoL tr' ms' md' HinL Hsm [HJ HR] Hag HsmL HJL'.
      apply in_map_iff in HinL as ([L0 JL0] & E & HinL). cbn [fst snd] in E.
      injection E as EL EJ. subst L0. subst JL'. destruct HJL' as [HJL HRL].
      destruct (Hout L JL0 tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag HsmL HJL) as [HI HC].
      split; [exact HI|]. intros rho' Hlink. destruct (HC rho' Hlink) as [_ HT].
      eapply etriple_pre; [|exact (HT r Hr)].
      intros w [HsmW [HJw HRw]]. split; [split; [exact HsmW | exact HJw] | exact HRw].
  -
    intros k kf ko J Jf Jo S rho Q _ Hi H17 HP _ Hok Hko Hk H32. specialize (Hok I).
    pose proof (FreeGap.page_round_up_Z_ge (bv_unsigned (eval rho (reg_sv S 11)))) as Hge.
    pose proof (urange (eval rho (reg_sv S 11))) as Hu.
    assert (Hn0 : 0 <= mmap_nZ (eval rho (reg_sv S 11))) by (unfold mmap_nZ; lia).
    split; [lia|]. intros r Hr.
    set (len := eval rho (reg_sv S 11)) in *.
    eapply etriple_pre with (P := SPJ segs (jroom J (r + k)) S rho).
    { intros w Hw. apply (proj1 (SPJ_room _ _ _ _ _)). exact Hw. }
    eapply etriple_seq.
    + apply (etriple_mmap_rw_okJ segs (jroom J (r + k)) (fun a => jroom (Jo a) (r + ko)) S rho Hi H17).
      intros tr ms md Hsp [HJ HR].
      destruct (pending_args segs rho S tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
      destruct (HP tr ms md Hsp HJ) as (Hlen & Hmod & Hnr & _ & Hall).
      assert (Hpos : 0 < bv_unsigned (ms_gpr ms 1)).
      { pose proof (urange (ms_gpr ms 1)) as U.
        destruct (Z.eq_dec (bv_unsigned (ms_gpr ms 1)) 0) as [E|NE]; [|lia].
        exfalso. apply Hlen. apply bv_eq. rewrite E. reflexivity. }
      rewrite G1 in *.
      destruct (vm_room_grant md (r + k) len HR Hpos H32 ltac:(lia))
        as (a & _ & _ & _ & _ & _ & _ & _ & Hpl & _ & HRo & _).
      split; [exact Hlen|]. split; [exact Hmod|]. split; [exact Hnr|].
      exists a. destruct (Hall a (Hpl _ _ Hnr)) as (Hdisj & Hnro & HJo).
      split; [exact (Hpl _ _ Hnr)|]. split; [exact Hdisj|]. split; [exact Hnro|].
      split; [exact HJo|]. eapply vm_room_mono; [|exact HRo]. lia.
    + apply etriple_ex. intros a. destruct (Hok a) as [_ HT].
      eapply etriple_pre; [|exact (HT r Hr)]. intros w Hw. exact (proj2 (SPJ_room _ _ _ _ _) Hw).
Qed.
End Angelic.
