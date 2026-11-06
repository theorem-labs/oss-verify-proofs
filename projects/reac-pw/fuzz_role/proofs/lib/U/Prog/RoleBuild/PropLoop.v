(** The property loop of the UBSan builder (pod.h:398-439): one property is [S_iter] (0x13160 -> 0x13e00, proved
    in Iter.v), then the latch 0x13e00-0x13e04 (i++, i = nprops?) back to the head, or 0x13e08 (s2 = len) to the
    end 0x13e0c. By induction on the properties left, the loop from [PROPH] reaches [POSTH] with the properties
    [Model.props_loop] makes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import Facts Cut CntLoop.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

Section PropLoop.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.

(** One property, 0x13160 -> 0x13e00: [Model.prop_step]. *)
Definition S_iter : Prop :=
  forall (sh np : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
    PROPH sp gp tp F fc m rest fl src pp lo sh np ps r ms ->
    evt rsegs (PROPL sp gp tp F fc m rest fl src pp lo sh np (length ps) (ps ++ [fst (prop_step sh r)])
                 (snd (prop_step sh r))) ms.

Hypothesis ITER : S_iter.

(** The latch 0x13e00: i + 1 < nprops goes back to the head, i + 1 = nprops leaves to the end. *)
Lemma prop_latch : forall sh np i ps r ms,
  PROPL sp gp tp F fc m rest fl src pp lo sh np i ps r ms ->
  evt rsegs (fun ms' =>
    ((length ps < Z.to_nat np)%nat /\ PROPH sp gp tp F fc m rest fl src pp lo sh np ps r ms') \/
    (length ps = Z.to_nat np /\ POSTH sp gp tp F fc m rest fl src pp lo sh ps r ms')) ms.
Proof.
  intros sh np i ps r ms
    (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CP & Hsuf & Hwf & Hnp & Hi & Hle).
  pose proof CF as (C08 & C20 & C28 & C48 & C50 & C58 & C60 & C68 & C70 & C78 & C80 & C98 & CA0).
  pose proof CP as (C10 & C18 & C90).
  pose proof Hwf as (Hsh & Hv & He & H3).
  assert (Hlen : Z.of_nat (length (pc_buf (PbCut sh ps None))) <= POD_BUF_MAX).
  { assert (Hv' : Forall (fun kv => pval_wf (snd kv)) ps)
      by (eapply Forall_impl; [|exact Hv]; intros kv [_ H]; exact H).
    destruct (pc_buf_len_none sh ps Hv' He) as [H _]. unfold POD_BUF_MAX. lia. }
  unfold PROP_LATCH.
  (* 0x13e00 addiw a7,a7,1 *)
  zstep. rewrite (swrap32_id (Z.of_nat i + 1)) by lia.
  replace (Z.of_nat i + 1) with (Z.of_nat (length ps)) by lia.
  (* 0x13e04 bne a7,s11 *)
  zstep. if_cases E; zify_cond E.
  - apply evt_done. cbv beta. left. split; [lia|].
    do 15 eexists. exists m1. split; [reflexivity|].
    split; [exact MB|]. split; [exact CF|]. split; [exact CP|].
    split; [exact Hsuf|]. split; [exact Hwf|]. split; [exact Hnp | lia].
  - pose proof (MBr_len_read sp m rest src pp lo _ m1 MB Hlen) as RL.
    (* 0x13e08 ld s2,0(s7) *)
    zstep.
    apply evt_done. cbv beta. right. split; [lia|].
    do 23 eexists. exists m1. split; [reflexivity|].
    split; [exact MB|]. split; [exact C10|]. split; [exact C20|]. split; [exact C68|]. split; [exact C70|].
    split; [exact Hsuf | exact Hwf].
Qed.

(** The loop: from property |ps| of nprops, the n = nprops - |ps| properties left are [props_loop n r]. *)
Lemma prop_loop : forall n sh np ps r ms, (length ps + n)%nat = Z.to_nat np ->
  PROPH sp gp tp F fc m rest fl src pp lo sh np ps r ms ->
  evt rsegs (POSTH sp gp tp F fc m rest fl src pp lo sh (ps ++ fst (props_loop sh n r))
               (snd (props_loop sh n r))) ms.
Proof.
  induction n as [|n IH]; intros sh np ps r ms Hn HP.
  - exfalso. destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & _ & _ & _ & Hlt). lia.
  - cbn [props_loop]. destruct (prop_step sh r) as [kv r1] eqn:Ek.
    destruct (props_loop sh n r1) as [ps2 r2] eqn:El. cbn [fst snd].
    eapply evt_cut; [exact (ITER sh np ps r ms HP)|].
    rewrite Ek. cbn [fst snd]. intros ms1 HL.
    eapply evt_cut; [exact (prop_latch sh np (length ps) (ps ++ [kv]) r1 ms1 HL)|].
    intros ms2 [[Hlt HP2] | [Heq HQ]].
    + specialize (IH sh np (ps ++ [kv]) r1 ms2 ltac:(rewrite length_app; cbn [length]; lia) HP2).
      rewrite El in IH. cbn [fst snd] in IH. rewrite <- app_assoc in IH. exact IH.
    + rewrite length_app in Heq. cbn [length] in Heq.
      assert (n = 0%nat) by lia. subst n. cbn [props_loop] in El. injection El as <- <-.
      apply evt_done. exact HQ.
Qed.

End PropLoop.
