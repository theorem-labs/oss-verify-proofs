(** The pod loop of a params Struct in the UBSan builder (pod.h:425-433): one turn is rb_ent_contract (ent_build,
    0x13360 -> 0x13c48), then [Cut.S_write] (0x13c48 -> 0x13cac), then the latch 0x13cac-0x13cb4 (k++, k = count?);
    the exit 0x13d94-0x13db0 reloads the property loop's registers and goes to the Struct's close 0x13db4. By
    induction on the pods left, the loop from [CNTH] k reaches [PCLOSE] with the pods [Model.ents_loop] makes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog.RoleBuild Require Import Facts Cut EntCut.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The block's len field, read from the image of a cut. *)
Lemma MBr_len_read : forall sp m rest src pp lo c m1,
  MBr sp m rest src pp lo (pc_image c) m1 -> Z.of_nat (length (pc_buf c)) <= POD_BUF_MAX ->
  ov_read_bytes rsegs m1 (wa (pp + POD_LEN_OFF)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf c))))).
Proof.
  intros sp m rest src pp lo c m1 MB Hb.
  pose proof MB as (_ & HL & _).
  erewrite MBr_read; [ | exact MB | unfold POD_LEN_OFF; lia | unfold POD_LEN_OFF, POD_PROPS in *; lia ].
  unfold pc_image, POD_LEN_OFF. change (Z.to_nat 16384) with (Z.to_nat OFF_LEN).
  rewrite pp_image_slice_len by exact Hb. rewrite le8_lit64. reflexivity.
Qed.

(** The length of an open Struct's buffer stays below the capacity. *)
Lemma pc_buf_open_cap : forall sh ps es, pc_wf sh ps -> Forall ent_wf es -> (length ps <= 2)%nat ->
  (length es <= 32)%nat -> Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) <= 5472.
Proof.
  intros sh ps es (_ & Hv & He & _) Hes Hp Hk.
  assert (Hv' : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hv]; intros kv [_ H]; exact H).
  destruct (pc_buf_len_open sh ps es Hv' He Hes) as [H _]. lia.
Qed.

(** A 32-bit result that fits is its own sign extension (addiw, subw). *)
Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Section CntLoop.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis ENT : rb_ent_contract.
Hypothesis WR : S_write sp gp tp F fc m rest fl src pp lo.

(** The latch 0x13cac: k + 1 < count goes back to the head, k + 1 = count leaves through 0x13d94 to the close. *)
Lemma cnt_latch : forall sh np ps i cnt es k e r ms,
  CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r ms ->
  evt rsegs (fun ms' =>
    (Z.of_nat (S k) < cnt /\ CNTH sp gp tp F fc m rest fl src pp lo sh np ps i cnt (es ++ [e]) (S k) r ms') \/
    (Z.of_nat (S k) = cnt /\ PCLOSE sp gp tp F fc m rest fl src pp lo sh np ps i (es ++ [e]) r ms')) ms.
Proof.
  intros sh np ps i cnt es k e r ms
    (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CV & CP & Hk & Hcnt & Hkc).
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof CV as (CPR & C30 & C38 & C40 & C88 & CA8 & CB0).
  pose proof CPR as (C10 & C18 & C90).
  pose proof CF as (C08 & C20 & C28 & C48 & C50 & C58 & C60 & C68 & C70 & C78 & C80 & C98 & CA0).
  pose proof CP as (Hsuf & Hwf & Hsh & Hnp & Hi & Hinp & Hes).
  assert (Hlen : Z.of_nat (length (pc_buf (PbCut sh ps (Some (es ++ [e]))))) <= 5472).
  { apply pc_buf_open_cap; [exact Hwf | exact Hes | lia | rewrite length_app; cbn [length]; lia]. }
  pose proof (cell8_read m1 _ _ CA8) as RA8.
  unfold CNT_LATCH.
  (* 0x13cac addiw s11,s11,1 *)
  zstep. rewrite (swrap32_id (Z.of_nat k + 1)) by lia.
  (* 0x13cb0 ld a0,0xa8(sp) *)
  zstep.
  (* 0x13cb4 bne s11,a0 *)
  zstep. if_cases E; zify_cond E.
  - (* back to the head 0x13360 *)
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
    apply evt_done. cbv beta. left. split; [lia|].
    do 18 eexists. exists m1. split; [reflexivity|].
    split; [exact MB|]. split; [exact CF|]. split; [exact CV|]. split; [exact CP|].
    split; [rewrite length_app; cbn [length]; lia|]. split; lia.
  - (* 0x13cb8 j 0x13d94 *)
    zstep.
    pose proof (MBr_len_read sp m rest src pp lo _ m1 MB ltac:(unfold POD_BUF_MAX; lia)) as RL.
    pose proof (cell8_read m1 _ _ C20) as R20.
    pose proof (cell8_read m1 _ _ C18) as R18.
    pose proof (cell8_read m1 _ _ C40) as R40.
    pose proof (cell8_read m1 _ _ C38) as R38.
    pose proof (cell8_read m1 _ _ C30) as R30.
    (* 0x13d94 ld a0,0(s7) .. 0x13db0 ld a4,0x30(sp) *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. cbv beta. right. split; [lia|].
    do 13 eexists. exists m1. split; [reflexivity|].
    split; [exact MB|]. split; [exact CF|]. split; [exact CPR|]. split; [exact C88|]. split; [exact CB0|].
    split; [exact CP | rewrite length_app; cbn [length]; lia].
Qed.

Local Ltac dj := cbn [disjoint_from]; repeat (split; [lia|]); exact I.

(** The window rb_ent_contract may change: the callees' stack below sp and [sp + 0xb8, sp + 0x1b8). *)
Definition WE : list (Z * Z) :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0xb8, bv_unsigned sp + FRAME_LOCALS)].

Lemma cell8_keep : forall m1 m2 o v, munch WE m1 m2 -> 0 <= o -> o + 8 <= 0xb8 ->
  cell8 m1 (bv_unsigned sp + o) v -> cell8 m2 (bv_unsigned sp + o) v.
Proof.
  intros m1 m2 o v MU Ho Ho8 C. unfold cell8 in *.
  apply (bytes_at_transport rsegs WE m1 m2 _ _ C MU). rewrite length_le8. unfold WE, MID_STACK, FRAME_LOCALS. dj.
Qed.

Lemma CFIX_keep : forall m1 m2, munch WE m1 m2 -> CFIX sp pp m1 -> CFIX sp pp m2.
Proof.
  intros m1 m2 MU (C08 & C20 & C28 & C48 & C50 & C58 & C60 & C68 & C70 & C78 & C80 & C98 & CA0).
  repeat split; (eapply cell8_keep; [exact MU | lia | lia | eassumption]).
Qed.

Lemma CVAR_keep : forall m1 m2 sh np ps i cnt, munch WE m1 m2 ->
  CVAR sp fl pp sh np ps i cnt m1 -> CVAR sp fl pp sh np ps i cnt m2.
Proof.
  intros m1 m2 sh np ps i cnt MU ((C10 & C18 & C90) & C30 & C38 & C40 & C88 & CA8 & CB0).
  repeat split; (eapply cell8_keep; [exact MU | lia | lia | eassumption]).
Qed.

(** The input left after a read is still a suffix of the builder's input. *)
Lemma suffix_rest : forall r r', suffix rest r -> is_rest r' r -> suffix rest r'.
Proof.
  intros r r' [j [Hj ->]] [k' ->]. rewrite skipn_skipn.
  destruct (Nat.le_gt_cases (k' + j) (length rest)) as [H|H].
  - exists (k' + j)%nat. split; [exact H | reflexivity].
  - exists (length rest). split; [lia|]. rewrite !skipn_all2 by lia. reflexivity.
Qed.

(** One turn: ent_build (rb_ent_contract), then the write and the record copy ([S_write]). *)
Lemma cnt_turn : forall sh np ps i cnt es k r ms,
  CNTH sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k r ms ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k
               (fst (ent_build r)) (snd (ent_build r))) ms.
Proof.
  intros sh np ps i cnt es k r ms
    (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & t3 & t4 & t5 & t6 & m1 & -> &
     MB & CF & CV & CP & Hk & Hcnt & Hkc).
  pose proof HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  pose proof CP as (Hsuf & Hwf & Hsh & Hnp & Hi & Hinp & Hes).
  pose proof MB as (HI & HL & HW & HR & MU & WM & MI & HS & HT).
  pose proof CF as (C08 & C20 & C28 & C48 & C50 & C58 & C60 & C68 & C70 & C78 & C80 & C98 & CA0).
  destruct Hsuf as [j [Hj Er]].
  assert (Hcur : cur rest src r = src + Z.of_nat j) by (unfold cur; rewrite Er, length_skipn; lia).
  assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Er, length_skipn; lia).
  assert (HBR : bytes_at rsegs m1 (cur rest src r) r)
    by (rewrite Hcur, Er; eapply MBr_rest; eassumption).
  unfold CNT_HEAD.
  eapply evt_cut.
  { eapply ENT with (r := r) (src := cur rest src r) (pp := pp) (lo := lo);
      try reflexivity; try eassumption; lia. }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s4' & s6' &
              t3' & t4' & t5' & t6' & m' & -> & HE & MU' & WM' & MI' & ST').
  assert (Ecur : cur rest src r + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build r)))
                 = cur rest src (snd (ent_build r))) by (unfold cur; lia).
  rewrite Ecur.
  eapply WR; [exact HOK | exact HPPA | exact HSPA |].
  assert (SUB : sub_fp WE [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS)]).
  { unfold sub_fp, WE, FRAME_LOCALS, MID_STACK. intros x Hx. cbn [outside] in *. lia. }
  assert (MB' : MBr sp m rest src pp lo (pc_image (PbCut sh ps (Some es))) m').
  { eapply MBr_call; [exact HOK | exact MB | exact MU' | exact WM' | exact MI' | exact ST' | exact SUB | |];
      unfold WE, MID_STACK, FRAME_LOCALS, POD_PROPS in *; dj. }
  do 18 eexists. exists m'. split; [reflexivity|].
  split; [exact MB'|]. split; [exact (CFIX_keep m1 m' MU' CF)|].
  split; [exact (CVAR_keep m1 m' sh np ps i cnt MU' CV)|]. split; [exact HE|].
  split; [apply ent_build_wf|].
  split; [|split; [exact Hk | split; lia]].
  split; [apply (suffix_rest r); [exists j; split; [exact Hj | exact Er] | apply ent_build_rest]|].
  exact (conj Hwf (conj Hsh (conj Hnp (conj Hi (conj Hinp Hes))))).
Qed.

(** The loop: from pod k of count, the n = count - k turns left make the pods [ents_loop n r] (the stop rule of
    pod.h:428 never fires, Model.pc_stop_never). *)
Lemma cnt_loop : forall n sh np ps i cnt es k r ms, (k + n)%nat = Z.to_nat cnt ->
  CNTH sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k r ms ->
  evt rsegs (PCLOSE sp gp tp F fc m rest fl src pp lo sh np ps i (es ++ fst (ents_loop n r))
               (snd (ents_loop n r))) ms.
Proof.
  induction n as [|n IH]; intros sh np ps i cnt es k r ms Hn HC.
  - exfalso. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & _ & _ & Hk & Hcnt & Hkc). lia.
  - pose proof HC as HC0.
    destruct HC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & _ & _ & _ & _ & Hk & Hcnt & Hkc).
    cbn [ents_loop]. destruct (ent_build r) as [e r1] eqn:Ee.
    destruct (ents_loop n r1) as [es2 r2] eqn:El. cbn [fst snd].
    eapply evt_cut; [exact (cnt_turn sh np ps i cnt es k r ms HC)|].
    rewrite Ee. cbn [fst snd]. intros ms1 HL.
    eapply evt_cut; [exact (cnt_latch sh np ps i cnt es k e r1 ms1 HL)|].
    intros ms2 [[Hlt HC2] | [Heq HP]].
    + specialize (IH sh np ps i cnt (es ++ [e]) (S k) r1 ms2 ltac:(lia) HC2).
      rewrite El in IH. cbn [fst snd] in IH. rewrite <- app_assoc in IH. exact IH.
    + assert (n = 0%nat) by lia. subst n. cbn [ents_loop] in El. injection El as <- <-.
      apply evt_done. exact HP.
Qed.

End CntLoop.
