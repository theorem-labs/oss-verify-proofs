(** headamp_build_contract of the UBSan image (lib/U/Prog/LLVMFuzzerTestOneInput_c.v, [0x13090, 0x140e0)): the
    inlined pod builder of pod.h:382-449. The walk is chained from its pieces: the header and the preheader
    (HeadBuild/Pre.v), the property loop (HeadBuild/PropLoop.v) over one property (HeadBuild/Iter.v: the key and
    flags of HeadBuild/Key.v, the Int-7 value, or the params Struct of HeadBuild/Struct.v with its pod loop
    HeadBuild/CntLoop.v, the pod write HeadBuild/Write.v and the close HeadBuild/Close.v), and the end with the
    top size word and the corruption (HeadBuild/Post.v). One pod of the pod loop is HeadBuild/EntTop.v's
    rb_ent_holds. It refines Pod/Model.pod_build and Pod/Layout.pp_bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import
  SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c strlen_c pod_write_ent_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import
  Facts Cut UTac CntLoop PropLoop Key Struct Iter EntCut EntTop Pre Post Write Close Shape7 Int7.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The buffer at a cut with no open Struct is as long as the object the record encodes: both are the size word
    and the body (Model.pc_buf, Model.pod_encode). *)
Lemma len_pc_buf_encode : forall sh ps,
  Z.of_nat (length (pc_buf (PbCut sh ps None))) = Z.of_nat (length (pod_encode (PodRec sh ps None))).
Proof.
  intros sh ps. unfold pc_buf, pod_encode, open_bytes. cbn [pc_shape pc_props pc_open p_shape p_props].
  rewrite app_nil_r, !length_app, !length_le32. reflexivity.
Qed.

(** The record pod_build makes, named by the reads the walk follows. *)
Lemma pod_build_rec : forall inp sh np r2 ps r3,
  fst (fuzz_u8 inp) mod 8 = sh -> fst (fuzz_u8 (snd (fuzz_u8 inp))) mod 4 = np ->
  snd (fuzz_u8 (snd (fuzz_u8 inp))) = r2 -> props_loop sh (Z.to_nat np) r2 = (ps, r3) ->
  fst (pod_build inp) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r3)).
Proof.
  intros inp sh np r2 ps r3 Esh Enp Er2 Hpl. subst sh np r2.
  unfold pod_build. destruct (fuzz_u8 inp) as [s r1]. cbn [fst snd] in *.
  destruct (fuzz_u8 r1) as [n0 r2]. cbn [fst snd] in *.
  rewrite Hpl. rewrite len_pc_buf_encode.
  destruct (corr_step (Z.of_nat (length (pod_encode (PodRec (s mod 8) ps None)))) r3) as [co r4].
  reflexivity.
Qed.

Theorem headamp_build_holds :
  memset_contract -> memcpy_contract -> strlen_contract -> pod_write_ent_contract -> headamp_build_contract.
Proof.
  intros MSET MCPY STRL PWE.
  pose proof (rb_ent_holds MSET MCPY STRL) as ENT.
  pose proof (shape7_holds MSET PWE) as SH7. pose proof (int7_holds MSET PWE) as INT7.
  unfold headamp_build_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  intros F fc m rest junk nl cap src pp lo.
  intros Ha0 Hpp0 Hppa Hs6 Hs2 Hs3 Hcap Hnl Hcell Hs1 Hs0 Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hstk Hmid Hspa Hsrom
    Hrelro Hmi.
  (* the bounds the pieces share *)
  assert (PB : 0 <= pp /\ pp + POD_PROPS <= 2^64).
  { pose proof (rw_cells_bound rsegs m pp [CB (Z.to_nat POD_PROPS) junk] Hblk) as (A & B).
    cbn [cells_size csize] in B. rewrite Nat.add_0_r, Z2Nat.id in B by (unfold POD_PROPS; lia).
    split; [exact A | exact B]. }
  assert (SR : 0 <= lo /\ bv_unsigned sp + FRAME_LOCALS <= 2^64)
    by (destruct Hstk as (A & B & _); split; [exact A | exact B]).
  assert (HOK : BOK sp rest src pp lo).
  { unfold BOK. destruct PB as (P1 & P2). destruct SR as (S1 & S2).
    split; [exact Hsrc0|]. split; [exact Hlo1|]. split; [exact Hlo2|]. split; [exact Hdj|].
    split; [exact Hmid|]. split; [exact S1|]. split; [exact S2|].
    split; [unfold POD_PROPS in *; lia|]. split; [exact Hrom | exact Hsrom]. }
  (* the property loop's step *)
  assert (ITER : S_iter sp gp tp F fc m rest (1 - nl) src pp lo cap).
  { apply (iter_ok sp gp tp F fc m rest (1 - nl) src pp lo cap HOK Hppa Hspa ENT
             (write_holds PWE MCPY sp gp tp F fc m rest (1 - nl) src pp lo cap)
             (close_holds sp gp tp F fc m rest (1 - nl) src pp lo cap)
             (SH7 sp gp tp F fc m rest (1 - nl) src pp lo cap HOK Hppa Hspa)
             (INT7 sp gp tp F fc m rest (1 - nl) src pp lo cap HOK Hppa Hspa)). }
  (* the end: POSTH of a record, then its QBrec is the contract's post *)
  assert (FIN : forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
            fst (pod_build rest) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)) ->
            POSTH sp gp tp F fc m rest (1 - nl) src pp lo cap sh ps r ms ->
            evt rsegs
              (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s9' s10' s11'
                                  t3' t4' t5' t6' : word) (m' : word -> option byte),
                 ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (head_len rest)) a1' a2' a3' a4' a5'
                               a6' a7' s2' (Z_to_bv 64 (head_len rest)) s4' s5' s6'
                               (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9' s10' s11' t3' t4' t5' t6')
                          F (Z_to_bv 64 HEAD_MALLOC2) fc None m' (seg_rom rsegs) /\
                 bytes_at rsegs m' pp (pp_bytes (head_rec rest)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 (1 - nl))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 pp)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
                 munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
                 wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS)) ms).
  { intros sh ps r ms Erec HQ.
    pose proof (post_holds sp gp tp F fc m rest (1 - nl) src pp lo cap HOK sh ps r ms HQ) as HP.
    unfold head_len, head_rec. rewrite Erec.
    eapply evt_mono; [exact HP|].
    intros ms' (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s4' & s5' & s6' &
                s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & Ems & HB & C10 & C70 & C68 & C78 & C08 & MU & WM &
                MI & ST).
    exists ra', t0', t1', t2', s0', s1', a1', a2', a3', a4', a5', a6', a7', s2', s4', s5', s6', s9', s10', s11', t3',
      t4', t5', t6', m'.
    split; [exact Ems|]. split; [exact HB|]. split; [exact C08|]. split; [exact C10|]. split; [exact C68|].
    split; [exact C70|]. split; [exact C78|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST]. }
  (* the first piece *)
  eapply evt_cut; [exact (pre_holds MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                            s9 s10 s11 t3 t4 t5 t6 F fc m rest junk (1 - nl) src pp lo cap Ha0 Hpp0 Hppa Hs6 Hs2 Hs3
                            ltac:(lia) Hcell Hs1 Hs0 Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hstk Hmid Hspa Hsrom Hrelro
                            Hmi)|].
  intros ms1 [[Hz HQ] | [Hnz HP]].
  - (* no property *)
    apply (FIN (fst (fuzz_u8 rest) mod 8) [] (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms1); [|exact HQ].
    eapply pod_build_rec; try reflexivity. rewrite Hz. cbn [Z.to_nat props_loop]. reflexivity.
  - (* the property loop *)
    eapply evt_cut.
    { eapply (prop_loop sp gp tp F fc m rest (1 - nl) src pp lo cap ITER
                (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)) (fst (fuzz_u8 rest) mod 8)
                (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4) [] (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms1);
        [cbn [length Nat.add]; reflexivity | exact HP]. }
    cbn [app]. intros ms2 HQ2.
    destruct (props_loop (fst (fuzz_u8 rest) mod 8) (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4))
                (snd (fuzz_u8 (snd (fuzz_u8 rest))))) as [ps r3] eqn:Epl.
    cbn [fst snd] in HQ2.
    apply (FIN (fst (fuzz_u8 rest) mod 8) ps r3 ms2); [|exact HQ2].
    eapply pod_build_rec; try reflexivity. exact Epl.
Qed.
