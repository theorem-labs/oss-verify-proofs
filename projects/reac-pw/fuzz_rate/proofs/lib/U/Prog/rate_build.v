(** rate_build_contract of the UBSan image (lib/U/Prog/LLVMFuzzerTestOneInput_c.v, [0x13110, 0x14208)): the
    inlined pod builder of pod.h:382-449. The walk is chained from its pieces: the header and the preheader
    (RateBuild/Pre.v), the property loop (RateBuild/PropLoop.v) over one property (RateBuild/Iter.v: the key and
    flags of RateBuild/Key.v, the Int-7 value of RateBuild/Int7.v, or the params Struct of RateBuild/Struct.v with
    its pod loop RateBuild/CntLoop.v, the pod turn of RateBuild/EntTop.v, the pod write RateBuild/Write.v and the
    close RateBuild/Close.v; the shape-7 object's pod of RateBuild/Shape7.v), and the end with the top size word
    and the corruption (RateBuild/Post.v). It refines Pod/Model.pod_build and Pod/Layout.pp_bytes. The form is
    reac-pw/fuzz_role's U/Prog/role_build.v with rate's cuts
    (RateBuild/Cut.v) and the six header values handed through (Cut.hdr). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import
  SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c strlen_c pod_write_ent_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import
  Facts Cut UTac CntLoop PropLoop Key Struct Iter EntCut EntTop Pre Post Write Close Shape7 Int7.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
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

(** The builder from the pod turn's contract (EntCut.rb_ent_contract) and the leaves. *)
Theorem rate_build_holds_ent :
  memset_contract -> memcpy_contract -> strlen_contract -> pod_write_ent_contract -> rb_ent_contract ->
  rate_build_contract.
Proof.
  intros MSET MCPY STRL PWE ENT.
  pose proof (shape7_holds MSET PWE) as SH7. pose proof (int7_holds MSET PWE) as INT7.
  unfold rate_build_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  intros F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo.
  intros Ha0 Hpp0 Hppa Hs7 Hs1 Hs2 Hs5 Hs4 C30 C28 C20 C18 Hfl Hmk Hbl Hb3 Hb4 Hb5 Hb6 Hs3 Hs0
    Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hstk Hmid Hspa Hsrom Hrelro Hmi.
  set (H := Hdr mask buflen b3 b4 b5 b6).
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
  assert (ITER : S_iter sp gp tp F fc m rest fl src pp lo H).
  { exact (iter_ok sp gp tp F fc m rest fl src pp lo H HOK Hppa Hspa ENT
             (write_holds PWE MCPY sp gp tp F fc m rest fl src pp lo H)
             (close_holds sp gp tp F fc m rest fl src pp lo H)
             (SH7 sp gp tp F fc m rest fl src pp lo H HOK Hppa Hspa)
             (INT7 sp gp tp F fc m rest fl src pp lo H HOK Hppa Hspa)). }
  (* the end: POSTH of a record, then its QBrec is the contract's post *)
  assert (FIN : forall (sh : Z) (ps : list (Z * pval)) (r : list byte) (ms : machine_state),
            fst (pod_build rest) = PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)) ->
            POSTH sp gp tp F fc m rest fl src pp lo H sh ps r ms ->
            evt rsegs
              (fun ms' => exists (ra' t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s9' s10' t3' t4' t5'
                                  t6' : word) (m' : word -> option byte),
                 ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 (rate_len rest)) a1' a2' a3' a4' a5' a6' a7'
                               (Z_to_bv 64 fl) s3' (Z_to_bv 64 (rate_len rest)) s5' s6' s7' (Z_to_bv 64 pp)
                               s9' s10' (Z_to_bv 64 (pp + POD_LEN_OFF)) t3' t4' t5' t6')
                          F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
                 bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 b3)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 mask)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x38) (le8 (Z_to_bv 64 fl)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0xd8) (le8 (Z_to_bv 64 pp)) /\
                 munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
                 wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS)) ms).
  { intros sh ps r ms Erec HQ.
    eapply evt_mono; [exact (post_holds sp gp tp F fc m rest fl src pp lo H HOK sh ps r ms HQ)|].
    intros ms' (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s5' & s6' &
                s7' & s9' & s10' & t3' & t4' & t5' & t6' & m' & E & HB & (D08 & D10 & D18 & D20 & D28 & D30) &
                D38 & D98 & DD8 & MU & WM & MI & ST).
    unfold rate_len. rewrite Erec.
    exists ra', t0', t1', t2', s0', s1', a1', a2', a3', a4', a5', a6', a7', s3', s5', s6', s7', s9', s10',
      t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact HB|].
    split; [exact D08|]. split; [exact D10|]. split; [exact D18|]. split; [exact D20|].
    split; [exact D28|]. split; [exact D30|]. split; [exact D38|]. split; [exact D98|]. split; [exact DD8|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST]. }
  (* the first piece *)
  eapply evt_cut; [exact (pre_holds MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                            s9 s10 s11 t3 t4 t5 t6 F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo
                            Ha0 Hpp0 Hppa Hs7 Hs1 Hs2 Hs5 Hs4 C30 C28 C20 C18 Hfl Hmk Hbl Hb3 Hb4 Hb5 Hb6 Hs3 Hs0
                            Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hstk Hmid Hspa Hsrom Hrelro Hmi)|].
  intros ms1 [[Hz HQ] | [Hnz HP]].
  - (* no property *)
    apply (FIN (fst (fuzz_u8 rest) mod 8) [] (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms1); [|exact HQ].
    eapply pod_build_rec; try reflexivity. rewrite Hz. cbn [Z.to_nat props_loop]. reflexivity.
  - (* the property loop *)
    eapply evt_cut.
    { eapply (prop_loop sp gp tp F fc m rest fl src pp lo H ITER
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

(** The builder from the leaves alone: the pod turn by EntTop.rb_ent_holds. *)
Theorem rate_build_holds :
  memset_contract -> memcpy_contract -> strlen_contract -> pod_write_ent_contract -> rate_build_contract.
Proof.
  intros MSET MCPY STRL PWE.
  exact (rate_build_holds_ent MSET MCPY STRL PWE (rb_ent_holds MSET MCPY STRL)).
Qed.
