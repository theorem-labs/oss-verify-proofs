(** The property loop of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, pod.h:398) and the
    builder as a whole: [build_of_pieces] composes the first piece's statement [Cut.S_pre] with the statements of one
    property [Cut.S_prop] and of the end [Cut.S_post] into rate_build_contract, and [rate_build_holds] discharges
    them with the proved pieces [Pre.pre_holds], [Prop.prop_holds] (one property, with [EntTop.rb_ent_holds] for
    the ent_build turn and [Write.write_holds] for the inlined pod_write_ent) and [Post.post_holds]. Ported from
    reac-pw/fuzz_role's Prog/RoleBuild/Loop.v at rate's registers,
    frame cells and pcs.

    [latch_ok] walks the latch 0x140e4 (`addiw a1,a1,1; bne a1,t2`) back to the head 0x13334, or through
    0x140ec-0x1410c (`mv t1,s6; ld s4,0(a6)`, the header reloads `ld s9,8(sp); ld s10,0x20(sp); ld s6,0x18(sp);
    ld s7,0x10(sp); ld s2,0x30(sp); ld s11,0(sp)`, `j 0x14114`) to the end cut 0x14114; [loop_ok] is the loop by
    induction on the properties left, the record after i properties being [Model.props_loop] of i. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import Facts Cut EntCut EntTop Write Post
  PropKit PropPath.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild.Pre.
Require OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild.Prop.
Import ListNotations.
Open Scope Z_scope.

(** ** The model *)
(** The buffer at the end cut is as long as the object [pod_encode] writes: both are the top size word and the
    body. *)
Lemma len_encode : forall sh ps,
  length (pod_encode (PodRec sh ps None)) = length (pc_buf (PbCut sh ps None)).
Proof.
  intros sh ps. unfold pod_encode, pc_buf, open_bytes. cbn [p_shape p_props pc_shape pc_props pc_open].
  rewrite !length_app, !length_le32. cbn [length]. lia.
Qed.

(** One more property at the end of the loop (Model.props_loop_S_end). *)
Lemma props_loop_snoc : forall sh n r2 ps r, props_loop sh n r2 = (ps, r) ->
  props_loop sh (S n) r2 = (ps ++ [fst (prop_step sh r)], snd (prop_step sh r)).
Proof.
  intros sh n r2 ps r H. rewrite props_loop_S_end, H. destruct (prop_step sh r). reflexivity.
Qed.

(** The record pod_build makes (Model.pod_build), once its shape, its property count and its properties are named. *)
Lemma pod_build_rec : forall rest ps r3,
  props_loop (fst (fuzz_u8 rest) mod 8) (Z.to_nat (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4))
    (snd (fuzz_u8 (snd (fuzz_u8 rest)))) = (ps, r3) ->
  fst (pod_build rest)
  = PodRec (fst (fuzz_u8 rest) mod 8) ps
      (fst (corr_step (Z.of_nat (length (pc_buf (PbCut (fst (fuzz_u8 rest) mod 8) ps None)))) r3)).
Proof.
  intros rest ps r3. unfold pod_build.
  destruct (fuzz_u8 rest) as [s r1]. cbn [fst snd].
  destruct (fuzz_u8 r1) as [n r2]. cbn [fst snd].
  intros H. rewrite H. rewrite len_encode.
  destruct (corr_step (Z.of_nat (length (pc_buf (PbCut (s mod 8) ps None)))) r3). reflexivity.
Qed.

(** ** The latch and the loop *)
Section Loop.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis SP : S_prop sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.

(** pp->len, as the end of the loop reloads it. *)
Lemma len_read : forall sh ps m1, pc_wf sh ps ->
  MBr sp m rest src pp lo (pc_image (PbCut sh ps None)) m1 ->
  ov_read_bytes rsegs m1 (wa (pp + 16384)) 8
  = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None)))))).
Proof.
  intros sh ps m1 Hwf MB.
  destruct (wf_facts sh ps Hwf) as (HL1 & _ & _ & _).
  pose proof (MBr_bounds sp m rest src pp lo _ m1 MB) as (_ & _ & HLB).
  rewrite (MBr_read sp m rest src pp lo _ m1 16384 8 MB) by (unfold POD_PROPS in HLB; lia).
  rewrite pc_image_of.
  change (Z.to_nat 16384) with (Z.to_nat OFF_LEN).
  rewrite pp_image_slice_len by (unfold POD_BUF_MAX; lia).
  rewrite le8_lit64. reflexivity.
Qed.

(** A header cell, as the latch's exit reloads it. *)
Lemma hdr_read : forall m1 (a v : Z), cell8 m1 a v -> ov_read_bytes rsegs m1 (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m1 a v H. exact (cell8_read m1 a v H). Qed.

(** 0x140e4 -> 0x13334, or 0x140e4 -> 0x14114 after the last property. *)
Lemma latch_ok : forall sh np i ps r ms, 0 < np <= 3 -> (S i <= Z.to_nat np)%nat ->
  PROPL sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np i ps r ms ->
  evt rsegs (fun ms' =>
    (Z.of_nat (S i) = np /\ POSTH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh ps r ms') \/
    (Z.of_nat (S i) < np /\ PROPH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np ps r ms')) ms.
Proof.
  intros sh np i ps r ms Hnp Hi HL.
  destruct HL as (ra & t1 & a0 & a2 & a3 & a4 & s2 & s7 & s8 & s9 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & HD & C48 & C40 & Hs & Hw & Hlen).
  subst ms.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  unfold PROP_LATCH, POD_LEN_OFF, S8V, S10V.
  (* 0x140e4 addiw a1,a1,1 *)
  step. rewrite (addiw1_lit (Z.of_nat i)) by lia.
  (* 0x140e8 bne a1,t2 *)
  step.
  destruct (Z.eq_dec (Z.of_nat i + 1) np) as [E | E].
  - (* the last property: 0x140ec *)
    brF.
    pose proof CF as (F38 & F50 & F68 & F70 & F80 & F90 & F98 & FB0).
    pose proof (HDR_cells sp m fl mask buflen b3 b4 b5 b6 m1 HD) as (H0 & H8 & H10 & H18 & H20 & H28 & H30).
    (* 0x140ec mv t1,s6 *)
    step.
    (* 0x140f0 ld s4,0(a6) *)
    pose proof (len_read sh ps m1 Hw MB) as HRL.
    step. clear HRL.
    (* 0x140f4 ld s9,8(sp) *)
    pose proof (hdr_read m1 _ _ H8) as HR. step. clear HR.
    (* 0x140f8 ld s10,0x20(sp) *)
    pose proof (hdr_read m1 _ _ H20) as HR. step. clear HR.
    (* 0x140fc ld s6,0x18(sp) *)
    pose proof (hdr_read m1 _ _ H18) as HR. step. clear HR.
    (* 0x14100 ld s7,0x10(sp) *)
    pose proof (hdr_read m1 _ _ H10) as HR. step. clear HR.
    (* 0x14104 ld s2,0x30(sp) *)
    pose proof (hdr_read m1 _ _ H30) as HR. step. clear HR.
    (* 0x14108 ld s11,0(sp) *)
    assert (HR : ov_read_bytes rsegs m1 sp 8 = Some (le8 (Z_to_bv 64 b5))).
    { rewrite <- (Z_to_bv_lit_self sp) at 1. exact (cell8_read m1 (bv_unsigned sp) b5 H0). }
    step. clear HR.
    (* 0x1410c j 0x14114 *)
    step.
    apply evt_done. left. split; [lia|].
    unfold POSTH. do 18 eexists.
    split; [reflexivity|].
    split; [exact MB|]. split; [exact H28|]. split; [exact F70|]. split; [exact F80|]. split; [exact FB0|].
    split; [exact Hs | exact Hw].
  - (* back to the head 0x13334 *)
    brT.
    apply evt_done. right. split; [lia|].
    replace (Z.of_nat i + 1) with (Z.of_nat (length ps)) by lia.
    unfold PROPH. do 14 eexists.
    split; [reflexivity|].
    split; [exact MB|]. split; [exact CF|]. split; [exact HD|]. split; [exact C48|]. split; [exact C40|].
    split; [exact Hs | exact Hw].
Qed.

(** The property loop (pod.h:398), by induction on the properties left: from the head after the record
    [props_loop sh i r2] to 0x14114 after all np. *)
Lemma loop_ok : forall sh np r2, 0 < np <= 3 ->
  forall j ps r ms, (length ps + S j)%nat = Z.to_nat np ->
  props_loop sh (length ps) r2 = (ps, r) ->
  PROPH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh np ps r ms ->
  evt rsegs (POSTH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh
               (fst (props_loop sh (Z.to_nat np) r2)) (snd (props_loop sh (Z.to_nat np) r2))) ms.
Proof.
  intros sh np r2 Hnp. induction j as [|j IH]; intros ps r ms Hj Hpl HP.
  - eapply evt_cut; [apply (SP HOK sh np ps r ms HP); lia |]. intros ms1 HL.
    eapply evt_cut;
      [apply (latch_ok sh np (length ps) (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r)) ms1 Hnp);
       [lia | exact HL] |].
    intros ms2 [[E HQ] | [E HQ]]; [| exfalso; lia].
    apply evt_done.
    replace (Z.to_nat np) with (S (length ps)) by lia.
    rewrite (props_loop_snoc sh (length ps) r2 ps r Hpl). cbn [fst snd]. exact HQ.
  - eapply evt_cut; [apply (SP HOK sh np ps r ms HP); lia |]. intros ms1 HL.
    eapply evt_cut;
      [apply (latch_ok sh np (length ps) (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r)) ms1 Hnp);
       [lia | exact HL] |].
    intros ms2 [[E HQ] | [E HQ]]; [exfalso; lia |].
    apply (IH (ps ++ [fst (prop_step sh r)]) (snd (prop_step sh r)) ms2).
    + rewrite length_app. cbn [length]. lia.
    + rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
      exact (props_loop_snoc sh (length ps) r2 ps r Hpl).
    + exact HQ.
Qed.

End Loop.

(** ** The builder *)
(** The bounds the pieces share, from rate_build_contract's premises. *)
Lemma bok_of : forall (sp : word) m (rest junk : list byte) (src pp lo : Z),
  pp <> 0 -> 0 < src ->
  rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
  (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
  (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
  src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
  stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp ->
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
  BOK sp rest src pp lo.
Proof.
  intros sp m rest junk src pp lo Hpp Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hsrom.
  pose proof (rw_cells_bound rsegs m pp [CB (Z.to_nat POD_PROPS) junk] Hblk) as (P1 & P2).
  destruct Hst as (L0 & S2 & _).
  unfold BOK. split; [exact Hsrc|]. split; [exact Hlo1|]. split; [exact Hlo2|]. split; [exact Hdj|].
  split; [exact Hmid|]. split; [exact L0|]. split; [exact S2|]. split; [lia|].
  split; [exact Hrom | exact Hsrom].
Qed.

(** rate_build_contract from the statements of the three pieces: the first piece, one property, the end. *)
Theorem build_of_pieces : Cut.S_pre ->
  (forall sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo,
     S_prop sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo) ->
  (forall sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo,
     S_post sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo) ->
  LLVMFuzzerTestOneInput_c.rate_build_contract.
Proof.
  intros PRE PROP POST. unfold rate_build_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo
         Ha0 Hpp0 Hppa Hs5 Hs0 Hs6 Hs9 Hs10 Hs7 H30 Hs11 Hs4 Hfl Hmask Hbl Hb3 Hb4 Hb5 Hb6 Hs3 Hs1
         Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hspa Hsrom Hrelro Hmi.
  pose proof (bok_of sp m rest junk src pp lo Hpp0 Hsrc0 Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hsrom) as HOK.
  pose proof (PROP sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo) as SP.
  pose proof (POST sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo HOK) as SQ.
  eapply evt_cut.
  { exact (PRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo
               Ha0 Hpp0 Hppa Hs5 Hs0 Hs6 Hs9 Hs10 Hs7 H30 Hs11 Hs4 Hfl Hmask Hbl Hb3 Hb4 Hb5 Hb6 Hs3 Hs1
               Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hspa Hsrom Hrelro Hmi). }
  intros ms HQ.
  set (sh := fst (fuzz_u8 rest) mod 8) in *.
  set (np := fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4) in *.
  set (r2 := snd (fuzz_u8 (snd (fuzz_u8 rest)))) in *.
  assert (Hnp : 0 <= np < 4) by (subst np; apply Z.mod_pos_bound; lia).
  (* the end cut, and the record it holds *)
  assert (HEND : forall ps r3 ms1, props_loop sh (Z.to_nat np) r2 = (ps, r3) ->
            POSTH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh ps r3 ms1 ->
            evt rsegs
              (fun ms' => exists (ra' t0' t1' t2' s0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s8' t3' t4' t5' t6' : word)
                                 (m' : word -> option byte),
                 ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' (Z_to_bv 64 pp) (Z_to_bv 64 (rate_len rest))
                               a1' a2' a3' a4' a5' a6' a7'
                               (Z_to_bv 64 (b4 * 256)) s3' (Z_to_bv 64 (rate_len rest)) s5' (Z_to_bv 64 fl)
                               (Z_to_bv 64 b3) s8' (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5)
                               t3' t4' t5' t6')
                          F (Z_to_bv 64 RATE_MALLOC2) fc None m' (seg_rom rsegs) /\
                 bytes_at rsegs m' pp (pp_bytes (fst (pod_build rest))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b6 * 256))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0x80) (le8 (Z_to_bv 64 pp)) /\
                 bytes_at rsegs m' (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
                 munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)] m m' /\
                 wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS))
              ms1).
  { intros ps r3 ms1 Hpl HP.
    pose proof (pod_build_rec rest ps r3 Hpl) as Erec. fold sh in Erec.
    eapply evt_mono; [exact (SQ sh ps r3 ms1 HP) |].
    intros ms' (ra' & t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s5' & s8'
                & t3' & t4' & t5' & t6' & m' & Ems & HB & C28 & C70 & C80 & CB0 & MU & WM & MI & ST).
    cbv beta. unfold rate_len. rewrite Erec.
    exists ra', t0', t1', t2', s0', a1', a2', a3', a4', a5', a6', a7', s3', s5', s8', t3', t4', t5', t6', m'.
    split; [exact Ems|]. split; [exact HB|]. split; [exact C28|]. split; [exact C70|]. split; [exact C80|].
    split; [exact CB0|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST]. }
  destruct HQ as [[E0 HP] | [E0 HP]].
  - (* no property *)
    apply (HEND [] r2 ms); [rewrite E0; reflexivity | exact HP].
  - (* the property loop *)
    eapply evt_cut.
    { apply (loop_ok sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo HOK SP Hspa sh np r2 ltac:(lia)
               (Z.to_nat np - 1)%nat [] r2 ms); [cbn [length]; lia | reflexivity | exact HP]. }
    intros ms1 HP1.
    eapply (HEND _ _ ms1); [apply surjective_pairing | exact HP1].
Qed.

(** rate_build_contract from memset's, memcpy's and strlen's contracts. *)
Theorem rate_build_holds :
  memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  LLVMFuzzerTestOneInput_c.rate_build_contract.
Proof.
  intros MSET MCPY STRL. apply build_of_pieces.
  - exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild.Pre.pre_holds MSET).
  - intros sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo.
    exact (OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild.Prop.prop_holds
             sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo MSET MCPY STRL (rb_ent_holds MSET MCPY STRL)
             (write_holds sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo MSET MCPY)).
  - exact post_holds.
Qed.
