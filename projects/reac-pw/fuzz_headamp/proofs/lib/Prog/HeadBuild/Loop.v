(** The property loop of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, pod.h:398) and the
    builder as a whole: [build_of_pre] composes the first piece's statement [Cut.S_pre] with the proved pieces
    [Prop.prop_holds] (one property), [Write.write_holds] (the inlined pod_write_ent), [EntTop.rb_ent_holds]
    (ent_build) and [Post.post_holds] (the end) into headamp_build_contract.

    [latch_ok] walks the latch 0x13f64 (`addiw a5,a5,1; bne a5,a4`) back to the head 0x13208, or through
    0x13f6c (`mv t0,s4; ld s4,0(s2); ld s7,8(sp); ld s6,0(sp); ld s8,0x38(sp)`: the buffer length, null, cap and
    &n_ent back in registers) to 0x13f80; [loop_ok] is the loop by induction on the properties left, the record after
    i properties being [Model.props_loop] of i. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  memset_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import Facts Cut EntCut EntTop Write Post
  PropKit PropPath.
Require OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild.Prop.
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
Variables (rest : list byte) (nl cap src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis SP : S_prop sp gp tp F fc m rest nl cap src pp lo.
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

(** 0x13f64 -> 0x13208, or 0x13f64 -> 0x13f80 after the last property. *)
Lemma latch_ok : forall sh np i ps r ms, 0 < np <= 3 -> (S i <= Z.to_nat np)%nat ->
  PROPL sp gp tp F fc m rest nl cap src pp lo sh np i ps r ms ->
  evt rsegs (fun ms' => (Z.of_nat (S i) = np /\ POSTH sp gp tp F fc m rest nl cap src pp lo sh ps r ms') \/
                        (Z.of_nat (S i) < np /\ PROPH sp gp tp F fc m rest nl cap src pp lo sh np ps r ms')) ms.
Proof.
  intros sh np i ps r ms Hnp Hi HL.
  destruct HL as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & s6 & s8 & t3 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & CH & Hs & Hw & Hlen).
  subst ms.
  pose proof (krng _ _ _ _ _ HOK) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
  unfold PROP_LATCH, POD_LEN_OFF, S8V, S10V.
  (* 0x13f64 addiw a5,a5,1 *)
  step. rewrite (addiw1_lit (Z.of_nat i)) by lia.
  (* 0x13f68 bne a5,a4 *)
  step.
  destruct (Z.eq_dec (Z.of_nat i + 1) np) as [E | E].
  - (* the last property: 0x13f6c *)
    brF.
    pose proof CF as (F10 & F18 & F30 & F38 & F50 & F58 & F70 & F78).
    pose proof CH as (C0 & C8 & C20 & C40).
    (* 0x13f6c mv t0,s4 *)
    step.
    (* 0x13f70 ld s4,0(s2) *)
    pose proof (len_read sh ps m1 Hw MB) as HRL.
    step. clear HRL.
    (* 0x13f74 ld s7,8(sp) *)
    pose proof (cell8_read m1 _ _ C8) as HR8.
    step. clear HR8.
    (* 0x13f78 ld s6,0(sp) *)
    assert (HR0 : ov_read_bytes rsegs m1 sp 8 = Some (le8 (Z_to_bv 64 cap))).
    { rewrite <- (Z_to_bv_lit_self sp) at 1. exact (cell8_read m1 (bv_unsigned sp) cap C0). }
    step. clear HR0.
    (* 0x13f7c ld s8,0x38(sp) *)
    pose proof (cell8_read m1 _ _ F38) as HR38.
    step. clear HR38.
    apply evt_done. left. split; [lia|].
    unfold POSTH. do 21 eexists.
    split; [reflexivity|].
    split; [exact MB|]. split; [exact F50|]. split; [exact F58|].
    split; [exact Hs | exact Hw].
  - (* back to the head 0x13208 *)
    brT.
    apply evt_done. right. split; [lia|].
    replace (Z.of_nat i + 1) with (Z.of_nat (length ps)) by lia.
    unfold PROPH. do 15 eexists.
    split; [reflexivity|].
    split; [exact MB|]. split; [exact CF|]. split; [exact CH|].
    split; [exact Hs | exact Hw].
Qed.

(** The property loop (pod.h:398), by induction on the properties left: from the head after the record
    [props_loop sh i r2] to 0x13f80 after all np. *)
Lemma loop_ok : forall sh np r2, 0 < np <= 3 ->
  forall j ps r ms, (length ps + S j)%nat = Z.to_nat np ->
  props_loop sh (length ps) r2 = (ps, r) ->
  PROPH sp gp tp F fc m rest nl cap src pp lo sh np ps r ms ->
  evt rsegs (POSTH sp gp tp F fc m rest nl cap src pp lo sh
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
(** The bounds the pieces share, from headamp_build_contract's premises. *)
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

(** headamp_build_contract from its first piece's statement and the three leaf contracts. *)
Theorem build_of_pre : Cut.S_pre ->
  memset_c.memset_contract -> memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  LLVMFuzzerTestOneInput_c.headamp_build_contract.
Proof.
  intros PRE MSET MCPY STRL. unfold headamp_build_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rest junk nl cap src pp lo
         Ha0 Hpp0 Hppa Hs3 Hs2 Hs7 Hnl Hs6 Hcap Hs1 Hs0 Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hspa Hsrom
         Hrelro Hmi.
  pose proof (bok_of sp m rest junk src pp lo Hpp0 Hsrc0 Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hsrom) as HOK.
  pose proof (OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild.Prop.prop_holds
                sp gp tp F fc m rest nl cap src pp lo MSET MCPY STRL (rb_ent_holds MSET MCPY STRL)
                (write_holds sp gp tp F fc m rest nl cap src pp lo MSET MCPY)) as SP.
  pose proof (post_holds sp gp tp F fc m rest nl cap src pp lo HOK) as SQ.
  eapply evt_cut.
  { exact (PRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               F fc m rest junk nl cap src pp lo
               Ha0 Hpp0 Hppa Hs3 Hs2 Hs7 Hnl Hs6 Hcap Hs1 Hs0 Hsrc0 Hsrc Hblk Hrom Hdj Hlo1 Hlo2 Hst Hmid Hspa
               Hsrom Hrelro Hmi). }
  intros ms HQ.
  set (sh := fst (fuzz_u8 rest) mod 8) in *.
  set (np := fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4) in *.
  set (r2 := snd (fuzz_u8 (snd (fuzz_u8 rest)))) in *.
  assert (Hnp : 0 <= np < 4) by (subst np; apply Z.mod_pos_bound; lia).
  (* the end cut, and the record it holds *)
  lazymatch goal with
  | |- evt _ ?Q _ =>
    assert (HEND : forall ps r3 ms1, props_loop sh (Z.to_nat np) r2 = (ps, r3) ->
              POSTH sp gp tp F fc m rest nl cap src pp lo sh ps r3 ms1 -> evt rsegs Q ms1)
  end.
  { intros ps r3 ms1 Hpl HP.
    pose proof (pod_build_rec rest ps r3 Hpl) as Erec. fold sh in Erec.
    eapply evt_mono; [exact (SQ sh ps r3 ms1 HP) |].
    intros ms' (ra' & t0' & t1' & t2' & s0' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3'
                & s9' & s10' & s11' & t3' & t4' & t5' & t6' & m' & Ems & HB & C50 & C58 & MU & WM & MI & ST).
    cbv beta. unfold head_len, head_rec. rewrite Erec.
    exists ra', t0', t1', t2', s0', s1', a1', a2', a3', a4', a5', a6', a7', s2', s3', s9', s10', s11',
           t3', t4', t5', t6', m'.
    split; [exact Ems|]. split; [exact HB|]. split; [exact C50|]. split; [exact C58|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST]. }
  destruct HQ as [[E0 HP] | [E0 HP]].
  - (* no property *)
    apply (HEND [] r2 ms); [rewrite E0; reflexivity | exact HP].
  - (* the property loop *)
    eapply evt_cut.
    { apply (loop_ok sp gp tp F fc m rest nl cap src pp lo HOK SP Hspa sh np r2 ltac:(lia)
               (Z.to_nat np - 1)%nat [] r2 ms); [cbn [length]; lia | reflexivity | exact HP]. }
    intros ms1 HP1.
    eapply (HEND _ _ ms1); [apply surjective_pairing | exact HP1].
Qed.
