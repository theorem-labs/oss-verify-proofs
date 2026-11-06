(** The builder's first piece, 0x13044 -> 0x13208 (or 0x13f80 when the object has no property): the NULL test of
    the first block, memset(pp, 0, sizeof *pp) (pod.h:384), the shape and nprops reads (pod.h:385-386, three paths
    by how many input bytes are left; nprops goes to the frame cell sp + 0x20), the object header (pod.h:388-396;
    the shape test goes to the frame cell sp + 0x40) and the property loop's preheader, which leaves the loop's
    constants in registers and frame cells and the harness's null and cap values in the cells sp + 8 and sp.

    After the header the block holds [Layout.pc_image] of the empty cut [PbCut shape [] None]: buf is the object's
    size word (still 0) and its header, len is 8 (a Struct) or 16 (an Object), is_props is the header's, and every
    other byte is memset's zero. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv memset_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** Two literal words are the same when their values agree modulo 2^64. *)
Lemma lit_mod : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

(** The multiplier of `v / 10` the preheader builds with a shift (0x131d8, 0x131f4). *)
Lemma mult10_fold : Z_to_bv 64 79228162510574988779661033472 = Z_to_bv 64 MULT10.
Proof. apply lit_mod. vm_compute. reflexivity. Qed.

(** The callees' stack bound, as a number. *)
Lemma mid_stack_528 : MID_STACK = 528.
Proof. reflexivity. Qed.

(** A 32-bit store of a literal word writes the field [le32] holds. *)
Lemma le4_lit32 : forall x, le4 (Z_to_bv 64 x) = le32 x.
Proof.
  intros x. unfold le4, le32. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_mod. cbn. lia.
Qed.

(** The header of an object that is not a Struct (pod.h:389-394). *)
Lemma hdr_other : forall sh, sh <> 7 ->
  hdr_bytes sh = le32 POD_OBJECT ++ le32 (if sh =? 6 then POD_OBJECT_PROPINFO else POD_OBJECT_PROPS)
                 ++ le32 POD_PARAM_PROPS.
Proof. intros sh H. unfold hdr_bytes. replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H). reflexivity. Qed.

Lemma hdr_struct : hdr_bytes 7 = le32 POD_STRUCT.
Proof. reflexivity. Qed.

(** The two images the header leaves, as one overwrite of the memset image each. *)
Lemma pc_buf_empty : forall sh, pc_buf (PbCut sh [] None) = le32 0 ++ hdr_bytes sh.
Proof.
  intros sh. unfold pc_buf, body_bytes, open_bytes. cbn [pc_shape pc_props pc_open flat_map].
  rewrite !app_nil_r. reflexivity.
Qed.

(** The block's image at the empty cut: the size word (still 0) and the header, is_props as the header says. *)
Lemma pc_image_empty : forall sh, pc_image (PbCut sh [] None)
  = pp_image (le32 0 ++ hdr_bytes sh) (negb (sh =? 6) && negb (sh =? 7)) false false [] false.
Proof. intros sh. unfold pc_image. rewrite pc_buf_empty. reflexivity. Qed.

(** The three input shapes the header reads tell apart (no byte, one byte, two or more). *)
Lemma list_cases3 : forall (l : list byte), l = [] \/ (exists b0, l = [b0]) \/ (exists b0 b1 r2, l = b0 :: b1 :: r2).
Proof. intros [|b0 [|b1 r2]]; eauto 7. Qed.

(** The shape the code computes from the first input byte (`andi a0,a0,7`). *)
Lemma shape_val : forall b0 : byte, Z.land (bv_unsigned (zxb b0)) 7 = bv_unsigned b0 mod 8.
Proof.
  intros b0. pose proof (byte_range b0). unfold zxb. rewrite unsigned_lit by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(** nprops as the code computes it from the second input byte (`andi a1,a1,3`). *)
Lemma np_val : forall b1 : byte, Z.land (bv_unsigned (zxb b1)) 3 = bv_unsigned b1 mod 4.
Proof.
  intros b1. pose proof (byte_range b1). unfold zxb. rewrite unsigned_lit by lia.
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma shape_cases : forall sh, 0 <= sh < 8 ->
  sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7.
Proof. intros sh H. lia. Qed.

(** is_props and the Object type word as the code computes them (`snez`, `seqz`, pod.h:393-395). *)
Lemma obj_isp : forall sh, 0 <= sh < 8 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (sh + -6)) = Z_to_bv 64 (Z.b2z (negb (sh =? 6))).
Proof.
  intros sh H. destruct (shape_cases sh H) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    vm_compute; reflexivity.
Qed.

Lemma obj_type : forall sh, 0 <= sh < 8 ->
  Z_to_bv 64 (262146 - bv_unsigned (v_sltiu (Z_to_bv 64 (sh + -6)) 1))
  = Z_to_bv 64 (if sh =? 6 then POD_OBJECT_PROPINFO else POD_OBJECT_PROPS).
Proof.
  intros sh H. destruct (shape_cases sh H) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    vm_compute; reflexivity.
Qed.

(** The buffer after the object's size word and its first type word (pod.h:389-392). *)
Definition buf8 (ty : Z) : list byte := le32 0 ++ le32 ty ++ zeros 8.

Section Pre.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest junk : list byte) (nl cap src pp lo : Z).

Hypothesis HPP0 : pp <> 0.
Hypothesis HPPA : pp mod 16 = 0.
Hypothesis HNL : 0 <= nl <= 1.
Hypothesis HCAP : 0 <= cap <= 9.
Hypothesis HSRC0 : 0 < src.
Hypothesis HSRC : bytes_at rsegs m src rest.
Hypothesis HBLK : rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk].
Hypothesis HROM : forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None.
Hypothesis HDJ : src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src.
Hypothesis HLO1 : src + Z.of_nat (length rest) <= lo.
Hypothesis HLO2 : pp + POD_PROPS <= lo.
Hypothesis HST : stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS).
Hypothesis HMID : lo + MID_STACK <= bv_unsigned sp.
Hypothesis HSPA : bv_unsigned sp mod 16 = 0.
Hypothesis HSROM : forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Hypothesis HRELRO : forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis HMI : mem_inv rsegs m.
Hypothesis MSET : memset_contract.

(** The block's bounds, from its cells. *)
Lemma pp_range : 0 <= pp /\ pp + POD_PROPS <= 2^64.
Proof.
  pose proof (rw_cells_bound rsegs m pp [CB (Z.to_nat POD_PROPS) junk] HBLK) as (A & B).
  cbn [cells_size csize] in B. rewrite Nat.add_0_r in B.
  rewrite Z2Nat.id in B by (unfold POD_PROPS; lia). split; [exact A | exact B].
Qed.

Lemma sp_range : 0 <= bv_unsigned sp /\ bv_unsigned sp + FRAME_LOCALS <= 2^64.
Proof. destruct HST as (A & B & _). pose proof (bv_unsigned_in_range 64 sp). split; [lia | exact B]. Qed.

Lemma lo_range : 0 <= lo.
Proof. destruct HST as (A & _). exact A. Qed.

Lemma HOK : BOK sp rest src pp lo.
Proof.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L1.
  unfold BOK. split; [exact HSRC0|]. split; [exact HLO1|]. split; [exact HLO2|]. split; [exact HDJ|].
  split; [exact HMID|]. split; [exact L1|]. split; [exact S2|]. split; [unfold POD_PROPS in *; lia|].
  split; [exact HROM | exact HSROM].
Qed.

(** The entry memory, as the walk carries it. *)
Lemma MB0 : MBr sp m rest src pp lo junk m.
Proof.
  assert (HW : wr_at rsegs m pp POD_PROPS).
  { pose proof (proj2 HBLK) as HW. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
    rewrite Z2Nat.id in HW by (unfold POD_PROPS; lia). exact HW. }
  assert (Hl : Z.of_nat (length junk) = POD_PROPS).
  { pose proof (cells_at_wf rsegs m pp _ (proj1 HBLK)) as Hwf. cbn [cells_wf cell_wf] in Hwf.
    destruct Hwf as [Hj _]. rewrite Hj. apply Z2Nat.id. unfold POD_PROPS. lia. }
  split; [exact (rw_cells_CB_bytes m pp _ junk HBLK)|]. split; [exact Hl|]. split; [exact HW|].
  split; [exact HSRC|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI|].
  split; [exact HST | exact HRELRO].
Qed.

(** The target of this piece: the property loop's head, or the end when the object has no property. *)
Definition PreQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  PREQ sp gp tp F fc m rest nl cap src pp lo sh np r.

(** Carry the frame cells across a store that does not touch them. *)
Ltac keep_cells :=
  repeat match goal with
  | H : bytes_at rsegs ?mm ?A ?bs |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w ?x) _) =>
      apply (bytes_at_write_other_w mm w x A bs) in H;
      [ | rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?unsigned_lit by lia; lia
        | rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?unsigned_lit by lia; lia ]
  end.

(** An 8-byte store into the frame cell at sp + OFF. *)
Ltac sd8 OFF :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- _ =>
      let HSok := fresh "HSok" in
      assert (HSok : store_ok rsegs mm (Z_to_bv 64 (bv_unsigned sp + OFF)) 8 = true)
        by (refine (MBr_stk_ok A1 A2 A3 A4 A5 A6 HOK Ib mm (bv_unsigned sp + OFF) 8 MB _ _);
            unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia);
      step; rewrite ?store_bytes_8'; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
          let MB2 := fresh "MB" in
          let C := fresh "C" in
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 Ib
                          (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + OFF)) bs))
            by (refine (MBr_stk_store A1 A2 A3 A4 A5 A6 HOK Ib mm (bv_unsigned sp + OFF) bs MB _ _ _);
                rewrite ?length_le8; unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia);
          assert (C : bytes_at rsegs (write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + OFF)) bs)
                        (bv_unsigned sp + OFF) bs)
            by (apply bytes_at_write_same; rewrite ?length_le8;
                unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia);
          clear MB HSok; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (Z_to_bv 64 (bv_unsigned sp + OFF)) bs) in *; clearbody mn
      end
  end.

(** The store at sp itself, whose address the semantics keeps as sp. *)
Ltac sd8sp :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- _ =>
      let HSok := fresh "HSok" in
      assert (HSok : store_ok rsegs mm sp 8 = true)
        by (refine (MBr_stk_ok_w A1 A2 A3 A4 A5 A6 HOK Ib mm sp (bv_unsigned sp) 8 MB _ _ _);
            [ symmetry; apply Z_to_bv_lit_self
            | unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia
            | unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia ]);
      step; rewrite ?store_bytes_8'; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
          let MB2 := fresh "MB" in
          let C := fresh "C" in
          let H := fresh "Hw" in
          assert (H : MBr A1 A2 A3 A4 A5 A6 Ib (write_to_mem mm sp bs) /\
                      bytes_at rsegs (write_to_mem mm sp bs) (bv_unsigned sp) bs /\
                      store_ok rsegs mm sp (length bs) = true)
            by (refine (MBr_stk_store_w A1 A2 A3 A4 A5 A6 HOK Ib mm sp (bv_unsigned sp) bs MB _ _ _ _);
                [ symmetry; apply Z_to_bv_lit_self
                | unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia
                | unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia
                | rewrite ?length_le8; unfold FRAME_LOCALS; rewrite ?mid_stack_528; lia ]);
          destruct H as (MB2 & C & _); clear MB HSok; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm sp bs) in *; clearbody mn
      end
  end.

(** A byte store into the block's buffer at pp + OFF, the buffer's bytes being the first K of the image. *)
Ltac st_pp OFF N :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- _ =>
      let HSok := fresh "HSok" in
      assert (HSok : store_ok rsegs mm (wa (A5 + OFF)) N = true)
        by (refine (MBr_pp_ok A1 A2 A3 A4 A5 A6 Ib mm OFF N MB _ _); cbn [Z.of_nat]; unfold POD_PROPS; lia);
      step; rewrite ?store_bytes_1', ?store_bytes_4', ?store_bytes_8'; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?w ?bs) _) =>
          let MB2 := fresh "MB" in
          let H := fresh "Hp" in
          assert (H : MBr A1 A2 A3 A4 A5 A6 (overwrite Ib (Z.to_nat OFF) bs) (write_to_mem mm w bs) /\
                      store_ok rsegs mm w (length bs) = true)
            by (refine (MBr_pp_store_w A1 A2 A3 A4 A5 A6 HOK Ib mm w OFF bs MB _ _ _);
                [ unfold wa; first [reflexivity | f_equal; lia]
                | lia
                | rewrite ?length_le1, ?length_le4, ?length_le8;
                  let HLb := fresh "HLb" in
                  pose proof (MBr_bounds A1 A2 A3 A4 A5 A6 Ib mm MB) as (_ & _ & HLb);
                  unfold POD_PROPS in HLb; lia ]);
          destruct H as (MB2 & _); clear MB HSok; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm w bs) in *; clearbody mn
      end
  end.

(** The constants every walk below unfolds before its first store. *)
Ltac pre_nums :=
  unfold POD_PROPS, POD_LEN_OFF, POD_NENT_OFF, FRAME_LOCALS in *; rewrite ?mid_stack_528 in *.

(** The property loop's preheader, 0x13184 -> 0x13208 (or 0x13f80 when nprops = 0): pp + n_ent and pp into frame
    cells, the nprops test (pod.h:398), then cap and null into the cells sp and sp + 8 and the loop's constants into
    registers and frame cells. *)
Lemma pre_tail : forall (sh np ln : Z) (sh7 : bool) (r : list byte) (m1 : word -> option byte)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  sh7 = (sh =? 7) -> ln = Z.of_nat (length (pc_buf (PbCut sh [] None))) ->
  MBr sp m rest src pp lo (pc_image (PbCut sh [] None)) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 np)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x40) (le8 (Z_to_bv 64 (Z.b2z sh7))) ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length r))) t1 t2 (Z_to_bv 64 POD_NENT_OFF) s1
             a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 ln)
             (Z_to_bv 64 pp) (Z_to_bv 64 cap) (Z_to_bv 64 nl) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13184) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np ln sh7 r m1 ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
         Hsh Hnp Hsuf Hsh7 Hln MB C50 C20 C40. subst sh7 ln.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L0.
  pre_nums.
  assert (Hwf : pc_wf sh []).
  { unfold pc_wf. split; [lia|]. split; [constructor|]. split; [constructor | cbn; lia]. }
  (* 0x13184 add s8,s5,s0 *)
  step.
  (* 0x13188 sd s5,0x58(sp) *)
  sd8 0x58.
  (* 0x1318c ld a0,0x20(sp); 0x13190 beqz a0 *)
  pose proof (cell8_read _ _ _ C20) as HR20. step. clear HR20.
  step. if_cases E; zify_cond E.
  - (* no property: 0x13f80 *)
    apply evt_done. unfold PreQ, PREQ. left. split; [exact E|].
    unfold POSTH. do 21 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact Hsuf | exact Hwf].
  - (* 0x13194 .. 0x13204: pp + n_ent, cap and null into the frame, the loop's constants *)
    sd8 0x38. sd8sp. sd8 0x8.
    do 16 step.
    sd8 0x10. step. sd8 0x18. step. sd8 0x30. step.
    pose proof (cell8_read _ _ _ C20) as HR20. step. clear HR20.
    sd8 0x78. sd8 0x70. step.
    rewrite mult10_fold.
    apply evt_done. unfold PreQ, PREQ. right. split; [exact E|].
    unfold PROPH. do 15 eexists. split; [reflexivity|].
    split; [eassumption|].
    split; [unfold CFIX; repeat (split; [eassumption|]); eassumption|].
    split; [unfold CHAR; repeat (split; [eassumption|]); eassumption|].
    split; [exact Hsuf | exact Hwf].
Qed.

(** 0x13148 -> 0x13184: the rest of an Object header (pod.h:393-396), for a shape that is not a Struct; the shape
    test's cell gets 0. *)
Lemma hdr_obj : forall (sh np : Z) (r : list byte) (m1 : word -> option byte)
    (ra t1 t2 s1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  0 <= sh < 8 -> sh <> 7 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo (pp_at (buf8 POD_OBJECT) 8 false false false [] false) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 np)) ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length r))) t1 t2 (Z_to_bv 64 POD_NENT_OFF) s1
             (Z_to_bv 64 (Z.b2z (negb (sh =? 6))))
             (Z_to_bv 64 (if sh =? 6 then POD_OBJECT_PROPINFO else POD_OBJECT_PROPS))
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (cur rest src r)) s4
             (Z_to_bv 64 pp) (Z_to_bv 64 cap) (Z_to_bv 64 nl) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13148) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r m1 ra t1 t2 s1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 Hsh H7 Hnp Hsuf MB C50 C20.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L0.
  pre_nums.
  assert (H7b : (sh =? 7) = false) by (apply Z.eqb_neq; exact H7).
  (* 0x13148 sd zero,0x40(sp) *)
  sd8 0x40.
  (* 0x1314c srli a2,a1,0x10; srli a3,a1,8 *)
  do 2 step.
  (* 0x13154 sb zero,0xe(s5); 0x13158 sb zero,0xf(s5) *)
  st_pp 14 1%nat. st_pp 15 1%nat.
  (* 0x1315c addi s4,zero,0x10; 0x13160 sd s4,0(s2): pp->len = 16 *)
  step. st_pp 16384 8%nat.
  (* 0x13164 sw a0,8(s2): pp->is_props *)
  st_pp 16392 4%nat.
  (* 0x13168 sb a1,8(s5); 0x1316c sb a3,9(s5) *)
  st_pp 8 1%nat. st_pp 9 1%nat.
  (* 0x13170 addi a0,zero,2 *)
  step.
  (* 0x13174 sb a2,0xa(s5) .. 0x13180 sb zero,0xd(s5) *)
  st_pp 10 1%nat. st_pp 11 1%nat. st_pp 12 1%nat. st_pp 13 1%nat.
  (* the image is the empty cut's *)
  lazymatch type of MB with MBr _ _ _ _ _ _ ?I _ =>
    assert (EI : I = pc_image (PbCut sh [] None)) end.
  { rewrite pc_image_empty, (hdr_other sh H7), H7b.
    destruct (sh =? 6); vm_compute; reflexivity. }
  rewrite EI in MB. clear EI.
  eapply (pre_tail sh np 16 false r);
    [exact Hsh | exact Hnp | exact Hsuf | symmetry; exact H7b | | exact MB | exact C50 | exact C20 | eassumption].
  rewrite pc_buf_empty, (hdr_other sh H7). reflexivity.
Qed.

(** 0x130ec -> 0x13184: the header of a Struct object (shape 7, pod.h:389-391); the shape test's cell gets 1. *)
Lemma hdr_struct_ok : forall (np : Z) (r : list byte) (m1 : word -> option byte)
    (ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo (pp_image [] false false false [] false) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 np)) ->
  evt rsegs (PreQ 7 np r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length r))) t1 t2 (Z_to_bv 64 POD_NENT_OFF) s1
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 (cur rest src r)) s4
             (Z_to_bv 64 pp) (Z_to_bv 64 cap) (Z_to_bv 64 nl) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130ec) fc None m1 (seg_rom rsegs)).
Proof.
  intros np r m1 ra t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 Hnp Hsuf MB C50 C20.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L0.
  pre_nums.
  (* 0x130ec sb zero,7(s5); addi a0,zero,0xe; addi s4,zero,8; sd s4,0(s2) *)
  st_pp 7 1%nat. step. step. st_pp 16384 8%nat.
  (* 0x130fc sb a0,4(s5); sb zero,5(s5); sb zero,6(s5) *)
  st_pp 4 1%nat. st_pp 5 1%nat. st_pp 6 1%nat.
  (* 0x13108 addi a0,zero,1; 0x1310c sd a0,0x40(sp); 0x13110 j 0x13184 *)
  step. sd8 0x40. step.
  lazymatch type of MB with MBr _ _ _ _ _ _ ?I _ =>
    assert (EI : I = pc_image (PbCut 7 [] None)) end.
  { rewrite pc_image_empty. vm_compute. reflexivity. }
  rewrite EI in MB. clear EI.
  eapply (pre_tail 7 np 8 true r);
    [lia | exact Hnp | exact Hsuf | reflexivity | reflexivity | exact MB | exact C50 | exact C20 | eassumption].
Qed.

(** 0x130e0: the shape test of pod.h:389, then the Struct header or the first half of an Object header. *)
Lemma shape_ok : forall (sh np : Z) (r : list byte) (m1 : word -> option byte)
    (ra t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo (pp_image [] false false false [] false) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 np)) ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (Z.of_nat (length r))) t1 t2 (Z_to_bv 64 POD_NENT_OFF) s1
             (Z_to_bv 64 sh) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (cur rest src r)) s4
             (Z_to_bv 64 pp) (Z_to_bv 64 cap) (Z_to_bv 64 nl) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130e0) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r m1 ra t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 s11 t3 t4 t5 t6 Hsh Hnp Hsuf MB C50 C20.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L0.
  pre_nums.
  (* 0x130e0 ld s2,0x50(sp); addi a1,zero,7; bne a0,a1 *)
  pose proof (cell8_read m1 _ _ C50) as HR50. step. clear HR50. step. step.
  destruct (Z.eqb_spec sh 7) as [E7|E7].
  - (* a Struct *)
    subst sh. if_false. eapply hdr_struct_ok; [exact Hnp | exact Hsuf | exact MB | exact C50 | exact C20].
  - (* an Object: 0x13114 .. 0x13144 *)
    if_cases E; zify_cond E; [| exfalso; rewrite ?unsigned_lit in E by lia; lia].
    st_pp 7 1%nat. do 3 step. step. st_pp 16384 8%nat. st_pp 4 1%nat. st_pp 5 1%nat. st_pp 6 1%nat.
    do 4 step.
    rewrite (obj_isp sh Hsh), (obj_type sh Hsh).
    lazymatch type of MB with MBr _ _ _ _ _ _ ?I _ =>
      assert (EI : I = pp_at (buf8 POD_OBJECT) 8 false false false [] false) end.
    { vm_compute. reflexivity. }
    rewrite EI in MB. clear EI.
    eapply hdr_obj; [exact Hsh | exact E7 | exact Hnp | exact Hsuf | exact MB | exact C50 | exact C20].
Qed.

(** 0x13044 -> 0x13208 or 0x13f80: the whole first piece. *)
Lemma pre_ok : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  evt rsegs (PreQ (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                  (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x5000) (Z_to_bv 64 POD_PROPS) (Z_to_bv 64 pp)
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length rest))) (Z_to_bv 64 src) s4 s5
             (Z_to_bv 64 cap) (Z_to_bv 64 nl) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6.
  unfold HEAD_BUILD.
  pose proof pp_range as (P1 & P2). pose proof sp_range as (S1 & S2). pose proof lo_range as L0.
  pose proof (bytes_at_bound rsegs m src rest HSRC) as (R1 & R2).
  pose proof MB0 as MBj.
  (* 0x13044 bnez a0 *)
  step. if_cases E; zify_cond E; try (exfalso; unfold POD_PROPS in P2; rewrite ?unsigned_lit in E by lia; lia).
  (* 0x1304c .. 0x13064: s5 = pp, s0 = 0x4d14, s4 = pp + 0x4000, the memset arguments; 0x13068 jal memset *)
  do 8 step.
  eapply evt_cut.
  { eapply MSET with (junk := junk).
    - rewrite !unsigned_lit by (unfold POD_PROPS in *; lia). exact HBLK.
    - exact HMI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                     Ems & MU2 & WM2 & MI2 & CB2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CB2 by (unfold POD_PROPS in *; lia).
  pose proof (rw_cells_CB_bytes m2 pp _ _ CB2) as HB2. clear CB2.
  lazymatch type of HB2 with bytes_at _ _ _ ?L =>
    assert (Ez : L = pp_image [] false false false [] false) by (vm_compute; reflexivity) end.
  rewrite Ez in HB2. clear Ez.
  assert (MB : MBr sp m rest src pp lo (pp_image [] false false false [] false) m2).
  { pose proof MBj as (_ & HLj & _).
    pose proof (MBr_call_pp sp m rest src pp lo HOK junk m m2 0 POD_PROPS (pp_image [] false false false [] false) MBj)
      as X.
    rewrite !Z.add_0_r in X.
    specialize (X MU2 WM2 MI2 HB2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold POD_PROPS in *; lia)).
    replace (overwrite junk (Z.to_nat 0) (pp_image [] false false false [] false))
      with (pp_image [] false false false [] false) in X; [exact X|].
    unfold overwrite. cbn [Z.to_nat firstn app]. rewrite skipn_all2; [rewrite app_nil_r; reflexivity|].
    pose proof (length_pp_image [] false false false [] false ltac:(cbn; unfold POD_BUF_MAX; lia)
                  ltac:(cbn; lia) (Forall_nil _)) as Hl2.
    unfold PP_SIZE in Hl2. unfold POD_PROPS in HLj. lia. }
  clear MBj HB2 MU2 WM2 MI2.
  pre_nums.
  (* 0x1306c sd s4,0x50(sp) *)
  sd8 0x50.
  (* 0x13070 beqz s2 *)
  step.
  destruct (list_cases3 rest) as [Er | [(b0 & Er) | (b0 & b1 & r2 & Er)]].
  - (* no input byte: shape 0, no property; 0x13094 .. 0x130c8, then 0x13148 *)
    rewrite Er. cbn [length Z.of_nat fuzz_u8 fst snd]. if_true.
    (* 0x13094 mv t0,zero; 0x13098 sd zero,0x20(sp) *)
    step. sd8 0x20.
    (* 0x1309c sb zero,7(s5) .. 0x130c8 j 0x13148 *)
    st_pp 7 1%nat. do 4 step. st_pp 16384 8%nat. st_pp 4 1%nat. st_pp 5 1%nat. st_pp 6 1%nat.
    do 3 step.
    lazymatch type of MB with MBr _ _ _ _ _ _ ?I _ =>
      assert (EI : I = pp_at (buf8 POD_OBJECT) 8 false false false [] false) end.
    { vm_compute. reflexivity. }
    rewrite EI in MB. clear EI.
    replace (Z_to_bv 64 src) with (Z_to_bv 64 (cur rest src [])) by (unfold cur; rewrite Er; cbn; f_equal; lia).
    change (0 mod 8) with 0. change (0 mod 4) with 0.
    eapply (hdr_obj 0 0 []);
      [lia | lia | lia | exists (length rest); rewrite Er; split; reflexivity | exact MB | eassumption | eassumption].
  - (* one byte: the shape from it, no property *)
    assert (HR0 : ov_read_bytes rsegs mm (wa src) 1 = Some [b0]).
    { pose proof (MBr_byte sp m rest src pp lo _ mm 0 b0 [] MB ltac:(rewrite Er; reflexivity)) as X.
      rewrite Z.add_0_r in X. exact X. }
    rewrite Er. cbn [length Z.of_nat fuzz_u8 fst snd]. if_false.
    (* 0x13074 lbu a0,0(s3); addi a1,zero,1; andi a0,a0,7; bne s2,a1 *)
    step. clear HR0. step. step. step. if_false.
    (* 0x13084 mv t0,zero; sd zero,0x20(sp); addi s3,s3,1; j 0x130e0 *)
    step. sd8 0x20. do 2 step.
    rewrite shape_val.
    replace (Z_to_bv 64 (src + 1)) with (Z_to_bv 64 (cur rest src [])) by (unfold cur; rewrite Er; cbn; f_equal; lia).
    change (0 mod 4) with 0.
    pose proof (byte_range b0).
    eapply (shape_ok (bv_unsigned b0 mod 8) 0 []);
      [apply Z.mod_pos_bound; lia | lia | exists 1%nat; rewrite Er; split; [cbn; lia | reflexivity]
      | exact MB | eassumption | eassumption].
  - (* two bytes or more: the shape, then nprops from the second into the cell sp + 0x20 *)
    assert (HR0 : ov_read_bytes rsegs mm (wa src) 1 = Some [b0]).
    { pose proof (MBr_byte sp m rest src pp lo _ mm 0 b0 (b1 :: r2) MB ltac:(rewrite Er; reflexivity)) as X.
      rewrite Z.add_0_r in X. exact X. }
    assert (HR1 : ov_read_bytes rsegs mm (wa (src + 1)) 1 = Some [b1]).
    { exact (MBr_byte sp m rest src pp lo _ mm 1 b1 r2 MB ltac:(rewrite Er; reflexivity)). }
    assert (HL : Z.of_nat (length rest) = Z.of_nat (length r2) + 2) by (rewrite Er; cbn [length]; lia).
    if_cases E0; zify_cond E0; [exfalso; rewrite ?unsigned_lit in E0 by lia; lia|].
    (* 0x13074 lbu a0,0(s3); addi a1,zero,1; andi a0,a0,7; bne s2,a1 *)
    step. clear HR0. step. step. step.
    if_cases E1; zify_cond E1; [|exfalso; rewrite ?unsigned_lit in E1 by lia; lia].
    (* 0x130cc lbu a1,1(s3); addi t0,s2,-2; addi s3,s3,2; andi a1,a1,3; 0x130dc sd a1,0x20(sp) *)
    step. clear HR1. do 3 step. sd8 0x20.
    rewrite shape_val. rewrite np_val in *.
    replace (Z_to_bv 64 (src + 2)) with (Z_to_bv 64 (cur rest src r2)) by (unfold cur; f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat (length rest) + -2)) with (Z_to_bv 64 (Z.of_nat (length r2))) by (f_equal; lia).
    replace (fuzz_u8 rest) with (bv_unsigned b0, b1 :: r2) by (rewrite Er; reflexivity).
    cbn [fuzz_u8 fst snd].
    pose proof (byte_range b0). pose proof (byte_range b1).
    eapply (shape_ok (bv_unsigned b0 mod 8) (bv_unsigned b1 mod 4) r2);
      [apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
      | exists 2%nat; rewrite Er; split; [cbn; lia | reflexivity] | exact MB | eassumption | eassumption].
Qed.

End Pre.

(** The first piece as Cut.v states it. *)
Theorem pre_holds : memset_contract -> S_pre.
Proof.
  intros MSET. unfold S_pre.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m rest junk nl cap src pp lo -> HPP0 HPPA -> -> -> HNL -> HCAP -> -> HSRC0 HSRC HBLK HROM HDJ HLO1
         HLO2 HST HMID HSPA HSROM HRELRO HMI.
  eapply pre_ok; eassumption.
Qed.
