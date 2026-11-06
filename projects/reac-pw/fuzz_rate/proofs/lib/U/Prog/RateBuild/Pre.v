(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 288 of its 318 lines of code are new or changed and 544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/U/Prog/Seg/M01.v, with its module paths and module names changed; 431 of its 468 lines of code are new or changed and 281 lines of the source are left out. *)
(** The UBSan builder's first piece, 0x13110 -> 0x1333c (or 0x140e0 when the object has no property): the NULL
    test of the first block (fuzz_rate.c:242), memset(pp, 0, sizeof *pp) (0x13124, pod.h:384), the shape and nprops
    reads (0x13128-0x1318c, pod.h:385-386, three paths by how many input bytes are left, the UBSan checks on the
    cursor at 0x13138 and 0x13178 not taken), mask to the cell sp + 0x10 (0x13190), the alignment check of pp
    (0x13194, pod.h:387, its trap 0x1319c not taken), the object header (0x131a0-0x13280, pod.h:388-396, b3 to the
    cell sp + 8 at 0x131b8, the UBSan checks on pp + 4, pp + 8 and pp + 12 at 0x131c8, 0x131f4, 0x1321c and 0x1325c
    not taken), the cells sp + 0x98, 0x38 (fl), 0xd8 and 0x50 (0x13284-0x132a0), the nprops = 0 exit (0x132a8 ->
    0x140e0) and the property loop's preheader (0x132ac-0x13338), which leaves the loop's constants in registers and
    frame cells. [pre_holds] is the statement of this piece.

    The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Pre.v, re-walked at
    rate's registers (src in s7, the bytes left in s1 then t1, len in s4, &pp->len in s11, ~pp in s6), frame cells
    (shape 0xb0, nprops 0xa8, the header values of Cut.CHDR) and addresses.

    After the header the block holds [Layout.pc_image] of the empty cut [PbCut shape [] None]: buf is the object's
    size word (still 0) and its header, len is 8 (a Struct) or 16 (an Object), is_props is the header's, and every
    other byte is memset's zero. The image is checked against the stores by computation ([lbeq]). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv memset_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut UTac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Byte lists compared by computation *)
Fixpoint lbeq (a b : list byte) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb (bv_unsigned x) (bv_unsigned y) && lbeq a' b'
  | _, _ => false
  end.

Lemma lbeq_ok : forall a b, lbeq a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [lbeq] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma overwrite_all : forall (l bs : list byte), length bs = length l -> overwrite l 0 bs = bs.
Proof.
  intros l bs H. unfold overwrite. cbn [firstn app]. rewrite Nat.add_0_l.
  rewrite skipn_all2 by lia. apply app_nil_r.
Qed.

(** ** Words *)
(** pp & 7 for a 16-aligned pp (pod.h:387). *)
Lemma land7_al : forall p, p mod 16 = 0 -> Z.land p 7 = 0.
Proof. intros p H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. lia. Qed.

(** shape = byte & 7 (pod.h:385). *)
Lemma land7b : forall b : byte, Z.land (bv_unsigned (zxb b)) 7 = bv_unsigned b mod 8.
Proof.
  intros b. pose proof (byte_range b). unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(** nprops = byte & 3 (pod.h:386). *)
Lemma land3b : forall b : byte, Z.land (bv_unsigned (zxb b)) 3 = bv_unsigned b mod 4.
Proof.
  intros b. pose proof (byte_range b). unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity.
Qed.

(** `seqz a4,a0` and `snez a0,a0` with a0 = shape - 6 (pod.h:393, :395). *)
Lemma seqz_sh : forall sh, 0 <= sh < 8 -> v_sltiu (Z_to_bv 64 (sh + -6)) 1 = Z_to_bv 64 (Z.b2z (sh =? 6)).
Proof.
  intros sh H.
  assert (E : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma snez_sh : forall sh, 0 <= sh < 8 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (sh + -6)) = Z_to_bv 64 (Z.b2z (negb (sh =? 6))).
Proof.
  intros sh H.
  assert (E : sh = 0 \/ sh = 1 \/ sh = 2 \/ sh = 3 \/ sh = 4 \/ sh = 5 \/ sh = 6 \/ sh = 7) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(** `subw a1,a1,a4`: SPA_TYPE_OBJECT_PropInfo or _Props (0x40002 - (shape = 6)). *)
Lemma subw_b2z : forall b,
  Z_to_bv 64 (bv_swrap 32 (262146 - bv_unsigned (Z_to_bv 64 (Z.b2z b)))) = Z_to_bv 64 (262146 - Z.b2z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

(** ** The block's images *)
(** The image memset leaves (pod.h:384). *)
Definition M0 : list byte := pp_image [] false false false [] false.

(** The image of the empty cut of an object that is not a Struct. *)
Lemma pc_image_obj : forall sh, sh <> 7 ->
  pc_image (PbCut sh [] None)
  = pp_image (le32 0 ++ le32 POD_OBJECT ++ le32 (if sh =? 6 then POD_OBJECT_PROPINFO else POD_OBJECT_PROPS)
              ++ le32 POD_PARAM_PROPS) (negb (sh =? 6)) false false [] false.
Proof.
  intros sh H. unfold pc_image, pc_buf, body_bytes, open_bytes, hdr_bytes.
  cbn [pc_shape pc_props pc_open flat_map].
  replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H).
  rewrite !app_nil_r. unfold is_props. cbn [p_shape].
  replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H).
  rewrite andb_true_r. reflexivity.
Qed.

Lemma pc_wf_nil : forall sh, 0 <= sh < 8 -> pc_wf sh [].
Proof. intros sh H. unfold pc_wf. split; [lia|]. split; [constructor|]. split; [constructor | cbn; lia]. Qed.

Lemma pc_buf_len_obj : forall sh, sh <> 7 -> Z.of_nat (length (pc_buf (PbCut sh [] None))) = 16.
Proof.
  intros sh H. unfold pc_buf, body_bytes, open_bytes, hdr_bytes. cbn [pc_shape pc_props pc_open flat_map].
  replace (sh =? 7) with false by (symmetry; apply Z.eqb_neq; exact H).
  rewrite !length_app, !length_le32. reflexivity.
Qed.

Section Pre.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.

(** The six header values (fuzz_rate.c:237-239) as Cut.v's record. *)
Local Notation HD := (Hdr mask buflen b3 b4 b5 b6).

(** The bounds of the block, of the input and of the frame. *)
Lemma bnds : 0 < pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 4096 <= bv_unsigned sp /\
             bv_unsigned sp + 488 <= 2^64 /\ 0 < src /\ src + Z.of_nat (length rest) <= lo.
Proof.
  destruct HOK as (H1 & H2 & H3 & _ & H5 & H6 & H7 & H8 & _ & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in *. lia.
Qed.

Ltac qlia := unfold POD_PROPS, POD_LEN_OFF, POD_NENT_OFF, MID_STACK, FRAME_LOCALS in *; lia.

(** The target of this piece: the property loop's head, or the end when the object has no property. *)
Definition PreQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  fun ms => (np = 0 /\ POSTH sp gp tp F fc m rest fl src pp lo HD sh [] r ms)
         \/ (np <> 0 /\ PROPH sp gp tp F fc m rest fl src pp lo HD sh np [] r ms).

(** ** Tactics of this walk *)
(** A branch decided by its condition: the words are literals, the test is arithmetic. *)
Ltac solve_br :=
  unfold c_eq, c_ltu, bv_eqb, bv_ltu; cbn [length] in *;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by qlia
         end;
  rewrite ?unsigned_lit_wrap;
  rewrite ?negb_true_iff, ?negb_false_iff;
  first [ reflexivity | apply Z.eqb_eq; qlia | apply Z.eqb_neq; qlia | apply Z.ltb_lt; qlia | apply Z.ltb_ge; qlia ].

Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_br]
  end.

(** `not rd,rs` (xori -1) as the cells' Z.lnot. *)
Ltac fix_not :=
  match goal with
  | |- context [Z.lxor (bv_unsigned (Z_to_bv 64 ?x)) 18446744073709551615] =>
      rewrite (unsigned_lit x) by qlia; rewrite (zb_lxor_ones x) by qlia; rewrite (lnot_lit x)
  end.

(** A store of n bytes into the block at pp + o: the block's image overwritten, the cells carried, the memory named
    again. *)
Ltac bst o n :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SK := fresh "SK" in
      let HLI := fresh "HLI" in
      pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (_ & _ & HLI);
      assert (SK : store_ok rsegs mm (Z_to_bv 64 (pp + o)) n = true)
        by (change (Z_to_bv 64 (pp + o)) with (wa (pp + o)); eapply MBr_pp_ok; [exact MB | qlia | qlia]);
      step; clear SK; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?w ?bs) _) =>
          change (write_to_mem mm w bs) with (write_to_mem mm (wa (pp + o)) bs);
          let MB2 := fresh "MB" in
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 (overwrite Ib (Z.to_nat o) bs) (write_to_mem mm (wa (pp + o)) bs))
            by (eapply MBr_pp_store;
                [ exact HOK | exact MB | qlia
                | rewrite ?length_le1, ?length_le4, ?length_le8; qlia ]);
          clear MB HLI; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (wa (pp + o)) bs) in *; clearbody mn
      end
  end.

(** An 8-byte store into the frame cell at sp + OFF (OFF > 0); the cell's bytes become the hypothesis C. *)
Ltac fst8 OFF C :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SK := fresh "SK" in
      assert (SK : store_ok rsegs mm (Z_to_bv 64 (bv_unsigned sp + OFF)) 8 = true)
        by (change (Z_to_bv 64 (bv_unsigned sp + OFF)) with (wa (bv_unsigned sp + OFF));
            eapply MBr_stk_ok; [exact HOK | exact MB | qlia | qlia]);
      step; clear SK; keep_cells;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?w ?bs) _) =>
          change (write_to_mem mm w bs) with (write_to_mem mm (wa (bv_unsigned sp + OFF)) bs);
          let MB2 := fresh "MB" in
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 Ib (write_to_mem mm (wa (bv_unsigned sp + OFF)) bs))
            by (eapply MBr_stk_store; [ exact HOK | exact MB | qlia | qlia | rewrite ?length_le8; qlia ]);
          assert (C : bytes_at rsegs (write_to_mem mm (wa (bv_unsigned sp + OFF)) bs) (bv_unsigned sp + OFF) bs)
            by (apply bytes_at_write_same; rewrite ?length_le8; qlia);
          clear MB; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (wa (bv_unsigned sp + OFF)) bs) in *; clearbody mn
      end
  end.

(** The 8-byte store at sp itself (`sd a0,0(sp)`): the step leaves the address as sp, not a literal sum, so the
    store's obligation is stated at sp and the address named [wa (sp + 0)] after the step. *)
Ltac fst0 C :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SK := fresh "SK" in
      let SK0 := fresh "SK" in
      assert (SK : store_ok rsegs mm sp 8 = true)
        by (eapply (MBr_stk_ok_w _ _ _ _ _ _ HOK _ mm sp (bv_unsigned sp + 0) 8 MB);
            [ symmetry; apply wa_of_var; lia | qlia | qlia ]);
      assert (SK0 : store_ok rsegs mm (Z_to_bv 64 (bv_unsigned sp + 0)) 8 = true)
        by (change (Z_to_bv 64 (bv_unsigned sp + 0)) with (wa (bv_unsigned sp + 0));
            eapply MBr_stk_ok; [exact HOK | exact MB | qlia | qlia]);
      step; clear SK SK0;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?w ?bs) _) =>
          replace (write_to_mem mm w bs) with (write_to_mem mm (wa (bv_unsigned sp + 0)) bs)
            by (f_equal; first [ reflexivity | apply wa_of_var; lia | symmetry; apply wa_of_var; lia
                               | unfold wa; f_equal; lia ]);
          keep_cells;
          let MB2 := fresh "MB" in
          assert (MB2 : MBr A1 A2 A3 A4 A5 A6 Ib (write_to_mem mm (wa (bv_unsigned sp + 0)) bs))
            by (eapply MBr_stk_store; [ exact HOK | exact MB | qlia | qlia | rewrite ?length_le8; qlia ]);
          assert (C : bytes_at rsegs (write_to_mem mm (wa (bv_unsigned sp + 0)) bs) (bv_unsigned sp + 0) bs)
            by (apply bytes_at_write_same; rewrite ?length_le8; qlia);
          clear MB; rename MB2 into MB;
          let mn := fresh "mm" in
          set (mn := write_to_mem mm (wa (bv_unsigned sp + 0)) bs) in *; clearbody mn
      end
  end.

(** The `slli s4,s4,32` result as MULT10 (the multiplier of v / 10). *)
Ltac fix_mult10 :=
  match goal with
  | |- context [Z_to_bv 64 ?z] =>
      lazymatch z with Zpos _ => idtac end;
      let v := eval vm_compute in (z mod 2^64 =? MULT10) in
      lazymatch v with true => rewrite (lit_mod z MULT10) by (vm_compute; reflexivity) end
  end.

(** ** 0x13284: the cells of the object, the nprops = 0 exit and the property loop's preheader (pod.h:398) *)
Lemma tail_ok : forall (sh np : Z) (r : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo (pc_image (PbCut sh [] None)) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 b3)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 mask)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0xa8) (le8 (Z_to_bv 64 np)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 sh)) ->
  s0 = Z_to_bv 64 0x5000 -> t1 = Z_to_bv 64 (Z.of_nat (length r)) -> s2 = Z_to_bv 64 fl ->
  s4 = Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh [] None)))) -> s7 = Z_to_bv 64 (cur rest src r) ->
  s8 = Z_to_bv 64 pp -> s11 = Z_to_bv 64 (pp + POD_LEN_OFF) ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13284) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hsh Hnp Hsuf MB C08 C10 C18 C20 C28 C30 CA8 CB0 -> -> -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (pc_wf_nil sh Hsh) as Hwf.
  (* 0x13284 addiw a0,s0,-0x2ec ; add a0,s8,a0 ; sd a0,0x98(sp) *)
  step. step. fst8 0x98 C98.
  (* 0x13290 not a0,s8 ; sd s2,0x38(sp) ; sd s8,0xd8(sp) ; mv s6,a0 ; sd a0,0x50(sp) *)
  step. fix_not. fst8 0x38 C38. fst8 0xd8 CD8. step. fst8 0x50 C50.
  (* 0x132a4 ld a0,0xa8(sp) ; beqz a0: no property, the end 0x140e0 *)
  pose proof (cell8_read _ _ _ CA8) as R. step. clear R. step.
  destruct (Z.eq_dec np 0) as [Hn0|Hn0].
  { br true. apply evt_done. cbv beta delta [PreQ]. left. split; [exact Hn0|].
    cbv beta delta [POSTH]. do 23 eexists. split; [reflexivity|].
    split; [exact MB|]. split; [exact (conj C08 (conj C10 (conj C18 (conj C20 (conj C28 C30)))))|].
    split; [exact C38|]. split; [exact C50|]. split; [exact C98|]. split; [exact CD8|].
    split; [exact Hsuf | exact Hwf]. }
  br false.
  (* 0x132ac .. 0x132e4: the loop's constants into registers *)
  do 15 step.
  (* 0x132e8 sd a5,0xc0(sp) ; addiw a5,t2,0x14 ; addi a1,a1,3 ; sd a1,0x58(sp) ; addi a2,a2,1 ; sd a2,0x78(sp) *)
  fst8 0xc0 CC0. step. step. fst8 0x58 C58. step. fst8 0x78 C78.
  (* 0x13300 addiw a0,a0,-1 ; sd a0,0xb8(sp) ; addi s4,a3,-0x333 ; addiw a0,a4,0x556 ; sd a0,0(sp) *)
  step. fst8 0xb8 CB8. step. step. fst0 C00.
  (* 0x13314 add a5,s8,a5 ; slli s4,s4,32 ; not a0,a6 ; sd a0,0xa0(sp) ; not a0,t0 ; sd a0,0x80(sp) *)
  step. step. fix_mult10. step. fix_not. fst8 0xa0 CA0. step. fix_not. fst8 0x80 C80.
  (* 0x1332c sd a5,0x88(sp) ; not a0,a5 ; sd a0,0x90(sp) ; sd s11,0xc8(sp) *)
  fst8 0x88 C88. step. fix_not. fst8 0x90 C90. fst8 0xc8 CC8.
  apply evt_done. cbv beta delta [PreQ]. right. split; [exact Hn0|].
  cbv beta delta [PROPH]. do 17 eexists. split; [reflexivity|].
  split; [exact MB|].
  split; [exact (conj C00 (conj C50 (conj C58 (conj C78 (conj C80 (conj C88 (conj C90 (conj C98 (conj CA0
                 (conj CB8 (conj CC0 (conj CC8 CD8))))))))))))|].
  split; [exact (conj C38 (conj CA8 (conj CB0 (conj C08 (conj C10 (conj C18 (conj C20 (conj C28 C30))))))))|].
  split; [exact Hsuf|]. split; [exact Hwf|]. split; [lia | cbn [length]; lia].
Qed.

(** ** 0x13190: mask to its cell, the alignment check (pod.h:387) and the object header (pod.h:388-396) *)
Lemma hdr_ok : forall (sh np : Z) (r : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo M0 m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0xa8) (le8 (Z_to_bv 64 np)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0xb0) (le8 (Z_to_bv 64 sh)) ->
  s0 = Z_to_bv 64 0x5000 -> t1 = Z_to_bv 64 (Z.of_nat (length r)) -> s7 = Z_to_bv 64 (cur rest src r) ->
  s8 = Z_to_bv 64 pp -> s2 = Z_to_bv 64 fl -> s4 = Z_to_bv 64 b3 -> s5 = Z_to_bv 64 mask ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13190) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hsh Hnp Hsuf MB C18 C20 C28 C30 CA8 CB0 -> -> -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  (* 0x13190 sd s5,0x10(sp): mask *)
  fst8 0x10 C10.
  (* 0x13194 andi a0,s8,7 ; beqz a0: pp is 8-aligned, the trap 0x1319c not taken *)
  step. rewrite (unsigned_lit pp) by qlia. rewrite (land7_al pp HPPA).
  step. br true.
  (* 0x131a0 lui a0,4 ; addi a1,zero,4 ; add s11,s8,a0 ; addi a0,zero,7 ; sd a1,0(s11): len = 4 *)
  step. step. step. step. bst 16384 8%nat.
  (* 0x131b4 ld a1,0xb0(sp) ; sd s4,8(sp) ; bne a1,a0: the shape (b3 to its cell on the way) *)
  pose proof (cell8_read _ _ _ CB0) as R. step. clear R. fst8 0x8 C08. step.
  destruct (Z.eq_dec sh 7) as [->|N7].
  - (* a Struct: 0x131c0 addi a0,zero,-4 ; bltu s8,a0 (pp + 4 does not wrap, the trap 0x131c8 not taken) *)
    br false. step. step. br true.
    (* 0x131cc sb zero,7(s8) ; addi a0,zero,14 ; addi s4,zero,8 ; sd s4,0(s11) ; sb a0,4(s8) ; sb zero,5(s8) ;
       sb zero,6(s8) ; j 0x13284 *)
    bst 7 1%nat. step. step. bst 16384 8%nat. bst 4 1%nat. bst 5 1%nat. bst 6 1%nat. step.
    lazymatch goal with
    | H : MBr _ _ _ _ _ _ ?I _ |- _ =>
        replace I with (pc_image (PbCut 7 [] None)) in H by (apply lbeq_ok; vm_compute; reflexivity)
    end.
    eapply tail_ok; [ lia | exact Hnp | exact Hsuf | exact MB | exact C08 | exact C10 | exact C18 | exact C20
                    | exact C28 | exact C30 | exact CA8 | exact CB0 | reflexivity | reflexivity | reflexivity
                    | f_equal; vm_compute; reflexivity | reflexivity | reflexivity | reflexivity ].
  - (* an Object: 0x131ec addi a0,zero,-4 ; bltu s8,a0 (the trap 0x131f4 not taken) *)
    br true. step. step. br true.
    (* 0x131f8 sb zero,7(s8) ; addi a0,zero,15 ; addi a1,zero,8 ; addi a2,zero,-8 ; sd a1,0(s11) ; sb a0,4(s8) ;
       sb zero,5(s8) ; sb zero,6(s8) ; bltu s8,a2 (pp + 8 does not wrap, the trap 0x1321c not taken) *)
    bst 7 1%nat. step. step. step. bst 16384 8%nat. bst 4 1%nat. bst 5 1%nat. bst 6 1%nat. step. br true.
    (* 0x13220 ld a0,0xb0(sp) ; addi a0,a0,-6 ; lui a1,0x40 ; sb zero,0xb(s8) ; addi a2,zero,4 ; addi a3,zero,0xc ;
       seqz a4,a0 *)
    pose proof (cell8_read _ _ _ CB0) as R. step. clear R. step. step. bst 11 1%nat. step. step. step.
    rewrite (seqz_sh sh Hsh).
    (* 0x1323c addi a1,a1,2 ; subw a1,a1,a4 ; addi a4,zero,-12 ; sd a3,0(s11) ; sb a1,8(s8) ; sb zero,9(s8) ;
       sb a2,0xa(s8) ; bltu s8,a4 (pp + 12 does not wrap, the trap 0x1325c not taken) *)
    step. step. rewrite subw_b2z. step. bst 16384 8%nat. bst 8 1%nat. bst 9 1%nat. bst 10 1%nat. step. br true.
    (* 0x13260 sb zero,0xe(s8) ; sb zero,0xf(s8) ; addi a1,zero,2 ; addi s4,zero,0x10 ; snez a0,a0 ;
       sd s4,0(s11) ; sw a0,8(s11) ; sb a1,0xc(s8) ; sb zero,0xd(s8) *)
    bst 14 1%nat. bst 15 1%nat. step. step. step. rewrite (snez_sh sh Hsh).
    bst 16384 8%nat. bst 16392 4%nat. bst 12 1%nat. bst 13 1%nat.
    lazymatch goal with
    | H : MBr _ _ _ _ _ _ ?I _ |- _ =>
        replace I with (pc_image (PbCut sh [] None)) in H
          by (rewrite (pc_image_obj sh N7); destruct (sh =? 6); apply lbeq_ok; vm_compute; reflexivity)
    end.
    eapply tail_ok; [ lia | exact Hnp | exact Hsuf | exact MB | exact C08 | exact C10 | exact C18 | exact C20
                    | exact C28 | exact C30 | exact CA8 | exact CB0 | reflexivity | reflexivity | reflexivity
                    | f_equal; symmetry; apply (pc_buf_len_obj sh N7) | reflexivity | reflexivity
                    | reflexivity ].
Qed.

(** ** 0x13128: the shape and nprops reads (pod.h:385-386), by how many input bytes are left *)
Lemma reads_ok : forall (rs : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  rs = rest -> MBr sp m rest src pp lo M0 m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
  s0 = Z_to_bv 64 0x5000 -> s1 = Z_to_bv 64 (Z.of_nat (length rs)) -> s7 = Z_to_bv 64 src ->
  s8 = Z_to_bv 64 pp -> s2 = Z_to_bv 64 fl -> s4 = Z_to_bv 64 b3 -> s5 = Z_to_bv 64 mask ->
  evt rsegs (PreQ (fst (fuzz_u8 rs) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rs))) mod 4)
                  (snd (fuzz_u8 (snd (fuzz_u8 rs)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13128) fc None m1 (seg_rom rsegs)).
Proof.
  intros rs ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hrs MB C18 C20 C28 C30 -> -> -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  rewrite <- Hrs in P7.
  (* 0x13128 beqz s1: no input byte *)
  step.
  destruct rs as [|b0 [|b1 r2]]; cbn [fuzz_u8 fst snd].
  - (* 0x1315c mv t1,zero ; sd zero,0xb0(sp) ; sd zero,0xa8(sp) ; j 0x13190 *)
    br true. step. fst8 0xb0 CB0. fst8 0xa8 CA8. step.
    eapply hdr_ok;
      [ lia | lia | exists (length rest); split; [lia | rewrite skipn_all; reflexivity]
      | exact MB | exact C18 | exact C20 | exact C28 | exact C30 | exact CA8 | exact CB0
      | reflexivity | reflexivity | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia
      | reflexivity | reflexivity | reflexivity | reflexivity ].
  - (* one byte: 0x1312c addi a0,s7,1 ; addi a1,zero,1 ; bltu a1,a0 (the cursor's check 0x13138, not taken) *)
    br false. step. step. step. br true.
    (* 0x1313c lbu a2,0(s7) ; andi a2,a2,7 ; sd a2,0xb0(sp) ; bne s1,a1 *)
    assert (HR0 : ov_read_bytes rsegs m1 (wa src) 1 = Some [b0]).
    { replace (wa src) with (wa (src + Z.of_nat 0)) by (f_equal; lia).
      eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity]. }
    step. clear HR0. step. rewrite land7b. fst8 0xb0 CB0. step. br false.
    (* 0x1314c mv t1,zero ; sd zero,0xa8(sp) ; mv s7,a0 ; j 0x13190 *)
    step. fst8 0xa8 CA8. step. step.
    eapply hdr_ok;
      [ lia | lia | exists (length rest); split; [lia | rewrite skipn_all; reflexivity]
      | exact MB | exact C18 | exact C20 | exact C28 | exact C30 | exact CA8 | exact CB0
      | reflexivity | reflexivity | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia
      | reflexivity | reflexivity | reflexivity | reflexivity ].
  - (* two bytes or more *)
    br false. step. step. step. br true.
    assert (HR0 : ov_read_bytes rsegs m1 (wa src) 1 = Some [b0]).
    { replace (wa src) with (wa (src + Z.of_nat 0)) by (f_equal; lia).
      eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity]. }
    step. clear HR0. step. rewrite land7b. fst8 0xb0 CB0. step. br true.
    (* 0x1316c addi a0,a0,1 ; addi a1,zero,1 ; bltu a1,a0 (the cursor's check 0x13178, not taken) *)
    step. step. step. br true.
    (* 0x1317c lbu a0,1(s7) ; addi t1,s1,-2 ; addi s7,s7,2 ; andi a0,a0,3 ; sd a0,0xa8(sp) *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HR1 : ov_read_bytes rsegs mm (wa (src + 1)) 1 = Some [b1])
          by (change (src + 1) with (src + Z.of_nat 1); eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity])
    end.
    step. clear HR1. step. step. step. rewrite land3b. fst8 0xa8 CA8.
    eapply hdr_ok;
      [ lia | lia | exists 2%nat; split; [rewrite <- Hrs; cbn [length]; lia | rewrite <- Hrs; reflexivity]
      | exact MB | exact C18 | exact C20 | exact C28 | exact C30 | exact CA8 | exact CB0
      | reflexivity | f_equal; cbn [length]; lia
      | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia
      | reflexivity | reflexivity | reflexivity | reflexivity ].
Qed.

(** ** 0x13110: the NULL test of the block (fuzz_rate.c:242) and memset(pp, 0, 19744) (0x13124, pod.h:384) *)
Lemma pre_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (junk : list byte),
  memset_contract ->
  a0 = Z_to_bv 64 pp -> pp <> 0 -> s7 = Z_to_bv 64 src -> s1 = Z_to_bv 64 (Z.of_nat (length rest)) ->
  s2 = Z_to_bv 64 fl -> s5 = Z_to_bv 64 mask -> s4 = Z_to_bv 64 b3 ->
  bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
  bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
  bytes_at rsegs m (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
  bytes_at rsegs m (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
  s3 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
  rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] -> mem_inv rsegs m ->
  MBr sp m rest src pp lo junk m ->
  evt rsegs (PreQ (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                  (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 junk
    MSET -> Hpp0 -> -> -> -> -> C30 C28 C20 C18 -> -> HBLK HMI MB.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (_ & _ & HLJ).
  unfold RATE_BUILD.
  (* 0x13110 bnez a0: the block is not NULL (the abort 0x13114 not reached) *)
  step. br true.
  (* 0x13118 mv s8,a0 ; mv a1,zero ; mv a2,s3 ; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET; [ rewrite !unsigned_lit by qlia; exact HBLK | exact HMI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU & WM & MI & RW).
  rewrite !unsigned_lit in MU, RW by qlia.
  rewrite (ret_pc_even 0x13128) by lia.
  (* the block after memset is the image of 19744 zeros *)
  lazymatch type of RW with
  | rw_cells _ _ _ [CB _ ?BS] =>
      assert (MB1 : MBr sp m rest src pp lo M0 m1);
      [ replace M0 with (overwrite junk (Z.to_nat 0) BS);
        [ eapply (MBr_call_pp _ _ _ _ _ _ HOK junk m m1 0 POD_PROPS);
          [ exact MB | rewrite !Z.add_0_r; exact MU | exact WM | exact MI
          | rewrite Z.add_0_r; exact (rw_cells_CB_bytes _ _ _ _ RW)
          | rewrite repeat_length; qlia | lia | qlia ]
        | change (Z.to_nat 0) with 0%nat; rewrite overwrite_all by (rewrite repeat_length; qlia);
          apply lbeq_ok; vm_compute; reflexivity ]
      | ]
  end.
  (* the header values' cells are outside the block *)
  assert (D18 : bytes_at rsegs m1 (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ C18 MU). cbn [disjoint_from]. rewrite length_le8.
    split; [right; qlia | exact I]. }
  assert (D20 : bytes_at rsegs m1 (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ C20 MU). cbn [disjoint_from]. rewrite length_le8.
    split; [right; qlia | exact I]. }
  assert (D28 : bytes_at rsegs m1 (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256)))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ C28 MU). cbn [disjoint_from]. rewrite length_le8.
    split; [right; qlia | exact I]. }
  assert (D30 : bytes_at rsegs m1 (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ C30 MU). cbn [disjoint_from]. rewrite length_le8.
    split; [right; qlia | exact I]. }
  clear MB C18 C20 C28 C30 MU WM RW.
  eapply (reads_ok rest); [ reflexivity | exact MB1 | exact D18 | exact D20 | exact D28 | exact D30
                          | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                          | reflexivity ].
Qed.

End Pre.

Theorem pre_holds : memset_c.memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (rest junk : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s7 = Z_to_bv 64 src -> s1 = Z_to_bv 64 (Z.of_nat (length rest)) ->
    s2 = Z_to_bv 64 fl -> s5 = Z_to_bv 64 mask -> s4 = Z_to_bv 64 b3 ->
    bytes_at rsegs m (bv_unsigned sp + 0x30) (le8 (Z_to_bv 64 buflen)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x28) (le8 (Z_to_bv 64 (b4 * 256))) ->
    bytes_at rsegs m (bv_unsigned sp + 0x20) (le8 (Z_to_bv 64 b5)) ->
    bytes_at rsegs m (bv_unsigned sp + 0x18) (le8 (Z_to_bv 64 (b6 * 256))) ->
    0 <= fl < 256 -> 0 <= mask < 256 -> 0 <= buflen < 24 ->
    0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 ->
    s3 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
    0 < src -> bytes_at rsegs m src rest ->
    rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] ->
    (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) ->
    (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) ->
    src + Z.of_nat (length rest) <= lo -> pp + POD_PROPS <= lo ->
    stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) ->
    (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms =>
         (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4 = 0 /\
          POSTH sp gp tp F fc m rest fl src pp lo (Hdr mask buflen b3 b4 b5 b6) (fst (fuzz_u8 rest) mod 8) []
                (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms) \/
         (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4 <> 0 /\
          PROPH sp gp tp F fc m rest fl src pp lo (Hdr mask buflen b3 b4 b5 b6) (fst (fuzz_u8 rest) mod 8)
                (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4) [] (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RATE_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk fl mask buflen b3 b4 b5 b6 src pp lo Ha0 Hpp0 HPPA Hs7 Hs1 Hs2 Hs5 Hs4 C30 C28 C20 C18
    HFL HMK HBL HB3 HB4 HB5 HB6 Hs3 Hs0 HSRC0 HSRC HBLK HROM HDJ HLO1 HLO2 HST HMID HSPA HSROM HRELRO HMI.
  assert (Hpp : 0 <= pp /\ pp + POD_PROPS <= 2^64).
  { pose proof (rw_cells_bound rsegs m pp _ HBLK) as (A & B). cbn [cells_size csize] in B.
    rewrite Nat.add_0_r in B. rewrite Z2Nat.id in B by (unfold POD_PROPS; lia). lia. }
  assert (Hsp : bv_unsigned sp + FRAME_LOCALS <= 2^64) by (destruct HST as (_ & B & _); exact B).
  assert (Hlo : 0 <= lo) by (destruct HST as (A & _); exact A).
  assert (HOK : BOK sp rest src pp lo).
  { split; [exact HSRC0|]. split; [exact HLO1|]. split; [exact HLO2|]. split; [exact HDJ|].
    split; [exact HMID|]. split; [exact Hlo|]. split; [exact Hsp|]. split; [lia|].
    split; [exact HROM | exact HSROM]. }
  assert (MB : MBr sp m rest src pp lo junk m).
  { assert (HW : wr_at rsegs m pp POD_PROPS).
    { pose proof (proj2 HBLK) as HW. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW.
      rewrite Z2Nat.id in HW by (unfold POD_PROPS; lia). exact HW. }
    assert (Hl : Z.of_nat (length junk) = POD_PROPS).
    { pose proof (cells_at_wf rsegs m pp _ (proj1 HBLK)) as Hwf. cbn [cells_wf cell_wf] in Hwf.
      destruct Hwf as [Hj _]. rewrite Hj. apply Z2Nat.id. unfold POD_PROPS. lia. }
    split; [exact (rw_cells_CB_bytes m pp _ junk HBLK)|]. split; [exact Hl|]. split; [exact HW|].
    split; [exact HSRC|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI|].
    split; [exact HST | exact HRELRO]. }
  exact (pre_ok sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo HOK HPPA ra t0 t1 t2 s0 s1 a0 a1 a2 a3
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 junk MSET Ha0 Hpp0 Hs7 Hs1 Hs2 Hs5 Hs4
           C30 C28 C20 C18 Hs3 Hs0 HBLK HMI MB).
Qed.
