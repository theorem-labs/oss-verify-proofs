(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 265 of its 295 lines of code are new or changed and 544 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/Seg/M01.v, with its module paths and module names changed; 394 of its 420 lines of code are new or changed and 269 lines of the source are left out. *)
(** The UBSan builder's first piece, 0x13090 -> 0x132a8 (or 0x13fbc when the object has no property): the NULL test
    of the first block (fuzz_headamp.c:320), memset(pp, 0, sizeof *pp) (pod.h:384), the shape and nprops reads
    (pod.h:385-386, three paths by how many input bytes are left, the UBSan checks on the cursor not taken), the
    alignment check of pp (pod.h:387, not taken), the harness's cap saved at sp + 0x8, the object header
    (pod.h:388-396, the UBSan checks on pp + 4, pp + 8 and pp + 12 not taken) and the property loop's preheader,
    which leaves the loop's constants in registers and frame cells. [pre_holds] is the statement of this piece.

    After the header the block holds [Layout.pc_image] of the empty cut [PbCut shape [] None]: buf is the object's
    size word (still 0) and its header, len is 8 (a Struct) or 16 (an Object), is_props is the header's, and every
    other byte is memset's zero. The image is checked against the stores by computation ([lbeq]), so the order in
    which the header's bytes and the len field are stored does not matter. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv memset_c LLVMFuzzerTestOneInput_c
  reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import Facts Cut UTac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Post.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
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

(** nprops = byte & 3 (pod.h:386). *)
Lemma land3 : forall b : byte, Z.land (bv_unsigned (zxb b)) 3 = bv_unsigned b mod 4.
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
Variables (rest : list byte) (fl src pp lo cap : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis HPPA : pp mod 16 = 0.

(** The bounds of the block, of the input and of the frame. *)
Lemma bnds : 0 < pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 512 <= bv_unsigned sp /\
             bv_unsigned sp + 472 <= 2^64 /\ 0 < src /\ src + Z.of_nat (length rest) <= lo.
Proof.
  destruct HOK as (H1 & H2 & H3 & _ & H5 & H6 & H7 & H8 & _ & _).
  unfold POD_PROPS, MID_STACK, PARSE_STACK, FRAME_LOCALS in *. lia.
Qed.

Ltac qlia := unfold POD_PROPS, POD_LEN_OFF, POD_NENT_OFF, MID_STACK, PARSE_STACK, FRAME_LOCALS in *; lia.

(** The target of this piece: the property loop's head, or the end when the object has no property. *)
Definition PreQ (sh np : Z) (r : list byte) : machine_state -> Prop :=
  fun ms => (np = 0 /\ POSTH sp gp tp F fc m rest fl src pp lo cap sh [] r ms)
         \/ (np <> 0 /\ PROPH sp gp tp F fc m rest fl src pp lo cap sh np [] r ms).

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

(** An 8-byte store into the frame cell at sp + OFF; the cell's bytes become the hypothesis C. *)
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

(** The 8-byte store at sp itself (`sd rs,0(sp)`): the step leaves the address as sp, not a literal sum, so
    store_ok is stated at sp ([Facts.MBr_stk_ok_w]) and the memory is named again at wa (sp + 0). *)
Ltac fst8_sp C :=
  lazymatch goal with
  | MB : MBr ?A1 ?A2 ?A3 ?A4 ?A5 ?A6 ?Ib ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let SK := fresh "SK" in
      assert (SK : store_ok rsegs mm sp 8 = true)
        by (apply (MBr_stk_ok_w A1 A2 A3 A4 A5 A6 HOK Ib mm sp (bv_unsigned sp + 0) 8 MB);
            [ symmetry; apply wa_of_var; lia | qlia | qlia ]);
      step; clear SK;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?w ?bs) _) =>
          replace (write_to_mem mm w bs) with (write_to_mem mm (wa (bv_unsigned sp + 0)) bs)
            by (f_equal; apply wa_of_var; lia);
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

(** The `slli s3,s3,32` result as MULT10 (the multiplier of v / 10). *)
Ltac fix_mult10 :=
  match goal with
  | |- context [Z_to_bv 64 ?z] =>
      lazymatch z with Zpos _ => idtac end;
      let v := eval vm_compute in (z mod 2^64 =? MULT10) in
      lazymatch v with true => rewrite (lit_mod z MULT10) by (vm_compute; reflexivity) end
  end.

(** ** 0x131f8: the property loop's preheader (pod.h:398) *)
Lemma tail_ok : forall (sh np : Z) (r : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo (pc_image (PbCut sh [] None)) m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x90) (le8 (Z_to_bv 64 sh)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x8) (le8 (Z_to_bv 64 cap)) ->
  s0 = Z_to_bv 64 0x5000 -> s2 = Z_to_bv 64 (Z.of_nat (length r)) ->
  s3 = Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh [] None)))) -> s6 = Z_to_bv 64 (cur rest src r) ->
  s7 = Z_to_bv 64 (pp + POD_LEN_OFF) -> s8 = Z_to_bv 64 pp -> s5 = Z_to_bv 64 np ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x131f8) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hsh Hnp Hsuf MB C10 C90 C08 -> -> -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (pc_wf_nil sh Hsh) as Hwf.
  (* 0x131f8 addiw a0,s0,-0x2ec ; add a0,s8,a0 ; sd a0,0x68(sp) *)
  step. step. fst8 0x68 C68.
  (* 0x13204 not s4,s8 ; sd s8,0x70(sp) ; sd s7,0x78(sp) ; sd s4,0x18(sp) *)
  step. fix_not. fst8 0x70 C70. fst8 0x78 C78. fst8 0x18 C18.
  (* 0x13214 beqz s5: no property, the end *)
  step.
  destruct (Z.eq_dec np 0) as [Hn0|Hn0].
  { br true. apply evt_done. cbv beta delta [PreQ]. left. split; [exact Hn0|].
    cbv beta delta [POSTH]. do 24 eexists. split; [reflexivity|].
    split; [exact MB|]. split; [exact C10|]. split; [exact C18|]. split; [exact C70|]. split; [exact C68|].
    split; [exact C78|]. split; [exact C08|].
    split; [exact Hsuf | exact Hwf]. }
  br false.
  (* 0x13218 .. 0x13250: the loop's constants into registers *)
  do 15 step.
  (* 0x13254 sd t1,0xa0(sp) ; addiw a5,a5,0x14 ; addi a1,a1,3 ; sd a1,0x30(sp) ; addi a2,a2,1 ; sd a2,0x48(sp) *)
  fst8 0xa0 CA0. step. step. fst8 0x30 C30. step. fst8 0x48 C48.
  (* 0x1326c addiw a0,a0,-1 ; sd a0,0x98(sp) ; addi s3,a3,-0x333 ; addiw a0,a4,0x556 ; sd a0,0(sp) *)
  step. fst8 0x98 C98. step. step. fst8_sp C00.
  (* 0x13280 add a5,s8,a5 ; slli s3,s3,32 ; not a0,a6 ; sd a0,0x80(sp) ; not a0,t0 ; sd a0,0x50(sp) *)
  step. step. fix_mult10. step. fix_not. fst8 0x80 C80. step. fix_not. fst8 0x50 C50.
  (* 0x13298 sd a5,0x58(sp) ; not a0,a5 ; sd a0,0x60(sp) ; sd s5,0x20(sp) *)
  fst8 0x58 C58. step. fix_not. fst8 0x60 C60. fst8 0x20 C20.
  apply evt_done. cbv beta delta [PreQ]. right. split; [exact Hn0|].
  cbv beta delta [PROPH]. do 16 eexists. split; [reflexivity|].
  split; [exact MB|].
  split; [exact (conj C00 (conj C18 (conj C30 (conj C48 (conj C50 (conj C58 (conj C60 (conj C70 (conj C68
                 (conj C78 (conj C80 (conj C98 (conj CA0 C08)))))))))))))|].
  split; [exact (conj C10 (conj C20 C90))|].
  split; [exact Hsuf|]. split; [exact Hwf|]. split; [lia | cbn [length]; lia].
Qed.

(** ** 0x13108: the alignment check (pod.h:387), the cap's cell and the object header (pod.h:388-396) *)
Lemma hdr_ok : forall (sh np : Z) (r : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  0 <= sh < 8 -> 0 <= np < 4 -> suffix rest r ->
  MBr sp m rest src pp lo M0 m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x90) (le8 (Z_to_bv 64 sh)) ->
  s0 = Z_to_bv 64 0x5000 -> s2 = Z_to_bv 64 (Z.of_nat (length r)) -> s3 = Z_to_bv 64 cap ->
  s6 = Z_to_bv 64 (cur rest src r) -> s8 = Z_to_bv 64 pp -> s5 = Z_to_bv 64 np ->
  evt rsegs (PreQ sh np r)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13108) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh np r ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hsh Hnp Hsuf MB C10 C90 -> -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  (* 0x13108 andi a0,s8,7 ; beqz a0: pp is 8-aligned, the check not taken *)
  step. rewrite (unsigned_lit pp) by qlia. rewrite (land7_al pp HPPA).
  step. br true.
  (* 0x13114 lui a0,4 ; addi a1,zero,4 ; add s7,s8,a0 ; addi a0,zero,7 ; sd a1,0(s7): len = 4 *)
  step. step. step. step. bst 16384 8%nat.
  (* 0x13128 ld a1,0x90(sp) ; sd s3,8(sp): the harness's cap ; bne a1,a0: the shape *)
  pose proof (cell8_read _ _ _ C90) as R. step. clear R. fst8 0x8 C08. step.
  destruct (Z.eq_dec sh 7) as [->|N7].
  - (* a Struct: 0x13134 addi a0,zero,-4 ; bltu s8,a0 (pp + 4 does not wrap) *)
    br false. step. step. br true.
    (* 0x13140 addi a0,zero,14 ; addi s3,zero,8 ; sb a0,4(s8) ; sb zero,5(s8) ; sb zero,6(s8) ; sb zero,7(s8) ;
       sd s3,0(s7) ; j 0x131f8 *)
    step. step. bst 4 1%nat. bst 5 1%nat. bst 6 1%nat. bst 7 1%nat. bst 16384 8%nat. step.
    lazymatch goal with
    | H : MBr _ _ _ _ _ _ ?I _ |- _ =>
        replace I with (pc_image (PbCut 7 [] None)) in H by (apply lbeq_ok; vm_compute; reflexivity)
    end.
    eapply tail_ok; [ lia | exact Hnp | exact Hsuf | exact MB | exact C10 | exact C90 | exact C08 | reflexivity
                    | reflexivity | f_equal; vm_compute; reflexivity | reflexivity | reflexivity | reflexivity
                    | reflexivity ].
  - (* an Object: 0x13160 addi a0,zero,-4 ; bltu s8,a0 *)
    br true. step. step. br true.
    (* 0x1316c addi a0,zero,15 ; addi a1,zero,8 ; sd a1,0(s7) ; addi a1,zero,-8 ; sb a0,4(s8) ; sb zero,5(s8) ;
       sb zero,6(s8) ; sb zero,7(s8) ; bltu s8,a1 (pp + 8 does not wrap) *)
    step. step. bst 16384 8%nat. step. bst 4 1%nat. bst 5 1%nat. bst 6 1%nat. bst 7 1%nat. step. br true.
    (* 0x13194 ld a0,0x90(sp) ; addi a0,a0,-6 ; lui a1,0x40 ; addi a2,zero,4 ; addi a3,zero,0xc ; seqz a4,a0 *)
    pose proof (cell8_read _ _ _ C90) as R. step. clear R. step. step. step. step. step.
    rewrite (seqz_sh sh Hsh).
    (* 0x131ac addi a1,a1,2 ; subw a1,a1,a4 ; addi a4,zero,-12 ; sb a1,8(s8) ; sb zero,9(s8) ; sb a2,0xa(s8) ;
       sb zero,0xb(s8) ; sd a3,0(s7) ; bltu s8,a4 (pp + 12 does not wrap) *)
    step. step. rewrite subw_b2z. step. bst 8 1%nat. bst 9 1%nat. bst 10 1%nat. bst 11 1%nat. bst 16384 8%nat.
    step. br true.
    (* 0x131d4 addi a1,zero,2 ; addi s3,zero,0x10 ; snez a0,a0 ; sb a1,0xc(s8) ; sb zero,0xd(s8) ;
       sb zero,0xe(s8) ; sb zero,0xf(s8) ; sd s3,0(s7) ; sw a0,8(s7) *)
    step. step. step. rewrite (snez_sh sh Hsh).
    bst 12 1%nat. bst 13 1%nat. bst 14 1%nat. bst 15 1%nat. bst 16384 8%nat. bst 16392 4%nat.
    lazymatch goal with
    | H : MBr _ _ _ _ _ _ ?I _ |- _ =>
        replace I with (pc_image (PbCut sh [] None)) in H
          by (rewrite (pc_image_obj sh N7); destruct (sh =? 6); apply lbeq_ok; vm_compute; reflexivity)
    end.
    eapply tail_ok; [ lia | exact Hnp | exact Hsuf | exact MB | exact C10 | exact C90 | exact C08 | reflexivity
                    | reflexivity | f_equal; symmetry; apply (pc_buf_len_obj sh N7) | reflexivity | reflexivity
                    | reflexivity | reflexivity ].
Qed.

(** ** 0x130a8: the shape and nprops reads (pod.h:385-386), by how many input bytes are left (s2) *)
Lemma reads_ok : forall (rs : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  rs = rest -> MBr sp m rest src pp lo M0 m1 ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
  s0 = Z_to_bv 64 0x5000 -> s2 = Z_to_bv 64 (Z.of_nat (length rs)) -> s3 = Z_to_bv 64 cap ->
  s6 = Z_to_bv 64 src -> s8 = Z_to_bv 64 pp ->
  evt rsegs (PreQ (fst (fuzz_u8 rs) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rs))) mod 4)
                  (snd (fuzz_u8 (snd (fuzz_u8 rs)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x130a8) fc None m1 (seg_rom rsegs)).
Proof.
  intros rs ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hrs MB C10 -> -> -> -> ->.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  rewrite <- Hrs in P7.
  (* 0x130a8 beqz s2: no input byte *)
  step.
  destruct rs as [|b0 [|b1 r2]]; cbn [fuzz_u8 fst snd].
  - (* 0x130dc sd zero,0x90(sp) ; mv s5,zero ; j 0x13108 *)
    br true. fst8 0x90 C90. step. step.
    eapply hdr_ok;
      [ lia | lia | exists (length rest); split; [lia | rewrite skipn_all; reflexivity]
      | exact MB | exact C10 | exact C90 | reflexivity | reflexivity | reflexivity
      | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia | reflexivity | reflexivity ].
  - (* one byte: 0x130ac addi a0,s6,1 ; addi a1,zero,1 ; bltu a1,a0 (the cursor's check, not taken) *)
    br false. step. step. step. br true.
    (* 0x130bc lbu a2,0(s6) ; andi a2,a2,7 ; sd a2,0x90(sp) ; bne s2,a1 *)
    assert (HR0 : ov_read_bytes rsegs m1 (wa src) 1 = Some [b0]).
    { replace (wa src) with (wa (src + Z.of_nat 0)) by (f_equal; lia).
      eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity]. }
    step. clear HR0. step. rewrite Post.land7. fst8 0x90 C90. step. br false.
    (* 0x130cc mv s2,zero ; mv s5,zero ; mv s6,a0 ; j 0x13108 *)
    step. step. step. step.
    eapply hdr_ok;
      [ lia | lia | exists (length rest); split; [lia | rewrite skipn_all; reflexivity]
      | exact MB | exact C10 | exact C90 | reflexivity | reflexivity | reflexivity
      | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia | reflexivity | reflexivity ].
  - (* two bytes or more *)
    br false. step. step. step. br true.
    assert (HR0 : ov_read_bytes rsegs m1 (wa src) 1 = Some [b0]).
    { replace (wa src) with (wa (src + Z.of_nat 0)) by (f_equal; lia).
      eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity]. }
    step. clear HR0. step. rewrite Post.land7. fst8 0x90 C90. step. br true.
    (* 0x130e8 addi a0,a0,1 ; addi a1,zero,1 ; bltu a1,a0 (the cursor's check, not taken) *)
    step. step. step. br true.
    (* 0x130f8 lbu a0,1(s6) ; addi s2,s2,-2 ; addi s6,s6,2 ; andi s5,a0,3 *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (HR1 : ov_read_bytes rsegs mm (wa (src + 1)) 1 = Some [b1])
          by (change (src + 1) with (src + Z.of_nat 1); eapply MBr_byte; [exact MB | rewrite <- Hrs; reflexivity])
    end.
    step. clear HR1. step. step. step. rewrite land3.
    eapply hdr_ok;
      [ lia | lia | exists 2%nat; split; [rewrite <- Hrs; cbn [length]; lia | rewrite <- Hrs; reflexivity]
      | exact MB | exact C10 | exact C90 | reflexivity | f_equal; cbn [length]; lia | reflexivity
      | f_equal; unfold cur; rewrite <- Hrs; cbn [length]; lia | reflexivity | reflexivity ].
Qed.

(** ** 0x13090: the NULL test of the block (fuzz_headamp.c:320) and memset(pp, 0, 19744) (pod.h:384) *)
Lemma pre_ok : forall (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (junk : list byte),
  memset_contract ->
  a0 = Z_to_bv 64 pp -> pp <> 0 -> s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) ->
  s3 = Z_to_bv 64 cap ->
  bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
  s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
  rw_cells rsegs m pp [CB (Z.to_nat POD_PROPS) junk] -> mem_inv rsegs m ->
  MBr sp m rest src pp lo junk m ->
  evt rsegs (PreQ (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4)
                  (snd (fuzz_u8 (snd (fuzz_u8 rest)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 junk
    MSET -> Hpp0 -> -> -> C10 -> -> HBLK HMI MB.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (MBr_bounds _ _ _ _ _ _ _ _ MB) as (_ & _ & HLJ).
  unfold HEAD_BUILD.
  (* 0x13090 bnez a0: the block is not NULL *)
  step. br true.
  (* 0x13098 mv s8,a0 ; mv a1,zero ; mv a2,s1 ; jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET; [ rewrite !unsigned_lit by qlia; exact HBLK | exact HMI ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU & WM & MI & RW).
  rewrite !unsigned_lit in MU, RW by qlia.
  rewrite (ret_pc_even 0x130a8) by lia.
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
  assert (C10' : bytes_at rsegs m1 (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl))).
  { apply (bytes_at_transport rsegs _ m m1 _ _ C10 MU). cbn [disjoint_from]. rewrite length_le8.
    split; [right; qlia | exact I]. }
  clear MB C10 MU WM RW.
  eapply (reads_ok rest); [ reflexivity | exact MB1 | exact C10' | reflexivity | reflexivity | reflexivity
                          | reflexivity | reflexivity ].
Qed.

End Pre.

Theorem pre_holds : memset_c.memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (rest junk : list byte) (fl src pp lo cap : Z),
    a0 = Z_to_bv 64 pp -> pp <> 0 -> pp mod 16 = 0 ->
    s6 = Z_to_bv 64 src -> s2 = Z_to_bv 64 (Z.of_nat (length rest)) -> s3 = Z_to_bv 64 cap -> 0 <= fl < 256 ->
    bytes_at rsegs m (bv_unsigned sp + 0x10) (le8 (Z_to_bv 64 fl)) ->
    s1 = Z_to_bv 64 POD_PROPS -> s0 = Z_to_bv 64 0x5000 ->
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
          POSTH sp gp tp F fc m rest fl src pp lo cap (fst (fuzz_u8 rest) mod 8) [] (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms) \/
         (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4 <> 0 /\
          PROPH sp gp tp F fc m rest fl src pp lo cap (fst (fuzz_u8 rest) mod 8) (fst (fuzz_u8 (snd (fuzz_u8 rest))) mod 4) []
                (snd (fuzz_u8 (snd (fuzz_u8 rest)))) ms))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 HEAD_BUILD) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rest junk fl src pp lo cap Ha0 Hpp0 HPPA Hs6 Hs2 Hs3 HFL C10 Hs1 Hs0 HSRC0 HSRC HBLK HROM HDJ HLO1 HLO2
    HST HMID HSPA HSROM HRELRO HMI.
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
  exact (pre_ok sp gp tp F fc m rest fl src pp lo cap HOK HPPA ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 junk MSET Ha0 Hpp0 Hs6 Hs2 Hs3 C10 Hs1 Hs0 HBLK HMI MB).
Qed.
