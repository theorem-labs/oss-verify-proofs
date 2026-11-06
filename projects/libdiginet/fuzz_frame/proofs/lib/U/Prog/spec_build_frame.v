(* the walk of spec_build_frame in fuzz_frame.ubsan proves spec_build_frame_contract from the memset and memcpy contracts, with none of its UBSan trap branches taken. *)
(* Walk of spec_build_frame (fuzz/spec.h:228-247 at 835f336c) in fuzz_frame.ubsan, 0x136a8 .. 0x13944:
   the 96-byte frame; memset of the max (60, 30 + len) bytes at out; memcpy of the two MACs; the
   18 header bytes (0x885F, numbytes, the sum of the loop 0x137bc .. 0x137e4 or 0, send, ack,
   retry, cmd, ncmds); then, when len is not 0, the tail call to memcpy of the body at 0x13904.
   Each UBSan check branches to the trap at 0x13940 only when out + k wraps past 2^64 (k <= 30)
   or, in the sum loop, when body + i wraps or body is 0; out + frame_len <= 2^64, body + len <=
   2^64 and body <> 0 decide each of them not taken.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import memset_c memcpy_c spec_build_frame_c.
Import ListNotations.
Open Scope Z_scope.

(* A hypothesis that the step machinery and lia do not read. *)
Definition sbf_hid (P : Prop) : Prop := P.

(** * Lists and bytes *)

Lemma sbf_firstn1_skipn : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] x N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma sbf_rd1 : forall m a l (i : nat) x, bytes_at rsegs m a l -> nth_error l i = Some x ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [x].
Proof.
  intros m a l i x BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m a l i 1 BL ltac:(lia)). f_equal. apply sbf_firstn1_skipn. exact N.
Qed.

Lemma sbf_sum_step : forall bb i x, nth_error bb i = Some x ->
  sum_bytes (firstn (S i) bb) = sum_bytes (firstn i bb) + bv_unsigned (zxb x).
Proof.
  intros bb i x N. assert (Hi : (i < length bb)%nat) by (apply nth_error_Some; congruence).
  rewrite sum_bytes_firstn_S by exact Hi. unfold at8. erewrite nth_error_nth by exact N.
  pose proof (bz_range x) as R. unfold zxb. unfold bz in *. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma sbf_seqz_nz : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma sbf_snez : forall z, 0 < z < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. unfold v_sltu, c_ltu. rewrite bv_ltu_Z. rewrite (unsigned_lit 0), (unsigned_lit z) by lia.
  replace (0 <? z) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* The byte a sb stores. *)
Lemma sbf_le1_b8 : forall (v : word) z, b8 (bv_unsigned v) = b8 z -> le1 v = [b8 z].
Proof. intros v z H. change (le1 v) with [b8 (bv_unsigned v)]. rewrite H. reflexivity. Qed.

Lemma sbf_le1_lit : forall (v : word) z, bv_unsigned v mod 2^8 = z mod 2^8 -> le1 v = [b8 z].
Proof. intros v z H. apply sbf_le1_b8. rewrite <- (b8_mod (bv_unsigned v)), <- (b8_mod z), H. reflexivity. Qed.

Lemma sbf_b8_shr : forall u x k w, 0 <= u < 2^64 -> 0 <= k -> k + 8 <= w -> u mod 2^w = x mod 2^w ->
  b8 (bv_unsigned (Z_to_bv 64 (Z.shiftr u k))) = b8 (x / 2^k).
Proof.
  intros u x k w Hu Hk Hw H.
  assert (P : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= u / 2^k <= u) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]).
  rewrite unsigned_lit by lia.
  rewrite <- (b8_div_mod u k w) by lia. rewrite <- (b8_div_mod x k w) by lia. rewrite H. reflexivity.
Qed.

Lemma sbf_swrap32 : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma sbf_sx32_mod : forall x, 0 <= x < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 x)) mod 2^32 = x mod 2^32.
Proof.
  intros x Hx. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  rewrite mod_mod_pow2 by lia. rewrite sbf_swrap32. Z.div_mod_to_equations. lia.
Qed.

Lemma sbf_le1_sx32 : forall x k, 0 <= x < 2^32 -> 0 <= k <= 24 ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 x))) k)) = [b8 (x / 2^k)].
Proof.
  intros x k Hx Hk. apply sbf_le1_b8.
  apply (sbf_b8_shr _ x k 32); [apply u64_range | lia | lia | apply sbf_sx32_mod; lia].
Qed.

Lemma sbf_le1_sx32_0 : forall x, 0 <= x < 2^32 -> le1 (sx32 (Z_to_bv 64 x)) = [b8 x].
Proof.
  intros x Hx. apply sbf_le1_b8. rewrite <- (b8_mod_w (bv_unsigned (sx32 (Z_to_bv 64 x))) 32) by lia.
  rewrite sbf_sx32_mod by lia. apply b8_mod_w. lia.
Qed.

Lemma sbf_le1_eq : forall z z', 0 <= z < 2^64 -> z = z' -> le1 (Z_to_bv 64 z) = [b8 z'].
Proof. intros z z' Hz <-. apply sbf_le1_b8. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma sbf_le1_srl : forall z z' k, 0 <= z < 2^64 -> 0 <= k -> z = z' ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 z)) k)) = [b8 (z' / 2^k)].
Proof.
  intros z z' k Hz Hk <-. apply sbf_le1_b8. rewrite (unsigned_lit z) by lia.
  apply (sbf_b8_shr z z k (k + 8)); [lia | lia | lia | reflexivity].
Qed.

(* The two bytes of the sum: the binary adds in 64 bits and stores the low 16 bits. *)
Lemma sbf_le1_sum_hi : forall S h, S mod 2^16 = h ->
  le1 (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 S)) 8)) = [b8 (h / 2^8)].
Proof.
  intros S h H. apply sbf_le1_b8.
  apply (sbf_b8_shr _ h 8 16); [apply u64_range | lia | lia |].
  rewrite unsigned_lit_wrap. rewrite mod_mod_pow2 by lia. rewrite <- H. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma sbf_le1_sum_lo : forall S h, S mod 2^16 = h -> le1 (Z_to_bv 64 S) = [b8 h].
Proof.
  intros S h H. apply sbf_le1_b8. rewrite unsigned_lit_wrap.
  rewrite (b8_mod_w S 64) by lia. rewrite <- (b8_mod_w S 16) by lia. rewrite H. reflexivity.
Qed.

(** * Byte blocks *)

Lemma sbf_split : forall m A B (k1 k2 : nat) l1 l2,
  B = A + Z.of_nat k1 -> length l1 = k1 ->
  rw_cells rsegs m A [CB (k1 + k2) (l1 ++ l2)] ->
  rw_cells rsegs m A [CB k1 l1] /\ rw_cells rsegs m B [CB k2 l2].
Proof.
  intros m A B k1 k2 l1 l2 -> L1 [[[Hl _] Hb] (Ha & Hn & Hw)].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in Hl, Hb, Hn, Hw.
  rewrite app_nil_r in Hb. rewrite length_app in Hl.
  apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2]. rewrite L1 in Hb2.
  split.
  - split; [split|].
    + cbn. split; [exact L1 | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
    + split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. apply Hw.
      cbn [cells_size csize] in Hi. lia.
  - split; [split|].
    + cbn. split; [lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
    + split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. rewrite <- Z.add_assoc. apply Hw.
      cbn [cells_size csize] in Hi. lia.
Qed.

Lemma sbf_join : forall m A B (k1 k2 : nat) l1 l2,
  B = A + Z.of_nat k1 ->
  rw_cells rsegs m A [CB k1 l1] -> rw_cells rsegs m B [CB k2 l2] ->
  rw_cells rsegs m A [CB (k1 + k2) (l1 ++ l2)].
Proof.
  intros m A B k1 k2 l1 l2 -> [[[L1 _] Hb1] (Ha1 & Hn1 & Hw1)] [[[L2 _] Hb2] (Ha2 & Hn2 & Hw2)].
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in L1, L2, Hb1, Hb2, Hn1, Hn2, Hw1, Hw2.
  rewrite app_nil_r in Hb1, Hb2.
  split; [split|].
  - cbn. split; [rewrite length_app; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hb1|].
    rewrite L1. exact Hb2.
  - split; [lia|]. split; [cbn [cells_size csize]; lia|]. intros i Hi. cbn [cells_size csize] in Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat k1)) as [Hlt|Hge].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat k1 + (i - Z.of_nat k1)) by lia. apply Hw2. lia.
Qed.

(* The block of memset at out, cut at the fields of the frame: the MACs, the 18 header bytes,
   the body and the zero pad. *)
Lemma sbf_slots : forall m A (N Lb : nat) z,
  N = (6 + (6 + (18 + (Lb + (30 - Lb)))))%nat ->
  rw_cells rsegs m A [CB N (repeat z N)] ->
  rw_cells rsegs m A [CB 6 (repeat z 6)] /\ rw_cells rsegs m (A + 6) [CB 6 (repeat z 6)] /\
  rw_cells rsegs m (A + 12) [CB 18 (repeat z 18)] /\ rw_cells rsegs m (A + 30) [CB Lb (repeat z Lb)] /\
  rw_cells rsegs m (A + 30 + Z.of_nat Lb) [CB (30 - Lb) (repeat z (30 - Lb))].
Proof.
  intros m A N Lb z -> H0. rewrite !repeat_app in H0.
  destruct (sbf_split m A (A + 6) 6 _ (repeat z 6) _ eq_refl (repeat_length z 6) H0) as [H1 R1].
  destruct (sbf_split m (A + 6) (A + 12) 6 _ (repeat z 6) _ ltac:(lia) (repeat_length z 6) R1) as [H2 R2].
  destruct (sbf_split m (A + 12) (A + 30) 18 _ (repeat z 18) _ ltac:(lia) (repeat_length z 18) R2) as [H3 R3].
  destruct (sbf_split m (A + 30) (A + 30 + Z.of_nat Lb) Lb _ (repeat z Lb) _ eq_refl (repeat_length z Lb) R3)
    as [H4 H5].
  tauto.
Qed.

Lemma sbf_merge_all : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge rsegs m A [] cs []) as M. rewrite app_nil_r in M. exact (M H).
Qed.

(* The five blocks at out make the frame. *)
Lemma sbf_frame : forall m out dmac smac send ack retry cmd ncmds bb (zs : bool) hdr,
  hdr = put16 0x885f ++ put16 (16 + Z.of_nat (length bb)) ++ put16 (if zs then 0 else spec_sum bb) ++
        put32 send ++ put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds] ->
  rw_cells rsegs m out [CB 6 dmac] ->
  rw_cells rsegs m (out + 6) [CB 6 smac] ->
  rw_cells rsegs m (out + 12) [CB 18 hdr] ->
  rw_cells rsegs m (out + 30) [CB (length bb) bb] ->
  rw_cells rsegs m (out + 30 + Z.of_nat (length bb)) [CB (30 - length bb) (repeat (b8 0) (30 - length bb))] ->
  rw_cells rsegs m out [CB (Z.to_nat (frame_len (length bb))) (build_frame dmac smac send ack retry cmd ncmds bb zs)].
Proof.
  intros m out dmac smac send ack retry cmd ncmds bb zs hdr Eh H1 H2 H3 H4 H5. subst hdr.
  pose proof (sbf_join m (out + 30) (out + 30 + Z.of_nat (length bb)) (length bb) _ _ _ eq_refl H4 H5) as H45.
  pose proof (sbf_join m (out + 12) (out + 30) 18 _ _ _ ltac:(lia) H3 H45) as H3'.
  pose proof (sbf_join m (out + 6) (out + 12) 6 _ _ _ ltac:(lia) H2 H3') as H2'.
  pose proof (sbf_join m out (out + 6) 6 _ _ _ ltac:(lia) H1 H2') as H1'.
  replace (Z.to_nat (frame_len (length bb)))
    with (6 + (6 + (18 + (length bb + (30 - length bb)))))%nat by (unfold frame_len; lia).
  unfold build_frame. exact H1'.
Qed.

(* The stack from lo to hi after a run that writes only the frame and out, both of which hold
   readable bytes after it. *)
Lemma sbf_stk_patch : forall m m' lo hi f1 f2 a b,
  stk rsegs m lo hi -> munch [(f1, f2); (a, b)] m m' -> wmono rsegs m m' ->
  stk rsegs m' f1 f2 -> stk rsegs m' a b -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi f1 f2 a b (H1 & H2 & H) MU WM (F1 & F2 & HF) (A1 & A2 & HA).
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (Z.le_gt_cases f1 x) as [X1|X1]; [destruct (Z.lt_ge_cases x f2) as [X2|X2]|].
  - apply HF. lia.
  - destruct (Z.le_gt_cases a x) as [Y1|Y1]; [destruct (Z.lt_ge_cases x b) as [Y2|Y2]|].
    + apply HA. lia.
    + destruct (H x Hx) as [Hw (bx & Hb)]. split; [apply WM; exact Hw|]. exists bx. unfold mrd in *.
      rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
    + destruct (H x Hx) as [Hw (bx & Hb)]. split; [apply WM; exact Hw|]. exists bx. unfold mrd in *.
      rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
  - destruct (Z.le_gt_cases a x) as [Y1|Y1]; [destruct (Z.lt_ge_cases x b) as [Y2|Y2]|].
    + apply HA. lia.
    + destruct (H x Hx) as [Hw (bx & Hb)]. split; [apply WM; exact Hw|]. exists bx. unfold mrd in *.
      rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
    + destruct (H x Hx) as [Hw (bx & Hb)]. split; [apply WM; exact Hw|]. exists bx. unfold mrd in *.
      rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

(** * Tactics *)

Ltac sbf_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.
Ltac sbf_usub_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) in H by lia end.
Ltac sbf_tonat_in H :=
  repeat match type of H with context [Z.to_nat ?z] =>
    is_Zlit z; let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v in H end.

(* A branch whose condition is closed. *)
Ltac sbf_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* A branch whose condition the context decides. *)
Ltac sbf_take v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; sbf_usub; fold_lit_ux; solve_cond_rec]
  end.

Ltac sbf_cur k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

(* The register map of the goal, a tree after the steps, written back as mkR. *)
Ltac sbf_to_mkR :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    lazymatch R with
    | TNode
        (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7)
                         (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3)
                  (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
           (Some ?x1)
           (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty))
                  (Some ?x5)
                  (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
        None
        (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty))
                      (Some ?x4)
                      (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty)))
               (Some ?x2)
               (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty))
                      (Some ?x6)
                      (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))) =>
        change R with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                           x24 x25 x26 x27 x28 x29 x30 x31)
    end
  end.

(* post_call, with the addresses and sizes of the callee's post as numbers. *)
Ltac sbf_post mm :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  sbf_usub_in PO; sbf_tonat_in PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ mm ?m' =>
      transport_after_call rsegs mm m' MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs mm |- _ => clear H end;
      try clear mm
  end;
  try destruct_ands PO;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).

(* A byte store whose le1 the equation E rewrites; a store of a literal byte, the low 8 bits of z. *)
Ltac sbf_sb E := step; rewrite E; mem_after_store.
Ltac sbf_sbl z := step; rewrite (sbf_le1_lit _ z) by (vm_compute; reflexivity); mem_after_store.

(** * 0x13710: a2 = max 60 (30 + len) *)

Lemma sbf_max : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L n : Z),
  0 <= L -> L + 30 < 2^64 -> n = Z.max 60 (30 + L) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 60) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3
                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13718) fc None m (seg_rom rsegs)) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 60) (Z_to_bv 64 (L + 30)) a3 a4 a5 a6 a7 s2 s3
                     s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13710) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L n
    HL0 HL HN H.
  destruct (Z.ltb_spec 60 (L + 30)) as [C|C].
  - step. sbf_take true. replace (L + 30) with n by lia. exact H.
  - step. sbf_take false. step. assert (E : n = 60) by lia. rewrite E in H. exact H.
Qed.

(** * The sum loop, 0x137bc .. 0x137e4 *)

Section Sum.
Variables (ra sp gp tp t0 t1 t2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (body : Z)
  (bb : list byte).
Hypothesis BB : bytes_at rsegs m body bb.
Hypothesis HB0 : 0 < body.

Local Notation ST pc a0 a2 a3 a4 a5 :=
  (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length bb))) (Z_to_bv 64 body) a0 (Z_to_bv 64 1) a2 a3
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma sbf_sum_loop : forall k (i : nat) (a5 : word) (v0 v2 v3 v4 : Z),
  (i + S k = length bb)%nat -> v0 = sum_bytes (firstn i bb) -> v2 = body + Z.of_nat i ->
  v3 = body + Z.of_nat i -> v4 = Z.of_nat (length bb) - Z.of_nat i ->
  (forall a2' a3' a4' a5', evt rsegs Q (ST 0x137e8 (Z_to_bv 64 (sum_bytes bb)) a2' a3' a4' a5')) ->
  evt rsegs Q (ST 0x137bc (Z_to_bv 64 v0) (Z_to_bv 64 v2) (Z_to_bv 64 v3) (Z_to_bv 64 v4) a5).
Proof.
  pose proof (bytes_at_bound _ _ _ _ BB) as HB.
  induction k as [|k IH]; intros i a5 v0 v2 v3 v4 Hk -> -> -> -> K.
  all: destruct (nth_error bb i) as [x|] eqn:Nx; [| apply nth_error_None in Nx; lia].
  all: pose proof (sbf_rd1 m body bb i x BB Nx) as R.
  (* 0x137bc: bltu a3, s1 (body + i wraps) *)
  all: step; sbf_take false.
  (* 0x137c0 .. 0x137c8: seqz, xor, beqz a5 ((body <> 0) = (body + i = 0)) *)
  all: step; rewrite (sbf_seqz_nz (body + Z.of_nat i)) by lia.
  all: step; step; sbf_brc.
  (* 0x137cc: beqz s1 *)
  all: step; sbf_take false.
  (* 0x137d0 .. 0x137e4: the byte, the counters, the sum, bnez a4 *)
  all: do 6 step.
  - sbf_take false. rewrite <- (sbf_sum_step bb i x Nx), (firstn_all2 (n := S i)) by lia. apply K.
  - sbf_take true.
    eapply (IH (S i)); [lia | symmetry; apply sbf_sum_step; exact Nx | lia | lia | lia | exact K].
Qed.

End Sum.

(** * The walk *)

Theorem spec_build_frame_holds : memset_contract -> memcpy_contract -> spec_build_frame_contract.
Proof.
  intros MSET MCPY. unfold spec_build_frame_contract, SPEC_BUILD_FRAME, SBF_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m out dst src body zs lo send ack
    retry cmd ncmds dmac smac bb oj Hsend Hack Hretry Hcmd Hncmds Hzs Hbody Ld BD Ls BS BB Loj RWo Ddo Dso Dbo
    ST Hlo Dfo Dfd Dfs Dfb MI.
  unfold memset_contract, MEMSET in MSET. unfold memcpy_contract in MCPY.
  pose proof (u64_range sp) as Rsp.
  remember (frame_len (length bb)) as n eqn:En.
  assert (Hn : n = Z.max 60 (30 + Z.of_nat (length bb))) by (rewrite En; reflexivity).
  assert (Eoj : length oj = Z.to_nat n) by lia.
  rewrite Loj in Ddo, Dso, Dbo, Dfo |- *. rewrite Eoj in RWo.
  pose proof (rw_cells_bound _ _ _ _ RWo) as RWb. cbn [cells_size csize] in RWb.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (bytes_at_bound _ _ _ _ BD) as BDb. pose proof (bytes_at_bound _ _ _ _ BS) as BSb.
  rewrite Ld in BDb. rewrite Ls in BSb.
  assert (HL30 : Z.of_nat (length bb) + 30 < 2^64) by (destruct Dbo; lia).
  destruct (stk_carve rsegs m lo (bv_unsigned sp) 96 ST ltac:(lia)) as [_ [junk FR]].
  replace (bv_unsigned sp - Z.of_nat 96) with (bv_unsigned sp + -96) in FR by lia.
  pose proof (proj1 ST) as Hlo0.
  (* hide what the steps do not read *)
  assert (HST : sbf_hid (stk rsegs m lo (bv_unsigned sp))) by exact ST. clear ST.
  assert (HBD : sbf_hid (bytes_at rsegs m dst dmac)) by exact BD. clear BD.
  assert (HBS : sbf_hid (bytes_at rsegs m src smac)) by exact BS. clear BS.
  assert (HBB : sbf_hid (bytes_at rsegs m body bb)) by exact BB. clear BB.
  assert (HDdo : sbf_hid (out + n <= dst \/ dst + 6 <= out)) by exact Ddo. clear Ddo.
  assert (HDso : sbf_hid (out + n <= src \/ src + 6 <= out)) by exact Dso. clear Dso.
  assert (HDbo : sbf_hid (out + n <= body \/ body + Z.of_nat (length bb) <= out)) by exact Dbo. clear Dbo.
  assert (HDfd : sbf_hid (dst + 6 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= dst)) by exact Dfd. clear Dfd.
  assert (HDfs : sbf_hid (src + 6 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= src)) by exact Dfs. clear Dfs.
  assert (HDfb : sbf_hid (body + Z.of_nat (length bb) <= bv_unsigned sp - 96 \/ bv_unsigned sp <= body))
    by exact Dfb. clear Dfb.
  assert (HZS : sbf_hid (zs = 0 \/ zs = 1)) by exact Hzs. clear Hzs.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (out, out + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x136a8 .. 0x1370c: the frame, the saves, the moves, a2 = len + 30, a1 = 60 *)
  do 26 step.
  eapply sbf_max with (n := n); [lia | lia | lia |].
  (* 0x13718 .. 0x13720: memset (out, 0, n) *)
  do 3 step.
  sbf_cur ltac:(fun mm => eapply evt_cut; [eapply MSET with (junk := oj) | sbf_post mm]).
  1: { sbf_usub. exact RWo. }
  1: { assumption. }
  lazymatch goal with H : rw_cells rsegs _ out [CB (Z.to_nat n) (repeat ?z _)] |- _ =>
    destruct (sbf_slots _ out (Z.to_nat n) (length bb) z ltac:(lia) H) as (W1 & W2 & W3 & W4 & W5);
    clear H end.
  (* 0x13724 .. 0x13730: memcpy (out, dst, 6) *)
  do 4 step.
  sbf_cur ltac:(fun mm => eapply evt_cut; [eapply MCPY with (src := dmac) | sbf_post mm]).
  1: { sbf_usub. unfold sbf_hid in HBD, HDdo, HDfd. eapply bytes_at_transport; [exact HBD | exact MU |].
       cbn [disjoint_from]. rewrite Ld. split; [lia | split; [lia | exact I]]. }
  1: { sbf_usub. rewrite Ld. reflexivity. }
  1: { sbf_usub. exact W1. }
  1: { sbf_usub. unfold sbf_hid in HDdo. lia. }
  1: { assumption. }
  lazymatch goal with H : bytes_at rsegs _ dst dmac |- _ => clear H end.
  lazymatch goal with H : rw_cells rsegs _ out [CB _ dmac] |- _ => rename H into V1 end.
  (* 0x13734 .. 0x13738: out + 6 wraps *)
  step. step. sbf_take false.
  (* 0x1373c .. 0x13748: memcpy (out + 6, src, 6) *)
  do 4 step.
  sbf_cur ltac:(fun mm => eapply evt_cut; [eapply MCPY with (src := smac) | sbf_post mm]).
  1: { sbf_usub. unfold sbf_hid in HBS, HDso, HDfs. eapply bytes_at_transport; [exact HBS | exact MU |].
       cbn [disjoint_from]. rewrite Ls. split; [lia | split; [lia | exact I]]. }
  1: { sbf_usub. rewrite Ls. reflexivity. }
  1: { sbf_usub. exact W2. }
  1: { sbf_usub. unfold sbf_hid in HDso. lia. }
  1: { assumption. }
  lazymatch goal with H : bytes_at rsegs _ src smac |- _ => clear H end.
  lazymatch goal with H : rw_cells rsegs _ (out + 6) [CB _ smac] |- _ => rename H into V2 end.
  (* 0x1374c .. 0x13750: out + 12 wraps *)
  step. step. sbf_take false.
  (* 0x13754 .. 0x13764: 0x88 at out + 12 *)
  do 3 step. sbf_sbl (0x885f / 2^8).
  step. sbf_take false.
  (* 0x13768 .. 0x13774: 0x5f at out + 13 *)
  do 2 step. sbf_sbl 0x885f.
  step. sbf_take false.
  (* 0x13778 .. 0x1378c: (len + 16) >> 8 at out + 14 *)
  do 4 step.
  sbf_sb (sbf_le1_srl (Z.of_nat (length bb) + 16) (16 + Z.of_nat (length bb)) 8 ltac:(lia) ltac:(lia) ltac:(lia)).
  step. sbf_take false.
  (* 0x13790 .. 0x13798: len + 16 at out + 15 *)
  step. sbf_sb (sbf_le1_eq (Z.of_nat (length bb) + 16) (16 + Z.of_nat (length bb)) ltac:(lia) ltac:(lia)).
  step. sbf_take false.
  (* 0x1379c: a0 = 0 *)
  step.
  (* From 0x137e8 on, with the sum S in a0 (a1 .. a5 as the path left them). *)
  sbf_to_mkR.
  lazymatch goal with
  | |- evt _ ?Q (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 _ _ _ _ _ _ ?xa6 ?xa7 ?xs2 ?xs3 ?xs4 ?xs5 ?xs6
                       ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc ?xrv ?mm ?xro) =>
    assert (AFTER : forall (S : Z) (y1 y2 y3 y4 y5 : word),
      S mod 2^16 = (if zs =? 1 then 0 else spec_sum bb) ->
      evt rsegs Q (MS (mkR xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 S) y1 y2 y3 y4 y5 xa6 xa7 xs2 xs3 xs4
                           xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                      xF (Z_to_bv 64 0x137e8) xfc xrv mm xro))
  end.
  { intros S y1 y2 y3 y4 y5 HS.
    (* 0x137e8 .. 0x137f8: the high byte of the sum at out + 16 *)
    do 3 step. sbf_sb (sbf_le1_sum_hi S _ HS). step. sbf_take false.
    (* 0x137fc .. 0x13804: the low byte at out + 17 *)
    step. sbf_sb (sbf_le1_sum_lo S _ HS). step. sbf_take false.
    (* 0x13808 .. 0x13844: send at out + 18 .. 21 *)
    do 3 step. sbf_sb (sbf_le1_sx32 send 24 Hsend ltac:(lia)). step. sbf_take false.
    do 2 step. sbf_sb (sbf_le1_sx32 send 16 Hsend ltac:(lia)). step. sbf_take false.
    do 2 step. sbf_sb (sbf_le1_sx32 send 8 Hsend ltac:(lia)). step. sbf_take false.
    step. sbf_sb (sbf_le1_sx32_0 send Hsend). step. sbf_take false.
    (* 0x13848 .. 0x13884: ack at out + 22 .. 25 *)
    do 3 step. sbf_sb (sbf_le1_sx32 ack 24 Hack ltac:(lia)). step. sbf_take false.
    do 2 step. sbf_sb (sbf_le1_sx32 ack 16 Hack ltac:(lia)). step. sbf_take false.
    do 2 step. sbf_sb (sbf_le1_sx32 ack 8 Hack ltac:(lia)). step. sbf_take false.
    step. sbf_sb (sbf_le1_sx32_0 ack Hack). step. sbf_take false.
    (* 0x13888 .. 0x138a4: retry at out + 26, 27 *)
    do 3 step. sbf_sb (sbf_le1_srl retry retry 8 ltac:(lia) ltac:(lia) eq_refl). step. sbf_take false.
    step. sbf_sb (sbf_le1_eq retry retry ltac:(lia) eq_refl). step. sbf_take false.
    (* 0x138a8 .. 0x138b4: cmd at out + 28, ncmds at out + 29 *)
    step. sbf_sb (sbf_le1_eq cmd cmd ltac:(lia) eq_refl). step. sbf_take false.
    sbf_sb (sbf_le1_eq ncmds ncmds ltac:(lia) eq_refl).
    lazymatch goal with H : rw_cells rsegs _ (out + 12) _ |- _ => apply sbf_merge_all in H; rename H into V3 end.
    (* 0x138b8: beqz s0 (len = 0) *)
    step.
    destruct (Z.eq_dec (Z.of_nat (length bb)) 0) as [L0|L0].
    (* len = 0, 0x13908 .. 0x1393c: the restores, ret *)
    1: (sbf_take true; do 14 step;
        assert (E0 : repeat (Z_to_bv 8 (0 mod 256)) (length bb) = bb)
          by (destruct bb; [reflexivity | cbn in L0; lia]);
        rewrite E0 in W4; rename W4 into V4).
    (* len <> 0, 0x138bc .. 0x138c0: out + 30 wraps; 0x138c4 .. 0x13904: the arguments, the
       restores, the tail call to memcpy (out + 30, body, len) *)
    2: (sbf_take false; step; step; sbf_take false; do 17 step).
    2: sbf_cur ltac:(fun mm => eapply evt_cut; [eapply MCPY with (src := bb) | sbf_post mm]).
    2: { sbf_usub. unfold sbf_hid in HBB, HDbo, HDfb. eapply bytes_at_transport; [exact HBB | exact MU |].
         cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
    2: { sbf_usub. rewrite Nat2Z.id. reflexivity. }
    2: { sbf_usub. rewrite Nat2Z.id. exact W4. }
    2: { sbf_usub. unfold sbf_hid in HDbo. lia. }
    2: { assumption. }
    2: (lazymatch goal with H : bytes_at rsegs _ body bb |- _ => clear H end;
        lazymatch goal with H : rw_cells rsegs _ (out + 30) [CB _ bb] |- _ =>
          rewrite Nat2Z.id in H; rename H into V4 end).
    (* the post *)
    all: apply evt_done; do 16 eexists; split; [reflexivity|].
    all: lazymatch goal with |- munch _ _ ?mf /\ _ =>
      assert (OUT : rw_cells rsegs mf out [CB (Z.to_nat (frame_len (length bb)))
                      (build_frame dmac smac send ack retry cmd ncmds bb (zs =? 1))])
        by (eapply sbf_frame; [reflexivity | exact V1 | exact V2 | exact V3 | exact V4 | exact W5]);
      pose proof (stk_of_rw_cells rsegs _ _ _ FR) as SF;
      pose proof (stk_of_rw_cells rsegs _ _ _ OUT) as SO
    end.
    all: cbn [cells_size csize Nat.add] in SF, SO.
    all: replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in SF by lia.
    all: replace (bv_unsigned sp + -96) with (bv_unsigned sp - 96) in SF by lia.
    all: rewrite <- En in SO; replace (out + Z.of_nat (Z.to_nat n + 0)) with (out + n) in SO by lia.
    all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
    all: split; [eapply (sbf_stk_patch m _ lo (bv_unsigned sp) (bv_unsigned sp - 96) (bv_unsigned sp) out (out + n));
                 [exact HST | exact MU | exact WM | exact SF | exact SO] |].
    all: rewrite Eoj, En; exact OUT. }
  (* 0x137a0: beqz s0 (len = 0: the sum is 0) *)
  step.
  destruct (Z.eq_dec (Z.of_nat (length bb)) 0) as [L0|L0].
  { sbf_take true. apply AFTER.
    assert (E0 : bb = []) by (destruct bb; [reflexivity | cbn in L0; lia]).
    rewrite E0. destruct (zs =? 1); reflexivity. }
  sbf_take false.
  (* 0x137a4: bnez s8 (zero_sum: the sum is 0) *)
  step. unfold sbf_hid in HZS. destruct HZS as [Z0|Z1]; subst zs.
  2: { sbf_brc. apply AFTER. reflexivity. }
  sbf_brc.
  (* 0x137a8 .. 0x137b8: a0 = 0, a1 = (body <> 0), a2 = a3 = body, a4 = len; the loop *)
  do 5 step. rewrite (sbf_snez body) by lia.
  eapply sbf_sum_loop with (k := (length bb - 1)%nat) (i := 0%nat).
  1: { unfold sbf_hid in HBB, HDbo, HDfb. eapply bytes_at_transport; [exact HBB | exact MU |].
       cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  1: lia.
  1: lia.
  1: reflexivity.
  1-3: lia.
  intros a2' a3' a4' a5'. apply AFTER. rewrite spec_sum_eq. reflexivity.
Qed.
