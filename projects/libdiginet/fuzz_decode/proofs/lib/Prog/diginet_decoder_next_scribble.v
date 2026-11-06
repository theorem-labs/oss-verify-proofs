(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* diginet_decoder_next in fuzz_decode.plain, the scribble case of the sysex switch (fn 0x40, from the jump target 0x1423c): address,
   len, the memcpy of the characters to ev->text (0x14274) and the NUL after them (diginet_decode.c:81-89).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnLayout diginet_cursor_init_c
  memcpy_c diginet_decoder_next_c diginet_decoder_next_bridge diginet_decoder_next_lib.
Import ListNotations.
Open Scope Z_scope.

(* ---- lists ---- *)

Lemma len_repeat : forall (A : Type) (a : A) n, length (repeat a n) = n.
Proof. intros A a n. induction n as [|n IH]; cbn [repeat length]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma repeat_add : forall (A : Type) (a : A) n k, repeat a (n + k) = repeat a n ++ repeat a k.
Proof. intros A a n k. induction n as [|n IH]; cbn [repeat app Nat.add]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_repeat_d : forall (A : Type) (a : A) m n, nth n (repeat a m) a = a.
Proof. intros A a m. induction m as [|m IH]; intros [|n]; cbn [repeat nth]; auto. Qed.

Lemma nth_firstn_lt : forall (A : Type) (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros n i d H.
  - destruct n; reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; cbn [firstn nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_skipn_add : forall (A : Type) (l : list A) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros A l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.

Lemma nth_map_seq : forall (A : Type) (f : nat -> A) n k i d, (i < n)%nat -> nth i (map f (seq k n)) d = f (k + i)%nat.
Proof.
  intros A f n. induction n as [|n IH]; intros k i d H; [lia|].
  cbn [seq map]. destruct i as [|i]; cbn [nth]; [f_equal; lia|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_map_seq0 : forall (A : Type) (f : nat -> A) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof. intros A f n i d H. rewrite nth_map_seq by exact H. reflexivity. Qed.

Lemma nth_list_set_eq : forall (l : list Z) i v d, (i < length l)%nat -> nth i (list_set l i v) d = v.
Proof.
  induction l as [|x l IH]; intros i v d H; cbn [length] in H; [lia|].
  destruct i as [|i]; cbn [list_set nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_list_set_ne : forall (l : list Z) i v j d, j <> i -> nth j (list_set l i v) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros i v j d H; [reflexivity|].
  destruct i as [|i], j as [|j]; cbn [list_set nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma length_list_set : forall (l : list Z) i v, length (list_set l i v) = length l.
Proof.
  induction l as [|x l IH]; intros i v; [reflexivity|].
  destruct i as [|i]; cbn [list_set length]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma length_copy_text : forall f t b src i, length (copy_text t b src i f) = length t.
Proof.
  induction f as [|f IH]; intros t b src i; cbn [copy_text]; [reflexivity|].
  rewrite IH, length_list_set. reflexivity.
Qed.

(* element j of copy_text: the byte src + j for j in i .. i + f - 1, else the old element *)
Lemma nth_copy_text : forall f t b src i j, 0 <= i -> (Z.to_nat i + f <= length t)%nat ->
  nth j (copy_text t b src i f) 0 =
  if (Z.to_nat i <=? j)%nat && (j <? Z.to_nat i + f)%nat then byte_at b (src + Z.of_nat j) else nth j t 0.
Proof.
  induction f as [|f IH]; intros t b src i j Hi Hf; cbn [copy_text].
  - destruct (Nat.leb_spec (Z.to_nat i) j), (Nat.ltb_spec j (Z.to_nat i + 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH by (rewrite ?length_list_set; lia).
    rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat.
    destruct (Nat.eq_dec j (Z.to_nat i)) as [->|N].
    + rewrite nth_list_set_eq by lia. rewrite Z2Nat.id by lia.
      destruct (Nat.leb_spec (Z.to_nat i + 1) (Z.to_nat i)); [lia|].
      destruct (Nat.leb_spec (Z.to_nat i) (Z.to_nat i)); [|lia].
      destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat i + S f)); [|lia]. reflexivity.
    + rewrite nth_list_set_ne by exact N.
      destruct (Nat.leb_spec (Z.to_nat i + 1) j), (Nat.ltb_spec j (Z.to_nat i + 1 + f)),
        (Nat.leb_spec (Z.to_nat i) j), (Nat.ltb_spec j (Z.to_nat i + S f)); cbn [andb]; try reflexivity; lia.
Qed.

(* ---- the text cells ---- *)

Lemma arr_cells_bytes : forall n (l : list Z), cells_bytes (arr_cells n l) = map (fun i => b8 (nth i l 0)) (seq 0 n).
Proof.
  intros n l. unfold arr_cells. generalize (seq 0 n) as s.
  induction s as [|x s IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity.
Qed.

Lemma arr_cells_wf : forall n (l : list Z), cells_wf (arr_cells n l).
Proof.
  intros n l. unfold arr_cells. generalize (seq 0 n) as s.
  induction s as [|x s IH]; cbn [map cells_wf cell_wf]; [exact I|]. split; [exact I | exact IH].
Qed.

Lemma cells_size_arr : forall n (l : list Z), cells_size (arr_cells n l) = n.
Proof.
  intros n l. unfold arr_cells. transitivity (length (seq 0 n)); [|apply length_seq].
  generalize (seq 0 n) as s. induction s as [|x s IH]; cbn [map cells_size csize length]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma cells_wf_repeat_C1 : forall b n, cells_wf (repeat (C1 b) n).
Proof. intros b n. induction n as [|n IH]; cbn [repeat cells_wf cell_wf]; [exact I | split; [exact I | exact IH]]. Qed.

Lemma cells_bytes_repeat_C1 : forall b n, cells_bytes (repeat (C1 b) n) = repeat b n.
Proof. intros b n. induction n as [|n IH]; cbn [repeat cells_bytes cbytes app]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* the text the model writes, with len = L: the L bytes from offset src, the NUL and the zeros after it *)
Lemma scribble_text_bytes : forall (bb : list byte) (src : Z) (L : nat),
  0 <= src -> (L <= 8)%nat -> (Z.to_nat src + L <= length bb)%nat ->
  cells_bytes (arr_cells 9 (list_set (copy_text (repeat 0 9) (map bz bb) src 0 L) L 0)) =
  firstn L (skipn (Z.to_nat src) bb) ++ repeat (b8 0) (9 - L).
Proof.
  intros bb src L Hs HL HB. rewrite arr_cells_bytes.
  assert (LF : length (firstn L (skipn (Z.to_nat src) bb)) = L).
  { rewrite length_firstn, length_skipn. lia. }
  apply (nth_ext _ _ (b8 0) (b8 0)).
  - rewrite length_map, length_seq, length_app, LF, len_repeat. lia.
  - intros i Hi. rewrite length_map, length_seq in Hi.
    rewrite nth_map_seq0 by exact Hi.
    destruct (Nat.eq_dec i L) as [->|N].
    + rewrite nth_list_set_eq by (rewrite length_copy_text, len_repeat; lia).
      rewrite app_nth2 by lia. rewrite nth_repeat_d. reflexivity.
    + rewrite nth_list_set_ne by exact N.
      rewrite nth_copy_text by (rewrite ?len_repeat; lia).
      change (Z.to_nat 0) with 0%nat. rewrite Nat.add_0_l. cbn [Nat.leb andb].
      destruct (Nat.ltb_spec i L) as [Lt|Ge].
      * rewrite app_nth1 by lia. rewrite nth_firstn_lt by exact Lt. rewrite nth_skipn_add.
        rewrite byte_at_map_Z by lia. unfold at8. rewrite b8_bz. f_equal. lia.
      * rewrite app_nth2 by lia. rewrite !nth_repeat_d. reflexivity.
Qed.

(* ---- cells and bytes of the event and the body ---- *)

Lemma rw_cells_split_at : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs))) (skipn k cs).
Proof. intros segs m A cs k H. apply rw_cells_app. rewrite firstn_skipn. exact H. Qed.

(* the 9 zero text cells as memcpy's destination of L bytes and the zeros after it *)
Lemma text_zero_split : forall segs m A L, (L <= 9)%nat ->
  rw_cells segs m A (repeat (C1 (b8 0)) 9) ->
  rw_cells segs m A [CB L (repeat (b8 0) L)] /\ rw_cells segs m (A + Z.of_nat L) (repeat (C1 (b8 0)) (9 - L)).
Proof.
  intros segs m A L HL H.
  assert (H2 : rw_cells segs m A (CB L (repeat (b8 0) L) :: repeat (C1 (b8 0)) (9 - L))).
  { eapply rw_cells_bytes; [exact H | |].
    - cbn [cells_wf cell_wf]. split; [apply len_repeat | apply cells_wf_repeat_C1].
    - cbn [cells_bytes cbytes]. rewrite !cells_bytes_repeat_C1, <- repeat_add.
      replace (L + (9 - L))%nat with 9%nat by lia. reflexivity. }
  apply rw_cells_cons in H2 as [H3 H4]. cbn [csize] in H4. split; assumption.
Qed.

(* memcpy's source: the L body bytes from offset s + 5 *)
Lemma sx_src : forall segs m body bb s L, bytes_at segs m body bb -> 0 <= s ->
  (Z.to_nat (s + 3 + 2) + L <= length bb)%nat ->
  bytes_at segs m (body + s + 5) (firstn L (skipn (Z.to_nat (s + 3 + 2)) bb)).
Proof.
  intros segs m body bb s L H Hs HL.
  rewrite <- (firstn_skipn (Z.to_nat (s + 3 + 2)) bb) in H.
  apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn L (skipn (Z.to_nat (s + 3 + 2)) bb)) in H.
  apply bytes_at_app in H as [H _].
  replace (body + s + 5) with (body + (s + 3 + 2)) by lia. exact H.
Qed.

(* the copied bytes and the zeros after them as the 9 text cells *)
Lemma sx_text_merge : forall segs m A B L src zs T,
  rw_cells segs m A [CB L src] -> rw_cells segs m B zs -> B = A + Z.of_nat L ->
  cells_bytes (arr_cells 9 T) = src ++ cells_bytes zs -> rw_cells segs m A (arr_cells 9 T).
Proof.
  intros segs m A B L src zs T H1 H2 -> E.
  pose proof (rw_cells_app_merge segs m A [CB L src] zs H1) as H. cbn [cells_size csize] in H.
  rewrite Nat.add_0_r in H. specialize (H H2).
  eapply rw_cells_bytes; [exact H | apply arr_cells_wf | exact E].
Qed.

(* the event's 40-byte head from the 20 bytes before the text, the text and the 11 bytes after it *)
Lemma sx_ev_merge : forall segs m A pre T post,
  rw_cells segs m A pre -> cells_size pre = 20%nat ->
  rw_cells segs m (A + 20) (arr_cells 9 T) -> rw_cells segs m (A + 29) post ->
  rw_cells segs m A (pre ++ arr_cells 9 T ++ post).
Proof.
  intros segs m A pre T post H1 S1 H2 H3. apply rw_cells_app_merge; [exact H1|]. rewrite S1.
  replace (A + Z.of_nat 20) with (A + 20) by lia.
  apply rw_cells_app_merge; [exact H2|]. rewrite cells_size_arr.
  replace (A + 20 + Z.of_nat 9) with (A + 29) by lia. exact H3.
Qed.

(* decode_sysex with the body bytes read as at8 (as in diginet_decoder_next_sysex.v) *)
Ltac sx_model :=
  unfold decode_sysex, DIGINET_SYSEX_MAKER, DIGINET_FN_RING, DIGINET_FN_METER, DIGINET_FN_LEDS,
    DIGINET_FN_SCRIBBLE, DIGINET_FN_COUNTER, DIGINET_FN_SYSTEM; cbv zeta;
  rewrite !byte_at_map_Z by lia.

Section Scribble.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (d ev body lo : Z) (bb ej cpad : list byte) (p : option Z)
  (res : Z * dgn_event * dgn_decoder) (msg : dgn_msg) (pos1 : nat) (st1 : Z) (mpad j0 jl jp : list byte).

Lemma dn_scribble : memcpy_contract ->
  forall (ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 : word) (m1 : word -> option byte),
  dn_ctx sp m0 d ev body lo bb p res msg pos1 st1 mpad ->
  dn_at sp m0 m1 d ev body bb cpad p pos1 st1 msg mpad j0 jl jp s3 s2 s1 s0 ra
    (de_set_device (at8 bb (Z.to_nat (dm_sysex msg + 1))) (dn_e0 msg)) ->
  dm_status msg = 240 -> 1 <= dm_sysex msg -> 3 <= dm_sysex_len msg ->
  dm_sysex msg + dm_sysex_len msg < Z.of_nat (length bb) ->
  at8 bb (Z.to_nat (dm_sysex msg)) = 19 -> at8 bb (Z.to_nat (dm_sysex msg + 2)) = 64 ->
  evt rsegs (dn_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 d ev body lo cpad ej res)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 ev) (Z_to_bv 64 1)
             (Z_to_bv 64 (dm_sysex_len msg + -3)) (Z_to_bv 64 (body + dm_sysex msg)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (dm_sysex_len msg)) s3' s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1423c) fc None m1 (seg_rom rsegs)).
Proof.
  intros MCPY ra' t0 t1 t2 a2 a3 a4 a5 a6 a7 s3' t3 t4 t5 t6 m1 HCTX HAT HF0 HS1 HN3 HSN MK HFN.
  dn_ctx_open HCTX. dn_open HAT.
  assert (HR : res = (1, decode_sysex (map bz bb) msg (dn_e0 msg), {| dd_c := cursor_of bb pos1 st1; dd_p := p |})).
  { rewrite HRES. unfold dn_tail. rewrite HF0. reflexivity. }
  (* addi a2 = 3; bltu pn, 3 *)
  step. step.
  rewrite (ltu_lit (dm_sysex_len msg + -3) 3) by lia.
  destruct (Z.ltb_spec (dm_sysex_len msg + -3) 3) as [P3|P3].
  { (* fewer than 3 bytes after the function: kind 13 *)
    dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite HFN, MK, (proj2 (Z.ltb_ge _ _) HN3); cbn [Z.eqb Pos.eqb orb negb];
      rewrite (proj2 (Z.ltb_lt (dm_sysex_len msg - 3) 3)) by lia; cbn [orb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  (* s2 = n - 5 = pn - 2 = len; addi a0 = 8; bltu 8, len *)
  step. step. step.
  rewrite (ltu_lit 8 (dm_sysex_len msg + -5)) by lia.
  destruct (Z.ltb_spec 8 (dm_sysex_len msg + -5)) as [P8|P8].
  { (* more than DIGINET_SCRIBBLE_MAX characters: kind 13 *)
    dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite HFN, MK, (proj2 (Z.ltb_ge _ _) HN3); cbn [Z.eqb Pos.eqb orb negb];
      unfold DIGINET_SCRIBBLE_MAX;
      rewrite (proj2 (Z.ltb_ge (dm_sysex_len msg - 3) 3)) by lia;
      rewrite (proj2 (Z.ltb_lt 8 (dm_sysex_len msg - 3 - 2))) by lia; cbn [orb].
    - dmsg_eq.
    - ev_head_lit. reflexivity. }
  (* kind 10 (sw 0(s0)); lbu the address, s3 = ev->text, sb 9(s0); sb len 0x13(s0); a1 = the characters *)
  step. step.
  pose proof (body_read rsegs _ body bb (dm_sysex msg) 3 HBB ltac:(lia)) as RD3.
  pose proof (at8_range bb (Z.to_nat (dm_sysex msg + 3))) as RB3.
  step.
  rewrite (dn_zxb_b8 (at8 bb (Z.to_nat (dm_sysex msg + 3)))) by lia.
  step. step. step. step. step. step.
  (* the event's text cells (ev + 20 .. ev + 28) apart from the 20 bytes before and the 11 after *)
  destruct (rw_cells_split_at _ _ _ _ 14 HE) as [HEa HEr]; clear HE.
  cbn [firstn skipn cells_size csize Nat.add] in HEa, HEr.
  replace (ev + Z.of_nat 20) with (ev + 20) in HEr by lia.
  destruct (rw_cells_split_at _ _ _ _ 9 HEr) as [HEt HEb]; clear HEr.
  cbn [firstn skipn cells_size csize Nat.add] in HEt, HEb.
  replace (ev + 20 + Z.of_nat 9) with (ev + 29) in HEb by lia.
  assert (Ue20 : bv_unsigned (Z_to_bv 64 (ev + 20)) = ev + 20) by (apply unsigned_lit; lia).
  assert (Ub5 : bv_unsigned (Z_to_bv 64 (body + dm_sysex msg + 5)) = body + dm_sysex msg + 5)
    by (apply unsigned_lit; lia).
  clear RD3.
  (* one case per len: memcpy's destination and the NUL's cell are then literal cells *)
  assert (HLc : dm_sysex_len msg + -5 = 1 \/ dm_sysex_len msg + -5 = 2 \/ dm_sysex_len msg + -5 = 3 \/
                dm_sysex_len msg + -5 = 4 \/ dm_sysex_len msg + -5 = 5 \/ dm_sysex_len msg + -5 = 6 \/
                dm_sysex_len msg + -5 = 7 \/ dm_sysex_len msg + -5 = 8) by lia.
  destruct HLc as [HLc|[HLc|[HLc|[HLc|[HLc|[HLc|[HLc|HLc]]]]]]].
  all: lazymatch type of HLc with _ = ?c =>
         let L := eval vm_compute in (Z.to_nat c) in
         rewrite HLc;
         destruct (text_zero_split rsegs _ _ L ltac:(lia) HEt) as [HT1 HTz]; clear HEt;
         cbn [repeat Nat.sub] in HT1, HTz;
         let k := eval vm_compute in (20 + c) in replace (ev + 20 + Z.of_nat L) with (ev + k) in HTz by lia;
         assert (Uc : bv_unsigned (Z_to_bv 64 c) = c) by reflexivity
       end.
  (* jal memcpy (ev->text, the characters, len) *)
  all: step.
  all: lazymatch type of HT1 with rw_cells _ _ _ [CB ?L _] =>
       lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply evt_cut;
         [ eapply MCPY;
           [ rewrite Ub5; exact (sx_src rsegs mm body bb (dm_sysex msg) L HBB ltac:(lia) ltac:(lia))
           | rewrite Uc, length_firstn, length_skipn; lia
           | rewrite Ue20, Uc; exact HT1
           | rewrite Ub5, Uc, Ue20; lia
           | exact MI ]
         | post_call rsegs mm ]
       end end.
  all: rename PC into HTc, MI0 into MI; clear POST.
  all: rewrite Ue20, Uc in HTc.
  all: lazymatch type of HTc with rw_cells _ _ _ [CB (Z.to_nat ?c) _] =>
         let L := eval vm_compute in (Z.to_nat c) in change (Z.to_nat c) with L in HTc end.
  (* add s2 = ev->text + len; sb zero (the NUL); j 0x140f8 *)
  all: do 3 step.
  (* the text cells as the model's text, then the event's whole head *)
  all: lazymatch type of HTc with rw_cells _ _ _ [CB ?L _] =>
         pose proof (sx_text_merge rsegs _ (ev + 20) _ L _ _
           (list_set (copy_text (repeat 0 9) (map bz bb) (dm_sysex msg + 3 + 2) 0 (Z.to_nat (dm_sysex_len msg + -5)))
              (Z.to_nat (dm_sysex_len msg + -5)) 0)
           HTc HTz ltac:(lia)
           ltac:(rewrite scribble_text_bytes by lia; rewrite HLc; reflexivity)) as HTX
       end.
  all: pose proof (sx_ev_merge rsegs _ ev _ _ _ HEa eq_refl HTX HEb) as HE; clear HEa HTX HEb HTc HTz.
  all: dn_fin HR HDc HD2 HE HEM; sx_model;
      rewrite HFN, MK, (proj2 (Z.ltb_ge _ _) HN3); cbn [Z.eqb Pos.eqb orb negb];
      unfold DIGINET_SCRIBBLE_MAX;
      rewrite (proj2 (Z.ltb_ge (dm_sysex_len msg - 3) 3)) by lia;
      rewrite (proj2 (Z.ltb_ge 8 (dm_sysex_len msg - 3 - 2))) by lia; cbn [orb];
      rewrite (u8_small (dm_sysex_len msg - 3 - 2)) by lia;
      replace (dm_sysex_len msg - 3 - 2) with (dm_sysex_len msg + -5) by lia;
      [ dmsg_eq | ev_head_lit; unfold DIGINET_EV_SCRIBBLE; reflexivity ].
Qed.

End Scribble.
