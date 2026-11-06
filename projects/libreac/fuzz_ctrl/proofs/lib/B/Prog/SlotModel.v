(* The pure model of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0, [0x81018, 0x83114)) that the cut
   states of B/Prog/SlotInv.v use (slot-plan-asan-ubsan.md; the plain / asan model with image B's addresses: the
   catalogue T = 0x9f620 (BOX_CATALOGUE of the v1.9.0 binary; patched 0x9f520) and the round trip's box 0x21140
   (round_trip.box, a frame_AG global, unchanged); the kind-name table KIND_NAME is B/Prog/reac_ctrl_kind_name_c.v's).
   Every value is a function of the input bytes and the image. The first-fragment state (fstate, turn,
   joined_byte, FI) follows the v1.9.0 source (fuzz/fuzz_ctrl.c v1.9.0:243-254, :398-411); it is layout-free and
   shared verbatim with lib/A/Prog/SlotModel.v (v190-model-B.md section 1 (a working note, not in this delivery)). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts RcEmit RcSynth RcDecl RcMatch RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
Import ListNotations.
Open Scope Z_scope.

(* The input: in[j] (0 past the end), c0, OUR, mode, i*, m. *)
Definition nlen (inp : list byte) : Z := Z.of_nat (length inp).
Definition inb (inp : list byte) (j : Z) : Z := bz (nthb inp (Z.to_nat j)).
Definition c0 (inp : list byte) : Z := Z.min (nlen inp) 7.
Definition OUR (inp : list byte) : list byte := map (nthb inp) (seq 0 6).
Definition mode (inp : list byte) : Z := if 7 <=? nlen inp then inb inp 6 else 0.
Definition rt_on (inp : list byte) : bool := Z.odd (mode inp).

(* BOX_CATALOGUE in image B (v1.9.0 .data.rel.ro [0x9f1a0, 0xa0890); patched 0x9f520). *)
Definition CAT : Z := 0x9f620.
Definition CAT_N : Z := 11.
Definition CAT_ROW : Z := 296.
Definition istar (inp : list byte) : Z := (mode inp / 2) mod CAT_N.
Definition mrow (inp : list byte) : Z := CAT + CAT_ROW * istar inp.

(* Image bytes: the catalogue rows, the row names, decl_i. *)
Definition img (a : Z) (n : nat) : list byte :=
  match Image.image_bytes rsegs a n with Some l => l | None => repeat (zb 0) n end.
Definition rowb (i : Z) : list byte := img (CAT + CAT_ROW * i) 296.
Fixpoint img_cstr (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => let b := nthb (img a 1) 0 in if bz b =? 0 then [b] else b :: img_cstr (a + 1) k'
  end.
Definition decl_i (i : Z) : list byte := RcDecl.decl (rowb i).

(* Shared helpers: a frame's first 50 bytes, the reply arm, the fragment arm. *)
Definition fr50 (bs : list byte) : list byte := firstn 50 (bs ++ repeat (zb 0) 50).
Definition z72 : list byte := repeat (zb 0) 72.
Definition b2z (b : bool) : Z := if b then 1 else 0.

Definition r_addr (g : list byte) : Z := cp_v g 36 * 256 + cp_v g 37.
Definition r_pll (g : list byte) : Z := ir_s g - 13.
Definition r_pl (g : list byte) : list byte := bsl g 38 (r_pll g).
Definition rp_r (len : Z) (g : list byte) : Z := if ir len g then 1 else 0.
Definition rp_id (idb : list byte) (len : Z) (g : list byte) : list byte :=
  if ir len g then snd (ING idb (r_addr g) (r_pl g)) else idb.

Definition fcls (len : Z) (st g : list byte) : fg_case := fg_class 1 1 1 1 1 len st g.
Definition fg_next (st g : list byte) (c : fg_case) : list byte :=
  match c with
  | FgRefuse | FgNone => st
  | FgFirst => fg_first st g
  | FgDrop => fg_clear st
  | FgJoin | FgClose => fg_clear (fg_join st g)
  end.
Definition fg_st (len : Z) (st g : list byte) : list byte := fg_next st g (fcls len st g).
Definition fg_rf (len : Z) (st g : list byte) : Z := fg_ret (fcls len st g).
Definition f_pll (st g : list byte) : Z := fg_T st g - 13.
Definition f_pl (len : Z) (st g : list byte) : list byte := bsl (fg_st len st g) 19 (f_pll st g).
Definition fg_id (idb : list byte) (len : Z) (st g : list byte) : list byte :=
  if fg_rf len st g =? 1 then snd (ING idb (fg_addr st g) (f_pl len st g)) else idb.

(* The round trip (mode odd): row m = row i*, E(b), n_b, F_b, k_b, RID_b, RFG_b (b : nat). *)
Definition box6 : list byte := map zb [0; 64; 171; 0; 0; 1].
(* round_trip.box (frame_AG (0x21140, 6)): the address the round trip passes, loaded in the entry round-trip setup. *)
Definition BOXA : Z := 0x21140.
Definition CNT16 : Z := 0x1234.
Definition rt_mb (inp : list byte) : list byte := rowb (istar inp).
Definition rt_nb (inp : list byte) : list byte := img_cstr (RcSynth.rname (rt_mb inp)) 16.
Definition rt_uw (inp : list byte) : Z := RcPorts.bm_uw (mrow inp) (firstn 8 (skipn 16 (rt_mb inp))).
Definition rt_E (inp : list byte) (b : Z) : bool := reac_ctrl_build_as_c.ba_E (rt_uw inp) (rt_mb inp) b.
Definition rt_n (inp : list byte) (b : Z) : Z := if rt_E inp b then 52 + 36 * rt_uw inp else 0.
Definition rt_X (inp : list byte) (b : Z) : list byte :=
  reac_ctrl_build_as_c.ba_X (mrow inp) (rt_mb inp) (rt_nb inp) b.
Definition rt_F (inp : list byte) (b : Z) : list byte :=
  RcEmit.em_fr (OUR inp) box6 CNT16 (zb 205) (zb 234) (rt_X inp b) (rt_n inp b).
Definition rt_g (inp : list byte) (b : Z) : list byte := fr50 (rt_F inp b).
Definition rt_k (inp : list byte) (b : Z) : Z := fst (ctrlparse (rt_n inp b) (rt_g inp b)).
Definition rt_B (inp : list byte) (b : Z) : list byte := snd (ctrlparse (rt_n inp b) (rt_g inp b)).
Definition rt_pbs (inp : list byte) : list byte := bsl (rt_g inp 0) 18 20.

Fixpoint rt_st (inp : list byte) (b : nat) : list byte * list byte :=
  match b with
  | O => (ID0, z72)
  | S b' =>
      let s := rt_st inp b' in
      let x := Z.of_nat b' in
      let n := rt_n inp x in
      let g := rt_g inp x in
      if n =? 0 then s
      else if (x =? 3) || (x =? 4) then (rp_id (fst s) n g, snd s)
      else if (x =? 5) || (x =? 6) then (fg_id (fst s) n (snd s) g, fg_st n (snd s) g)
      else s
  end.
Definition RID (inp : list byte) (b : nat) : list byte := fst (rt_st inp b).
Definition RFG (inp : list byte) (b : nat) : list byte := snd (rt_st inp b).

(* The frame loop: c_j, left_j, h_j, L_j, len_j, body_j (offsets from p), Φ's bytes, J. *)
Definition f_left (inp : list byte) (c : Z) : Z := nlen inp - c.
Definition f_h (inp : list byte) (c : Z) : Z := Z.min 2 (f_left inp c).
Definition f_L (inp : list byte) (c : Z) : Z :=
  inb inp c + (if 2 <=? f_left inp c then 256 * inb inp (c + 1) else 0).
Definition f_len (inp : list byte) (c : Z) : Z := Z.min (f_L inp c) (f_left inp c - f_h inp c).
Definition f_body (inp : list byte) (c : Z) : Z := c + f_h inp c.
Definition f_next (inp : list byte) (c : Z) : Z := f_body inp c + f_len inp c.
Definition f_phi (inp : list byte) (c : Z) : list byte :=
  firstn (Z.to_nat (f_len inp c)) (skipn (Z.to_nat (f_body inp c)) inp).
Fixpoint fc (inp : list byte) (j : nat) : Z :=
  match j with O => c0 inp | S j' => f_next inp (fc inp j') end.
Fixpoint fJ_from (inp : list byte) (j fuel : nat) : nat :=
  match fuel with
  | O => j
  | S f => if 0 <? f_left inp (fc inp j) then fJ_from inp (S j) f else j
  end.
Definition fJ (inp : list byte) : nat := fJ_from inp 0 256.

(* The frame-loop state at the top of turn j: ID_j, FG_j and FS_j = (have, n, body), the harness's
   struct first_frag (fuzz/fuzz_ctrl.c v1.9.0:243-247): have, the length n = block[8] of the last FIRST
   fragment's body, and that body, the n bytes block[9 ..] (block = frame + 18). *)
Record fstate := FSt { fs_id : list byte; fs_fg : list byte; fs_have : Z; fs_n : Z; fs_body : list byte }.
Definition fs0 : fstate := FSt ID0 z72 0 0 [].
Definition f_opens (len : Z) (g : list byte) : bool := fg_fr len g && (bat g 19 =? 1).
Definition turn (s : fstate) (len : Z) (g : list byte) : fstate :=
  let idr := rp_id (fs_id s) len g in
  let id' := fg_id idr len (fs_fg s) g in
  let fg' := fg_st len (fs_fg s) g in
  if f_opens len g then FSt id' fg' 1 (bat g 26) (firstn (Z.to_nat (bat g 26)) (skipn 27 g))
  else FSt id' fg' (fs_have s) (fs_n s) (fs_body s).

(* joined_byte (fuzz_ctrl.c v1.9.0:251-254): byte i of the record that the FIRST fragment (state s) and the
   LAST frame g join: the FIRST body, then the LAST block's bytes from block[9]. *)
Definition joined_byte (s : fstate) (g : list byte) (i : Z) : Z :=
  if i <? fs_n s then bat (fs_body s) i else bat g (27 + i - fs_n s).
(* The address the harness compares with the fragment call's addr (fuzz_ctrl.c v1.9.0:398-400). *)
Definition joined_addr (s : fstate) (g : list byte) : Z := 256 * joined_byte s g 9 + joined_byte s g 10.

(* Turn j's values (j : nat). *)
Definition t_c (inp : list byte) (j : nat) : Z := fc inp j.
Definition t_left (inp : list byte) (j : nat) : Z := f_left inp (fc inp j).
Definition t_h (inp : list byte) (j : nat) : Z := f_h inp (fc inp j).
Definition t_len (inp : list byte) (j : nat) : Z := f_len inp (fc inp j).
Definition t_body (inp : list byte) (j : nat) : Z := f_body inp (fc inp j).
Definition t_phi (inp : list byte) (j : nat) : list byte := f_phi inp (fc inp j).
Definition t_g (inp : list byte) (j : nat) : list byte := fr50 (t_phi inp j).

Fixpoint fst_at (inp : list byte) (j : nat) : fstate :=
  match j with
  | O => fs0
  | S j' => turn (fst_at inp j') (t_len inp j') (t_g inp j')
  end.
Definition t_ID (inp : list byte) (j : nat) : list byte := fs_id (fst_at inp j).
Definition t_FG (inp : list byte) (j : nat) : list byte := fs_fg (fst_at inp j).

Definition t_k (inp : list byte) (j : nat) : Z := fst (ctrlparse (t_len inp j) (t_g inp j)).
Definition t_B (inp : list byte) (j : nat) : list byte := snd (ctrlparse (t_len inp j) (t_g inp j)).
Definition t_big (inp : list byte) (j : nat) : bool := 50 <=? t_len inp j.
Definition t_sum_ok (inp : list byte) (j : nat) : bool :=
  t_big inp j && (blocksum (skipn 18 (t_g inp j)) =? 0).
Definition t_tfill (inp : list byte) (j : nat) : bool :=
  t_big inp j && (cp_v (t_g inp j) 16 =? 0) && (cp_v (t_g inp j) 17 =? 0).
Definition t_8819 (inp : list byte) (j : nat) : bool :=
  t_big inp j && (cp_v (t_g inp j) 12 =? 0x88) && (cp_v (t_g inp j) 13 =? 0x19).
Definition t_TF (inp : list byte) (j : nat) : bool := t_sum_ok inp j || t_tfill inp j.
Definition t_ir (inp : list byte) (j : nat) : bool := ir (t_len inp j) (t_g inp j).
Definition t_r (inp : list byte) (j : nat) : Z := rp_r (t_len inp j) (t_g inp j).
Definition t_IDr (inp : list byte) (j : nat) : list byte := rp_id (t_ID inp j) (t_len inp j) (t_g inp j).
Definition t_rf (inp : list byte) (j : nat) : Z := fg_rf (t_len inp j) (t_FG inp j) (t_g inp j).
Definition t_FGf (inp : list byte) (j : nat) : list byte := fg_st (t_len inp j) (t_FG inp j) (t_g inp j).
Definition t_blk (inp : list byte) (j : nat) : list byte := bsl (t_g inp j) 18 32.
Definition t_pbs (inp : list byte) (j : nat) : list byte := bsl (t_g inp j) 18 20.
Definition t_want_v (inp : list byte) (j : nat) : Z :=
  if RcLeaf.hv (cp_b (t_g inp j) 18) (cp_b (t_g inp j) 19) (bsl (t_g inp j) 34 6) then 0 else -1.
Definition t_rp (inp : list byte) (j : nat) : Z := if RcLeaf.decl (t_pbs inp j) then 0 else -1.
Definition t_unk (inp : list byte) (j : nat) : Z :=
  if RcPorts.pu_decl (t_pbs inp j) then 4 * RcPorts.pu_nunk (t_pbs inp j) 12 else -1.
Definition t_first (inp : list byte) (j : nat) : Z :=
  if RcPorts.pu_decl (t_pbs inp j) then RcPorts.pu_first (t_pbs inp j) 12 else 0.
Definition is_empty (c : Z) : bool := c =? 3.
Definition t_cls (inp : list byte) (j : nat) : option Z := RcClassify.classify (t_len inp j) (t_g inp j) (OUR inp).

Fixpoint rob (blk : list byte) (i fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f => if bool_decide (decl_i (Z.of_nat i) = blk) then CAT + CAT_ROW * Z.of_nat i else rob blk (S i) f
  end.
Definition row_of_block (blk : list byte) : Z := rob blk 0 11.
Definition t_rowsel (inp : list byte) (j : nat) : bool :=
  (t_k inp j =? 9) && (cp_v (t_g inp j) 16 =? 0xcd) && (cp_v (t_g inp j) 17 =? 0xea).
Definition t_want_m (inp : list byte) (j : nat) : Z := if t_rowsel inp j then row_of_block (t_blk inp j) else 0.
Definition t_want (inp : list byte) (j : nat) : Z := RcMatch.want CAT (t_len inp j) (t_g inp j).

(* The invariants frag_ok (struct.reac_identity_frag FG2) and FI (struct.first_frag FF2). FI: while the
   reassembly state st holds a FIRST (byte 6 = 1), the harness's state is that FIRST: have = 1, n = st's length
   byte 7, body = st's buffer bytes 8 .. 8 + n. *)
Definition frag_ok (st : list byte) : Prop :=
  (bat st 6 = 0 \/ bat st 6 = 1) /\ (bat st 6 = 1 -> 1 <= bat st 7 <= 22).
Definition FI (st : list byte) (s : fstate) : Prop :=
  bat st 6 = 1 ->
  fs_have s = 1 /\ fs_n s = bat st 7 /\ fs_body s = firstn (Z.to_nat (bat st 7)) (skipn 8 st).

Lemma OUR_length : forall inp, length (OUR inp) = 6%nat.
Proof. intros inp. unfold OUR. rewrite length_map, length_seq. reflexivity. Qed.

Lemma fr50_length : forall bs, length (fr50 bs) = 50%nat.
Proof. intros bs. unfold fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma z72_length : length z72 = 72%nat.
Proof. reflexivity. Qed.

Lemma fst_at_S : forall inp j, fst_at inp (S j) = turn (fst_at inp j) (t_len inp j) (t_g inp j).
Proof. reflexivity. Qed.

Lemma fc_S : forall inp j, fc inp (S j) = f_next inp (fc inp j).
Proof. reflexivity. Qed.
