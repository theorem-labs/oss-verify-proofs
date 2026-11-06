(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.   (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

Lemma zbytes_length : forall l, length (zbytes l) = length l.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_app : forall l1 l2, zbytes (l1 ++ l2) = zbytes l1 ++ zbytes l2.
Proof. intros. unfold zbytes. apply map_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record yconsts : Type := mkYC {
  yc_malloc_w : Z;       (* [comment removed for export] *)
  yc_realloc_w : Z;      (* [comment removed for export] *)
  yc_free_w : Z;         (* [comment removed for export] *)
  yc_callbacks : Z;      (* [comment removed for export] *)
  yc_cb_null : Z; yc_cb_boolean : Z; yc_cb_number : Z; yc_cb_string : Z;
  yc_cb_start_map : Z; yc_cb_map_key : Z; yc_cb_end_map : Z; yc_cb_start_array : Z; yc_cb_end_array : Z;
  yc_perr : perr -> Z;   (* [comment removed for export] *)
  yc_buf_alloc_error : Z;  (* [comment removed for export] *)
  yc_noop_allocs : Z       (* [comment removed for export] *)
}.

Section YajlRep.
Variable segs : list Segment.
Variable yc : yconsts.

Notation rw_cells := (rw_cells segs).
Notation bytes_at := (bytes_at segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record mbuf : Type := mkMB { mb_id : bptr; mb_addr : Z; mb_did : bptr; mb_data : Z }.

(* [comment removed for export] *)
Record mhand : Type := mkMH {
  mh_id : bptr; mh_addr : Z;
  mh_lid : bptr; mh_lexer : Z;
  mh_lexbuf : mbuf; mh_decbuf : mbuf;
  mh_sid : bptr; mh_stack : Z;
  mh_ctx : Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SIZEOF_BUF : Z := 32.
Definition SIZEOF_LEXER : Z := 48.
Definition SIZEOF_HANDLE : Z := 104.

(* [comment removed for export] *)
Definition buf_cells (b : ybuf) (D AF : Z) : list cell :=
  [C4 (wz (buf_state_code (yb_state b))); C4 (wz (yb_len b)); C4 (wz (yb_used b)); C4 (wz 0);
   C8 (wz D); C8 (wz AF)].

Definition buf_struct (m : mem) (B : Z) (b : ybuf) (D AF : Z) : Prop :=
  rw_cells m B (buf_cells b D AF)
  /\ (yb_data b = None <-> D = 0)
  /\ 0 <= yb_len b < 2^31 /\ 0 <= yb_used b < 2^31.

(* [comment removed for export] *)
Definition buf_data (m : mem) (D : Z) (b : ybuf) : Prop :=
  match yb_data b with
  | None => True
  | Some _ => 0 <= yb_used b < yb_len b /\ exists junk,
      rw_cells m D [CB (Z.to_nat (yb_used b)) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0);
                    CB (Z.to_nat (yb_len b - yb_used b - 1)) junk]
  end.

(* [comment removed for export] *)
Definition buf_rep (m : mem) (mb : mbuf) (b : ybuf) (AF : Z) : Prop :=
  buf_struct m (mb_addr mb) b (mb_data mb) AF /\ buf_data m (mb_data mb) b
  /\ Forall (fun c => 0 <= c < 256) (yb_bytes b).

(* [comment removed for export] *)
Definition buf_blocks (mb : mbuf) (b : ybuf) : list block :=
  (mb_id mb, mb_addr mb, SIZEOF_BUF)
  :: match yb_data b with Some _ => [(mb_did mb, mb_data mb, yb_len b)] | None => [] end.

(* [comment removed for export] *)
Definition buf_alloc_error_cells : list cell :=
  [C4 (wz 1); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz (yc_noop_allocs yc))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lexer_cells (lx : ylexer) (LB AF : Z) : list cell :=
  [C4 (wz (lx_lineOff lx)); C4 (wz (lx_charOff lx)); C4 (wz (lex_error_code (lx_error lx))); C4 (wz 0);
   C8 (wz LB); C4 (wz (lx_bufOff lx)); C4 (wz (lx_bufInUse lx));
   C4 (wz (lx_allowComments lx)); C4 (wz (lx_validateUTF8 lx)); C8 (wz AF)].

Definition lexer_struct (m : mem) (L : Z) (lx : ylexer) (LB AF : Z) : Prop :=
  rw_cells m L (lexer_cells lx LB AF)
  /\ 0 <= lx_lineOff lx < 2^31 /\ 0 <= lx_charOff lx < 2^31 /\ 0 <= lx_bufOff lx < 2^31
  /\ 0 <= lx_bufInUse lx <= 1 /\ 0 <= lx_allowComments lx <= 1 /\ 0 <= lx_validateUTF8 lx <= 1.

(* [comment removed for export] *)
Definition lexer_rep (m : mem) (L : Z) (lx : ylexer) (mbl : mbuf) (AF : Z) : Prop :=
  lexer_struct m L lx (mb_addr mbl) AF /\ buf_rep m mbl (lx_buf lx) AF.

Definition lexer_blocks (lid : bptr) (L : Z) (mbl : mbuf) (lx : ylexer) : list block :=
  (lid, L, SIZEOF_LEXER) :: buf_blocks mbl (lx_buf lx).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_bytes (st : list ystate) : list Z := rev (map state_code st).

Definition bs_rep (m : mem) (SB : Z) (h : yhandle) : Prop :=
  match h_stack_blk h with
  | None => SB = 0
  | Some _ => SB <> 0 /\ exists junk,
      rw_cells m SB [CB (Z.to_nat (h_used h)) (zbytes (stack_bytes (h_stack h)));
                     CB (Z.to_nat (h_stack_size h - h_used h)) junk]
  end.

Definition bs_blocks (sid : bptr) (SB : Z) (h : yhandle) : list block :=
  match h_stack_blk h with Some _ => [(sid, SB, h_stack_size h)] | None => [] end.

(* [comment removed for export] *)
Definition ctx_cells (cx : yctx) : list cell := [C4 (wz (cx_arrayLevel cx)); C4 (wz (cx_objectLevel cx))].
Definition ctx_rep (m : mem) (CX : Z) (cx : yctx) : Prop :=
  rw_cells m CX (ctx_cells cx) /\ 0 <= cx_arrayLevel cx < 2^31 /\ 0 <= cx_objectLevel cx < 2^31.

(* [comment removed for export] *)
Definition callbacks_cells : list cell :=
  [C8 (wz (yc_cb_null yc)); C8 (wz (yc_cb_boolean yc)); C8 (wz 0); C8 (wz 0);
   C8 (wz (yc_cb_number yc)); C8 (wz (yc_cb_string yc)); C8 (wz (yc_cb_start_map yc));
   C8 (wz (yc_cb_map_key yc)); C8 (wz (yc_cb_end_map yc)); C8 (wz (yc_cb_start_array yc));
   C8 (wz (yc_cb_end_array yc))].

(* [comment removed for export] *)
Definition alloc_cells : list cell :=
  [C8 (wz (yc_malloc_w yc)); C8 (wz (yc_realloc_w yc)); C8 (wz (yc_free_w yc)); C8 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition perr_word (pe : option perr) (w : word) : Prop :=
  match pe with None => True | Some e => w = wz (yc_perr yc e) end.

(* [comment removed for export] *)
Definition hand_head_cells (h : yhandle) (mh : mhand) (pew pad : word) : list cell :=
  [C8 (wz (yc_callbacks yc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew;
   C4 (wz (h_bytesConsumed h)); C4 pad; C8 (wz (mb_addr (mh_decbuf mh)));
   C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))].
Definition hand_cells (h : yhandle) (mh : mhand) (pew pad : word) : list cell :=
  hand_head_cells h mh pew pad ++ alloc_cells.

Definition hand_struct (m : mem) (h : yhandle) (mh : mhand) : Prop :=
  (exists pew pad, rw_cells m (mh_addr mh) (hand_cells h mh pew pad) /\ perr_word (h_parseError h) pew)
  /\ 0 <= h_bytesConsumed h < 2^31 /\ 0 <= h_stack_size h < 2^31 /\ 0 <= h_used h <= h_stack_size h
  /\ (h_stack_blk h = None <-> mh_stack mh = 0).

(* [comment removed for export] *)
Definition hand_rep (m : mem) (h : yhandle) (mh : mhand) : Prop :=
  hand_struct m h mh
  /\ lexer_rep m (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72)
  /\ buf_rep m (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72)
  /\ bs_rep m (mh_stack mh) h.

(* [comment removed for export] *)
Definition yblocks (mh : mhand) (h : yhandle) : list block :=
  (mh_id mh, mh_addr mh, SIZEOF_HANDLE)
  :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)
  ++ buf_blocks (mh_decbuf mh) (h_decbuf h)
  ++ bs_blocks (mh_sid mh) (mh_stack mh) h.

(* [comment removed for export] *)
Definition in_blocks (BS : list block) (a : Z) : Prop :=
  exists b, In b BS /\ blk_addr b <= a < blk_addr b + blk_size b.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition text_at (m : mem) (T : Z) (txt : list Z) : Prop :=
  bytes_at m T (zbytes txt) /\ Forall (fun c => 0 <= c < 256) txt
  /\ 0 < T /\ T + zlength txt < 2^62.

Lemma text_at_agree : forall P m m' T txt,
  agree_on P m m' -> text_at m T txt -> (forall a, T <= a < T + zlength txt -> P a) -> text_at m' T txt.
Proof.
  intros P m m' T txt HP (HB & HF & HT) HR. split; [|auto].
  eapply bytes_at_agree; eauto. rewrite zbytes_length. unfold zlength in HR. exact HR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma buf_struct_agree : forall P m m' B b D AF,
  agree_on P m m' -> buf_struct m B b D AF -> (forall a, B <= a < B + SIZEOF_BUF -> P a) ->
  buf_struct m' B b D AF.
Proof.
  intros P m m' B b D AF HP (HC & HR) HF. split; [|exact HR].
  eapply rw_cells_agree; [exact HP | exact HC |]. intros a Ha. apply HF. cbn in Ha. unfold SIZEOF_BUF. lia.
Qed.

Lemma buf_data_agree : forall P m m' D b,
  agree_on P m m' -> buf_data m D b ->
  (yb_data b <> None -> forall a, D <= a < D + yb_len b -> P a) ->
  buf_data m' D b.
Proof.
  intros P m m' D b HP HD HF. unfold buf_data in *. destruct (yb_data b) as [d|]; [|exact I].
  destruct HD as (HU & junk & HC). split; [exact HU|]. exists junk.
  pose proof (rw_cells_bound segs _ _ _ HC) as HB.
  eapply rw_cells_agree; [exact HP | exact HC |]. intros a Ha. apply HF; [congruence|].
  revert Ha. cbn [cells_size csize]. intros Ha. lia.
Qed.

Lemma buf_rep_agree : forall P m m' mb b AF,
  agree_on P m m' -> buf_rep m mb b AF ->
  (forall a, mb_addr mb <= a < mb_addr mb + SIZEOF_BUF -> P a) ->
  (yb_data b <> None -> forall a, mb_data mb <= a < mb_data mb + yb_len b -> P a) ->
  buf_rep m' mb b AF.
Proof.
  intros P m m' mb b AF HP (BS & BD & FB) H1 H2. split; [eapply buf_struct_agree; eauto|].
  split; [eapply buf_data_agree; eauto| exact FB].
Qed.

Lemma lexer_rep_agree : forall P m m' L lx mbl AF,
  agree_on P m m' -> lexer_rep m L lx mbl AF ->
  (forall a, L <= a < L + SIZEOF_LEXER -> P a) ->
  (forall a, mb_addr mbl <= a < mb_addr mbl + SIZEOF_BUF -> P a) ->
  (yb_data (lx_buf lx) <> None -> forall a, mb_data mbl <= a < mb_data mbl + yb_len (lx_buf lx) -> P a) ->
  lexer_rep m' L lx mbl AF.
Proof.
  intros P m m' L lx mbl AF HP ((LC & LR) & BR) H1 H2 H3. split; [split; [| exact LR]| eapply buf_rep_agree; eauto].
  eapply rw_cells_agree; [exact HP| exact LC|]. intros a Ha. apply H1. revert Ha. cbn [cells_size csize lexer_cells Nat.add]. unfold SIZEOF_LEXER. lia.
Qed.

Lemma ctx_rep_agree : forall P m m' CX cx,
  agree_on P m m' -> ctx_rep m CX cx -> (forall a, CX <= a < CX + 8 -> P a) -> ctx_rep m' CX cx.
Proof.
  intros P m m' CX cx HP (HC & HR) HF. split; [|exact HR]. eapply rw_cells_agree; [exact HP | exact HC |].
  intros a Ha. apply HF. cbn in Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma buf_cells_size : forall b D AF, cells_size (buf_cells b D AF) = 32%nat.
Proof. reflexivity. Qed.
Lemma lexer_cells_size : forall lx LB AF, cells_size (lexer_cells lx LB AF) = 48%nat.
Proof. reflexivity. Qed.
Lemma hand_cells_size : forall h mh pew pad, cells_size (hand_cells h mh pew pad) = 104%nat.
Proof. reflexivity. Qed.
Lemma hand_head_cells_size : forall h mh pew pad, cells_size (hand_head_cells h mh pew pad) = 72%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ywr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma ycells_app : forall m A cs1 cs2,
  rw_cells m A (cs1 ++ cs2) <-> rw_cells m A cs1 /\ rw_cells m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold Step.rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite ywr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma hand_cells_app : forall m h mh pew pad,
  rw_cells m (mh_addr mh) (hand_cells h mh pew pad)
  <-> rw_cells m (mh_addr mh) (hand_head_cells h mh pew pad) /\ rw_cells m (mh_addr mh + 72) alloc_cells.
Proof. intros. unfold hand_cells. rewrite ycells_app, hand_head_cells_size. reflexivity. Qed.
Lemma callbacks_cells_size : cells_size callbacks_cells = 88%nat.
Proof. reflexivity. Qed.
Lemma ctx_cells_size : forall cx, cells_size (ctx_cells cx) = 8%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma stack_bytes_cons : forall s st, stack_bytes (s :: st) = stack_bytes st ++ [state_code s].
Proof. intros. unfold stack_bytes. cbn [map]. apply rev_unit || reflexivity. Qed.
Lemma stack_bytes_length : forall st, length (stack_bytes st) = length st.
Proof. intros. unfold stack_bytes. rewrite length_rev, length_map. reflexivity. Qed.

End YajlRep.
End RC__1.
