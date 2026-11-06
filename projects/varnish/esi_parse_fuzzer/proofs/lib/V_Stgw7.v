(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation w64 z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition VSB_MAGIC      : Z := 0x4a82dd8a.
Definition VSB_AUTOEXTEND : Z := 0x1.
Definition VSB_DYNAMIC    : Z := 0x10000.
Definition VSB_FINISHED   : Z := 0x20000.
Definition VSB_DYNSTRUCT  : Z := 0x80000.
Definition VSB_FLAGS_LIVE : Z := 0x90001.   (* [comment removed for export] *)
Definition VSB_FLAGS_FIN  : Z := 0xb0001.   (* [comment removed for export] *)
Definition ENOMEM : Z := 12.

Record vsb_rec : Type := VSBR {
  vb_error : Z;   (* [comment removed for export] *)
  vb_buf   : Z;   (* [comment removed for export] *)
  vb_size  : Z;   (* [comment removed for export] *)
  vb_len   : Z;   (* [comment removed for export] *)
  vb_flags : Z;   (* [comment removed for export] *)
  vb_indent: Z    (* [comment removed for export] *)
}.

Definition vsb_cells (v : vsb_rec) : list cell :=
  [ C4 (w64 VSB_MAGIC); C4 (w64 (vb_error v)); C8 (w64 (vb_buf v)); C8 (w64 (vb_size v));
    C8 (w64 (vb_len v)); C4 (w64 (vb_flags v)); C4 (w64 (vb_indent v)) ].

Lemma vsb_cells_size : forall v, cells_size (vsb_cells v) = 40%nat.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition vsb_inv (v : vsb_rec) (fin : bool) : Prop :=
  16 <= vb_size v <= 2^40 /\
  0 <= vb_len v < vb_size v /\
  vb_error v = 0 /\   (* [comment removed for export] *)
  vb_indent v = 0 /\
  vb_flags v = (if fin then VSB_FLAGS_FIN else VSB_FLAGS_LIVE) /\
  0 < vb_buf v /\ vb_buf v + vb_size v < 2^47 /\ vb_buf v mod 16 = 0 /\ vb_size v mod 16 = 0.

(* [comment removed for export] *)
Definition vsb_set_buf_size (v : vsb_rec) (b sz : Z) : vsb_rec :=
  VSBR (vb_error v) b sz (vb_len v) (vb_flags v) (vb_indent v).
Definition vsb_set_len (v : vsb_rec) (l : Z) : vsb_rec :=
  VSBR (vb_error v) (vb_buf v) (vb_size v) l (vb_flags v) (vb_indent v).
Definition vsb_set_error (v : vsb_rec) (e : Z) : vsb_rec :=
  VSBR e (vb_buf v) (vb_size v) (vb_len v) (vb_flags v) (vb_indent v).
Definition vsb_set_flags (v : vsb_rec) (f : Z) : vsb_rec :=
  VSBR (vb_error v) (vb_buf v) (vb_size v) (vb_len v) f (vb_indent v).

(* [comment removed for export] *)
Fixpoint vsb_dbl (k : nat) (ns sz : Z) : Z :=
  match k with O => ns | S k' => if ns <? sz then vsb_dbl k' (2 * ns) sz else ns end.
Definition vsb_extendsize (sz : Z) : Z :=
  if sz <? 4096 then vsb_dbl 9 16 sz else (sz + 4095) / 4096 * 4096.

Lemma vsb_dbl_ge : forall k ns sz, 0 < ns -> sz <= ns * 2 ^ Z.of_nat k -> sz <= vsb_dbl k ns sz /\ 0 < vsb_dbl k ns sz.
Proof.
  induction k as [|k IH]; intros ns sz Hns Hsz; cbn [vsb_dbl].
  - rewrite Z.pow_0_r in Hsz. lia.
  - destruct (Z.ltb_spec ns sz) as [Hlt|Hge]; [|lia].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hsz by lia. apply IH; lia.
Qed.
Lemma vsb_dbl_le : forall k ns sz, 0 < ns -> vsb_dbl k ns sz < Z.max (ns + 1) (2 * sz).
Proof.
  induction k as [|k IH]; intros ns sz Hns; cbn [vsb_dbl].
  - lia.
  - destruct (Z.ltb_spec ns sz) as [Hlt|Hge]; [|lia].
    specialize (IH (2 * ns) sz ltac:(lia)). lia.
Qed.
Lemma vsb_dbl_mod16 : forall k ns sz, ns mod 16 = 0 -> vsb_dbl k ns sz mod 16 = 0.
Proof.
  induction k as [|k IH]; intros ns sz H; cbn [vsb_dbl]; [exact H|].
  destruct (ns <? sz); [|exact H]. apply IH.
  replace (2 * ns) with (ns + ns) by lia. rewrite Z.add_mod, H by lia. reflexivity.
Qed.

Lemma vsb_extendsize_spec : forall sz, 16 <= sz <= 2^40 ->
  sz <= vsb_extendsize sz /\ vsb_extendsize sz < 2 * sz + 4096 /\ vsb_extendsize sz mod 16 = 0.
Proof.
  intros sz Hsz. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge].
  - destruct (vsb_dbl_ge 9 16 sz ltac:(lia)) as [A B]. { cbn. lia. }
    pose proof (vsb_dbl_le 9 16 sz ltac:(lia)) as C.
    pose proof (vsb_dbl_mod16 9 16 sz eq_refl) as D. lia.
  - split; [|split]; [lia|lia|].
    replace ((sz + 4095) / 4096 * 4096) with (((sz + 4095) / 4096 * 256) * 16) by lia.
    apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma vsb_extendsize_tight : forall sz, vsb_extendsize sz <= Z.max 4096 (sz + 4095).
Proof.
  intros sz. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge].
  - cbn [vsb_dbl Z.mul Pos.mul].
    repeat (match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b); [|lia] end). lia.
  - pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition WS_MAGIC       : Z := 0x35fac554.
Definition WS_EMU_MAGIC   : Z := 0x1c89b6ab.
Definition WS_ALLOC_MAGIC : Z := 0x22e7fd05.

Record ws_rec : Type := WSR {
  ws_id : list byte;  (* [comment removed for export] *)
  ws_s  : Z;          (* [comment removed for export] *)
  ws_f  : Z;          (* [comment removed for export] *)
  ws_r  : Z;          (* [comment removed for export] *)
  ws_e  : Z           (* [comment removed for export] *)
}.
Definition ws_cells (w : ws_rec) : list cell :=
  [ C4 (w64 WS_MAGIC); CB 4 (ws_id w); C8 (w64 (ws_s w)); C8 (w64 (ws_f w)); C8 (w64 (ws_r w)); C8 (w64 (ws_e w)) ].
Lemma ws_cells_size : forall w, length (ws_id w) = 4%nat -> cells_size (ws_cells w) = 40%nat.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Record wsemu_rec : Type := WER {
  we_len   : Z;   (* [comment removed for export] *)
  we_ws    : Z;   (* [comment removed for export] *)
  we_first : Z;   (* [comment removed for export] *)
  we_last  : Z    (* [comment removed for export] *)
}.
Definition wsemu_cells (e : wsemu_rec) : list cell :=
  [ C4 (w64 WS_EMU_MAGIC); C4 (w64 (we_len e)); C8 (w64 (we_ws e)); C8 (w64 (we_first e)); C8 (w64 (we_last e)) ].

Record wsalloc_rec : Type := WAR {
  wa_off  : Z;   (* [comment removed for export] *)
  wa_len  : Z;   (* [comment removed for export] *)
  wa_ptr  : Z;   (* [comment removed for export] *)
  wa_next : Z;   (* [comment removed for export] *)
  wa_prev : Z    (* [comment removed for export] *)
}.
Definition wsalloc_cells (a : wsalloc_rec) (pad : list byte) : list cell :=
  [ C4 (w64 WS_ALLOC_MAGIC); C4 (w64 (wa_off a)); C4 (w64 (wa_len a)); CB 4 pad;
    C8 (w64 (wa_ptr a)); C8 (w64 (wa_next a)); C8 (w64 (wa_prev a)) ].

(* [comment removed for export] *)
Definition wsemu_WS0 (wsbuf : Z) : wsemu_rec := WER 1016 0 0 (wsbuf + 16).
Definition wsemu_WS1 (wa : Z) : wsemu_rec := WER 1016 0 wa (wa + 24).
Definition wsalloc_WS1 (wsbuf vep : Z) : wsalloc_rec := WAR 0 312 vep 0 (wsbuf + 16).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition VEP_MAGIC : Z := 0x55cb9b82.

Inductive vf : Type :=
  Fflags | Fvsb | Furl | Fvc | Fdogzip | Fcb | Fcb_priv | Fcb_x | Fstate | Fstartup | Fesi_found | Fendtag | Femptytag | Fcanattr | Fremove | Fo_wait | Fo_pending | Fo_total | Fcrc | Fo_crc | Fcrcp | Fo_last | Fhack_p | Fver_p | Funtil | Funtil_p | Funtil_s | Fin_esi_tag | Fesicmt | Fesicmt_p | Fattr | Fattr_vsb | Fattr_delim | Fmatch | Fmatch_hit | Ftag_i | Fdostuff | Finclude_src | Finclude_continue | Fnm_skip | Fnm_verbatim | Fnm_pending | Flast_mark.
(* [comment removed for export] *)
Definition vf_index (f : vf) : N :=
  match f with
  | Fflags => 0
  | Fvsb => 1
  | Furl => 2
  | Fvc => 3
  | Fdogzip => 4
  | Fcb => 5
  | Fcb_priv => 6
  | Fcb_x => 7
  | Fstate => 8
  | Fstartup => 9
  | Fesi_found => 10
  | Fendtag => 11
  | Femptytag => 12
  | Fcanattr => 13
  | Fremove => 14
  | Fo_wait => 15
  | Fo_pending => 16
  | Fo_total => 17
  | Fcrc => 18
  | Fo_crc => 19
  | Fcrcp => 20
  | Fo_last => 21
  | Fhack_p => 22
  | Fver_p => 23
  | Funtil => 24
  | Funtil_p => 25
  | Funtil_s => 26
  | Fin_esi_tag => 27
  | Fesicmt => 28
  | Fesicmt_p => 29
  | Fattr => 30
  | Fattr_vsb => 31
  | Fattr_delim => 32
  | Fmatch => 33
  | Fmatch_hit => 34
  | Ftag_i => 35
  | Fdostuff => 36
  | Finclude_src => 37
  | Finclude_continue => 38
  | Fnm_skip => 39
  | Fnm_verbatim => 40
  | Fnm_pending => 41
  | Flast_mark => 42
  end%N.
Definition vf_beq (f g : vf) : bool := N.eqb (vf_index f) (vf_index g).
Lemma vf_index_inj : forall f g, vf_index f = vf_index g -> f = g.
Proof. intros f g H; destruct f; destruct g; try reflexivity; discriminate H. Qed.

Definition vep := vf -> Z.
Definition fupd (v : vep) (f : vf) (x : Z) : vep := fun g => if vf_beq g f then x else v g.

Lemma vf_beq_eq : forall f g, vf_beq f g = true <-> f = g.
Proof. intros f g; unfold vf_beq; rewrite N.eqb_eq; split; [apply vf_index_inj | intros ->; reflexivity]. Qed.
Lemma vf_beq_refl : forall f, vf_beq f f = true.
Proof. intros f. apply (proj2 (vf_beq_eq f f)). reflexivity. Qed.
Lemma fupd_same : forall v f x, fupd v f x f = x.
Proof. intros; unfold fupd; rewrite vf_beq_refl; reflexivity. Qed.
Lemma fupd_other : forall v f x g, g <> f -> fupd v f x g = v g.
Proof. intros v f x g H; unfold fupd. destruct (vf_beq g f) eqn:E; [apply vf_beq_eq in E; congruence | reflexivity]. Qed.

(* [comment removed for export] *)
Record vep_pads : Type := VPADS { p36 : list byte; p124 : list byte; p140 : list byte; p196 : list byte;
                                  p236 : list byte; p268 : list byte; p308 : list byte }.
Definition vep_pads_wf (q : vep_pads) : Prop :=
  length (p36 q) = 4%nat /\ length (p124 q) = 4%nat /\ length (p140 q) = 4%nat /\ length (p196 q) = 4%nat /\
  length (p236 q) = 4%nat /\ length (p268 q) = 4%nat /\ length (p308 q) = 4%nat.

(* [comment removed for export] *)
Definition vep_cells (v : vep) (tag : list byte) (q : vep_pads) : list cell :=
  [ C4 (w64 VEP_MAGIC); C4 (w64 (v Fflags)); C8 (w64 (v Fvsb)); C8 (w64 (v Furl)); C8 (w64 (v Fvc));
    C4 (w64 (v Fdogzip)); CB 4 (p36 q); C8 (w64 (v Fcb)); C8 (w64 (v Fcb_priv));
    C8 (w64 (v Fcb_x)); C8 (w64 (v Fstate)); C4 (w64 (v Fstartup)); C4 (w64 (v Fesi_found));
    C4 (w64 (v Fendtag)); C4 (w64 (v Femptytag)); C4 (w64 (v Fcanattr)); C4 (w64 (v Fremove));
    C8 (w64 (v Fo_wait)); C8 (w64 (v Fo_pending)); C8 (w64 (v Fo_total)); C4 (w64 (v Fcrc));
    CB 4 (p124 q); C8 (w64 (v Fo_crc)); C4 (w64 (v Fcrcp)); CB 4 (p140 q);
    C8 (w64 (v Fo_last)); C8 (w64 (v Fhack_p)); C8 (w64 (v Fver_p)); C8 (w64 (v Funtil));
    C8 (w64 (v Funtil_p)); C8 (w64 (v Funtil_s)); C4 (w64 (v Fin_esi_tag)); CB 4 (p196 q);
    C8 (w64 (v Fesicmt)); C8 (w64 (v Fesicmt_p)); C8 (w64 (v Fattr)); C8 (w64 (v Fattr_vsb));
    C4 (w64 (v Fattr_delim)); CB 4 (p236 q); C8 (w64 (v Fmatch)); C8 (w64 (v Fmatch_hit));
    CB 8 tag; C4 (w64 (v Ftag_i)); CB 4 (p268 q); C8 (w64 (v Fdostuff));
    C8 (w64 (v Finclude_src)); C4 (w64 (v Finclude_continue)); C4 (w64 (v Fnm_skip)); C4 (w64 (v Fnm_verbatim));
    C4 (w64 (v Fnm_pending)); C4 (w64 (v Flast_mark)); CB 4 (p308 q) ].

Lemma vep_cells_size : forall v tag q, length tag = 8%nat -> vep_pads_wf q -> cells_size (vep_cells v tag q) = 312%nat.
Proof. (intros v tag q Ht; (first [ intro dR_1; dand7 dR_1 as A B C D E F G | intros (A & B & C & D & E & F & G) ])). reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OFF_flags : Z := 4. Definition OFF_vsb : Z := 8. Definition OFF_url : Z := 16. Definition OFF_vc : Z := 24.
Definition OFF_dogzip : Z := 32. Definition OFF_cb : Z := 40. Definition OFF_cb_priv : Z := 48. Definition OFF_cb_x : Z := 56.
Definition OFF_state : Z := 64. Definition OFF_startup : Z := 72. Definition OFF_esi_found : Z := 76. Definition OFF_endtag : Z := 80.
Definition OFF_emptytag : Z := 84. Definition OFF_canattr : Z := 88. Definition OFF_remove : Z := 92. Definition OFF_o_wait : Z := 96.
Definition OFF_o_pending : Z := 104. Definition OFF_o_total : Z := 112. Definition OFF_crc : Z := 120. Definition OFF_o_crc : Z := 128.
Definition OFF_crcp : Z := 136. Definition OFF_o_last : Z := 144. Definition OFF_hack_p : Z := 152. Definition OFF_ver_p : Z := 160.
Definition OFF_until : Z := 168. Definition OFF_until_p : Z := 176. Definition OFF_until_s : Z := 184. Definition OFF_in_esi_tag : Z := 192.
Definition OFF_esicmt : Z := 200. Definition OFF_esicmt_p : Z := 208. Definition OFF_attr : Z := 216. Definition OFF_attr_vsb : Z := 224.
Definition OFF_attr_delim : Z := 232. Definition OFF_match : Z := 240. Definition OFF_match_hit : Z := 248. Definition OFF_tag_i : Z := 264.
Definition OFF_dostuff : Z := 272. Definition OFF_include_src : Z := 280. Definition OFF_include_continue : Z := 288. Definition OFF_nm_skip : Z := 292.
Definition OFF_nm_verbatim : Z := 296. Definition OFF_nm_pending : Z := 300. Definition OFF_last_mark : Z := 304.

(* [comment removed for export] *)
Definition bool01 (z : Z) : Prop := z = 0 \/ z = 1.

Definition vep_cnt_inv (v : vep) (n size : Z) : Prop :=
  0 <= n <= size /\ size < 2^26 /\
  0 <= v Fo_wait <= n /\ 0 <= v Fo_pending <= n /\ 0 <= v Fo_total <= n /\
  0 <= v Fo_crc <= n /\ 0 <= v Fo_last <= n /\ 0 <= v Fcb_x <= n /\ v Fo_last <= v Fcb_x.

Definition vep_flags_inv (v : vep) : Prop :=
  0 <= v Fflags < 16 /\ v Fdogzip = 0 /\
  bool01 (v Fstartup) /\ bool01 (v Fesi_found) /\ bool01 (v Fendtag) /\ bool01 (v Femptytag) /\
  bool01 (v Fcanattr) /\ bool01 (v Fremove) /\ bool01 (v Fin_esi_tag) /\ bool01 (v Finclude_continue) /\
  bool01 (v Flast_mark) /\
  0 <= v Ftag_i <= 7 /\
  (v Fattr_delim = 0 \/ v Fattr_delim = 0x20 \/ v Fattr_delim = 0x22 \/ v Fattr_delim = 0x27) /\
  0 <= v Fcrc < 2^32 /\ 0 <= v Fcrcp < 2^32 /\
  0 <= v Fnm_skip < 2^32 /\ 0 <= v Fnm_verbatim < 2^32 /\ 0 <= v Fnm_pending < 2^32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition VFP_CTX_MAGIC : Z := 0x61d9d3e5.
Definition HTTP_MAGIC    : Z := 0x6428b5c9.
Definition WORKER_MAGIC  : Z := 0x6391adcf.

(* [comment removed for export] *)
Definition vc_cells (pad : list byte) (resp wrk : Z) (rest : list byte) : list cell :=
  [ C4 (w64 VFP_CTX_MAGIC); CB 12 pad; C8 (w64 resp); C8 (w64 wrk); CB 40 rest ].
(* [comment removed for export] *)
Definition wrk_cells (pad : list byte) (rest : list byte) : list cell :=
  [ C4 (w64 WORKER_MAGIC); CB 28 pad; C8 (w64 0); CB 144 rest ].
