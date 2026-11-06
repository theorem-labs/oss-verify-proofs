(** * reac-pw/fuzz_link (asan, image A): the memory FILE's lemmas, link's instance, and its image checks.

    The A twin of lib/MemFile.v (plain). The definitions are in AMemFileSink.v (re-exported here). This file has:
    - frame lemmas: [amemfile_at] reads only the first [AMF_ZEROED] bytes of its block; [amf_gi] / [amf_sink] add
      the three heads and the three stdio words;
    - across a callee's A journal ([YCbq.ajournal]): a live block outside the callee's footprint stays live with
      its bytes ([amf_block_kept]), and the whole kept state, ledger included, survives a callee whose footprint
      is closed (no sink token) and avoids the kept block ([amf_gi_ledger_kept]);
    - the kept block in the A allocator ledger: the AR laws give its alignment, range, presence, ownership and
      ASan shadow (each 8-byte granule of the block marked addressable, [block_shadow]; the shadow of its hull
      readable, [shadow_hull_vis]; the AR laws state no redzone) ([amf_block_facts]);
    - the accounting of the kept block ([amf_blocks_post_bytes]);
    - the states the run reaches, as stores ([amf_state], as the plain [mf_state]) and the lemmas that every such
      state satisfies [amemfile_at], [amf_gi] and [amf_sink];
    - link's asan instance [link_amf] and [link_asink_head], each value read from link's asan image by the
      instruction list [link_amf_code], checked against the image's bytes ([link_amf_code_ok]). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK04 YA0i YA0n YP09 YP02 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Export AMemFileSink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** Frame lemmas *)
Section c.
Variable segs : list Segment.
Variable MS : amemfile_syms.
Local Notation fld m f off n v := (val_mem segs m (f + off) n v).

Lemma amf_val_mem_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma amemfile_at_frame : forall (m m' : word -> option byte) f,
  (forall x, f <= x < f + AMF_ZEROED -> mbyte segs m' x = mbyte segs m x) ->
  amemfile_at segs MS m f -> amemfile_at segs MS m' f.
Proof.
  intros m m' f Hfr (Hf0 & Hf1 & Hf2 & Hs & Hfl & Hom & Hw & Hc).
  assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_ZEROED ->
    val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
  { intros off n v H0 H1 Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
  unfold AMF_ZEROED, AMF_COOKIE in *.
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold amemfile_static in *. unfold AMF_COOKIE in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end; (apply HV; [lia | cbn; lia | assumption]).
  - destruct Hfl as [H|H]; [left|right]; (apply HV; [lia | cbn; lia | exact H]).
  - destruct Hom as [H|H]; [left|right]; (apply HV; [lia | cbn; lia | exact H]).
  - destruct Hw as (H8 & H16 & [(H1 & H2 & H3) | (k & Hk & H1 & H2 & H3)]).
    + split; [apply HV; [lia | cbn; lia | exact H8]|]. split; [apply HV; [lia | cbn; lia | exact H16]|].
      left. split; [|split]; (apply HV; [lia | cbn; lia | assumption]).
    + split; [apply HV; [lia | cbn; lia | exact H8]|]. split; [apply HV; [lia | cbn; lia | exact H16]|].
      right. exists k. split; [exact Hk|]. split; [|split]; (apply HV; [lia | cbn; lia | assumption]).
  - destruct Hc as (pos & len & Hp & Hl & H1 & H2). exists pos, len. split; [exact Hp|]. split; [exact Hl|].
    unfold AMF_COOKIE. split; (apply HV; [lia | cbn; lia | assumption]).
Qed.

Lemma amf_heads_frame : forall (m m' : word -> option byte) v,
  (forall a, amf_head_addr MS a -> mbyte segs m' a = mbyte segs m a) ->
  amf_heads segs MS m v -> amf_heads segs MS m' v.
Proof.
  intros m m' v Hfr (H1 & H2 & H3). unfold amf_heads.
  split; [|split]; (eapply amf_val_mem_frame; [|eassumption]); intros x Hx; apply Hfr;
    unfold amf_head_addr; cbn in Hx; lia.
Qed.

Lemma amf_env_frame : forall (m m' : word -> option byte),
  (forall a, amf_env_addr MS a -> mbyte segs m' a = mbyte segs m a) ->
  amf_env segs MS m -> amf_env segs MS m'.
Proof.
  intros m m' Hfr (H1 & H2 & H3). unfold amf_env.
  split; [|split]; (eapply amf_val_mem_frame; [|eassumption]); intros x Hx; apply Hfr;
    unfold amf_env_addr; cbn in Hx; lia.
Qed.

(** [amf_gi] reads the three heads and the first [AMF_ZEROED] bytes of the kept block. *)
Lemma amf_gi_frame : forall (m m' : word -> option byte) T,
  (forall a, amf_head_addr MS a -> mbyte segs m' a = mbyte segs m a) ->
  (forall f x, In (f, AMF_BLOCK) T -> f <= x < f + AMF_ZEROED -> mbyte segs m' x = mbyte segs m x) ->
  amf_gi segs MS T m -> amf_gi segs MS T m'.
Proof.
  intros m m' T Hh Hb [(H0 & HT) | (f & Hf & HT & Hm)].
  - left. split; [exact (amf_heads_frame m m' 0 Hh H0) | exact HT].
  - right. exists f. split; [exact (amf_heads_frame m m' f Hh Hf)|]. split; [exact HT|].
    apply (amemfile_at_frame m m' f); [|exact Hm]. intros x Hx. apply (Hb f x); [rewrite HT; left; reflexivity | exact Hx].
Qed.

(** [amf_sink] is kept by a step that leaves the stdio words, the heads and the FILE's bytes as they were. *)
Lemma amf_sink_frame : forall (m m' : word -> option byte),
  (forall a, amf_env_addr MS a -> mbyte segs m' a = mbyte segs m a) ->
  (forall a, amf_head_addr MS a -> mbyte segs m' a = mbyte segs m a) ->
  (forall f, amf_heads segs MS m f -> amemfile_at segs MS m f ->
     forall x, f <= x < f + AMF_ZEROED -> mbyte segs m' x = mbyte segs m x) ->
  amf_sink segs MS m -> amf_sink segs MS m'.
Proof.
  intros m m' He Hh Hb (Henv & H). split; [exact (amf_env_frame m m' He Henv)|].
  destruct H as [H0 | (f & Hf & Hm)].
  - left. exact (amf_heads_frame m m' 0 Hh H0).
  - right. exists f. split; [exact (amf_heads_frame m m' f Hh Hf)|].
    exact (amemfile_at_frame m m' f (Hb f Hf Hm) Hm).
Qed.

(** What close_file reads on this FILE ([__stdio_exit]'s list loop, asan 0x969b0-0x96a08, checked in
    [link_amf_code]): [lock] = -1 (no __lockfile), [write] = mwrite (called only when [wpos <> wbase]),
    [rpos] = [rend] (no seek), [next] = 0 (the loop ends). *)
Lemma amemfile_close_reads : forall m f, amemfile_at segs MS m f ->
  fld m f 140 4 AU32M1 /\ fld m f 72 8 (amf_write MS) /\ fld m f 8 8 0 /\ fld m f 16 8 0 /\
  fld m f 112 8 0.
Proof.
  intros m f (_ & _ & _ & Hs & _ & _ & (H8 & H16 & _) & _). unfold amemfile_static in Hs.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; assumption.
Qed.

(** ** The states the run reaches, as stores (the plain [mf_state]: fmemopen's memset and stores, __ofl_add's
    [f->next = 0], the words later calls write, and the three heads). *)
Definition amf_upd (m : word -> option byte) (a : Z) (n : nat) (v : Z) : word -> option byte :=
  fun w => if (a <=? bv_unsigned w) && (bv_unsigned w <? a + Z.of_nat n)
           then Some (Z_to_bv 8 (YO0f.le_byte v n (Z.to_nat (bv_unsigned w - a)))) else m w.

Definition amf_fm (m : word -> option byte) (f : Z) : word -> option byte :=
  amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd
  (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd
    m f 272 0)                                (* +0xbc memset (f, 0, 272) *)
    (f + 152) 8 (f + AMF_COOKIE))             (* +0xcc sd a0,0x98(s0) *)
    (f + 88) 8 (f + AMF_BUF))                 (* +0xd4 sd a2,0x58(s0) *)
    (f + 96) 8 AMF_BUFSIZ)                    (* +0xd8 sd a0,0x60(s0) *)
    (f + 120) 4 AU32M1)                       (* +0xdc sw a1,0x78(s0): fd = -1 *)
    (f + 144) 4 AU32M1)                       (* +0xe0 sw a1,0x90(s0): lbf = EOF *)
    (f + (AMF_COOKIE + 16)) 8 (amf_size MS))  (* +0xfc sd s2,0xf8(s0) *)
    (f + (AMF_COOKIE + 24)) 8 (amf_buf MS))   (* +0x100 sd s1,0x100(s0) *)
    (f + (AMF_COOKIE + 32)) 4 (amf_mode MS))  (* +0x108 sw a0,0x108(s0) *)
    (f + 0) 4 AF_NORD)                        (* +0x128 sw a0,0(s0) *)
    (f + 24) 8 (amf_close MS))                (* +0x190 sd a3,0x18(s0) *)
    (f + 64) 8 (amf_read MS))                 (* +0x194 sd a0,0x40(s0) *)
    (f + 72) 8 (amf_write MS))                (* +0x198 sd a1,0x48(s0) *)
    (f + 80) 8 (amf_seek MS))                 (* +0x19c sd a2,0x50(s0) *)
    (f + 140) 4 AU32M1)                       (* +0x1a8 sw a0,0x8c(s0): lock = -1 (__libc.threaded = 0) *)
    (f + 112) 8 0.                            (* __ofl_add +0x18 sd a1,0x70(s0): next = old head = 0 *)

Definition amf_dynw (m : word -> option byte) (f fl om wend wpos wbase pos len : Z) : word -> option byte :=
  amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd (amf_upd m
    (f + 0) 4 fl) (f + 136) 4 om) (f + 32) 8 wend) (f + 40) 8 wpos) (f + 56) 8 wbase)
    (f + AMF_COOKIE) 8 pos) (f + (AMF_COOKIE + 8)) 8 len.

Definition amf_heads_set (m : word -> option byte) (f : Z) : word -> option byte :=
  amf_upd (amf_upd (amf_upd m (amf_ofl_head MS) 8 f) (amf_sink_addr MS) 8 f) (amf_say_addr MS) 8 f.

Definition amf_state (m : word -> option byte) (f fl om wend wpos wbase pos len : Z) : word -> option byte :=
  amf_heads_set (amf_dynw (amf_fm m f) f fl om wend wpos wbase pos len) f.

Definition amf_open (m : word -> option byte) (f : Z) : word -> option byte :=
  amf_state m f AF_NORD 0 0 0 0 0 0.

Lemma amf_unsigned64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hx.
Qed.

Lemma amf_upd_in : forall m a n v x, 0 <= x < 2 ^ 64 -> a <= x < a + Z.of_nat n ->
  mbyte segs (amf_upd m a n v) x = Some (Z_to_bv 8 (YO0f.le_byte v n (Z.to_nat (x - a)))).
Proof.
  intros m a n v x Hx Ha. unfold mbyte, amf_upd. rewrite (amf_unsigned64 x Hx).
  replace ((a <=? x) && (x <? a + Z.of_nat n)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma amf_upd_out : forall m a n v x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + Z.of_nat n) ->
  mbyte segs (amf_upd m a n v) x = mbyte segs m x.
Proof.
  intros m a n v x Hx Ha. unfold mbyte, amf_upd. rewrite (amf_unsigned64 x Hx).
  replace ((a <=? x) && (x <? a + Z.of_nat n)) with false; [reflexivity|].
  symmetry. apply andb_false_iff.
  destruct (Z.leb_spec a x) as [H|H]; [right; apply Z.ltb_ge; lia | left; reflexivity].
Qed.

Lemma amf_le_byte_0 : forall n k, YO0f.le_byte 0 n k = 0.
Proof. intros n k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. Qed.

Lemma amf_val_mem_upd_same : forall m a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem segs (amf_upd m a n v) a n v.
Proof.
  intros m a n v H0 H1 k Hk. rewrite amf_upd_in by lia.
  replace (a + Z.of_nat k - a) with (Z.of_nat k) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma amf_val_mem_upd_other : forall m a n v b k w, 0 <= b -> b + Z.of_nat k <= 2 ^ 64 ->
  a + Z.of_nat n <= b \/ b + Z.of_nat k <= a ->
  val_mem segs m b k w -> val_mem segs (amf_upd m a n v) b k w.
Proof. intros m a n v b k w H0 H1 H2 H j Hj. rewrite amf_upd_out by lia. exact (H j Hj). Qed.

Lemma amf_val_mem_upd_zero : forall m a n b k, 0 <= a -> a <= b -> b + Z.of_nat k <= a + Z.of_nat n ->
  a + Z.of_nat n <= 2 ^ 64 -> val_mem segs (amf_upd m a n 0) b k 0.
Proof.
  intros m a n b k H0 H1 H2 H3 j Hj. rewrite amf_upd_in by lia. rewrite !amf_le_byte_0. reflexivity.
Qed.

Ltac amf_ar := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *; lia.

Ltac amf_fld :=
  repeat first
    [ apply amf_val_mem_upd_same; amf_ar
    | apply amf_val_mem_upd_zero; amf_ar
    | apply amf_val_mem_upd_other; [amf_ar | amf_ar | amf_ar | ] ].

Lemma amf_fm_out : forall m f x, 0 <= x < 2 ^ 64 -> ~ (f <= x < f + AMF_ZEROED) ->
  mbyte segs (amf_fm m f) x = mbyte segs m x.
Proof.
  intros m f x Hx Hn. unfold amf_fm, AMF_ZEROED, AMF_COOKIE in *.
  repeat (rewrite amf_upd_out; [|exact Hx|cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). reflexivity.
Qed.

Lemma amf_dynw_out : forall m f fl om wend wpos wbase pos len x, 0 <= x < 2 ^ 64 -> ~ (f <= x < f + AMF_ZEROED) ->
  mbyte segs (amf_dynw m f fl om wend wpos wbase pos len) x = mbyte segs m x.
Proof.
  intros m f fl om wend wpos wbase pos len x Hx Hn. unfold amf_dynw, AMF_ZEROED, AMF_COOKIE in *.
  repeat (rewrite amf_upd_out; [|exact Hx|cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). reflexivity.
Qed.

(** Where the block may lie: nonzero, 16-aligned, clear of the three heads and of the three stdio words. *)
Definition amf_apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

Definition amf_place (f : Z) : Prop :=
  0 < f /\ f + AMF_BLOCK <= 2 ^ 64 /\ f mod 16 = 0 /\
  amf_apart f AMF_BLOCK (amf_sink_addr MS) 8 /\ amf_apart f AMF_BLOCK (amf_say_addr MS) 8 /\
  amf_apart f AMF_BLOCK (amf_ofl_head MS) 8 /\ amf_apart f AMF_BLOCK (amf_threaded MS) 1 /\
  amf_apart f AMF_BLOCK (amf_need_locks MS) 1 /\ amf_apart f AMF_BLOCK (amf_ofl_lock MS) 4.

(** The three heads: in range, pairwise apart and apart from the three stdio words; the size is not negative. *)
Definition amf_heads_ok : Prop :=
  0 <= amf_sink_addr MS /\ amf_sink_addr MS + 8 <= 2 ^ 64 /\ 0 <= amf_say_addr MS /\ amf_say_addr MS + 8 <= 2 ^ 64 /\
  0 <= amf_ofl_head MS /\ amf_ofl_head MS + 8 <= 2 ^ 64 /\
  0 <= amf_threaded MS /\ amf_threaded MS + 1 <= 2 ^ 64 /\ 0 <= amf_need_locks MS /\ amf_need_locks MS + 1 <= 2 ^ 64 /\
  0 <= amf_ofl_lock MS /\ amf_ofl_lock MS + 4 <= 2 ^ 64 /\
  amf_apart (amf_sink_addr MS) 8 (amf_say_addr MS) 8 /\ amf_apart (amf_sink_addr MS) 8 (amf_ofl_head MS) 8 /\
  amf_apart (amf_say_addr MS) 8 (amf_ofl_head MS) 8 /\
  amf_apart (amf_sink_addr MS) 8 (amf_threaded MS) 1 /\ amf_apart (amf_say_addr MS) 8 (amf_threaded MS) 1 /\
  amf_apart (amf_ofl_head MS) 8 (amf_threaded MS) 1 /\
  amf_apart (amf_sink_addr MS) 8 (amf_need_locks MS) 1 /\ amf_apart (amf_say_addr MS) 8 (amf_need_locks MS) 1 /\
  amf_apart (amf_ofl_head MS) 8 (amf_need_locks MS) 1 /\
  amf_apart (amf_sink_addr MS) 8 (amf_ofl_lock MS) 4 /\ amf_apart (amf_say_addr MS) 8 (amf_ofl_lock MS) 4 /\
  amf_apart (amf_ofl_head MS) 8 (amf_ofl_lock MS) 4 /\
  0 <= amf_size MS.

Lemma amf_heads_set_file : forall m f, amf_place f -> forall x, f <= x < f + AMF_ZEROED ->
  mbyte segs (amf_heads_set m f) x = mbyte segs m x.
Proof.
  intros m f (H0 & H1 & _ & Hs & Hy & Ho & _) x Hx. unfold amf_heads_set, amf_apart, AMF_ZEROED, AMF_BLOCK in *.
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity.
Qed.

(** Every FILE state the code leaves at a return satisfies [amemfile_at]. *)
Lemma amf_state_at : forall m f fl om wend wpos wbase pos len,
  amf_place f -> 0 <= amf_size MS ->
  fl = AF_NORD \/ fl = AF_NORD + AF_ERR -> om = 0 \/ om = AU32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= AMF_BUFSIZ /\ wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF + k /\ wbase = f + AMF_BUF) ->
  0 <= pos <= len -> len <= amf_size MS ->
  amemfile_at segs MS (amf_state m f fl om wend wpos wbase pos len) f.
Proof.
  intros m f fl om wend wpos wbase pos len HP Hsz Hfl Hom Hw Hp Hl.
  pose proof HP as (Hf0 & Hf1 & Hf2 & _).
  unfold amf_state. apply (amemfile_at_frame (amf_dynw (amf_fm m f) f fl om wend wpos wbase pos len)).
  { intros x Hx. exact (amf_heads_set_file _ f HP x Hx). }
  unfold amf_dynw, amf_fm.
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold amemfile_static. repeat match goal with |- _ /\ _ => split end; amf_fld.
  - destruct Hfl as [-> | ->]; [left | right]; amf_fld.
  - destruct Hom as [-> | ->]; [left | right]; amf_fld.
  - split; [amf_fld|]. split; [amf_fld|].
    destruct Hw as [(-> & -> & ->) | (k & Hk & -> & -> & ->)].
    + left. split; [|split]; amf_fld.
    + right. exists k. split; [exact Hk|]. split; [|split]; amf_fld.
  - exists pos, len. split; [exact Hp|]. split; [exact Hl|]. split; amf_fld.
Qed.

Lemma amf_state_heads : forall m f fl om wend wpos wbase pos len, amf_heads_ok ->
  amf_heads segs MS (amf_state m f fl om wend wpos wbase pos len) f.
Proof.
  intros m f fl om wend wpos wbase pos len
    (Hs0 & Hs1 & Hy0 & Hy1 & Ho0 & Ho1 & _ & _ & _ & _ & _ & _ & Hsy & Hso & Hyo & _).
  unfold amf_state, amf_heads_set, amf_heads, amf_apart in *.
  split; [|split].
  - apply amf_val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply amf_val_mem_upd_same; cbn; lia.
  - apply amf_val_mem_upd_same; cbn; lia.
  - apply amf_val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply amf_val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply amf_val_mem_upd_same; cbn; lia.
Qed.

(** The GI conjunct's second arm, and the post's clause, hold at every such state. *)
Lemma amf_state_gi : forall m f fl om wend wpos wbase pos len,
  amf_place f -> amf_heads_ok ->
  fl = AF_NORD \/ fl = AF_NORD + AF_ERR -> om = 0 \/ om = AU32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= AMF_BUFSIZ /\ wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF + k /\ wbase = f + AMF_BUF) ->
  0 <= pos <= len -> len <= amf_size MS ->
  amf_gi segs MS [(f, AMF_BLOCK)] (amf_state m f fl om wend wpos wbase pos len).
Proof.
  intros m f fl om wend wpos wbase pos len HP HH Hfl Hom Hw Hp Hl.
  right. exists f. split; [exact (amf_state_heads m f fl om wend wpos wbase pos len HH)|].
  split; [reflexivity|].
  apply amf_state_at; try assumption.
  destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
  exact H.
Qed.

(** A word apart from the block and the three heads keeps its value in every such state. (A lemma of its own,
    so that each [lia] sees four disjunctions, not the twenty of [amf_place] and [amf_heads_ok].) *)
Lemma amf_state_keeps : forall m f fl om wend wpos wbase pos len a n v,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> amf_apart f AMF_BLOCK a (Z.of_nat n) ->
  amf_apart (amf_sink_addr MS) 8 a (Z.of_nat n) -> amf_apart (amf_say_addr MS) 8 a (Z.of_nat n) ->
  amf_apart (amf_ofl_head MS) 8 a (Z.of_nat n) ->
  val_mem segs m a n v -> val_mem segs (amf_state m f fl om wend wpos wbase pos len) a n v.
Proof.
  intros m f fl om wend wpos wbase pos len a n v Ha0 Ha1 Haf Has Hay Hao Hv k Hk. unfold amf_state, amf_heads_set.
  unfold amf_apart, AMF_BLOCK, AMF_ZEROED in *.
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite amf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite amf_dynw_out by (unfold AMF_ZEROED; lia). rewrite amf_fm_out by (unfold AMF_ZEROED; lia).
  exact (Hv k Hk).
Qed.

Lemma amf_state_env : forall m f fl om wend wpos wbase pos len,
  amf_place f -> amf_heads_ok -> amf_env segs MS m ->
  amf_env segs MS (amf_state m f fl om wend wpos wbase pos len).
Proof.
  intros m f fl om wend wpos wbase pos len HP HH (Ht & Hn & Hl).
  destruct HP as (_ & _ & _ & _ & _ & _ & Hft & Hfn & Hfl).
  destruct HH as (_ & _ & _ & _ & _ & _ & Ht0 & Ht1 & Hn0 & Hn1 & Hl0 & Hl1 & _ & _ & _ &
    Hst & Hyt & Hot & Hsn & Hyn & Hon & Hsl & Hyl & Hol & _).
  split; [|split].
  - apply amf_state_keeps; [exact Ht0 | exact Ht1 | exact Hft | exact Hst | exact Hyt | exact Hot | exact Ht].
  - apply amf_state_keeps; [exact Hn0 | exact Hn1 | exact Hfn | exact Hsn | exact Hyn | exact Hon | exact Hn].
  - apply amf_state_keeps; [exact Hl0 | exact Hl1 | exact Hfl | exact Hsl | exact Hyl | exact Hol | exact Hl].
Qed.

Lemma amf_state_sink : forall m f fl om wend wpos wbase pos len,
  amf_place f -> amf_heads_ok ->
  fl = AF_NORD \/ fl = AF_NORD + AF_ERR -> om = 0 \/ om = AU32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= AMF_BUFSIZ /\ wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF + k /\ wbase = f + AMF_BUF) ->
  0 <= pos <= len -> len <= amf_size MS ->
  amf_env segs MS m -> amf_sink segs MS (amf_state m f fl om wend wpos wbase pos len).
Proof.
  intros m f fl om wend wpos wbase pos len HP HH Hfl Hom Hw Hp Hl He.
  apply (amf_sink_of_gi segs MS [(f, AMF_BLOCK)]); [apply amf_state_gi; assumption|].
  exact (amf_state_env m f fl om wend wpos wbase pos len HP HH He).
Qed.

End c.

(** ** Across a callee's A journal *)
Definition zz_eq_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(** A callee's footprint avoids every byte of the blocks [T]. *)
Definition amf_fp_avoids (FP T : list (Z * Z)) : Prop :=
  forall p n i, In (p, n) T -> 0 <= i < req_size n -> ~ inFP FP (p + i).

Section k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable MS : amemfile_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(** A live block outside the callee's footprint stays live, with its bytes ([ajournal]'s block clauses). *)
Lemma amf_block_kept : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k p n,
  YCbq.ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> 0 < req_size n -> (forall i, 0 <= i < req_size n -> ~ inFP FP (p + i)) ->
  In (p, n) (ablocks B ly' S') /\
  (forall i, 0 <= i < req_size n -> mbyte segs (rd W' mem') (p + i) = mbyte segs (rd W mem) (p + i)).
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p n HJ Hin Hpos Hav.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & Hgone & _).
  assert (Hin' : In (p, n) (ablocks B ly' S')).
  { destruct (in_dec zz_eq_dec (p, n) (ablocks B ly' S')) as [H|H]; [exact H|].
    exfalso. apply (Hav 0); [lia|]. exact (Hgone p n 0 Hin H ltac:(lia)). }
  split; [exact Hin'|].
  intros i Hi. eapply mbyte_of_aview. exact (F2 p n i Hin Hin' Hi (Hav i Hi)).
Qed.

(** The kept state survives a callee whose footprint is closed (no sink token: the open-file head is not
    spared, so the journal keeps it) and avoids the kept block, when the heads and the stdio words are image
    bytes outside the allocator's statics and errno. *)
Lemma amf_gi_ledger_kept : forall STK sp0 FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k T,
  YCbq.ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  (forall a, amf_head_addr MS a \/ amf_env_addr MS a ->
     in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
  amf_fp_avoids FP T ->
  amf_gi_ledger B segs MS ly S T (rd W mem) -> amf_env segs MS (rd W mem) ->
  amf_gi_ledger B segs MS ly' S' T (rd W' mem') /\ amf_env segs MS (rd W' mem').
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k T HJ Hc Himg Hav (HG & Hincl) He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  assert (Hi : forall a, amf_head_addr MS a \/ amf_env_addr MS a -> mbyte segs (rd W' mem') a = mbyte segs (rd W mem) a).
  { intros a Ha. destruct (Himg a Ha) as (H1 & H2 & H3). eapply mbyte_of_aview.
    exact (F3 a H1 H2 H3 (fp_spares_closed FP a Hc)). }
  assert (Hb : forall f, In (f, AMF_BLOCK) T ->
    In (f, AMF_BLOCK) (ablocks B ly' S') /\
    (forall x, f <= x < f + AMF_BLOCK -> mbyte segs (rd W' mem') x = mbyte segs (rd W mem) x)).
  { intros f Hf. assert (Hr : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
    assert (Hp0 : 0 < req_size AMF_BLOCK) by (rewrite Hr; unfold AMF_BLOCK; lia).
    destruct (amf_block_kept STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f AMF_BLOCK HJ (Hincl _ Hf) Hp0
      (fun i Hi' => Hav f AMF_BLOCK i Hf Hi')) as [Hin' Hby].
    split; [exact Hin'|]. intros x Hx. replace x with (f + (x - f)) by lia. apply Hby. rewrite Hr. lia. }
  split; [split|].
  - apply (amf_gi_frame segs MS (rd W mem) (rd W' mem') T); [intros a Ha; exact (Hi a (or_introl Ha)) | | exact HG].
    intros f x Hf Hx. apply (proj2 (Hb f Hf)). unfold AMF_ZEROED, AMF_BLOCK in *. lia.
  - intros [p n] Hpn. destruct (amf_gi_shape segs MS T _ HG) as [-> | (f & ->)]; [destruct Hpn|].
    destruct Hpn as [Hpn | []]. injection Hpn as <- <-. exact (proj1 (Hb f (or_introl eq_refl))).
  - apply (amf_env_frame segs MS (rd W mem) (rd W' mem')); [intros a Ha; exact (Hi a (or_intror Ha)) | exact He].
Qed.

End k.

(** ** The kept block in the A allocator ledger: the AR laws give its range, presence, ownership and shadow. *)
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

Lemma amf_block_facts : forall ly S (W : world segs) mem md f,
  AR segs B ly S W mem md -> In (f, AMF_BLOCK) (ablocks B ly S) ->
  f mod 16 = 0 /\ 4096 <= f /\ f + AMF_BLOCK <= alloc_ceiling /\ in_app f AMF_BLOCK /\
  (forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img segs a) /\
  block_shadow (aview segs (w_H W) mem) SHADOW_OFF f AMF_BLOCK /\
  shadow_hull_vis (aview segs (w_H W) mem) f AMF_BLOCK.
Proof.
  intros ly S W mem md f HAR Hin.
  assert (Hr : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
  pose proof (al_blocks _ _ LAWS ly S W mem md f AMF_BLOCK HAR Hin) as (H16 & Hlo & Hhi & Happ & Hby & _ & _).
  pose proof (al_shadow _ _ LAWS ly S W mem md f AMF_BLOCK HAR Hin) as (Hsh & Hhull).
  rewrite Hr in *.
  split; [exact H16|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Happ|].
  split; [|split; [exact Hsh | exact Hhull]].
  intros a Ha. destruct (Hby a Ha) as [Hp Ho]. split; [exact Hp|]. split; [exact Ho|].
  refine (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR _)).
  left. exists f, AMF_BLOCK. split; [exact Hin | rewrite Hr; exact Ha].
Qed.

End b.

(** ** Accounting of the kept block *)
Lemma kept_bytes_app : forall l1 l2, kept_bytes (l1 ++ l2) = kept_bytes l1 + kept_bytes l2.
Proof.
  unfold kept_bytes. induction l1 as [|b l1 IH]; intros l2; cbn [app fold_right]; [reflexivity|].
  rewrite IH. apply Z.add_assoc.
Qed.

Lemma kept_bytes_perm : forall l1 l2, Permutation l1 l2 -> kept_bytes l1 = kept_bytes l2.
Proof.
  unfold kept_bytes. intros l1 l2 H.
  induction H as [| x l l' _ IH | x y l | l l' l'' _ IH1 _ IH2]; cbn [fold_right].
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite !Z.add_assoc, (Z.add_comm (snd y) (snd x)). reflexivity.
  - rewrite IH1. exact IH2.
Qed.

Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(** The A ledger's live bytes are the sum of its live blocks' sizes. *)
Lemma blocks_bytes_ablocks : forall ly S, kept_bytes (ablocks B ly S) = blocks_bytes S.
Proof.
  intros ly S. unfold kept_bytes, ablocks, blocks, blocks_bytes.
  induction (st_chunks S) as [|c l IH]; [reflexivity|].
  simpl. destruct (is_alloc c); simpl; [rewrite IH; reflexivity | exact IH].
Qed.

(** A call that keeps [D] more raises the live bytes by exactly what the kept list grows. *)
Lemma amf_blocks_post_bytes : forall ly S ly' S' T T',
  amf_blocks_post T T' (ablocks B ly S) (ablocks B ly' S') ->
  blocks_bytes S' + kept_bytes T = blocks_bytes S + kept_bytes T'.
Proof.
  intros ly S ly' S' T T' (D & -> & HP).
  rewrite <- (blocks_bytes_ablocks ly S), <- (blocks_bytes_ablocks ly' S').
  rewrite (kept_bytes_perm _ _ HP), !kept_bytes_app. lia.
Qed.

End a.

(** fmemopen's request is a primary-size, model-admitted size ([ml_malloc]'s [0 <= n < MALLOC_MAX]). *)
Lemma amf_block_size_ok : 0 <= AMF_BLOCK < MALLOC_MAX.
Proof. unfold AMF_BLOCK, MALLOC_MAX. lia. Qed.

(** ** The harness journal's footprint [amf_harness_fp] (AMemFileSink.v)

    The target call's journal footprint is [amf_harness_fp T] for the kept blocks [T] of the call's start: pcap's
    [[sink_token]] before the first mark, [[sink_token; (f, f + AMF_BLOCK)]] after it. It is always sink-open
    (the token), it covers every byte of each kept block, and the journal's write clause then grants those bytes
    ([amf_harness_fp_grants]); [amf_gi] fixes which form a call has ([amf_harness_fp_of_gi]) and the post's
    [amf_blocks_post] with [amf_gi] gives the next call's ([amf_harness_fp_next]: unchanged once the FILE is open;
    on the first marking call, the FILE's range is added exactly when the call keeps the block). *)
Lemma amf_harness_fp_nil : amf_harness_fp [] = [YI16.sink_token].
Proof. reflexivity. Qed.

Lemma amf_harness_fp_one : forall f, amf_harness_fp [(f, AMF_BLOCK)] = [YI16.sink_token; (f, f + AMF_BLOCK)].
Proof. reflexivity. Qed.

Lemma amf_harness_fp_sink_open : forall T, YI16.sink_open_fp (amf_harness_fp T).
Proof. intros T. apply YI16.sink_open_token. left. reflexivity. Qed.

Lemma amf_harness_fp_in : forall T f n a, In (f, n) T -> f <= a < f + n -> inFP (amf_harness_fp T) a.
Proof.
  intros T f n a Hin Ha. exists (f, f + n). split; [|cbn [fst snd]; lia].
  right. apply in_map_iff. exists (f, n). split; [reflexivity | exact Hin].
Qed.

Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(** Every byte of a kept block that is still live at the write is granted by the journal's FP clause. *)
Lemma amf_harness_fp_grants : forall STK sp0 T bl0 blc ly own f a,
  In (f, AMF_BLOCK) T -> In (f, AMF_BLOCK) blc -> f <= a < f + AMF_BLOCK ->
  awr_byte STK sp0 (amf_harness_fp T) bl0 blc ly own a.
Proof.
  intros STK sp0 T bl0 blc ly own f a HT Hb Ha. right. left. split.
  - exact (amf_harness_fp_in T f AMF_BLOCK a HT Ha).
  - exists f, AMF_BLOCK. split; [exact Hb|]. replace (req_size AMF_BLOCK) with AMF_BLOCK by reflexivity. exact Ha.
Qed.

End h.

(** Which form a call's footprint has, from the GI at its start. *)
Lemma amf_harness_fp_of_gi : forall segs MS T m, amf_gi segs MS T m ->
  (amf_heads segs MS m 0 /\ amf_harness_fp T = [YI16.sink_token]) \/
  (exists f, amf_heads segs MS m f /\ amemfile_at segs MS m f /\
     amf_harness_fp T = [YI16.sink_token; (f, f + AMF_BLOCK)]).
Proof.
  intros segs MS T m [(H & ->) | (f & H & -> & Hf)].
  - left. split; [exact H | reflexivity].
  - right. exists f. split; [exact H|]. split; [exact Hf | reflexivity].
Qed.

(** The next call's footprint: the same once the FILE is open; on a call that started with nothing kept, either
    still [[sink_token]], or the FILE's range when the call keeps exactly the FILE block. *)
Lemma amf_harness_fp_next : forall segs MS T T' bl bl' m',
  amf_blocks_post T T' bl bl' -> amf_gi segs MS T' m' ->
  (T <> [] -> T' = T /\ amf_harness_fp T' = amf_harness_fp T) /\
  (T = [] -> (T' = [] /\ amf_harness_fp T' = [YI16.sink_token] /\ Permutation bl' bl) \/
     exists f, T' = [(f, AMF_BLOCK)] /\ amf_harness_fp T' = [YI16.sink_token; (f, f + AMF_BLOCK)] /\
       Permutation bl' ((f, AMF_BLOCK) :: bl)).
Proof.
  intros segs MS T T' bl bl' m' (D & -> & HP) HG. split.
  - intros HT. destruct T as [|t rest]; [exfalso; apply HT; reflexivity|].
    destruct (amf_gi_shape segs MS _ m' HG) as [E | (f & E)]; cbn [app] in E; [discriminate|].
    injection E as Et Erest.
    destruct rest as [|r rest]; [|discriminate]. destruct D as [|d D]; [|discriminate].
    split; reflexivity.
  - intros ->. cbn [app] in HG |- *.
    destruct (amf_gi_shape segs MS _ m' HG) as [-> | (f & ->)].
    + left. split; [reflexivity|]. split; [reflexivity|]. exact HP.
    + right. exists f. split; [reflexivity|]. split; [reflexivity | exact HP].
Qed.

(** ** Link's asan instance, each value read from link's asan image (pin 059dae63e07c)

    [link_amf_code] lists the instructions the values come from, as (address, instruction) pairs;
    [link_amf_code_ok] checks each against the asan image's bytes, and [link_amf_from_image] computes each value
    from those instructions:
    - [g_sink]: mark_quietly 0x883ec [auipc s2,0x5a8], 0x88414 [sd a0,-0x52c(s2)] (fmemopen's result);
    - [g_said]: 0x883fc [auipc a0,0x5a8], 0x88404 [addi a0,a0,-0x51c] (fmemopen's first argument);
    - size: 0x8840c [lui a1,1] (its second argument, 4096);
    - mode: 0x88400 [auipc a1,0xfff99], 0x88408 [addi a2,a1,-0x1a0] (its third argument, the string at 0x21260,
      whose bytes are "w\0", [link_amf_mode_bytes]); fmemopen +0x104 [lbu a0,0(s3)], +0x108 [sw a0,0x108(s0)]
      store its first byte in the cookie;
    - [g_say]: reac_served_say_to 0x89504 [auipc a1,0x5a8], 0x89508 [sd a0,-0x224(a1)];
    - read / write / seek / close: fmemopen 0x96b84-0x96b90 [auipc a0..a3,0], 0x96b98-0x96ba4 [addi], stored at
      0x96bb0 / 0x96bb4 / 0x96bb8 / 0x96bac;
    - [__libc.threaded]: fmemopen 0x96b94 [auipc a4,0x5bb], 0x96ba8 [lbu a4,0x30d(a4)];
    - [__libc.need_locks]: __lock 0x9b4d4 [auipc a1,0x5b7], 0x9b4d8 [lb a3,-0x631(a1)], 0x9b4dc [beqz a3] to the
      [ret] at 0x9b6cc;
    - [ofl_lock] and the list head: __ofl_lock 0x971a0 [auipc a0,0x5bb], 0x971a4 [addi s0,a0,0x160], 0x971b0
      [addi a0,s0,8]; the only read of [ofl_lock] (since __lock returns at once when need_locks is 0) is
      __unlock's 0x9b75c [lw a1,0(a0)], reached from __ofl_add +0x28 through __ofl_unlock 0x971c4
      [auipc a0,0x5bb], 0x971c8 [addi a0,a0,0x13c]; a negative value would take the futex wake;
    - mark_quietly reads [g_sink] twice: +0x1c (the test, +0x24 [bnez a1]) and +0x4c (rewind's argument).
    mark_quietly calls fmemopen through the trampoline 0x430a8 [j 0x48024] and the interceptor 0x48024, which
    jumps to the cell 0xa3780 (+0x24 / +0x28 / +0x4c); the image's .data holds 0x96a1c (fmemopen) there
    ([link_amf_real_fmemopen]). The FILE's malloc is fmemopen +0x98 [jal 0x540cc], [Tfib_code]'s
    [pc_wrap_malloc]. *)
Definition link_amf : amemfile_syms := {|
  amf_sink_addr := 0x62fec0; amf_say_addr := 0x6312e0; amf_buf := 0x62fee0; amf_size := 4096; amf_mode := 119;
  amf_read := 0x96bec; amf_write := 0x96cc0; amf_seek := 0x96dd4; amf_close := 0x96e70;
  amf_threaded := 0x651ea1; amf_need_locks := 0x651ea3; amf_ofl_lock := 0x652300 |}.

(** The open-file list head of link's asan image, as the A frame's [sink_head] (passed explicitly, as pcap's
    PcapEntry.v does). *)
Definition link_asink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x652308 |}.

Lemma link_amf_head_law : @amf_head_law link_asink_head link_amf.
Proof. reflexivity. Qed.

(** ** Reading link's asan image (the same reader as the plain MemFile.v, over the asan segments) *)
Inductive ishape : Type :=
| SAuipc (rd u : Z)
| SLui (rd u : Z)
| SAddi (rd rs1 imm : Z)
| SLd (nbytes : Z) (sg : bool) (rd rs1 off : Z)
| SSt (nbytes : Z) (rs1 rs2 off : Z)
| SBr (c : branch_cond) (rs1 rs2 target : Z)
| SJal (rd target : Z)
| SJalr (rd rs1 off : Z).

Definition shape_ok (pc : Z) (s : ishape) (i : instr) : bool :=
  match s, i with
  | SAuipc rd u, Auipc rd' u' => Z.eqb (bv_unsigned rd') rd && Z.eqb (bv_signed u') u
  | SLui rd u, Lui rd' u' => Z.eqb (bv_unsigned rd') rd && Z.eqb (bv_signed u') u
  | SAddi rd rs imm, OpImm ALU_ADD rd' rs' imm' =>
      Z.eqb (bv_unsigned rd') rd && Z.eqb (bv_unsigned rs') rs && Z.eqb (bv_signed imm') imm
  | SLd n sg rd rs off, Load sz sg' rd' rs' off' =>
      Z.eqb (msize_bytes sz) n && Bool.eqb sg sg' && Z.eqb (bv_unsigned rd') rd && Z.eqb (bv_unsigned rs') rs &&
      Z.eqb (bv_signed off') off
  | SSt n rs1 rs2 off, Store sz rs1' rs2' off' =>
      Z.eqb (msize_bytes sz) n && Z.eqb (bv_unsigned rs1') rs1 && Z.eqb (bv_unsigned rs2') rs2 &&
      Z.eqb (bv_signed off') off
  | SBr c rs1 rs2 t, Branch c' rs1' rs2' off' =>
      bool_decide (c = c') && Z.eqb (bv_unsigned rs1') rs1 && Z.eqb (bv_unsigned rs2') rs2 &&
      Z.eqb (pc + bv_signed off') t
  | SJal rd t, Jal rd' off' => Z.eqb (bv_unsigned rd') rd && Z.eqb (pc + bv_signed off') t
  | SJalr rd rs off, Jalr rd' rs' off' =>
      Z.eqb (bv_unsigned rd') rd && Z.eqb (bv_unsigned rs') rs && Z.eqb (bv_signed off') off
  | _, _ => false
  end.

Definition code_at (tbl : ctable) (pc : Z) : option instr :=
  match clookup tbl pc with
  | Some w =>
      if is_ecall (Z_to_bv 32 w) then None else
      match decode_any (Z_to_bv 32 w) with
      | Some (i, sz) => if Z.eqb sz 4 then Some i else None
      | None => None
      end
  | None => None
  end.

Definition code_list_ok (tbl : ctable) (l : list (Z * ishape)) : bool :=
  forallb (fun p => match code_at tbl (fst p) with Some i => shape_ok (fst p) (snd p) i | None => false end) l.

Lemma code_at_sound : forall segs tbl pc i, table_ok segs tbl -> code_at tbl pc = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
Proof.
  intros segs tbl pc i Ht H. unfold code_at in H.
  destruct (clookup tbl pc) as [w|] eqn:E; [|discriminate].
  destruct (is_ecall (Z_to_bv 32 w)) eqn:Ee; [discriminate|].
  destruct (decode_any (Z_to_bv 32 w)) as [[i' sz]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec sz 4) as [->|]; [|discriminate]. injection H as <-.
  exists (Z_to_bv 32 w). split; [exact (Ht pc w E)|]. split; [exact Ee | exact D].
Qed.

Lemma code_list_sound : forall tbl l, code_list_ok tbl l = true ->
  forall pc s, In (pc, s) l -> exists i, code_at tbl pc = Some i /\ shape_ok pc s i = true.
Proof.
  intros tbl l H pc s Hin. unfold code_list_ok in H. rewrite forallb_forall in H.
  specialize (H (pc, s) Hin). cbn [fst snd] in H.
  destruct (code_at tbl pc) as [i|]; [exists i; split; [reflexivity | exact H] | discriminate].
Qed.

(** The asan image's words at the functions this file reads: mark_quietly (0x883d4, 31 words), reac_served_say_to
    (0x89504, 3), the fmemopen trampoline (0x430a8, 1) and interceptor (0x48024, 20), fmemopen (0x96a1c, 116),
    __ofl_lock and __ofl_unlock (0x97194, 15), __ofl_add (0x971d0, 16), __stdio_exit (0x96878, 105), __lock and
    the head of __unlock (0x9b4d4, 165), mwrite (0x96cc0, 69) and ___errno_location (0x90a7c, 3); every one a
    4-byte word in the image. *)
Definition amf_tbl : ctable := Eval vm_compute in
  build_table tfibsegs 0x883d4 31 (build_table tfibsegs 0x89504 3 (build_table tfibsegs 0x430a8 1
  (build_table tfibsegs 0x48024 20 (build_table tfibsegs 0x96a1c 116 (build_table tfibsegs 0x97194 15
  (build_table tfibsegs 0x971d0 16 (build_table tfibsegs 0x96878 105 (build_table tfibsegs 0x9b4d4 165
  (build_table tfibsegs 0x96cc0 69 (build_table tfibsegs 0x90a7c 3 TEmpty)))))))))).

Lemma amf_tbl_eq : amf_tbl =
  build_table tfibsegs 0x883d4 31 (build_table tfibsegs 0x89504 3 (build_table tfibsegs 0x430a8 1
  (build_table tfibsegs 0x48024 20 (build_table tfibsegs 0x96a1c 116 (build_table tfibsegs 0x97194 15
  (build_table tfibsegs 0x971d0 16 (build_table tfibsegs 0x96878 105 (build_table tfibsegs 0x9b4d4 165
  (build_table tfibsegs 0x96cc0 69 (build_table tfibsegs 0x90a7c 3 TEmpty)))))))))).
Proof. vm_cast_no_check (eq_refl amf_tbl). Qed.

Lemma amf_tbl_ok : table_ok tfibsegs amf_tbl.
Proof.
  rewrite amf_tbl_eq. do 10 (apply build_table_ok; [lia|]). apply build_table_ok0. lia.
Qed.

(** The instructions [link_amf] and the layout are read from (asan image). *)
Definition link_amf_code : list (Z * ishape) := [
  (0x883ec, SAuipc 18 0x5a8);  (* mark_quietly +0x18 auipc s2,0x5a8 *)
  (0x883f0, SLd 8 true 11 18 (-0x52c));  (* +0x1c ld a1,-0x52c(s2): if (!g_sink) *)
  (0x883f8, SBr BC_NE 11 0 0x88420);  (* +0x24 bnez a1 -> +0x4c *)
  (0x883fc, SAuipc 10 0x5a8);  (* +0x28 auipc a0,0x5a8 *)
  (0x88400, SAuipc 11 (-0x67));  (* +0x2c auipc a1,0xfff99 *)
  (0x88404, SAddi 10 10 (-0x51c));  (* +0x30 addi a0,a0,-0x51c: g_said *)
  (0x88408, SAddi 12 11 (-0x1a0));  (* +0x34 addi a2,a1,-0x1a0: "w" *)
  (0x8840c, SLui 11 1);  (* +0x38 lui a1,1: 4096 *)
  (0x88410, SJal 1 0x430a8);  (* +0x3c jal fmemopen's trampoline *)
  (0x88414, SSt 8 18 10 (-0x52c));  (* +0x40 sd a0,-0x52c(s2): g_sink = ... *)
  (0x88418, SBr BC_EQ 10 0 0x88448);  (* +0x44 beqz a0 -> abort *)
  (0x8841c, SJal 1 0x89504);  (* +0x48 jal reac_served_say_to *)
  (0x88420, SLd 8 true 10 18 (-0x52c));  (* +0x4c ld a0,-0x52c(s2): g_sink, rewind's argument *)
  (0x88424, SJal 1 0x430d4);  (* +0x50 jal rewind's trampoline *)
  (0x88448, SJal 1 0x5b318);  (* +0x74 jal __asan_handle_no_return *)
  (0x8844c, SJal 1 0x90ac4);  (* +0x78 jal abort *)
  (0x89504, SAuipc 11 0x5a8);  (* reac_served_say_to auipc a1,0x5a8 *)
  (0x89508, SSt 8 11 10 (-0x224));  (* sd a0,-0x224(a1): g_say = out *)
  (0x430a8, SJal 0 0x48024);  (* __interceptor_trampoline_fmemopen j __interceptor_fmemopen *)
  (0x48044, SJal 1 0x5b214);  (* __interceptor_fmemopen +0x20 jal TryAsanInitFromRtl *)
  (0x48048, SAuipc 10 0x5b);  (* +0x24 auipc a0,0x5b *)
  (0x4804c, SLd 8 true 6 10 0x738);  (* +0x28 ld t1,0x738(a0): REAL(fmemopen), the cell 0xa3780 *)
  (0x48070, SJalr 0 6 0);  (* +0x4c jr t1 *)
  (0x96ab0, SAddi 10 0 0x518);  (* fmemopen +0x94 addi a0,zero,0x518 *)
  (0x96ab4, SJal 1 0x540cc);  (* +0x98 jal malloc (the interceptor's trampoline) *)
  (0x96ab8, SBr BC_NE 10 0 0x96acc);  (* +0x9c bnez a0 *)
  (0x96ad0, SAddi 12 0 0x110);  (* +0xb4 addi a2,zero,0x110 *)
  (0x96ad4, SAddi 11 0 0);  (* +0xb8 mv a1,zero *)
  (0x96ad8, SJal 1 0x52d70);  (* +0xbc jal memset (the interceptor's trampoline) *)
  (0x96adc, SAddi 10 8 0xe8);  (* +0xc0 addi a0,s0,0xe8 *)
  (0x96ae0, SAddi 11 0 (-1));  (* +0xc4 addi a1,zero,-1 *)
  (0x96ae4, SAddi 12 8 0x118);  (* +0xc8 addi a2,s0,0x118 *)
  (0x96ae8, SSt 8 8 10 0x98);  (* +0xcc sd a0,0x98(s0): cookie *)
  (0x96aec, SAddi 10 0 0x400);  (* +0xd0 addi a0,zero,0x400 *)
  (0x96af0, SSt 8 8 12 0x58);  (* +0xd4 sd a2,0x58(s0): buf *)
  (0x96af4, SSt 8 8 10 0x60);  (* +0xd8 sd a0,0x60(s0): buf_size *)
  (0x96af8, SSt 4 8 11 0x78);  (* +0xdc sw a1,0x78(s0): fd *)
  (0x96afc, SSt 4 8 11 0x90);  (* +0xe0 sw a1,0x90(s0): lbf *)
  (0x96b18, SSt 8 8 18 0xf8);  (* +0xfc sd s2,0xf8(s0): c.size *)
  (0x96b1c, SSt 8 8 9 0x100);  (* +0x100 sd s1,0x100(s0): c.buf *)
  (0x96b20, SLd 1 false 10 19 0);  (* +0x104 lbu a0,0(s3) *)
  (0x96b24, SSt 4 8 10 0x108);  (* +0x108 sw a0,0x108(s0): c.mode *)
  (0x96b38, SAddi 10 0 4);  (* +0x11c addi a0,zero,4 *)
  (0x96b44, SSt 4 8 10 0);  (* +0x128 sw a0,0(s0): flags *)
  (0x96b84, SAuipc 10 0);  (* +0x168 auipc a0,0 *)
  (0x96b88, SAuipc 11 0);  (* +0x16c auipc a1,0 *)
  (0x96b8c, SAuipc 12 0);  (* +0x170 auipc a2,0 *)
  (0x96b90, SAuipc 13 0);  (* +0x174 auipc a3,0 *)
  (0x96b94, SAuipc 14 0x5bb);  (* +0x178 auipc a4,0x5bb *)
  (0x96b98, SAddi 10 10 0x68);  (* +0x17c addi a0,a0,0x68: mread *)
  (0x96b9c, SAddi 11 11 0x138);  (* +0x180 addi a1,a1,0x138: mwrite *)
  (0x96ba0, SAddi 12 12 0x248);  (* +0x184 addi a2,a2,0x248: mseek *)
  (0x96ba4, SAddi 13 13 0x2e0);  (* +0x188 addi a3,a3,0x2e0: mclose *)
  (0x96ba8, SLd 1 false 14 14 0x30d);  (* +0x18c lbu a4,0x30d(a4): __libc.threaded *)
  (0x96bac, SSt 8 8 13 0x18);  (* +0x190 sd a3,0x18(s0): close *)
  (0x96bb0, SSt 8 8 10 0x40);  (* +0x194 sd a0,0x40(s0): read *)
  (0x96bb4, SSt 8 8 11 0x48);  (* +0x198 sd a1,0x48(s0): write *)
  (0x96bb8, SSt 8 8 12 0x50);  (* +0x19c sd a2,0x50(s0): seek *)
  (0x96bbc, SBr BC_NE 14 0 0x96bc8);  (* +0x1a0 bnez a4 *)
  (0x96bc0, SAddi 10 0 (-1));  (* +0x1a4 addi a0,zero,-1 *)
  (0x96bc4, SSt 4 8 10 0x8c);  (* +0x1a8 sw a0,0x8c(s0): lock *)
  (0x96be8, SJal 0 0x971d0);  (* +0x1cc j __ofl_add *)
  (0x971a0, SAuipc 10 0x5bb);  (* __ofl_lock +0xc auipc a0,0x5bb *)
  (0x971a4, SAddi 8 10 0x160);  (* +0x10 addi s0,a0,0x160: &ofl_lock *)
  (0x971ac, SJal 1 0x9b4d4);  (* +0x18 jal __lock *)
  (0x971b0, SAddi 10 8 8);  (* +0x1c addi a0,s0,8: &ofl_head *)
  (0x9b4d4, SAuipc 11 0x5b7);  (* __lock +0x0 auipc a1,0x5b7 *)
  (0x9b4d8, SLd 1 true 13 11 (-0x631));  (* +0x4 lb a3,-0x631(a1): __libc.need_locks *)
  (0x9b4dc, SBr BC_EQ 13 0 0x9b6cc);  (* +0x8 beqz a3 -> ret *)
  (0x9b6cc, SJalr 0 1 0);  (* +0x1f8 ret *)
  (0x971e0, SJal 1 0x97194);  (* __ofl_add +0x10 jal __ofl_lock *)
  (0x971e4, SLd 8 true 11 10 0);  (* +0x14 ld a1,0(a0) *)
  (0x971e8, SSt 8 8 11 0x70);  (* +0x18 sd a1,0x70(s0): next = head *)
  (0x971ec, SBr BC_EQ 11 0 0x971f4);  (* +0x1c beqz a1: old head 0, +0x20 sd prev skipped *)
  (0x971f4, SSt 8 10 8 0);  (* +0x24 sd s0,0(a0): head = f *)
  (0x971f8, SJal 1 0x971c4);  (* +0x28 jal __ofl_unlock *)
  (0x971c4, SAuipc 10 0x5bb);  (* __ofl_unlock +0x0 auipc a0,0x5bb *)
  (0x971c8, SAddi 10 10 0x13c);  (* +0x4 addi a0,a0,0x13c: &ofl_lock *)
  (0x971cc, SJal 0 0x9b75c);  (* +0x8 j __unlock *)
  (0x9b75c, SLd 4 true 11 10 0);  (* __unlock +0x0 lw a1,0(a0): ofl_lock *)
  (0x9b760, SBr BC_LT 11 0 0x9b768);  (* +0x4 bltz a1 -> the futex wake *)
  (0x9b764, SJalr 0 1 0);  (* +0x8 ret *)
  (0x96884, SJal 1 0x97194);  (* __stdio_exit +0xc jal __ofl_lock *)
  (0x96888, SLd 8 true 8 10 0);  (* +0x10 ld s0,0(a0) *)
  (0x9688c, SBr BC_NE 8 0 0x969b8);  (* +0x14 bnez s0 -> loop *)
  (0x969b0, SLd 8 true 8 8 0x70);  (* loop +0x0 ld s0,0x70(s0) *)
  (0x969b4, SBr BC_EQ 8 0 0x96890);  (* loop +0x4 beqz s0 -> the stdin / stdout / stderr part *)
  (0x969b8, SLd 4 true 10 8 0x8c);  (* loop +0x8 lw a0,0x8c(s0) *)
  (0x969bc, SBr BC_LT 10 0 0x969c8);  (* loop +0xc bltz a0 *)
  (0x969c0, SAddi 10 8 0);  (* loop +0x10 mv a0,s0 *)
  (0x969c4, SJal 1 0x9648c);  (* loop +0x14 jal __lockfile (taken only when lock >= 0) *)
  (0x969c8, SLd 8 true 10 8 0x28);  (* loop +0x18 ld a0,0x28(s0) *)
  (0x969cc, SLd 8 true 11 8 0x38);  (* loop +0x1c ld a1,0x38(s0) *)
  (0x969d0, SBr BC_EQ 10 11 0x969e8);  (* loop +0x20 beq a0,a1 *)
  (0x969d4, SLd 8 true 13 8 0x48);  (* loop +0x24 ld a3,0x48(s0) *)
  (0x969d8, SAddi 10 8 0);  (* loop +0x28 mv a0,s0 *)
  (0x969dc, SAddi 11 0 0);  (* loop +0x2c mv a1,zero *)
  (0x969e0, SAddi 12 0 0);  (* loop +0x30 mv a2,zero *)
  (0x969e4, SJalr 1 13 0);  (* loop +0x34 jalr a3: f->write *)
  (0x969e8, SLd 8 true 10 8 8);  (* loop +0x38 ld a0,8(s0) *)
  (0x969ec, SLd 8 true 11 8 0x10);  (* loop +0x3c ld a1,0x10(s0) *)
  (0x969f0, SBr BC_EQ 10 11 0x969b0);  (* loop +0x40 beq a0,a1 *)
  (0x969f4, SLd 8 true 13 8 0x50);  (* loop +0x44 ld a3,0x50(s0) *)
  (0x969fc, SAddi 12 0 1);  (* loop +0x4c addi a2,zero,1 *)
  (0x96a00, SAddi 10 8 0);  (* loop +0x50 mv a0,s0 *)
  (0x96a04, SJalr 1 13 0);  (* loop +0x54 jalr a3: f->seek *)
  (0x96a08, SJal 0 0x969b0)  (* loop +0x58 j loop *)
].

Lemma link_amf_code_ok : code_list_ok amf_tbl link_amf_code = true.
Proof. vm_compute. reflexivity. Qed.

(** The mode string fmemopen gets is "w" (its two bytes in the image). *)
Lemma link_amf_mode_bytes :
  option_map bv_unsigned (seg_rom tfibsegs (Z_to_bv 64 (0x88400 + (-0x67) * 4096 - 0x1a0))) = Some 119 /\
  option_map bv_unsigned (seg_rom tfibsegs (Z_to_bv 64 (0x88400 + (-0x67) * 4096 - 0x1a0 + 1))) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

(** The cell the fmemopen interceptor jumps through holds fmemopen (0x96a1c) in the image's .data. *)
Lemma link_amf_real_fmemopen : forall k, (k < 8)%nat ->
  option_map bv_unsigned (seg_rom tfibsegs (Z_to_bv 64 (0x48048 + 0x5b * 4096 + 0x738 + Z.of_nat k))) =
  Some (YO0f.le_byte 0x96a1c 8 k).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

(** Each value from the immediates in [link_amf_code] (auipc + addi / ld / sd / lbu / lb: [pc + u * 4096 + imm]). *)
Lemma link_amf_from_image :
  amf_sink_addr link_amf = 0x883ec + 0x5a8 * 4096 - 0x52c /\
  amf_say_addr link_amf = 0x89504 + 0x5a8 * 4096 - 0x224 /\
  amf_buf link_amf = 0x883fc + 0x5a8 * 4096 - 0x51c /\
  amf_size link_amf = 1 * 4096 /\
  amf_mode link_amf = 119 /\
  amf_read link_amf = 0x96b84 + 0 * 4096 + 0x68 /\
  amf_write link_amf = 0x96b88 + 0 * 4096 + 0x138 /\
  amf_seek link_amf = 0x96b8c + 0 * 4096 + 0x248 /\
  amf_close link_amf = 0x96b90 + 0 * 4096 + 0x2e0 /\
  amf_threaded link_amf = 0x96b94 + 0x5bb * 4096 + 0x30d /\
  amf_need_locks link_amf = 0x9b4d4 + 0x5b7 * 4096 - 0x631 /\
  amf_ofl_lock link_amf = 0x971a0 + 0x5bb * 4096 + 0x160 /\
  amf_ofl_lock link_amf = 0x971c4 + 0x5bb * 4096 + 0x13c /\
  amf_ofl_head link_amf = 0x971a0 + 0x5bb * 4096 + 0x160 + 8.
Proof. repeat split; reflexivity. Qed.

(** The layout constants from the same instructions: the malloc size, the memset length, the cookie and buffer
    offsets, the buffer size, F_NORD; and the malloc / memset the FILE's set-up calls are [Tfib_code]'s
    interceptor entries. *)
Lemma link_alayout_from_image :
  AMF_BLOCK = 0x518 /\ AMF_ZEROED = 0x110 /\ AMF_COOKIE = 0xe8 /\ AMF_BUF = 0x118 /\ AMF_BUFSIZ = 0x400 /\
  AF_NORD = 4 /\ pc_wrap_malloc Tfib_code = 0x540cc /\ pc_wrap_memset Tfib_code = 0x52d70.
Proof. repeat split; reflexivity. Qed.
