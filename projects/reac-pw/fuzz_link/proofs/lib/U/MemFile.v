(** * reac-pw/fuzz_link (UBSan): the harness's one memory FILE.

    [mark_quietly] (projects/reac-pw/fuzz_link/source/fuzz_link.c:150-164) opens
    [g_sink = fmemopen(g_said, 4096, "w")] once, gives it to the library ([reac_served_say_to],
    reac_served_mark.c:16-19, which stores it in [g_say]) and never closes it. musl's fmemopen tail-calls
    [__ofl_add], so from the first mark on the open-file list is [g_sink] alone, and at exit
    [__stdio_exit] runs [close_file] on it.

    This file states that FILE for the frame, outside the released Reusable files (YI14 / YI5c / YL03 keep
    [sk_file := None]: that field is the fopen-backed sink, which link does not have):
    - [memfile_syms] / [link_mf]: the FILE's fixed parts (the address of [g_sink], of [g_say], the cookie's
      buffer [g_said], size 4096, mode 'w', the four m* function pointers), each value read from link's
      UBSan image ([link_mf_from_image]);
    - [memfile_at]: the FILE block at [f] (the address [g_sink] holds; its cookie is at [f + MF_COOKIE]);
    - [mf_gi]: the conjunct the slot's global invariant carries across driver calls;
    - [mf_sink]: the post's open-file clause, the same disjunction; [sink_none] is its [g_sink = 0] arm;
    - the block's accounting ([mf_TD_open], [mf_TD_keep]) and room ([mf_room_slots], [mf_room_cf]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YK11 YK0s YK15 YM06 YP09 YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YI06 YI16 YI00 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YH00 YH03 YH02 YI5b YI5c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import YM05 YL0g YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** ** Layout of musl's [struct mem_FILE], read from link's fmemopen

    The FILE (232 bytes), then the cookie [struct cookie { size_t pos, len, size; unsigned char *buf; int mode; }]
    at +232, then [unsigned char buf[UNGET + BUFSIZ]] at +272; one malloc block. Offsets below are from the
    start of fmemopen (plain 0x192a0, ubsan 0x19ad4; the code is the same in both builds). *)
Definition MF_BLOCK : Z := 1304.   (* +0x94 addi a0,zero,0x518; +0x98 jal malloc *)
Definition MF_ZEROED : Z := 272.   (* +0xb4 addi a2,zero,0x110; +0xbc jal memset (f, 0, 272) *)
Definition MF_COOKIE : Z := 232.   (* +0xc0 addi a0,s0,0xe8; +0xcc sd a0,0x98(s0): f->cookie *)
Definition MF_BUF : Z := 280.      (* +0xc8 addi a2,s0,0x118; +0xd4 sd a2,0x58(s0): f->buf (UNGET = 8) *)
Definition MF_BUFSIZ : Z := 1024.  (* +0xd0 addi a0,zero,0x400; +0xd8 sd a0,0x60(s0): f->buf_size *)
Definition F_NORD : Z := 4.        (* +0x11c addi a0,zero,4; +0x128 sw a0,0(s0): mode "w" without '+' *)
Definition F_ERR : Z := 32.        (* mwrite +0x94 ori a0,a0,0x20: a write past the cookie's size *)

(** The FILE's fixed parts. The FILE's own address is not fixed (malloc returns it): it is the [f] of
    [memfile_at], the value [g_sink] holds, and its cookie is [f + MF_COOKIE]. *)
Record memfile_syms : Type := MkMemFileSyms {
  mf_sink_addr : Z;  (* &g_sink (fuzz_link.c:151) *)
  mf_say_addr : Z;   (* &g_say (reac_served_mark.c:14) *)
  mf_buf : Z;        (* &g_said: the cookie's buf (fuzz_link.c:150, 156) *)
  mf_size : Z;       (* sizeof g_said: the cookie's size *)
  mf_mode : Z;       (* the first byte of the mode string "w": the cookie's mode *)
  mf_read : Z;       (* mread: f->read *)
  mf_write : Z;      (* mwrite: f->write *)
  mf_seek : Z;       (* mseek: f->seek *)
  mf_close : Z       (* mclose: f->close *)
}.

Section c.
Variable B : malloc_syms.
Context {SH : sink_head} {SK : sink_syms}.
Variable MS : memfile_syms.
Local Notation segs := (ms_segs B).
Local Notation fld mem f off n v := (val_mem segs mem (f + off) n v).

(** What fmemopen writes and no later code changes: the FILE fields it sets (memset leaves the others 0),
    the cookie's [size], [buf] and [mode], and [prev] / [next] (the list holds this FILE alone). *)
Definition memfile_static (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 24 8 (mf_close MS) /\ fld mem f 48 8 0 /\
  fld mem f 64 8 (mf_read MS) /\ fld mem f 72 8 (mf_write MS) /\ fld mem f 80 8 (mf_seek MS) /\
  fld mem f 88 8 (f + MF_BUF) /\ fld mem f 96 8 MF_BUFSIZ /\
  fld mem f 104 8 0 /\ fld mem f 112 8 0 /\
  fld mem f 120 4 U32M1 /\ fld mem f 124 4 0 /\ fld mem f 128 8 0 /\
  fld mem f 140 4 U32M1 /\ fld mem f 144 4 U32M1 /\
  fld mem f 152 8 (f + MF_COOKIE) /\
  fld mem f 160 8 0 /\ fld mem f 168 8 0 /\ fld mem f 176 8 0 /\ fld mem f 184 8 0 /\
  fld mem f 192 8 0 /\ fld mem f 200 8 0 /\ fld mem f 208 8 0 /\ fld mem f 216 8 0 /\ fld mem f 224 8 0 /\
  fld mem f (MF_COOKIE + 16) 8 (mf_size MS) /\ fld mem f (MF_COOKIE + 24) 8 (mf_buf MS) /\
  fld mem f (MF_COOKIE + 32) 4 (mf_mode MS).

(** [flags]: F_NORD, with F_ERR after a write past the cookie's size (mwrite) until the next rewind clears it;
    nothing sets F_EOF (no read); vfprintf clears F_ERR on entry and ORs the entry value back on exit, so an
    F_ERR that mwrite sets during the call stays set. *)
Definition memfile_flags (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 0 4 F_NORD \/ fld mem f 0 4 (F_NORD + F_ERR).

(** [mode] (the FILE's orientation, +136): 0 from fmemopen; __towrite makes it -1 at the first write. *)
Definition memfile_omode (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 136 4 0 \/ fld mem f 136 4 U32M1.

(** The buffer window. [rpos] / [rend] are 0 (fmemopen's memset; __towrite and __fseeko_unlocked write 0).
    [wend] / [wpos] / [wbase] are all 0 (after fmemopen, rewind, or mwrite's write past the end), or the
    buffer is active (__towrite): [wbase = buf], [wend = buf + 1024] and [wpos = buf + k], k bytes pending. *)
Definition memfile_window (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 8 8 0 /\ fld mem f 16 8 0 /\
  ((fld mem f 32 8 0 /\ fld mem f 40 8 0 /\ fld mem f 56 8 0) \/
   (exists k, 0 <= k <= MF_BUFSIZ /\
      fld mem f 32 8 (f + MF_BUF + MF_BUFSIZ) /\ fld mem f 40 8 (f + MF_BUF + k) /\ fld mem f 56 8 (f + MF_BUF))).

(** The cookie's [pos] and [len]: every mark rewinds (fuzz_link.c:162): __fseeko_unlocked flushes, then mseek
    sets [pos] to 0; when the flush passes the size, __fseeko_unlocked returns before mseek and [pos] stays at
    the size. mwrite moves [pos] and raises [len] to it, cutting at [size]. So [pos] is not invariant, only its
    range is. *)
Definition memfile_cookie (mem : word -> option byte) (f : Z) : Prop :=
  exists pos len, 0 <= pos <= len /\ len <= mf_size MS /\
    fld mem f MF_COOKIE 8 pos /\ fld mem f (MF_COOKIE + 8) 8 len.

Definition memfile_at (mem : word -> option byte) (f : Z) : Prop :=
  0 < f /\ f + MF_BLOCK <= 2 ^ 64 /\ f mod 16 = 0 /\
  memfile_static mem f /\ memfile_flags mem f /\ memfile_omode mem f /\ memfile_window mem f /\
  memfile_cookie mem f.

(** [g_sink], [g_say] and the open-file list head all hold [v]. *)
Definition mf_heads (mem : word -> option byte) (v : Z) : Prop :=
  word_mem segs mem (mf_sink_addr MS) v /\ word_mem segs mem (mf_say_addr MS) v /\
  word_mem segs mem sk_ofl_head v.

(** The GI conjunct, over the slot's kept blocks [T] (the frame's [GI j T mem]): before the first mark,
    [g_sink = 0] and the list is empty; from then on [g_sink = f], the list is [f] (head [f], [f->next = 0]),
    the library speaks to [f], [f] is the one kept block, and it is a memory FILE over [g_said]. *)
Definition mf_gi (T : list (Z * Z)) (mem : word -> option byte) : Prop :=
  (mf_heads mem 0 /\ T = []) \/
  (exists f, mf_heads mem f /\ T = [(f, MF_BLOCK)] /\ memfile_at mem f).

(** The post's open-file clause: [sink_none] with its [ofl_head = 0] replaced by the same disjunction. *)
Definition mf_sink (mem : word -> option byte) (md : Model) : Prop :=
  closed_stdio_env B mem /\ Namei.fd_names_path (m_fds md) sink_path = false /\
  (mf_heads mem 0 \/ exists f, mf_heads mem f /\ memfile_at mem f).

(** The bytes [mf_gi] reads outside the kept block. *)
Definition mf_head_addr (a : Z) : Prop :=
  (mf_sink_addr MS <= a < mf_sink_addr MS + 8) \/ (mf_say_addr MS <= a < mf_say_addr MS + 8) \/
  (sk_ofl_head <= a < sk_ofl_head + 8).

(** The buffer [g_said] the FILE writes into, and the globals the slot's [G] must hold for this text: the three
    heads and [g_said] (the post's image clause lets a call change an image byte only inside [G]). *)
Definition mf_said_addr (a : Z) : Prop := mf_buf MS <= a < mf_buf MS + mf_size MS.

Definition mf_globals : list (Z * Z) :=
  [(mf_sink_addr MS, 8); (mf_say_addr MS, 8); (mf_buf MS, mf_size MS); (sk_ofl_head, 8)].

Lemma mf_globals_cover : forall a, mf_head_addr a \/ mf_said_addr a -> in_globals mf_globals a.
Proof.
  intros a [[H | [H | H]] | H]; unfold in_globals, mf_globals.
  - exists (mf_sink_addr MS), 8. split; [left; reflexivity | exact H].
  - exists (mf_say_addr MS), 8. split; [right; left; reflexivity | exact H].
  - exists sk_ofl_head, 8. split; [right; right; right; left; reflexivity | exact H].
  - exists (mf_buf MS), (mf_size MS). split; [right; right; left; reflexivity | exact H].
Qed.

Lemma mf_heads_ofl : forall mem v, mf_heads mem v -> word_mem segs mem sk_ofl_head v.
Proof. intros mem v (_ & _ & H). exact H. Qed.

Lemma mf_sink_of_none : forall mem md,
  sink_none B mem md -> word_mem segs mem (mf_sink_addr MS) 0 -> word_mem segs mem (mf_say_addr MS) 0 ->
  mf_sink mem md.
Proof.
  intros mem md (Henv & Hh & Hn) Hs Hy. split; [exact Henv|]. split; [exact Hn|].
  left. split; [exact Hs|]. split; [exact Hy | exact Hh].
Qed.

Lemma mf_none_of_sink : forall mem md, mf_sink mem md -> mf_heads mem 0 -> sink_none B mem md.
Proof.
  intros mem md (Henv & Hn & _) H0. split; [exact Henv|]. split; [exact (mf_heads_ofl _ _ H0) | exact Hn].
Qed.

Lemma mf_sink_names : forall mem md, mf_sink mem md -> Namei.fd_names_path (m_fds md) sink_path = false.
Proof. intros mem md (_ & H & _). exact H. Qed.

Lemma mf_sink_env : forall mem md, mf_sink mem md -> closed_stdio_env B mem.
Proof. intros mem md (H & _). exact H. Qed.

Lemma mf_sink_of_gi : forall T mem md,
  mf_gi T mem -> closed_stdio_env B mem -> Namei.fd_names_path (m_fds md) sink_path = false -> mf_sink mem md.
Proof.
  intros T mem md HG Henv Hn. split; [exact Henv|]. split; [exact Hn|].
  destruct HG as [(H & _) | (f & H & _ & Hf)]; [left; exact H | right; exists f; split; assumption].
Qed.

Lemma mf_gi_of_sink : forall mem md, mf_sink mem md -> exists T, mf_gi T mem.
Proof.
  intros mem md (_ & _ & [H | (f & H & Hf)]).
  - exists []. left. split; [exact H | reflexivity].
  - exists [(f, MF_BLOCK)]. right. exists f. split; [exact H|]. split; [reflexivity | exact Hf].
Qed.

(** *** Frame: [memfile_at] reads only the first [MF_ZEROED] bytes of its block; [mf_gi] adds the three heads. *)
Lemma memfile_at_frame : forall (mem mem' : word -> option byte) f,
  (forall x, f <= x < f + MF_ZEROED -> mbyte segs mem' x = mbyte segs mem x) ->
  memfile_at mem f -> memfile_at mem' f.
Proof.
  intros mem mem' f Hfr (Hf0 & Hf1 & Hf2 & Hs & Hfl & Hom & Hw & Hc).
  assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= MF_ZEROED ->
    val_mem segs mem (f + off) n v -> val_mem segs mem' (f + off) n v).
  { intros off n v H0 H1 Hv. eapply val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
  unfold MF_ZEROED, MF_COOKIE in *.
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold memfile_static in *. unfold MF_COOKIE in *.
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
    unfold MF_COOKIE. split; (apply HV; [lia | cbn; lia | assumption]).
Qed.

Lemma mf_heads_frame : forall (mem mem' : word -> option byte) v,
  (forall a, mf_head_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
  mf_heads mem v -> mf_heads mem' v.
Proof.
  intros mem mem' v Hfr (H1 & H2 & H3). unfold mf_heads.
  repeat split; apply (val_mem_word_mem segs);
    [apply (val_mem_word_mem segs) in H1 | apply (val_mem_word_mem segs) in H2 | apply (val_mem_word_mem segs) in H3];
    (eapply val_mem_frame; [|eassumption]); intros x Hx; apply Hfr; unfold mf_head_addr; cbn in Hx; lia.
Qed.

Lemma in_tb_one : forall f k x, f <= x < f + k -> in_tb [(f, k)] x.
Proof. intros f k x Hx. exists f, k. split; [left; reflexivity | exact Hx]. Qed.

(** [mf_gi] is local to the globals holding the three heads and to the kept block: the frame's
    [G_local_T] for the slot's GI, so the driver carries it between calls. *)
Lemma mf_gi_local : forall G, (forall a, mf_head_addr a -> in_globals G a) ->
  G_local_T segs G (fun _ T m => mf_gi T m).
Proof.
  intros G HG j T m m' Hfr H.
  assert (Hh : forall v, mf_heads m v -> mf_heads m' v).
  { intros v Hv. apply (mf_heads_frame m m' v); [|exact Hv]. intros a Ha. apply Hfr. left. exact (HG a Ha). }
  destruct H as [(H0 & HT) | (f & Hf & HT & Hm)].
  - left. split; [exact (Hh 0 H0) | exact HT].
  - right. exists f. split; [exact (Hh f Hf)|]. split; [exact HT|].
    apply (memfile_at_frame m m' f); [|exact Hm].
    intros x Hx. apply Hfr. right. subst T. apply in_tb_one. unfold MF_ZEROED, MF_BLOCK in *. lia.
Qed.

(** [mf_sink] is kept by a step that leaves the stdio words, the heads and the FILE's bytes as they were and
    the descriptor table as it was. *)
Lemma mf_sink_frame : forall (mem mem' : word -> option byte) md md',
  (forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall a, mf_head_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
  (forall f, mf_heads mem f -> memfile_at mem f -> forall x, f <= x < f + MF_ZEROED -> mbyte segs mem' x = mbyte segs mem x) ->
  m_fds md' = m_fds md -> mf_sink mem md -> mf_sink mem' md'.
Proof.
  intros mem mem' md md' Henv Hh Hb Hfd (He & Hn & H). split; [exact (closed_stdio_env_frame B mem mem' Henv He)|].
  split; [rewrite Hfd; exact Hn|].
  destruct H as [H0 | (f & Hf & Hm)].
  - left. exact (mf_heads_frame mem mem' 0 Hh H0).
  - right. exists f. split; [exact (mf_heads_frame mem mem' f Hh Hf)|].
    exact (memfile_at_frame mem mem' f (Hb f Hf Hm) Hm).
Qed.

(** *** What close_file reads on this FILE ([__stdio_exit]'s list loop, ubsan 0x1a310-0x1a368): [lock] = -1
    (no __lockfile), [write] = mwrite (called only when [wpos <> wbase]), [rpos] = [rend] (no seek),
    [next] = 0 (the loop ends). *)
Lemma memfile_close_reads : forall mem f, memfile_at mem f ->
  fld mem f 140 4 U32M1 /\ fld mem f 72 8 (mf_write MS) /\ fld mem f 8 8 0 /\ fld mem f 16 8 0 /\
  fld mem f 112 8 0.
Proof.
  intros mem f (_ & _ & _ & Hs & _ & _ & (H8 & H16 & _) & _). unfold memfile_static in Hs.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; assumption.
Qed.

(** ** The states the run reaches, as stores

    [mf_upd mem a n v] is [mem] after an [n]-byte little-endian store of [v] at [a]. [mf_fm mem f] is [mem]
    after fmemopen's memset and stores (offsets from fmemopen; [link_mf_code] checks each instruction) and
    __ofl_add's [f->next = *head]; [mf_dynw] then sets the FILE words a call writes later (flags, orientation,
    window, cookie pos / len: rewind / __fseeko_unlocked / mseek, __towrite, __fwritex, vfprintf and mwrite
    write no other word of the first [MF_ZEROED] bytes, except [rpos] / [rend], which __towrite and
    __fseeko_unlocked store as 0, fmemopen's value); [mf_heads_set] stores [f] in the list head
    (__ofl_add), [g_sink] (mark_quietly) and [g_say] (reac_served_say_to). Stores to disjoint words commute,
    so [mf_state] is the memory at any return after the first mark, with the values that call left, and
    [mf_open] (flags F_NORD, the rest 0) the memory just after the first mark's fmemopen and say_to. *)
Definition mf_upd (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : word -> option byte :=
  fun w => if (a <=? bv_unsigned w) && (bv_unsigned w <? a + Z.of_nat n)
           then Some (Z_to_bv 8 (le_byte v n (Z.to_nat (bv_unsigned w - a)))) else mem w.

Definition mf_fm (mem : word -> option byte) (f : Z) : word -> option byte :=
  mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd
  (mf_upd (mf_upd (mf_upd
    mem f 272 0)                            (* +0xbc memset (f, 0, 272) *)
    (f + 152) 8 (f + MF_COOKIE))            (* +0xcc sd a0,0x98(s0) *)
    (f + 88) 8 (f + MF_BUF))                (* +0xd4 sd a2,0x58(s0) *)
    (f + 96) 8 MF_BUFSIZ)                   (* +0xd8 sd a0,0x60(s0) *)
    (f + 120) 4 U32M1)                      (* +0xdc sw a1,0x78(s0): fd = -1 *)
    (f + 144) 4 U32M1)                      (* +0xe0 sw a1,0x90(s0): lbf = EOF *)
    (f + (MF_COOKIE + 16)) 8 (mf_size MS))  (* +0xfc sd s2,0xf8(s0) *)
    (f + (MF_COOKIE + 24)) 8 (mf_buf MS))   (* +0x100 sd s1,0x100(s0) *)
    (f + (MF_COOKIE + 32)) 4 (mf_mode MS))  (* +0x108 sw a0,0x108(s0) *)
    (f + 0) 4 F_NORD)                       (* +0x128 sw a0,0(s0) *)
    (f + 24) 8 (mf_close MS))               (* +0x190 sd a3,0x18(s0) *)
    (f + 64) 8 (mf_read MS))                (* +0x194 sd a0,0x40(s0) *)
    (f + 72) 8 (mf_write MS))               (* +0x198 sd a1,0x48(s0) *)
    (f + 80) 8 (mf_seek MS))                (* +0x19c sd a2,0x50(s0) *)
    (f + 140) 4 U32M1)                      (* +0x1a8 sw a0,0x8c(s0): lock = -1 (__libc.threaded = 0) *)
    (f + 112) 8 0.                          (* __ofl_add +0x18 sd a1,0x70(s0): next = old head = 0 *)

Definition mf_dynw (m : word -> option byte) (f fl om wend wpos wbase pos len : Z) : word -> option byte :=
  mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd (mf_upd m
    (f + 0) 4 fl) (f + 136) 4 om) (f + 32) 8 wend) (f + 40) 8 wpos) (f + 56) 8 wbase)
    (f + MF_COOKIE) 8 pos) (f + (MF_COOKIE + 8)) 8 len.

Definition mf_heads_set (m : word -> option byte) (f : Z) : word -> option byte :=
  mf_upd (mf_upd (mf_upd m sk_ofl_head 8 f) (mf_sink_addr MS) 8 f) (mf_say_addr MS) 8 f.

Definition mf_state (mem : word -> option byte) (f fl om wend wpos wbase pos len : Z) : word -> option byte :=
  mf_heads_set (mf_dynw (mf_fm mem f) f fl om wend wpos wbase pos len) f.

Definition mf_open (mem : word -> option byte) (f : Z) : word -> option byte :=
  mf_state mem f F_NORD 0 0 0 0 0 0.

Lemma mf_unsigned64 : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hx.
Qed.

Lemma mf_upd_in : forall mem a n v x, 0 <= x < 2 ^ 64 -> a <= x < a + Z.of_nat n ->
  mbyte segs (mf_upd mem a n v) x = Some (Z_to_bv 8 (le_byte v n (Z.to_nat (x - a)))).
Proof.
  intros mem a n v x Hx Ha. unfold mbyte, mf_upd. rewrite (mf_unsigned64 x Hx).
  replace ((a <=? x) && (x <? a + Z.of_nat n)) with true; [reflexivity|].
  symmetry. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma mf_upd_out : forall mem a n v x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + Z.of_nat n) ->
  mbyte segs (mf_upd mem a n v) x = mbyte segs mem x.
Proof.
  intros mem a n v x Hx Ha. unfold mbyte, mf_upd. rewrite (mf_unsigned64 x Hx).
  replace ((a <=? x) && (x <? a + Z.of_nat n)) with false; [reflexivity|].
  symmetry. apply andb_false_iff.
  destruct (Z.leb_spec a x) as [H|H]; [right; apply Z.ltb_ge; lia | left; reflexivity].
Qed.

Lemma le_byte_0 : forall n k, le_byte 0 n k = 0.
Proof. intros n k. unfold le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. reflexivity. Qed.

Lemma val_mem_upd_same : forall mem a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem segs (mf_upd mem a n v) a n v.
Proof.
  intros mem a n v H0 H1 k Hk. rewrite mf_upd_in by lia.
  replace (a + Z.of_nat k - a) with (Z.of_nat k) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma val_mem_upd_other : forall mem a n v b m w, 0 <= b -> b + Z.of_nat m <= 2 ^ 64 ->
  a + Z.of_nat n <= b \/ b + Z.of_nat m <= a ->
  val_mem segs mem b m w -> val_mem segs (mf_upd mem a n v) b m w.
Proof. intros mem a n v b m w H0 H1 H2 H k Hk. rewrite mf_upd_out by lia. exact (H k Hk). Qed.

Lemma val_mem_upd_zero : forall mem a n b m, 0 <= a -> a <= b -> b + Z.of_nat m <= a + Z.of_nat n ->
  a + Z.of_nat n <= 2 ^ 64 -> val_mem segs (mf_upd mem a n 0) b m 0.
Proof. intros mem a n b m H0 H1 H2 H3 k Hk. rewrite mf_upd_in by lia. rewrite !le_byte_0. reflexivity. Qed.

Ltac mf_ar := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold MF_COOKIE, MF_BUF, MF_BUFSIZ, MF_BLOCK in *; lia.

Ltac mf_fld :=
  repeat first
    [ apply val_mem_upd_same; mf_ar
    | apply val_mem_upd_zero; mf_ar
    | apply val_mem_upd_other; [mf_ar | mf_ar | mf_ar | ] ].

(** The stores of [mf_fm] and [mf_dynw] stay in the first [MF_ZEROED] bytes of the block. *)
Lemma mf_fm_out : forall mem f x, 0 <= x < 2 ^ 64 -> ~ (f <= x < f + MF_ZEROED) ->
  mbyte segs (mf_fm mem f) x = mbyte segs mem x.
Proof.
  intros mem f x Hx Hn. unfold mf_fm, MF_ZEROED, MF_COOKIE in *.
  repeat (rewrite mf_upd_out; [|exact Hx|cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). reflexivity.
Qed.

Lemma mf_dynw_out : forall m f fl om wend wpos wbase pos len x, 0 <= x < 2 ^ 64 -> ~ (f <= x < f + MF_ZEROED) ->
  mbyte segs (mf_dynw m f fl om wend wpos wbase pos len) x = mbyte segs m x.
Proof.
  intros m f fl om wend wpos wbase pos len x Hx Hn. unfold mf_dynw, MF_ZEROED, MF_COOKIE in *.
  repeat (rewrite mf_upd_out; [|exact Hx|cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]). reflexivity.
Qed.

(** Where the block may lie: nonzero, 16-aligned, clear of the three heads and of the two stdio words
    [closed_stdio_env] reads. *)
Definition mf_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Definition mf_place (f : Z) : Prop :=
  0 < f /\ f + MF_BLOCK <= 2 ^ 64 /\ f mod 16 = 0 /\
  mf_apart f MF_BLOCK (mf_sink_addr MS) 8 /\ mf_apart f MF_BLOCK (mf_say_addr MS) 8 /\
  mf_apart f MF_BLOCK sk_ofl_head 8 /\ mf_apart f MF_BLOCK sk_threaded 1 /\ mf_apart f MF_BLOCK sk_ofl_lock 4.

(** The three heads: in range, pairwise apart and apart from the two stdio words; the size is not negative. *)
Definition mf_heads_ok : Prop :=
  0 <= mf_sink_addr MS /\ mf_sink_addr MS + 8 <= 2 ^ 64 /\ 0 <= mf_say_addr MS /\ mf_say_addr MS + 8 <= 2 ^ 64 /\
  0 <= sk_ofl_head /\ sk_ofl_head + 8 <= 2 ^ 64 /\
  0 <= sk_threaded /\ sk_threaded + 1 <= 2 ^ 64 /\ 0 <= sk_ofl_lock /\ sk_ofl_lock + 4 <= 2 ^ 64 /\
  mf_apart (mf_sink_addr MS) 8 (mf_say_addr MS) 8 /\ mf_apart (mf_sink_addr MS) 8 sk_ofl_head 8 /\
  mf_apart (mf_say_addr MS) 8 sk_ofl_head 8 /\
  mf_apart (mf_sink_addr MS) 8 sk_threaded 1 /\ mf_apart (mf_say_addr MS) 8 sk_threaded 1 /\
  mf_apart sk_ofl_head 8 sk_threaded 1 /\
  mf_apart (mf_sink_addr MS) 8 sk_ofl_lock 4 /\ mf_apart (mf_say_addr MS) 8 sk_ofl_lock 4 /\
  mf_apart sk_ofl_head 8 sk_ofl_lock 4 /\
  0 <= mf_size MS.

Lemma mf_heads_set_file : forall m f, mf_place f -> forall x, f <= x < f + MF_ZEROED ->
  mbyte segs (mf_heads_set m f) x = mbyte segs m x.
Proof.
  intros m f (H0 & H1 & _ & Hs & Hy & Ho & _) x Hx. unfold mf_heads_set, mf_apart, MF_ZEROED, MF_BLOCK in *.
  rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). reflexivity.
Qed.

(** Every FILE state the code leaves at a return satisfies [memfile_at]: flags F_NORD or F_NORD | F_ERR,
    orientation 0 or -1, the window empty or active with [k <= 1024] bytes pending, [pos <= len <= size]. *)
Lemma mf_state_at : forall mem f fl om wend wpos wbase pos len,
  mf_place f -> 0 <= mf_size MS ->
  fl = F_NORD \/ fl = F_NORD + F_ERR -> om = 0 \/ om = U32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= MF_BUFSIZ /\ wend = f + MF_BUF + MF_BUFSIZ /\ wpos = f + MF_BUF + k /\ wbase = f + MF_BUF) ->
  0 <= pos <= len -> len <= mf_size MS ->
  memfile_at (mf_state mem f fl om wend wpos wbase pos len) f.
Proof.
  intros mem f fl om wend wpos wbase pos len HP Hsz Hfl Hom Hw Hp Hl.
  pose proof HP as (Hf0 & Hf1 & Hf2 & _).
  unfold mf_state. apply (memfile_at_frame (mf_dynw (mf_fm mem f) f fl om wend wpos wbase pos len)).
  { intros x Hx. exact (mf_heads_set_file _ f HP x Hx). }
  unfold mf_dynw, mf_fm.
  split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|].
  split; [|split; [|split; [|split]]].
  - unfold memfile_static. repeat match goal with |- _ /\ _ => split end; mf_fld.
  - destruct Hfl as [-> | ->]; [left | right]; mf_fld.
  - destruct Hom as [-> | ->]; [left | right]; mf_fld.
  - split; [mf_fld|]. split; [mf_fld|].
    destruct Hw as [(-> & -> & ->) | (k & Hk & -> & -> & ->)].
    + left. split; [|split]; mf_fld.
    + right. exists k. split; [exact Hk|]. split; [|split]; mf_fld.
  - exists pos, len. split; [exact Hp|]. split; [exact Hl|]. split; mf_fld.
Qed.

Lemma mf_state_heads : forall mem f fl om wend wpos wbase pos len, mf_heads_ok ->
  mf_heads (mf_state mem f fl om wend wpos wbase pos len) f.
Proof.
  intros mem f fl om wend wpos wbase pos len
    (Hs0 & Hs1 & Hy0 & Hy1 & Ho0 & Ho1 & _ & _ & _ & _ & Hsy & Hso & Hyo & _).
  unfold mf_state, mf_heads_set, mf_heads, mf_apart in *.
  split; [|split]; apply (val_mem_word_mem segs).
  - apply val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply val_mem_upd_same; cbn; lia.
  - apply val_mem_upd_same; cbn; lia.
  - apply val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply val_mem_upd_other; [lia | cbn; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    apply val_mem_upd_same; cbn; lia.
Qed.

(** The GI conjunct's second arm, and the post's clause, hold at every such state. *)
Lemma mf_state_gi : forall mem f fl om wend wpos wbase pos len,
  mf_place f -> mf_heads_ok ->
  fl = F_NORD \/ fl = F_NORD + F_ERR -> om = 0 \/ om = U32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= MF_BUFSIZ /\ wend = f + MF_BUF + MF_BUFSIZ /\ wpos = f + MF_BUF + k /\ wbase = f + MF_BUF) ->
  0 <= pos <= len -> len <= mf_size MS ->
  mf_gi [(f, MF_BLOCK)] (mf_state mem f fl om wend wpos wbase pos len).
Proof.
  intros mem f fl om wend wpos wbase pos len HP HH Hfl Hom Hw Hp Hl.
  right. exists f. split; [exact (mf_state_heads mem f fl om wend wpos wbase pos len HH)|].
  split; [reflexivity|].
  apply mf_state_at; try assumption. destruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H).
  exact H.
Qed.

Lemma mf_state_env : forall mem f fl om wend wpos wbase pos len,
  mf_place f -> mf_heads_ok -> closed_stdio_env B mem ->
  closed_stdio_env B (mf_state mem f fl om wend wpos wbase pos len).
Proof.
  intros mem f fl om wend wpos wbase pos len HP HH [Ht Hl].
  destruct HP as (Hf0 & Hf1 & _ & _ & _ & _ & Hft & Hfl).
  destruct HH as (Hs0 & Hs1 & Hy0 & Hy1 & Ho0 & Ho1 & Ht0 & Ht1 & Hl0 & Hl1 & _ & _ & _ & Hst & Hyt & Hot & Hsl & Hyl & Hol & _).
  assert (K : forall a n v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> mf_apart f MF_BLOCK a (Z.of_nat n) ->
    mf_apart (mf_sink_addr MS) 8 a (Z.of_nat n) -> mf_apart (mf_say_addr MS) 8 a (Z.of_nat n) ->
    mf_apart sk_ofl_head 8 a (Z.of_nat n) ->
    val_mem segs mem a n v -> val_mem segs (mf_state mem f fl om wend wpos wbase pos len) a n v).
  { intros a n v Ha0 Ha1 Haf Has Hay Hao Hv k Hk. unfold mf_state, mf_heads_set.
    unfold mf_apart, MF_BLOCK, MF_ZEROED in *.
    rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite mf_upd_out by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite mf_dynw_out by (unfold MF_ZEROED; lia). rewrite mf_fm_out by (unfold MF_ZEROED; lia).
    exact (Hv k Hk). }
  split.
  - apply K; [exact Ht0 | exact Ht1 | exact Hft | exact Hst | exact Hyt | exact Hot | exact Ht].
  - apply K; [exact Hl0 | exact Hl1 | exact Hfl | exact Hsl | exact Hyl | exact Hol | exact Hl].
Qed.

Lemma mf_state_sink : forall mem md f fl om wend wpos wbase pos len,
  mf_place f -> mf_heads_ok ->
  fl = F_NORD \/ fl = F_NORD + F_ERR -> om = 0 \/ om = U32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= MF_BUFSIZ /\ wend = f + MF_BUF + MF_BUFSIZ /\ wpos = f + MF_BUF + k /\ wbase = f + MF_BUF) ->
  0 <= pos <= len -> len <= mf_size MS ->
  closed_stdio_env B mem -> Namei.fd_names_path (m_fds md) sink_path = false ->
  mf_sink (mf_state mem f fl om wend wpos wbase pos len) md.
Proof.
  intros mem md f fl om wend wpos wbase pos len HP HH Hfl Hom Hw Hp Hl He Hn.
  apply (mf_sink_of_gi [(f, MF_BLOCK)]); [apply mf_state_gi; assumption | | exact Hn].
  exact (mf_state_env mem f fl om wend wpos wbase pos len HP HH He).
Qed.

End c.

(** ** Across a callee's journal

    The released callee contracts end in a [journal] (YI06.v), whose image clause keeps every image byte the
    allocator does not own outside the open-sink footprint, and whose block clauses keep a live block that the
    footprint avoids. Like [sink_none_kept] / [sink_kept] for the fopen sink (YI14.v), [mf_sink] and the FILE
    block survive such a call when the three heads are image bytes the allocator does not own. *)
Section k.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Context {SH : sink_head} {SK : sink_syms}.
Variable MS : memfile_syms.
Local Notation segs := (ms_segs B).

Lemma mf_block_kept : forall STK sp0 FP L A mem md L' A' mem' md' f,
  journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
  In (f, MF_BLOCK) (blocks L A) -> fp_avoids FP f (f + MF_BLOCK) ->
  In (f, MF_BLOCK) (blocks L' A') /\
  (forall x, f <= x < f + MF_BLOCK -> mbyte segs mem' x = mbyte segs mem x).
Proof.
  intros STK sp0 FP L A mem md L' A' mem' md' f HJ Hin Hav.
  pose proof HJ as (HH & Hos & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
  assert (HFB : MF_BLOCK = 1304) by reflexivity.
  assert (Hlive : In (f, MF_BLOCK) (blocks L' A')).
  { destruct (in_dec zz_eq_dec (f, MF_BLOCK) (blocks L' A')) as [H|H]; [exact H|]. exfalso.
    apply (Hav (f + 0)); [lia|]. apply (Hgone f MF_BLOCK 0 Hin H). lia. }
  split; [exact Hlive|].
  intros x Hx. replace x with (f + (x - f)) by lia. apply (Hblk f MF_BLOCK (x - f) Hin Hlive); [lia|].
  replace (f + (x - f)) with x by lia. apply Hav. exact Hx.
Qed.

Lemma mf_sink_kept : forall {SL : sink_laws B} STK sp0 FP L A mem md L' A' mem' md',
  journal B MR STK sp0 FP L A mem md L' A' mem' md' -> ~ sink_open_fp FP ->
  (forall a, mf_head_addr MS a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
  (forall f, mf_heads B MS mem f -> memfile_at B MS mem f ->
     In (f, MF_BLOCK) (blocks L A) /\ fp_avoids FP f (f + MF_BLOCK)) ->
  mf_sink B MS mem md -> mf_sink B MS mem' md'.
Proof.
  intros SL STK sp0 FP L A mem md L' A' mem' md' HJ Hn HHI HB (He & Hnm & H).
  pose proof HJ as (HH & Hos & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
  assert (Himgb : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
    ~ (errno_addr B <= a < errno_addr B + 4) -> mbyte segs mem' a = mbyte segs mem a).
  { intros a H1 H2 H3 H4. apply (Himg a H1 H2 H3 H4). intros [Ho _]. exact (Hn Ho). }
  assert (Himge : forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. destruct (skl_env B a Ha) as (T1 & T2 & T3 & T4). exact (Himgb _ T1 T2 T3 T4). }
  assert (Hh : forall a, mf_head_addr MS a -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. destruct (HHI a Ha) as (T1 & T2 & T3 & T4). exact (Himgb _ T1 T2 T3 T4). }
  destruct (os_step_shielded FP md md' Hos Hn) as (Efd & _ & _).
  split; [exact (closed_stdio_env_frame B mem mem' Himge He)|].
  split; [rewrite Efd; exact Hnm|].
  destruct H as [H0 | (f & Hf & Hm)].
  - left. exact (mf_heads_frame B MS mem mem' 0 Hh H0).
  - right. exists f. split; [exact (mf_heads_frame B MS mem mem' f Hh Hf)|].
    destruct (HB f Hf Hm) as [Hin Hav].
    destruct (mf_block_kept STK sp0 FP L A mem md L' A' mem' md' f HJ Hin Hav) as [_ Hfr].
    apply (memfile_at_frame B MS mem mem' f); [|exact Hm].
    intros x Hx. apply Hfr. unfold MF_ZEROED, MF_BLOCK in *. lia.
Qed.

End k.

(** ** Accounting of the kept block

    The frame's T-form posts charge the kept blocks by [TD T T' b]: the first mark keeps the FILE
    ([T = []], [T' = [(f, MF_BLOCK)]]: one block of 1304 bytes more), every later call keeps it again
    ([T = T']: the bound is unchanged). *)
Lemma mf_TD_open : forall f b, TD [] [(f, MF_BLOCK)] b = sb_malloc b MF_BLOCK.
Proof. intros f [l y c]. reflexivity. Qed.

Lemma mf_TD_keep : forall f b, TD [(f, MF_BLOCK)] [(f, MF_BLOCK)] b = b.
Proof.
  intros f [l y c]. unfold TD. cbn [fold_left snd]. unfold sb_free, sb_malloc. cbn [sb_live sb_bytes sb_cap].
  f_equal; lia.
Qed.

Lemma mf_TD_none : forall b, TD [] [] b = b.
Proof. intros b. reflexivity. Qed.

(** ** Room: the budget premise cuts fmemopen's failure path

    fmemopen returns 0 only when its malloc does (+0x9c [bnez a0], else +0x6c [mv a0,zero]), and only then
    does mark_quietly abort (fuzz_link.c:157-159; ubsan 0x16430 [beqz a0] to 0x16464 [jal abort]). The
    frame's malloc contract returns a non-zero, 16-aligned, fresh block whenever [room_slots b n] holds
    ([malloc_ret]: [res <> 0]); for the halts statements that room comes from the 16 GiB premise through
    the slot's [lib_room], as for link's other mallocs, and for ubsan_agrees through [room_cf]
    ([SlotAgree.room_cf_of_limit]: [2 ^ 34 <= vm_limit]). The FILE asks for 1304 bytes. *)
Lemma mf_room_slots : forall b, sb_live b + 1 <= sb_cap b <= CAPMAX -> 0 <= sb_bytes b ->
  sb_bytes b + MF_BLOCK <= 2 ^ 40 -> room_slots b MF_BLOCK.
Proof. intros b Hc Hb Hn. apply room_slots_small; [unfold MF_BLOCK; lia | exact Hc | exact Hb | exact Hn]. Qed.

Lemma mf_room_cf : forall md b, 2 ^ 34 <= vm_limit (m_vmmaps md) -> 0 <= sb_live b ->
  sb_live b + 1 <= sb_cap b <= SlotAgree.CAP_AG -> 0 <= sb_bytes b -> sb_bytes b + MF_BLOCK <= 2 ^ 29 ->
  SlotAgree.room_cf md b MF_BLOCK.
Proof.
  intros md b Hl Hl0 Hc Hb Hn. apply SlotAgree.room_cf_of_limit; [exact Hl | | lia | exact Hn].
  apply mf_room_slots; [unfold SlotAgree.CAP_AG, CAPMAX in *; lia | exact Hb | unfold MF_BLOCK in *; lia].
Qed.

(** ** Link's UBSan instance, each value read from link's UBSan image

    [link_mf_code] lists the instructions the values come from, as (address, instruction) pairs;
    [link_mf_code_ok] checks each against the image's code table (a vm_compute over the pinned image), and
    [link_mf_from_image] computes each value from those instructions:
    - [g_sink]: mark_quietly 0x16404 [auipc s2,0x5f], 0x1642c [sd a0,-0x69c(s2)] (fmemopen's result);
    - [g_said]: 0x16414 [auipc a0,0x5f], 0x1641c [addi a0,a0,-0x6a4] (fmemopen's first argument);
    - size: 0x16424 [lui a1,1] (its second argument, 4096);
    - mode: 0x16418 [auipc a1,0xffffa], 0x16420 [addi a2,a1,0x14a] (its third argument, the string at
      0x10562, whose bytes are "w\0", [link_mf_mode_bytes]); fmemopen +0x104 [lbu a0,0(s3)], +0x108
      [sw a0,0x108(s0)] store its first byte in the cookie;
    - [g_say]: reac_served_say_to 0x16b84 [auipc a1,0x5f], 0x16b88 [sd a0,0x1ec(a1)];
    - read / write / seek / close: fmemopen 0x19c3c-0x19c48 [auipc a0..a3,0], 0x19c50-0x19c5c
      [addi a0,a0,0x68 / a1,a1,0x138 / a2,a2,0x248 / a3,a3,0x2e0], stored at 0x19c68 [sd a0,0x40(s0)],
      0x19c6c [sd a1,0x48(s0)], 0x19c70 [sd a2,0x50(s0)], 0x19c64 [sd a3,0x18(s0)]. *)
Definition link_mf : memfile_syms := {|
  mf_sink_addr := 0x74d68; mf_say_addr := 0x75d70; mf_buf := 0x74d70; mf_size := 4096; mf_mode := 119;
  mf_read := 0x19ca4; mf_write := 0x19d78; mf_seek := 0x19e8c; mf_close := 0x19f28 |}.

(** ** Reading link's image

    [code_at tbl pc] is the instruction at [pc] in the image's code table ([src0tbl], [table_ok]: the word
    [fetch_word] reads there), when it is a 4-byte instruction and not [ecall]. [ishape] writes an expected
    instruction with signed immediates and absolute branch targets; [code_list_ok] checks a list of them. *)
Inductive ishape : Type :=
| SAuipc (rd u : Z)                      (* auipc rd, u *)
| SLui (rd u : Z)                        (* lui rd, u *)
| SAddi (rd rs1 imm : Z)                 (* addi rd, rs1, imm *)
| SLd (nbytes : Z) (sg : bool) (rd rs1 off : Z)  (* load nbytes (sign-extending if sg) rd <- mem[rs1 + off] *)
| SSt (nbytes : Z) (rs1 rs2 off : Z)     (* store nbytes mem[rs1 + off] <- rs2 *)
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

(** The instructions [link_mf] and the layout above are read from (UBSan image). *)
Definition link_mf_code : list (Z * ishape) := [
  (0x16404, SAuipc 18 0x5f);  (* mark_quietly +0x18 auipc s2,0x5f *)
  (0x16408, SLd 8 true 11 18 (-1692));  (* +0x1c ld a1,-0x69c(s2): if (!g_sink) *)
  (0x16414, SAuipc 10 0x5f);  (* +0x28 auipc a0,0x5f *)
  (0x16418, SAuipc 11 (-6));  (* +0x2c auipc a1,0xffffa *)
  (0x1641c, SAddi 10 10 (-1700));  (* +0x30 addi a0,a0,-0x6a4: g_said *)
  (0x16420, SAddi 12 11 0x14a);  (* +0x34 addi a2,a1,0x14a: "w" *)
  (0x16424, SLui 11 1);  (* +0x38 lui a1,1: 4096 *)
  (0x16428, SJal 1 0x19ad4);  (* +0x3c jal fmemopen *)
  (0x1642c, SSt 8 18 10 (-1692));  (* +0x40 sd a0,-0x69c(s2): g_sink = ... *)
  (0x16430, SBr BC_EQ 10 0 0x16464);  (* +0x44 beqz a0 -> abort *)
  (0x16434, SJal 1 0x16b84);  (* +0x48 jal reac_served_say_to *)
  (0x16440, SJal 1 0x1a3f8);  (* +0x54 jal rewind *)
  (0x16464, SJal 1 0x17644);  (* +0x78 jal abort *)
  (0x16b84, SAuipc 11 0x5f);  (* reac_served_say_to auipc a1,0x5f *)
  (0x16b88, SSt 8 11 10 0x1ec);  (* sd a0,0x1ec(a1): g_say = out *)
  (0x19b68, SAddi 10 0 0x518);  (* fmemopen +0x94 addi a0,zero,0x518 *)
  (0x19b6c, SJal 1 0x17d48);  (* +0x98 jal malloc *)
  (0x19b70, SBr BC_NE 10 0 0x19b84);  (* +0x9c bnez a0 *)
  (0x19b88, SAddi 12 0 0x110);  (* +0xb4 addi a2,zero,0x110 *)
  (0x19b8c, SAddi 11 0 0);  (* +0xb8 mv a1,zero *)
  (0x19b90, SJal 1 0x1f894);  (* +0xbc jal memset *)
  (0x19b94, SAddi 10 8 0xe8);  (* +0xc0 addi a0,s0,0xe8 *)
  (0x19b98, SAddi 11 0 (-1));  (* +0xc4 addi a1,zero,-1 *)
  (0x19b9c, SAddi 12 8 0x118);  (* +0xc8 addi a2,s0,0x118 *)
  (0x19ba0, SSt 8 8 10 0x98);  (* +0xcc sd a0,0x98(s0): cookie *)
  (0x19ba4, SAddi 10 0 0x400);  (* +0xd0 addi a0,zero,0x400 *)
  (0x19ba8, SSt 8 8 12 0x58);  (* +0xd4 sd a2,0x58(s0): buf *)
  (0x19bac, SSt 8 8 10 0x60);  (* +0xd8 sd a0,0x60(s0): buf_size *)
  (0x19bb0, SSt 4 8 11 0x78);  (* +0xdc sw a1,0x78(s0): fd *)
  (0x19bb4, SSt 4 8 11 0x90);  (* +0xe0 sw a1,0x90(s0): lbf *)
  (0x19bd0, SSt 8 8 18 0xf8);  (* +0xfc sd s2,0xf8(s0): c.size *)
  (0x19bd4, SSt 8 8 9 0x100);  (* +0x100 sd s1,0x100(s0): c.buf *)
  (0x19bd8, SLd 1 false 10 19 0);  (* +0x104 lbu a0,0(s3) *)
  (0x19bdc, SSt 4 8 10 0x108);  (* +0x108 sw a0,0x108(s0): c.mode *)
  (0x19bf0, SAddi 10 0 4);  (* +0x11c addi a0,zero,4 *)
  (0x19bfc, SSt 4 8 10 0);  (* +0x128 sw a0,0(s0): flags *)
  (0x19c3c, SAuipc 10 0);  (* +0x168 auipc a0,0 *)
  (0x19c40, SAuipc 11 0);  (* +0x16c auipc a1,0 *)
  (0x19c44, SAuipc 12 0);  (* +0x170 auipc a2,0 *)
  (0x19c48, SAuipc 13 0);  (* +0x174 auipc a3,0 *)
  (0x19c4c, SAuipc 14 0x7c);  (* +0x178 auipc a4,0x7c *)
  (0x19c50, SAddi 10 10 0x68);  (* +0x17c addi a0,a0,0x68: mread *)
  (0x19c54, SAddi 11 11 0x138);  (* +0x180 addi a1,a1,0x138: mwrite *)
  (0x19c58, SAddi 12 12 0x248);  (* +0x184 addi a2,a2,0x248: mseek *)
  (0x19c5c, SAddi 13 13 0x2e0);  (* +0x188 addi a3,a3,0x2e0: mclose *)
  (0x19c60, SLd 1 false 14 14 0x48d);  (* +0x18c lbu a4,0x48d(a4): __libc.threaded *)
  (0x19c64, SSt 8 8 13 0x18);  (* +0x190 sd a3,0x18(s0): close *)
  (0x19c68, SSt 8 8 10 0x40);  (* +0x194 sd a0,0x40(s0): read *)
  (0x19c6c, SSt 8 8 11 0x48);  (* +0x198 sd a1,0x48(s0): write *)
  (0x19c70, SSt 8 8 12 0x50);  (* +0x19c sd a2,0x50(s0): seek *)
  (0x19c74, SBr BC_NE 14 0 0x19c80);  (* +0x1a0 bnez a4 *)
  (0x19c78, SAddi 10 0 (-1));  (* +0x1a4 addi a0,zero,-1 *)
  (0x19c7c, SSt 4 8 10 0x8c);  (* +0x1a8 sw a0,0x8c(s0): lock *)
  (0x19ca0, SJal 0 0x1a3b8);  (* +0x1cc j __ofl_add *)
  (0x1a388, SAuipc 10 0x7c);  (* __ofl_lock +0xc auipc a0,0x7c *)
  (0x1a38c, SAddi 8 10 0x178);  (* +0x10 addi s0,a0,0x178: &ofl_lock *)
  (0x1a398, SAddi 10 8 8);  (* +0x1c addi a0,s0,8: &ofl_head *)
  (0x1a3c8, SJal 1 0x1a37c);  (* __ofl_add +0x10 jal __ofl_lock *)
  (0x1a3cc, SLd 8 true 11 10 0);  (* +0x14 ld a1,0(a0) *)
  (0x1a3d0, SSt 8 8 11 0x70);  (* +0x18 sd a1,0x70(s0): next = head *)
  (0x1a3dc, SSt 8 10 8 0);  (* +0x24 sd s0,0(a0): head = f *)
  (0x1a1e4, SJal 1 0x1a37c);  (* __stdio_exit +0xc jal __ofl_lock *)
  (0x1a1e8, SLd 8 true 8 10 0);  (* +0x10 ld s0,0(a0) *)
  (0x1a1ec, SBr BC_NE 8 0 0x1a318);  (* +0x14 bnez s0 -> loop *)
  (0x1a310, SLd 8 true 8 8 0x70);  (* loop +0x0 ld s0,0x70(s0) *)
  (0x1a314, SBr BC_EQ 8 0 0x1a1f0);  (* loop +0x4 beqz s0, -0x124 *)
  (0x1a318, SLd 4 true 10 8 0x8c);  (* loop +0x8 lw a0,0x8c(s0) *)
  (0x1a31c, SBr BC_LT 10 0 0x1a328);  (* loop +0xc bltz a0, 0xc *)
  (0x1a320, SAddi 10 8 0);  (* loop +0x10 mv a0,s0 *)
  (0x1a324, SJal 1 0x19978);  (* loop +0x14 jal __lockfile (taken only when lock >= 0) *)
  (0x1a328, SLd 8 true 10 8 0x28);  (* loop +0x18 ld a0,0x28(s0) *)
  (0x1a32c, SLd 8 true 11 8 0x38);  (* loop +0x1c ld a1,0x38(s0) *)
  (0x1a330, SBr BC_EQ 10 11 0x1a348);  (* loop +0x20 beq a0, a1, 0x18 *)
  (0x1a334, SLd 8 true 13 8 0x48);  (* loop +0x24 ld a3,0x48(s0) *)
  (0x1a338, SAddi 10 8 0);  (* loop +0x28 mv a0,s0 *)
  (0x1a33c, SAddi 11 0 0);  (* loop +0x2c mv a1,zero *)
  (0x1a340, SAddi 12 0 0);  (* loop +0x30 mv a2,zero *)
  (0x1a344, SJalr 1 13 0);  (* loop +0x34 jalr a3: f->write (+0x34) / f->seek (+0x54) *)
  (0x1a348, SLd 8 true 10 8 8);  (* loop +0x38 ld a0,8(s0) *)
  (0x1a34c, SLd 8 true 11 8 0x10);  (* loop +0x3c ld a1,0x10(s0) *)
  (0x1a350, SBr BC_EQ 10 11 0x1a310);  (* loop +0x40 beq a0, a1, -0x40 *)
  (0x1a354, SLd 8 true 13 8 0x50);  (* loop +0x44 ld a3,0x50(s0) *)
  (0x1a35c, SAddi 12 0 1);  (* loop +0x4c addi a2,zero,1 *)
  (0x1a360, SAddi 10 8 0);  (* loop +0x50 mv a0,s0 *)
  (0x1a364, SJalr 1 13 0);  (* loop +0x54 jalr a3: f->write (+0x34) / f->seek (+0x54) *)
  (0x1a368, SJal 0 0x1a310)  (* loop +0x58 j -0x58 *)
].

Lemma link_mf_code_ok : code_list_ok src0tbl link_mf_code = true.
Proof. vm_compute. reflexivity. Qed.

(** The mode string fmemopen gets is "w" (its two bytes in the image). *)
Lemma link_mf_mode_bytes :
  option_map bv_unsigned (seg_rom src0segs (Z_to_bv 64 (0x16418 + (-6) * 4096 + 0x14a))) = Some 119 /\
  option_map bv_unsigned (seg_rom src0segs (Z_to_bv 64 (0x16418 + (-6) * 4096 + 0x14a + 1))) = Some 0.
Proof. split; vm_compute; reflexivity. Qed.

(** Each value from the immediates in [link_mf_code] (auipc + addi / ld / sd: [pc + u * 4096 + imm]). *)
Lemma link_mf_from_image :
  mf_sink_addr link_mf = 0x16404 + 0x5f * 4096 + (-1692) /\
  mf_say_addr link_mf = 0x16b84 + 0x5f * 4096 + 0x1ec /\
  mf_buf link_mf = 0x16414 + 0x5f * 4096 + (-1700) /\
  mf_size link_mf = 1 * 4096 /\
  mf_mode link_mf = 119 /\
  mf_read link_mf = 0x19c3c + 0 * 4096 + 0x68 /\
  mf_write link_mf = 0x19c40 + 0 * 4096 + 0x138 /\
  mf_seek link_mf = 0x19c44 + 0 * 4096 + 0x248 /\
  mf_close link_mf = 0x19c48 + 0 * 4096 + 0x2e0.
Proof. repeat split; reflexivity. Qed.

(** The layout constants and the stdio words, from the same instructions: the malloc size, the memset
    length, the cookie and buffer offsets, the buffer size, F_NORD; [__libc.threaded] (fmemopen +0x178 /
    +0x18c) and the list head (__ofl_lock +0xc / +0x10 / +0x1c) are the frame's [sk_threaded] / [sk_ofl_head]. *)
Lemma link_layout_from_image :
  MF_BLOCK = 0x518 /\ MF_ZEROED = 0x110 /\ MF_COOKIE = 0xe8 /\ MF_BUF = 0x118 /\ MF_BUFSIZ = 0x400 /\
  F_NORD = 4 /\
  @sk_threaded src0_sink = 0x19c4c + 0x7c * 4096 + 0x48d /\
  @sk_ofl_lock src0_sink = 0x1a388 + 0x7c * 4096 + 0x178 /\
  @sk_ofl_head src0_sink_head = 0x1a388 + 0x7c * 4096 + 0x178 + 8.
Proof. repeat split; reflexivity. Qed.
