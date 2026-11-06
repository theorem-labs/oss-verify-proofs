(** * reac-pw/fuzz_link (plain): the memory FILE's record and the post clause [mf_sink], below the slot's
    contract forms.

    The frame's slot contract forms ([lib_pre_x], [lib_post_x_R], ... in Reusable/YL0i.v) state the open-file
    clause of the slot's pre and post as [mf_sink B link_mf]. So [mf_sink], [memfile_at] and link's record
    [link_mf] live here, in a file YL0i.v can import; MemFile.v re-exports this file and keeps everything that
    needs YL0i.v (the GI conjunct [mf_gi], the frame lemmas, the image checks). The text of each definition is
    the one MemFile.v had (MemFile.v holds the comments on each value and where it is read from). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI06 YI16 YI00 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** Layout of musl's [struct mem_FILE] (MemFile.v: each value with the instruction it is read from). *)
Definition MF_BLOCK : Z := 1304.
Definition MF_ZEROED : Z := 272.
Definition MF_COOKIE : Z := 232.
Definition MF_BUF : Z := 280.
Definition MF_BUFSIZ : Z := 1024.
Definition F_NORD : Z := 4.
Definition F_ERR : Z := 32.

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

Definition memfile_flags (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 0 4 F_NORD \/ fld mem f 0 4 (F_NORD + F_ERR).

Definition memfile_omode (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 136 4 0 \/ fld mem f 136 4 U32M1.

Definition memfile_window (mem : word -> option byte) (f : Z) : Prop :=
  fld mem f 8 8 0 /\ fld mem f 16 8 0 /\
  ((fld mem f 32 8 0 /\ fld mem f 40 8 0 /\ fld mem f 56 8 0) \/
   (exists k, 0 <= k <= MF_BUFSIZ /\
      fld mem f 32 8 (f + MF_BUF + MF_BUFSIZ) /\ fld mem f 40 8 (f + MF_BUF + k) /\ fld mem f 56 8 (f + MF_BUF))).

Definition memfile_cookie (mem : word -> option byte) (f : Z) : Prop :=
  exists pos len, 0 <= pos <= len /\ len <= mf_size MS /\
    fld mem f MF_COOKIE 8 pos /\ fld mem f (MF_COOKIE + 8) 8 len.

Definition memfile_at (mem : word -> option byte) (f : Z) : Prop :=
  0 < f /\ f + MF_BLOCK <= 2 ^ 64 /\ f mod 16 = 0 /\
  memfile_static mem f /\ memfile_flags mem f /\ memfile_omode mem f /\ memfile_window mem f /\
  memfile_cookie mem f.

Definition mf_heads (mem : word -> option byte) (v : Z) : Prop :=
  word_mem segs mem (mf_sink_addr MS) v /\ word_mem segs mem (mf_say_addr MS) v /\
  word_mem segs mem sk_ofl_head v.

Definition mf_sink (mem : word -> option byte) (md : Model) : Prop :=
  closed_stdio_env B mem /\ Namei.fd_names_path (m_fds md) sink_path = false /\
  (mf_heads mem 0 \/ exists f, mf_heads mem f /\ memfile_at mem f).

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

End c.

(** Link's plain instance (MemFile.v [link_mf_code] / [link_mf_from_image]: each value read from link's
    plain image). *)
Definition link_mf : memfile_syms := {|
  mf_sink_addr := 0x74528; mf_say_addr := 0x75530; mf_buf := 0x74530; mf_size := 4096; mf_mode := 119;
  mf_read := 0x19470; mf_write := 0x19544; mf_seek := 0x19658; mf_close := 0x196f4 |}.
