(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YI14.v, with its module paths changed; 15 of its 334 lines of code are new or changed and 3 lines of the source are left out. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition FILE_BLOCK : Z := 1264.
Definition FILE_BUF_OFF : Z := 240.
Definition FILE_BUFSIZ : Z := 1024.
Definition SINK_MAX : Z := 2 ^ 62.
Definition U32M1 : Z := 4294967295.
Definition bytes (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma bytes_length : forall l, length (bytes l) = length l.
Proof. intros l. unfold bytes. apply length_map. Qed.
Lemma bytes_app : forall l1 l2, bytes (l1 ++ l2) = bytes l1 ++ bytes l2.
Proof. intros. unfold bytes. apply map_app. Qed.
Lemma bytes_inj : forall l1 l2, bytes_ok l1 -> bytes_ok l2 -> bytes l1 = bytes l2 -> l1 = l2.
Proof.
assert (HU : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x).
{ intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
induction l1 as [|x l1 IH]; intros [|y l2] H1 H2 E; cbn in E; try discriminate; [reflexivity|].
pose proof (f_equal (fun l => match l with b :: _ => bv_unsigned b | [] => 0 end) E) as Exy.
pose proof (f_equal (@tl _) E) as Et. cbn [tl] in Et. cbv beta iota in Exy.
inversion H1; subst. inversion H2; subst. rewrite !HU in Exy by assumption. f_equal; [exact Exy | apply IH; assumption].
Qed.
Class sink_syms : Type := mkSinkSyms {
sk_ofl_lock : Z;
sk_threaded : Z;
sk_read : Z; sk_write : Z; sk_seek : Z; sk_close : Z;
sk_path_addr : Z;
sk_mode_addr : Z;
sk_trailer_addr : Z;
sk_rwa_addr : Z;
sk_highs_addr : Z;
sk_ones_addr : Z
}.
Definition sink_trailer_Z : list Z := [59].
Definition sink_rwa_Z : list Z := [114; 119; 97; 0; 47; 100; 101; 118].
Definition sink_highs_Z : list Z := [128; 128; 128; 128; 128; 128; 128; 128].
Definition sink_ones_Z : list Z := [0; 1; 1; 1; 1; 1; 1; 1].
Section c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).
Local Notation fld mem f off n v := (val_mem segs mem (f + off) n v).
Definition file_static (mem : word -> option byte) (f fd : Z) : Prop :=
0 <= fd < 2 ^ 31 /\
fld mem f 0 4 4   /\ fld mem f 8 8 0   /\ fld mem f 16 8 0   /\
fld mem f 24 8 sk_close /\ fld mem f 48 8 0   /\
fld mem f 64 8 sk_read /\ fld mem f 72 8 sk_write /\ fld mem f 80 8 sk_seek /\
fld mem f 88 8 (f + FILE_BUF_OFF)   /\ fld mem f 96 8 FILE_BUFSIZ   /\
fld mem f 104 8 0   /\ fld mem f 112 8 0   /\
fld mem f 120 4 fd /\ fld mem f 124 4 0   /\ fld mem f 128 8 0   /\
fld mem f 140 4 U32M1   /\ fld mem f 144 4 U32M1   /\
fld mem f 152 8 0   /\ fld mem f 160 8 0   /\ fld mem f 168 8 0   /\
fld mem f 176 8 0   /\ fld mem f 184 8 0   /\ fld mem f 192 8 0 /\ fld mem f 200 8 0   /\
fld mem f 208 8 0 /\ fld mem f 216 8 0   /\ fld mem f 224 8 0  .
Definition file_window (mem : word -> option byte) (f : Z) (P : list Z) : Prop :=
(P = [] /\ fld mem f 32 8 0   /\ fld mem f 40 8 0   /\ fld mem f 56 8 0   /\ fld mem f 136 4 0  )
\/
(fld mem f 32 8 (f + FILE_BUF_OFF + FILE_BUFSIZ) /\ fld mem f 40 8 (f + FILE_BUF_OFF + Z.of_nat (length P)) /\
fld mem f 56 8 (f + FILE_BUF_OFF) /\ fld mem f 136 4 U32M1   /\
garr8 segs mem (f + FILE_BUF_OFF) P /\ Z.of_nat (length P) <= FILE_BUFSIZ).
Definition file_at (mem : word -> option byte) (f fd : Z) (P : list Z) : Prop :=
file_static mem f fd /\ file_window mem f P.
Definition stdio_env (mem : word -> option byte) : Prop :=
val_mem segs mem sk_threaded 1 0 /\
val_mem segs mem sk_ofl_lock 4 0 /\
garr8 segs mem sk_path_addr (sink_path_Z ++ [0]) /\
garr8 segs mem sk_mode_addr (sink_mode_Z ++ [0]) /\
garr8 segs mem sk_trailer_addr (sink_trailer_Z ++ [0]) /\
garr8 segs mem sk_rwa_addr sink_rwa_Z /\
garr8 segs mem sk_highs_addr sink_highs_Z /\
garr8 segs mem sk_ones_addr sink_ones_Z.
Definition names_sink (e : FdEntry) : Prop :=
match e with FdFile p _ | FdFileW p _ | FdFileA p _ | FdFileRW p _ => p = sink_path | _ => False end.
Definition sink_at (mem : word -> option byte) (md : Model) (f : Z) (S : list Z) : Prop :=
exists (fd : Z) (W P : list Z),
S = W ++ P /\ bytes_ok S /\ Z.of_nat (length S) <= SINK_MAX /\
stdio_env mem /\ file_at mem f fd P /\ word_mem segs mem sk_ofl_head f /\ f <> 0 /\
Fs.fs_lookup (m_fs md) sink_path = Some (bytes W) /\
fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length W)))) /\
Namei.fd_names_path (fd_remove (m_fds md) (Z_to_bv 64 fd)) sink_path = false.
(* The checksum harness never opens a GIF sink.  A closed sink therefore
   needs only the musl lock state and empty open-file list; CGIF-specific
   string/table contents remain obligations of stdio_env for sink_at. *)
Definition closed_stdio_env (mem : word -> option byte) : Prop :=
val_mem segs mem sk_threaded 1 0 /\ val_mem segs mem sk_ofl_lock 4 0.
Definition sink_none (mem : word -> option byte) (md : Model) : Prop :=
closed_stdio_env mem /\ word_mem segs mem sk_ofl_head 0 /\
Namei.fd_names_path (m_fds md) sink_path = false.
Lemma fd_names_path_lookup : forall fds fd e,
Namei.fd_names_path fds sink_path = false -> fd_lookup fds fd = Some e -> ~ names_sink e.
Proof.
induction fds as [|[k e0] r IH]; intros fd e Hs Hl; [discriminate Hl|].
cbn [fd_lookup] in Hl.
assert (Hr : Namei.fd_names_path r sink_path = false).
{ cbn [Namei.fd_names_path] in Hs. destruct e0; try exact Hs; apply Bool.orb_false_iff in Hs; exact (proj2 Hs). }
destruct (bv_eqb k fd); [|exact (IH fd e Hr Hl)].
injection Hl as <-. intros Hn. cbn [Namei.fd_names_path] in Hs.
destruct e0; cbn in Hn; try contradiction; subst p;
apply Bool.orb_false_iff in Hs; destruct Hs as [Hs _]; rewrite Fs.path_eqb_refl in Hs; discriminate Hs.
Qed.
Definition sink_closed (md0 md : Model) (S : list Z) : Prop :=
m_fds md = m_fds md0 /\ m_fs md = Fs.fs_set (m_fs md0) sink_path (bytes S).
Definition sink_gone (md0 md : Model) : Prop :=
m_fds md = m_fds md0 /\ m_fs md = Fs.fs_remove (m_fs md0) sink_path.
Definition sink_fp (f : Z) : list (Z * Z) := [sink_token; (f, f + FILE_BLOCK)].
Definition fp_avoids (FP : list (Z * Z)) (lo hi : Z) : Prop := forall a, lo <= a < hi -> ~ inFP FP a.
Definition env_addr (a : Z) : Prop :=
(sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4) \/
(sk_path_addr <= a < sk_path_addr + 13) \/ (sk_mode_addr <= a < sk_mode_addr + 3) \/
(sk_trailer_addr <= a < sk_trailer_addr + 2) \/
(sk_rwa_addr <= a < sk_rwa_addr + 8) \/ (sk_highs_addr <= a < sk_highs_addr + 8) \/ (sk_ones_addr <= a < sk_ones_addr + 8).
Class sink_laws : Prop := mkSinkLaws {
skl_env : forall a, env_addr a ->
in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4);
skl_errno : forall a, errno_addr B <= a < errno_addr B + 4 ->
in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)
}.
Lemma val_mem_frame : forall (mem mem' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> mbyte segs mem' x = mbyte segs mem x) ->
val_mem segs mem a n v -> val_mem segs mem' a n v.
Proof. intros mem mem' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.
Lemma stdio_env_frame : forall (mem mem' : word -> option byte),
(forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a) -> stdio_env mem -> stdio_env mem'.
Proof.
intros mem mem' Hfr (H1 & H0 & H2 & H3 & H4 & H5 & H6 & H7). split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- eapply val_mem_frame; [|exact H1]. intros x Hx. apply Hfr. right. left. cbn in Hx. lia.
- eapply val_mem_frame; [|exact H0]. intros x Hx. apply Hfr. right. right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H2|]. intros x Hx. apply Hfr. right. right. right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H3|]. intros x Hx. apply Hfr. right. right. right. right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H4|]. intros x Hx. apply Hfr. right. right. right. right. right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H5|]. intros x Hx. apply Hfr. do 6 right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H6|]. intros x Hx. apply Hfr. do 7 right. left. cbn in Hx. lia.
- eapply garr8_frame; [exact H7|]. intros x Hx. apply Hfr. do 8 right. cbn in Hx. lia.
Qed.
Lemma file_at_frame : forall (mem mem' : word -> option byte) f fd P,
(forall x, f <= x < f + FILE_BLOCK -> mbyte segs mem' x = mbyte segs mem x) ->
file_at mem f fd P -> file_at mem' f fd P.
Proof.
intros mem mem' f fd P Hfr [Hs Hw].
assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= FILE_BLOCK -> val_mem segs mem (f + off) n v -> val_mem segs mem' (f + off) n v).
{ intros off n v H0 H1 Hv. eapply val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr. lia. }
assert (HFB : FILE_BLOCK = 1264) by reflexivity. assert (HBO : FILE_BUF_OFF = 240) by reflexivity. assert (HBS : FILE_BUFSIZ = 1024) by reflexivity.
split.
- unfold file_static in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat match goal with |- _ /\ _ => split end;
first [ assumption | lia | (apply HV; [lia | cbn; lia | assumption]) ].
- destruct Hw as [(HP & H1 & H2 & H3 & H4) | (H1 & H2 & H3 & H4 & HG & HL)]; [left | right].
+ split; [exact HP|]. repeat match goal with |- _ /\ _ => split end; (apply HV; [lia | cbn; lia | assumption]).
+ split; [apply HV; [lia | cbn; lia | assumption]|]. split; [apply HV; [lia | cbn; lia | assumption]|].
split; [apply HV; [lia | cbn; lia | assumption]|]. split; [apply HV; [lia | cbn; lia | assumption]|].
split; [|exact HL]. eapply garr8_frame; [exact HG|]. intros x Hx. apply Hfr. lia.
Qed.
Lemma sink_at_frame : forall (mem mem' : word -> option byte) md f S,
(forall a, f <= a < f + FILE_BLOCK \/ env_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
sink_at mem md f S -> sink_at mem' md f S.
Proof.
intros mem mem' md f S Hfr (fd & W & P & -> & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
exists fd, W, P. split; [reflexivity|]. split; [exact Hok|]. split; [exact Hmax|].
split; [apply (stdio_env_frame mem mem'); [intros a Ha; apply Hfr; right; exact Ha | exact Henv]|].
split; [apply (file_at_frame mem mem'); [intros a Ha; apply Hfr; left; exact Ha | exact Hfile]|].
split.
{ apply (val_mem_word_mem segs). apply (val_mem_word_mem segs) in Hhead.
eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. right. left. cbn in Hx. lia. }
split; [exact Hf0|]. split; [exact Hfs|]. split; [exact Hfd | exact Huniq].
Qed.
Lemma closed_stdio_env_frame : forall (mem mem' : word -> option byte),
(forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
closed_stdio_env mem -> closed_stdio_env mem'.
Proof.
intros mem mem' Hfr [Ht Hl]. split.
- eapply val_mem_frame; [|exact Ht]. intros x Hx. apply Hfr.
  unfold env_addr. right. left. cbn in Hx. lia.
- eapply val_mem_frame; [|exact Hl]. intros x Hx. apply Hfr.
  unfold env_addr. right. right. left. cbn in Hx. lia.
Qed.
Lemma sink_none_frame : forall (mem mem' : word -> option byte) md,
(forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a) ->
sink_none mem md -> sink_none mem' md.
Proof.
intros mem mem' md Hfr (Henv & Hhead & Hn).
split; [exact (closed_stdio_env_frame mem mem' Hfr Henv)|]. split; [|exact Hn].
apply (val_mem_word_mem segs). apply (val_mem_word_mem segs) in Hhead.
eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. left. cbn in Hx. lia.
Qed.
Lemma sink_at_env : forall mem md f S, sink_at mem md f S -> stdio_env mem.
Proof. intros mem md f S (fd & W & P & _ & _ & _ & H & _). exact H. Qed.
Lemma stdio_env_trailer : forall mem, stdio_env mem -> garr8 segs mem sk_trailer_addr sink_trailer_Z.
Proof. intros mem (_ & _ & _ & _ & Ht & _). exact (proj1 (proj1 (garr8_app _ _ _ _ _) Ht)). Qed.
Lemma sink_at_trailer : forall mem md f S, sink_at mem md f S -> garr8 segs mem sk_trailer_addr sink_trailer_Z.
Proof. intros mem md f S H. exact (stdio_env_trailer mem (sink_at_env mem md f S H)). Qed.
Lemma sink_at_nonnull : forall mem md f S, sink_at mem md f S -> f <> 0.
Proof. intros mem md f S (fd & W & P & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma sink_at_bytes_ok : forall mem md f S, sink_at mem md f S -> bytes_ok S.
Proof. intros mem md f S (fd & W & P & _ & H & _). exact H. Qed.
Lemma sink_at_max : forall mem md f S, sink_at mem md f S -> Z.of_nat (length S) <= SINK_MAX.
Proof. intros mem md f S (fd & W & P & _ & _ & H & _). exact H. Qed.
Lemma sink_kept : forall {SL : sink_laws} STK sp0 FP L A mem md L' A' mem' md' f S,
journal B MR STK sp0 FP L A mem md L' A' mem' md' ->
~ sink_open_fp FP -> In (f, FILE_BLOCK) (blocks L A) -> fp_avoids FP f (f + FILE_BLOCK) ->
sink_at mem md f S ->
sink_at mem' md' f S /\ In (f, FILE_BLOCK) (blocks L' A').
Proof.
intros SL STK sp0 FP L A mem md L' A' mem' md' f S HJ Hn Hin Hav (fd & W & P & -> & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
pose proof HJ as (HH & Hos & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
assert (HFB : FILE_BLOCK = 1264) by reflexivity.
assert (Hlive : In (f, FILE_BLOCK) (blocks L' A')).
{ destruct (in_dec zz_eq_dec (f, FILE_BLOCK) (blocks L' A')) as [H|H]; [exact H|]. exfalso.
apply (Hav (f + 0)); [lia|]. apply (Hgone f FILE_BLOCK 0 Hin H). lia. }
split; [|exact Hlive].
assert (Hfr : forall x, f <= x < f + FILE_BLOCK -> mbyte segs mem' x = mbyte segs mem x).
{ intros x Hx. replace x with (f + (x - f)) by lia. apply (Hblk f FILE_BLOCK (x - f) Hin Hlive); [lia|].
replace (f + (x - f)) with x by lia. apply Hav. exact Hx. }
assert (Himgb : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> mbyte segs mem' a = mbyte segs mem a).
{ intros a H1 H2 H3 H4. apply (Himg a H1 H2 H3 H4). intros [Ho _]. exact (Hn Ho). }
assert (Himge : forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a).
{ intros a Ha. destruct (skl_env a Ha) as (T1 & T2 & T3 & T4). exact (Himgb _ T1 T2 T3 T4). }
destruct (os_step_shielded FP md md' Hos Hn) as (Efd & Efs & _).
exists fd, W, P. split; [reflexivity|]. split; [exact Hok|]. split; [exact Hmax|].
split.
{ exact (stdio_env_frame mem mem' Himge Henv). }
split; [exact (file_at_frame mem mem' f fd P Hfr Hfile)|].
split.
{ apply (val_mem_word_mem segs). apply (val_mem_word_mem segs) in Hhead.
eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Himge. left. cbn in Hx. lia. }
split; [exact Hf0|]. rewrite Efd, Efs. split; [exact Hfs|]. split; [exact Hfd | exact Huniq].
Qed.
Lemma sink_none_kept : forall {SL : sink_laws} STK sp0 FP L A mem md L' A' mem' md',
journal B MR STK sp0 FP L A mem md L' A' mem' md' -> ~ sink_open_fp FP ->
sink_none mem md -> sink_none mem' md'.
Proof.
intros SL STK sp0 FP L A mem md L' A' mem' md' HJ Hn (Henv & Hhead & Hnone).
pose proof HJ as (HH & Hos & Hhigh & Hblk & Hgone & Hst & Herr & Himg).
assert (Himgb : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> mbyte segs mem' a = mbyte segs mem a).
{ intros a H1 H2 H3 H4. apply (Himg a H1 H2 H3 H4). intros [Ho _]. exact (Hn Ho). }
assert (Himge : forall a, env_addr a -> mbyte segs mem' a = mbyte segs mem a).
{ intros a Ha. destruct (skl_env a Ha) as (T1 & T2 & T3 & T4). exact (Himgb _ T1 T2 T3 T4). }
destruct (os_step_shielded FP md md' Hos Hn) as (Efd & _ & _).
split.
{ exact (closed_stdio_env_frame mem mem' Himge Henv). }
split.
{ apply (val_mem_word_mem segs). apply (val_mem_word_mem segs) in Hhead.
eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Himge. left. cbn in Hx. lia. }
rewrite Efd. exact Hnone.
Qed.
Lemma sink_fds_restored : forall FP mem md mem' md',
os_step FP md md' -> sink_none mem md -> sink_none mem' md' ->
forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd.
Proof.
intros FP mem md mem' md' Hos (_ & _ & Hn0) (_ & _ & Hn0') fd.
pose proof (fun fd e => fd_names_path_lookup (m_fds md) fd e Hn0) as Hn.
pose proof (fun fd e => fd_names_path_lookup (m_fds md') fd e Hn0') as Hn'.
destruct (os_step_fds FP md md' Hos fd) as [E | [[E1 | (o1 & E1)] [E2 | (o2 & E2)]]].
- exact E.
- rewrite E1, E2. reflexivity.
- exfalso. exact (Hn' fd _ E2 eq_refl).
- exfalso. exact (Hn fd _ E1 eq_refl).
- exfalso. exact (Hn fd _ E1 eq_refl).
Qed.
Section d.
Definition FOPEN_STK : Z := 512 + ALLOC_STACK.
Definition FWRITE_STK : Z := 512.
Definition FCLOSE_STK : Z := 512 + ALLOC_STACK.
Definition UNLINK_STK : Z := 64.
Definition fopen_spec (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md,
fn_pre B MR FOPEN_STK L A regs mem md -> st_init_done A = true ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 sk_path_addr -> getr regs 11 = Z_to_bv 64 sk_mode_addr ->
sink_none mem md ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FOPEN_STK (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ Permutation (blocks L' A') (blocks L A) /\ sink_none mem' md' /\ m_fds md' = m_fds md /\
(m_fs md' = m_fs md \/ m_fs md' = Fs.fs_set (m_fs md) sink_path [])) \/
(res <> 0 /\ Permutation (blocks L' A') ((res, FILE_BLOCK) :: blocks L A) /\ sink_at mem' md' res [] /\
m_fs md' = Fs.fs_set (m_fs md) sink_path []))).
Definition fwrite_spec (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md (src n f : Z) (S bs : list Z),
fn_pre B MR FWRITE_STK L A regs mem md ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 src -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 n -> getr regs 13 = Z_to_bv 64 f ->
In (f, FILE_BLOCK) (blocks L A) -> sink_at mem md f S ->
garr8 segs mem src bs -> n = Z.of_nat (length bs) -> 0 <= src -> src + n <= 2 ^ 47 ->
(src + n <= f \/ f + FILE_BLOCK <= src) ->
(src + n <= spZ regs - FWRITE_STK \/ spZ regs <= src) ->
Z.of_nat (length S) + n <= SINK_MAX ->
n <= 2 ^ 30 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FWRITE_STK (spZ regs) (sink_fp f) L A mem md L A mem' md' /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 n /\
sink_at mem' md' f (S ++ bs)).
Definition fclose_spec (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md (f : Z) (S : list Z) (rest : list (Z * Z)),
fn_pre B MR FCLOSE_STK L A regs mem md -> st_init_done A = true ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 f ->
Permutation (blocks L A) ((f, FILE_BLOCK) :: rest) -> sink_at mem md f S ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR FCLOSE_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 0 /\
Permutation (blocks L' A') rest /\
sink_none mem' md' /\ Fs.fs_lookup (m_fs md') sink_path = Some (bytes S)).
Definition unlink_spec (pc : Z) : Prop :=
forall L A (regs : bvmap 5 word) mem md,
fn_pre B MR UNLINK_STK L A regs mem md ->
getr regs 10 = Z_to_bv 64 sk_path_addr ->
sink_none mem md ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
journal B MR UNLINK_STK (spZ regs) [sink_token] L A mem md L A mem' md' /\
regs_preserved regs regs' /\
sink_none mem' md' /\ m_fds md' = m_fds md /\
(m_fs md' = m_fs md \/ m_fs md' = Fs.fs_remove (m_fs md) sink_path)).
End d.
End c.
