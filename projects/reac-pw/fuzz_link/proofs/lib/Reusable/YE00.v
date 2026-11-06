(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE00.v, with its module paths changed; asink_syms has the field ak_owned (the sink's own static cells), aenv_addr is those cells and the 8-byte ofl head, aenv_core names the four cells astdio_env reads and the frame lemmas frame over aenv_core, and astdio_env no longer states the path, mode, "rwa" and trailer strings: asink_strs states them, only for a harness that writes a file (astdio_env_trailer becomes asink_strs_trailer). *)
(* Modified by Theorem Labs, 2026-10: taken BY PATH from libreac/fuzz_grant's lib/Reusable/YE00.v at a working branch 4d244de18f0 (a Theorem Labs lane's release text of the shared sink form; also in a working branch c8e8b0fa5ec), module paths fuzz_grant -> fuzz_pcap only (porter a Theorem Labs lane): an internal statement change of fuzz_pcap's shared core. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP09 YI04 YI00 YI16 YK04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition FILE_BLOCK : Z := 1264.
Definition FILE_HDR : Z := 232.
Definition FILE_BUF_OFF : Z := 240.
Definition FILE_BUFSIZ : Z := 1024.
Definition SINK_MAX : Z := 2 ^ 62.
Definition U32M1 : Z := 4294967295.
Definition AMETA_BUCKETS : Z := 31051.
Definition AMETA_BUCKET : Z := 120.
Definition AMETA_SIZE : Z := 3727360.
Lemma AMETA_SIZE_ok : AMETA_BUCKETS * AMETA_BUCKET <= AMETA_SIZE /\ AMETA_SIZE mod 4096 = 0.
Proof. vm_compute. split; [discriminate | reflexivity]. Qed.
Definition sink_rwa_Z : list Z := [114; 119; 97].
Definition sink_trailer_Z : list Z := [59].
Definition bytes (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Lemma bytes_length : forall l, length (bytes l) = length l.
Proof. intros l. apply length_map. Qed.
Lemma bytes_app : forall l1 l2, bytes (l1 ++ l2) = bytes l1 ++ bytes l2.
Proof. intros. apply map_app. Qed.
Record asink_syms : Type := mkASink {
ak_read : Z; ak_write : Z; ak_seek : Z; ak_close : Z;
ak_path : Z;
ak_mode : Z;
ak_rwa : Z;
ak_trailer : Z;
ak_threaded : Z;
ak_need_locks : Z;
ak_ofl_lock : Z;
ak_meta_ptr : Z;
ak_meta_mem : Z;
ak_can_got : Z;
ak_canary : Z;
ak_icells : list (Z * Z);
ak_owned : list (Z * Z)
}.
Definition ak_ofl_head (K : asink_syms) : Z := ak_ofl_lock K + 8.
Definition asink_fp (f : Z) : list (Z * Z) := [(f, f + FILE_BLOCK); sink_token].
Lemma asink_fp_open : forall f, sink_open_fp (asink_fp f).
Proof. intros f. exists sink_token. split; [right; left; reflexivity | cbn; lia]. Qed.
Lemma in_asink_fp : forall f a, inFP (asink_fp f) a <-> (f <= a < f + FILE_BLOCK) \/ (0 <= a < 1).
Proof.
intros f a. split.
- intros (r & [<-|[<-|[]]] & H); cbn in H; [left | right]; exact H.
- intros [H|H]; [exists (f, f + FILE_BLOCK) | exists sink_token]; split; cbn; auto; lia.
Qed.
Definition os_kept (md md' : Model) : Prop :=
m_io md' = m_io md /\ m_pipes md' = m_pipes md /\
m_proc md' = mkProcState (procst_halted (m_proc md)) (procst_tid (m_proc md)) (procst_creds (m_proc md)) (procst_setsid_succeeded (m_proc md))
(procst_sigmask (m_proc md)) (procst_children (m_proc md)) (procst_utsname (m_proc md)) (procst_sigaltstack_installed (m_proc md))
(procst_killed (m_proc md)) (procst_sigabrt_pending (m_proc md)) (procst_abort_terminal (m_proc md)) (m_statpins md').
Lemma os_kept_refl : forall md, os_kept md md.
Proof. intros [fd vm io fs [h ti c ss sm ch u sa k sp at_ pins] li tm]. repeat split; reflexivity. Qed.
Lemma os_kept_trans : forall m1 m2 m3, os_kept m1 m2 -> os_kept m2 m3 -> os_kept m1 m3.
Proof.
intros m1 m2 m3 (A1 & A2 & A3) (B1 & B2 & B3). split; [rewrite B1; exact A1|]. split; [rewrite B2; exact A2|].
unfold m_statpins in *. rewrite B3. rewrite A3. reflexivity.
Qed.
Lemma os_kept_sbm : forall m m', same_but_materialized m m' -> os_kept m m'.
Proof.
intros m m' Hs. pose proof (same_but_materialized_frame m m' Hs) as (_ & _ & _ & Hio & _ & Hproc & _ & _ & _ & Hpipes & _).
split; [exact Hio|]. split; [exact Hpipes|]. unfold m_statpins. rewrite Hproc. destruct m as [fd vm io fs [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity.
Qed.
Lemma os_kept_with_fds : forall fds m, os_kept m (with_fds fds m).
Proof. intros fds [fd vm io fs [h ti c ss sm ch u sa k sp at_ pins] li tm]. repeat split; reflexivity. Qed.
Lemma os_kept_with_fs : forall fs' m, os_kept m (with_fs fs' m).
Proof. intros fs' m. rewrite with_fs_os_upd. destruct m as [fd vm io fs [h ti c ss sm ch u sa k sp at_ pins] li tm]. repeat split; reflexivity. Qed.
Section b.
Variable segs : list Segment.
Variable K : asink_syms.
Local Notation fld m f off n v := (val_mem segs m (f + off) n v).
Definition file_static (m : word -> option byte) (f fd : Z) : Prop :=
0 <= fd < 2 ^ 31 /\
fld m f 0 4 4   /\ fld m f 8 8 0   /\ fld m f 16 8 0   /\
fld m f 24 8 (ak_close K) /\ fld m f 48 8 0   /\
fld m f 64 8 (ak_read K) /\ fld m f 72 8 (ak_write K) /\ fld m f 80 8 (ak_seek K) /\
fld m f 88 8 (f + FILE_BUF_OFF)   /\ fld m f 96 8 FILE_BUFSIZ   /\
fld m f 104 8 0   /\ fld m f 112 8 0   /\
fld m f 120 4 fd /\ fld m f 124 4 0   /\ fld m f 128 8 0   /\
fld m f 140 4 U32M1   /\ fld m f 144 4 U32M1   /\
fld m f 152 8 0   /\ fld m f 160 8 0   /\ fld m f 168 8 0   /\
fld m f 176 8 0   /\ fld m f 184 8 0   /\ fld m f 192 8 0 /\ fld m f 200 8 0   /\
fld m f 208 8 0 /\ fld m f 216 8 0   /\ fld m f 224 8 0  .
Definition file_window (m : word -> option byte) (f : Z) (P : list Z) : Prop :=
(P = [] /\ fld m f 32 8 0   /\ fld m f 40 8 0   /\ fld m f 56 8 0   /\ fld m f 136 4 0  )
\/
(fld m f 32 8 (f + FILE_BUF_OFF + FILE_BUFSIZ) /\ fld m f 40 8 (f + FILE_BUF_OFF + Z.of_nat (length P)) /\
fld m f 56 8 (f + FILE_BUF_OFF) /\ fld m f 136 4 U32M1   /\
garr8 segs m (f + FILE_BUF_OFF) P /\ Z.of_nat (length P) <= FILE_BUFSIZ).
Definition file_at (m : word -> option byte) (f fd : Z) (P : list Z) : Prop :=
file_static m f fd /\ file_window m f P.
Definition astdio_env (m : word -> option byte) : Prop :=
val_mem segs m (ak_threaded K) 1 0 /\
val_mem segs m (ak_need_locks K) 1 0 /\
val_mem segs m (ak_ofl_lock K) 4 0 /\
(exists cval, 0 <= cval < 2 ^ 64 /\ val_mem segs m (ak_canary K) 8 cval).
Definition asink_strs (m : word -> option byte) : Prop :=
garr8 segs m (ak_path K) (sink_path_Z ++ [0]) /\
garr8 segs m (ak_mode K) (sink_mode_Z ++ [0]) /\
garr8 segs m (ak_rwa K) (sink_rwa_Z ++ [0]) /\
garr8 segs m (ak_trailer K) (sink_trailer_Z ++ [0]).
Definition ameta_ok (m : word -> option byte) (M : Z) : Prop :=
val_mem segs m (ak_meta_ptr K) 8 (ak_meta_mem K) /\
val_mem segs m (ak_meta_mem K) 8 M /\
0 <= M /\ M + AMETA_SIZE <= 2 ^ 47 /\ M mod 4096 = 0 /\
(forall a, M <= a < M + AMETA_SIZE -> mbyte segs m a = Some (Z_to_bv 8 0)).
Definition asink_at (m : word -> option byte) (md : Model) (f : Z) (S : list Z) : Prop :=
exists (fd : Z) (W P : list Z),
S = W ++ P /\ bytes_ok S /\ Z.of_nat (length S) <= SINK_MAX /\
astdio_env m /\ file_at m f fd P /\ val_mem segs m (ak_ofl_head K) 8 f /\ f <> 0 /\
Fs.fs_lookup (m_fs md) sink_path = Some (bytes W) /\
fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length W)))) /\
Namei.fd_names_path (fd_remove (m_fds md) (Z_to_bv 64 fd)) sink_path = false.
Definition asink_none (m : word -> option byte) (md : Model) : Prop :=
astdio_env m /\ val_mem segs m (ak_ofl_head K) 8 0 /\
Namei.fd_names_path (m_fds md) sink_path = false.
Definition asink_closed (md0 md : Model) (S : list Z) : Prop :=
m_fds md = m_fds md0 /\ m_fs md = Fs.fs_set (m_fs md0) sink_path (bytes S).
Definition asink_gone (md0 md : Model) : Prop :=
m_fds md = m_fds md0 /\ m_fs md = Fs.fs_remove (m_fs md0) sink_path.
Definition aenv_core (a : Z) : Prop :=
a = ak_threaded K \/ a = ak_need_locks K \/ (ak_ofl_lock K <= a < ak_ofl_lock K + 4) \/
(ak_canary K <= a < ak_canary K + 8).
Definition aenv_addr (a : Z) : Prop :=
Exists (YG0n.in_zr a) (ak_owned K) \/ (ak_ofl_head K <= a < ak_ofl_head K + 8).
Definition astrs_addr (a : Z) : Prop :=
(ak_path K <= a < ak_path K + 13) \/ (ak_mode K <= a < ak_mode K + 3) \/ (ak_rwa K <= a < ak_rwa K + 4) \/
(ak_trailer K <= a < ak_trailer K + 2).
Lemma val_mem_frame : forall (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.
Lemma astdio_env_frame : forall (m m' : word -> option byte),
(forall a, aenv_core a -> mbyte segs m' a = mbyte segs m a) -> astdio_env m -> astdio_env m'.
Proof.
intros m m' Hfr (H1 & H2 & H3 & (cv & Hcv & H8)). unfold astdio_env.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H3]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
exists cv. split; [exact Hcv|]. eapply val_mem_frame; [|exact H8]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia.
Qed.
Lemma asink_strs_frame : forall (m m' : word -> option byte),
(forall a, astrs_addr a -> mbyte segs m' a = mbyte segs m a) -> asink_strs m -> asink_strs m'.
Proof.
intros m m' Hfr (H4 & H5 & H6 & H7). unfold asink_strs.
split; [eapply garr8_frame; [exact H4|]; intros x Hx; apply Hfr; unfold astrs_addr; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H5|]; intros x Hx; apply Hfr; unfold astrs_addr; cbn in Hx; lia|].
split; [eapply garr8_frame; [exact H6|]; intros x Hx; apply Hfr; unfold astrs_addr; cbn in Hx; lia|].
eapply garr8_frame; [exact H7|]; intros x Hx; apply Hfr; unfold astrs_addr; cbn in Hx; lia.
Qed.
Lemma file_at_frame : forall (m m' : word -> option byte) f fd P,
(forall x, f <= x < f + FILE_BLOCK -> mbyte segs m' x = mbyte segs m x) ->
file_at m f fd P -> file_at m' f fd P.
Proof.
intros m m' f fd P Hfr [Hs Hw].
assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= FILE_BLOCK -> val_mem segs m (f + off) n v -> val_mem segs m' (f + off) n v).
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
Lemma asink_at_frame : forall (m m' : word -> option byte) md f S,
(forall a, f <= a < f + FILE_BLOCK \/ aenv_core a \/ (ak_ofl_head K <= a < ak_ofl_head K + 8) -> mbyte segs m' a = mbyte segs m a) ->
asink_at m md f S -> asink_at m' md f S.
Proof.
intros m m' md f S Hfr (fd & W & P & -> & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
exists fd, W, P. split; [reflexivity|]. split; [exact Hok|]. split; [exact Hmax|].
split; [apply (astdio_env_frame m m'); [intros a Ha; apply Hfr; right; left; exact Ha | exact Henv]|].
split; [apply (file_at_frame m m'); [intros a Ha; apply Hfr; left; exact Ha | exact Hfile]|].
split.
{ eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. right. right. unfold ak_ofl_head in *. cbn in Hx. lia. }
split; [exact Hf0|]. split; [exact Hfs|]. split; [exact Hfd | exact Huniq].
Qed.
Lemma asink_none_frame : forall (m m' : word -> option byte) md,
(forall a, aenv_core a \/ (ak_ofl_head K <= a < ak_ofl_head K + 8) -> mbyte segs m' a = mbyte segs m a) -> asink_none m md -> asink_none m' md.
Proof.
intros m m' md Hfr (Henv & Hhead & Hn). split; [exact (astdio_env_frame m m' (fun a Ha => Hfr a (or_introl Ha)) Henv)|]. split; [|exact Hn].
eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. right. unfold ak_ofl_head in *. cbn in Hx. lia.
Qed.
Lemma asink_at_model : forall m md md' f S,
m_fs md' = m_fs md -> m_fds md' = m_fds md -> asink_at m md f S -> asink_at m md' f S.
Proof.
intros m md md' f S Efs Efd (fd & W & P & HS & Hok & Hmax & Henv & Hfile & Hhead & Hf0 & Hfs & Hfd & Huniq).
exists fd, W, P. rewrite Efs, Efd. repeat (split; [assumption|]). exact Huniq.
Qed.
Lemma ameta_ok_frame : forall (m m' : word -> option byte) M,
(forall a, (ak_meta_ptr K <= a < ak_meta_ptr K + 8) \/ (ak_meta_mem K <= a < ak_meta_mem K + 8) \/ (M <= a < M + AMETA_SIZE) ->
mbyte segs m' a = mbyte segs m a) ->
ameta_ok m M -> ameta_ok m' M.
Proof.
intros m m' M Hfr (H1 & H2 & H3 & H4 & H5 & HZ). unfold ameta_ok.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; cbn in Hx; lia|].
split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
intros a Ha. rewrite Hfr by lia. exact (HZ a Ha).
Qed.
Lemma asink_at_env : forall m md f S, asink_at m md f S -> astdio_env m.
Proof. intros m md f S (fd & W & P & _ & _ & _ & H & _). exact H. Qed.
Lemma asink_at_nonnull : forall m md f S, asink_at m md f S -> f <> 0.
Proof. intros m md f S (fd & W & P & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma asink_at_bytes_ok : forall m md f S, asink_at m md f S -> bytes_ok S.
Proof. intros m md f S (fd & W & P & _ & H & _). exact H. Qed.
Lemma asink_at_max : forall m md f S, asink_at m md f S -> Z.of_nat (length S) <= SINK_MAX.
Proof. intros m md f S (fd & W & P & _ & _ & H & _). exact H. Qed.
Lemma asink_strs_trailer : forall m, asink_strs m -> garr8 segs m (ak_trailer K) sink_trailer_Z.
Proof. intros m (_ & _ & _ & Ht). exact (proj1 (proj1 (garr8_app _ _ _ _ _) Ht)). Qed.
Lemma astdio_env_canary : forall m, astdio_env m -> exists cval, 0 <= cval < 2 ^ 64 /\ val_mem segs m (ak_canary K) 8 cval.
Proof. intros m (_ & _ & _ & Hc). exact Hc. Qed.
End b.
