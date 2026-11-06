(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Uaccess.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZsi.
Import ListNotations.
Open Scope Z_scope.

Section Sys.
Context {fF : FPF} {fC : FPC}.
Variable segs : list Segment.
Variable J : aj_base segs.

Definition iovec_bytes (iovs : list (word * word)) : list byte := flat_map (fun p => QZDE.le8 (fst p) ++ QZDE.le8 (snd p)) iovs.

Definition open_pre (regs : bvmap 5 word) (mem : word -> option byte) (path : list byte) : Prop :=
getr regs 17 = Z_to_bv 64 56 /\ getr regs 10 = Z_to_bv 64 (-100) /\
Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0 /\
~ In (Z_to_bv 8 0) path /\ path_has_slash path = false /\ path_eqb path dotdot_path = false /\
QZDE.bytes_at segs mem (bv_unsigned (getr regs 11)) (path ++ [Z_to_bv 8 0]).

Definition same_io (c c' : config) : Prop :=
m_fds (cfg_model c') = m_fds (cfg_model c) /\ m_fs (cfg_model c') = m_fs (cfg_model c).

Record aj_sys : Prop := AJSYS {
ajs_close : forall regs (pc : word) mem rom c fd e T,
CK J c -> getr regs 17 = Z_to_bv 64 57 -> getr regs 10 = Z_to_bv 64 fd -> 3 <= fd < 2^32 ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some e ->
(forall c', CNEXT J c c' ->
m_fds (cfg_model c') = fd_remove (m_fds (cfg_model c)) (Z_to_bv 64 fd) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J T c' (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)) ->
AJ J T c (epend regs pc mem rom (getr regs 17));

ajs_ioctl_winsz : forall regs (pc : word) mem rom c fd T,
CK J c -> getr regs 17 = Z_to_bv 64 29 -> getr regs 10 = Z_to_bv 64 fd -> 0 <= fd <= 2 ->
getr regs 11 = Z_to_bv 64 21523 ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom)) ->
AJ J T c (epend regs pc mem rom (getr regs 17));

ajs_read_file : forall regs (pc : word) mem rom c fd buf cnt p off data T,
CK J c -> getr regs 17 = Z_to_bv 64 63 -> getr regs 10 = Z_to_bv 64 fd -> 3 <= fd < 2^32 ->
getr regs 11 = Z_to_bv 64 buf -> getr regs 12 = Z_to_bv 64 cnt ->
1 <= cnt <= 16777216 -> buf + cnt <= TASK_SIZE -> QZDE.wr_at segs mem buf cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
let bs := file_read data off (Z_to_bv 64 cnt) in
(forall c', CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J T c' (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
(mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])))) ->
AJ J T c (epend regs pc mem rom (getr regs 17));

ajs_read_dir : forall regs (pc : word) mem rom c fd buf cnt T,
CK J c -> getr regs 17 = Z_to_bv 64 63 -> getr regs 10 = Z_to_bv 64 fd -> 3 <= fd < 2^32 ->
getr regs 11 = Z_to_bv 64 buf -> getr regs 12 = Z_to_bv 64 cnt ->
1 <= cnt <= 16777216 -> buf + cnt <= TASK_SIZE -> QZDE.wr_at segs mem buf cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some FdDir ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom)) ->
AJ J T c (epend regs pc mem rom (getr regs 17));

ajs_open_toolong : forall regs (pc : word) mem c path T,
CK J c -> open_pre regs mem path -> (path_max <= length path)%nat ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J T c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_open_empty : forall regs (pc : word) mem c T,
CK J c -> open_pre regs mem [] ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J T c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_open_absent : forall regs (pc : word) mem c path T,
CK J c -> open_pre regs mem path -> (length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = None ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J T c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_open_file : forall regs (pc : word) mem c path d TA TB,
CK J c -> open_pre regs mem path -> (length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = Some d ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXT J c c' -> same_io c c' ->
AJ J TA c' (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))) ->
(forall c', CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) (FdFile path (Z_to_bv 64 0)) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J TB c' (mkst (regupd regs 10 (alloc_fd (m_fds (cfg_model c)))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt2 TA TB) c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_open_dot : forall regs (pc : word) mem c TA TB,
CK J c -> open_pre regs mem dot_path ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXT J c c' -> same_io c c' ->
AJ J TA c' (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs))) ->
(forall c', CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) FdDir ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J TB c' (mkst (regupd regs 10 (alloc_fd (m_fds (cfg_model c)))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt2 TA TB) c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_writev : forall regs (pc : word) mem c (fd : Z) iovs bufs (T : nat -> TSet),
CK J c -> getr regs 17 = Z_to_bv 64 66 -> (fd = 1 \/ fd = 2) -> getr regs 10 = Z_to_bv 64 fd ->
getr regs 12 = Z_to_bv 64 (Z.of_nat (length bufs)) -> (1 <= length bufs <= 1024)%nat ->
Z.of_nat (length (concat bufs)) <= 67108864 ->
QZDE.bytes_at segs mem (bv_unsigned (getr regs 11)) (iovec_bytes iovs) ->
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ QZDE.bytes_at segs mem (bv_unsigned (fst iov)) bs) iovs bufs ->
bv_unsigned (getr regs 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE ->
Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= TASK_SIZE) iovs ->
(1 <= length (concat bufs))%nat ->
(forall (k : nat) c', (1 <= k)%nat -> (k <= length (concat bufs))%nat -> CNEXT J c c' -> same_io c c' ->
AJ J (T k) c' (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J (t_alt (fun i : wr_index (concat bufs) =>
t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (concat bufs))) (T (proj1_sig i))))
c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_writev0 : forall regs (pc : word) mem c (fd : Z) iovs bufs T,
CK J c -> getr regs 17 = Z_to_bv 64 66 -> (fd = 1 \/ fd = 2) -> getr regs 10 = Z_to_bv 64 fd ->
getr regs 12 = Z_to_bv 64 (Z.of_nat (length bufs)) -> (1 <= length bufs <= 1024)%nat ->
concat bufs = [] ->
QZDE.bytes_at segs mem (bv_unsigned (getr regs 11)) (iovec_bytes iovs) ->
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ QZDE.bytes_at segs mem (bv_unsigned (fst iov)) bs) iovs bufs ->
bv_unsigned (getr regs 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE ->
Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= TASK_SIZE) iovs ->
(forall c', CNEXT J c c' -> same_io c c' ->
AJ J T c' (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))) ->
AJ J T c (epend regs pc mem (seg_rom segs) (getr regs 17));

ajs_exit : forall regs (pc : word) mem rom c code,
CK J c -> (getr regs 17 = Z_to_bv 64 93 \/ getr regs 17 = Z_to_bv 64 94) -> getr regs 10 = Z_to_bv 64 code ->
AJ J (t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs (cfg_model c))) c (epend regs pc mem rom (getr regs 17))
}.

Lemma aj_ecall : forall regs (pc : word) mem rom w c T,
fetch_word segs pc = Some w -> is_ecall w = true ->
AJ J T c (epend regs pc mem rom (getr regs 17)) ->
AJ J T c (mkst regs pc mem rom).
Proof.
intros regs pc mem rom w c T HF HE K. apply (aj_evt J).
eapply QbrW.evt_step; [| apply QbrW.evt_done; exact K].
split; [reflexivity | exact (step_ecall_epend segs regs pc mem rom w HF HE)].
Qed.

Lemma ajs_read_file_w : aj_sys -> forall regs (pc : word) mem rom c fd buf cnt p off data T,
CK J c -> getr regs 17 = Z_to_bv 64 63 -> getr regs 10 = Z_to_bv 64 fd -> 3 <= fd < 2^32 ->
getr regs 11 = Z_to_bv 64 buf -> getr regs 12 = Z_to_bv 64 cnt ->
1 <= cnt <= 16777216 -> buf + cnt <= TASK_SIZE -> QZDE.wr_at segs mem buf cnt ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
let bs := file_read data off (Z_to_bv 64 cnt) in
(forall c', CNEXT J c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJ J T c' (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (Qnhz.Mq0.wbytes mem (Z_to_bv 64 buf) bs) rom)) ->
AJ J T c (epend regs pc mem rom (getr regs 17)).
Proof.
intros SYS regs pc mem rom c fd buf cnt p off data T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk Hfs bs HK.
apply (ajs_read_file SYS regs pc mem rom c fd buf cnt p off data T HCK H17 H10 Hfd H11 H12 Hcnt Htop Hwr Hlk Hfs).
intros c' HN F S. fold bs.
replace (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])))
with (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (Qnhz.Mq0.wbytes mem (Z_to_bv 64 buf) bs) rom); [exact (HK c' HN F S)|].
destruct bs as [|b bsr]; cbn [delivered_writes].
- rewrite QSpR.Mq2.adv_ret_epend. reflexivity.
- rewrite QSpR.Mq2.adv_write1_epend. reflexivity.
Qed.
End Sys.
