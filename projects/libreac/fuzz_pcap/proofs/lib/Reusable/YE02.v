(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE02.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00 YI16 YI17.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section X.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asink_syms.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Lemma SRr_srz : forall (W : world segs) (c : config) (R : world segs -> config -> Prop) (T : TSet),
SRr segs W c R -> AI segs (w_H W) (w_A W) (cfg_model c) ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> R W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Proof. intros W c R T HS HAI HK. exact (HS HAI T HK). Qed.
Definition aunlink_postA (STK : Z) (W : world segs) ly S regs mem md : world segs -> config -> Prop :=
fun W' c' => exists regs' mem' md' (e : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 (2 ^ 64 - 1) /\
asink_none segs K (rd W' mem') md' /\ m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
1 <= e <= 4095 /\ val_mem segs (rd W' mem') (as_errno B) 4 e.
Definition aunlink_postB (STK : Z) (W : world segs) ly S regs mem md : world segs -> config -> Prop :=
fun W' c' => exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly S W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
asink_none segs K (rd W' mem') md' /\ m_fds md' = m_fds md /\
m_fs md' = Fs.fs_remove (m_fs md) sink_path /\ Fs.fs_lookup (m_fs md) sink_path <> None.
Definition aunlink_x (pc : Z) : Prop :=
forall W ly S regs mem md ch (TA TB : TSet),
AI segs (w_H W) (w_A W) md ->
afn_pre segs B AUNLINK_STK ly S W regs mem md ch ->
getr regs 10 = w64 (ak_path K) ->
asink_none segs K (rd W mem) md ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> aunlink_postA AUNLINK_STK W ly S regs mem md W' c' -> srealizes segs c' TA) ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> aunlink_postB AUNLINK_STK W ly S regs mem md W' c' -> srealizes segs c' TB) ->
srealizes segs (cfg_at segs pc regs mem md) (unlink_shape (m_fs md) TA TB).
Definition afopen_postA (STK : Z) (W : world segs) ly S regs mem md : world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' (e : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\ frames S' = frames S /\
ablocks B ly' S' = ablocks B ly S /\ asink_none segs K (rd W' mem') md' /\
m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
1 <= e <= 4095 /\ val_mem segs (rd W' mem') (as_errno B) 4 e.
Definition afopen_postB (STK : Z) (W : world segs) ly S regs mem md : world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal STK (spZ regs) [YI16.sink_token] ly S W mem md [] ly' S' W' mem' md' 1 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 res /\ frames S' = frames S /\
4096 <= res /\ ablocks B ly' S' = ablocks B ly S ++ [(res, FILE_BLOCK)] /\
asink_at segs K (rd W' mem') md' res [] /\ Fs.fs_lookup (m_fs md') sink_path = Some [] /\
m_fs md' = Fs.fs_set (m_fs md) sink_path [].
Definition afopen_x (pc ra rlo rhi : Z) : Prop :=
forall W ly S regs mem md ch (M : Z) (TA TB : TSet),
AI segs (w_H W) (w_A W) md ->
afn_pre segs B AFOPEN_STK ly S W regs mem md ch ->
getr regs 10 = w64 (ak_path K) -> getr regs 11 = w64 (ak_mode K) ->
asink_none segs K (rd W mem) md ->
ameta_inv segs K ly (rd W mem) M -> arodata_okS segs B rlo rhi (aview segs (w_H W) mem) ->
st_nev S + 1 <= EV_MAX -> blocks_bytes S + FILE_BLOCK <= LIVE_MAX ->
In [pc_malloc_ra0 (as_code B); ra] (as_universe B) ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> afopen_postA AFOPEN_STK W ly S regs mem md W' c' -> srealizes segs c' TA) ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> afopen_postB AFOPEN_STK W ly S regs mem md W' c' -> srealizes segs c' TB) ->
srealizes segs (cfg_at segs pc regs mem md) (openat_shape (m_fs md) TA TB).
End X.
End a.
