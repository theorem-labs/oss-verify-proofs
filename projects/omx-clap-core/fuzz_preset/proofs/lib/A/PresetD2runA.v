(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from the post-read driver leaves of proofs/cgif/cgif_file_fuzzer/lib/A
   (relocated here as lib/A): AD2d.v:388 tfib_run_Q (RUNQ) with its consumer type run_QM_tfa (AD2d.v:74), AD2c.v:159
   tfib_post_P (POSTP), AD2g.v:235 tfib_hdr (HDR), AD22.v:45 tfib_rd0_dir (RDD), AD1z.v:479 tfib_rd0_file (RDF),
   AD26.v:320 tfib_file_arm (HFILE) and AD26.v:326 tfib_dir_arm (HDIR); their B twins are lib/YD2d.v :385, YD2c.v :157,
   YD2g.v :233, YD22.v :46, YD1z.v :480, YD26.v :316 / :322. For fuzz_preset's asan image; lib/AU/PresetD2runB.v is
   the asan-ubsan twin (lane CwRunqB). STATEMENTS only: the proofs are lib/A/PresetD2runAPf.v. Nothing in this file
   is a proof of a function (rule 24: the composition / driver layer of a port).
   Changes from the donor, the same in every item (closedwalk-plan.md 1e, 2b, 2f; h-pre-b1's design of 2026-10-28
   22:44Z and its rulings of 23:2xZ):
   (1) cgif's AR is a8's ARcf at the ghost head set Hp = [] (lib/Reusable/YG0ncf.v); the switch from AR is at the
       allocator's initial state (ARcf_nil_init, YGcfNilInit.v), so these leaves convert nothing. The laws are a8's
       AR_laws_cf, proved (AR_laws_ok_cf, YG0lawscf.v), so no leaf takes them as a premise; cgif's model_laws goes
       too (the driver's mallocs use a8's malloc_cf_apath_success, YGcfApath.v).
   (2) cgif's event bounds (`st_nev S <= 1`, `st_nev S <= 64`) are DROPPED: the cf instance has no event cap, and
       a8's malloc_post_cf (YG07cf.v:255) bounds st_nev from below only. In their place each state carries the
       allocator room for the driver's remaining allocator calls, ROOM_cf_k k S: k = 11 after the first malloc
       (at most 10 grows of the read buffer, then the payload copy), k = 1 at the header (the payload copy).
       The arms at the initial state take ROOM_cf_k 12 init_state as a premise of their result.
   (3) cgif's drv_minv (AD1v.v:161) loses prim_pristine_except and quar_bytes, which no cf law speaks of and no cf
       consumer needs: drv_minv_cf. The donor's file-arm facts prim_pristine_except S [] / quar_bytes S = 0 go.
   (4) cgif's FINV is the program interface's PINV (lib/A/PresetCfnA.v:150) at the start-up ledger (0 0): no harness
       call has run before these leaves.
   (5) NEW premise NR inp (the agreement's no-refusal premise, closedwalk-plan.md 2f), right after valid_fs, on the
       file path (HFILE -> RDF -> HDR -> POSTP -> RUNQ -> RUNQM); the directory path makes no harness call.
   (6) tail_at is lane CwSites' tail_at_pinv_A (the donor's AD1w.v:42 with (1)-(4)).
   Dropped from the donor (preset's driver writes no file): every obligation on cgif's output file; this file names
   none of A_WB, A_TRAILER, A_PATH, astdio_env, FINV.
   Section 1 holds other lanes' statements, PROVISIONAL until their shas land (each marked with its owner).
   Section 2 is this lane's: the leaf types <donor predicate>_cf. Section 3: the results tfib_<x>_cf_A, closed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD2runA.v, with its module paths changed; 77 of its 205 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from the post-read driver leaves of proofs/cgif/cgif_file_fuzzer/lib/A
   (relocated here as lib/A): AD2d.v:388 tfib_run_Q (RUNQ), AD2c.v:159 tfib_post_P (POSTP), AD2g.v:235 tfib_hdr (HDR),
   AD22.v:45 tfib_rd0_dir (RDD), AD1z.v:479 tfib_rd0_file (RDF), AD26.v:320 tfib_file_arm (HFILE) and AD26.v:326
   tfib_dir_arm (HDIR); their B twins are lib/YD2d.v :385, YD2c.v :157, YD2g.v :233, YD22.v :46, YD1z.v :480,
   YD26.v :316 / :322. For fuzz_preset's asan image; lib/AU/PresetD2runB.v is the asan-ubsan twin (lane CwRunqB).
   STATEMENTS only: the proofs are lib/A/PresetD2runAPf{Q,H,M}.v. The closed RUNQ result tfib_run_Q_cf_A, whose
   premises are lane CwLoopA's loop and lane CwRunqm's RUNQM, is in lib/A/PresetD2runQA.v, so this file does not
   depend on those two files. Nothing in this file is a proof of a function (rule 24: the composition / driver
   layer of a port).
   Changes from the donor, the same in every item (the internal file closedwalk-plan.md 1e, 2b, 2f; a Theorem Labs lane's design of 2026-10-28
   22:44Z and its rulings of 23:2xZ):
   (1) cgif's AR is a8's ARcf at the ghost head set Hp = [] (lib/Reusable/YG0ncf.v); the switch from AR is at the
       allocator's initial state (ARcf_nil_init, YGcfNilInit.v), so these leaves convert nothing. The laws are a8's
       AR_laws_cf, proved (AR_laws_ok_cf, YG0lawscf.v), so no leaf takes them as a premise; cgif's model_laws goes
       too (the driver's mallocs use a8's malloc_cf_apath_success, YGcfApath.v).
   (2) cgif's event bounds (`st_nev S <= 1`, `st_nev S <= 64`) are DROPPED: the cf instance has no event cap, and
       a8's malloc_post_cf (YG07cf.v:255) bounds st_nev from below only. In their place each state of the read and
       header leaves carries the allocator's NON-PRIMARY room as a state predicate, `iface_room_np S` (a Theorem Labs lane's
       decision of 2026-10-29 ~04:55Z on the driver-leaf room; resume brief 03:48Z, design change 1): the run-level
       `ROOM_cf_k init_state (4 * N_LLVMF + 24)` and every headroom number are DELETED (unsatisfiable,
       port/n-llvmf.md). iface_room_np is the program interface's Section Variable (lib/A/PresetCfnA.v, lane
       IfacePort; PROVISIONAL, owner a Theorem Labs lane with its room_live_cf), quantified here under that name. A site gets
       its one-call room from IfacePort's iface_room_np_tail; after a driver malloc / free the state keeps
       iface_room_np by a8's two PROVISIONAL laws, the interface's PCA.iface_room_np_init / PCA.iface_room_np_step
       (lib/A/PresetCfnA.v section 3b). The driver leaves carry NO P8 conjunct: before the first harness call the
       interface's iface_room_at (os = []) follows from length (blocks S) <= 3, qtight S and Wf_cf alone, and lane
       CwRunqm derives it at the loop entry. N_LLVMF is gone from this file.
   (3) cgif's drv_minv (AD1v.v:161) loses prim_pristine_except and quar_bytes, which no cf law speaks of and no cf
       consumer needs: drv_minv_cf. The donor's file-arm facts prim_pristine_except S [] / quar_bytes S = 0 go.
   (4) cgif's FINV is the program interface's PINV (lib/A/PresetCfnA.v:150) at the start-up ledger (0 0): no harness
       call has run before these leaves.
   (5) NEW premise NR inp (the agreement's no-refusal premise, the internal file closedwalk-plan.md 2f), right after valid_fs, on the
       file path (HFILE -> RDF -> HDR -> POSTP -> RUNQ -> RUNQM); the directory path makes no harness call.
   (6) tail_at is lane CwSites' tail_at_pinv_A (the donor's AD1w.v:42 with (1)-(4)).
   (7) NEW, memnorm (lane MnPrefix, a Theorem Labs lane, 2026-10-29): `YAkMemnorm.memnorm tfibsegs (ms_mem ms)` of the full
       overlay is a premise of file_arm_tfa_cf, rd0_file_tfa_cf and hdr_tfa_cf (after PINV), and the last conjunct of
       tail_at_pinv_A (so post_P / run_Q / run_QM carry it), so the at-main seed reaches the loop head. The read loop
       keeps it across its read check by read_check_tfa_cf's memnorm keep (lib/A/PresetD1preA.v; OPEN: its realizer
       aread_check_stmt_cf has no keep yet).
   Dropped from the donor (preset's driver writes no file): every obligation on cgif's output file; this file names
   none of A_WB, A_TRAILER, A_PATH, astdio_env, FINV.
   Section 1 names the other owners' statements this file cites (none is copied). Section 2 is this lane's: the leaf
   types <donor predicate>_cf. Section 3: the results tfib_<x>_cf_A, closed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1v AD2h AD2f AD1w ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfRoomPre YGcfTok YG07cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvSecsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
(* Owners' statements, cited, none copied: lane CwSites' drv_pre_cf / drv_minv_cf / tail_at_pinv_A / free_site_cf
   (lib/A/PresetD1sitesA.v, a working branch 869d1b83d936, Section order B, NP) and lane CwPreA's
   leaf types malloc_site_tfa_cf (B NP), read_check_tfa_cf, memcpy_site_tfa_cf, rderr_leaf_tfa_cf,
   refused_leaf_tfa_cf (B), short_leaf_tfa_cf / overrun_leaf_tfa_cf (B NP) (lib/A/PresetD1preA.v,
   a working branch cc057e7d0f22). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1preA.
(* Required, not imported: PresetCfnA defines A_LLVMF / A_EMPTY / LIVE_LIB / LLVMF_STK at preset's values, which would
   shadow the driver's names; its names are written qualified. *)
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s.
(* Every class argument is a Context variable and is passed by name where the tree has #[global] instances of its
   class (run_shape's / POSTX's / RPX's / CLOSEDX_loaded's LS). *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
(* The program interface's non-primary room (lib/A/PresetCfnA.v Section Variable iface_room_np, lane IfacePort;
   PROVISIONAL, owner a Theorem Labs lane): the state predicate every read / header leaf state carries (header change (2)). *)
Variable iface_room_np : astate -> Prop.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).

(* ---------------------------------------------------------------------- *)
(* 1. Other owners' statements: none copied. The non-primary room's laws are the interface's
      PCA.iface_room_np_init / PCA.iface_room_np_step (lib/A/PresetCfnA.v section 3b, lane IfacePort,
      a working branch 3f83c075b61f; PROVISIONAL premises until a Theorem Labs lane's
      lib/A/CfRoomLivePreset.v gives them bodies), cited by name.                                          *)

Variable NR : ProcInput -> Prop.
(* ---------------------------------------------------------------------- *)
(* 2. This lane's leaf types: <donor predicate>_cf.                        *)

(* AD1w.v:172 run_Q_tfa. *)
Definition run_Q_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
let E3 := E_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at_pinv_A B iface_room_np (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
(* #102 (lane StackDrv): the live real stack above the entry sp, carried from main to the loop head *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).

(* AD1w.v:66 post_P_tfa. *)
Definition post_P_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
tail_at_pinv_A B iface_room_np S_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
(* #102 (lane StackDrv): the live real stack above the entry sp *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).

(* AD1v.v:340 hdr_tfa. *)
Definition hdr_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> iface_room_np S ->
xs_placed_cf ly S -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_LEN) = dlen data -> 65536 <= cap <= 2 ^ 26 ->
drv_minv_cf B S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* #102 (lane StackDrv): the live real stack above the entry sp *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (POSTX (LS := LS) data (in_fs inp)).

(* AD1v.v:244 rd0_file_tfa. *)
Definition rd0_file_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> iface_room_np S ->
xs_placed_cf ly S -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) ->
frames S = [] -> qtight S -> prim_pristine_except S [kBatchClass] ->
(* the depot holds fixed traces only (the first malloc's, from the start state's empty depot) *)
drv_depot_fixed B S ->
(* COUNT meter row A18 (lane CountDrvA): the driver's own secondary entries at buffer size 65536, the first malloc's
   (lib/A/PresetDrvSecsA.v drv_secs_first); the read loop keeps it to the tail in drv_minv_cf *)
PresetDrvSecsA.drv_secs_cf S 65536 ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* #102 (lane StackDrv): the live real stack above the entry sp *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (RPX (LS := LS) data (in_fs inp) READ_FUEL CAP0).

(* AD1v.v:257 rd0_dir_tfa. *)
Definition rd0_dir_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p : list byte) (pb : sptr),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (havoc (ELV sp a0 p inp xw xd) K_M1 ws) ss_rd0 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> iface_room_np S ->
xs_placed_cf ly S -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, 65536)] -> qtight S -> sptr_addr B ly pb = bv_unsigned (ew (havoc (ELV sp a0 p inp xw xd) K_M1 ws) A_BUF) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_read_error p) (in_fs inp)).

(* AD1v.v:131 file_arm_tfa. *)
Definition file_arm_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p data : list byte),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
(length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs (ELV sp a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* #102 (lane StackDrv): the live real stack above the entry sp *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded (LS := LS) data (in_fs inp)).

(* AD1v.v:142 dir_arm_tfa. *)
Definition dir_arm_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> entry_stack_fits sp [a0; p] (in_envp inp) -> p = dot_path ->
st_ok tfibsegs (ELV sp a0 p inp xw xd) ss_m1 (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md ->
top_ok (bv_unsigned sp) ly -> PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
(* TEMPORARY (removed when the call contracts drop memnorm): memnorm of the full overlay, for the
   first malloc's drv_pre_cf (lib/A/PresetD1sitesA.v), as file_arm_tfa_cf takes it *)
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
End s.

(* ---------------------------------------------------------------------- *)
(* 3. The results, closed: every class argument, the interface's non-primary room iface_room_np and every leaf
      universally quantified. Each is proved in a PresetD2runAPf*.v file as <name>_holds. The leaves are the donor's
      Section hypotheses (AD1p.v:50-83) at their _cf types; AR_laws / model_laws are a8's, not premises (change (1)
      of the header). tfib_run_Q_cf_A is in lib/A/PresetD2runQA.v. *)

(* AD2c.v:159 tfib_post_P. *)
Definition tfib_post_P_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop),
TfibSyms B ->
run_Q_tfa_cf (LS := LS) B iface_room_np NR -> post_P_tfa_cf (LS := LS) B iface_room_np NR.

(* AD2g.v:235 tfib_hdr. *)
Definition tfib_hdr_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop),
TfibSyms B ->
short_leaf_tfa_cf B iface_room_np -> overrun_leaf_tfa_cf B iface_room_np ->
post_P_tfa_cf (LS := LS) B iface_room_np NR ->
hdr_tfa_cf (LS := LS) B iface_room_np NR.

(* AD22.v:45 tfib_rd0_dir. *)
Definition tfib_rd0_dir_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop),
TfibSyms B ->
rderr_leaf_tfa_cf B -> rd0_dir_tfa_cf B iface_room_np.

(* AD1z.v:479 tfib_rd0_file. The read loop's grow arm makes a malloc and then frees the old buffer, so the
   non-primary room after the malloc comes from the interface's PCA.iface_room_np_step, the grow's one-call room
   from PCA.iface_room_np_tail, and the grown request (at most 2 ^ 26) needs 2 ^ 26 < cf_malloc_max (a computation
   at CfParams_preset); all three as CwPinvA's gr_grow_cf_A takes them (found by WalkMain). *)
Definition tfib_rd0_file_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop),
TfibSyms B -> PCA.iface_room_np_step (cp := cp) iface_room_np ->
PCA.iface_room_np_tail (cp := cp) iface_room_np -> 2 ^ 26 < @cf_malloc_max cp ->
malloc_site_tfa_cf B iface_room_np -> read_check_tfa_cf B -> memcpy_site_tfa_cf B ->
free_site_cf B iface_room_np -> refused_leaf_tfa_cf B -> hdr_tfa_cf (LS := LS) B iface_room_np NR ->
rd0_file_tfa_cf (LS := LS) B iface_room_np NR.

(* AD26.v:320 tfib_file_arm: its malloc is the first allocator call of the run; the interface's PROVISIONAL laws
   carry the non-primary room from the initial state across it. a8's malloc_cf_keeps_pristine_except is a theorem
   (YGcfPristine.v:381), so it is not a premise. *)
Definition tfib_file_arm_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop),
TfibSyms B -> PCA.iface_room_np_init iface_room_np -> PCA.iface_room_np_step (cp := cp) iface_room_np ->
malloc_site_tfa_cf B iface_room_np -> rd0_file_tfa_cf (LS := LS) B iface_room_np NR ->
file_arm_tfa_cf (LS := LS) B NR.

(* AD26.v:326 tfib_dir_arm. *)
Definition tfib_dir_arm_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (iface_room_np : astate -> Prop),
TfibSyms B -> PCA.iface_room_np_init iface_room_np -> PCA.iface_room_np_step (cp := cp) iface_room_np ->
malloc_site_tfa_cf B iface_room_np -> rd0_dir_tfa_cf B iface_room_np ->
dir_arm_tfa_cf B.
