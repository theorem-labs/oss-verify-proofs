(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase StackLayout Fs State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymCall SymExit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_open__G1.Drv_open.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record Fctx := mkFctx {
  f_sp : word; f_brk : word; f_mb : word; f_draw : EntryDraw;
  f_inp : ProcInput;
  f_ent : valid_entry48 imgP (mkEntry f_sp f_brk f_mb f_draw) f_inp;
  f_inp_ok : valid_input_either f_inp;
  f_argc : length (in_argv f_inp) = 2%nat;
  f_md0 : Model;
  f_fds0 : m_fds f_md0 = std_fds;
  f_fs0 : m_fs f_md0 = in_fs f_inp;
  f_ok : world -> Prop;
  f_okK : forall K, K_tcons (Spec f_inp) K -> ok_frame segs f_ok K;
  f_okP : forall K, K_tcons (Spec f_inp) K -> ok_pframe segs f_ok K;
  f_okh : ok_halted f_ok (Spec f_inp);
  f_may : open_may_succeed (nth 1 (in_argv f_inp) []) (in_fs f_inp);
  f_F : list byte;
  f_HF : fs_lookup (in_fs f_inp) (nth 1 (in_argv f_inp) []) = Some f_F;
  f_nd : nth 1 (in_argv f_inp) [] <> dot_path
}.
