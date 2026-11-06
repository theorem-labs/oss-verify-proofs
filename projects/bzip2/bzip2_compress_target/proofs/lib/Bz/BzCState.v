(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Export BzParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
Definition BZ_M_IDLE : Z := 1.
Definition BZ_M_RUNNING : Z := 2.
Definition BZ_M_FLUSHING : Z := 3.
Definition BZ_M_FINISHING : Z := 4.
Definition BZ_S_OUTPUT : Z := 1.
Definition BZ_S_INPUT : Z := 2.
Definition BZ_N_OVERSHOOT : Z := 34.
Definition BZ_G_SIZE : Z := 50.

Record est := EST {
  e_mode : Z; e_state : Z; e_avail_in_expect : Z;
  e_arr1 : zarr; e_arr2 : zarr; e_ftab : zarr;
  e_origPtr : Z;
  e_state_in_ch : Z; e_state_in_len : Z;
  e_nblock : Z; e_state_out_pos : Z;
  e_nInUse : Z; e_inUse : zarr; e_unseqToSeq : zarr;
  e_bw : bw;                                   (* [comment removed for export] *)
  e_blockCRC : Z; e_combinedCRC : Z; e_blockNo : Z;
  e_nMTF : Z; e_mtfFreq : zarr; e_selector : zarr; e_selectorMtf : zarr;
  e_len : zarr; e_code : zarr; e_rfreq : zarr; e_len_pack : zarr
}.

(* [comment removed for export] *)
Definition est_rl (e : est) : rlst :=
  RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) (e_state_in_ch e) (e_state_in_len e).
Definition est_set_rl (e : est) (r : rlst) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (rl_block r) (e_ftab e) (e_origPtr e)
      (rl_ch r) (rl_len r) (rl_nblock r) (e_state_out_pos e) (e_nInUse e) (rl_inUse r) (e_unseqToSeq e)
      (e_bw e) (rl_crc r) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).

(* [comment removed for export] *)
Definition est_set_bw (e : est) (b : bw) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      b (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Definition est_set_modes (e : est) (mode state expect : Z) : est :=
  EST mode state expect (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Definition est_set_outpos (e : est) (p : Z) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) p (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
      (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).

(* [comment removed for export] *)
Definition est_init (arr1 arr2 ftab inUse unseq mtfFreq sel selMtf len code rfreq lenp : zarr)
           (bsBuff bsLive nInUse origPtr nMTF : Z) : est :=
  EST BZ_M_RUNNING BZ_S_INPUT 0 arr1 arr2 ftab origPtr
      256 0 0 0 nInUse (inUse_clear inUse 0 256) unseq
      (BW bsBuff bsLive 0 znew) crc_init 0 1 nMTF mtfFreq sel selMtf len code rfreq lenp.

End ACeilS1.
