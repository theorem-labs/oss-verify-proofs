(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate Uncompr HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition dinitC_run (level : Z) (chs : DCH) (z : zstrm) : option (option deflate_state * ZRet) :=
  dpure (deflateInit2_m dhooks (zc_none z) level Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY) chs.

Definition dinitC (level : Z) : option (option deflate_state * ZRet) := dinitC_run level (dchs (fun _ => g0)) zstrm0.
Definition dsC (level : Z) : deflate_state := match dinitC level with Some (Some s, _) => s | _ => ds_dummy end.
Definition dzC (level : Z) : zstrm := match dinitC level with Some (_, zr) => zr_strm zr | None => zstrm0 end.

Definition cfg_row (level : Z) : Z * Z * Z * Z :=
  (ds_good_match (dsC level), ds_max_lazy_match (dsC level), ds_nice_match (dsC level), ds_max_chain_length (dsC level)).

Definition e1_compress2 (destLen : Z) (src : list Z) (level : Z) : option (Z * list Z * Z) :=
  dpure (compress2_m dhooks destLen src level) (dchs (fun _ => g0)).

Definition e1_uncompress2 (destLen : Z) (src : list Z) : option (Z * list Z * Z * Z) :=
  dpure (uncompress2_m ivar_ref dhooks destLen src (zlength src)) [Some (5%N, g0); Some (6%N, g0)].
