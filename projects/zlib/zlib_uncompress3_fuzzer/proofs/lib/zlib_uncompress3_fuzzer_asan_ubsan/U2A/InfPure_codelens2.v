(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AArr InfPure InfPure_w7 ItAPure ItBridgeA InfPure_table InfPure_codelens.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma sinv_cl_bad : forall cx st lf cf ci H B,
  sinv cx st lf cf -> t_mode st = CODELENS -> buf_ok cx st ci H B ->
  sinv cx (bad_ofP (st_cl st ci H B (t_shave st))) lf cf /\ meas cx (bad_ofP (st_cl st ci H B (t_shave st))) < meas cx st.
Proof.
  intros cx st lf cf ci H B SI Hm BUF.
  destruct (cl_facts _ _ _ _ SI Hm) as (_ & _ & _ & _ & SH0 & SH1 & L15 & _ & _ & _ & _ & _ & _ & RLF & _).
  destruct (sinv_clb cx st lf cf ci H B (t_shave st) lf SI Hm BUF SH0 SH1 RLF L15) as (SI1 & ME1).
  split; [apply sinv_bad_ofP; exact SI1|].
  pose proof (meas_bad_ofP cx (st_cl st ci H B (t_shave st))) as E.
  replace (t_mode (st_cl st ci H B (t_shave st))) with CODELENS in E by (unfold st_cl; cbn [t_mode]; symmetry; exact Hm).
  change (rank CODELENS) with 20 in E. lia.
Qed.
