(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCHuff BzCMtf BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


Section Phases.
  Variable e : est.                                   (* [comment removed for export] *)
  Variables cost0 fave0 pos0 in160 heap0 weight0 parent0 : zarr.   (* [comment removed for export] *)

  Definition sm_alpha : Z := e_nInUse e + 2.
  Definition sm_nmtf : Z := e_nMTF e.

  (* [comment removed for export] *)
  Definition smA_len : zarr := sm_len_init 6%nat (e_len e) sm_alpha 0.
  Definition smA_ng : Z := sm_nGroups sm_nmtf.
  Definition smA_ip : sip := sm_init_tables 8%nat (e_mtfFreq e) smA_ng sm_alpha (SIP smA_len smA_ng sm_nmtf 0).
  Definition est_A : est :=
    EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e)
        (ip_len smA_ip) (e_code e) (e_rfreq e) (e_len_pack e).

  (* [comment removed for export] *)
  Definition smB_it : sits :=
    sm_iters BZ_N_ITERS (e_arr1 e) smA_ng sm_alpha sm_nmtf
             (SITS (ip_len smA_ip) (e_rfreq e) (e_len_pack e) (e_selector e) cost0 fave0 0 heap0 weight0 parent0).
  Definition smB_nsel : Z := it_nSel smB_it.
  Definition est_B : est :=
    EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (it_sel smB_it) (e_selectorMtf e)
        (it_len smB_it) (e_code e) (it_rfreq smB_it) (it_lp smB_it).

  (* [comment removed for export] *)
  Definition smC_pos0 : zarr := yy_init (Z.to_nat smA_ng) pos0 0.
  Definition smC_pm : zarr * zarr := sm_selmtf (Z.to_nat smB_nsel) smC_pos0 (it_sel smB_it) (e_selectorMtf e) 0.
  Definition smC_code : zarr := sm_assign (Z.to_nat smA_ng) (e_code e) (it_len smB_it) sm_alpha 0.
  Definition est_C : est :=
    EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (it_sel smB_it) (snd smC_pm)
        (it_len smB_it) smC_code (it_rfreq smB_it) (it_lp smB_it).

  (* [comment removed for export] *)
  Definition smD_in16 : zarr := sm_in16 16%nat in160 (e_inUse e) 0.
  Definition smD_b0 : bw := sm_put_in16 16%nat (e_bw e) smD_in16 0.
  Definition smD_b1 : bw := sm_put_inuse 16%nat smD_b0 smD_in16 (e_inUse e) 0.
  Definition smD_b2 : bw := bsW (bsW smD_b1 3 smA_ng) 15 smB_nsel.
  Definition smD_b3 : bw := sm_put_sels (Z.to_nat smB_nsel) smD_b2 (snd smC_pm) 0.
  Definition smD_b4 : bw := sm_put_lens (Z.to_nat smA_ng) smD_b3 (it_len smB_it) sm_alpha 0.
  Definition smD_bd : bw * Z := sm_put_data (Z.to_nat (sm_nmtf + 1)) smD_b4 (it_len smB_it) smC_code (e_arr1 e) (it_sel smB_it) sm_nmtf 0 0.
  Definition est_D : est :=
    EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
        (fst smD_bd) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) (e_nMTF e) (e_mtfFreq e) (it_sel smB_it) (snd smC_pm)
        (it_len smB_it) smC_code (it_rfreq smB_it) (it_lp smB_it).

  (* [comment removed for export] *)
  Lemma sendMTF_phases : fst (sendMTFValues e cost0 fave0 pos0 in160 heap0 weight0 parent0) = est_D.
  Proof.
    unfold sendMTFValues, est_D, smD_bd, smD_b4, smD_b3, smD_b2, smD_b1, smD_b0, smD_in16, smC_code, smC_pm, smC_pos0,
           smB_nsel, smB_it, smA_ip, smA_ng, smA_len, sm_nmtf, sm_alpha.
    destruct (sm_selmtf _ _ _ _ _) as [pos selMtf]. cbn [fst snd].
    destruct (sm_put_data _ _ _ _ _ _ _ _ _) as [b selCtr]. reflexivity.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Phases.

(* [comment removed for export] *)

End ACeilS1.
