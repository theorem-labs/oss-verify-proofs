(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepGrantcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 c23f271ec80e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, RepF4Append's relation side): a placement witness for the errbuf mmap
   of __asan::AppendToErrorMessageBuffer (RepIFcf.append_spec_cf), from the cf relation alone.  It is half (A) of
   RepF4Append's slice premise errb_map_fits_cf: a grant exists, so the MmapOrDie refusal branch needs only the
   budget half.
   rule 24: proves no function (kind: invariant lemma, grant existence at the errbuf mmap from the relation; no
   machine code runs).  Reuse: a Theorem Labs lane's parametric placement lemma SecGrantP.sec_grant_exists_live_P
   (SecGrantP.v:306), the lemma SecGrantW.ifs_grant_w_cf instantiates; it is applied here directly at
   segs := tfibsegs, nob := cf_nob, lim := cf_place_limit, mmax := cf_malloc_max, xs := xs_cf, because
   ifs_grant_w_cf is stated over ImgBase's im_segs (an AImg instance) and this walk's segments are tfibsegs.
   Its four ledger facts are ALedger_cf's alc_img / alc_reserved / alc_top / alc_cover word for word: alc_cover's
   zone list lazy_zones ly ++ sec_extents ly S ++ errb_zone ly S is ledger_cover's lazy_zones ly ++ zs at
   zs := sec_extents ly S ++ xs_cf ly S (errb_zone := xs_cf, YG0ncf.v:109), so nothing is weakened.
   The live count needs ONE more than CfParams' cf_sec_live_ok (cf_sec_live_max <= cf_place_limit) gives, because
   xs_cf adds up to one extent: that is CfParams' field cf_sec_live_place_lt (YGcfNames.v:139, added for this). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK13 YK0g YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0d YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import SecGrantP.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.

Lemma errb_grant_exists_cf : forall (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) (mat : list word) (nZ : Z),
  ARcf tfibsegs B ly S Hp W mem md -> 0 < nZ <= cf_nob ->
  exists a, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a nZ = true.
Proof.
intros Hp ly S W mem md mat nZ (M & L & _ & MW & _) HnZ.
pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
set (md0 := with_vm_backing (m_vm_lazy md) mat md).
pose proof (amwf_same md md0 eq_refl eq_refl MW) as [_ NZ].
assert (LC : ledger_cover tfibsegs ly md0 (sec_extents ly S ++ xs_cf ly S)).
{ unfold ledger_cover. split; [exact (alc_img _ _ _ _ L)|]. split; [exact (alc_reserved _ _ _ _ L)|].
  split; [exact (alc_top _ _ _ _ L)|]. intros e He. exact (alc_cover _ _ _ _ L e He). }
assert (SC : sec_chunks_ok cf_malloc_max S).
{ split; [exact (wfc_chunks_nodup _ _ _ _ _ WF)|]. split.
  - apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hk) as [Hn CK].
    split; [exact Hn|]. intros r o E. rewrite E in CK. cbn iota in CK. destruct CK as (_ & Ho & _). exact Ho.
  - intros k r Hk E. apply (proj2 (wsc_arr_chunks _ (wfc_secondary _ _ _ _ _ WF) r)). exists k. split; [exact Hk | exact E]. }
assert (LIVE : Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs_cf ly S)) <= cf_place_limit).
{ pose proof (wfc_sec_live _ _ _ _ _ WF). pose proof (xs_cf_length ly S). pose proof cf_sec_live_place_lt. lia. }
assert (XS : Forall (fun e => 0 <= snd e <= cf_nob) (xs_cf ly S)).
{ unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None); [|constructor].
  constructor; [|constructor]. cbn [snd]. exact (errb_cap_bound_cf _ _ _ _ _ WF). }
exact (sec_grant_exists_live_P cf_nob cf_place_limit cf_malloc_max tfibsegs ly S md0 (xs_cf ly S) nZ
  cf_nob_lo cf_nob_al cf_place_ok cf_sizes_ok LO LC NZ SC LIVE XS HnZ).
Qed.

End a.
