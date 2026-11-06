(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfPlace.v, sha256 f08b06a57c5329e597917d9aad965f798a738bc696267eb1b332ac24d48ac38b.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the LPS placement lemma for the event-free second allocator instance (suffix cf).
   c-asan's sec_grant_exists_AR_P (SecGrantP.v) instantiated with
     AR := ARmcf (YG0ncf.v), Wf := Wf_cf (YG01cf.v), LG := ALedger_cf, xs := xs_cf (the live
     error-message-buffer extent, at most one entry, xs_cf_length), nob := cf_nob, lim := cf_place_limit,
     mmax := cf_malloc_max, with the side conditions cf_nob_lo, cf_nob_al, cf_place_ok and cf_sizes_ok of CfParams.
   The grant covers every map of at most cf_nob bytes, so both KMmapSec asks of the instance: malloc_cf's
   secondary map (sec_alloc) and the error-buffer map (errb_map_cf). The live premise
   length st_sec_arr + length xs_cf <= cf_place_limit comes from acall_pre_cf's strict count
   length st_sec_arr < cf_sec_live_max, cf_sec_live_ok and xs_cf_length.
   cgif's helpers (SecGrantP.v:330-344) name chunk_ok / wf_sec / WfP, so they are restated over chunk_ok_cf /
   wf_sec_cf / WfP_cf here. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK13 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import SecGrantP.
(* stdpp, through the LPS modules, shadows Forall_impl, Forall_forall and filter; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section PL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The state facts, over the cf invariant.                                     *)
Lemma ck_sec_ok_of_chunk_ok_cf : forall S k, chunk_ok_cf S k -> ck_sec_ok cf_malloc_max k.
Proof.
intros S k [Hr Hb]. split; [exact Hr|]. intros r o E. rewrite E in Hb. destruct Hb as (_ & Ho & _). exact Ho.
Qed.

Lemma sec_arr_of_wf_sec_cf : forall S, wf_sec_cf S ->
forall k r, In k (st_chunks S) -> ck_beg k = PSec r kPage -> In r (st_sec_arr S).
Proof. intros S WS k r Hk Hb. apply (proj2 (wsc_arr_chunks _ WS r)). exists k. split; assumption. Qed.

Lemma sec_chunks_ok_of_WfP_cf : forall U pp cc bb S, WfP_cf U pp cc bb S -> sec_chunks_ok cf_malloc_max S.
Proof.
intros U pp cc bb S W. split; [exact (wfc_chunks_nodup _ _ _ _ _ W)|]. split.
- apply Forall_impl with (2 := wfc_chunks _ _ _ _ _ W). intros k. apply ck_sec_ok_of_chunk_ok_cf.
- exact (sec_arr_of_wf_sec_cf S (wfc_secondary _ _ _ _ _ W)).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The extra extent: the live error buffer, at most cf_nob bytes.               *)
Lemma cfpl_last_P {A : Type} (P : A -> Prop) : forall l d, P d -> Forall P l -> P (last l d).
Proof.
intros l d Hd H. induction H as [|x t Hx Ht IH]; [exact Hd|]. destruct t as [|y t']; [exact Hx | exact IH].
Qed.

(* errb_cap_cf is the sm_len of an st_secs entry (or 0), and wsc_lens caps every entry at cf_nob. *)
Lemma errb_cap_cf_le_nob : forall S, wf_sec_cf S -> 0 <= errb_cap_cf S <= cf_nob.
Proof.
intros S WS. pose proof (wsc_lens _ WS) as LEN. pose proof cf_nob_lo as N0.
unfold errb_cap_cf, errb_e.
assert (H : 0 <= sm_len (last (filter is_errb_cap (st_secs S)) (mkSec 0 ERRB_CAP_TAG false)) <= cf_nob).
{ apply (cfpl_last_P (fun sm => 0 <= sm_len sm <= cf_nob)); [cbn [sm_len]; lia|].
  apply Forall_forall. intros sm Hsm. apply filter_In in Hsm as [Hsm _].
  exact (proj1 (Forall_forall _ _) LEN sm Hsm). }
lia.
Qed.

Lemma xs_cf_ok : forall ly S, wf_sec_cf S -> Forall (fun e => 0 <= snd e <= cf_nob) (xs_cf ly S).
Proof.
intros ly S WS. unfold xs_cf. destruct (last_cap_idx (st_secs S) 0 None); [|constructor].
constructor; [cbn [snd]; exact (errb_cap_cf_le_nob S WS) | constructor].
Qed.

(* The ledger facts the counting argument uses: ALedger_cf's cover already runs over
   lazy_zones ++ sec_extents ++ errb_zone, and errb_zone is xs_cf. *)
Lemma ledger_cover_of_ALedger_cf : forall segs ly S md, ALedger_cf segs ly S md ->
ledger_cover segs ly md (sec_extents ly S ++ xs_cf ly S).
Proof.
intros segs ly S md L. split; [exact (alc_img _ _ _ _ L)|]. split; [exact (alc_reserved _ _ _ _ L)|].
split; [exact (alc_top _ _ _ _ L) | exact (alc_cover _ _ _ _ L)].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The grant.                                                                   *)
(* sec_grant_exists_AR_P at the cf instance, with its live premise as stated there. *)
Theorem sec_grant_exists_cf_live : forall segs B ly S Hp rd md nZ,
ARmcf B ly S Hp rd -> ALedger_cf segs ly S md -> amwf md ->
Z.of_nat (length (st_sec_arr S)) + Z.of_nat (length (xs_cf ly S)) <= cf_place_limit ->
0 < nZ <= cf_nob ->
exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros segs B ly S Hp rd md nZ M L W LIVE HnZ.
assert (WS : wf_sec_cf S) by exact (wfc_secondary _ _ _ _ _ (amc_wf _ _ _ _ _ M)).
exact (sec_grant_exists_AR_P cf_nob cf_place_limit cf_malloc_max segs (Wf_cf (as_universe B))
(fun ly0 S0 => ARmcf B ly0 S0 Hp rd) (ALedger_cf segs) xs_cf
cf_nob_lo cf_nob_al cf_place_ok cf_sizes_ok
(fun ly0 S0 M0 => amc_layout _ _ _ _ _ M0) (fun ly0 S0 M0 => amc_wf _ _ _ _ _ M0)
(sec_chunks_ok_of_WfP_cf (as_universe B) 0 0 0)
(fun ly0 S0 md0 L0 => ledger_cover_of_ALedger_cf segs ly0 S0 md0 L0)
ly S md nZ M L W LIVE (xs_cf_ok ly S WS) HnZ).
Qed.

(* Over ARcf, with the strict live count the call forms carry. *)
Theorem sec_grant_exists_ARcf : forall segs B ly S Hp W mem md nZ,
ARcf segs B ly S Hp W mem md -> Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max -> 0 < nZ <= cf_nob ->
exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros segs B ly S Hp W mem md nZ (M & L & _ & MW & _) LIVE HnZ.
apply (sec_grant_exists_cf_live segs B ly S Hp _ md nZ M L MW); [|exact HnZ].
pose proof (xs_cf_length ly S). pose proof cf_sec_live_ok. lia.
Qed.

(* At an allocator call: the grant for a new map of at most cf_nob bytes. *)
Theorem sec_grant_exists_cf : forall segs B ly S Hp W regs mem md ch nZ,
acall_pre_cf segs B ly S Hp W regs mem md ch -> 0 < nZ <= cf_nob ->
exists a, grant_ok_na_pin md a nZ = true.
Proof.
intros segs B ly S Hp W regs mem md ch nZ (AR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIVE & _) HnZ.
exact (sec_grant_exists_ARcf segs B ly S Hp W mem md nZ AR LIVE HnZ).
Qed.

End PL.
