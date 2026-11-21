(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (KL_init reads the launch's reserved ledger as the image's reservations followed by the vDSO/vvar pair, which the placement base's floor and the brk window keep above the brk guard, and proves KL's three vDSO fields, with kl_prd_ge and vdso_reserved_small). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWy.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvVk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvVk.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOnw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOnw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Q5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Q5.Mq0.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma KL_model_ok : forall L pbrk md, KL L pbrk md -> model_ok md.
Proof. intros L pbrk md HK. split; [exact (kl_halt _ _ _ HK)| exact (kl_lazy _ _ _ HK)]. Qed.

#[using="Type"] Lemma reserved_top_ge : forall maps e, In e maps -> ehi e <= reserved_top maps.
Proof.
induction maps as [|[a sz] maps IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; [rewrite ehi_pair; lia|]. pose proof (IH e Hin). lia.
Qed.

(* Rounding a placement bound down to its page loses at most a page less one byte. *)
#[using="Type"] Lemma kl_prd_ge : forall y, y - 4095 <= page_round_down_Z y.
Proof.
intros y. unfold page_round_down_Z, page_size.
pose proof (Z_div_mod_eq_full y 4096) as E. pose proof (Z.mod_pos_bound y 4096 ltac:(lia)) as B. lia.
Qed.

(* The vDSO/vvar pair is at most two ledger entries, each at most sixteen pages. *)
#[using="Type"] Lemma vdso_reserved_small : forall kb top,
(length (vdso_reserved kb top) <= 2)%nat /\
Forall (fun p : word * word => bv_unsigned (snd p) <= 2^30) (vdso_reserved kb top).
Proof.
intros kb top. pose proof (vdso_text_pages_pos kb) as T1. pose proof (vdso_text_pages_le kb) as T2.
unfold vdso_reserved. cbv zeta. destruct (top - vdso_len kb <? page_size).
- split; [cbn [length]; lia| apply Forall_nil].
- split; [cbn [length]; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [snd];
rewrite unsigned_lit by (unfold vdso_vvar_pages, page_size in *; lia); unfold vdso_vvar_pages, page_size in *; lia.
Qed.

(* LPS 727298f3: [State.init_model] reserves the image's intervals and then the launch's
   vDSO/vvar pair ([State.init_reserved]), so the ledger the allocator starts from is the
   image's part [rs] only.  The pair sits just below the placement base, which
   [Run.valid_mmap_base] keeps above [State.mmap_base_min], while the brk window stays
   below 2^40: the pair is far above the brk guard. *)
#[using="Type"] Lemma KL_init : forall md pbrk (rs : list (word * word)),
m_halted md = None -> m_vm_lazy md = [] ->
vm_maps (m_vmmaps md) = [] -> vm_noaccess (m_vmmaps md) = [] ->
vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md) ->
vm_reserved (m_vmmaps md) = rs ++ vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md)) ->
reserved_top rs <= bv_unsigned (vm_start_brk (m_vmmaps md)) ->
mmap_base_min <= bv_unsigned (vm_mmap_base (m_vmmaps md)) ->
bv_unsigned (vm_start_brk (m_vmmaps md)) <= 2^40 ->
0 < bv_unsigned (vm_start_brk (m_vmmaps md)) ->
bv_unsigned (vm_start_brk (m_vmmaps md)) mod PGSZ = 0 ->
bv_unsigned (vm_start_brk (m_vmmaps md)) + 4 * PGSZ <= alloc_ceiling ->
alloc_top (m_vmmaps md) = alloc_ceiling ->
KL (led_init (map wwZ rs)) pbrk md.
Proof.
intros md pbrk rs Hh Hl Hm Hn Hb Hrs Htop Hmb H40 S1 S2 S4 Hceil. pose proof alloc_ceiling_small as Hcl.
pose proof alloc_ceiling_ge as Hcg.
pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps md))) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 64) with (2^64) in R.
pose proof (page_round_down_Z_le (alloc_top (m_vmmaps md))) as P1.
pose proof (kl_prd_ge (alloc_top (m_vmmaps md))) as P2.
pose proof (page_round_down_Z_le (mmap_top (m_vmmaps md))) as P3.
pose proof (kl_prd_ge (mmap_top (m_vmmaps md))) as P4.
assert (MT : mmap_base_min - 4095 <= mmap_top (m_vmmaps md) <= alloc_ceiling).
{ unfold mmap_top.
destruct (Z.min_spec (bv_unsigned (vm_mmap_base (m_vmmaps md))) (page_round_down_Z (alloc_top (m_vmmaps md)))) as [[C E]|[C E]];
rewrite E; unfold mmap_base_min in *; lia. }
assert (VT : mmap_base_min - 8190 <= vdso_top (m_vmmaps md) < two_pow_64).
{ unfold vdso_top, two_pow_64. lia. }
pose proof (vdso_len_bounds (m_kernel md)) as VL.
constructor; cbn [led_init ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?Hm, ?Hn.
- exact Hh.
- exact Hl.
- exact Hceil.
- split; [intros e []| constructor].
- exists rs, (vdso_reserved (m_kernel md) (vdso_top (m_vmmaps md))). split; [exact Hrs| reflexivity].
- intros e He. rewrite Hrs in He. apply in_app_or in He as [He|He].
+ pose proof (reserved_top_ge _ _ He). lia.
+ destruct e as [ea en]. destruct (vdso_reserved_above _ _ ea en (proj2 VT) He) as [_ Hle].
rewrite ehi_pair. unfold two_pow_64 in VT. lia.
- intros e He. rewrite Hrs in He. apply in_app_or in He as [He|He].
+ left. pose proof (reserved_top_ge _ _ He). lia.
+ right. exact He.
- rewrite Hb. splits; auto; lia.
- intros b l [].
- intros b l [].
- intros b l k [].
- constructor.
- intros e [].
- intros b l E. discriminate.
- split; [exact Hb| reflexivity].
- rewrite Hrs. apply incl_appr, incl_refl.
- intros [ea en] Hin. destruct (vdso_reserved_above _ _ ea en (proj2 VT) Hin) as [Hge _].
unfold elo. cbn [fst]. unfold mmap_base_min, page_size, PGSZ in *. lia.
- intros r Hr e [].
Qed.

Section Link.
Variable segs : list Segment.

#[using="Type"] Theorem ev_ok : EV_OK segs KL vm_only.
Proof.
intros e L pbrk md ms1 J KE HJ HK PRE HAT HC.
destruct e as [req|a len prot flags|a len|a len prot|p c h|w|a ol nl fl]; cbn in KE; try discriminate; cbn in PRE; unfold ev_at in HAT; cbn [ev_node] in HAT.
-
destruct PRE as [[-> Hph] | [(cur & Hph & Hreq) | (b & l & Hph & Hreg & Hreq)]].
+ eapply ev1_brk0; eauto.
+ eapply ev1_brk_grow1; eauto.
+ eapply ev1_brk_grow2; eauto.
-
destruct PRE as [(Hq & -> & -> & Hprot & Hlen) | (cur & Hph & -> & -> & -> & ->)].
+ eapply ev1_mmap_anon; eauto.
+ eapply ev1_mmap_fixed; eauto.
-
destruct PRE as (Hq & l & Hin & Hlen). eapply ev1_munmap; eauto.
-
destruct PRE as (Hq & -> & -> & b & l & k & Hin & Ha & Hk). eapply ev1_mprotect; eauto.
-
destruct PRE as (Hq & Hfl & Hnl & Hal & l & Hin & Hol & Hne). eapply ev1_mremap; eauto.
Qed.

Definition membed_realizes_KL {R : Type} :=
@membed_realizes RC__ segs KL vm_only vm_only_refl vm_only_trans KL_model_ok ev_ok R.

End Link.

End RC__1.
