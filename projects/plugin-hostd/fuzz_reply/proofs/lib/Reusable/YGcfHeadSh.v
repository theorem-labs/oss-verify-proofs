(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfHeadSh.v, sha256 29ecfe07e1d303b146baa9a38d5c57e14303bfe46516d383347dcc402af7edd7.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the shadow of a live block
   split at its hidden head, derived from AR_laws_cf / ARcf with no record change.
   - AR_head_shadow_cf, for a block whose base is in Hp: the user range past the head has the allocator's
     shadow (alc_shadow at hd_skip Hp a = cf_head), and each of the cf_head / 8 head shadow bytes reads
     shUserPoison. The head part is amc_shadow (shadow_ok_cf) at a head granule g: the granule is in a's
     head, so in_head Hp g = true, and it lies in a's own chunk (amc_hp_live: cf_head <= ck_n), so
     find_chunk_at gives ashadow B ly S g = Some _. The base is 16-aligned (cfacts_cf) and the head
     8-aligned (cf_head_al), so head byte i is the shadow of granule a + 8 * i.
   - AR_user_shadow_cf, for a block whose base is NOT in Hp: cgif's form, block_shadow over the whole user
     range (hd_skip Hp a = 0).
   - ARx_hshadow_law_cf_ok: the head-split law ARx_hshadow_law_cf at hl = cf_head (block shadow and visible
     hull past the head, over req_size n), from AR_head_shadow_cf and alc_shadow's hull on a sub-range.
   No cgif file and no cf file is edited. No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma hd_skip_in_cf : forall Hp a, In a Hp -> hd_skip Hp a = cf_head.
Proof.
intros Hp a Hin. unfold hd_skip.
replace (existsb (Z.eqb a) Hp) with true; [reflexivity|].
symmetry. apply existsb_exists. exists a. split; [exact Hin | apply Z.eqb_refl].
Qed.

Lemma hd_skip_notin_cf : forall Hp a, ~ In a Hp -> hd_skip Hp a = 0.
Proof.
intros Hp a Hn. unfold hd_skip. destruct (existsb (Z.eqb a) Hp) eqn:E; [|reflexivity].
exfalso. apply existsb_exists in E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. exact (Hn Hx).
Qed.

Theorem AR_head_shadow_cf : forall segs B ly S Hp W mem md a n,
AR_laws_cf segs B -> ARcf segs B ly S Hp W mem md -> In (a, n) (ablocks B ly S) -> In a Hp ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF (a + cf_head) (req_size n - cf_head) /\
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem (shadow_addr a + i) = Some shUserPoison).
Proof.
intros segs B ly S Hp W mem md a n LAWS H Hb Hin.
split.
- pose proof (proj1 (alc_shadow _ _ LAWS ly S Hp W mem md a n H Hb)) as BS.
  rewrite (hd_skip_in_cf Hp a Hin) in BS. exact BS.
- intros i Hi.
  pose proof H as (M & _).
  destruct (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) a Hin) as (k & Hk & _ & Ea & Hn).
  pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (_ & _ & G3 & G4 & G5 & G6 & _ & G8 & _).
  pose proof (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as ND.
  pose proof cf_head_al as A8. pose proof cf_head_nonneg as A0.
  apply Z.mod_divide in A8 as [c Hc]; [|lia].
  rewrite Hc in Hi. rewrite Z.div_mul in Hi by lia.
  apply Z.mod_divide in G3 as [qb Hqb]; [|lia].
  apply Z.mod_divide in G6 as [qr Hqr]; [|lia].
  unfold ck_n in Hn.
  assert (Ga : a = (2 * qb + 2 * qr) * 8) by lia.
  assert (Gg : a + 8 * i = (2 * qb + 2 * qr + i) * 8) by lia.
  assert (G8' : (a + 8 * i) mod 8 = 0) by (rewrite Gg; apply Z.mod_mul; lia).
  assert (Hash : ashadow B ly S (a + 8 * i) = Some (chunk_granule k ((a + 8 * i - ck_base B ly k) / 8))).
  { unfold ashadow. rewrite (find_chunk_at_hit_cf B ly S Hp _ (st_chunks S) k (a + 8 * i) M (fun x Hx => Hx) ND Hk) by lia.
    reflexivity. }
  pose proof (amc_shadow _ _ _ _ _ M (a + 8 * i) _ G8' Hash) as SH.
  replace (in_head Hp (a + 8 * i)) with true in SH.
  2:{ symmetry. unfold in_head. apply existsb_exists. exists a. split; [exact Hin|].
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  replace (shadow_addr a + i) with (shadow_addr (a + 8 * i)); [exact SH|].
  unfold shadow_addr. rewrite Gg, Ga. rewrite !Z.div_mul by lia. lia.
Qed.

Theorem AR_user_shadow_cf : forall segs B ly S Hp W mem md a n,
AR_laws_cf segs B -> ARcf segs B ly S Hp W mem md -> In (a, n) (ablocks B ly S) -> ~ In a Hp ->
block_shadow (aview segs (w_H W) mem) SHADOW_OFF a (req_size n).
Proof.
intros segs B ly S Hp W mem md a n LAWS H Hb Hn.
pose proof (proj1 (alc_shadow _ _ LAWS ly S Hp W mem md a n H Hb)) as BS.
rewrite (hd_skip_notin_cf Hp a Hn), Z.add_0_r, Z.sub_0_r in BS. exact BS.
Qed.

(* c-omx-alloc's head-split shadow law at the cf instance, a proposal with no source in c-omx-alloc yet (text
   from CfCore, 2026-10-29). It mirrors ARx_shadow_law (YCbqG.v:92-97 at ea24ad37a3c) over req_size n, for a
   block whose base is in Hp: past a head of hl bytes, the user range has a block shadow and a visible hull. *)
Definition ARx_hshadow_law_cf segs B (hl : Z) : Prop := forall ly S Hp W mem md b n, ARcf segs B ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp -> block_shadow (aview segs (w_H W) mem) SHADOW_OFF (b + hl) (req_size n - hl) /\ (hl < req_size n -> shadow_hull_vis (aview segs (w_H W) mem) (b + hl) (req_size n - hl)).

(* The hull is closed under sub-ranges: both of its ends are monotone in the range's ends. *)
Lemma shadow_hull_vis_sub_cf : forall rd x n x' n',
shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.

(* The block shadow past the head is AR_head_shadow_cf's; the hull is alc_shadow's over (b, req_size n),
   restricted to (b + cf_head, req_size n - cf_head), which ends at the same byte. *)
Theorem ARx_hshadow_law_cf_ok : forall segs B, AR_laws_cf segs B -> ARx_hshadow_law_cf segs B cf_head.
Proof.
intros segs B LAWS. unfold ARx_hshadow_law_cf. intros ly S Hp W mem md b n H Hb Hin. split.
- exact (proj1 (AR_head_shadow_cf segs B ly S Hp W mem md b n LAWS H Hb Hin)).
- intros _. pose proof (proj2 (alc_shadow _ _ LAWS ly S Hp W mem md b n H Hb)) as HV.
  pose proof cf_head_nonneg as A0.
  eapply shadow_hull_vis_sub_cf; [exact HV | lia | lia].
Qed.

End j.
