(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the HIDDEN-HEAD layer.
   The ghost set Hp of YGcfNames.v section 3 (hidden block bases; a hidden head [p, p + cf_head) has shadow
   shUserPoison) moves only at the harness's two shadow calls. This file gives:
     - the contracts of __asan_poison_memory_region (p, cf_head) and __asan_unpoison_memory_region (p, cf_head)
      over ARcf (apoison_realizes_cf / aunpoison_realizes_cf), their pcs taken from the per-image CfImg
      fields cf_pc_poison / cf_pc_unpoison, never literals;
     - laws (a) - (e) of YGcfNames.v:278-293 (hp_malloc_cf, ahead_poison_law, ahead_unpoison_law,
       realloc_cf_hp_post_ok, realloc_cf_hp_post_null) as Definitions, each proved as <name>_proof.
   Ported from port-fm's fuzz_manifest/lib/A/FMupoison.v and FMpoisonS.v at 8d043571f33: upoison_ok_one
   (:202) -> hp_live_one, ARU_poison_step (:263) -> ahead_poison_law, ARU_unpoison_step (:333) ->
   ahead_unpoison_law, apoison16_realizes / aunpoison16_realizes (FMpoisonS.v) -> the two contracts.
   port-fm's ARU reads cgif's AR over the memory with the user-poisoned shadow bytes read as 0, so cgif's
   frame law moves its set. Here the set is inside ARmcf (amc_shadow, amc_hp_live), every law of AR_laws_cf
   (YG0dcf.v) keeps Hp fixed, and the head shadow bytes are aowned, so the one fact the steps need beyond
   AR_laws_cf is AR_head_frame_law_cf below: the frame law with Hp moving, in the shape of cgif's
   astack_free_law (YG0d.v:301). Every law here takes AR_laws_cf and, where it needs it, AR_head_frame_law_cf
   as explicit premises. No address: every numeral is a shadow-encoding constant. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0scf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The poison / unpoison pcs are the per-image fields cf_pc_poison / cf_pc_unpoison of CfImg
   (YGcfNames.v); the temporary class CfPoisonImg of 29c8b46b1cef is gone. *)

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* hp_live_cf and hd_shadow (amc_hp_live's body, and the hidden-head shadow bytes) are
   defined in YG0dcf.v beside AR_head_frame_law_cf, which is a field of AR_laws_cf. *)

Section R.
Variable segs : list Segment.
Variable B : asyms.

(* AR_head_frame_law_cf, the frame law with Hp moving, is defined in YG0dcf.v (moved there
   verbatim from this file, 29c8b46b1cef :63-74) because it is the 15th field of AR_laws_cf. *)

(* ---------------------------------------------------------------------------- *)
(* 3. Laws (a) - (e) of YGcfNames.v:278-293.                                     *)
(* (a) malloc_cf success: Hp is unchanged (one Hp in pre and post), and a block   *)
(*     that was not live before is not in Hp, so its whole user range has shadow  *)
(*     0 and the harness may write its head before hiding it.                     *)
Definition hp_malloc_cf : Prop :=
forall ly S Hp W mem md ly' S' W' mem' md' q n,
ARcf segs B ly S Hp W mem md ->
ARcf segs B ly' S' Hp W' mem' md' ->
In (q, n) (ablocks B ly' S') -> ~ In q (map fst (ablocks B ly S)) ->
~ In q Hp /\ block_shadow (aview segs (w_H W') mem') SHADOW_OFF q (req_size n).

(* (b) __asan_poison_memory_region (p, cf_head) on a live block of at least cf_head  *)
(*     bytes (port of ARU_poison_step): if the run keeps the memory outside its     *)
(*     stack window [lo, hi) and the cf_head / 8 head shadow bytes, and makes those *)
(*     shUserPoison, then p joins Hp.                                               *)
Definition ahead_poison_law : Prop :=
forall ly S Hp W mem md p n mem1 md1 lo hi,
ARcf segs B ly S Hp W mem md -> cf_head mod 8 = 0 ->
In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr p <= a < shadow_addr p + cf_head / 8) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
(forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem1 (shadow_addr p + i) = Some shUserPoison) ->
m_vmmaps md1 = m_vmmaps md -> m_vm_lazy md1 = m_vm_lazy md -> eager_used md1 = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem1 (w64 a) = mem (w64 a)) ->
ARcf segs B ly S (p :: Hp) W mem1 md1.

(* (c) __asan_unpoison_memory_region (p, cf_head) for p in Hp (port of             *)
(*     ARU_unpoison_step): if the run keeps the memory outside its stack window     *)
(*     and the head shadow bytes, and makes those 0, then p leaves Hp.              *)
Definition ahead_unpoison_law : Prop :=
forall ly S Hp W mem md p mem1 md1 lo hi,
ARcf segs B ly S Hp W mem md -> cf_head mod 8 = 0 -> In p Hp ->
ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr p <= a < shadow_addr p + cf_head / 8) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
(forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem1 (shadow_addr p + i) = Some 0) ->
m_vmmaps md1 = m_vmmaps md -> m_vm_lazy md1 = m_vm_lazy md -> eager_used md1 = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem1 (w64 a) = mem (w64 a)) ->
ARcf segs B ly S (remove Z.eq_dec p Hp) W mem1 md1.

(* (d) realloc success: the old block p is freed, q is new, every other live block  *)
(*     survives. Then remove p Hp satisfies am_hp_live at the post, keeping p would *)
(*     not (p is no longer live), q is not hidden, and at a post ARcf over          *)
(*     remove p Hp the new block's whole user range has shadow 0.                   *)
Definition realloc_cf_hp_post_ok : Prop :=
forall ly S Hp W mem md ly' S' W' mem' md' p q n,
ARcf segs B ly S Hp W mem md ->
In (q, n) (ablocks B ly' S') -> ~ In q (map fst (ablocks B ly S)) ->
~ In p (map fst (ablocks B ly' S')) ->
(forall b, In b (ablocks B ly S) -> fst b <> p -> In b (ablocks B ly' S')) ->
Forall (hp_live_cf B ly' S') (remove Z.eq_dec p Hp) /\
(In p Hp -> ~ Forall (hp_live_cf B ly' S') Hp) /\
~ In q (remove Z.eq_dec p Hp) /\
(ARcf segs B ly' S' (remove Z.eq_dec p Hp) W' mem' md' ->
block_shadow (aview segs (w_H W') mem') SHADOW_OFF q (req_size n)).

(* (e) realloc NULL: over a call post at the SAME Hp (acall_post_cf), with the old  *)
(*     block still live, its bytes are unchanged, its shadow past the hidden head  *)
(*     is the allocator's, and a hidden head still reads shUserPoison.             *)
Definition realloc_cf_hp_post_null : Prop :=
forall stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' p n_old,
ARcf segs B ly S Hp W mem md ->
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
In (p, n_old) (ablocks B ly S) -> In (p, n_old) (ablocks B ly' S') ->
(forall a, p <= a < p + req_size n_old -> ~ ascratch B stk regs a /\ ~ E a) ->
(forall a, p <= a < p + req_size n_old -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
block_shadow (aview segs (w_H W') mem') SHADOW_OFF (p + hd_skip Hp p) (req_size n_old - hd_skip Hp p) /\
(cf_head mod 8 = 0 -> In p Hp -> forall i, 0 <= i < cf_head / 8 ->
aview segs (w_H W') mem' (shadow_addr p + i) = Some shUserPoison).

(* ---------------------------------------------------------------------------- *)
(* 4. The two contracts (FMpoisonS.v's apoison16_realizes / aunpoison16_realizes   *)
(*    over ARcf). The head is [p, p + cf_head) of a live block of at least cf_head  *)
(*    bytes (cf_head <= req_size n: fuzz_malloc (0) mallocs 16 B and hides all of   *)
(*    it, preset alloc.c:65-76); the stack window is ecall_pre_cf's ESTACK window.   *)
Section C.
Definition apoison_realizes_cf : Prop :=
forall ly S Hp (W : world segs) regs mem md p n,
ecall_pre_cf segs B ly S Hp W regs mem md ->
getr regs 10 = w64 p -> getr regs 11 = w64 cf_head -> cf_head mod 8 = 0 ->
In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
SRr segs W (cfg_at segs cf_pc_poison regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S (p :: Hp) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem' (shadow_addr p + i) = Some shUserPoison) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ (shadow_addr p <= a < shadow_addr p + cf_head / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(* the overlay normal form is kept (the walks of S1 pay memnorm across each allocator call) *)
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

Definition aunpoison_realizes_cf : Prop :=
forall ly S Hp (W : world segs) regs mem md p n,
ecall_pre_cf segs B ly S Hp W regs mem md ->
getr regs 10 = w64 p -> getr regs 11 = w64 cf_head -> cf_head mod 8 = 0 -> In p Hp ->
In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
SRr segs W (cfg_at segs cf_pc_unpoison regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARcf segs B ly S (remove Z.eq_dec p Hp) W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem' (shadow_addr p + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> ~ (shadow_addr p <= a < shadow_addr p + cf_head / 8) ->
aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).
End C.

(* ---------------------------------------------------------------------------- *)
(* 5. Helpers.                                                                    *)
Lemma in_head_cons : forall p L g, in_head (p :: L) g = ((p <=? g) && (g <? p + cf_head)) || in_head L g.
Proof. reflexivity. Qed.
Lemma in_head_app : forall L1 L2 g, in_head (L1 ++ L2) g = in_head L1 g || in_head L2 g.
Proof. intros L1 L2 g. unfold in_head. apply existsb_app. Qed.
Lemma in_head_spec : forall L g, in_head L g = true <-> exists q, In q L /\ q <= g < q + cf_head.
Proof.
intros L g. unfold in_head. rewrite existsb_exists. split; intros (q & Hq & Hg); exists q; split; try exact Hq.
- apply andb_prop in Hg as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
- apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma in_head_remove_sub : forall p L g, in_head (remove Z.eq_dec p L) g = true -> in_head L g = true.
Proof.
intros p L g H. apply in_head_spec in H as (q & Hq & Hg). apply in_remove in Hq as [Hq _].
apply in_head_spec. exists q. split; [exact Hq | exact Hg].
Qed.
Lemma hd_skip_notin : forall Hp p, ~ In p Hp -> hd_skip Hp p = 0.
Proof.
intros Hp p H. unfold hd_skip. destruct (existsb (Z.eqb p) Hp) eqn:E; [|reflexivity].
exfalso. apply existsb_exists in E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. exact (H Hx).
Qed.
Lemma ablocks_In_hp : forall ly S p n, In (p, n) (ablocks B ly S) <->
exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ sptr_addr B ly (ck_user k) = p /\ ck_req k = n.
Proof.
intros ly S p n. unfold ablocks, blocks. rewrite in_map_iff. split.
- intros ([q m] & E & Hin). cbn [fst snd] in E. injection E as E1 E2.
  apply in_map_iff in Hin as (k & Ek & Hk). injection Ek as Ek1 Ek2. apply filter_In in Hk as [Hk Ha].
  exists k. subst. split; [exact Hk|]. split; [|split; reflexivity].
  unfold is_alloc in Ha. destruct (ck_state k); try reflexivity; discriminate.
- intros (k & Hk & Hs & Hp & Hn). exists (ck_user k, ck_req k). cbn [fst snd]. split; [rewrite Hp, Hn; reflexivity|].
  apply in_map_iff. exists k. split; [reflexivity|]. apply filter_In. split; [exact Hk|].
  unfold is_alloc. rewrite Hs. reflexivity.
Qed.
Lemma hp_live_ablock : forall ly S q, hp_live_cf B ly S q -> exists n, In (q, n) (ablocks B ly S) /\ cf_head <= req_size n.
Proof.
intros ly S q (k & Hk & Hs & -> & Hn). exists (ck_req k). split; [|exact Hn].
apply ablocks_In_hp. exists k. repeat split; auto.
Qed.
(* Port of upoison_ok_one (FMupoison.v:202): a live block of at least cf_head bytes may be hidden. *)
Lemma hp_live_one : forall ly S p n, In (p, n) (ablocks B ly S) -> cf_head <= req_size n -> hp_live_cf B ly S p.
Proof.
intros ly S p n Hb Hn. apply ablocks_In_hp in Hb as (k & Hk & Hs & Hp & Hr). exists k. subst. unfold ck_n.
repeat split; auto.
Qed.
Lemma pairwise_In2 {X : Type} (R : X -> X -> Prop) : forall l x y, pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
induction l as [|a t IH]; intros x y P Hx Hy Ne; [destruct Hx|]. destruct P as [F P].
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
- exfalso. apply Ne. reflexivity.
- left. exact (proj1 (Forall_forall _ _) F y Hy).
- right. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy Ne).
Qed.
Lemma blocks_apart : forall (LAWS : AR_laws_cf segs B) ly S Hp W mem md p n q m,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> p <> q ->
p + req_size n <= q \/ q + req_size m <= p.
Proof.
intros LAWS ly S Hp W mem md p n q m H Hbp Hbq Ne.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n H Hbp) as (_ & _ & _ & _ & _ & PW & _).
assert (X : In (p, req_size n) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))) by (apply in_map_iff; exists (p, n); auto).
assert (Y : In (q, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))) by (apply in_map_iff; exists (q, m); auto).
destruct (pairwise_In2 zdisjoint _ _ _ PW X Y ltac:(intros E; injection E as E _; exact (Ne E))) as [D|D];
unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.
Lemma heads_apart : forall (LAWS : AR_laws_cf segs B) ly S Hp W mem md p n q g,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
hp_live_cf B ly S q -> q <> p -> q <= g < q + cf_head -> ~ (p <= g < p + cf_head).
Proof.
intros LAWS ly S Hp W mem md p n q g H Hbp Hn HL Ne Hg Hg'.
destruct (hp_live_ablock ly S q HL) as (m & Hm & Hc).
destruct (blocks_apart LAWS ly S Hp W mem md p n q m H Hbp Hm ltac:(congruence)) as [D|D]; lia.
Qed.
Lemma live_head_bounds : forall (LAWS : AR_laws_cf segs B) ly S Hp W mem md q g,
ARcf segs B ly S Hp W mem md -> hp_live_cf B ly S q -> q <= g < q + cf_head ->
q mod 16 = 0 /\ 4096 <= g /\ 0 <= shadow_addr g < 2 ^ 64 /\ shadow_addr g < ly_stk_lo ly /\ in_band_rw (shadow_addr g).
Proof.
intros LAWS ly S Hp W mem md q g H HL Hg.
destruct (hp_live_ablock ly S q HL) as (m & Hm & Hc).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md q m H Hm) as (Q16 & Q4k & Qce & Qapp & _).
pose proof (lo_top _ (amc_layout _ _ _ _ _ (proj1 H))) as (_ & _ & _ & _ & _ & _ & SK).
pose proof (@ASAN_CEIL_range _) as [CR _]. unfold ASAN_CEIL in CR.
assert (IB : in_band_rw (shadow_addr g)).
{ replace g with (q + (g - q)) by lia. apply (shadow_addr_in_band q (req_size m)); [exact Qapp | lia]. }
split; [exact Q16|]. split; [lia|]. split; [|split; [|exact IB]]; unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.
Lemma shadow_idx : forall p g, p mod 8 = 0 -> g mod 8 = 0 -> shadow_addr g = shadow_addr p + (g - p) / 8.
Proof.
intros p g Hp Hg. apply Z.mod_divide in Hp as [a Ha]; [|lia]. apply Z.mod_divide in Hg as [b Hb]; [|lia]. subst p g.
unfold shadow_addr. replace (b * 8 - a * 8) with ((b - a) * 8) by ring. rewrite !Z.div_mul by lia. ring.
Qed.
Lemma shadow_inv : forall g, g mod 8 = 0 -> 8 * (shadow_addr g - SHADOW_OFF) = g.
Proof. intros g Hg. apply Z.mod_divide in Hg as [b Hb]; [|lia]. subst g. unfold shadow_addr. rewrite Z.div_mul by lia. ring. Qed.
Lemma head_shadow_iff : forall p g, p mod 8 = 0 -> g mod 8 = 0 -> cf_head mod 8 = 0 ->
(shadow_addr p <= shadow_addr g < shadow_addr p + cf_head / 8 <-> p <= g < p + cf_head).
Proof.
intros p g Hp Hg Hc. apply Z.mod_divide in Hp as [a Ha]; [|lia]. apply Z.mod_divide in Hg as [b Hb]; [|lia].
apply Z.mod_divide in Hc as [c Hc']; [|lia]. rewrite Hc'. subst p g. unfold shadow_addr. rewrite !Z.div_mul by lia. lia.
Qed.
Lemma head_idx_range : forall p g, p mod 8 = 0 -> g mod 8 = 0 -> cf_head mod 8 = 0 -> p <= g < p + cf_head ->
0 <= (g - p) / 8 < cf_head / 8.
Proof.
intros p g Hp Hg Hc Hr. apply Z.mod_divide in Hp as [a Ha]; [|lia]. apply Z.mod_divide in Hg as [b Hb]; [|lia].
apply Z.mod_divide in Hc as [c Hc']; [|lia]. rewrite Hc' in *. subst p g.
replace (b * 8 - a * 8) with ((b - a) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.
Lemma head_shadow_g : forall p a, p mod 8 = 0 -> cf_head mod 8 = 0 -> shadow_addr p <= a < shadow_addr p + cf_head / 8 ->
exists g, g mod 8 = 0 /\ p <= g < p + cf_head /\ a = shadow_addr g.
Proof.
intros p a Hp Hc Ha. apply Z.mod_divide in Hp as [x Hx]; [|lia]. apply Z.mod_divide in Hc as [c Hc']; [|lia].
rewrite Hc' in *. subst p. unfold shadow_addr in *. rewrite !Z.div_mul in * by lia.
exists ((a - SHADOW_OFF) * 8). rewrite Z.mod_mul, Z.div_mul by lia. lia.
Qed.
Lemma p8_of_p16 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof.
intros p H. apply Z.mod_divide in H as [x Hx]; [|lia]. subst p. replace (x * 16) with ((x * 2) * 8) by ring. apply Z.mod_mul. lia.
Qed.
Lemma wz_hp : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma wz8_hp : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros v Hv. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia. Qed.
Lemma aview_at_hp : forall Hd m1 m2 a, m1 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) -> aview segs Hd m1 a = aview segs Hd m2 a.
Proof. intros Hd m1 m2 a E. unfold aview, mbyte, mrestrict. destruct (Hd (Z_to_bv 64 a)); [reflexivity|]. rewrite E. reflexivity. Qed.
Lemma aview_hidden_hp : forall Hd m1 m2 a, Hd (Z_to_bv 64 a) = true -> aview segs Hd m1 a = aview segs Hd m2 a.
Proof. intros Hd m1 m2 a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma aview_byte_hp : forall Hd m a b, Hd (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) = Some b ->
aview segs Hd m a = Some (bv_unsigned b).
Proof. intros Hd m a b E M. unfold aview, mbyte, mrestrict. rewrite E, M. reflexivity. Qed.
Lemma aview_mod_hp : forall Hd m a, aview segs Hd m a = aview segs Hd m (a mod 2 ^ 64).
Proof.
intros Hd m a. assert (E : Z_to_bv 64 a = Z_to_bv 64 (a mod 2 ^ 64)).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
unfold aview, mbyte. rewrite E. reflexivity.
Qed.
(* YG0q.v:611-640 (seg_rom_none_above, aview_band_hidden), copied: YG0q is not in this file's closure. *)
Lemma seg_rom_none_above_hp : forall a,
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
kImgEnd <= a < 2 ^ 64 -> seg_rom segs (w64 a) = None.
Proof.
intros a IMG Ha. unfold seg_rom, memory_read. unfold kImgEnd in *.
assert (FS : find_segment segs (bv_unsigned (w64 a)) 1 = None).
{ unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
clear - IMG Ha. induction segs as [|sg t IH]; [reflexivity|]. cbn [find_segment].
destruct (IMG sg (or_introl eq_refl)) as [G1 G2].
destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); destruct (Z.leb_spec (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))); cbn [andb]; try lia.
all: apply IH; intros sg' Hin; apply IMG; right; exact Hin. }
change (Z.of_N 1) with 1. rewrite FS. reflexivity.
Qed.
Lemma aview_band_hidden_hp : forall Hd mem a,
(forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
in_band_rw a -> Hd (Z_to_bv 64 a) = true -> aview segs Hd mem a = None.
Proof.
intros Hd mem a IMG Ha Hh. unfold aview, mbyte, mrestrict. rewrite Hh.
change (Z_to_bv 64 a) with (w64 a). rewrite (seg_rom_none_above_hp a IMG) by (unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). reflexivity.
Qed.
Lemma arcf_img : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof.
intros ly S Hp W mem md (M & L & _) sg Hsg. pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2].
pose proof (lo_img _ (amc_layout _ _ _ _ _ M)) as (J0 & J1 & J2 & J3). unfold kImgLo, kImgEnd in *. lia.
Qed.
Lemma ashadow_range : forall ly S g v, ashadow B ly S g = Some v -> 0 <= v < 256.
Proof.
intros ly S g v H. unfold ashadow in H. destruct (find_chunk_at B ly (st_chunks S) g) as [k|].
- injection H as <-. unfold chunk_granule. cbv zeta. pose proof (Z.mod_pos_bound (ck_n k) 8 ltac:(lia)).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  try (destruct (ck_state k)); repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  unfold shHeapLeftRz, shHeapFreed, shAddressable; lia.
- match type of H with context [in_rangesb ?x ?y] => destruct (in_rangesb x y) end;
  [injection H as <-; unfold shHeapLeftRz; lia | discriminate].
Qed.

(* The probe memory of head_ashadow0: at each visible head shadow byte of p, the allocator's own shadow
   value (1 where the allocator has none); elsewhere mem. *)
Definition hs_in (p x : Z) : bool := (shadow_addr p <=? x) && (x <? shadow_addr p + cf_head / 8).
Lemma hs_in_iff : forall p x, hs_in p x = true <-> shadow_addr p <= x < shadow_addr p + cf_head / 8.
Proof.
intros p x. unfold hs_in. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.
Definition probe_mem (ly : alayout) (S : astate) (Hd : word -> bool) (mem : word -> option byte) (p : Z) : word -> option byte :=
fun w => if hs_in p (bv_unsigned w) && negb (Hd w)
then Some (Z_to_bv 8 (match ashadow B ly S (8 * (bv_unsigned w - SHADOW_OFF)) with Some v => v | None => 1 end))
else mem w.
Lemma probe_out : forall ly S Hd mem p w, hs_in p (bv_unsigned w) = false -> probe_mem ly S Hd mem p w = mem w.
Proof. intros ly S Hd mem p w E. unfold probe_mem. rewrite E. reflexivity. Qed.
Lemma probe_hid : forall ly S Hd mem p w, Hd w = true -> probe_mem ly S Hd mem p w = mem w.
Proof. intros ly S Hd mem p w E. unfold probe_mem. rewrite E. destruct (hs_in p (bv_unsigned w)); reflexivity. Qed.
Lemma probe_in : forall ly S Hd mem p w, hs_in p (bv_unsigned w) = true -> Hd w = false ->
probe_mem ly S Hd mem p w =
Some (Z_to_bv 8 (match ashadow B ly S (8 * (bv_unsigned w - SHADOW_OFF)) with Some v => v | None => 1 end)).
Proof. intros ly S Hd mem p w E F. unfold probe_mem. rewrite E, F. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. A hidden head's granules have allocator shadow 0. Moving p out of Hp onto   *)
(*    the probe memory (AR_head_frame_law_cf), the shadow law at the smaller Hp    *)
(*    reads 0 over the whole block, and the probe holds the allocator's value.     *)
Lemma head_ashadow0 : AR_laws_cf segs B -> AR_head_frame_law_cf segs B ->
forall ly S Hp W mem md p, ARcf segs B ly S Hp W mem md -> In p Hp -> cf_head mod 8 = 0 ->
forall g, g mod 8 = 0 -> p <= g < p + cf_head -> ashadow B ly S g = Some 0.
Proof.
intros LAWS HF ly S Hp W mem md p H Hin A8 g G8 Gr.
pose proof H as (M & _).
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M)) as LV.
pose proof (LV p Hin) as HL.
destruct (hp_live_ablock ly S p HL) as (n & Hb & Hn).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n H Hb) as (P16 & _).
pose proof (p8_of_p16 p P16) as P8.
pose proof (arcf_img ly S Hp W mem md H) as IMG.
pose proof (amc_shadow _ _ _ _ _ M) as SH.
(* For a head granule h of p: its shadow byte is in range, in the band, and not hidden in mem. *)
assert (PH : forall h v, h mod 8 = 0 -> p <= h < p + cf_head -> ashadow B ly S h = Some v ->
hs_in p (bv_unsigned (Z_to_bv 64 (shadow_addr h))) = true /\ w_H W (Z_to_bv 64 (shadow_addr h)) = false /\
0 <= shadow_addr h < 2 ^ 64).
{ intros h v H8 Hr Hv. destruct (live_head_bounds LAWS ly S Hp W mem md p h H HL Hr) as (_ & _ & R & _ & IB).
  rewrite (wz_hp _ R). split; [apply hs_in_iff, head_shadow_iff; auto|]. split; [|exact R].
  destruct (w_H W (Z_to_bv 64 (shadow_addr h))) eqn:Hh; [|reflexivity]. exfalso.
  pose proof (SH h v H8 Hv) as X. rewrite (aview_band_hidden_hp _ _ _ IMG IB Hh) in X. discriminate X. }
(* Outside p's head, a granule of the head of q in Hp is the head of q in remove p Hp. *)
assert (OQ : forall h, h mod 8 = 0 -> in_head Hp h = true -> ~ (p <= h < p + cf_head) ->
in_head (remove Z.eq_dec p Hp) h = true /\ 0 <= shadow_addr h < 2 ^ 64 /\ hs_in p (shadow_addr h) = false).
{ intros h H8 IH NP. apply in_head_spec in IH as (q & Hq & Hh).
  assert (Ne : q <> p) by (intros ->; exact (NP Hh)).
  destruct (live_head_bounds LAWS ly S Hp W mem md q h H (LV q Hq) Hh) as (_ & _ & R & _).
  split; [apply in_head_spec; exists q; split; [apply in_in_remove; auto | exact Hh]|]. split; [exact R|].
  destruct (hs_in p (shadow_addr h)) eqn:E; [|reflexivity]. exfalso. apply NP.
  apply hs_in_iff in E. apply (head_shadow_iff p h P8 H8 A8). exact E. }
assert (H2 : ARcf segs B ly S (remove Z.eq_dec p Hp) W (probe_mem ly S (w_H W) mem p) md).
{ apply (HF ly S Hp (remove Z.eq_dec p Hp) W mem md (probe_mem ly S (w_H W) mem p) md H).
  - apply Forall_forall. intros x Hx. apply in_remove in Hx as [Hx _]. exact (LV x Hx).
  - intros h v H8 Hv Hor.
    assert (IH : in_head Hp h = true) by (destruct Hor as [E|E]; [exact E | exact (in_head_remove_sub p Hp h E)]).
    pose proof (SH h v H8 Hv) as X. rewrite IH in X.
    destruct (Z_le_gt_dec p h) as [L1|L1]; [destruct (Z_lt_ge_dec h (p + cf_head)) as [L2|L2]|].
    + assert (NI : in_head (remove Z.eq_dec p Hp) h = false).
      { destruct (in_head (remove Z.eq_dec p Hp) h) eqn:E; [|reflexivity]. exfalso.
        apply in_head_spec in E as (q & Hq & Hh). apply in_remove in Hq as [Hq Ne].
        exact (heads_apart LAWS ly S Hp W mem md p n q h H Hb Hn (LV q Hq) Ne Hh ltac:(lia)). }
      rewrite NI. destruct (PH h v H8 ltac:(lia) Hv) as (HS & HH & R).
      rewrite (aview_byte_hp _ _ _ _ HH (probe_in ly S (w_H W) mem p _ HS HH)).
      rewrite (wz_hp _ R), (shadow_inv h H8), Hv. cbv iota beta. rewrite (wz8_hp v (ashadow_range ly S h v Hv)). reflexivity.
    + destruct (OQ h H8 IH ltac:(lia)) as (IQ & R & E). rewrite IQ.
      rewrite (aview_at_hp _ _ mem); [exact X|]. apply probe_out. rewrite (wz_hp _ R). exact E.
    + destruct (OQ h H8 IH ltac:(lia)) as (IQ & R & E). rewrite IQ.
      rewrite (aview_at_hp _ _ mem); [exact X|]. apply probe_out. rewrite (wz_hp _ R). exact E.
  - intros a Ha Hown Hnot. apply aview_at_hp. apply probe_out. rewrite (wz_hp _ Ha).
    destruct (hs_in p a) eqn:E; [|reflexivity]. exfalso. apply hs_in_iff in E.
    destruct (head_shadow_g p a P8 A8 E) as (h & H8 & Hr & ->). apply Hnot. exists h. split; [exact H8|]. split; [|reflexivity].
    rewrite in_head_app. apply orb_true_intro. left. apply in_head_spec. exists p. split; [exact Hin | exact Hr].
  - intros a Hv.
    destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [rewrite (aview_hidden_hp _ _ mem a Hh); exact Hv|].
    destruct (hs_in p (bv_unsigned (Z_to_bv 64 a))) eqn:E.
    + rewrite (aview_byte_hp _ _ _ _ Hh (probe_in ly S (w_H W) mem p _ E Hh)). discriminate.
    + rewrite (aview_at_hp _ _ mem a (probe_out ly S (w_H W) mem p _ E)). exact Hv.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros a _ Hh. apply probe_hid. exact Hh. }
destruct (alc_shadow _ _ LAWS ly S (remove Z.eq_dec p Hp) W (probe_mem ly S (w_H W) mem p) md p n H2 Hb) as [BS _].
rewrite (hd_skip_notin (remove Z.eq_dec p Hp) p (remove_In Z.eq_dec Hp p)), Z.add_0_r, Z.sub_0_r in BS.
destruct BS as (_ & _ & BS).
pose proof (head_idx_range p g P8 G8 A8 Gr) as IR.
pose proof (Z.div_le_mono cf_head (req_size n) 8 ltac:(lia) Hn) as DH.
pose proof (Z.div_le_mono (req_size n) (req_size n + 7) 8 ltac:(lia) ltac:(lia)) as DM.
specialize (BS ((g - p) / 8) ltac:(lia)).
replace ((g - p) / 8 <? req_size n / 8) with true in BS by (symmetry; apply Z.ltb_lt; lia).
replace (shadow_of_addr SHADOW_OFF p + (g - p) / 8) with (shadow_addr g) in BS by (rewrite (shadow_idx p g P8 G8); reflexivity).
destruct (live_head_bounds LAWS ly S Hp W mem md p g H HL Gr) as (_ & _ & R & _ & IB).
destruct (w_H W (Z_to_bv 64 (shadow_addr g))) eqn:Hh.
{ exfalso. rewrite (aview_band_hidden_hp _ _ _ IMG IB Hh) in BS. discriminate BS. }
assert (HS : hs_in p (bv_unsigned (Z_to_bv 64 (shadow_addr g))) = true) by (rewrite (wz_hp _ R); apply hs_in_iff, head_shadow_iff; auto).
rewrite (aview_byte_hp _ _ _ _ Hh (probe_in ly S (w_H W) mem p _ HS Hh)) in BS.
rewrite (wz_hp _ R), (shadow_inv g G8) in BS.
destruct (ashadow B ly S g) as [v|] eqn:Ev; cbv iota beta in BS.
- rewrite (wz8_hp v (ashadow_range ly S g v Ev)) in BS. injection BS as ->. reflexivity.
- rewrite (wz8_hp 1 ltac:(lia)) in BS. discriminate BS.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. The proofs of (a) - (e).                                                    *)
Lemma hp_malloc_cf_proof : AR_laws_cf segs B -> hp_malloc_cf.
Proof.
intros LAWS ly S Hp W mem md ly' S' W' mem' md' q n H H' Hb' Fr.
assert (NQ : ~ In q Hp).
{ intros Hq. pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ (proj1 H)) q Hq) as HL.
  destruct (hp_live_ablock ly S q HL) as (m & Hm & _). apply Fr. apply in_map_iff. exists (q, m). split; [reflexivity | exact Hm]. }
split; [exact NQ|].
destruct (alc_shadow _ _ LAWS ly' S' Hp W' mem' md' q n H' Hb') as [BS _].
rewrite (hd_skip_notin Hp q NQ), Z.add_0_r, Z.sub_0_r in BS. exact BS.
Qed.

(* The vis premise of AR_head_frame_law_cf for a run that keeps the memory outside a stack window
   and the head shadow bytes of p, and makes the window and those bytes present. *)
Lemma step_vis : forall (W : world segs) mem mem1 p lo hi x,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (shadow_addr p <= a < shadow_addr p + cf_head / 8) ->
aview segs (w_H W) mem1 a = aview segs (w_H W) mem a) ->
(forall a, lo <= a < hi -> aview segs (w_H W) mem1 a <> None) ->
(forall i, 0 <= i < cf_head / 8 -> aview segs (w_H W) mem1 (shadow_addr p + i) = Some x) ->
forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem1 a <> None.
Proof.
intros W mem mem1 p lo hi x FR STK P a Hv. rewrite aview_mod_hp in Hv |- *.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *. clearbody a'.
destruct (Z_lt_le_dec a' (shadow_addr p)) as [S1|S1]; [|destruct (Z_lt_le_dec a' (shadow_addr p + cf_head / 8)) as [S2|S2]].
2: { replace a' with (shadow_addr p + (a' - shadow_addr p)) by lia. rewrite P by lia. discriminate. }
all: destruct (Z_lt_le_dec a' lo) as [K1|K1]; [|destruct (Z_lt_le_dec a' hi) as [K2|K2]].
all: try (apply STK; lia).
all: rewrite FR by lia; exact Hv.
Qed.

Lemma ahead_poison_law_proof : AR_laws_cf segs B -> AR_head_frame_law_cf segs B -> ahead_poison_law.
Proof.
intros LAWS HF ly S Hp W mem md p n mem1 md1 lo hi H A8 Hb Hn Hlo Hhi FR STK P E1 E2 E3 HB.
pose proof H as (M & _).
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M)) as LV.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n H Hb) as (P16 & _).
pose proof (p8_of_p16 p P16) as P8.
apply (HF ly S Hp (p :: Hp) W mem md mem1 md1 H).
- constructor; [exact (hp_live_one ly S p n Hb Hn) | exact (amc_hp_live _ _ _ _ _ M)].
- intros g v G8 Hv Hor.
  assert (IN : in_head (p :: Hp) g = true) by (rewrite in_head_cons; destruct Hor as [E|E]; [rewrite E, orb_true_r; reflexivity | exact E]).
  rewrite IN.
  destruct (Z_le_gt_dec p g) as [L1|L1]; [destruct (Z_lt_ge_dec g (p + cf_head)) as [L2|L2]|].
  + rewrite (shadow_idx p g P8 G8). apply P. exact (head_idx_range p g P8 G8 A8 ltac:(lia)).
  + assert (IH : in_head Hp g = true).
    { rewrite in_head_cons in IN. replace ((p <=? g) && (g <? p + cf_head)) with false in IN
        by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia). exact IN. }
    pose proof (amc_shadow _ _ _ _ _ M g v G8 Hv) as SH. rewrite IH in SH.
    apply in_head_spec in IH as (q & Hq & Hg).
    destruct (live_head_bounds LAWS ly S Hp W mem md q g H (LV q Hq) Hg) as (_ & _ & R & SK & _).
    rewrite FR; [exact SH | exact R | lia |]. intros Hs. apply (head_shadow_iff p g P8 G8 A8) in Hs. lia.
  + assert (IH : in_head Hp g = true).
    { rewrite in_head_cons in IN. replace ((p <=? g) && (g <? p + cf_head)) with false in IN
        by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia). exact IN. }
    pose proof (amc_shadow _ _ _ _ _ M g v G8 Hv) as SH. rewrite IH in SH.
    apply in_head_spec in IH as (q & Hq & Hg).
    destruct (live_head_bounds LAWS ly S Hp W mem md q g H (LV q Hq) Hg) as (_ & _ & R & SK & _).
    rewrite FR; [exact SH | exact R | lia |]. intros Hs. apply (head_shadow_iff p g P8 G8 A8) in Hs. lia.
- intros a Ha Hown Hnot. apply FR; [exact Ha | |].
  + intros Hw. exact (alc_stack _ _ LAWS ly S Hp W mem md a H ltac:(lia) Hown).
  + intros Hs. apply Hnot. destruct (head_shadow_g p a P8 A8 Hs) as (g & G8 & Gr & ->).
    exists g. split; [exact G8|]. split; [|reflexivity].
    rewrite in_head_app. apply orb_true_intro. right. apply in_head_spec. exists p. split; [left; reflexivity | exact Gr].
- exact (step_vis W mem mem1 p lo hi shUserPoison FR STK P).
- exact E1.
- exact E2.
- exact E3.
- exact HB.
Qed.

Lemma ahead_unpoison_law_proof : AR_laws_cf segs B -> AR_head_frame_law_cf segs B -> ahead_unpoison_law.
Proof.
intros LAWS HF ly S Hp W mem md p mem1 md1 lo hi H A8 Hin Hlo Hhi FR STK P E1 E2 E3 HB.
pose proof H as (M & _).
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M)) as LV.
destruct (hp_live_ablock ly S p (LV p Hin)) as (n & Hb & Hn).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n H Hb) as (P16 & _).
pose proof (p8_of_p16 p P16) as P8.
pose proof (head_ashadow0 LAWS HF ly S Hp W mem md p H Hin A8) as HV.
apply (HF ly S Hp (remove Z.eq_dec p Hp) W mem md mem1 md1 H).
- apply Forall_forall. intros x Hx. apply in_remove in Hx as [Hx _]. exact (LV x Hx).
- intros g v G8 Hv Hor.
  assert (IH : in_head Hp g = true) by (destruct Hor as [E|E]; [exact E | exact (in_head_remove_sub p Hp g E)]).
  destruct (Z_le_gt_dec p g) as [L1|L1]; [destruct (Z_lt_ge_dec g (p + cf_head)) as [L2|L2]|].
  + assert (NI : in_head (remove Z.eq_dec p Hp) g = false).
    { destruct (in_head (remove Z.eq_dec p Hp) g) eqn:E; [|reflexivity]. exfalso.
      apply in_head_spec in E as (q & Hq & Hg). apply in_remove in Hq as [Hq Ne].
      exact (heads_apart LAWS ly S Hp W mem md p n q g H Hb Hn (LV q Hq) Ne Hg ltac:(lia)). }
    rewrite NI. rewrite (HV g G8 ltac:(lia)) in Hv. injection Hv as <-.
    rewrite (shadow_idx p g P8 G8). apply P. exact (head_idx_range p g P8 G8 A8 ltac:(lia)).
  + pose proof (amc_shadow _ _ _ _ _ M g v G8 Hv) as SH. rewrite IH in SH.
    apply in_head_spec in IH as (q & Hq & Hg).
    assert (Ne : q <> p) by (intros ->; lia).
    assert (IQ : in_head (remove Z.eq_dec p Hp) g = true) by (apply in_head_spec; exists q; split; [apply in_in_remove; auto | exact Hg]).
    rewrite IQ.
    destruct (live_head_bounds LAWS ly S Hp W mem md q g H (LV q Hq) Hg) as (_ & _ & R & SK & _).
    rewrite FR; [exact SH | exact R | lia |]. intros Hs. apply (head_shadow_iff p g P8 G8 A8) in Hs. lia.
  + pose proof (amc_shadow _ _ _ _ _ M g v G8 Hv) as SH. rewrite IH in SH.
    apply in_head_spec in IH as (q & Hq & Hg).
    assert (Ne : q <> p) by (intros ->; lia).
    assert (IQ : in_head (remove Z.eq_dec p Hp) g = true) by (apply in_head_spec; exists q; split; [apply in_in_remove; auto | exact Hg]).
    rewrite IQ.
    destruct (live_head_bounds LAWS ly S Hp W mem md q g H (LV q Hq) Hg) as (_ & _ & R & SK & _).
    rewrite FR; [exact SH | exact R | lia |]. intros Hs. apply (head_shadow_iff p g P8 G8 A8) in Hs. lia.
- intros a Ha Hown Hnot. apply FR; [exact Ha | |].
  + intros Hw. exact (alc_stack _ _ LAWS ly S Hp W mem md a H ltac:(lia) Hown).
  + intros Hs. apply Hnot. destruct (head_shadow_g p a P8 A8 Hs) as (g & G8 & Gr & ->).
    exists g. split; [exact G8|]. split; [|reflexivity].
    rewrite in_head_app. apply orb_true_intro. left. apply in_head_spec. exists p. split; [exact Hin | exact Gr].
- exact (step_vis W mem mem1 p lo hi 0 FR STK P).
- exact E1.
- exact E2.
- exact E3.
- exact HB.
Qed.

Lemma realloc_cf_hp_post_ok_proof : AR_laws_cf segs B -> realloc_cf_hp_post_ok.
Proof.
intros LAWS ly S Hp W mem md ly' S' W' mem' md' p q n H Hq Fq Gp SV.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ (proj1 H))) as HL.
assert (NQ : ~ In q (remove Z.eq_dec p Hp)).
{ intros Hr. apply in_remove in Hr as [Hr _]. destruct (hp_live_ablock ly S q (HL q Hr)) as (m & Hm & _).
  apply Fq. apply in_map_iff. exists (q, m). split; [reflexivity | exact Hm]. }
split; [|split; [|split; [exact NQ|]]].
- apply Forall_forall. intros x Hx. apply in_remove in Hx as [Hx Ne].
  destruct (hp_live_ablock ly S x (HL x Hx)) as (m & Hm & Hc).
  exact (hp_live_one ly' S' x m (SV (x, m) Hm Ne) Hc).
- intros Hin F. pose proof (proj1 (Forall_forall _ _) F p Hin) as Hp'.
  destruct (hp_live_ablock ly' S' p Hp') as (m & Hm & _).
  apply Gp. apply in_map_iff. exists (p, m). split; [reflexivity | exact Hm].
- intros H'. destruct (alc_shadow _ _ LAWS ly' S' (remove Z.eq_dec p Hp) W' mem' md' q n H' Hq) as [BS _].
  rewrite (hd_skip_notin _ q NQ), Z.add_0_r, Z.sub_0_r in BS. exact BS.
Qed.

Lemma realloc_cf_hp_post_null_proof : AR_laws_cf segs B -> AR_head_frame_law_cf segs B -> realloc_cf_hp_post_null.
Proof.
intros LAWS HF stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' p n_old H Hpost Hb Hb' NS.
destruct Hpost as (H' & _ & _ & _ & _ & FRp & _).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n_old H Hb) as (_ & P4k & Pce & _ & Pbytes & _).
destruct (alc_blocks _ _ LAWS ly' S' Hp W' mem' md' p n_old H' Hb') as (P16 & _ & _ & _ & Pbytes' & _).
pose proof (@ASAN_CEIL_range _) as [CR _]. unfold ASAN_CEIL in CR.
split; [|split].
- intros a Ha. destruct (NS a Ha) as [N1 N2].
  apply FRp; [lia | exact (proj2 (Pbytes a Ha)) | exact (proj2 (Pbytes' a Ha)) | exact N1 | exact N2].
- exact (proj1 (alc_shadow _ _ LAWS ly' S' Hp W' mem' md' p n_old H' Hb')).
- intros A8 Hin i Hi.
  pose proof (p8_of_p16 p P16) as P8.
  assert (G8 : (p + 8 * i) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_add by lia; exact P8).
  assert (Gr : p <= p + 8 * i < p + cf_head)
    by (pose proof A8 as A8'; apply Z.mod_divide in A8' as [c Hc]; [|lia]; rewrite Hc in Hi |- *; rewrite Z.div_mul in Hi by lia; lia).
  pose proof (head_ashadow0 LAWS HF ly' S' Hp W' mem' md' p H' Hin A8 (p + 8 * i) G8 Gr) as Hv.
  pose proof (amc_shadow _ _ _ _ _ (proj1 H') (p + 8 * i) 0 G8 Hv) as SH.
  replace (in_head Hp (p + 8 * i)) with true in SH by (symmetry; apply in_head_spec; exists p; split; [exact Hin | exact Gr]).
  rewrite (shadow_idx p (p + 8 * i) P8 G8) in SH. replace (p + 8 * i - p) with (i * 8) in SH by ring.
  rewrite Z.div_mul in SH by lia. exact SH.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 8. The shadow byte after a block's head is visible when the block IS its head *)
(*    (req_size n = cf_head) and cf_head <= 16. Both shadow calls read the shadow *)
(*    byte of p + cf_head. cf_head is granule-aligned (cf_head_al), so n is 8 or  *)
(*    16 and the block is class 1 (chunk_class 8 = chunk_class 16 = 1,            *)
(*    class_size 1 = 32, rz_size 8 = rz_size 16 = 16: p is the chunk base + 16),  *)
(*    so p + cf_head lies in [region_base ly 1, region_base ly 1 +                *)
(*    kFreeArrayOffset] (cfacts_cf's PPrim arm: x + 32 <= rg_alloc_user <=        *)
(*    rg_mapped_user <= kFreeArrayOffset). ahs_pres gives the byte: its address   *)
(*    is in the high shadow band, no client byte (block and frame bytes are       *)
(*    application addresses; a frame's shadow is the fake stack's, disjoint from  *)
(*    the primary reservation, lo_disj) and in no vis0 zone                       *)
(*    (frontier_not_vis0_cf). The band, abudget_ok_cf's third conjunct, makes it  *)
(*    visible. Without cf_head <= 16 the statement fails for a larger head: at    *)
(*    cf_head = 48 the block is class 2 and p + cf_head can be class 2's end, off  *)
(*    the band. The preset form, at cf_head = 16, is CfApiPreset.poison_next_vis_cf. *)
Lemma poison_next_vis_cf_le16 : forall ly S Hp (W : world segs) mem md p n,
ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> req_size n = cf_head -> cf_head <= 16 ->
aview segs (w_H W) mem (shadow_addr (p + cf_head)) <> None.
Proof.
intros ly S Hp W mem md p n (M & _ & (_ & _ & BAND) & _ & (HPRES & _)) Hb Hrq Hh.
pose proof cf_head_nonneg as H0. pose proof cf_head_al as A8.
assert (HN : n = 8 \/ n = 16).
{ revert Hrq. unfold req_size. destruct (Z.eqb_spec n 0) as [_|Hn0]; intros Hrq; cbv beta iota in Hrq.
  - rewrite <- Hrq in A8. vm_compute in A8. discriminate A8.
  - apply Z.mod_divide in A8 as [c Hc]; [|lia]. lia. }
assert (CK : chunk_class n = 1 /\ rz_size n = 16 /\ from_primary n = true)
by (destruct HN as [-> | ->]; (split; [reflexivity | split; reflexivity])).
destruct CK as (CK1 & CK2 & CK3).
pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (lo_space_in _ LO) as [S1 S2]. pose proof (lo_high _ LO) as [Hi1 Hi2].
pose proof (@ASAN_CEIL_range _) as [CR _].
apply ablocks_In_hp in Hb as (k & Hk & _ & Hpk & Hr).
pose proof (YG0scf.chunk_facts_cf B ly S Hp _ k M Hk) as (_ & _ & _ & G4 & _ & _ & _ & _ & GG).
unfold ck_rz in G4. rewrite Hr, CK2 in G4.
revert GG. destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; intros GG; [destruct GG | | | destruct GG].
2: { destruct GG as (_ & Fp & _). rewrite Hr, CK3 in Fp. discriminate Fp. }
cbv beta iota zeta in GG. destruct GG as (_ & _ & Cc & _ & Cb & X0 & _ & Xa & Xm1 & Xm2).
rewrite Hr, CK1 in Cc. rewrite <- Cc in Cb, X0, Xa, Xm1, Xm2.
replace (class_size 1) with 32 in Xa by reflexivity.
set (g := p + cf_head) in *.
assert (Hg : region_base ly 1 <= g <= region_base ly 1 + kFreeArrayOffset) by (unfold g; lia).
assert (Rg : kHighMemBeg <= g /\ g + 8 <= ASAN_CEIL).
{ unfold region_base, region_off in Hg. change (Z.shiftl 1 32) with 4294967296 in Hg.
  unfold kFreeArrayOffset, kPrimResvSize, kSpaceSize in *. lia. }
(* the band makes the byte visible *)
assert (HV : w_H W (Z_to_bv 64 (shadow_addr g)) = false).
{ refine (BAND (shadow_addr g) _). unfold shadow_addr. split; apply Z.add_le_mono_l; apply Z.div_le_mono; lia. }
(* ahs_pres gives the byte *)
assert (HM : mem (Z_to_bv 64 (shadow_addr g)) <> None).
{ refine (HPRES (shadow_addr g) _ _ _).
  - unfold in_band_rw. right. exact (shadow_addr_band g (proj1 Rg) (proj2 Rg)).
  - pose proof (shadow_addr_band g (proj1 Rg) (proj2 Rg)) as SB.
    assert (NA : ~ app_addr (shadow_addr g)) by (unfold app_addr, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    intros [(k' & Hk' & _ & Hin')|([cid' pos'] & Hcp & [Hin'|Hin'])].
    + pose proof (YG0scf.chunk_facts_cf B ly S Hp _ k' M Hk') as (K1 & _ & _ & K4 & K5 & _ & _ & K8 & _).
      unfold ck_n in Hin'. rewrite K4 in Hin'.
      apply NA. apply (in_app_addr _ _ _ K1). lia.
    + destruct (YG0scf.frame_facts_cf B ly S Hp _ cid' pos' M Hcp) as (C0 & _ & F3 & _ & _ & F6 & F7 & _).
      apply NA. apply (in_app_addr _ _ _ F3). unfold in_zr, frame_addr in Hin'. cbn [fst snd] in Hin'.
      unfold kFakeFramesOff in F6. lia.
    + destruct (YG0scf.frame_facts_cf B ly S Hp _ cid' pos' M Hcp) as (C0 & _ & _ & _ & _ & F6 & F7 & _).
      pose proof (lo_disj _ LO) as PD. unfold static_extents, owned_extents in PD. cbn [app pairwise] in PD.
      destruct PD as [F0 _]. rewrite !Forall_cons_iff in F0. destruct F0 as (_ & _ & DF & _).
      unfold zdisjoint in DF. cbn [fst snd] in DF.
      unfold in_zr, frame_addr, shadow_addr in Hin'. cbn [fst snd] in Hin'.
      unfold region_base, region_off in Hg. change (Z.shiftl 1 32) with 4294967296 in Hg.
      unfold kFakeFramesOff, kFreeArrayOffset, kPrimResvSize, kSpaceSize in *.
      #[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      #[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - right. exact (frontier_not_vis0_cf ly g LO Hg). }
unfold aview, mbyte, mrestrict. rewrite HV.
destruct (mem (Z_to_bv 64 (shadow_addr g))) as [b|] eqn:E.
- cbn. discriminate.
- exfalso. first [exact (HM E) | exact (HM eq_refl)].
Qed.

End R.
End H.
