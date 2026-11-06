(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: what acall_post_cf (YG0dcf.v:57-65) gives about PRESENCE (apresent, YG0n.v:28-29).
   The frame clause keeps the VIEW (aview) of every byte outside aowned B ly S, aowned B ly' S', ascratch and E.
   A kept view is a kept presence only off the loaded segments: aview falls back to seg_rom when the memory has
   no byte, so on a segment byte the frame clause cannot tell a present byte from a lost one.
   - acall_post_cf_presence: a byte present before the call is present after it when it is outside the
     segments, outside aowned B ly S and aowned B ly' S', outside the errno cell and outside E.
     The stack window [spZ regs - stk, spZ regs) is present after the call in every case (the last clause).
   - Owned bytes: the frame clause says nothing. The post's ARcf makes every range of aareas S' visible
     (amc_areas), so such a byte is present after the call off the segments, whether present before or not.
     In particular every secondary extent of a chunk still in st_chunks S' (allocated or quarantined) is
     present after the call (acall_post_cf_sec_present).
   - What is NOT kept: the secondaries a free's quarantine recycle unmaps (sec_dealloc, YG00.v:473-486, on
     earlier-freed quarantined chunks). Their extents are in sec_extents ly S (built from every chunk,
     quarantined included) and are not client bytes, so they are aowned B ly S: they fall under the owned
     exception, and their bytes are really absent after the call.
   - The RAW frame (the last conjunct of malloc_leaf_cf / malloc_cf_null_post / free_leaf_cf, YG0dcf.v, and of
     realloc_leaf_cf, YGcfRealloc.v) keeps presence on EVERY byte outside both owned sets, the errno cell and E,
     image bytes included (acall_post_cf_presence_raw), so the image-byte presence a site rule states follows at
     each leaf's exception set (free_post_img_presence, malloc_post_img_presence).
   - errno_view_of_raw: the leaves' raw errno conjunct gives the VIEW form when errno's bytes lie in a loaded
     segment, where every world's hidden map is false (w_Hoff; cfp_img_unhidden). The post does not say that errno
     is a segment byte: the caller supplies it.
   No cgif file and no cf file is edited. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
(* stdpp, through the LPS modules, shadows Forall_forall and Exists_exists; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. View and presence off the segments.                                         *)
Lemma cfp_seg_rom_none : forall segs a, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> seg_rom segs (Z_to_bv 64 a) = None.
Proof.
intros segs a Ha Hn. unfold seg_rom, memory_read.
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). cbn [Z.of_N].
destruct (find_segment segs a 1) as [sg|] eqn:E; [|reflexivity].
exfalso. apply Hn. apply find_segment_some_spec in E as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

Lemma cfp_view_of_present : forall segs H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof.
intros segs H mem a [Hh (b & Hb)]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

Lemma cfp_present_of_view : forall segs H mem a, seg_rom segs (Z_to_bv 64 a) = None ->
aview segs H mem a <> None -> apresent H mem a.
Proof.
intros segs H mem a Hr Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
destruct (H (Z_to_bv 64 a)) eqn:EH; [rewrite Hr in Hv; exfalso; apply Hv; reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|] eqn:EM; [split; [reflexivity | exists b; reflexivity]|].
rewrite Hr in Hv. exfalso. apply Hv. reflexivity.
Qed.

(* The post's ledger puts every segment inside ly_img (alc_img), so ~ in_zr a (ly_img ly) is enough. *)
Lemma cfp_not_img : forall segs ly S md a, ALedger_cf segs ly S md -> ~ in_zr a (ly_img ly) -> ~ in_img segs a.
Proof.
intros segs ly S md a L Hn (sg & Hsg & Hr). pose proof (alc_img _ _ _ _ L sg Hsg). apply Hn. unfold in_zr. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. Unowned bytes: presence before implies presence after.                      *)
Theorem acall_post_cf_presence : forall segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) -> ~ E a ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P a Ha Hi N1 N2 NE0 NE HP.
destruct P as (_ & _ & _ & _ & _ & FR & STK).
assert (C : (spZ regs - stk <= a < spZ regs) \/ ~ ascratch B stk regs a).
{ destruct (Z_le_gt_dec (spZ regs - stk) a); destruct (Z_lt_ge_dec a (spZ regs)); try (left; lia);
  right; intros [X|X]; first [lia | exact (NE0 X)]. }
destruct C as [C|NS]; [exact (STK a C)|].
apply cfp_present_of_view with (segs := segs); [exact (cfp_seg_rom_none segs a Ha Hi)|].
rewrite (FR a Ha N1 N2 NS NE). exact (cfp_view_of_present segs _ _ a HP).
Qed.

(* The same with the image test the walks usually carry: off ly_img. *)
Corollary acall_post_cf_presence_img : forall segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_zr a (ly_img ly) ->
~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) -> ~ E a ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P a Ha Hi.
pose proof P as ((_ & L & _) & LE & _).
destruct LE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eimg & _).
apply (acall_post_cf_presence segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P a Ha).
apply (cfp_not_img segs ly' S' md' a L). rewrite Eimg. exact Hi.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. Owned bytes: every area of the post state is present after the call.        *)
Lemma acall_post_cf_areas_present : forall segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
forall r i, In r (aareas S') -> 0 <= i < snd r ->
0 <= aeval B ly' (fst r) + i < 2 ^ 64 -> ~ in_img segs (aeval B ly' (fst r) + i) ->
apresent (w_H W') mem' (aeval B ly' (fst r) + i).
Proof.
intros segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P r i Hr Hi Ha Hn.
destruct P as ((M & _) & _).
apply cfp_present_of_view with (segs := segs); [exact (cfp_seg_rom_none segs _ Ha Hn)|].
exact (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) r Hr i Hi).
Qed.

Lemma cfp_sec_in_areas : forall B ly S e, In e (sec_extents ly S) ->
exists r, In r (aareas S) /\ aeval B ly (fst r) = fst e /\ snd r = snd e.
Proof.
intros B ly S e He. unfold sec_extents in He. apply in_flat_map in He as (k & Hk & He).
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; try destruct He as [<-|[]]; try destruct He.
exists (ASec r 0, sec_map_size (ck_req k)). split; [|cbn [fst snd aeval]; split; lia].
unfold aareas. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
apply in_flat_map. exists k. split; [exact Hk|]. rewrite Eb. left. reflexivity.
Qed.

(* Every secondary extent of a chunk still in st_chunks S', allocated or quarantined, is present after. *)
Lemma acall_post_cf_sec_present : forall segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
forall a, Exists (in_zr a) (sec_extents ly' S') -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
apresent (w_H W') mem' a.
Proof.
intros segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P a Hx Ha Hn.
apply Exists_exists in Hx as (e & He & Hz). unfold in_zr in Hz.
destruct (cfp_sec_in_areas B ly' S' e He) as (r & Hr & E1 & E2).
replace a with (aeval B ly' (fst r) + (a - fst e)) in Ha, Hn |- * by lia.
apply (acall_post_cf_areas_present segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P r);
[exact Hr | lia | exact Ha | exact Hn].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The raw frame: presence on every byte outside both owned sets, errno and E.  *)
Theorem acall_post_cf_presence_raw : forall segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md',
acall_post_cf segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' S' (bv_unsigned x) ->
 ~ ascratch B stk regs (bv_unsigned x) -> ~ E (bv_unsigned x) -> mem' x = mem x) ->
forall a, 0 <= a < 2 ^ 64 ->
~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) -> ~ E a ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' P RAW a Ha N1 N2 NE0 NE [Hh (b & Hb)].
pose proof P as (_ & _ & WLE & _ & _ & _ & STK).
destruct (Z_le_gt_dec (spZ regs - stk) a) as [L1|L1]; [destruct (Z_lt_ge_dec a (spZ regs)) as [L2|L2]|].
- exact (STK a (conj L1 L2)).
- assert (E1 : bv_unsigned (Z_to_bv 64 a) = a)
    by (rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
  assert (NS : ~ ascratch B stk regs a) by (intros [X|X]; [lia | exact (NE0 X)]).
  split.
  + destruct (w_H W' (Z_to_bv 64 a)) eqn:E'; [|reflexivity]. rewrite (WLE _ E') in Hh. discriminate.
  + exists b. rewrite RAW; [exact Hb | rewrite E1; exact N1 | rewrite E1; exact N2 | rewrite E1; exact NS | rewrite E1; exact NE].
- assert (E1 : bv_unsigned (Z_to_bv 64 a) = a)
    by (rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia); reflexivity).
  assert (NS : ~ ascratch B stk regs a) by (intros [X|X]; [lia | exact (NE0 X)]).
  split.
  + destruct (w_H W' (Z_to_bv 64 a)) eqn:E'; [|reflexivity]. rewrite (WLE _ E') in Hh. discriminate.
  + exists b. rewrite RAW; [exact Hb | rewrite E1; exact N1 | rewrite E1; exact N2 | rewrite E1; exact NS | rewrite E1; exact NE].
Qed.

(* The image-byte presence of a free site rule (port-reply's afree_cf_rule / afree_null_cf_rule, W_journal.v, their
   last conjunct) at free_leaf_cf's exception set, for every p: the freed range is excepted only when p <> PNull
   (free_leaf_cf's E), so at p = PNull nothing is excepted (free_post_img_presence_null). The image lies below
   kLowMemEnd (the donor's segs_low). *)
Corollary free_post_img_presence : forall segs B ly S Hp W regs mem md (p : sptr) n ly' S' W' regs' mem' md',
acall_post_cf segs B ASTACK ly S Hp W regs mem md
  (fun a => p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ly' S' W' regs' mem' md' ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' S' (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x) ->
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
forall a, in_img segs a -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B ly S Hp W regs mem md p n ly' S' W' regs' mem' md' P RAW LOW a Hi N1 N2 NE0 NB HP.
pose proof (LOW a Hi) as La. unfold kLowMemEnd in La.
apply (acall_post_cf_presence_raw segs B ASTACK ly S Hp W regs mem md _ ly' S' W' regs' mem' md' P RAW a);
[lia | exact N1 | exact N2 | exact NE0 | exact NB | exact HP].
Qed.

(* free(NULL): no range is excepted. *)
Corollary free_post_img_presence_null : forall segs B ly S Hp W regs mem md n ly' S' W' regs' mem' md',
acall_post_cf segs B ASTACK ly S Hp W regs mem md
  (fun a => PNull <> PNull /\ sptr_addr B ly PNull <= a < sptr_addr B ly PNull + req_size n) ly' S' W' regs' mem' md' ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' S' (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ (PNull <> PNull /\ sptr_addr B ly PNull <= bv_unsigned x < sptr_addr B ly PNull + req_size n) -> mem' x = mem x) ->
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
forall a, in_img segs a -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B ly S Hp W regs mem md n ly' S' W' regs' mem' md' P RAW LOW a Hi N1 N2 NE0 HP.
exact (free_post_img_presence segs B ly S Hp W regs mem md PNull n ly' S' W' regs' mem' md' P RAW LOW a Hi N1 N2 NE0
  (fun H => proj1 H eq_refl) HP).
Qed.

(* The same at malloc_leaf_cf's exception set: the new block q and the errbuf extents before and after. *)
Corollary malloc_post_img_presence : forall segs B ly S Hp W regs mem md (q : sptr) n ly' S' W' regs' mem' md',
acall_post_cf segs B ASTACK ly S Hp W regs mem md
  (fun a => (q <> PNull /\ sptr_addr B ly' q <= a < sptr_addr B ly' q + req_size n)
    \/ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S')) ly' S' W' regs' mem' md' ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly' S' (bv_unsigned x) ->
 ~ ascratch B ASTACK regs (bv_unsigned x) ->
 ~ ((q <> PNull /\ sptr_addr B ly' q <= bv_unsigned x < sptr_addr B ly' q + req_size n)
    \/ Exists (in_zr (bv_unsigned x)) (xs_cf ly S ++ xs_cf ly' S')) -> mem' x = mem x) ->
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
forall a, in_img segs a -> ~ aowned B ly S a -> ~ aowned B ly' S' a -> ~ (as_errno B <= a < as_errno B + 4) ->
~ (sptr_addr B ly' q <= a < sptr_addr B ly' q + req_size n) -> ~ Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' S') ->
apresent (w_H W) mem a -> apresent (w_H W') mem' a.
Proof.
intros segs B ly S Hp W regs mem md q n ly' S' W' regs' mem' md' P RAW LOW a Hi N1 N2 NE0 NB NX HP.
pose proof (LOW a Hi) as La. unfold kLowMemEnd in La.
apply (acall_post_cf_presence_raw segs B ASTACK ly S Hp W regs mem md _ ly' S' W' regs' mem' md' P RAW a);
[lia | exact N1 | exact N2 | exact NE0 | intros [[_ X] | X]; [exact (NB X) | exact (NX X)] | exact HP].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. errno: the raw conjunct in the VIEW form.                                     *)
(* A segment byte is visible in every world (w_Hoff, YA0n.v). *)
Lemma cfp_img_unhidden : forall segs (W : world segs) a, 0 <= a < 2 ^ 64 -> in_img segs a ->
w_H W (Z_to_bv 64 a) = false.
Proof.
intros segs [H A HO HA] a Ha (sg & Hsg & H1 & H2). cbn [w_H].
destruct (H (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
pose proof (HO _ E) as N.
rewrite Z_to_bv_unsigned, bv_wrap_small in N by (change (bv_modulus 64) with (2 ^ 64); lia).
assert (Hlt : (a + 1 <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg))%Z) by lia.
exact (find_segment_none_spec segs a 1 N sg Hsg (conj H1 Hlt)).
Qed.

(* port-reply's errno conjunct (W_journal.v: errno's four bytes keep their view) from a leaf's raw errno conjunct.
   The extra premise, that errno's bytes are segment bytes, is not in the post (the donor's api_env gives it). *)
Corollary errno_view_of_raw : forall segs B (W W' : world segs) (mem mem' : word -> option byte),
(forall i, 0 <= i < 4 -> 0 <= as_errno B + i < 2 ^ 64 /\ in_img segs (as_errno B + i)) ->
(forall i, 0 <= i < 4 -> mem' (w64 (as_errno B + i)) = mem (w64 (as_errno B + i))) ->
forall i, 0 <= i < 4 -> aview segs (w_H W') mem' (as_errno B + i) = aview segs (w_H W) mem (as_errno B + i).
Proof.
intros segs B W W' mem mem' HI HR i Hi. destruct (HI i Hi) as [Ha Hm].
pose proof (HR i Hi) as E. cbv delta [YG0d.w64 YG0n.w64] beta in E.
unfold aview, mbyte, mrestrict.
rewrite (cfp_img_unhidden segs W' _ Ha Hm), (cfp_img_unhidden segs W _ Ha Hm), E. reflexivity.
Qed.

End P.
