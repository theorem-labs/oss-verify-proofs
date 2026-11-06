(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 267 of its 331 lines of code are new or changed and 714 lines of the source are left out. *)
(* fuzz_preset, slice S6 (WalkS6): the IMAGE-FREE pieces of the pj_* walks (pj_get_str, pj_get, pj_string, pj_free, ...),
   generic over the program listing {L} and its image facts {PA : PAImg L}, so image A's walks (lib/A/Prog/S6Pj*.v) and
   image B's (lib/B/Prog) import ONE copy. No address, no image fact, no listing slot: byte / node / register / shadow
   arithmetic over PRH_Reader.v's tree predicates and the engine's stretch facts, and four tactics.
   Numerals: 56 / 24 / 16 / 8 / 4 (LENGTH: node, node fields, word, word part), 8 / 3 (granule), 2 ^ 44 / 2 ^ 46 / 2 ^ 47
   (DERIVED: shadow and stack bounds), the tags 0 .. 6 of PjTree.tag, register numbers 2 / 3 / 4 / 8 / 9 / 18 .. 27
   (DERIVED: acallee_saved). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- no state ---- *)
Lemma gs_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
(* a byte off a stretch's write windows keeps its value *)
Lemma gs_mr_keep : forall E' rs (m m' : word -> option byte) a,
  frame_of E' rs m m' -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros E' rs m m' a HF Hn Ha. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.
(* the callee-saved registers other than sp and s0 (YG0d.v acallee_saved) *)
Definition gs_kept : list (bv 5) := map (Z_to_bv 5) [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma gs_aregs : forall (regs regs1 regs2 regsF : bvmap 5 word),
  (forall r : bv 5, In r gs_kept -> getr regs1 r = getr regs r) ->
  aregs_preserved regs1 regs2 ->
  (forall r : bv 5, In r gs_kept -> getr regsF r = getr regs2 r) ->
  getr regsF 2%bv = getr regs 2%bv -> getr regsF 8%bv = getr regs 8%bv ->
  aregs_preserved regs regsF.
Proof.
intros regs regs1 regs2 regsF H1 H2 H3 E2 E8 r Hr.
assert (Hk : r = 2 \/ r = 8 \/ In (Z_to_bv 5 r) gs_kept).
{ unfold acallee_saved in Hr. unfold gs_kept.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
    [left; reflexivity | right; right; apply in_map; cbn; tauto | right; right; apply in_map; cbn; tauto
    | right; left; reflexivity | right; right; apply in_map; cbn; tauto |].
  right; right. apply in_map.
  assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H as [-> | H]; [cbn; tauto|]). subst r. cbn; tauto. }
destruct Hk as [-> | [-> | Hk]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact E2.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact E8.
- rewrite (H3 _ Hk), (H2 r Hr), (H1 _ Hk). reflexivity.
Qed.
(* the type word a load reads (env atom n), sign-extended from 32 bits, is the tag *)
Lemma gs_tagU : forall (E' : env) n v, ew E' n = Z_to_bv 64 (tag v) -> U E' (SExt true 32 (SOff n 0)) = tag v.
Proof.
intros E' n v H. rewrite U_SExt, (U_atom E' n (tag v) H) by (destruct v; cbn [tag]; lia).
destruct v; vm_compute; reflexivity.
Qed.
Lemma gs_tag4 : forall v, tag v = 4 -> exists s, v = JStr s.
Proof. intros v H. destruct v; cbn [tag] in H; try discriminate H. exists s. reflexivity. Qed.
Lemma gs_tag6 : forall v, tag v = 6 -> exists members, v = JObj members.
Proof. intros v H. destruct v; cbn [tag] in H; try discriminate H. exists members. reflexivity. Qed.
Lemma gs_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma gs_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.

(* the found member's address the code computes, kids - (-56 i) (the engine's add of a times -1); transcribed from
   fuzz_state's lib/A/FSW_pj_get.v pg_U_hit (cold/rd5-pjget 703aaa74bca), any two atoms *)
Lemma gs_U_hit : forall E na nb i kids, ew E na = Z_to_bv 64 (-56 * i) -> ew E nb = Z_to_bv 64 kids ->
  0 <= kids < 2 ^ 64 -> 0 <= kids + 56 * i < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff na 0) (SLit (-1))) (SOff nb 0)) = kids + 56 * i.
Proof.
intros E na nb i kids Ha Hb Hk Hki. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E nb kids Hb Hk), U_SLit, U_SOff, Ha, Z.add_0_r, Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_mod_idemp_l by lia. rewrite Z.mod_mod by lia.
rewrite <- (Z.add_mod_idemp_l ((-56 * i) mod 2 ^ 64 * (-1 mod 2 ^ 64)) kids (2 ^ 64)) by lia.
rewrite <- Z.mul_mod by lia. rewrite Z.add_mod_idemp_l by lia.
replace (-56 * i * -1 + kids) with (kids + 56 * i) by lia.
apply Z.mod_small. exact Hki.
Qed.
(* a register value an offset atom names, as a literal *)
Lemma gs_denot_off : forall E n w c, ew E n = Z_to_bv 64 w -> sv_denot E (SOff n c) = Z_to_bv 64 (w + c).
Proof.
intros E n w c Hn. apply bv_eq. rewrite denot_SOff, Hn, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation SEGS := (@pa_segs _ L PA).

(* a set of bytes whose words keep their values agrees in the reader's sense (PRH_Reader.v pj_agreeR) *)
Lemma gs_agree : forall (m m' : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> pj_agreeR SEGS m m' X.
Proof.
intros m m' X H x Hx. unfold mbyte, writable_at. rewrite <- (H x Hx) at 1.
split; [reflexivity|]. unfold wview. rewrite (H x Hx). auto.
Qed.
(* the 8 bytes at a fix the word they hold (two rd_u64 of one cell read the same value) *)
Lemma gs_val8_uniq : forall (m : word -> option byte) a v v',
  val_mem SEGS m a 8 v -> val_mem SEGS m a 8 v' -> 0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros m a v v' H H' Hv Hv'.
assert (Bk : forall k, (k < 8)%nat -> YO0f.le_byte v 8 k = YO0f.le_byte v' 8 k).
{ intros k Hk. pose proof (H k Hk) as A. pose proof (H' k Hk) as A'. rewrite A in A'. injection A' as Eb.
  change (bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte v' 8 k))) in Eb.
  rewrite !Z_to_bv_unsigned in Eb. unfold bv_wrap, bv_modulus in Eb.
  change (2 ^ Z.of_N 8) with 256 in Eb. unfold YO0f.le_byte in *. rewrite !Z.mod_mod in Eb by lia. exact Eb. }
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 64) as [Hl|Hl].
- pose proof (Z.div_pos i 8 Hi ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod i 8 ltac:(lia)) as Hdm.
  assert (Hd8 : i / 8 < 8) by (apply Z.div_lt_upper_bound; lia).
  assert (Hk : (Z.to_nat (i / 8) < 8)%nat) by lia.
  pose proof (Bk _ Hk) as B0. unfold YO0f.le_byte in B0. rewrite Z2Nat.id in B0 by lia.
  replace (8 * Z.of_nat 8) with 64 in B0 by reflexivity. rewrite !(Z.mod_small _ (2 ^ 64)) in B0 by lia.
  assert (T : forall x, Z.testbit x i = Z.testbit (Z.shiftr x (8 * (i / 8)) mod 256) (i mod 8)).
  { intros x. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. f_equal. lia. }
  rewrite !T, B0. reflexivity.
- rewrite <- (Z.mod_small v (2 ^ 64)) by lia. rewrite <- (Z.mod_small v' (2 ^ 64)) by lia.
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* every node has a header whose type word is its tag *)
Lemma gs_node_hdr : forall m lblk p t D, pj_nodeR SEGS m lblk p t D ->
  exists num str kids keys n cap, pj_hdrR SEGS m p (tag t) num str kids keys n cap.
Proof.
intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _); exists num, str, kids, keys, n, cap; exact Hh.
Qed.
(* the subtree's blocks of a node are the block predicate's (an item / a member names its own) *)
Lemma gs_items_in : forall (P : Z -> jv -> list (Z * Z) -> Prop) l a D b,
  pj_itemsR P a l D -> In b D -> exists i u D1, nth_error l i = Some u /\ P (a + 56 * Z.of_nat i) u D1 /\ In b D1.
Proof.
intros P l. induction l as [|u r IH]; intros a D b H Hb; cbn [pj_itemsR] in H; [subst D; destruct Hb|].
destruct H as (D1 & D2 & -> & H1 & H2). apply in_app_or in Hb as [Hb|Hb].
- exists 0%nat, u, D1. split; [reflexivity|]. split; [|exact Hb]. replace (a + 56 * Z.of_nat 0) with a by lia. exact H1.
- destruct (IH (a + 56) D2 b H2 Hb) as (i & u' & D1' & Hi & HP & Hin).
  exists (S i), u', D1'. split; [exact Hi|]. split; [|exact Hin].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP.
Qed.
Lemma gs_mems_in : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D b,
  pj_memsR SEGS m lblk P a ka l D -> In b D ->
  (exists x k nm, b = (x, k) /\ pj_cstrR SEGS m lblk x k nm) \/
  exists i nm u D1, nth_error l i = Some (nm, u) /\ P (a + 56 * Z.of_nat i) u D1 /\ In b D1.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D b H Hb; cbn [pj_memsR] in H; [subst D; destruct Hb|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2).
destruct Hb as [<- | Hb]; [left; exists x, k, nm; split; [reflexivity | exact Hc]|].
apply in_app_or in Hb as [Hb|Hb].
- right. exists 0%nat, nm, u, D1. split; [reflexivity|]. split; [|exact Hb].
  replace (a + 56 * Z.of_nat 0) with a by lia. exact H1.
- destruct (IH (a + 56) (ka + 8) D2 b H2 Hb) as [L' | (i & nm' & u' & D1' & Hi & HP & Hin)]; [left; exact L'|].
  right. exists (S i), nm', u', D1'. split; [exact Hi|]. split; [|exact Hin].
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP.
Qed.
Lemma pj_nodeR_lblk : forall t m lblk p D, pj_nodeR SEGS m lblk p t D -> forall b, In b D -> lblk (fst b) (snd b).
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
  intros m lblk p D H b Hb; cbn [pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & Hb2).
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & ->). destruct Hb.
- destruct Hb2 as (_ & _ & _ & _ & _ & k & Hc & ->). destruct Hb as [<- | []]. exact (proj1 Hc).
- destruct Hb2 as (_ & _ & _ & _ & k & Hc & ->). destruct Hb as [<- | []]. exact (proj1 Hc).
- destruct Hb2 as (_ & _ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hb as [<- | []]. destruct Hcap as [(Hc0 & _) | (_ & Hl)]; [lia | exact Hl].
  + destruct (gs_items_in _ items kids Di b Hi Hb) as (i & u & D1 & Hil & HP & Hin).
    rewrite Forall_forall in IH. exact (IH u (nth_error_In items i Hil) m lblk _ D1 HP b Hin).
- destruct Hb2 as (_ & _ & _ & Hcap & Di & -> & Hi). apply in_app_or in Hb as [Hb|Hb].
  + destruct (cap =? 0) eqn:Ec; [destruct Hb|]. apply Z.eqb_neq in Ec.
    destruct Hcap as [(Hc0 & _) | (_ & Hk & Hy)]; [lia|].
    destruct Hb as [<- | [<- | []]]; [exact Hk | exact Hy].
  + destruct (gs_mems_in m lblk _ members kids keys Di b Hi Hb) as [(x & k & nm & -> & Hc) | (i & nm & u & D1 & Hil & HP & Hin)].
    * exact (proj1 Hc).
    * rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)). cbn [snd] in IH.
      exact (IH m lblk _ D1 HP b Hin).
Qed.
(* a byte array read through one world is the same array through another when the views agree *)
Lemma gs_garr8_move : forall (Wa Wb : world SEGS) m m' x d l, garr8 SEGS (mrestrict (w_H Wa) m) x l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H Wb) m' (d + Z.of_nat j) = aview SEGS (w_H Wa) m (x + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H Wb) m') d l.
Proof.
intros Wa Wb m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte SEGS (mrestrict (w_H Wb) m') (d + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
(* a key string (cstr_ok) below alloc_ceiling survives a step that keeps every view below alloc_ceiling *)
Lemma gs_cstr_kept : forall (Wa Wb : world SEGS) m m' p l, cstr_ok (PA := PA) Wa m p l ->
  (forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H Wb) m' a = aview SEGS (w_H Wa) m a) ->
  cstr_ok (PA := PA) Wb m' p l.
Proof.
intros Wa Wb m m' p l HC HA. destruct HC as ((Hg & Hnz) & H4096 & Hceil & H32 & Hamr & HRA & HH & Hv).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [split; [|exact Hnz]|].
- apply (gs_garr8_move Wa Wb m m' p p (l ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn in Hj. apply HA. lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Hamr|]. split; [|split].
  + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply HA. lia.
  + intros s0 Hs. pose proof (gs_hull_low p (Z.of_nat (length l) + 1) s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs).
    rewrite HA by lia. apply HH. exact Hs.
  + intros a Ha.
    (* the NUL's aligned word lies below alloc_ceiling: the string ends below it (cstr_ok's ceiling bound, with or
       without the old `+ 8`: K1's batch states `p + len + 1`) and alloc_ceiling is page-aligned
       (YM05.alloc_ceiling_value). Proof form by WalkS6R (cold/h-rw-pre-5-r102-s6-batchprep 825f574a1c52). *)
    assert (Hqa : 0 <= a < alloc_ceiling).
    { pose proof alloc_ceiling_value as [_ Hc4096].
      set (e := p + Z.of_nat (length l)) in *.
      pose proof (Z.div_mod e 8 ltac:(lia)) as Ee. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Re.
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Ec. rewrite Hc4096 in Ec.
      clear - Ha Hceil H4096 Ee Re Ec. lia. }
    rewrite HA by exact Hqa. apply Hv. exact Ha.
Qed.
(* a stretch whose write windows lie inside [lo, hi) keeps every view outside it *)
Lemma gs_keep_out : forall E' rs (Wx : world SEGS) m m' lo hi,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  (forall a, in_wrange E' rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros E' rs Wx m m' lo hi HF Hw a Ha Hn.
unfold aview, mbyte. rewrite (gs_mr_keep E' rs _ _ a HF); [reflexivity | | exact Ha].
intros Hin. apply Hn. exact (Hw a Hin).
Qed.
(* off the image, equal views are equal bytes of the restricted memories *)
Lemma gs_raw_of_aview : forall H H' (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H' m' a = aview SEGS H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. apply mbyte_of_aview in E. unfold mbyte in E. rewrite (seg_rom_none SEGS a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
(* a tree whose footprint is off the image and keeps its views is the same tree (PRH_Reader.v pj_nodeR_frame) *)
Lemma gs_node_kept : forall (Wx : world SEGS) m m' lblk p t D,
  pj_nodeR SEGS (mrestrict (w_H Wx) m) lblk p t D ->
  (forall x, pj_footR p D x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H Wx) m' x = aview SEGS (w_H Wx) m x) ->
  pj_nodeR SEGS (mrestrict (w_H Wx) m') lblk p t D.
Proof.
intros Wx m m' lblk p t D H HF. apply (pj_nodeR_frame SEGS t (mrestrict (w_H Wx) m) _ lblk p D H).
apply gs_agree. intros x Hx. destruct (HF x Hx) as (Hr & Hn & E). exact (gs_raw_of_aview _ _ m m' x Hr Hn E).
Qed.
Lemma gs_ro_img : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
Lemma gs_rod_kept : forall (B : asyms) (Wa Wb : world SEGS) m m',
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H Wa) m) ->
  (forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H Wb) m' a = aview SEGS (w_H Wa) m a) ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H Wb) m').
Proof.
intros B Wa Wb m m' H HA a Hro Hn He. pose proof (@pa_segs_low _ _ PA a (gs_ro_img a Hro)) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5). rewrite HA by lia. exact (H a Hro Hn He).
Qed.
(* a shadow address register (s = Bx + x >> 3), as the code computes it before a loop *)
Lemma gs_U_shadow_of : forall (E : env) nb nx b x, ew E nb = Z_to_bv 64 b -> ew E nx = Z_to_bv 64 x ->
  0 <= b < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> b + x / 8 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SOff nx 0) (SLit 3))) = b + x / 8.
Proof.
intros E nb nx b x Hb Hx Rb Rx Rbx. rewrite !U_SAlu, (U_atom E nb b Hb Rb), (U_atom E nx x Hx Rx), U_SLit.
cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (x / 8)) by (unfold M64; lia). apply zcanon_id. unfold M64; lia.
Qed.
Lemma gs_reg_shadow_of : forall (E : env) nb nx b x (w : word), ew E nb = Z_to_bv 64 b -> ew E nx = Z_to_bv 64 x ->
  0 <= b < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> b + x / 8 < 2 ^ 64 -> w = Z_to_bv 64 (b + x / 8) ->
  w = sv_denot E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SOff nx 0) (SLit 3))).
Proof. intros E nb nx b x w Hb Hx Rb Rx Rbx ->. rewrite (denot_lit_U E), (gs_U_shadow_of E nb nx b x); auto. Qed.
(* a seat register given as an expression over the env's atoms (YC1fP.v st_ok_pi_pin_reg' for any expression) *)
Lemma gs_set_reg : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS (@pa_val _ L PA) E ss ms -> getr (ms_regs ms) r = sv_denot E e -> bv_eqb r 0 = false ->
  st_ok_pi SEGS (@pa_val _ L PA) E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (@pa_val _ L PA A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg SEGS E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq. symmetry. exact Hr.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End c.

(* ---- tactics ---- *)
(* the own frame's stores at sp + off (atom 2), the only writes of a stretch *)
Ltac gs_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
  rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| repeat (eapply awr_ok_cons_gen; [reflexivity | reflexivity | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia |]);
  apply awr_ok_nil ].
(* the same, with the frame region anywhere in the list (regions without a write window around it) *)
Ltac gs_awr_step rg HU :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
  first [ eapply awr_ok_cons_gen; [reflexivity | reflexivity | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia |]
        | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0'));
          [ reflexivity
          | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
            rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
          | cbn [YP09.r_wlo stack_region]; lia
          | cbn [YP09.r_whi stack_region]; lia
          | ] ]
end.
Ltac gs_awr_any rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat gs_awr_step rg HU.
(* a stretch whose regions have no write window *)
Ltac gs_awr0 :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat (eapply awr_ok_cons_gen; [reflexivity | reflexivity | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia |]);
apply awr_ok_nil.
(* a stretch over regions without write windows leaves the memory as it was *)
Ltac gs_memeq HF EQ :=
let xx := fresh "xx" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
lazymatch type of HF with frame_of _ _ ?m ?m' =>
assert (EQ : m' = m) by (apply functional_extensionality; intros xx; apply HF; intros (rr & Hin & Hr);
  vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]);
  destruct Hin) end.
(* a loaded type word in a branch condition: Fty : ew E n = Z_to_bv 64 (tag v) of the seat's env *)
Ltac gs_tag_in Hc v Fty :=
lazymatch type of Hc with context [U ?E' (SExt true 32 (SOff ?n 0))] =>
  rewrite (gs_tagU E' n v ltac:(rewrite ?ew_ewset_other by lia; exact Fty)) in Hc end.
(* the write windows of a state's regions lie in [lo, hi): only the frame region (atom 2, the stack) has one;
   Usp : bv_unsigned (ew E 2) = sp, and the context bounds the frame inside [lo, hi) *)
Ltac gs_win Usp :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia); rewrite ?Usp in Hr; lia|]);
destruct Hin.
(* the views outside [lo, hi) after a stretch, from its frame_of over the restricted memories *)
Ltac gs_keep HFr Usp lo hi K :=
lazymatch type of HFr with frame_of ?E' ?rs (mrestrict (w_H ?Wx) ?m) (mrestrict (w_H ?Wx) ?m') =>
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview _ (w_H Wx) m' a = aview _ (w_H Wx) m a)
  by (apply (gs_keep_out E' rs Wx m m' lo hi HFr); gs_win Usp) end.
