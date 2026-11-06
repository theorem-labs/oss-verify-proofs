(* The 16-byte head of a block (fuzz/alloc.c own / disown, inlined in fuzz_malloc, fuzz_free and fuzz_realloc): what a
   walk needs for own's 8-byte store of n and disown's 8-byte load of the head, each guarded by two inline ASan checks
   `lb shadow(h); bnez` / `lb shadow(h + 7); bnez`.
   - fs_head_shadow0: the head's two shadow bytes read 0 on the machine's memory, from ARU at any U whose ranges are all
     apart from the head and the block live: a FRESH block (own, after malloc / realloc) or a block whose head was just
     unpoisoned (disown: the head has left U). The allocator's 0 comes from AR (FSupoison.block_granule0) over the
     unpoisoned memory; the head's shadow bytes are no shadow byte of U (FSupoison.ush16_out), so the two readings agree.
   - fs_head_shent: the token run's shadow entry for the head (YCbn.shent_ok at Bx := FSW_K.fs_Bx, she_m the atom holding
     h, offsets [0, 16)), from the two shadow facts; the two checks then close by the token run (fsw_aj_run_tokU).
   - fs_head_region / fs_head_region_ok: the head's first 8 bytes as a region based at h's atom (writable window [0, w):
     8 for own's store, 0 for disown's load; chunks cs, e.g. fs_head_chunk_ok's CVal 8 of n), and fs_head_img_apart:
     the head lies off every image range (the walk's pairwise_disjoint with the GOT / cell / static regions).
   - fs_head_apart_rest: a head removed from a pairwise-disjoint U is apart from the rest (disown's premise).
   ONE COPY (ruling 23:1xZ): single writer a Theorem Labs lane; another imports it. Rule 24: grep of FSW_K, FSW_ret,
   FSW_rres, FSW_K3 and a Theorem Labs lane's kit branches (all working branches) for a block-shadow / shent setup found only
   FSW_K.v:255-260's note (fs_Bx / fs_Bspan, "one shent per object", the donor's A/ACes.v:28-29); no lemma.
   Ported from: FSupoison.v's block_granule0 / ush16_out (a Theorem Labs lane's FMupoison), YG0v's block_shadow; the region_ok form of
   FSW_statics.v's fs_pstat_region. No rename. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YP0m YP0e YP09 YK04 YA0i YA0n YI04 YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI16 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_Gen FSH_Base FSW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* a head removed from a pairwise-disjoint U is apart from every range left *)
Lemma fs_head_apart_rest : forall (U1 U2 : list (Z * Z)) h,
  pairwise zdisjoint (U1 ++ (h, 16) :: U2) -> Forall (zdisjoint (h, 16)) (U1 ++ U2).
Proof.
intros U1 U2 h P.
assert (P' : pairwise zdisjoint ((h, 16) :: U1 ++ U2)).
{ exact (FSupoisonU.pairwise_zdisjoint_perm (U1 ++ (h, 16) :: U2) _
    ltac:(symmetry; apply Permutation.Permutation_middle) P). }
exact (proj1 P').
Qed.

(* the head's 8-byte region based at the atom m that holds h; writable window [0, w) *)
Definition fs_head_region (m : nat) (w : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some m) 0 8 0 w cs.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* an application byte (a block byte) is no user-poisoned shadow byte: the two memories agree there *)
Lemma fs_head_app_view : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha [Hl|Hh].
- apply (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 a) H). rewrite (wz a Ha). exact Hl.
- exact (fsw_unpoison_high B ly S U W mem md a H ltac:(lia)).
Qed.

(* the two shadow bytes of the head (h, 16) of a live block read 0 on the machine's memory *)
Lemma fs_head_shadow0 : forall ly S U (W : world tfibsegs) mem md h m,
  ARU tfibsegs B ly S U W mem md -> In (h, m) (ablocks B ly S) -> 16 <= req_size m ->
  Forall (zdisjoint (h, 16)) U ->
  aview tfibsegs (w_H W) mem (shadow_addr h) = Some 0 /\ aview tfibsegs (w_H W) mem (shadow_addr h + 1) = Some 0.
Proof.
intros ly S U W mem md h m H Hb Hm DJ.
pose proof H as (HAR & OK & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m HAR Hb) as (H16 & H4096 & Hceil & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (H8 : h mod 8 = 0).
{ pose proof (Z.div_mod h 16 ltac:(lia)) as D. rewrite H16, Z.add_0_r in D. rewrite D.
  replace (16 * (h / 16)) with ((2 * (h / 16)) * 8) by lia. apply Z.mod_mul. lia. }
assert (AL : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) U).
{ eapply Forall_impl; [|exact (proj1 OK)]. intros r (A1 & _ & A2 & _). exact (conj A1 A2). }
assert (Hq : 2 <= req_size m / 8) by (apply Z.div_le_lower_bound; lia).
assert (E8 : shadow_addr (h + 8) = shadow_addr h + 1).
{ unfold shadow_addr. apply Z.mod_divide in H8 as [x Hx]; [|lia]. subst h.
  replace (x * 8 + 8) with ((x + 1) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
assert (G0 : aview tfibsegs (w_H W) (unpoison U mem) (shadow_addr h) = Some 0)
  by exact (block_granule0 tfibsegs B LAWS ly S W (unpoison U mem) md h m h HAR Hb H8 ltac:(lia) ltac:(lia)).
assert (G1 : aview tfibsegs (w_H W) (unpoison U mem) (shadow_addr (h + 8)) = Some 0).
{ exact (block_granule0 tfibsegs B LAWS ly S W (unpoison U mem) md h m (h + 8) HAR Hb
    ltac:(rewrite Z.add_mod, H8 by lia; reflexivity) ltac:(lia) ltac:(lia)). }
rewrite E8 in G1.
assert (SR : forall s, shadow_addr h <= s < shadow_addr h + 2 -> 0 <= s < 2 ^ 64).
{ intros s Hs. unfold shadow_addr, SHADOW_OFF in *. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)).
  assert (h / 8 <= h) by (apply Z.div_le_upper_bound; lia). unfold YM05.alloc_ceiling in *. lia. }
split.
- rewrite <- G0. symmetry.
  exact (aview_unpoison_out tfibsegs _ U mem (shadow_addr h)
    ltac:(rewrite (wz _ (SR (shadow_addr h) ltac:(lia))); exact (ush16_out h U (shadow_addr h) H8 AL DJ ltac:(lia)))).
- rewrite <- G1. symmetry.
  exact (aview_unpoison_out tfibsegs _ U mem (shadow_addr h + 1)
    ltac:(rewrite (wz _ (SR (shadow_addr h + 1) ltac:(lia))); exact (ush16_out h U (shadow_addr h + 1) H8 AL DJ ltac:(lia)))).
Qed.

(* the token run's shadow entry for the head held in atom m: [h, h + 16) addressable, apart from the shadow. Generic in
   the token run's base Bx: fs_Bx (atom 32 of a T state) at entry, or the register atom a resumed state holds the
   shadow base in (s4 in fuzz_realloc) *)
Lemma fs_head_shent : forall (Bx : sv) E (W : world tfibsegs) mem (m : nat) h,
  U E (SOff m 0) = h -> U E Bx = SHADOW_OFF -> h mod 8 = 0 -> in_app h 16 ->
  aview tfibsegs (w_H W) mem (shadow_addr h) = Some 0 -> aview tfibsegs (w_H W) mem (shadow_addr h + 1) = Some 0 ->
  YCbn.shent_ok tfibsegs Bx E (mrestrict (w_H W) mem) (YCbn.mkSHE m 0 16).
Proof.
intros Bx E W mem m h Hm HB H8 Happ Z0 Z1.
pose proof asan_consts as (C1 & _ & C3 & _).
split.
- intros x Hx. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Hx. rewrite Hm in Hx. rewrite HB.
  exists 0. split; [|left; reflexivity].
  change (YCbn.rd_of tfibsegs (mrestrict (w_H W) mem) (shadow_of_addr SHADOW_OFF x))
    with (aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
  apply Z.mod_divide in H8 as [q Hq]; [|lia]. rewrite Hq in Z0, Z1, Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert (E0 : shadow_addr (q * 8) = SHADOW_OFF + q) by (unfold shadow_addr; rewrite Z.div_mul by lia; reflexivity).
  rewrite E0 in Z0, Z1. unfold shadow_of_addr.
  assert (x / 8 = q \/ x / 8 = q + 1) as [-> | ->] by lia; [exact Z0 | rewrite Z.add_assoc; exact Z1].
- intros a Ha. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Ha. rewrite Hm in Ha. rewrite HB.
  change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha.
  unfold in_app, kLowShadowBeg, SHADOW_OFF in *. rewrite C3 in Happ. lia.
Qed.

(* the same entry anchored at any atom m that holds h - lo (the window [lo, lo + 16) of m is the head): disown's second
   check in fuzz_realloc reads the shadow of p - 9 through s2 = p, i.e. atom 18 with lo = -16 *)
Lemma fs_head_shent_at : forall (Bx : sv) E (W : world tfibsegs) mem (m : nat) (lo : Z) h,
  U E (SOff m 0) + lo = h -> U E Bx = SHADOW_OFF -> h mod 8 = 0 -> in_app h 16 ->
  aview tfibsegs (w_H W) mem (shadow_addr h) = Some 0 -> aview tfibsegs (w_H W) mem (shadow_addr h + 1) = Some 0 ->
  YCbn.shent_ok tfibsegs Bx E (mrestrict (w_H W) mem) (YCbn.mkSHE m lo (lo + 16)).
Proof.
intros Bx E W mem m lo h Hm HB H8 Happ Z0 Z1.
pose proof asan_consts as (C1 & _ & C3 & _).
assert (Hm' : U E (SOff m 0) = h - lo) by lia.
split.
- intros x Hx. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Hx. rewrite Hm' in Hx. rewrite HB.
  exists 0. split; [|left; reflexivity].
  change (YCbn.rd_of tfibsegs (mrestrict (w_H W) mem) (shadow_of_addr SHADOW_OFF x))
    with (aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
  assert (Hx' : h <= x < h + 16) by lia. clear Hx.
  apply Z.mod_divide in H8 as [q Hq]; [|lia]. rewrite Hq in Z0, Z1, Hx'.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert (E0 : shadow_addr (q * 8) = SHADOW_OFF + q) by (unfold shadow_addr; rewrite Z.div_mul by lia; reflexivity).
  rewrite E0 in Z0, Z1. unfold shadow_of_addr.
  assert (x / 8 = q \/ x / 8 = q + 1) as [-> | ->] by lia; [exact Z0 | rewrite Z.add_assoc; exact Z1].
- intros a Ha. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi] in Ha. rewrite Hm' in Ha. rewrite HB.
  unfold in_app, kLowShadowBeg, SHADOW_OFF in *. rewrite C3 in Happ. lia.
Qed.

(* the head's region: in the block, so present (writable) and below alloc_ceiling *)
Lemma fs_head_region_ok : forall ly S U (W : world tfibsegs) mem md E m h w cs p n,
  ARU tfibsegs B ly S U W mem md -> In (p, n) (ablocks B ly S) -> p <= h -> h + 8 <= p + req_size n ->
  bv_unsigned (ew E m) = h -> 0 <= w <= 8 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem) h) cs ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_head_region m w cs).
Proof.
intros ly S U W mem md E m h w cs p n H Hb Hp Hn Hm Hw Hcs.
pose proof H as (HAR & _ & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hb) as (H16 & H4096 & Hceil & Happ & Hpr & _).
pose proof asan_consts as (C1 & _ & C3 & _).
unfold region_ok, fs_head_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hm.
split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs).
  destruct (Hpr (h + o) ltac:(lia)) as [[Hh [b Hbb]] _]. split; [exact Hh|]. exists b.
  rewrite <- (fs_head_app_view ly S U W mem md (h + o) H ltac:(lia)
    ltac:(unfold in_app, kLowShadowBeg, SHADOW_OFF in *; rewrite C3 in Happ; lia)). exact Hbb.
- exact Hcs.
Qed.

(* the 8-byte head value as the region's chunk *)
Lemma fs_head_chunk_ok : forall E (H : word -> bool) mem h e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) h 8 v ->
  YP09.chunk_ok tfibsegs E (mrestrict H mem) h (YP09.mkChunk 0 (CVal 8 e)).
Proof.
intros E H mem h e v He Hv Hm.
exact (chunk_ok_val tfibsegs E _ h 0 8 e v He ltac:(cbn; lia) ltac:(cbn; lia) ltac:(rewrite Z.add_0_r; exact Hm)).
Qed.

(* a block's head range lies off every image range *)
Lemma fs_head_img_apart : forall ly S (W : world tfibsegs) mem md p n h g len,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= h -> h + 8 <= p + req_size n -> 0 < len ->
  (forall x, g <= x < g + len -> in_img tfibsegs x) -> h + 8 <= g \/ g + len <= h.
Proof.
intros ly S W mem md p n h g len HAR Hb Hp Hn Hl Hi.
destruct (Z_le_gt_dec (h + 8) g) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (g + len) h) as [L'|L']; [right; exact L'|].
exfalso. apply (blk_img tfibsegs B LAWS ly S W mem md p n (Z.max h g) HAR Hb ltac:(lia)). apply Hi. lia.
Qed.
End h.
