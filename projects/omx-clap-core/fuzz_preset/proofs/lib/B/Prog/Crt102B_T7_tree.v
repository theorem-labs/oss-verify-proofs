(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 443 of its 506 lines of code are new or changed and 451 lines of the source are left out. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T7 = CRT-B-CEXIT (segment C + the
   exit, B' entry + 0x6f8 .. + 0x80c): the READER LAYER of the row. Everything the walk needs to know about the bytes
   of the read-back tree `back` (crt_tc t = ck_crt_tree t over the blocks Dback, Crt102Glue.v crt_at_C_B), derived
   from PRH_Reader.v's pj_nodeR and the ledger, with no machine state:
   no st_ok, no SRr, no sym_run.

   proves no function (kind: reader-layer lemmas for a segment walk).

   INPUTS OF RECORD (taken by path):
   - base commit 91762d8dd6b1 (= cc93c792c645 merged with commit
     11c39f7e88b7): lib/A/PRH_Reader.v (pj_hdrR, pj_cstrR, pj_memsR, pj_nodeR), lib/A/PRH_Base.v (prh_ledger,
     prh_hblock, prh_lin, kept_img), lib/A/Prog/Crt102Model.v (cm_at, cm_crt_at), lib/A/Prog/Crt102Img.v
     (CRT_MOD_AT_B, CRT_STAMP_B, crt_str_rom_B), lib/A/Prog/S1Ledger.v (prh_ledger_hblock), lib/Reusable/YCbqG.v
     (AR_laws_x: alx_blocks, alx_hshadow, alx_blocks_tail, alx_zshadow, alx_const_cells), lib/Reusable/YGcallMxmn.v
     (aj_strcmp_at_xro: the per-string premises this file's cb7t_str_prem / cb7t_rom_prem_* deliver).
   - worked models, PORTED (not Required): slice S9's lib/A/Prog/Wsame_base.v (s9_ra_of_bshadow, s9_hull_sub) and
     Wsame_memB.v (s9b_aview_vm, s9b_garr8_at, s9b_aview_pres, s9_str_ok) at commit
     9a0674f0b5f2; S1's lib/B/Prog/FuzzStrdupB.v (sd_hull_img, sd_amr8, sd_src_shadow's kept_img arm).

   NAMED SECTION HYPOTHESES (each one stated with its text where it is taken):
   - LAWS : AR_laws_x SEGS B ARx cf_head (the same hypothesis lib/B/Prog/Crt102B_T4.v:491 takes; discharged at the
     instance ARcfx by lib/Reusable/YGcallcf.v AR_laws_x_xs).
   - BOK : asyms_ok B (only for the read-only strings: aso_zshadow, the 8-alignment of as_zero_shadow's ranges;
     image B's generated start-up facts carry it, AF0m.v-style ts_ok / YF0m).
   - IMGVIS (only for the read-only strings: the shadow hull of an image string; img_shadow_vis_cf,
     lib/Reusable/YGcfAmx2.v:47, over ARx; FuzzStrdupB.v:286-289 takes the ARcf form as a Section hypothesis too).

   NUMERALS. WORD: 4 / 6 (PjTree.tag of a string / an object). LENGTH: 8 / 56 (a key slot / a struct pj, the
   strides), 16 (cf_head at CfParams_preset, read by `reflexivity`), 8 (shadow granule), 64 (GrantRo's hull margin),
   2 ^ 32 / 2 ^ 63 (the strcmp rule's bounds). No ADDRESS literal: the two read-only strings are Crt102Img.v's
   CRT_MOD_AT_B / CRT_STAMP_B (VAL (A_OBJ 2) + offset), read by computation. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* PART 1, image-free: the read-back tree's bytes from pj_nodeR alone.                                      *)
Section rd.
Variable segs : list Segment.

(* the i-th member of an object's member list: its key word, the key string, the kid node, inside the footprint *)
Lemma cb7t_mems_nth : forall m lblk l a ka D i nm u,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k Di, rd_u64 segs m (ka + 8 * Z.of_nat i) x /\ pj_cstrR segs m lblk x k nm /\
    pj_nodeR segs m lblk (a + 56 * Z.of_nat i) u Di /\ In (x, k) D /\ incl Di D.
Proof.
intros m lblk l. induction l as [|[nm0 u0] r IH]; intros a ka D i nm u H He.
- destruct i; discriminate He.
- cbn [pj_memsR] in H. destruct H as (x & k & D1 & D2 & -> & Hx & Hc & Hn & Hr).
  destruct i as [|i]; cbn [nth_error] in He.
  + injection He as <- <-. exists x, k, D1.
    replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
    split; [exact Hx|]. split; [exact Hc|]. split; [exact Hn|]. split; [left; reflexivity|].
    intros y Hy. right. apply in_or_app. left. exact Hy.
  + destruct (IH (a + 56) (ka + 8) D2 i nm u Hr He) as (x' & k' & Di & H1 & H2 & H3 & H4 & H5).
    exists x', k', Di.
    replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [right; apply in_or_app; right; exact H4|].
    intros y Hy. right. apply in_or_app. right. exact (H5 y Hy).
Qed.

(* a non-empty object: its header, its two blocks (kids 56 * cap, keys 8 * cap) at the head of its footprint *)
Lemma cb7t_obj_shape : forall m lblk p l D,
  pj_nodeR segs m lblk p (PjTree.JObj l) D -> (0 < length l)%nat ->
  exists num kids keys n cap Di,
    pj_hdrR segs m p (PjTree.tag (PjTree.JObj l)) num 0 kids keys n cap /\
    n = Z.of_nat (length l) /\ n <= cap /\ 0 < cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap) /\
    D = [(kids, 56 * cap); (keys, 8 * cap)] ++ Di /\ pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys l Di.
Proof.
intros m lblk p l D H Hl. cbn [pj_nodeR] in H.
destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & En & Hle & Hcap & Di & ED & Hm).
subst str.
destruct Hcap as [(C0 & _) | (Cp & Hk & Hy)]; [lia|].
destruct (Z.eqb_spec cap 0) as [C|C]; [lia|].
exists num, kids, keys, n, cap, Di.
split; [exact Hh|]. split; [exact En|]. split; [exact Hle|]. split; [exact Cp|].
split; [exact Hk|]. split; [exact Hy|]. split; [exact ED | exact Hm].
Qed.

(* a string node: its header (type 4, no kids, no keys), its string, its one block *)
Lemma cb7t_str_node : forall m lblk p s D,
  pj_nodeR segs m lblk p (PjTree.JStr s) D ->
  exists num str k, pj_hdrR segs m p 4 num str 0 0 0 0 /\ pj_cstrR segs m lblk str k s /\ D = [(str, k)].
Proof.
intros m lblk p s D H. cbn [pj_nodeR] in H.
destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & -> & -> & -> & -> & k & Hc & ED).
exists num, str, k. split; [exact Hh|]. split; [exact Hc | exact ED].
Qed.

(* ---- the read-back of the rewritten tree, read at at = cm_at ms (fuzz_preset.c new:756-768) ---- *)
Section bk.
Variable t : PjTree.jv.
Variable ms : list (list Z * PjTree.jv).
Hypothesis HT : t = PjTree.JObj ms.

Lemma cb7t_back_at : forall m lblk bk Dback,
  pj_nodeR segs m lblk bk (ck_crt_tree t) Dback ->
  exists num kids keys n cap kx kk sx sk Dkid num2,
    pj_hdrR segs m bk 6 num 0 kids keys n cap /\ 0 < cap /\ Z.of_nat (cm_at ms) < n /\ n <= cap /\
    lblk kids (56 * cap) /\ lblk keys (8 * cap) /\ In (kids, 56 * cap) Dback /\ In (keys, 8 * cap) Dback /\
    rd_u64 segs m (keys + 8 * Z.of_nat (cm_at ms)) kx /\ pj_cstrR segs m lblk kx kk ck_MOD_AT /\ In (kx, kk) Dback /\
    pj_nodeR segs m lblk (kids + 56 * Z.of_nat (cm_at ms)) (PjTree.JStr ck_STAMP) Dkid /\ incl Dkid Dback /\
    pj_hdrR segs m (kids + 56 * Z.of_nat (cm_at ms)) 4 num2 sx 0 0 0 0 /\
    pj_cstrR segs m lblk sx sk ck_STAMP /\ In (sx, sk) Dback.
Proof.
intros m lblk bk Dback H.
destruct (cm_crt_at t ms HT) as (ms' & Et & Hat & _ & _).
rewrite Et in H.
assert (Hl : (cm_at ms < length ms')%nat) by (apply nth_error_Some; rewrite Hat; discriminate).
destruct (cb7t_obj_shape m lblk bk ms' Dback H ltac:(lia))
  as (num & kids & keys & n & cap & Di & Hh & En & Hle & Hc & Hk & Hy & ED & Hm).
destruct (cb7t_mems_nth m lblk ms' kids keys Di (cm_at ms) ck_MOD_AT (PjTree.JStr ck_STAMP) Hm Hat)
  as (kx & kk & Dkid & Hx & Hcx & Hn & Hin & Hinc).
destruct (cb7t_str_node m lblk _ ck_STAMP Dkid Hn) as (num2 & sx & sk & Hh2 & Hcs & ED2).
exists num, kids, keys, n, cap, kx, kk, sx, sk, Dkid, num2.
subst Dback. cbn [app].
split; [exact Hh|]. split; [exact Hc|]. split; [lia|]. split; [exact Hle|]. split; [exact Hk|].
split; [exact Hy|]. split; [left; reflexivity|]. split; [right; left; reflexivity|].
split; [exact Hx|]. split; [exact Hcx|]. split; [right; right; exact Hin|].
split; [exact Hn|]. split; [intros z Hz; right; right; exact (Hinc z Hz)|].
split; [exact Hh2|]. split; [exact Hcs|].
right; right. apply Hinc. rewrite ED2. left. reflexivity.
Qed.
End bk.
End rd.

(* ======================================================================================================== *)
(* PART 2, image-free helpers: bytes and shadow of a view. PORTED, statement and proof, from slice S9
   (commit 9a0674f0b5f2): Wsame_base.v s9_ra_of_bshadow / s9_hull_sub, Wsame_memB.v
   s9b_aview_vm / s9b_garr8_at / s9b_aview_pres; and S1's lib/B/Prog/FuzzStrdupB.v sd_hull_img. *)
Lemma cb7t_ra_of_bshadow : forall (rd : Z -> option Z) p n x len,
  block_shadow rd SHADOW_OFF p n -> p <= x -> x + len <= p + n -> range_addressable rd SHADOW_OFF x len.
Proof.
intros rd p n x len (Hp & Hn & Hb) Hx Hxl y Hy.
assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
set (i := (y - p) / 8).
assert (Hi0 : 0 <= i) by (apply Z.div_pos; lia).
assert (Ey : y / 8 = p / 8 + i).
{ unfold i. replace y with ((p / 8) * 8 + (y - p)) at 1 by lia. rewrite Z.div_add_l by lia. reflexivity. }
assert (Hi : i < (n + 7) / 8).
{ unfold i. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
pose proof (Hb i (conj Hi0 Hi)) as Hs. unfold shadow_of_addr in *. rewrite Ey, Z.add_assoc.
eexists. split; [exact Hs|].
destruct (Z.ltb_spec i (n / 8)) as [Hl|Hl]; [left; reflexivity|right].
pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
pose proof (Z.div_mod (y - p) 8 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound (y - p) 8 ltac:(lia)) as My.
fold i in Dy.
assert (Hi' : i < n / 8 + 1) by lia.
assert (Ei : i = n / 8) by lia.
assert (Hym : y mod 8 = (y - p) mod 8).
{ rewrite Ep. replace (y - 8 * (p / 8)) with (y + (- (p / 8)) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
rewrite Hym. lia.
Qed.

Lemma cb7t_hull_sub : forall (rd : Z -> option Z) x n y m,
  shadow_hull_vis rd x n -> x <= y -> y + m <= x + n -> 0 < m -> shadow_hull_vis rd y m.
Proof.
intros rd x n y m H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (A1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + y / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
assert (A2 : (SHADOW_OFF + (y + m - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
lia.
Qed.

Lemma cb7t_aview_vm : forall segs (H : word -> bool) (mem : word -> option byte) a (n : nat) v (j : nat),
  val_mem segs (mrestrict H mem) a n v -> (j < n)%nat -> aview segs H mem (a + Z.of_nat j) = Some (le_byte v n j).
Proof.
intros segs H mem a n v j Hv Hj. unfold aview. rewrite (Hv j Hj). cbn [option_map]. f_equal.
change (bv_unsigned (Z_to_bv 8 (le_byte v n j)) = le_byte v n j).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. apply Z.mod_mod. lia.
Qed.

Lemma cb7t_garr8_at : forall segs (H : word -> bool) (mem : word -> option byte) x l (j : nat),
  garr8 segs (mrestrict H mem) x l -> (j < length l)%nat -> aview segs H mem (x + Z.of_nat j) = Some (nth j l 0).
Proof.
intros segs H mem x l j Hg Hj. destruct (Hg j Hj) as [Hv Hr].
pose proof (cb7t_aview_vm segs H mem (x + Z.of_nat j) 1 (nth j l 0) 0 Hv ltac:(lia)) as E.
replace (x + Z.of_nat j + Z.of_nat 0) with (x + Z.of_nat j) in E by lia. rewrite E. f_equal.
change (Z.shiftr (nth j l 0 mod 256) 0 mod 256 = nth j l 0).
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (nth j l 0) 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma cb7t_aview_pres : forall segs (H : word -> bool) (mem : word -> option byte) a,
  apresent H mem a -> aview segs H mem a <> None.
Proof. intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* a byte of an image segment is visible, whatever the memory holds there (mbyte falls back to the segment) *)
Lemma cb7t_aview_rom : forall segs (H : word -> bool) (mem : word -> option byte) a,
  seg_rom segs (Z_to_bv 64 a) <> None -> aview segs H mem a <> None.
Proof.
intros segs H mem a Hr. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn [option_map]; discriminate|].
destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:E; [cbn [option_map]; discriminate|].
exfalso. apply Hr. reflexivity.
Qed.

(* fuzz_grant GrantRo.v:82-100 ro_hull's arithmetic (FuzzStrdupB.v sd_hull_img), over any image band [lo, hi): the
   hull of a range at least 64 bytes inside it is the shadow of bytes of the band (no image constant: the band is the
   instance's pa_lo / pa_hi, which kept_img states) *)
Lemma cb7t_hull_img : forall lo hi a n s, 0 < n -> lo + 64 <= a -> a + n + 64 <= hi ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_addr (8 * (s - SHADOW_OFF)) /\ lo <= 8 * (s - SHADOW_OFF) < hi.
Proof.
intros lo hi a n s Hn Hlo Hhi Hs. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.

(* a tail of at most 7 bytes after y + n, from the bytes y + n + 1 + j, j < 8 *)
Lemma cb7t_tail_idx : forall (P : Z -> Prop) y n,
  (forall j, (j < 8)%nat -> P (y + n + 1 + Z.of_nat j)) ->
  forall a, y + n < a < y + n - (y + n) mod 8 + 8 -> P a.
Proof.
intros P y n H a Ha. pose proof (Z.mod_pos_bound (y + n) 8 ltac:(lia)) as M.
replace a with (y + n + 1 + Z.of_nat (Z.to_nat (a - (y + n + 1)))) by lia. apply H. lia.
Qed.

(* ======================================================================================================== *)
(* PART 3, at any image (PA parametric): a LIVE HARNESS BLOCK of the ledger, and the strcmp rule's per-string
   premises for a heap string and for a read-only image string.                                             *)
Section blk. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
Context {PI : PrhImg} {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation RLO := (@pa_relro_lo _ L PA).
#[local] Notation RHI := (@pa_relro_hi _ L PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* NAMED HYPOTHESIS LAWS: the allocator relation's laws at the harness head length cf_head. Text
   `AR_laws_x SEGS B ARx cf_head`, the same hypothesis lib/B/Prog/Crt102B_T4.v:491 takes; owner: the engine,
   discharged at the instance ARcfx by lib/Reusable/YGcallcf.v AR_laws_x_xs. *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* ---- a live harness block (a, k) of the ledger at (ly, S, Hp, W, mem), read at a later ARx state (ly1, S1, Hp1, W1,
   mem1, md1) with the same blocks and the same hidden heads (the walk's case: the ledger of a boundary, read at the
   memory of a load or a call inside the segment). The allocator block is (a - 16, k + 16); its user range [a, a + k)
   is application memory below alloc_ceiling, present, with a block shadow (all zero but a partial last granule) and
   a visible shadow hull; its tail granule is present. ---- *)
Lemma cb7t_blk_bounds : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly1 S1 Hp1 (W1 : world SEGS) mem1 md1
    a k,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (a, k) Lam ->
  0 <= k /\ a mod 16 = 0 /\ 4096 <= a /\ a + k <= YM05.alloc_ceiling /\ in_app a k /\ in_app (a - 16) (k + 16) /\
  (forall y, a <= y < a + k -> apresent (w_H W1) mem1 y) /\
  block_shadow (aview SEGS (w_H W1) mem1) SHADOW_OFF a k /\
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W1) mem1) a k) /\
  (forall y, a + k <= y < (a + k + 7) / 8 * 8 -> aview SEGS (w_H W1) mem1 y <> None) /\
  (forall y n, a <= y -> y + n <= a + k -> range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF y n) /\
  (forall y, a <= y -> y + 8 <= a + k -> y mod 8 = 0 -> aview SEGS (w_H W1) mem1 (shadow_addr y) = Some 0).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 a k HLED HAR1 EB EH Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk0 & Hab & Hhp & H16 & _).
assert (Hch16 : @cf_head CfParams_preset = 16) by reflexivity.
rewrite Hch16 in Hab, Hhp. rewrite <- EB in Hab. rewrite <- EH in Hhp.
assert (Erq : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hab) as (_ & H4096 & Hcl & Happ & Hpres & _).
destruct (alx_hshadow _ _ _ LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hab Hhp) as (Hbs & Hhull).
pose proof (fun y => alx_blocks_tail _ _ _ LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ y HAR1 Hab) as Htl.
rewrite Hch16 in Hbs, Hhull.
rewrite Erq in Hcl, Happ, Hpres, Hbs, Hhull, Htl.
replace (a - 16 + 16) with a in Hbs, Hhull by lia. replace (k + 16 - 16) with k in Hbs, Hhull by lia.
replace (a - 16 + (k + 16)) with (a + k) in Hcl, Htl by lia.
split; [exact Hk0|]. split; [exact H16|]. split; [lia|]. split; [lia|].
split; [apply (in_app_sub _ _ _ _ Happ); lia|]. split; [exact Happ|].
split; [intros y Hy; exact (proj1 (Hpres y ltac:(lia)))|].
split; [exact Hbs|].
split; [intros Hk; apply Hhull; lia|].
split; [intros y Hy; apply Htl; lia|].
split; [intros y n Hy1 Hy2; exact (cb7t_ra_of_bshadow _ a k y n Hbs Hy1 Hy2)|].
intros y Hy1 Hy2 Hy8.
destruct Hbs as (Ha8 & _ & Hb).
assert (Ea : a = a / 8 * 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia).
assert (Ey : y = y / 8 * 8) by (pose proof (Z.div_mod y 8 ltac:(lia)); lia).
assert (Hjk : y / 8 - a / 8 + 1 <= k / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hk7 : k / 8 <= (k + 7) / 8) by (apply Z.div_le_mono; lia).
assert (Hj0 : a / 8 <= y / 8) by (apply Z.div_le_mono; lia).
specialize (Hb (y / 8 - a / 8) ltac:(lia)).
rewrite (proj2 (Z.ltb_lt (y / 8 - a / 8) (k / 8)) ltac:(lia)) in Hb.
unfold shadow_of_addr in Hb. unfold shadow_addr.
replace (SHADOW_OFF + y / 8) with (SHADOW_OFF + a / 8 + (y / 8 - a / 8)) by lia. exact Hb.
Qed.

(* ---- THE SHADOW WINDOWS the walk's three ASan shadow loads read, in the symbolic engine's reader spelling
   (YP0j.v:343 rd_of over the restricted memory, :345-346 shent_ok's range_addressable): any window inside a live
   block, and its two instances, the key word keys[i] (8 bytes) and the first 24 bytes of the kid kids[i] (type at
   0, str at 16) ---- *)
Lemma cb7t_sh_win : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly1 S1 Hp1 (W1 : world SEGS) mem1 md1
    a k addr n,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (a, k) Lam -> a <= addr -> addr + n <= a + k ->
  range_addressable (fun y => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict (w_H W1) mem1) y))
    SHADOW_OFF addr n.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 a k addr n HLED HAR1 EB EH Hin H1 H2.
destruct (cb7t_blk_bounds ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 a k HLED HAR1 EB EH Hin)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hra & _).
exact (Hra addr n H1 H2).
Qed.

Lemma cb7t_sh_win_keys : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly1 S1 Hp1 (W1 : world SEGS) mem1 md1
    keys cap i,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (keys, 8 * cap) Lam -> 0 <= i < cap ->
  range_addressable (fun y => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict (w_H W1) mem1) y))
    SHADOW_OFF (keys + 8 * i) 8.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 keys cap i HLED HAR1 EB EH Hin Hi.
apply (cb7t_sh_win ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 keys (8 * cap)); [assumption.. | lia | lia].
Qed.

Lemma cb7t_sh_win_kids : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly1 S1 Hp1 (W1 : world SEGS) mem1 md1
    kids cap i,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  In (kids, 56 * cap) Lam -> 0 <= i < cap ->
  range_addressable (fun y => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict (w_H W1) mem1) y))
    SHADOW_OFF (kids + 56 * i) 24.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 kids cap i HLED HAR1 EB EH Hin Hi.
apply (cb7t_sh_win ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 kids (56 * cap)); [assumption.. | lia | lia].
Qed.

(* ---- a HEAP string of the reader (pj_cstrR over the ledger's blocks) meets the x-side premises of
   YGcallMxmn.v aj_strcmp_at_xro at kx = its length (port of S9's Wsame_memB.v s9_str_ok, with amem_range8 for
   amem_range and no S9_BMAX: the block law's alloc_ceiling bound gives x + kx + 1 <= 2 ^ 63) ---- *)
Lemma cb7t_str_prem : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own ly1 S1 Hp1 (W1 : world SEGS) mem1 md1
    (regsT : bvmap 5 word) x k s,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> Hp1 = Hp ->
  pj_cstrR SEGS (mrestrict (w_H W1) mem1) (prh_lin Lam) x k s ->
  YM05.alloc_ceiling + ESTACK <= spZ regsT ->
  0 < x /\ 0 <= Z.of_nat (length s) /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ x + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
  first_byte SEGS W1 mem1 x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)) /\
  src_ok SEGS W1 regsT mem1 x (Z.of_nat (length s) + 1) /\
  (forall a, x <= a <= x + Z.of_nat (length s) -> a < YM05.alloc_ceiling) /\
  YGcallMx.amem_range8 x (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W1) mem1) x (Z.of_nat (length s) + 1) /\
  (forall a, x + Z.of_nat (length s) < a < x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W1) mem1 a <> None).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 regsT x k s HLED HAR1 EB EH Hc Hsp.
destruct Hc as (Hin & Hk & H32 & Fs & Gs). unfold prh_lin in Hin.
destruct (cb7t_blk_bounds ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 x k HLED HAR1 EB EH Hin)
  as (Hk0 & H16 & H4096 & Hcl & Happ & Happ16 & Hpres & Hbs & Hhull & Htl & Hra & _).
pose proof YM05.alloc_ceiling_lt as Hlt.
assert (PRES : forall a, x <= a < x + k -> aview SEGS (w_H W1) mem1 a <> None).
{ intros a Ha. apply cb7t_aview_pres. exact (Hpres a Ha). }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold first_byte. split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) s 0).
    assert (Hj : (Z.to_nat i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (cb7t_garr8_at SEGS (w_H W1) mem1 x (s ++ [0]) (Z.to_nat i) Gs Hj) as A.
    rewrite Z2Nat.id in A by lia. rewrite app_nth1 in A by lia. split; [exact A|].
    assert (Hn : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Fs _ Hn) as Hc. cbv beta in Hc. lia.
  - intros _.
    assert (Hj : (length s < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (cb7t_garr8_at SEGS (w_H W1) mem1 x (s ++ [0]) (length s) Gs Hj) as A.
    rewrite nth_middle in A. exact A. }
split; [intros a Ha; split; [apply PRES; lia | lia]|].
split; [intros a Ha; lia|].
split.
{ pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold YGcallMx.amem_range8, in_app, kLowShadowBeg, ASAN_CEIL in *. rewrite C3, C4, C5. lia. }
split; [apply Hra; lia|].
split; [apply (cb7t_hull_sub _ x k x (Z.of_nat (length s) + 1)); [apply Hhull; lia | lia | lia | lia]|].
intros a Ha.
pose proof (Z.div_mod (x + Z.of_nat (length s)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (x + k + 7) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (x + k + 7) 8 ltac:(lia)) as M3.
destruct (Z.lt_ge_cases a (x + k)) as [Hak | Hak]; [apply PRES; lia|].
apply Htl. lia.
Qed.

(* ---- a READ-ONLY image string y (kept_img, the text's premise for check_round_trip's two strings) whose bytes s ++
   [0] are the image's at y meets the same premises, at the view of any ARx state whose read-only bytes are the
   image's (arodata_okP, a conjunct of every crt boundary, Crt102Glue.v crt_side). The two named hypotheses below
   are what kept_img does not give at a generic ARx: the hull (8 shadow bytes, i.e. 64 image bytes around the
   string, beyond the string's own granules) and the 8-alignment of the zero-shadow ranges (kept_img's in_zs arm). *)
Section rom.
(* NAMED HYPOTHESIS BOK. Text `asyms_ok B`. Used for aso_zshadow only (every as_zero_shadow range starts and ends on
   an 8-byte boundary). Owner: image B's generated start-up record lib/Reusable/YF0m.v TfibSyms (field ts_ok, :1602),
   discharged where the instance fixes B (the image instance / the unit's top). *)
Hypothesis BOK : asyms_ok B.
(* NAMED HYPOTHESIS IMGVIS, here over the instance's image band [pa_lo, pa_hi) (kept_img's band). Text `forall ly S
   Hp (W : world SEGS) mem md a, ARx ly S Hp W mem md -> pa_lo <= a < pa_hi -> aview SEGS (w_H W) mem (shadow_addr
   a) <> None`. The image's shadow is visible in every ARx state. Owner: the visibility row (Definition img_shadow_vis_cf,
   lib/Reusable/YGcfAmx2.v:47, the same statement over ARcf at cf_img_lo / cf_img_top; at image B CfImgB.CfImg_B's
   [cf_img_lo, cf_img_top) is PI_prog_B's [pa_lo, pa_hi), cb7t_band_eq_B in Section bi below);
   lib/B/Prog/FuzzStrdupB.v takes it at CfImg_B as a Section hypothesis too. *)
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @pa_lo _ L PA <= a < @pa_hi _ L PA -> aview SEGS (w_H W) mem (shadow_addr a) <> None.

Lemma cb7t_rom_prem_gen : forall ly S Hp (W : world SEGS) mem md (regsT : bvmap 5 word) y (s : list Z),
  0 <= @pa_lo _ L PA /\ @pa_hi _ L PA + 64 <= kLowMemEnd ->
  ARx ly S Hp W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  kept_img B y (Z.of_nat (length s) + 1) ->
  (forall j, (j < length (s ++ [0%Z]))%nat ->
     option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 (y + Z.of_nat j))) =
     Some (nth j (s ++ [0]) 0)) ->
  Forall (fun c => c <> 0) s ->
  (forall j, (j < 8)%nat -> seg_rom SEGS (Z_to_bv 64 (y + Z.of_nat (length s) + 1 + Z.of_nat j)) <> None) ->
  YM05.alloc_ceiling + ESTACK <= spZ regsT ->
  0 < y /\ 0 <= Z.of_nat (length s) /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ y + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
  first_byte SEGS W mem y (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)) /\
  src_ok SEGS W regsT mem y (Z.of_nat (length s) + 1) /\
  (forall a, y <= a <= y + Z.of_nat (length s) -> a < YM05.alloc_ceiling) /\
  YGcallMx.amem_range8 y (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF y (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) y (Z.of_nat (length s) + 1) /\
  (forall a, y + Z.of_nat (length s) < a < y + Z.of_nat (length s) - (y + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md regsT y s HBAND HAR HRO HKI HROM Fs HTL Hsp.
pose proof HKI as (Hlo & Hhi & HK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HBAND as (HB0 & HB1).
assert (Hlo' : 64 <= y) by lia.
assert (Hhi' : y + (Z.of_nat (length s) + 1) + 128 <= 0x7fff8000) by (rewrite <- C5; lia).
assert (VAL : forall j, (j < length (s ++ [0%Z]))%nat ->
  aview SEGS (w_H W) mem (y + Z.of_nat j) = Some (nth j (s ++ [0]) 0)).
{ intros j Hj. pose proof Hj as Hj'. rewrite length_app in Hj'. cbn [length] in Hj'.
  destruct (HK (y + Z.of_nat j) ltac:(lia)) as (Hr & Ho & He & _).
  rewrite (HRO _ Hr Ho He). exact (HROM j Hj). }
assert (VIS : forall a, y <= a < y + Z.of_nat (length s) + 1 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha.
  assert (Hj : (Z.to_nat (a - y) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof (VAL _ Hj) as E. rewrite Z2Nat.id in E by lia. replace (y + (a - y)) with a in E by lia.
  rewrite E. discriminate. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold first_byte. split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) s 0).
    assert (Hj : (Z.to_nat i < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (VAL _ Hj) as A.
    rewrite Z2Nat.id in A by lia. rewrite app_nth1 in A by lia. split; [exact A|].
    assert (Hn : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
    exact (proj1 (Forall_forall _ _) Fs _ Hn).
  - intros _.
    assert (Hj : (length s < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (VAL _ Hj) as A. rewrite nth_middle in A. exact A. }
split; [intros a Ha; split; [apply VIS; lia | lia]|].
split; [intros a Ha; lia|].
split; [unfold YGcallMx.amem_range8; rewrite C5; lia|].
split.
{ intros x Hx. destruct (HK x Hx) as (_ & _ & _ & [Hzg | (v & Hcell & Hv)]).
  - destruct Hzg as (q & m & Hin & Hq & Hqm).
    pose proof (proj1 (Forall_forall _ _) (aso_zshadow B BOK) (q, m) Hin) as (Z1 & Z2 & Z3 & Z4 & Z5).
    cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
    pose proof (alx_zshadow _ _ _ LAWS ly S Hp W mem md (q, m) HAR
      ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
    cbn [fst snd] in Hz.
    pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
    exact (zero_shadow_range (aview SEGS (w_H W) mem) SHADOW_OFF q m Z3 Z4 Hz x ltac:(lia)).
  - pose proof (proj1 (Forall_forall _ _) (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR) _ (Hcell ly)) as Hc.
    unfold cell_holds, z1, c1 in Hc. cbn [c_at c_w c_val aeval] in Hc.
    specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
    pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
    assert (Hb : YG0f.le_byte v 1 0 = v).
    { unfold YG0f.le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
      replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
      change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
    exists v. split; [|exact Hv].
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite Hc, Hb. reflexivity. }
split.
{ intros s0 Hs. destruct (cb7t_hull_img (@pa_lo _ L PA) (@pa_hi _ L PA) y (Z.of_nat (length s) + 1) s0 ltac:(lia)
    Hlo Hhi Hs) as [E Hr].
  rewrite E. exact (IMGVIS ly S Hp W mem md _ HAR Hr). }
apply (cb7t_tail_idx (fun a => aview SEGS (w_H W) mem a <> None) y (Z.of_nat (length s))).
intros j Hj. apply cb7t_aview_rom. exact (HTL j Hj).
Qed.
End rom.
End blk.

(* ======================================================================================================== *)
(* PART 4, image B' (lib/B/PAImg_prog.v PI_prog_B): the read-only premise bundle for check_round_trip's two strings,
   "modifiedAt" at CRT_MOD_AT_B and the stamp at CRT_STAMP_B (Crt102Img.v:1024-1025), from their kept_img (the
   text's premise, PRH_FnCheck.v tcheck_round_trip_specX) and the image bytes crt_str_rom_B (Crt102Img.v:1050). *)
Section bi. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation MOD_AT := (@CRT_MOD_AT_B _ PA).
#[local] Notation STAMP := (@CRT_STAMP_B _ PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* NAMED HYPOTHESES LAWS / BOK as in Section blk / rom above, at PA := PI_prog_B; IMGVIS in its owner's own form at
   image B: YGcfAmx2.img_shadow_vis_cf's band [cf_img_lo, cf_img_top) at ci := CfImgB.CfImg_B (the owner's
   statement over ARcf where the invariant is ARcf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.

(* PI_prog_B's band (kept_img's, pa_lo / pa_hi) is CfImg_B's [cf_img_lo, cf_img_top) and lies far below kLowMemEnd *)
Lemma cb7t_band_eq_B : @pa_lo _ B_prog_listing PA = @cf_img_lo CfImgB.CfImg_B /\
  @pa_hi _ B_prog_listing PA = @cf_img_top CfImgB.CfImg_B.
Proof. split; reflexivity. Qed.
Lemma cb7t_band_B : 0 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA + 64 <= kLowMemEnd.
Proof.
destruct cb7t_band_eq_B as [E1 E2]. rewrite E1, E2.
pose proof asan_consts as (_ & _ & _ & _ & C5). rewrite C5. vm_compute. split; discriminate.
Qed.
Lemma cb7t_imgvis_band : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha. destruct cb7t_band_eq_B as [E1 E2]. rewrite E1, E2 in Ha.
exact (IMGVIS ly S Hp W mem md a HAR Ha).
Qed.

Lemma cb7t_base_B : @pa_val _ B_prog_listing PA A_TEXT = B_prog_base.
Proof. vm_compute. reflexivity. Qed.

(* the granule tails past the two NULs are image bytes (by computation on the generated segments) *)
Lemma cb7t_tail_mod_at_B : forall j, (j < 8)%nat ->
  seg_rom SEGS (Z_to_bv 64 (MOD_AT + Z.of_nat (length ck_MOD_AT) + 1 + Z.of_nat j)) <> None.
Proof. intros j Hj. do 8 (destruct j as [|j]; [vm_compute; discriminate|]). lia. Qed.
Lemma cb7t_tail_stamp_B : forall j, (j < 8)%nat ->
  seg_rom SEGS (Z_to_bv 64 (STAMP + Z.of_nat (length ck_STAMP) + 1 + Z.of_nat j)) <> None.
Proof. intros j Hj. do 8 (destruct j as [|j]; [vm_compute; discriminate|]). lia. Qed.

Lemma cb7t_nz_mod_at : Forall (fun c => c <> 0) ck_MOD_AT.
Proof. apply Forall_forall. intros c Hc. cbn [ck_MOD_AT In] in Hc. repeat destruct Hc as [<- | Hc]; first [discriminate | contradiction]. Qed.
Lemma cb7t_nz_stamp : Forall (fun c => c <> 0) ck_STAMP.
Proof. apply Forall_forall. intros c Hc. cbn [ck_STAMP In] in Hc. repeat destruct Hc as [<- | Hc]; first [discriminate | contradiction]. Qed.

Lemma cb7t_rom_prem_mod_at : forall ly S Hp (W : world SEGS) mem md (regsT : bvmap 5 word),
  ARx ly S Hp W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  @kept_img _ B_prog_listing PA B MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) ->
  YM05.alloc_ceiling + ESTACK <= spZ regsT ->
  0 < MOD_AT /\ 0 <= Z.of_nat (length ck_MOD_AT) /\ Z.of_nat (length ck_MOD_AT) + 1 < 2 ^ 32 /\
  MOD_AT + Z.of_nat (length ck_MOD_AT) + 1 <= 2 ^ 63 /\
  first_byte SEGS W mem MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) 0 (Z.of_nat (length ck_MOD_AT)) /\
  src_ok SEGS W regsT mem MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) /\
  (forall a, MOD_AT <= a <= MOD_AT + Z.of_nat (length ck_MOD_AT) -> a < YM05.alloc_ceiling) /\
  YGcallMx.amem_range8 MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) /\
  (forall a, MOD_AT + Z.of_nat (length ck_MOD_AT) < a <
     MOD_AT + Z.of_nat (length ck_MOD_AT) - (MOD_AT + Z.of_nat (length ck_MOD_AT)) mod 8 + 8 ->
     aview SEGS (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md regsT HAR HRO HKI Hsp.
destruct (crt_str_rom_B (PA := PA) cb7t_base_B eq_refl) as (HM & _).
exact (cb7t_rom_prem_gen B ARx LAWS BOK cb7t_imgvis_band ly S Hp W mem md regsT MOD_AT ck_MOD_AT cb7t_band_B HAR HRO HKI HM
  cb7t_nz_mod_at cb7t_tail_mod_at_B Hsp).
Qed.

Lemma cb7t_rom_prem_stamp : forall ly S Hp (W : world SEGS) mem md (regsT : bvmap 5 word),
  ARx ly S Hp W mem md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) ->
  @kept_img _ B_prog_listing PA B STAMP (Z.of_nat (length ck_STAMP) + 1) ->
  YM05.alloc_ceiling + ESTACK <= spZ regsT ->
  0 < STAMP /\ 0 <= Z.of_nat (length ck_STAMP) /\ Z.of_nat (length ck_STAMP) + 1 < 2 ^ 32 /\
  STAMP + Z.of_nat (length ck_STAMP) + 1 <= 2 ^ 63 /\
  first_byte SEGS W mem STAMP (Z.of_nat (length ck_STAMP) + 1) 0 (Z.of_nat (length ck_STAMP)) /\
  src_ok SEGS W regsT mem STAMP (Z.of_nat (length ck_STAMP) + 1) /\
  (forall a, STAMP <= a <= STAMP + Z.of_nat (length ck_STAMP) -> a < YM05.alloc_ceiling) /\
  YGcallMx.amem_range8 STAMP (Z.of_nat (length ck_STAMP) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF STAMP (Z.of_nat (length ck_STAMP) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) STAMP (Z.of_nat (length ck_STAMP) + 1) /\
  (forall a, STAMP + Z.of_nat (length ck_STAMP) < a <
     STAMP + Z.of_nat (length ck_STAMP) - (STAMP + Z.of_nat (length ck_STAMP)) mod 8 + 8 ->
     aview SEGS (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md regsT HAR HRO HKI Hsp.
destruct (crt_str_rom_B (PA := PA) cb7t_base_B eq_refl) as (_ & HS).
exact (cb7t_rom_prem_gen B ARx LAWS BOK cb7t_imgvis_band ly S Hp W mem md regsT STAMP ck_STAMP cb7t_band_B HAR HRO HKI HS
  cb7t_nz_stamp cb7t_tail_stamp_B Hsp).
Qed.
End bi.
