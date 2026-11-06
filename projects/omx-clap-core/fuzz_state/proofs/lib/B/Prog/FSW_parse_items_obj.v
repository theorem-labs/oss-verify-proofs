(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) B-LOCAL COPY of the A walk's object lemmas, copied from
   a working branch 4480a5df1ae proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items_obj.v
   (a Theorem Labs lane). It has no B twin. The lemmas take each step's memory effect as hypotheses and name no instruction
   address; the changes are the imports (lib/A image modules -> their lib/B twins, A's lib/A/Prog FSW_pj_set_heads ->
   lib/B/Prog FSW_pj_set_heads); statements and proofs verbatim.
   The A header, kept: *)
(* fs program part, READER lane (a Theorem Labs lane): the OBJECT lemmas of parse_items' member loop
   (A 0x84a04), for parse_items_spec's composition. One member is grow, parse_string (the key), the walk's store
   keys[n] := key, __asan_memset of the kid, parse_value (level k + 1) of the kid, the walk's store v->n := n + 1. These
   lemmas carry the OBJECT v (Prog/parse_items_shape.v pis_open over the live list L = pis_slots ++ Di) and its BLOCK
   BOOKKEEPING (L against ablocks and U, rd_sum L = held T) across each step; each step's memory effect arrives as
   hypotheses (the walk's journals and symbolic runs are not their business):
     pio_close : the members done, v is a tree (rtree) of JObj dn over L.
     pio_snoc  : the store v->n := n + 1 closes the member: pis_open with (kk, x) appended.
     pio_key   : parse_string's block (a, |kk| + 1) and the store keys[n] := a join L.
     pio_zero  : __asan_memset of the kid keeps everything pio_key concluded.
     pio_value : parse_value's blocks Dx join L, the kid vk is a pj_node of x over L ++ Dx.
     pio_grow  : grow's new kids / keys blocks replace the old ones in L.
   Template: lib/A/Prog/FSW_pj_set_fn.v (Section P: pj_set's grow + key + kid + n++ is the same object move), the grow
   step of lib/A/Prog/FSW_pj_set_holds.v, and lib/A/Prog/FSW_pj_set_heads.v (imported); idioms copied, no Section-local
   lemma of theirs imported.
   Rule 24: a lemma file for function parse_items (no function's contract is proved here). Lookup for parse_items
   (proof-index by name, 03:15Z, exit 0, a Theorem Labs lane's lookup/parse_items.resume.0315.txt): 14 named, 26 by
   address, 12 related, 7 lemma(s); the check verdict (a Theorem Labs lane's lookup/confirm-resume.md, by name and by address in
   both images, A 0x84a04 / B 0x84e70): parse_items: CONFIRM (no ASan donor; the walk is needed). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_kit FSW_parse_items_mdl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section O. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ================= helpers (idioms of lib/A/Prog/FSW_pj_set_fn.v Section F, restated here) ================= *)
Lemma pio_mbyte_raw : forall (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  mbyte tfibsegs m' x = mbyte tfibsegs m x.
Proof. intros m m' x E. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma pio_same_raw : forall (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  parse_items_shape.pis_same tfibsegs m m' x.
Proof.
intros m m' x E. split; [exact (pio_mbyte_raw m m' x E) | intros Hw; exact (writable_at_eq tfibsegs m m' x E Hw)].
Qed.

Lemma pio_aview_raw : forall (H : word -> bool) (m m' : word -> option byte) x,
  mrestrict H m' (Z_to_bv 64 x) = mrestrict H m (Z_to_bv 64 x) -> aview tfibsegs H m' x = aview tfibsegs H m x.
Proof. intros H m m' x E. unfold aview. rewrite (pio_mbyte_raw _ _ x E). reflexivity. Qed.

Lemma pio_raw_of_mbyte : forall (m m' : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x ->
  mbyte tfibsegs m' x = mbyte tfibsegs m x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
intros m m' x Hx Hn E. unfold mbyte in E. rewrite (YCbq.seg_rom_none tfibsegs x Hx Hn) in E.
destruct (m' (Z_to_bv 64 x)), (m (Z_to_bv 64 x)); congruence.
Qed.

Lemma pio_req_hb : forall k, 0 < k -> req_size (k + HEAD) = k + HEAD.
Proof. intros k Hk. unfold req_size, HEAD. destruct (Z.eqb_spec (k + 16) 0); lia. Qed.

Lemma pio_pstat_off : forall x, x < 0x10000 \/ FS_IMG_END <= x -> ~ inFP FS_PSTAT_FP x.
Proof.
intros x Hx (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold FS_IMG_END in Hx.
destruct Hr as [E|[E|[E|[E|[]]]]]; subst r; cbn [fst snd] in Ha; lia.
Qed.

Lemma pio_shadow_rng : forall x, 0 <= x < alloc_ceiling ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44 /\ 0 <= shadow_of_addr SHADOW_OFF x < alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _). pose proof (fsw_shadow_below x Hx) as Hb.
split; [|exact Hb]. unfold shadow_of_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* a byte of the kids / keys arrays (first len slots) or of a member block lies in a block of slots ++ Di *)
Lemma pio_ifoot_in : forall kids keys cap len Di x, 0 <= len <= cap ->
  parse_items_shape.pis_ifoot true kids keys len Di x ->
  exists b, In b (parse_items_shape.pis_slots true kids keys cap ++ Di) /\ PjStruct.pj_holds b x.
Proof.
intros kids keys cap len Di x Hl [Hx|[(_ & Hx)|(b & Hb & Hx)]].
- exists (kids, 56 * cap). split.
  + apply in_or_app. left. unfold parse_items_shape.pis_slots, ReaderRes.kids_blk.
    rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
  + unfold PjStruct.pj_holds. cbn [fst snd]. lia.
- exists (keys, 8 * cap). split.
  + apply in_or_app. left. unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
    rewrite (proj2 (Z.eqb_neq cap 0)) by lia. cbn. right. left. reflexivity.
  + unfold PjStruct.pj_holds. cbn [fst snd]. lia.
- exists b. split; [apply in_or_app; right; exact Hb | exact Hx].
Qed.

(* ---- AR's block geometry ---- *)
Lemma pio_blk_geo : forall ly S (W : world tfibsegs) mx md P N x, AR tfibsegs B ly S W mx md ->
  In (P, N) (ablocks B ly S) -> P <= x < P + req_size N ->
  4096 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros ly S W mx md P N x HAR Hin Hx.
destruct (fsw_ablock_low B ly S W mx md P N HAR Hin) as (L1 & L2 & _).
split; [lia|]. split; [|split].
- refine (proj2 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md x HAR _)).
  left. exists P, N. split; [exact Hin | exact Hx].
- apply pio_pstat_off. destruct (fsw_ablock_off_img B ly S W mx md P N HAR Hin); lia.
- exact (fsw_ablock_off_shadow B ly S W mx md P N HAR Hin x Hx).
Qed.

Lemma pio_rb_geo : forall ly S (W : world tfibsegs) mx md m p k x, AR tfibsegs B ly S W mx md ->
  fs_rblock tfibsegs B ly S W m p k -> p - HEAD <= x < p + k ->
  4096 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros ly S W mx md m p k x HAR (Hin & _ & Hk & _) Hx.
apply (pio_blk_geo ly S W mx md (p - HEAD) (k + HEAD) x HAR Hin). rewrite pio_req_hb by exact Hk.
unfold HEAD in *. lia.
Qed.

Lemma pio_v_geo : forall ly S (W : world tfibsegs) mx md m v x, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> v <= x < v + 56 ->
  4096 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros ly S W mx md m v x HAR HP Hx.
destruct (fsw_pobj_low B ly S W mx md m v HAR HP) as (L1 & L2).
assert (Hi : ~ in_img tfibsegs x).
{ pose proof HP as ([((cid & pos & Hin & _ & _ & F1 & F2) & _)|((b & mm & Hin & B1 & B2) & _)] & _);
    refine (proj2 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md x HAR _)).
  - right. left. exists cid, pos. split; [exact Hin | lia].
  - left. exists b, mm. split; [exact Hin | unfold HEAD in B1; lia]. }
split; [lia|]. split; [exact Hi|]. split.
- apply pio_pstat_off. destruct (fsw_pobj_off_img B ly S W mx md m v HAR HP); lia.
- exact (fsw_pobj_off_shadow B ly S W mx md m v HAR HP x Hx).
Qed.

(* the head of a reader block is not inside a placed object (pSh_obj_apart's three cases) *)
Lemma pio_head_off_obj : forall ly S (W : world tfibsegs) mx md m v p k x, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> In (p - HEAD, k + HEAD) (ablocks B ly S) -> 0 < k ->
  p - HEAD <= x < p - HEAD + 8 -> ~ (v <= x < v + 56).
Proof.
intros ly S W mx md m v p k x HAR HP Hin Hk Hx.
pose proof (pio_req_hb k Hk) as E.
destruct (pSh_obj_apart B ly S W mx md m v HAR HP (p - HEAD) (k + HEAD) Hin) as [H|[H|H]];
  rewrite ?E in H; unfold HEAD in *; lia.
Qed.

(* a reader block keeps its head when its 8 head bytes are kept *)
Lemma pio_rblock_keep : forall ly S (W : world tfibsegs) (m m' : word -> option byte) p k,
  fs_rblock tfibsegs B ly S W m p k ->
  (forall x, p - HEAD <= x < p - HEAD + 8 -> rdW W m' (Z_to_bv 64 x) = rdW W m (Z_to_bv 64 x)) ->
  fs_rblock tfibsegs B ly S W m' p k.
Proof.
intros ly S W m m' p k (Hin & Hal & Hk & Hv) E.
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hk|].
intros j Hj. rewrite (pio_mbyte_raw _ _ _ (E (p - HEAD + Z.of_nat j) ltac:(lia))). exact (Hv j Hj).
Qed.

(* a placed object keeps its placement when its shadow bytes and its own writability are kept *)
Lemma pio_pobj_xfer : forall ly S (W : world tfibsegs) (m m' : word -> option byte) v, pobj tfibsegs B ly S W m v ->
  (forall x, v <= x < v + 56 ->
     aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (rdW W m') (v + i)) ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' v ([(Hf & H8 & Hr)|(Hb & H8 & Hr)] & _) Hsh Hw; (split; [|exact Hw]).
- left. split; [exact Hf|]. split; [exact H8|]. intros x Hx. destruct (Hr x Hx) as (s & Es & Ok).
  exists s. rewrite (Hsh x Hx). split; [exact Es | exact Ok].
- right. split; [exact Hb|]. split; [exact H8|]. intros x Hx. destruct (Hr x Hx) as (s & Es & Ok).
  exists s. rewrite (Hsh x Hx). split; [exact Es | exact Ok].
Qed.

Lemma pio_pstat_off_shadow : forall a, inFP FS_PSTAT_FP a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros a (r & Hr & Ha) Hs. unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold SHADOW_OFF in Hs.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.

(* two different live reader blocks are apart, heads included *)
Lemma pio_rb_disj : forall ly S (W : world tfibsegs) mx md p k q j x y, AR tfibsegs B ly S W mx md ->
  In (p - HEAD, k + HEAD) (ablocks B ly S) -> In (q - HEAD, j + HEAD) (ablocks B ly S) -> 0 < k -> 0 < j ->
  (p, k) <> (q, j) -> p - HEAD <= x < p + k -> q - HEAD <= y < q + j -> x <> y.
Proof.
intros ly S W mx md p k q j x y HAR Hp Hq Hk Hj Hne Hx Hy E. subst y.
assert (NE : (p - HEAD, k + HEAD) <> (q - HEAD, j + HEAD))
  by (intros E; injection E as E1 E2; apply Hne; f_equal; lia).
pose proof (sep_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md _ _ _ _ HAR Hp Hq NE) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite !pio_req_hb in D by assumption. unfold HEAD in *. lia.
Qed.

(* the head of a live reader block is no byte of a live reader block's body *)
Lemma pio_head_body : forall ly S (W : world tfibsegs) mx md p k q j x y, AR tfibsegs B ly S W mx md ->
  In (p - HEAD, k + HEAD) (ablocks B ly S) -> In (q - HEAD, j + HEAD) (ablocks B ly S) -> 0 < k -> 0 < j ->
  p - HEAD <= x < p - HEAD + 8 -> q <= y < q + j -> x <> y.
Proof.
intros ly S W mx md p k q j x y HAR Hp Hq Hk Hj Hx Hy. destruct (pSh_zz_dec (p, k) (q, j)) as [E|NE].
- injection E as -> ->. unfold HEAD in *. lia.
- apply (pio_rb_disj ly S W mx md p k q j x y HAR Hp Hq Hk Hj NE); unfold HEAD in *; lia.
Qed.

(* a block live after a step but not before it is apart from an object placed before it (frames kept, and the block
   holding the object kept) *)
Lemma pio_new_apart : forall ly S (W : world tfibsegs) m v ly' S' (W' : world tfibsegs) mx' md' P N,
  AR tfibsegs B ly' S' W' mx' md' -> pobj tfibsegs B ly S W m v ->
  frames S' = frames S -> (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
  (forall b mm, In (b, mm) (ablocks B ly S) -> b + HEAD <= v -> v + 56 <= b + req_size mm ->
     In (b, mm) (ablocks B ly' S')) ->
  In (P, N) (ablocks B ly' S') -> ~ In (P, N) (ablocks B ly S) ->
  forall z, P <= z < P + req_size N -> ~ (v <= z < v + 56).
Proof.
intros ly S W m v ly' S' W' mx' md' P N HAR' HPv Hfr HFA Hinc HP' HP z Hz Hv.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HPv as [[((cid & pos & Hcp & _ & _ & H1 & H2) & _)|((b & mm & Hb & H1 & H2) & _)] _].
- assert (Hcp' : In (cid, pos) (frames S')) by (rewrite Hfr; exact Hcp).
  pose proof (sep_block_frame tfibsegs B LAWS ly' S' W' mx' md' P N cid pos HAR' HP' Hcp') as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj. rewrite (HFA cid pos) in Dj. lia.
- assert (NE : (b, mm) <> (P, N)) by (intros E; rewrite E in Hb; exact (HP Hb)).
  pose proof (sep_blocks tfibsegs B LAWS ly' S' W' mx' md' b mm P N HAR' (Hinc _ _ Hb H1 H2) HP' NE) as Dj.
  unfold zdisjoint in Dj. cbn [fst snd] in Dj.
  assert (Hm : mm <= req_size mm) by (unfold req_size; destruct (Z.eqb_spec mm 0); lia).
  unfold HEAD in H1. lia.
Qed.

(* a call's journal (own = []) keeps the fake frames and their addresses *)
Lemma pio_jr_frames : forall STK sp FP ly S (W : world tfibsegs) mx md ly' S' (W' : world tfibsegs) mx' md' kc,
  ajournal tfibsegs B STK sp FP ly S W mx md [] ly' S' W' mx' md' kc -> AR tfibsegs B ly S W mx md ->
  frames S' = frames S /\ (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos).
Proof.
intros STK sp FP ly S W mx md ly' S' W' mx' md' kc HJ HAR. pose proof HJ as (_ & Hly & _ & _ & _ & Hfr & _).
destruct (al_layout tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md ly' HAR Hly) as (_ & HFA & _).
split; [exact Hfr | exact HFA].
Qed.

(* the live list of a Permutation of a state's blocks has no duplicate, and is fresh against the rest *)
Lemma pio_nodup_L : forall ly S (W : world tfibsegs) mx md A L, AR tfibsegs B ly S W mx md ->
  Permutation (ablocks B ly S) (A ++ rd_hblocks L) -> NoDup L.
Proof.
intros ly S W mx md A L HAR HP.
pose proof (Permutation_NoDup HP (pSh_ablocks_nodup B ly S W mx md HAR)) as ND.
apply NoDup_ListNoDup in ND. pose proof (parse_items_shape.pis_nodup_r _ _ _ ND) as ND3.
apply NoDup_ListNoDup in ND3. unfold rd_hblocks in ND3. apply NoDup_ListNoDup.
eapply List.NoDup_map_inv. exact ND3.
Qed.

Lemma pio_perm_fresh : forall ly S (W : world tfibsegs) mx md A D p k, AR tfibsegs B ly S W mx md ->
  Permutation (ablocks B ly S) (A ++ rd_hblocks D) -> In (p, k) D -> ~ In (p - HEAD, k + HEAD) A.
Proof.
intros ly S W mx md A D p k HAR HP Hpk HA.
pose proof (Permutation_NoDup HP (pSh_ablocks_nodup B ly S W mx md HAR)) as ND.
apply NoDup_ListNoDup in ND.
apply (parse_items_shape.pis_nodup_app_disj _ _ _ _ ND HA).
unfold rd_hblocks. exact (in_map (fun b => (fst b - HEAD, snd b + HEAD)) D (p, k) Hpk).
Qed.

(* a byte off the kid and off the image statics is off parse_value's footprint *)
Lemma pio_inFP_kid : forall vk z, ~ (vk <= z < vk + 56) -> ~ inFP FS_PSTAT_FP z ->
  ~ inFP ([(vk, vk + 56)] ++ FS_PSTAT_FP) z.
Proof.
intros vk z H1 H2 (r & Hr & Hz). apply in_app_or in Hr as [[<-|[]]|Hr].
- cbn [fst snd] in Hz. exact (H1 Hz).
- apply H2. exists r. split; [exact Hr | exact Hz].
Qed.

(* the 16-byte head of a reader block is not inside a placed object *)
Lemma pio_head16_off_obj : forall ly S (W : world tfibsegs) mx md m v p k x, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> In (p - HEAD, k + HEAD) (ablocks B ly S) -> 0 < k ->
  p - HEAD <= x < p -> ~ (v <= x < v + 56).
Proof.
intros ly S W mx md m v p k x HAR HP Hin Hk Hx. pose proof (pio_req_hb k Hk) as E.
destruct (pSh_obj_apart B ly S W mx md m v HAR HP (p - HEAD) (k + HEAD) Hin) as [H|[H|H]];
  rewrite ?E in H; unfold HEAD in *; lia.
Qed.

(* a reader block whose body is apart from a placed object is apart from it, head included *)
Lemma pio_blk_off_obj : forall ly S (W : world tfibsegs) mx md m v p k, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> In (p - HEAD, k + HEAD) (ablocks B ly S) -> 0 < k ->
  (forall x, p <= x < p + k -> ~ (v <= x < v + 56)) ->
  forall z, p - HEAD <= z < p + k -> ~ (v <= z < v + 56).
Proof.
intros ly S W mx md m v p k HAR HP Hin Hk Hb z Hz Hv. pose proof (pio_req_hb k Hk) as E.
destruct (pSh_obj_apart B ly S W mx md m v HAR HP (p - HEAD) (k + HEAD) Hin) as [H|[H|H]]; rewrite ?E in H.
- unfold HEAD in *. lia.
- unfold HEAD in *. lia.
- apply (Hb v); unfold HEAD in *; lia.
Qed.

(* a byte off v's two written fields, off the old kids / keys blocks and off the image statics is off grow's
   footprint *)
Lemma pio_off_FPg : forall v (D0 : list (Z * Z)) z, ~ (v + 24 <= z < v + 56) ->
  (forall p k, In (p, k) D0 -> ~ (p - HEAD <= z < p - HEAD + req_size (k + HEAD))) -> ~ inFP FS_PSTAT_FP z ->
  ~ inFP ([(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (rd_hblocks D0) ++ FS_PSTAT_FP) z.
Proof.
intros v D0 z Hv Ho Hp. rewrite !inFP_app. intros [H|[H|H]].
- rewrite !inFP_cons in H. destruct H as [H|[H|H]]; [lia | lia | exact (inFP_nil _ H)].
- destruct (pSh_inFP_hblocks _ _ H) as (p & k & Hpk & Hz). exact (Ho p k Hpk Hz).
- exact (Hp H).
Qed.

Lemma pio_wr_of_mbyte : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x ->
  mbyte tfibsegs m x = Some b -> writable_at tfibsegs m x.
Proof.
intros m x b Hx Hn H. unfold mbyte in H. rewrite (YCbq.seg_rom_none tfibsegs x Hx Hn) in H.
destruct (m (Z_to_bv 64 x)) eqn:E; [|discriminate H].
unfold writable_at, wview. rewrite E. discriminate.
Qed.

(* the i-th kid of an open object's member list is a node, so its bytes are present *)
Lemma pio_mems_node : forall (m : word -> option byte) lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D i,
  PjStruct.pj_mems tfibsegs m lblk P a ka l D -> (i < length l)%nat ->
  exists u D1, P (a + 56 * Z.of_nat i) u D1.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D i H Hi; [cbn in Hi; lia|].
cbn [PjStruct.pj_mems] in H. destruct H as (x & k & D1 & D2 & _ & _ & _ & HP & HR).
destruct i as [|i].
- exists u, D1. replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
- cbn [length] in Hi. destruct (IH (a + 56) (ka + 8) D2 i HR ltac:(lia)) as (u' & D' & HP').
  exists u', D'. replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia. exact HP'.
Qed.

Lemma pio_kids_present : forall (m : word -> option byte) lblk kids keys (ts : list PjTree.jv) ns Di i,
  parse_items_shape.pis_items tfibsegs m lblk true kids keys ts ns Di ->
  0 <= i < 56 * Z.of_nat (length ts) -> exists b, mbyte tfibsegs m (kids + i) = Some b.
Proof.
intros m lblk kids keys ts ns Di i Hit Hi. cbn [parse_items_shape.pis_items] in Hit. destruct Hit as (Hl & Hm).
assert (Q : 56 * (i / 56) <= i < 56 * (i / 56) + 56)
  by (pose proof (Z.mod_pos_bound i 56 ltac:(lia)); pose proof (Z.div_mod i 56 ltac:(lia)); lia).
assert (Hj : (Z.to_nat (i / 56) < length (combine ns ts))%nat).
{ rewrite (PjStruct.pj_combine_len _ _ ns ts Hl). assert (0 <= i / 56) by (apply Z.div_pos; lia). lia. }
destruct (pio_mems_node m lblk _ _ kids keys Di _ Hm Hj) as (u & D1 & HP).
pose proof (parse_items_shape.pis_node_rw tfibsegs _ _ _ _ _ HP) as (_ & (_ & _ & Hst)).
assert (Hr : kids + 56 * Z.of_nat (Z.to_nat (i / 56)) <= kids + i < kids + 56 * Z.of_nat (Z.to_nat (i / 56)) + 56)
  by (rewrite Z2Nat.id by (apply Z.div_pos; lia); lia).
destruct (Hst (kids + i) Hr) as (_ & b & Hb). exists b. exact Hb.
Qed.

Lemma pio_sum_slots : forall k y c, 0 <= c -> rd_sum (parse_items_shape.pis_slots true k y c) = 64 * c.
Proof.
intros k y c Hc. destruct (Z.eq_dec c 0) as [->|Hne]; [reflexivity|].
assert (E : parse_items_shape.pis_slots true k y c = [(k, 56 * c); (y, 8 * c)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq c 0)) by lia. reflexivity. }
rewrite E. unfold rd_sum. cbn [fold_right fst snd]. lia.
Qed.

(* ---- list facts for grow's U / block bookkeeping ---- *)
Lemma pio_ug_split : forall (U R U1 U2 : list (Z * Z)) x, U ++ R = U1 ++ x :: U2 -> ~ In x U ->
  exists X, U1 = U ++ X /\ R = X ++ x :: U2.
Proof.
induction U as [|u U IH]; intros R U1 U2 x E Hx.
- exists U1. split; [reflexivity | exact E].
- destruct U1 as [|u1 U1].
  + cbn [app] in E. injection E as E1 _. exfalso. apply Hx. left. exact E1.
  + cbn [app] in E. injection E as E1 E2. subst u1.
    destruct (IH R U1 U2 x E2 (fun H => Hx (or_intror H))) as (X & -> & ->).
    exists X. split; reflexivity.
Qed.

(* one fuzz_realloc's U step keeps the prefix U when the old head is not U's *)
Lemma pio_ug_step : forall (U R U' : list (Z * Z)) old new, ugrow1 (U ++ R) U' old new ->
  (old <> 0 -> ~ In (old - HEAD, HEAD) U) ->
  exists R', U' = U ++ R' /\ (old = 0 -> R' = R ++ [(new - HEAD, HEAD)]) /\
    (old <> 0 -> Permutation (R ++ [(new - HEAD, HEAD)]) ((old - HEAD, HEAD) :: R')).
Proof.
intros U R U' old new [(E0 & EU)|(Hne & U1 & U2 & E & EU)] HnU.
- exists (R ++ [(new - HEAD, HEAD)]). split; [rewrite EU, app_assoc; reflexivity|].
  split; [intros _; reflexivity | intros H; contradiction].
- destruct (pio_ug_split U R U1 U2 _ E (HnU Hne)) as (X & -> & ->).
  exists (X ++ U2 ++ [(new - HEAD, HEAD)]). split; [rewrite EU, <- app_assoc; reflexivity|].
  split; [intros H; contradiction|].
  intros _. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma pio_perm3 : forall (a b c : list (Z * Z)), Permutation (a ++ b ++ c) (c ++ b ++ a).
Proof.
intros a b c. rewrite app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma pio_perm_cancel : forall (A' Ac A0 hO hN hD : list (Z * Z)),
  Permutation (A' ++ hO) (Ac ++ hN) -> Permutation Ac (A0 ++ (hO ++ hD)) -> Permutation A' (A0 ++ (hN ++ hD)).
Proof.
intros A' Ac A0 hO hN hD H1 H2. apply (Permutation_app_inv_r hO).
eapply Permutation_trans; [exact H1|]. eapply Permutation_trans; [apply Permutation_app_tail; exact H2|].
rewrite <- !app_assoc. apply Permutation_app_head. apply pio_perm3.
Qed.

Lemma pio_heads_two : forall (Rd R1 R2 hD : list (Z * Z)) hk hy hk' hy',
  Permutation Rd (hk :: hy :: hD) -> Permutation (Rd ++ [hk']) (hk :: R1) -> Permutation (R1 ++ [hy']) (hy :: R2) ->
  Permutation R2 (hk' :: hy' :: hD).
Proof.
intros Rd R1 R2 hD hk hy hk' hy' H1 H2 H3.
assert (Q1 : Permutation R1 (hy :: hD ++ [hk'])).
{ apply Permutation_cons_inv with (a := hk). eapply Permutation_trans; [apply Permutation_sym; exact H2|].
  change (hk :: hy :: hD ++ [hk']) with ((hk :: hy :: hD) ++ [hk']). apply Permutation_app_tail. exact H1. }
assert (Q2 : Permutation R2 ((hD ++ [hk']) ++ [hy'])).
{ apply Permutation_cons_inv with (a := hy). eapply Permutation_trans; [apply Permutation_sym; exact H3|].
  change (hy :: (hD ++ [hk']) ++ [hy']) with ((hy :: hD ++ [hk']) ++ [hy']). apply Permutation_app_tail. exact Q1. }
eapply Permutation_trans; [exact Q2|]. rewrite <- app_assoc. cbn [app].
change (hk' :: hy' :: hD) with ([hk'; hy'] ++ hD). apply Permutation_app_comm.
Qed.

Lemma pio_heads_zero : forall (Rd hD : list (Z * Z)) hk' hy', Permutation Rd hD ->
  Permutation ((Rd ++ [hk']) ++ [hy']) (hk' :: hy' :: hD).
Proof.
intros Rd hD hk' hy' H. rewrite <- app_assoc. cbn [app].
change (hk' :: hy' :: hD) with ([hk'; hy'] ++ hD).
eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_head. exact H.
Qed.

(* ================= (O6) pio_close: the members done, v is a tree of JObj dn over L ================= *)
Lemma pio_close : forall ly1 S1 (W1 : world tfibsegs) mem v kids keys cap (dn : list (list Z * PjTree.jv)) Di,
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  parse_items_shape.pis_open tfibsegs (rdW W1 mem) (ReaderRes.lin L) v true 0 kids keys cap (Z.of_nat (length dn))
    (map snd dn) (map fst dn) Di ->
  rd_blocks_ok tfibsegs B ly1 S1 W1 mem L ->
  rtree tfibsegs B ly1 S1 W1 mem v (PjTree.JObj dn) L.
Proof.
intros ly1 S1 W1 mem v kids keys cap dn Di L Ho Hb.
split; [|split; [exact Hb | apply incl_refl]].
pose proof (parse_items_shape.pis_open_n tfibsegs _ _ _ _ _ _ _ _ _ _ _ _ Ho) as Hn.
rewrite <- (parse_items_shape.pis_combine_map _ _ dn).
apply (PjStruct.pj_open_obj tfibsegs _ _ v (Z.of_nat (length dn)) (map snd dn) (map fst dn) L).
split; [rewrite length_map; reflexivity | exact Hn].
Qed.

(* ================= (O5) pio_snoc: the walk's store v->n := n + 1 closes the member (kk, x) =================
   From pio_value's conclusions at mem6 (L3 = slots ++ (Di ++ [(a, Ka)] ++ Dx), the form app_assoc gives); the store
   changes only [v + 40, v + 48) below alloc_ceiling and writes le8 (n + 1) there. *)
Lemma pio_snoc : forall ly6 S6 U6 (W6 : world tfibsegs) mem6 md6 mem7 v text len tcap k' y' cap' (n : nat)
  (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) Di a Dx,
  let Ka := Z.of_nat (length kk) + 1 in
  let L3 := parse_items_shape.pis_slots true k' y' cap' ++ (Di ++ [(a, Ka)] ++ Dx) in
  length dn = n -> Z.of_nat n < cap' ->
  ARU tfibsegs B ly6 S6 U6 W6 mem6 md6 ->
  rd_blocks_ok tfibsegs B ly6 S6 W6 mem6 L3 -> rd_text tfibsegs B ly6 S6 W6 mem6 text len tcap ->
  pobj tfibsegs B ly6 S6 W6 mem6 v ->
  parse_items_shape.pis_open tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di ->
  PjStruct.pj_u64 tfibsegs (rdW W6 mem6) (y' + 8 * Z.of_nat n) a ->
  PjStruct.pj_cstr tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) a Ka kk ->
  PjStruct.pj_node tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) (k' + 56 * Z.of_nat n) x Dx ->
  NoDup L3 -> PjStruct.pj_apart ([(a, Ka)] ++ Dx) v ->
  (* the store v->n := n + 1 *)
  val_mem tfibsegs (rdW W6 mem7) (v + 40) 8 (Z.of_nat n + 1) ->
  (forall z, 0 <= z < alloc_ceiling -> ~ (v + 40 <= z < v + 48) ->
     rdW W6 mem7 (Z_to_bv 64 z) = rdW W6 mem6 (Z_to_bv 64 z)) ->
  (forall z, v + 40 <= z < v + 48 -> writable_at tfibsegs (rdW W6 mem7) z) ->
  PjStruct.pj_hdr tfibsegs (rdW W6 mem7) v 6 0 0 k' y' (Z.of_nat n + 1) cap' /\
  parse_items_shape.pis_open tfibsegs (rdW W6 mem7) (ReaderRes.lin L3) v true 0 k' y' cap'
    (Z.of_nat (length (dn ++ [(kk, x)]))) (map snd (dn ++ [(kk, x)])) (map fst (dn ++ [(kk, x)]))
    (Di ++ [(a, Ka)] ++ Dx) /\
  rd_blocks_ok tfibsegs B ly6 S6 W6 mem7 L3 /\ rd_text tfibsegs B ly6 S6 W6 mem7 text len tcap /\
  pobj tfibsegs B ly6 S6 W6 mem7 v.
Proof.
intros ly6 S6 U6 W6 mem6 md6 mem7 v text len tcap k' y' cap' n dn kk x Di a Dx Ka L3 Hn Hncap HARU HB6 HT6 HP6
  Hop6 Hu6 Hc6 Hx6 HND HAP Hv7 HK7 Hw7.
pose proof HARU as (HAR & _ & _). pose proof asan_consts as (C1 & _).
pose proof Hop6 as (_ & _ & Hh6 & (_ & (Hn0 & Hcap54) & _) & _).
destruct (fsw_pobj_low B ly6 S6 W6 _ md6 mem6 v HAR HP6) as (Lv1 & Lv2).
assert (Hh7 : PjStruct.pj_hdr tfibsegs (rdW W6 mem7) v 6 0 0 k' y' (Z.of_nat n + 1) cap').
{ apply (parse_items_shape.pis_hdr_n tfibsegs (rdW W6 mem6) (rdW W6 mem7) v 6 0 0 k' y' (Z.of_nat n) cap'
    (Z.of_nat n + 1) Hh6).
  - lia.
  - refine (proj2 (fsw_val_pj_u64 tfibsegs _ _ _ Hv7 _ _ _)); lia.
  - intros z Hz Hz'. apply pio_mbyte_raw. apply HK7; [lia | exact Hz'].
  - intros z Hz Hw. destruct (Z_lt_le_dec z (v + 40)) as [H1|H1];
      [|destruct (Z_lt_le_dec z (v + 48)) as [H2|H2]].
    + apply (writable_at_eq tfibsegs (rdW W6 mem6) (rdW W6 mem7) z); [apply HK7; lia | exact Hw].
    + exact (Hw7 z ltac:(lia)).
    + apply (writable_at_eq tfibsegs (rdW W6 mem6) (rdW W6 mem7) z); [apply HK7; lia | exact Hw]. }
assert (Hsn : parse_items_shape.pis_open tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) v true 0 k' y' cap' (Z.of_nat n)
  (map snd dn ++ [x]) (map fst dn ++ [kk]) (Di ++ [(a, Ka)] ++ Dx)).
{ apply (parse_items_shape.pis_snoc tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di x kk [(a, Ka)] Dx Hop6).
  - rewrite length_map, Hn. exact Hx6.
  - cbv iota beta. exists a, Ka. split; [reflexivity|]. rewrite length_map, Hn. split; [exact Hu6 | exact Hc6].
  - exact HND.
  - exact HAP. }
assert (Hlen : 0 <= Z.of_nat (length (map snd dn ++ [x])) <= cap')
  by (rewrite length_app, length_map, Hn; cbn [length]; lia).
assert (HL : forall z, parse_items_shape.pis_ifoot true k' y' (Z.of_nat (length (map snd dn ++ [x])))
    (Di ++ [(a, Ka)] ++ Dx) z -> parse_items_shape.pis_same tfibsegs (rdW W6 mem6) (rdW W6 mem7) z).
{ intros z Hz. destruct (pio_ifoot_in k' y' cap' _ _ z Hlen Hz) as ([p k] & Hb & Hh).
  pose proof Hsn as (_ & HAs & _). pose proof (HAs (p, k) z Hb Hh) as Hnv.
  unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
  destruct (pio_rb_geo ly6 S6 W6 _ md6 mem6 p k z HAR (HB6 p k Hb) ltac:(unfold HEAD; lia)) as (G1 & _).
  apply pio_same_raw. apply HK7; lia. }
split; [exact Hh7|]. split.
{ replace (Z.of_nat (length (dn ++ [(kk, x)]))) with (Z.of_nat n + 1)
    by (rewrite length_app, Hn; cbn [length]; lia).
  rewrite !map_app. cbn [map fst snd].
  exact (parse_items_shape.pis_frame tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) (rdW W6 mem7) (ReaderRes.lin L3) v true
    0 k' y' cap' (Z.of_nat n) _ _ _ 0 (Z.of_nat n + 1) Hsn Hh7 ltac:(lia)
    (parse_items_shape.pis_open_lblk tfibsegs _ _ _ _ _ _ _ _ _ _ _ _ Hsn) HL). }
split.
{ intros p k Hpk. apply (pio_rblock_keep ly6 S6 W6 mem6 mem7 p k (HB6 p k Hpk)).
  intros z Hz. pose proof (HB6 p k Hpk) as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly6 S6 W6 _ md6 mem6 p k z HAR (HB6 p k Hpk) ltac:(unfold HEAD in *; lia)) as (G1 & _).
  pose proof (pio_head_off_obj ly6 S6 W6 _ md6 mem6 v p k z HAR HP6 Hin Hk Hz).
  apply HK7; lia. }
split.
{ destruct HT6 as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
  apply (pio_rblock_keep ly6 S6 W6 mem6 mem7 text tcap T2).
  intros z Hz. pose proof T2 as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly6 S6 W6 _ md6 mem6 text tcap z HAR T2 ltac:(unfold HEAD in *; lia)) as (G1 & _).
  pose proof (pio_head_off_obj ly6 S6 W6 _ md6 mem6 v text tcap z HAR HP6 Hin Hk Hz).
  apply HK7; lia. }
apply (pio_pobj_xfer ly6 S6 W6 mem6 mem7 v HP6).
- intros z Hz. destruct (pio_v_geo ly6 S6 W6 _ md6 mem6 v z HAR HP6 Hz) as (G1 & _).
  destruct (pio_shadow_rng z ltac:(lia)) as (R1 & R2).
  apply pio_aview_raw. apply HK7; [lia|]. intros Hs.
  destruct (pio_v_geo ly6 S6 W6 _ md6 mem6 v (shadow_of_addr SHADOW_OFF z) HAR HP6 ltac:(lia)) as (_ & _ & _ & G4).
  exact (G4 R1).
- intros i Hi. pose proof Hh7 as ((_ & (_ & _ & Hst)) & _). destruct (Hst (v + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* ================= (O2) pio_key: parse_string's key block and the walk's store keys[n] := a =================
   c2 = (ly2 S2 U2 W2 mem2) at the parse_string call, c3 = its return (ly3 S3 W3 mem3, heads U2 ++ [(a - HEAD, HEAD)]),
   mem4 after the store keys[n] := a (same W3 / ly3 / S3). Beyond the spec's conclusions it concludes that the key
   block is apart from v (pio_snoc's pis_snoc needs it; it is read off c2, where v is placed and the block is not). *)
Lemma pio_key : forall ly S U ly2 S2 U2 (W2 : world tfibsegs) mem2 md2 ly3 S3 (W3 : world tfibsegs) mem3 md3 mem4
  STKp spP v text len tcap (n : nat) (dn : list (list Z * PjTree.jv)) k' y' cap' Di Da T a (kk : list Z),
  let L := parse_items_shape.pis_slots true k' y' cap' ++ Di in
  let L2 := L ++ [(a, Z.of_nat (length kk) + 1)] in
  length dn = n -> Z.of_nat n < cap' -> cap' <= 2 ^ 54 ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 -> FSupoisonU.fs_heads B ly2 S2 U2 -> FSupoisonU.fs_heads B ly S U ->
  rd_text tfibsegs B ly2 S2 W2 mem2 text len tcap -> In (text - HEAD, tcap + HEAD) (ablocks B ly S) ->
  pobj tfibsegs B ly2 S2 W2 mem2 v ->
  rd_blocks_ok tfibsegs B ly2 S2 W2 mem2 L -> Permutation (ablocks B ly2 S2) (ablocks B ly S ++ rd_hblocks L) ->
  U2 = U ++ rd_heads Da -> Permutation Da L -> rd_sum L = PjGrammar.held T -> (length L <= length T)%nat ->
  PjStruct.pj_hdr tfibsegs (rdW W2 mem2) v 6 0 0 k' y' (Z.of_nat n) cap' ->
  parse_items_shape.pis_open tfibsegs (rdW W2 mem2) (ReaderRes.lin L) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di ->
  (* parse_string's post (FSH_Fn_reader.parse_string_spec, as FSW_parse_items_calls.pic_ps_at hands it over) *)
  ajournal tfibsegs B STKp spP FS_PSTAT_FP ly2 S2 W2 (unpoison U2 mem2) md2 [] ly3 S3 W3
    (unpoison (U2 ++ [(a - HEAD, HEAD)]) mem3) md3 EV_fuzz_malloc ->
  ARU tfibsegs B ly3 S3 (U2 ++ [(a - HEAD, HEAD)]) W3 mem3 md3 ->
  4096 + HEAD <= a -> ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(a - HEAD, Z.of_nat (length kk) + 1 + HEAD)] ->
  fs_rblock tfibsegs B ly3 S3 W3 mem3 a (Z.of_nat (length kk) + 1) ->
  PjStruct.pj_cbytes tfibsegs (rdW W3 mem3) a kk ->
  rd_text tfibsegs B ly3 S3 W3 mem3 text len tcap ->
  PjStruct.pj_hdr tfibsegs (rdW W3 mem3) v 6 0 0 k' y' (Z.of_nat n) cap' ->
  (forall x, v <= x < v + 56 -> mbyte tfibsegs (rdW W3 mem3) x = mbyte tfibsegs (rdW W2 mem2) x) ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  (forall x, k' <= x < k' + 56 * cap' \/ y' <= x < y' + 8 * cap' ->
     mbyte tfibsegs (rdW W3 mem3) x = mbyte tfibsegs (rdW W2 mem2) x) ->
  (* the walk's store keys[n] := a: only the 8 bytes of the slot change below alloc_ceiling *)
  val_mem tfibsegs (rdW W3 mem4) (y' + 8 * Z.of_nat n) 8 a ->
  (forall x, 0 <= x < alloc_ceiling -> ~ (y' + 8 * Z.of_nat n <= x < y' + 8 * Z.of_nat n + 8) ->
     rdW W3 mem4 (Z_to_bv 64 x) = rdW W3 mem3 (Z_to_bv 64 x)) ->
  (forall x, y' + 8 * Z.of_nat n <= x < y' + 8 * Z.of_nat n + 8 -> writable_at tfibsegs (rdW W3 mem4) x) ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem4 L2 /\
  Permutation (ablocks B ly3 S3) (ablocks B ly S ++ rd_hblocks L2) /\
  U2 ++ [(a - HEAD, HEAD)] = U ++ rd_heads (Da ++ [(a, Z.of_nat (length kk) + 1)]) /\
  Permutation (Da ++ [(a, Z.of_nat (length kk) + 1)]) L2 /\
  rd_sum L2 = PjGrammar.held (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) /\
  (length L2 <= length (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]))%nat /\
  FSupoisonU.fs_heads B ly3 S3 (U2 ++ [(a - HEAD, HEAD)]) /\
  rd_text tfibsegs B ly3 S3 W3 mem4 text len tcap /\ pobj tfibsegs B ly3 S3 W3 mem4 v /\
  PjStruct.pj_hdr tfibsegs (rdW W3 mem4) v 6 0 0 k' y' (Z.of_nat n) cap' /\
  parse_items_shape.pis_open tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di /\
  PjStruct.pj_u64 tfibsegs (rdW W3 mem4) (y' + 8 * Z.of_nat n) a /\
  PjStruct.pj_cstr tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) a (Z.of_nat (length kk) + 1) kk /\
  PjStruct.pj_apart [(a, Z.of_nat (length kk) + 1)] v.
Proof.
intros ly S U ly2 S2 U2 W2 mem2 md2 ly3 S3 W3 mem3 md3 mem4 STKp spP v text len tcap n dn k' y' cap' Di Da T a kk L L2
  Hn Hncap Hc54 HARU2 HH2 HH HT2 HTe HP2 HB2 HPm2 HU2 HDa Hsum Hlen Hh2 Hop2 HJ HARU3 Ha16 Hab3 Hrb3 Hcb3 HT3 Hh3 Hv3
  HBK3 HKY3 Hv4 HK4 Hw4.
pose proof asan_consts as (C1 & _). assert (HEADv : HEAD = 16) by reflexivity.
pose proof HARU2 as (HAR2 & _ & _).
pose proof HARU3 as (HAR3 & OK3 & PO3).
assert (Hcap0 : 0 < cap') by lia.
assert (ES : parse_items_shape.pis_slots true k' y' cap' = [(k', 56 * cap'); (y', 8 * cap')]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity. }
assert (HinYs : In (y', 8 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES; right; left; reflexivity).
assert (HinK : In (k', 56 * cap') L) by (unfold L; rewrite ES; apply in_or_app; left; left; reflexivity).
assert (HinY : In (y', 8 * cap') L) by (unfold L; apply in_or_app; left; exact HinYs).
assert (HbL : forall p k, In (p, k) L -> In (p - HEAD, k + HEAD) (ablocks B ly2 S2) /\ 0 < k)
  by (intros p k H; destruct (HB2 p k H) as (Hin & _ & Hk & _); split; [exact Hin | exact Hk]).
destruct (HbL _ _ HinY) as (HinY2 & HkY).
assert (Hinc23 : incl (ablocks B ly2 S2) (ablocks B ly3 S3))
  by (intros b Hb; rewrite Hab3; apply in_or_app; left; exact Hb).
assert (Hnew3 : In (a - HEAD, Z.of_nat (length kk) + 1 + HEAD) (ablocks B ly3 S3))
  by (rewrite Hab3; apply in_or_app; right; left; reflexivity).
assert (Hnew2 : ~ In (a - HEAD, Z.of_nat (length kk) + 1 + HEAD) (ablocks B ly2 S2)).
{ intros Hin. pose proof (pSh_ablocks_nodup B ly3 S3 W3 _ md3 HAR3) as ND. rewrite Hab3 in ND.
  apply (List.NoDup_remove_2 (ablocks B ly2 S2) [] _ ND). rewrite app_nil_r. exact Hin. }
destruct (pio_jr_frames _ _ _ ly2 S2 W2 _ md2 ly3 S3 W3 _ md3 _ HJ HAR2) as (Hfr3 & HFA3).
(* the bytes of the blocks of L are kept by parse_string (its footprint is the image statics) *)
assert (KEEP23 : forall p k z, In (p, k) L -> p - HEAD <= z < p + k ->
  rdW W3 mem3 (Z_to_bv 64 z) = rdW W2 mem2 (Z_to_bv 64 z)).
{ intros p k z Hpk Hz. destruct (HbL p k Hpk) as (Hin & Hk).
  destruct (pio_rb_geo ly2 S2 W2 _ md2 mem2 p k z HAR2 (HB2 p k Hpk) Hz) as (_ & _ & G3 & _).
  refine (proj2 (fsw_journal_kept_byte B STKp spP FS_PSTAT_FP ly2 S2 U2 W2 mem2 md2 ly3 S3 _ W3 mem3 md3
    EV_fuzz_malloc z HJ HARU2 OK3 PO3 _ G3)).
  left. exists (p - HEAD), (k + HEAD). split; [exact Hin|]. rewrite pio_req_hb by exact Hk. unfold HEAD in *. lia. }
(* the slot keys[n] is no byte of another block of L, and no head of a block live at c3 *)
assert (NSL : forall p k z, In (p, k) L -> (p, k) <> (y', 8 * cap') -> p - HEAD <= z < p + k ->
  ~ (y' + 8 * Z.of_nat n <= z < y' + 8 * Z.of_nat n + 8)).
{ intros p k z Hpk Hne Hz Hs. destruct (HbL p k Hpk) as (Hin & Hk).
  exact (pio_rb_disj ly2 S2 W2 _ md2 p k y' (8 * cap') z z HAR2 Hin HinY2 Hk HkY Hne Hz
    ltac:(unfold HEAD; lia) eq_refl). }
assert (NSH : forall p k z, In (p - HEAD, k + HEAD) (ablocks B ly3 S3) -> 0 < k -> p - HEAD <= z < p - HEAD + 8 ->
  ~ (y' + 8 * Z.of_nat n <= z < y' + 8 * Z.of_nat n + 8)).
{ intros p k z Hin Hk Hz Hs.
  exact (pio_head_body ly3 S3 W3 _ md3 p k y' (8 * cap') z z HAR3 Hin (Hinc23 _ HinY2) Hk HkY Hz ltac:(lia) eq_refl). }
destruct (pio_rb_geo ly2 S2 W2 _ md2 mem2 y' (8 * cap') y' HAR2 (HB2 _ _ HinY) ltac:(unfold HEAD; lia)) as (GY0 & _).
destruct (pio_rb_geo ly2 S2 W2 _ md2 mem2 y' (8 * cap') (y' + 8 * cap' - 1) HAR2 (HB2 _ _ HinY)
  ltac:(unfold HEAD; lia)) as (GY1 & _).
destruct (pio_rb_geo ly3 S3 W3 _ md3 mem3 a _ (a + Z.of_nat (length kk)) HAR3 Hrb3 ltac:(unfold HEAD; lia))
  as (GA1 & _).
(* (a) the blocks of L2 *)
assert (RB3 : rd_blocks_ok tfibsegs B ly3 S3 W3 mem3 L2).
{ intros p k Hpk. unfold L2 in Hpk. apply in_app_or in Hpk as [Hpk|[E|[]]].
  - pose proof Hpk as HpkL. unfold L in Hpk. apply in_app_or in Hpk as [Hs|Hd].
    + exact (HBK3 p k Hs).
    + apply (fs_rblock_kept_call B STKp spP FS_PSTAT_FP ly2 S2 U2 W2 mem2 md2 ly3 S3 _ W3 mem3 md3 EV_fuzz_malloc p k
        HJ HARU2 OK3 PO3); [|exact (HB2 p k HpkL)].
      intros z Hz. exact (proj1 (proj2 (proj2 (pio_rb_geo ly2 S2 W2 _ md2 mem2 p k z HAR2 (HB2 p k HpkL) Hz)))).
  - injection E as <- <-. exact Hrb3. }
assert (RB4 : rd_blocks_ok tfibsegs B ly3 S3 W3 mem4 L2).
{ intros p k Hpk. apply (pio_rblock_keep ly3 S3 W3 mem3 mem4 p k (RB3 p k Hpk)).
  intros z Hz. pose proof (RB3 p k Hpk) as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly3 S3 W3 _ md3 mem3 p k z HAR3 (RB3 p k Hpk) ltac:(unfold HEAD in *; lia)) as (G1 & _).
  apply HK4; [lia | exact (NSH p k z Hin Hk Hz)]. }
(* (g) the heads at c3 *)
assert (HH3 : FSupoisonU.fs_heads B ly3 S3 (U2 ++ [(a - HEAD, HEAD)])).
{ intros r Hr. apply in_app_or in Hr as [Hr|[<-|[]]].
  - destruct (HH2 r Hr) as (E16 & mm & Hm & Hr16). split; [exact E16|]. exists mm.
    split; [exact (Hinc23 _ Hm) | exact Hr16].
  - cbn [fst snd]. split; [reflexivity|]. exists (Z.of_nat (length kk) + 1 + HEAD). split; [exact Hnew3|].
    rewrite pio_req_hb by lia. unfold HEAD. lia. }
(* (h) the text *)
assert (HT4 : rd_text tfibsegs B ly3 S3 W3 mem4 text len tcap).
{ destruct HT3 as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
  apply (pio_rblock_keep ly3 S3 W3 mem3 mem4 text tcap T2). intros z Hz. pose proof T2 as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly3 S3 W3 _ md3 mem3 text tcap z HAR3 T2 ltac:(unfold HEAD in *; lia)) as (G1 & _).
  apply HK4; [lia | exact (NSH text tcap z Hin Hk Hz)]. }
(* (i) v: placed at c3 by the journal, its bytes off the slot *)
pose proof Hop2 as (HND2 & HA2 & _).
assert (HP3 : pobj tfibsegs B ly3 S3 W3 mem3 v).
{ apply (pobj_kept_call B STKp spP FS_PSTAT_FP ly2 S2 U2 W2 mem2 md2 ly3 S3 _ W3 mem3 md3 EV_fuzz_malloc v
    HJ HARU2 OK3 PO3).
  - intros z Hz. exact (proj1 (proj2 (proj2 (pio_v_geo ly2 S2 W2 _ md2 mem2 v z HAR2 HP2 Hz)))).
  - exact pio_pstat_off_shadow.
  - exact HH3.
  - exact HP2. }
assert (VNS : forall z, v <= z < v + 56 -> ~ (y' + 8 * Z.of_nat n <= z < y' + 8 * Z.of_nat n + 8)).
{ intros z Hz Hs. apply (HA2 (y', 8 * cap') z HinY); [unfold PjStruct.pj_holds; cbn [fst snd]; lia | exact Hz]. }
assert (V34 : forall z, v <= z < v + 56 -> rdW W3 mem4 (Z_to_bv 64 z) = rdW W3 mem3 (Z_to_bv 64 z)).
{ intros z Hz. destruct (pio_v_geo ly2 S2 W2 _ md2 mem2 v z HAR2 HP2 Hz) as (G1 & _).
  apply HK4; [lia | exact (VNS z Hz)]. }
assert (HP4 : pobj tfibsegs B ly3 S3 W3 mem4 v).
{ apply (pio_pobj_xfer ly3 S3 W3 mem3 mem4 v HP3).
  - intros z Hz. destruct (pio_v_geo ly2 S2 W2 _ md2 mem2 v z HAR2 HP2 Hz) as (G1 & _).
    destruct (pio_shadow_rng z ltac:(lia)) as (R1 & R2).
    apply pio_aview_raw. apply HK4; [lia|]. intros Hs.
    destruct (pio_rb_geo ly2 S2 W2 _ md2 mem2 y' (8 * cap') (shadow_of_addr SHADOW_OFF z) HAR2 (HB2 _ _ HinY)
      ltac:(unfold HEAD; lia)) as (_ & _ & _ & G4).
    exact (G4 R1).
  - intros i Hi. pose proof HP3 as (_ & Hw3).
    apply (writable_at_eq tfibsegs (rdW W3 mem3) (rdW W3 mem4) (v + i)); [exact (V34 (v + i) ltac:(lia)) | exact (Hw3 i Hi)]. }
(* (j) v's header *)
assert (Hh4 : PjStruct.pj_hdr tfibsegs (rdW W3 mem4) v 6 0 0 k' y' (Z.of_nat n) cap').
{ apply (parse_items_shape.pis_hdr_frame tfibsegs (rdW W3 mem3) (rdW W3 mem4) v 6 0 0 k' y' (Z.of_nat n) cap' Hh3).
  intros z Hz. apply pio_same_raw. exact (V34 z Hz). }
(* (k) the open object over L2 *)
assert (Hop4 : parse_items_shape.pis_open tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
  (map snd dn) (map fst dn) Di).
{ apply (parse_items_shape.pis_frame tfibsegs (rdW W2 mem2) (ReaderRes.lin L) (rdW W3 mem4) (ReaderRes.lin L2) v true
    0 k' y' cap' (Z.of_nat n) _ _ _ 0 (Z.of_nat n) Hop2 Hh4 ltac:(lia)).
  - intros p k Hpk. unfold ReaderRes.lin, L2. apply in_or_app. left. exact Hpk.
  - intros z Hz. rewrite length_map, Hn in Hz.
    assert (NS : ~ (y' + 8 * Z.of_nat n <= z < y' + 8 * Z.of_nat n + 8)).
    { destruct Hz as [Hz|[(_ & Hz)|(b & Hb & Hz)]].
      - apply (NSL k' (56 * cap') z HinK); [intros E; injection E as _ E; lia | unfold HEAD; lia].
      - lia.
      - destruct b as [p k]. assert (HbL' : In (p, k) L) by (unfold L; apply in_or_app; right; exact Hb).
        apply (NSL p k z HbL').
        + intros E. rewrite E in Hb. exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HND2 HinYs Hb).
        + unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz. unfold HEAD; lia. }
    destruct (pio_ifoot_in k' y' cap' (Z.of_nat n) Di z ltac:(lia) Hz) as ([p k] & Hb & Hh).
    unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    destruct (pio_rb_geo ly2 S2 W2 _ md2 mem2 p k z HAR2 (HB2 p k Hb) ltac:(unfold HEAD; lia)) as (G1 & _).
    apply pio_same_raw. rewrite (HK4 z ltac:(lia) NS). exact (KEEP23 p k z Hb ltac:(unfold HEAD; lia)). }
(* (l) the slot, (m) the key *)
assert (Hu4 : PjStruct.pj_u64 tfibsegs (rdW W3 mem4) (y' + 8 * Z.of_nat n) a)
  by (apply (fsw_val_pj_u64 tfibsegs _ _ _ Hv4); lia).
assert (HKB : forall z, a <= z < a + Z.of_nat (length kk) + 1 ->
  rdW W3 mem4 (Z_to_bv 64 z) = rdW W3 mem3 (Z_to_bv 64 z)).
{ intros z Hz. apply HK4; [lia|]. intros Hs.
  apply (pio_rb_disj ly3 S3 W3 _ md3 a (Z.of_nat (length kk) + 1) y' (8 * cap') z z HAR3 Hnew3 (Hinc23 _ HinY2)
    ltac:(lia) HkY).
  - intros E. injection E as Ea Ek. apply Hnew2. rewrite Ea, Ek. exact HinY2.
  - unfold HEAD; lia.
  - unfold HEAD; lia.
  - reflexivity. }
assert (Hc4 : PjStruct.pj_cstr tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) a (Z.of_nat (length kk) + 1) kk).
{ split; [unfold ReaderRes.lin, L2; apply in_or_app; right; left; reflexivity|]. split; [lia|].
  destruct Hcb3 as (Hf & Hb). split; [exact Hf|].
  apply (parse_items_shape.pis_bytes_mv tfibsegs (rdW W3 mem3) (rdW W3 mem4) a a _ Hb).
  - lia.
  - rewrite length_map, length_app. cbn [length]. lia.
  - intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi. apply pio_mbyte_raw. apply HKB. lia. }
(* (n) the key block is apart from v *)
assert (HAPk : PjStruct.pj_apart [(a, Z.of_nat (length kk) + 1)] v).
{ intros b z [<-|[]] Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
  apply (pio_new_apart ly2 S2 W2 mem2 v ly3 S3 W3 _ md3 _ _ HAR3 HP2 Hfr3 HFA3 (fun b mm Hb _ _ => Hinc23 _ Hb) Hnew3
    Hnew2).
  rewrite pio_req_hb by lia. unfold HEAD. lia. }
split; [exact RB4|].
split.
{ unfold L2. rewrite Hab3, pim_rd_hblocks_app, app_assoc.
  change (rd_hblocks [(a, Z.of_nat (length kk) + 1)]) with [(a - HEAD, Z.of_nat (length kk) + 1 + HEAD)].
  apply Permutation_app_tail. exact HPm2. }
split; [rewrite HU2, pim_rd_heads_app, app_assoc; reflexivity|].
split; [unfold L2; apply Permutation_app_tail; exact HDa|].
split.
{ unfold L2. rewrite pim_rd_sum_app, PjGrammar.held_app, Hsum. unfold rd_sum. cbn [fold_right fst snd PjGrammar.held].
  unfold PjGrammar.held_ev. lia. }
split; [unfold L2; rewrite !length_app; cbn [length]; lia|].
split; [exact HH3|]. split; [exact HT4|]. split; [exact HP4|]. split; [exact Hh4|]. split; [exact Hop4|].
split; [exact Hu4|]. split; [exact Hc4 | exact HAPk].
Qed.

(* ================= (O3) pio_zero: __asan_memset of the kid vk = k' + 56 n =================
   Same world / layout / state (W3 ly3 S3); FSW_parse_items_calls.pic_ms_at's continuation hands over the memset's
   frame (the view kept off the kid and off the stack window [spC - ESTACK, spC)) and ARU at mem5. Every object byte
   is below alloc_ceiling <= spC - ESTACK, so the stack window is irrelevant. pio_key's conclusions at mem4 hold at
   mem5; its heads / ablocks / U facts are memory-free and carry over unchanged. *)
Lemma pio_zero : forall ly S ly3 S3 U3 (W3 : world tfibsegs) mem4 mem5 md5 spC v text len tcap (n : nat)
  (dn : list (list Z * PjTree.jv)) k' y' cap' Di a (kk : list Z),
  let L2 := (parse_items_shape.pis_slots true k' y' cap' ++ Di) ++ [(a, Z.of_nat (length kk) + 1)] in
  let vk := k' + 56 * Z.of_nat n in
  length dn = n -> Z.of_nat n < cap' -> alloc_ceiling <= spC - ESTACK ->
  ARU tfibsegs B ly3 S3 U3 W3 mem5 md5 ->
  (* pio_key's conclusions at mem4 *)
  Permutation (ablocks B ly3 S3) (ablocks B ly S ++ rd_hblocks L2) ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem4 L2 -> rd_text tfibsegs B ly3 S3 W3 mem4 text len tcap ->
  pobj tfibsegs B ly3 S3 W3 mem4 v ->
  PjStruct.pj_hdr tfibsegs (rdW W3 mem4) v 6 0 0 k' y' (Z.of_nat n) cap' ->
  parse_items_shape.pis_open tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di ->
  PjStruct.pj_u64 tfibsegs (rdW W3 mem4) (y' + 8 * Z.of_nat n) a ->
  PjStruct.pj_cstr tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) a (Z.of_nat (length kk) + 1) kk ->
  (* the memset's frame (pic_ms_at's continuation) *)
  (forall x, 0 <= x < 2 ^ 64 -> ~ (vk <= x < vk + 56) -> ~ (spC - ESTACK <= x < spC) ->
     aview tfibsegs (w_H W3) mem5 x = aview tfibsegs (w_H W3) mem4 x) ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem5 L2 /\ rd_text tfibsegs B ly3 S3 W3 mem5 text len tcap /\
  pobj tfibsegs B ly3 S3 W3 mem5 v /\ PjStruct.pj_hdr tfibsegs (rdW W3 mem5) v 6 0 0 k' y' (Z.of_nat n) cap' /\
  parse_items_shape.pis_open tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di /\
  PjStruct.pj_u64 tfibsegs (rdW W3 mem5) (y' + 8 * Z.of_nat n) a /\
  PjStruct.pj_cstr tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) a (Z.of_nat (length kk) + 1) kk.
Proof.
intros ly S ly3 S3 U3 W3 mem4 mem5 md5 spC v text len tcap n dn k' y' cap' Di a kk L2 vk Hn Hncap Hsp HARU HPm
  HB4 HT4 HP4 Hh4 Hop4 Hu4 Hc4 HMS.
pose proof asan_consts as (C1 & _). assert (HEADv : HEAD = 16) by reflexivity.
pose proof HARU as (HAR & _ & _).
assert (Hcap0 : 0 < cap') by lia.
assert (ES : parse_items_shape.pis_slots true k' y' cap' = [(k', 56 * cap'); (y', 8 * cap')]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity. }
assert (HinKs : In (k', 56 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES; left; reflexivity).
assert (HinYs : In (y', 8 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES; right; left; reflexivity).
assert (HinK : In (k', 56 * cap') L2) by (unfold L2; apply in_or_app; left; apply in_or_app; left; exact HinKs).
assert (HinY : In (y', 8 * cap') L2) by (unfold L2; apply in_or_app; left; apply in_or_app; left; exact HinYs).
assert (HinA : In (a, Z.of_nat (length kk) + 1) L2) by (unfold L2; apply in_or_app; right; left; reflexivity).
pose proof (HB4 _ _ HinK) as (HinK3 & _ & HkK & _).
assert (HND : NoDup L2) by exact (pio_nodup_L ly3 S3 W3 _ md5 _ L2 HAR HPm).
assert (HAk : (a, Z.of_nat (length kk) + 1) <> (k', 56 * cap')).
{ intros E. unfold L2 in HND. rewrite E in HND.
  exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HND (in_or_app _ _ _ (or_introl HinKs)) (or_introl eq_refl)). }
(* the kid is no byte of another block of L2, nor of a live block's head *)
assert (KV : forall p k z, In (p, k) L2 -> (p, k) <> (k', 56 * cap') -> p - HEAD <= z < p + k ->
  ~ (vk <= z < vk + 56)).
{ intros p k z Hpk Hne Hz Hv. pose proof (HB4 p k Hpk) as (Hin & _ & Hk & _).
  exact (pio_rb_disj ly3 S3 W3 _ md5 p k k' (56 * cap') z z HAR Hin HinK3 Hk HkK Hne Hz
    ltac:(unfold vk in Hv; lia) eq_refl). }
assert (KH : forall p k z, In (p - HEAD, k + HEAD) (ablocks B ly3 S3) -> 0 < k -> p - HEAD <= z < p - HEAD + 8 ->
  ~ (vk <= z < vk + 56)).
{ intros p k z Hin Hk Hz Hv.
  exact (pio_head_body ly3 S3 W3 _ md5 p k k' (56 * cap') z z HAR Hin HinK3 Hk HkK Hz
    ltac:(unfold vk in Hv; lia) eq_refl). }
assert (K45 : forall z, 4096 <= z < alloc_ceiling -> ~ in_img tfibsegs z -> ~ (vk <= z < vk + 56) ->
  rdW W3 mem5 (Z_to_bv 64 z) = rdW W3 mem4 (Z_to_bv 64 z)).
{ intros z Hz Hi Hv. apply (fsw_restrict_of_aview (w_H W3) (w_H W3) mem4 mem5 z ltac:(lia) Hi).
  apply HMS; [lia | exact Hv | lia]. }
assert (RB5 : rd_blocks_ok tfibsegs B ly3 S3 W3 mem5 L2).
{ intros p k Hpk. apply (pio_rblock_keep ly3 S3 W3 mem4 mem5 p k (HB4 p k Hpk)).
  intros z Hz. pose proof (HB4 p k Hpk) as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 p k z HAR (HB4 p k Hpk) ltac:(lia)) as (G1 & G2 & _).
  exact (K45 z G1 G2 (KH p k z Hin Hk Hz)). }
assert (HT5 : rd_text tfibsegs B ly3 S3 W3 mem5 text len tcap).
{ destruct HT4 as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
  apply (pio_rblock_keep ly3 S3 W3 mem4 mem5 text tcap T2). intros z Hz. pose proof T2 as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 text tcap z HAR T2 ltac:(lia)) as (G1 & G2 & _).
  exact (K45 z G1 G2 (KH text tcap z Hin Hk Hz)). }
pose proof Hop4 as (HND4 & HA4 & _).
assert (VK : forall z, v <= z < v + 56 -> ~ (vk <= z < vk + 56)).
{ intros z Hz Hv. apply (HA4 (k', 56 * cap') z (in_or_app _ _ _ (or_introl HinKs))); [|exact Hz].
  unfold PjStruct.pj_holds. cbn [fst snd]. unfold vk in Hv. lia. }
assert (V45 : forall z, v <= z < v + 56 -> rdW W3 mem5 (Z_to_bv 64 z) = rdW W3 mem4 (Z_to_bv 64 z)).
{ intros z Hz. destruct (pio_v_geo ly3 S3 W3 _ md5 mem4 v z HAR HP4 Hz) as (G1 & G2 & _). exact (K45 z G1 G2 (VK z Hz)). }
assert (HP5 : pobj tfibsegs B ly3 S3 W3 mem5 v).
{ apply (pio_pobj_xfer ly3 S3 W3 mem4 mem5 v HP4).
  - intros z Hz. destruct (pio_v_geo ly3 S3 W3 _ md5 mem4 v z HAR HP4 Hz) as (G1 & _).
    destruct (pio_shadow_rng z ltac:(lia)) as (R1 & R2).
    apply HMS; [lia | | lia]. intros Hv.
    destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 k' (56 * cap') (shadow_of_addr SHADOW_OFF z) HAR (HB4 _ _ HinK)
      ltac:(unfold vk in Hv; lia)) as (_ & _ & _ & G4).
    exact (G4 R1).
  - intros i Hi. pose proof HP4 as (_ & Hw4).
    apply (writable_at_eq tfibsegs (rdW W3 mem4) (rdW W3 mem5) (v + i)); [exact (V45 (v + i) ltac:(lia)) | exact (Hw4 i Hi)]. }
assert (Hh5 : PjStruct.pj_hdr tfibsegs (rdW W3 mem5) v 6 0 0 k' y' (Z.of_nat n) cap').
{ apply (parse_items_shape.pis_hdr_frame tfibsegs (rdW W3 mem4) (rdW W3 mem5) v 6 0 0 k' y' (Z.of_nat n) cap' Hh4).
  intros z Hz. apply pio_same_raw. exact (V45 z Hz). }
assert (Hop5 : parse_items_shape.pis_open tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
  (map snd dn) (map fst dn) Di).
{ apply (parse_items_shape.pis_frame tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) (rdW W3 mem5) (ReaderRes.lin L2) v true
    0 k' y' cap' (Z.of_nat n) _ _ _ 0 (Z.of_nat n) Hop4 Hh5 ltac:(lia)
    (parse_items_shape.pis_open_lblk tfibsegs _ _ _ _ _ _ _ _ _ _ _ _ Hop4)).
  intros z Hz. rewrite length_map, Hn in Hz.
  assert (NV : ~ (vk <= z < vk + 56)).
  { destruct Hz as [Hz|[(_ & Hz)|(b & Hb & Hz)]].
    - unfold vk. lia.
    - apply (KV y' (8 * cap') z HinY); [intros E; injection E as _ E; lia | lia].
    - destruct b as [p k].
      assert (HbL : In (p, k) L2) by (unfold L2; apply in_or_app; left; apply in_or_app; right; exact Hb).
      apply (KV p k z HbL).
      + intros E. rewrite E in Hb. exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HND4 HinKs Hb).
      + unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz. lia. }
  destruct (pio_ifoot_in k' y' cap' (Z.of_nat n) Di z ltac:(lia) Hz) as ([p k] & Hb & Hh).
  unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
  assert (HbL : In (p, k) L2) by (unfold L2; apply in_or_app; left; exact Hb).
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 p k z HAR (HB4 p k HbL) ltac:(lia)) as (G1 & G2 & _).
  apply pio_same_raw. exact (K45 z G1 G2 NV). }
assert (Hu5 : PjStruct.pj_u64 tfibsegs (rdW W3 mem5) (y' + 8 * Z.of_nat n) a).
{ apply (parse_items_shape.pis_u64_frame tfibsegs (rdW W3 mem4) (rdW W3 mem5) _ a Hu4).
  intros z Hz. apply pio_mbyte_raw.
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 y' (8 * cap') z HAR (HB4 _ _ HinY) ltac:(lia)) as (G1 & G2 & _).
  apply (K45 z G1 G2). apply (KV y' (8 * cap') z HinY); [intros E; injection E as _ E; lia | lia]. }
assert (Hc5 : PjStruct.pj_cstr tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) a (Z.of_nat (length kk) + 1) kk).
{ apply (parse_items_shape.pis_cstr_frame tfibsegs (rdW W3 mem4) (ReaderRes.lin L2) (rdW W3 mem5) (ReaderRes.lin L2)
    a _ kk Hc4 HinA).
  intros z Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz. apply pio_mbyte_raw.
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem4 a _ z HAR (HB4 _ _ HinA) ltac:(lia)) as (G1 & G2 & _).
  apply (K45 z G1 G2). apply (KV a _ z HinA HAk). lia. }
split; [exact RB5|]. split; [exact HT5|]. split; [exact HP5|]. split; [exact Hh5|]. split; [exact Hop5|].
split; [exact Hu5 | exact Hc5].
Qed.

(* ================= (O4) pio_value: parse_value's blocks Dx join L, the kid vk is a node of x =================
   c3 after the memset (mem5, heads U3 = U ++ rd_heads Da2) to c6 = parse_value's return (ly6 S6 W6 mem6, heads
   U3 ++ rd_heads Dax, Permutation Dax Dx), as FSW_parse_items_calls.pic_pv_at's continuation hands it over. Beyond the
   spec's conclusions it concludes that the new blocks are apart from v (pio_snoc's pis_snoc needs it). *)
Lemma pio_value : forall ly S U ly3 S3 U3 (W3 : world tfibsegs) mem5 md5 ly6 S6 (W6 : world tfibsegs) mem6 md6
  STKv spV kv v text len tcap (n : nat) (dn : list (list Z * PjTree.jv)) k' y' cap' Di Da2 T2 a (kk : list Z)
  (x : PjTree.jv) Dx Dax,
  let Ka := Z.of_nat (length kk) + 1 in
  let L2 := (parse_items_shape.pis_slots true k' y' cap' ++ Di) ++ [(a, Ka)] in
  let L3 := L2 ++ Dx in
  let vk := k' + 56 * Z.of_nat n in
  length dn = n -> Z.of_nat n < cap' ->
  (* at c3 after the memset (mem5): pio_key's bookkeeping and pio_zero's object facts *)
  ARU tfibsegs B ly3 S3 U3 W3 mem5 md5 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly S ++ rd_hblocks L2) ->
  U3 = U ++ rd_heads Da2 -> Permutation Da2 L2 -> rd_sum L2 = PjGrammar.held T2 -> (length L2 <= length T2)%nat ->
  FSupoisonU.fs_heads B ly3 S3 U3 ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 mem5 L2 -> pobj tfibsegs B ly3 S3 W3 mem5 v ->
  parse_items_shape.pis_open tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di ->
  PjStruct.pj_u64 tfibsegs (rdW W3 mem5) (y' + 8 * Z.of_nat n) a ->
  PjStruct.pj_cstr tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) a Ka kk ->
  PjStruct.pj_apart [(a, Ka)] v ->
  (* parse_value's post at c6 *)
  Permutation Dax Dx ->
  ajournal tfibsegs B STKv spV ([(vk, vk + 56)] ++ FS_PSTAT_FP) ly3 S3 W3 (unpoison U3 mem5) md5 []
    ly6 S6 W6 (unpoison (U3 ++ rd_heads Dax) mem6) md6 kv ->
  ARU tfibsegs B ly6 S6 (U3 ++ rd_heads Dax) W6 mem6 md6 ->
  Permutation (ablocks B ly6 S6) (ablocks B ly3 S3 ++ rd_hblocks Dx) ->
  rtree tfibsegs B ly6 S6 W6 mem6 vk x Dx -> rd_sum Dx = PjGrammar.held (PjRoundTrip.ttrace x) ->
  (length Dx <= length (PjRoundTrip.ttrace x))%nat ->
  rd_text tfibsegs B ly6 S6 W6 mem6 text len tcap ->
  PjStruct.pj_hdr tfibsegs (rdW W6 mem6) v 6 0 0 k' y' (Z.of_nat n) cap' ->
  (forall z, v <= z < v + 56 -> mbyte tfibsegs (rdW W6 mem6) z = mbyte tfibsegs (rdW W3 mem5) z) ->
  rd_blocks_ok tfibsegs B ly6 S6 W6 mem6 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  (forall z, k' <= z < k' + 56 * cap' \/ y' <= z < y' + 8 * cap' -> ~ (vk <= z < vk + 56) ->
     mbyte tfibsegs (rdW W6 mem6) z = mbyte tfibsegs (rdW W3 mem5) z) ->
  rd_blocks_ok tfibsegs B ly6 S6 W6 mem6 L3 /\
  Permutation (ablocks B ly6 S6) (ablocks B ly S ++ rd_hblocks L3) /\
  U3 ++ rd_heads Dax = U ++ rd_heads (Da2 ++ Dax) /\ Permutation (Da2 ++ Dax) L3 /\
  rd_sum L3 = PjGrammar.held (T2 ++ PjRoundTrip.ttrace x) /\
  (length L3 <= length (T2 ++ PjRoundTrip.ttrace x))%nat /\
  FSupoisonU.fs_heads B ly6 S6 (U3 ++ rd_heads Dax) /\
  rd_text tfibsegs B ly6 S6 W6 mem6 text len tcap /\ pobj tfibsegs B ly6 S6 W6 mem6 v /\
  PjStruct.pj_hdr tfibsegs (rdW W6 mem6) v 6 0 0 k' y' (Z.of_nat n) cap' /\
  parse_items_shape.pis_open tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) v true 0 k' y' cap' (Z.of_nat n)
    (map snd dn) (map fst dn) Di /\
  PjStruct.pj_u64 tfibsegs (rdW W6 mem6) (y' + 8 * Z.of_nat n) a /\
  PjStruct.pj_cstr tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) a Ka kk /\
  PjStruct.pj_node tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) vk x Dx /\ NoDup L3 /\
  PjStruct.pj_apart ([(a, Ka)] ++ Dx) v.
Proof.
intros ly S U ly3 S3 U3 W3 mem5 md5 ly6 S6 W6 mem6 md6 STKv spV kv v text len tcap n dn k' y' cap' Di Da2 T2 a kk x
  Dx Dax Ka L2 L3 vk Hn Hncap HARU3 HPm3 HU3 HDa2 Hsum2 Hlen2 HH3 HB5 HP5 Hop5 Hu5 Hc5 HAPk HDax HJ HARU6 HPx HTx
  Hsumx Hlenx HT6 Hh6 Hv6 HBk6 HKY6.
pose proof asan_consts as (C1 & _). assert (HEADv : HEAD = 16) by reflexivity.
pose proof HARU3 as (HAR3 & _ & _).
pose proof HARU6 as (HAR6 & OK6 & PO6).
assert (Hcap0 : 0 < cap') by lia.
assert (ES : parse_items_shape.pis_slots true k' y' cap' = [(k', 56 * cap'); (y', 8 * cap')]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity. }
assert (HinKs : In (k', 56 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES; left; reflexivity).
assert (HinYs : In (y', 8 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES; right; left; reflexivity).
assert (HinK : In (k', 56 * cap') L2) by (unfold L2; apply in_or_app; left; apply in_or_app; left; exact HinKs).
assert (HinY : In (y', 8 * cap') L2) by (unfold L2; apply in_or_app; left; apply in_or_app; left; exact HinYs).
assert (HinA : In (a, Ka) L2) by (unfold L2; apply in_or_app; right; left; reflexivity).
pose proof (HB5 _ _ HinK) as (HinK3 & _ & HkK & _).
assert (HND2 : NoDup L2) by exact (pio_nodup_L ly3 S3 W3 _ md5 _ L2 HAR3 HPm3).
assert (HAk : (a, Ka) <> (k', 56 * cap')).
{ intros E. unfold L2 in HND2. rewrite E in HND2.
  exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HND2 (in_or_app _ _ _ (or_introl HinKs)) (or_introl eq_refl)). }
assert (KV : forall p k z, In (p, k) L2 -> (p, k) <> (k', 56 * cap') -> p - HEAD <= z < p + k ->
  ~ (vk <= z < vk + 56)).
{ intros p k z Hpk Hne Hz Hv. pose proof (HB5 p k Hpk) as (Hin & _ & Hk & _).
  exact (pio_rb_disj ly3 S3 W3 _ md5 p k k' (56 * cap') z z HAR3 Hin HinK3 Hk HkK Hne Hz
    ltac:(unfold vk in Hv; lia) eq_refl). }
assert (Hinc36 : incl (ablocks B ly3 S3) (ablocks B ly6 S6)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPx)). apply in_or_app. left. exact Hb. }
destruct (pio_jr_frames _ _ _ ly3 S3 W3 _ md5 ly6 S6 W6 _ md6 _ HJ HAR3) as (Hfr6 & HFA6).
(* parse_value's journal keeps the bytes of the blocks of L2 off the kid *)
assert (KEEP56 : forall p k z, In (p, k) L2 -> p - HEAD <= z < p + k -> ~ (vk <= z < vk + 56) ->
  rdW W6 mem6 (Z_to_bv 64 z) = rdW W3 mem5 (Z_to_bv 64 z)).
{ intros p k z Hpk Hz Hv. pose proof (HB5 p k Hpk) as (Hin & _ & Hk & _).
  destruct (pio_rb_geo ly3 S3 W3 _ md5 mem5 p k z HAR3 (HB5 p k Hpk) Hz) as (_ & _ & G3 & _).
  refine (proj2 (fsw_journal_kept_byte B STKv spV _ ly3 S3 U3 W3 mem5 md5 ly6 S6 _ W6 mem6 md6 kv z HJ HARU3 OK6 PO6 _
    (pio_inFP_kid vk z Hv G3))).
  left. exists (p - HEAD), (k + HEAD). split; [exact Hin|]. rewrite pio_req_hb by exact Hk. lia. }
pose proof HTx as (HNx & HBx & _).
(* the blocks of L3 *)
assert (RB6 : rd_blocks_ok tfibsegs B ly6 S6 W6 mem6 L3).
{ intros p k Hpk. unfold L3 in Hpk. apply in_app_or in Hpk as [Hpk|Hpk]; [|exact (HBx p k Hpk)].
  destruct (pSh_zz_dec (p, k) (k', 56 * cap')) as [E|NE].
  - injection E as -> ->. exact (HBk6 _ _ HinKs).
  - apply (fs_rblock_kept_call B STKv spV _ ly3 S3 U3 W3 mem5 md5 ly6 S6 _ W6 mem6 md6 kv p k HJ HARU3 OK6 PO6);
      [|exact (HB5 p k Hpk)].
    intros z Hz. apply pio_inFP_kid; [exact (KV p k z Hpk NE Hz)|].
    exact (proj1 (proj2 (proj2 (pio_rb_geo ly3 S3 W3 _ md5 mem5 p k z HAR3 (HB5 p k Hpk) Hz)))). }
assert (HPm6 : Permutation (ablocks B ly6 S6) (ablocks B ly S ++ rd_hblocks L3)).
{ unfold L3. rewrite pim_rd_hblocks_app, app_assoc.
  apply (Permutation_trans HPx). apply Permutation_app_tail. exact HPm3. }
assert (HH6 : FSupoisonU.fs_heads B ly6 S6 (U3 ++ rd_heads Dax)).
{ intros r Hr. apply in_app_or in Hr as [Hr|Hr].
  - destruct (HH3 r Hr) as (E16 & mm & Hm & Hr16). split; [exact E16|]. exists mm.
    split; [exact (Hinc36 _ Hm) | exact Hr16].
  - unfold rd_heads in Hr. apply in_map_iff in Hr as ([p k] & <- & Hpk). cbn [fst snd].
    apply (Permutation_in _ HDax) in Hpk. destruct (HBx p k Hpk) as (Hin & _ & Hk & _).
    split; [reflexivity|]. exists (k + HEAD). split; [exact Hin|]. rewrite pio_req_hb by exact Hk. lia. }
(* v *)
pose proof Hop5 as (HND5 & HA5 & _).
assert (VK : forall z, v <= z < v + 56 -> ~ (vk <= z < vk + 56)).
{ intros z Hz Hv. apply (HA5 (k', 56 * cap') z (in_or_app _ _ _ (or_introl HinKs))); [|exact Hz].
  unfold PjStruct.pj_holds. cbn [fst snd]. unfold vk in Hv. lia. }
assert (HP6 : pobj tfibsegs B ly6 S6 W6 mem6 v).
{ apply (pobj_kept_call B STKv spV _ ly3 S3 U3 W3 mem5 md5 ly6 S6 _ W6 mem6 md6 kv v HJ HARU3 OK6 PO6).
  - intros z Hz. apply pio_inFP_kid; [exact (VK z Hz)|].
    exact (proj1 (proj2 (proj2 (pio_v_geo ly3 S3 W3 _ md5 mem5 v z HAR3 HP5 Hz)))).
  - intros z (r & Hr & Hz). apply in_app_or in Hr as [[<-|[]]|Hr].
    + cbn [fst snd] in Hz.
      exact (proj2 (proj2 (proj2 (pio_rb_geo ly3 S3 W3 _ md5 mem5 k' (56 * cap') z HAR3 (HB5 _ _ HinK)
        ltac:(unfold vk in Hz; lia))))).
    + apply pio_pstat_off_shadow. exists r. split; [exact Hr | exact Hz].
  - exact HH6.
  - exact HP5. }
(* the open object over L3 *)
assert (Hop6 : parse_items_shape.pis_open tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) v true 0 k' y' cap' (Z.of_nat n)
  (map snd dn) (map fst dn) Di).
{ apply (parse_items_shape.pis_frame tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) (rdW W6 mem6) (ReaderRes.lin L3) v true
    0 k' y' cap' (Z.of_nat n) _ _ _ 0 (Z.of_nat n) Hop5 Hh6 ltac:(lia)).
  - intros p k Hpk. unfold ReaderRes.lin, L3, L2. apply in_or_app. left. apply in_or_app. left. exact Hpk.
  - intros z Hz. rewrite length_map, Hn in Hz.
    assert (NV : ~ (vk <= z < vk + 56)).
    { destruct Hz as [Hz|[(_ & Hz)|(b & Hb & Hz)]].
      - unfold vk. lia.
      - apply (KV y' (8 * cap') z HinY); [intros E; injection E as _ E; lia | lia].
      - destruct b as [p k].
        assert (HbL : In (p, k) L2) by (unfold L2; apply in_or_app; left; apply in_or_app; right; exact Hb).
        apply (KV p k z HbL).
        + intros E. rewrite E in Hb. exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HND5 HinKs Hb).
        + unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz. lia. }
    destruct (pio_ifoot_in k' y' cap' (Z.of_nat n) Di z ltac:(lia) Hz) as ([p k] & Hb & Hh).
    unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    assert (HbL : In (p, k) L2) by (unfold L2; apply in_or_app; left; exact Hb).
    apply pio_same_raw. exact (KEEP56 p k z HbL ltac:(lia) NV). }
assert (Hu6 : PjStruct.pj_u64 tfibsegs (rdW W6 mem6) (y' + 8 * Z.of_nat n) a).
{ apply (parse_items_shape.pis_u64_frame tfibsegs (rdW W3 mem5) (rdW W6 mem6) _ a Hu5).
  intros z Hz. apply pio_mbyte_raw. apply (KEEP56 y' (8 * cap') z HinY); [lia|].
  apply (KV y' (8 * cap') z HinY); [intros E; injection E as _ E; lia | lia]. }
assert (Hc6 : PjStruct.pj_cstr tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) a Ka kk).
{ apply (parse_items_shape.pis_cstr_frame tfibsegs (rdW W3 mem5) (ReaderRes.lin L2) (rdW W6 mem6) (ReaderRes.lin L3)
    a _ kk Hc5).
  - unfold ReaderRes.lin, L3. apply in_or_app. left. exact HinA.
  - intros z Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz. apply pio_mbyte_raw.
    apply (KEEP56 a Ka z HinA); [lia|]. apply (KV a Ka z HinA HAk). lia. }
assert (Hnode : PjStruct.pj_node tfibsegs (rdW W6 mem6) (ReaderRes.lin L3) vk x Dx).
{ apply (parse_items_shape.pis_node_frame tfibsegs x (rdW W6 mem6) (fun a0 k0 => In (a0, k0) Dx) (rdW W6 mem6)
    (ReaderRes.lin L3) vk Dx HNx).
  - intros p k Hpk. unfold ReaderRes.lin, L3. apply in_or_app. right. exact Hpk.
  - intros z _. split; [reflexivity | intros Hw; exact Hw]. }
assert (HND3 : NoDup L3) by exact (pio_nodup_L ly6 S6 W6 _ md6 _ L3 HAR6 HPm6).
assert (HAP6 : PjStruct.pj_apart ([(a, Ka)] ++ Dx) v).
{ apply PjStruct.pj_apart_app; [exact HAPk|].
  intros [p k] z Hpk Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
  destruct (HBx p k Hpk) as (Hin & _ & Hk & _).
  apply (pio_new_apart ly3 S3 W3 mem5 v ly6 S6 W6 _ md6 _ _ HAR6 HP5 Hfr6 HFA6 (fun b mm Hb _ _ => Hinc36 _ Hb) Hin
    (pio_perm_fresh ly6 S6 W6 _ md6 _ Dx p k HAR6 HPx Hpk)).
  rewrite pio_req_hb by exact Hk. lia. }
split; [exact RB6|]. split; [exact HPm6|].
split; [rewrite HU3, pim_rd_heads_app, app_assoc; reflexivity|].
split; [unfold L3; exact (Permutation_app HDa2 HDax)|].
split; [unfold L3; rewrite pim_rd_sum_app, PjGrammar.held_app, Hsum2, Hsumx; reflexivity|].
split; [unfold L3; rewrite !length_app; lia|].
split; [exact HH6|]. split; [exact HT6|]. split; [exact HP6|]. split; [exact Hh6|]. split; [exact Hop6|].
split; [exact Hu6|]. split; [exact Hc6|]. split; [exact Hnode|]. split; [exact HND3 | exact HAP6].
Qed.

(* ================= (O1) pio_grow: grow's return (FSH_Fn_reader.grow_res, n = length dn) =================
   The call state c = (lyc Sc Uc W1 memC) to grow's return c' = (ly' S' U' W' mem'), with the journal over grow's
   footprint FPg (v's kids / keys and n-cap fields, the old kids / keys blocks, the image statics): the object moves
   to the new kids / keys arrays (or stays, n < cap), and the live list L = old slots ++ Di becomes L' = new slots ++
   Di, its heads tracked through grow's two U steps (ugrow1). *)
Lemma pio_grow : forall ly S U lyc Sc Uc (W1 : world tfibsegs) memC mdC ly' S' U' (W' : world tfibsegs)
  mem' md' kg spC v text len tcap (n : nat) (dn : list (list Z * PjTree.jv)) kids keys cap k' y' cap'
  Dold Dnew Di Da T,
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  let L' := parse_items_shape.pis_slots true k' y' cap' ++ Di in
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  let FPg := [(v + 24, v + 40); (v + 48, v + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP in
  length dn = n -> (n <= Z.to_nat cap)%nat -> 0 <= cap ->
  ARU tfibsegs B lyc Sc Uc W1 memC mdC -> FSupoisonU.fs_heads B lyc Sc Uc -> FSupoisonU.fs_heads B ly S U ->
  rd_text tfibsegs B lyc Sc W1 memC text len tcap -> In (text - HEAD, tcap + HEAD) (ablocks B ly S) ->
  pobj tfibsegs B lyc Sc W1 memC v ->
  rd_blocks_ok tfibsegs B lyc Sc W1 memC L -> Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  Uc = U ++ rd_heads Da -> Permutation Da L ->
  rd_sum L = PjGrammar.held T -> (length L <= length T)%nat ->
  PjStruct.pj_hdr tfibsegs (rdW W1 memC) v 6 0 0 kids keys (Z.of_nat n) cap ->
  parse_items_shape.pis_open tfibsegs (rdW W1 memC) (ReaderRes.lin L) v true 0 kids keys cap (Z.of_nat n)
    (map snd dn) (map fst dn) Di ->
  grow_res 6 (Z.of_nat n) cap kids keys k' y' cap' Dold Dnew Uc U' ->
  ajournal tfibsegs B STK_grow spC FPg lyc Sc W1 (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kg ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  Permutation (ablocks B ly' S' ++ rd_hblocks Dold) (ablocks B lyc Sc ++ rd_hblocks Dnew) ->
  PjStruct.pj_hdr tfibsegs (rdW W' mem') v 6 0 0 k' y' (Z.of_nat n) cap' ->
  PjStruct.pj_slots_at (fun a k => In (a, k) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap')) 6 k' y'
    (Z.of_nat n) cap' ->
  rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  rd_moved tfibsegs W1 W' memC mem' kids k' (56 * cap) -> rd_moved tfibsegs W1 W' memC mem' keys y' (8 * cap) ->
  pobj tfibsegs B ly' S' W' mem' v ->
  rd_sizes_ok (PjRoundTrip.grow_ev true n (Z.to_nat cap)) ->
  exists Da',
    rd_text tfibsegs B ly' S' W' mem' text len tcap /\
    rd_blocks_ok tfibsegs B ly' S' W' mem' L' /\ Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks L') /\
    U' = U ++ rd_heads Da' /\ Permutation Da' L' /\
    rd_sum L' = PjGrammar.held (T ++ PjRoundTrip.grow_ev true n (Z.to_nat cap)) /\
    (length L' <= length (T ++ PjRoundTrip.grow_ev true n (Z.to_nat cap)))%nat /\
    FSupoisonU.fs_heads B ly' S' U' /\
    cap' = Z.of_nat (PjRoundTrip.gcap n (Z.to_nat cap)) /\ Z.of_nat n < cap' /\
    parse_items_shape.pis_open tfibsegs (rdW W' mem') (ReaderRes.lin L') v true 0 k' y' cap' (Z.of_nat n)
      (map snd dn) (map fst dn) Di.
Proof.
intros ly S U lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' kg spC v text len tcap n dn kids keys cap k' y' cap'
  Dold Dnew Di Da T L L' Dold0 FPg Hn Hncap Hcap0 HARUc HHc HH HTc HTe HPc HBc HPmc HUc HDa Hsum Hlen Hhc Hopc
  HG HJ HARU' HPg Hh' Hsl' HBn Hmk Hmy HP' Hsz.
pose proof asan_consts as (C1 & _). assert (HEADv : HEAD = 16) by reflexivity.
pose proof HARUc as (HARc & OKc & POc).
pose proof HARU' as (HAR' & OK' & PO').
pose proof Hopc as (HNDc & HAc & _ & Hslc & _ & Hitc).
pose proof Hslc as (_ & (Hnc & Hc54) & Hc0 & Hcp).
assert (Ecap : Z.of_nat (Z.to_nat cap) = cap) by lia.
assert (HDo : forall p k, In (p, k) Dold0 -> In (p, k) L) by (intros p k H; apply in_or_app; left; exact H).
assert (HDi : forall p k, In (p, k) Di -> In (p, k) L) by (intros p k H; apply in_or_app; right; exact H).
assert (OLDH : forall p k, In (p, k) Dold0 -> In (p - HEAD, k + HEAD) (ablocks B lyc Sc) /\ 0 < k)
  by (intros p k H; destruct (HBc p k (HDo p k H)) as (Hin & _ & Hk & _); split; [exact Hin | exact Hk]).
destruct (pio_jr_frames _ _ _ lyc Sc W1 _ mdC ly' S' W' _ md' _ HJ HARc) as (Hfr' & HFA').
(* grow's journal keeps a live block byte off FPg *)
assert (KEEPc : forall P N z, In (P, N) (ablocks B lyc Sc) -> P <= z < P + req_size N -> ~ inFP FPg z ->
  rdW W' mem' (Z_to_bv 64 z) = rdW W1 memC (Z_to_bv 64 z)).
{ intros P N z Hin Hz Hf.
  refine (proj2 (fsw_journal_kept_byte B STK_grow spC FPg lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' kg z
    HJ HARUc OK' PO' _ Hf)).
  left. exists P, N. split; [exact Hin | exact Hz]. }
(* a byte of a block of Di, v's first byte, and the text's head are off FPg *)
assert (DiFP : forall p k z, In (p, k) Di -> p - HEAD <= z < p + k -> ~ inFP FPg z).
{ intros p k z Hpk Hz. pose proof (HBc p k (HDi p k Hpk)) as (Hin & _ & Hk & _).
  apply pio_off_FPg.
  - assert (Hb : forall x, p <= x < p + k -> ~ (v <= x < v + 56)).
    { intros x Hx. apply (HAc (p, k) x (HDi p k Hpk)). unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
    pose proof (pio_blk_off_obj lyc Sc W1 _ mdC memC v p k HARc HPc Hin Hk Hb z Hz). lia.
  - intros p0 k0 H0 Hz0. destruct (OLDH p0 k0 H0) as (Hin0 & Hk0). rewrite pio_req_hb in Hz0 by exact Hk0.
    apply (pio_rb_disj lyc Sc W1 _ mdC p k p0 k0 z z HARc Hin Hin0 Hk Hk0); [|exact Hz|lia|reflexivity].
    intros E. rewrite E in Hpk. exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ HNDc H0 Hpk).
  - exact (proj1 (proj2 (proj2 (pio_rb_geo lyc Sc W1 _ mdC memC p k z HARc (HBc p k (HDi p k Hpk)) Hz)))). }
assert (vFP : ~ inFP FPg v).
{ apply pio_off_FPg.
  - lia.
  - intros p0 k0 H0 Hz0. destruct (OLDH p0 k0 H0) as (Hin0 & Hk0). rewrite pio_req_hb in Hz0 by exact Hk0.
    destruct (Z_lt_le_dec v p0) as [Hl|Hg].
    + exact (pio_head16_off_obj lyc Sc W1 _ mdC memC v p0 k0 v HARc HPc Hin0 Hk0 ltac:(lia) ltac:(lia)).
    + exact (HAc (p0, k0) v (HDo p0 k0 H0) ltac:(unfold PjStruct.pj_holds; cbn [fst snd]; lia) ltac:(lia)).
  - exact (proj1 (proj2 (proj2 (pio_v_geo lyc Sc W1 _ mdC memC v v HARc HPc ltac:(lia))))). }
assert (TXT : forall z, text - HEAD <= z < text - HEAD + 8 -> ~ inFP FPg z).
{ intros z Hz. pose proof HTc as (_ & Hrt & _). pose proof Hrt as (Hint & _ & Hkt & _).
  apply pio_off_FPg.
  - pose proof (pio_head_off_obj lyc Sc W1 _ mdC memC v text tcap z HARc HPc Hint Hkt Hz). lia.
  - intros p0 k0 H0 Hz0. destruct (OLDH p0 k0 H0) as (Hin0 & Hk0). rewrite pio_req_hb in Hz0 by exact Hk0.
    apply (pio_rb_disj lyc Sc W1 _ mdC text tcap p0 k0 z z HARc Hint Hin0 Hkt Hk0); [|lia|lia|reflexivity].
    intros E. injection E as E1 E2. subst p0 k0.
    exact (pio_perm_fresh lyc Sc W1 _ mdC _ L text tcap HARc HPmc (HDo _ _ H0) HTe).
  - exact (proj1 (proj2 (proj2 (pio_rb_geo lyc Sc W1 _ mdC memC text tcap z HARc Hrt ltac:(lia))))). }
(* the block holding v survives grow *)
assert (SURVv : forall b mm, In (b, mm) (ablocks B lyc Sc) -> b + HEAD <= v -> v + 56 <= b + req_size mm ->
  In (b, mm) (ablocks B ly' S')).
{ intros b mm Hb H1 H2.
  apply (fsw_journal_block_live B STK_grow spC FPg lyc Sc W1 _ mdC ly' S' W' _ md' kg b mm v HJ Hb);
    [lia | exact vFP]. }
(* the text, the blocks of L', the heads at c' *)
assert (HT' : rd_text tfibsegs B ly' S' W' mem' text len tcap).
{ pose proof HTc as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
  pose proof T2 as (Hint & Hal & Hkt & Hvt).
  split; [|split; [exact Hal | split; [exact Hkt|]]].
  - apply (fsw_journal_block_live B STK_grow spC FPg lyc Sc W1 _ mdC ly' S' W' _ md' kg _ _ (text - HEAD) HJ Hint).
    + rewrite pio_req_hb by exact Hkt. lia.
    + apply TXT. lia.
  - intros j Hj.
    assert (Ez : rdW W' mem' (Z_to_bv 64 (text - HEAD + Z.of_nat j)) =
                 rdW W1 memC (Z_to_bv 64 (text - HEAD + Z.of_nat j))).
    { apply (KEEPc _ _ _ Hint); [rewrite pio_req_hb by exact Hkt; lia | apply TXT; lia]. }
    rewrite (pio_mbyte_raw _ _ _ Ez). exact (Hvt j Hj). }
assert (RB' : rd_blocks_ok tfibsegs B ly' S' W' mem' L').
{ intros p k Hpk. unfold L' in Hpk. apply in_app_or in Hpk as [Hs|Hd]; [exact (HBn p k Hs)|].
  apply (fs_rblock_kept_call B STK_grow spC FPg lyc Sc Uc W1 memC mdC ly' S' U' W' mem' md' kg p k HJ HARUc OK' PO');
    [exact (fun z => DiFP p k z Hd) | exact (HBc p k (HDi p k Hd))]. }
assert (HH' : FSupoisonU.fs_heads B ly' S' U').
{ apply (pSh_heads_after_grow B lyc Sc Uc ly' S' U' W1 W' memC mem' mdC md' v kids keys (Z.of_nat n) cap k' y' cap'
    Dold Dnew HARUc HARU' HHc HG).
  - intros r Hr. rewrite HUc. apply in_or_app. right. unfold rd_heads in Hr |- *.
    apply in_map_iff in Hr as ([p k] & <- & Hb). apply (in_map (fun b : Z * Z => (fst b - HEAD, HEAD))).
    exact (Permutation_in _ (Permutation_sym HDa) (HDo p k Hb)).
  - intros p k Hpk. exact (HBc p k (HDo p k Hpk)).
  - exact HBn.
  - intros p nn z Hin Hz Hf. exact (fsw_journal_block_live B STK_grow spC FPg lyc Sc W1 _ mdC ly' S' W' _ md' kg p nn z
      HJ Hin Hz Hf).
  - exact (pSh_obj_apart B lyc Sc W1 _ mdC memC v HARc HPc). }
(* ---- the two arms of grow_res ---- *)
assert (CASE : cap' = Z.of_nat (PjRoundTrip.gcap n (Z.to_nat cap)) /\ Z.of_nat n < cap' /\
  Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks L') /\
  (exists Da', U' = U ++ rd_heads Da' /\ Permutation Da' L') /\
  PjStruct.pj_apart (parse_items_shape.pis_slots true k' y' cap') v /\
  (k' = kids \/ forall p k, In (p, k) Di -> (p, k) <> (k', 56 * cap')) /\
  (length L' <= length L + length (PjRoundTrip.grow_ev true n (Z.to_nat cap)))%nat).
{ pose proof HG as HGc.
  destruct HGc as [(Hlt & Ek & Ey & Ec & Eo & En & EU)|(Heq & Ec & Eo & Hk16 & Hkm & Hy16 & _ & Edn & Um & Hug1 & Hug2)].
  - (* n < cap: nothing moves *)
    subst k' y' cap' Dold Dnew U'.
    split; [rewrite (pim_gcap_lt n (Z.to_nat cap) ltac:(lia)); lia|].
    split; [exact Hlt|].
    split.
    { change (rd_hblocks []) with (@nil (Z * Z)) in HPg. rewrite !app_nil_r in HPg.
      exact (Permutation_trans HPg HPmc). }
    split; [exists Da; split; [exact HUc | exact HDa]|].
    split; [intros b x Hb; apply HAc; apply in_or_app; left; exact Hb|].
    split; [left; reflexivity|].
    unfold PjRoundTrip.grow_ev. rewrite (proj2 (Nat.ltb_lt n (Z.to_nat cap)) ltac:(lia)).
    unfold L', L. cbn [length]. lia.
  - (* n = cap: kids / keys reallocated to cap' = cap2 cap *)
    change (ugrow1 Um U' keys y') in Hug2.
    assert (EDn : Dnew = [(k', 56 * cap'); (y', 8 * cap')]) by (rewrite Edn; reflexivity).
    assert (Ecn : Z.to_nat cap = n) by lia.
    assert (Hcap2 : cap' = Z.of_nat (PjRoundTrip.gcap n (Z.to_nat cap))).
    { rewrite Ecn, Ec, <- (pim_cap2 n n (Nat.le_refl n) (Nat.lt_irrefl n)). f_equal. lia. }
    assert (Hncap2 : Z.of_nat n < cap') by (rewrite Ec; unfold ReaderRes.cap2; destruct (Z.eqb_spec cap 0); lia).
    assert (ES2 : parse_items_shape.pis_slots true k' y' cap' = [(k', 56 * cap'); (y', 8 * cap')]).
    { unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
      rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity. }
    destruct (pSh_fresh_after_grow B lyc Sc ly' S' W' _ md' (Z.of_nat n) cap kids keys k' y' cap' Dold Dnew Uc U'
      HAR' HG HPg Heq) as (Fk & Fy).
    split; [exact Hcap2|]. split; [exact Hncap2|].
    split.
    { rewrite EDn, Eo in HPg.
      change L with (Dold0 ++ Di) in HPmc. rewrite pim_rd_hblocks_app in HPmc.
      unfold L'. rewrite ES2, pim_rd_hblocks_app.
      exact (pio_perm_cancel _ _ _ _ _ _ HPg HPmc). }
    split.
    { assert (NDUc : List.NoDup Uc).
      { destruct OKc as (F & PW). apply pSh_nodup; [exact PW|]. rewrite Forall_forall in F |- *.
        intros r Hr. destruct (F r Hr) as (_ & H8 & _). lia. }
      assert (HnU : forall p k, In (p, k) L -> ~ In (p - HEAD, HEAD) U).
      { intros p k Hpk HU0. rewrite HUc in NDUc. apply NoDup_ListNoDup in NDUc.
        apply (parse_items_shape.pis_nodup_app_disj _ _ _ _ NDUc HU0).
        change (In ((fun b : Z * Z => (fst b - HEAD, HEAD)) (p, k)) (map (fun b : Z * Z => (fst b - HEAD, HEAD)) Da)).
        apply in_map. exact (Permutation_in _ (Permutation_sym HDa) Hpk). }
      rewrite HUc in Hug1.
      destruct (pio_ug_step U (rd_heads Da) Um kids k' Hug1) as (R1 & EUm & R1z & R1p).
      { intros Hk.
        assert (Hc : 0 < cap) by (destruct (Z.eq_dec cap 0) as [E0|]; [exfalso; exact (Hk (proj1 (Hc0 E0))) | lia]).
        exact (HnU kids (56 * cap) (proj1 (Hcp Hc))). }
      rewrite EUm in Hug2.
      destruct (pio_ug_step U R1 U' keys y' Hug2) as (R2 & EU2 & R2z & R2p).
      { intros Hk.
        assert (Hc : 0 < cap)
          by (destruct (Z.eq_dec cap 0) as [E0|]; [exfalso; exact (Hk (proj2 (Hc0 E0) eq_refl)) | lia]).
        exact (HnU keys (8 * cap) (proj2 (Hcp Hc) eq_refl)). }
      assert (PR2 : Permutation R2 (rd_heads L')).
      { unfold L'. rewrite ES2. unfold rd_heads. cbn [map app fst snd].
        destruct (Z.eq_dec cap 0) as [E0|Hc].
        - destruct (Hc0 E0) as (Ek0 & Ey0). specialize (Ey0 eq_refl).
          rewrite (R2z Ey0), (R1z Ek0). unfold rd_heads.
          apply pio_heads_zero. apply Permutation_map.
          eapply Permutation_trans; [exact HDa|]. change L with (Dold0 ++ Di). unfold Dold0. rewrite E0.
          apply Permutation_refl.
        - assert (Hc' : 0 < cap) by lia.
          destruct (pio_rb_geo lyc Sc W1 _ mdC memC kids (56 * cap) kids HARc (HBc _ _ (proj1 (Hcp Hc'))) ltac:(lia))
            as (GK & _).
          destruct (pio_rb_geo lyc Sc W1 _ mdC memC keys (8 * cap) keys HARc (HBc _ _ (proj2 (Hcp Hc') eq_refl))
            ltac:(lia)) as (GY & _).
          apply (pio_heads_two (map (fun b : Z * Z => (fst b - HEAD, HEAD)) Da) R1 R2 _ (kids - HEAD, HEAD)
            (keys - HEAD, HEAD)).
          + change ((kids - HEAD, HEAD) :: (keys - HEAD, HEAD) :: map (fun b : Z * Z => (fst b - HEAD, HEAD)) Di) with
              (map (fun b : Z * Z => (fst b - HEAD, HEAD)) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di)).
            apply Permutation_map. eapply Permutation_trans; [exact HDa|]. change L with (Dold0 ++ Di).
            unfold Dold0. rewrite (pSh_blk_ne0 kids keys cap ltac:(lia)). apply Permutation_refl.
          + exact (R1p ltac:(lia)).
          + exact (R2p ltac:(lia)). }
      unfold rd_heads in PR2. apply Permutation_map_inv in PR2 as (Da' & E2 & P2).
      exists Da'. split; [rewrite EU2, E2; reflexivity|]. first [exact (Permutation_sym P2) | exact P2]. }
    split.
    { rewrite ES2. intros b z Hb Hz.
      assert (HiK : In (k', 56 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES2; left; reflexivity).
      assert (HiY : In (y', 8 * cap') (parse_items_shape.pis_slots true k' y' cap'))
        by (rewrite ES2; right; left; reflexivity).
      destruct Hb as [<-|[<-|[]]]; unfold PjStruct.pj_holds in Hz; cbn [fst snd] in Hz.
      - destruct (HBn _ _ HiK) as (Hin & _ & Hk & _).
        apply (pio_new_apart lyc Sc W1 memC v ly' S' W' _ md' _ _ HAR' HPc Hfr' HFA' SURVv Hin Fk z).
        rewrite pio_req_hb by exact Hk. lia.
      - destruct (HBn _ _ HiY) as (Hin & _ & Hk & _).
        apply (pio_new_apart lyc Sc W1 memC v ly' S' W' _ md' _ _ HAR' HPc Hfr' HFA' SURVv Hin Fy z).
        rewrite pio_req_hb by exact Hk. lia. }
    split.
    { right. intros p k Hpk E. injection E as Ep Ek. subst p k.
      destruct (HBc _ _ (HDi _ _ Hpk)) as (Hin & _). exact (Fk Hin). }
    unfold L', L, PjRoundTrip.grow_ev. rewrite ES2, (proj2 (Nat.ltb_ge n (Z.to_nat cap)) ltac:(lia)).
    rewrite !length_app. cbn [length]. lia. }
destruct CASE as (Hcap2 & Hncap' & HPA' & (Da' & EU' & HDa') & HAPs & HKD & HlenL).
assert (Hcap'0 : 0 < cap') by lia.
assert (ES' : parse_items_shape.pis_slots true k' y' cap' = [(k', 56 * cap'); (y', 8 * cap')]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity. }
assert (HinK' : In (k', 56 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES'; left; reflexivity).
assert (HinY' : In (y', 8 * cap') (parse_items_shape.pis_slots true k' y' cap')) by (rewrite ES'; right; left; reflexivity).
pose proof (HBn _ _ HinK') as HbK'. pose proof (HBn _ _ HinY') as HbY'.
pose proof HbK' as (HinK'A & Hk'16 & _ & _).
assert (Hk'8 : k' mod 8 = 0).
{ apply Z.mod_divide in Hk'16 as [q Hq]; [|lia]. rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia.
  apply Z_mod_mult. }
destruct (pio_rb_geo ly' S' W' _ md' mem' k' (56 * cap') k' HAR' HbK' ltac:(lia)) as (GK0 & _).
destruct (pio_rb_geo ly' S' W' _ md' mem' k' (56 * cap') (k' + 56 * cap' - 1) HAR' HbK' ltac:(lia)) as (GK1 & _).
destruct (pio_rb_geo ly' S' W' _ md' mem' y' (8 * cap') y' HAR' HbY' ltac:(lia)) as (GY0 & _).
destruct (pio_rb_geo ly' S' W' _ md' mem' y' (8 * cap') (y' + 8 * cap' - 1) HAR' HbY' ltac:(lia)) as (GY1 & _).
assert (HNDL' : NoDup L') by exact (pio_nodup_L ly' S' W' _ md' _ L' HAR' HPA').
(* the open object at c' *)
assert (Hop' : parse_items_shape.pis_open tfibsegs (rdW W' mem') (ReaderRes.lin L') v true 0 k' y' cap' (Z.of_nat n)
  (map snd dn) (map fst dn) Di).
{ apply (parse_items_shape.pis_xfer tfibsegs (rdW W1 memC) (ReaderRes.lin L) (rdW W' mem') (ReaderRes.lin L') v true 0
    kids keys cap (Z.of_nat n) _ _ _ 0 k' y' cap' (Z.of_nat n) Hopc Hh').
  - apply (parse_items_shape.pis_slots_at_mv _ _ true k' y' (Z.of_nat n) (Z.of_nat n) cap' Hsl' ltac:(lia) ltac:(lia)).
    intros a0 k0 H. unfold ReaderRes.lin, L'. apply in_or_app. left. exact H.
  - intros E. discriminate E.
  - exact HNDL'.
  - exact HAPs.
  - intros a0 k0 H. unfold ReaderRes.lin, L'. apply in_or_app. right. exact H.
  - intros z (b & Hb & Hz). destruct b as [p k]. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
    pose proof (HBc p k (HDi p k Hb)) as (Hin & _ & Hk & _).
    apply pio_same_raw. apply (KEEPc (p - HEAD) (k + HEAD) z Hin); [rewrite pio_req_hb by exact Hk; lia|].
    apply (DiFP p k z Hb). lia.
  - rewrite length_map, Hn. intros i Hi. exact (Hmk i ltac:(lia)).
  - rewrite length_map, Hn. intros i Hi _.
    destruct (pio_kids_present _ _ _ _ _ _ _ i Hitc ltac:(rewrite length_map, Hn; lia)) as (b & Hb).
    destruct (pio_rb_geo ly' S' W' _ md' mem' k' (56 * cap') (k' + i) HAR' HbK' ltac:(lia)) as (_ & Hni & _).
    apply (pio_wr_of_mbyte _ (k' + i) b ltac:(lia) Hni). rewrite (Hmk i ltac:(lia)). exact Hb.
  - intros _. rewrite length_map, Hn. split; [exact Hk'8|]. lia.
  - destruct HKD as [E|HKD]; [left; exact E|right].
    intros [p k] x Hb Hh Hx. unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh. rewrite length_map, Hn in Hx.
    assert (HbL : In (p, k) L') by (unfold L'; apply in_or_app; right; exact Hb).
    pose proof (RB' p k HbL) as (Hin' & _ & Hk & _).
    apply (pio_rb_disj ly' S' W' _ md' p k k' (56 * cap') x x HAR' Hin' HinK'A Hk ltac:(lia) (HKD p k Hb));
      [lia | lia | reflexivity].
  - intros _. rewrite length_map, Hn. split; [intros i Hi; exact (Hmy i ltac:(lia)) | intros _; lia]. }
assert (HsumL' : rd_sum L' = PjGrammar.held (T ++ PjRoundTrip.grow_ev true n (Z.to_nat cap))).
{ unfold L'. rewrite pim_rd_sum_app, PjGrammar.held_app, pim_held_grow by lia.
  change L with (parse_items_shape.pis_slots true kids keys cap ++ Di) in Hsum. rewrite pim_rd_sum_app in Hsum.
  rewrite (pio_sum_slots k' y' cap') by lia. rewrite (pio_sum_slots kids keys cap) in Hsum by lia. lia. }
assert (HlenL'' : (length L' <= length (T ++ PjRoundTrip.grow_ev true n (Z.to_nat cap)))%nat)
  by (rewrite length_app; lia).
exists Da'. split; [exact HT'|]. split; [exact RB'|]. split; [exact HPA'|]. split; [exact EU'|]. split; [exact HDa'|].
split; [exact HsumL'|]. split; [exact HlenL''|]. split; [exact HH'|]. split; [exact Hcap2|].
split; [exact Hncap' | exact Hop'].
Qed.

End O.
