(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan) composition of grow's walk (FSW_grow.v's stage lemmas)
   through its two fuzz_realloc calls: grow_holds : grow_spec (lib/B/FSH_Fn_reader.v:575). rule 24 line, reuse search and
   port source: FSW_grow.v's header (lane brief (internal path), CONFIRM a Theorem Labs lane;
   ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/B/Prog/grow.v).
   The callee contract is ALLOC's fuzz_realloc_spec (lib/B/FSH_Fn_alloc.v, CTX-free, the text of S0
   a working branch f32db4da382), the named Section hypothesis fuzz_realloc_holds; the image fact is
   FsShadowSyms B (the shadow-base cells; FSW_grow.v's stages). The theorem's shape mirrors image A's
   (grow_holds : forall {fx rc SK} B, FsShadowSyms B -> fuzz_realloc_spec tfibsegs B -> grow_spec tfibsegs B), with
   tfibsegs B's image (lib/B/YB1v.v, AsanUbsan's loaded segments); grow_spec's Section hypothesis IMG (fs_img_facts) is not
   needed by this walk, so it is not a premise.
   PORTED lemma by lemma (copied, never Required, never bridged), from the image-A walk of the same C, final at
   a working branch 728177ca53c lib/A/Prog/FSW_grow_holds.v (a Theorem Labs lane; its lines 1-501 equal 582c4d69613's):
     fs_pstat_img, grow_frame_chunks (frame 96, s9), gB_rs_ok / gB_disj (shadow cell of v + 24 at atom 25 = s9),
     gC_rs_ok / gC_disj (frame 96), grow_bb, grow_rsum_app, grow_rsum_perm, grow_garr8_ex, grow_mbyte_eq, grow_val_eq,
     grow_writable_grows, fs_pstat_not_ro (B's static addresses 0xa41c0 / 0x5daac0 .. 0x5dab08), grow_perm_swap,
     grow_blk_nodup, grow_block_bytes, grow_v_off_rblk, grow_pj_rw, grow_awr, grow_hdr_upd, grow_glob_img,
     grow_arodata_img, grow_rblock_eq, grow_pobj_run, grow_realloc_step, grow_inFP_blk, grow_val_eqm, grow_moved,
     grow_word_eq, grow_req, ghide, grow_cap_arm (B: frame 96, resumes 0x83d68 / 0x83db8, s9 = the shadow of v + 24,
     the kept registers 3 4 18 26 27) and grow_holds;
   and, for B's own code, from a working branch 75e39a1f41d lib/B/Prog/grow.v: the realloc arms' shape
   (gr_oom_seg / gr_keys_oom_seg are dead here: grow_spec's quiet makes every fuzz_realloc grant, and the resumed a0's
   fact decides the OOM beqz 0x83d6c / 0x83db8 not taken) and the size arithmetic gr_cap2 / gr_sz. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_grow_holds.v, with its module paths and module names changed; 1108 of its 1188 lines of code are new or changed and 1234 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) copy of lib/A/Prog/FSW_pj_set_fn.v (a working branch
   866e579f961, taken there from a working branch a091229a685 with its mem_grows premise weakened), same lemma
   names and bodies; imports point at lib/B's image files and kit. Its image values are read by name from lib/B
   (FS_IMG_END, FS_PSTAT_FP, FS_RO_STRS, FS_SN_FMTS); fn_ro_range / fn_fmt_range are recomputed on image B's tables. *)
(* pj_set's DATA side (fs.asan-ubsan pj_set 0x83adc, a Theorem Labs lane): from the byte facts pj_set's machine stages export
   after each of its calls (lib/B/Prog/FSW_pj_set_holds.v pj_set_get_call / pj_set_grow_call / pj_set_sd_call
   continuations, FSW_pj_set.v pj_set_stageD's continuation, the memcpy and memset steps), the data clauses of
   pj_set_spec's post (lib/B/FSH_Fn_reader.v): obj's tree with the new member, val zeroed, both objects still placed,
   the key still a C string, and the two block permutations.
   LEMMA FILE (rule 24): no function contract is proved here. The tree reasoning is the released plain pj_set proof's,
   generic in segs and memory: lib/Prog/pj_set_shape.v (ps_node_open, ps_obj_node, ps_set_miss, ps_mems_split) and
   lib/Prog/parse_items_shape.v (pis_xfer, pis_snoc, pis_node_xfer), instantiated at tfibsegs with the memories
   mrestrict (w_H W) m and the block relation fun a k => In (a, k) L. What is new is the ASan block geometry: which
   live block each byte belongs to, from AR's separation law at the two ends of grow (its Permutation of ablocks). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj FSW_K3 FSW_rd FSW_rres FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_pj_set_tbl FSW_pj_set FSW_rdx.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require pj_set_shape parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= generic helpers ================= *)
(* the ASan block of a reader block (a, k): its 16-byte head and the request (FSH_Gen.fs_rblock) *)
Definition fn_hb (e : Z * Z) : Z * Z := (fst e - HEAD, snd e + HEAD).

Lemma fn_hb_inj : forall e1 e2, fn_hb e1 = fn_hb e2 -> e1 = e2.
Proof. intros [p k] [q j] E. unfold fn_hb in E. cbn [fst snd] in E. injection E as E1 E2. f_equal; lia. Qed.

Lemma fn_holds_hb : forall e x, PjStruct.pj_holds e x -> PjStruct.pj_holds (fn_hb e) x.
Proof. intros [p kk] x. unfold PjStruct.pj_holds, fn_hb, HEAD. cbn [fst snd]. lia. Qed.

Lemma fn_req_hb : forall k, 0 < k -> req_size (k + HEAD) = k + HEAD.
Proof. intros k Hk. unfold req_size, HEAD. destruct (Z.eqb_spec (k + 16) 0); lia. Qed.

Definition fn_zz_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* a block live before a step that is not among the freed ones is live after it and is none of the new ones *)
Lemma fn_surv : forall (A3 HO A1 HN : list (Z * Z)) e,
  Permutation (A3 ++ HO) (A1 ++ HN) -> NoDup A3 -> In e A1 -> ~ In e HO -> In e A3 /\ ~ In e HN.
Proof.
intros A3 HO A1 HN e HP HD H1 H0. apply NoDup_ListNoDup in HD.
assert (I3 : In e A3).
{ assert (Hin : In e (A3 ++ HO)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1).
  apply in_app_or in Hin as [Hin|Hin]; [exact Hin | contradiction]. }
split; [exact I3|]. intros HNe.
assert (C : forall x, count_occ fn_zz_dec (A3 ++ HO) x = count_occ fn_zz_dec (A1 ++ HN) x).
{ apply Permutation_count_occ. exact HP. }
specialize (C e). rewrite !count_occ_app in C.
assert (C3 : forall x, In x A3 -> count_occ fn_zz_dec A3 x = 1%nat) by (apply NoDup_count_occ'; exact HD).
assert (C0 : count_occ fn_zz_dec HO e = 0%nat) by (apply count_occ_not_In; exact H0).
assert (C1 : (count_occ fn_zz_dec A1 e > 0)%nat) by (apply count_occ_In; exact H1).
assert (CN : (count_occ fn_zz_dec HN e > 0)%nat) by (apply count_occ_In; exact HNe).
specialize (C3 e I3). lia.
Qed.

Lemma fn_pw_map_in : forall (X : Type) (f : X -> Z * Z) (A : list X) e1 e2,
  pairwise zdisjoint (map f A) -> In e1 A -> In e2 A -> e1 <> e2 -> zdisjoint (f e1) (f e2).
Proof.
intros X f A. induction A as [|x t IH]; intros e1 e2 HP H1 H2 Hne; [destruct H1|].
cbn [map pairwise] in HP. destruct HP as [HF HP]. rewrite Forall_forall in HF.
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- subst. contradiction.
- subst x. apply HF. apply in_map. exact H2.
- subst x. pose proof (HF (f e1) (in_map f t e1 H1)) as D. unfold zdisjoint in *. lia.
- exact (IH e1 e2 HP H1 H2 Hne).
Qed.

Lemma fn_pw_map_nodup : forall (X : Type) (f : X -> Z * Z) (A : list X),
  pairwise zdisjoint (map f A) -> (forall e, In e A -> 0 < snd (f e)) -> NoDup A.
Proof.
intros X f A HP Hpos. apply NoDup_ListNoDup. revert HP Hpos.
induction A as [|x t IH]; intros HP Hpos; [apply List.NoDup_nil|].
cbn [map pairwise] in HP. destruct HP as [HF HP]. rewrite Forall_forall in HF. apply List.NoDup_cons.
- intros Hin. pose proof (HF (f x) (in_map f t x Hin)) as D. pose proof (Hpos x (or_introl eq_refl)) as P.
  unfold zdisjoint in D. lia.
- apply IH; [exact HP | intros e He; apply Hpos; right; exact He].
Qed.

Lemma fn_pw_cross : forall (L1 L2 : list (Z * Z)) x y, pairwise zdisjoint (L1 ++ L2) -> In x L1 -> In y L2 ->
  zdisjoint x y.
Proof.
intros L1. induction L1 as [|z t IH]; intros L2 x y HP H1 H2; [destruct H1|].
cbn [app pairwise] in HP. destruct HP as [HF HP]. destruct H1 as [E|H1].
- subst z. rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact H2.
- exact (IH L2 x y HP H1 H2).
Qed.

Lemma fn_pstat_off : forall x, x < 0x10000 \/ FS_IMG_END <= x -> ~ inFP FS_PSTAT_FP x.
Proof.
intros x Hx (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr. unfold FS_IMG_END in Hx.
destruct Hr as [E|[E|[E|[E|[]]]]]; subst r; cbn [fst snd] in Ha; lia.
Qed.

(* fs's read-only strings and formats lie in the image's data, between 0x10000 and FS_IMG_END (computed) *)
Lemma fn_ro_range : forall p l, In (p, l) FS_RO_STRS -> 0x10000 <= p /\ p + Z.of_nat (length l) + 1 <= FS_IMG_END.
Proof.
intros p l H.
assert (C : forallb (fun e => (0x10000 <=? fst e) && (fst e + Z.of_nat (length (snd e)) + 1 <=? FS_IMG_END))
  FS_RO_STRS = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C (p, l) H). cbn [fst snd] in C.
apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma fn_fmt_range : forall p ps, In (p, ps) FS_SN_FMTS ->
  0x10000 <= p /\ p + Z.of_nat (length (fmt_bytes ps)) + 1 <= FS_IMG_END.
Proof.
intros p ps H.
assert (C : forallb (fun e => (0x10000 <=? fst e) && (fst e + Z.of_nat (length (fmt_bytes (snd e))) + 1 <=? FS_IMG_END))
  FS_SN_FMTS = true) by (vm_compute; reflexivity).
rewrite forallb_forall in C. specialize (C (p, ps) H). cbn [fst snd] in C.
apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

Lemma fn_node_nodup : forall segs m lblk p t D, PjStruct.pj_node segs m lblk p t D -> NoDup D.
Proof. intros segs m lblk p t D H. destruct t; cbn [PjStruct.pj_node] in H; exact (proj1 H). Qed.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

(* ---- byte helpers over tfibsegs ---- *)
Lemma fn_mbyte_eq : forall (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  mbyte tfibsegs m' x = mbyte tfibsegs m x.
Proof. intros m m' x E. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma fn_val_xfer : forall (m m' : word -> option byte) a0 (wd : nat) v, val_mem tfibsegs m a0 wd v ->
  (forall j, (j < wd)%nat -> mbyte tfibsegs m' (a0 + Z.of_nat j) = mbyte tfibsegs m (a0 + Z.of_nat j)) ->
  val_mem tfibsegs m' a0 wd v.
Proof. intros m m' a0 wd v H E j Hj. rewrite E by exact Hj. exact (H j Hj). Qed.

Lemma fn_val_some : forall (m : word -> option byte) a0 (wd : nat) v, val_mem tfibsegs m a0 wd v ->
  forall x, a0 <= x < a0 + Z.of_nat wd -> exists b, mbyte tfibsegs m x = Some b.
Proof.
intros m a0 wd v H x Hx. assert (Hj : (Z.to_nat (x - a0) < wd)%nat) by lia.
pose proof (H (Z.to_nat (x - a0)) Hj) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (a0 + (x - a0)) with x in Hb by lia. eexists. exact Hb.
Qed.

Lemma fn_some_of_mbyte : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x ->
  mbyte tfibsegs m x = Some b -> m (Z_to_bv 64 x) = Some b.
Proof.
intros m x b Hx Hn H. unfold mbyte in H. rewrite (YCbq.seg_rom_none tfibsegs x Hx Hn) in H.
destruct (m (Z_to_bv 64 x)); congruence.
Qed.

Lemma fn_wr_of_mbyte : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img tfibsegs x ->
  mbyte tfibsegs m x = Some b -> writable_at tfibsegs m x.
Proof.
intros m x b Hx Hn H. pose proof (fn_some_of_mbyte m x b Hx Hn H) as E.
unfold writable_at, wview. rewrite E. discriminate.
Qed.

Lemma fn_aview_some : forall (H : word -> bool) (m : word -> option byte) x v, aview tfibsegs H m x = Some v ->
  mbyte tfibsegs (mrestrict H m) x = Some (Z_to_bv 8 v).
Proof.
intros H m x v E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) x) as [b|]; cbn [option_map] in E;
  [|discriminate E].
injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma fn_aview_none : forall (H : word -> bool) (m : word -> option byte) x,
  aview tfibsegs H m x = None <-> mbyte tfibsegs (mrestrict H m) x = None.
Proof.
intros H m x. unfold aview. destruct (mbyte tfibsegs (mrestrict H m) x); cbn [option_map]; split; intros E;
  solve [discriminate E | reflexivity].
Qed.

Lemma fn_mbyte_grows : forall (M M' : word -> option byte) x, mem_grows M M' ->
  mbyte tfibsegs M x <> None -> mbyte tfibsegs M' x <> None.
Proof.
intros M M' x G H. unfold mbyte in *. destruct (M (Z_to_bv 64 x)) eqn:E.
- assert (G' : M' (Z_to_bv 64 x) <> None) by (apply G; rewrite E; discriminate).
  destruct (M' (Z_to_bv 64 x)) eqn:E'; [discriminate | exfalso; exact (G' eq_refl)].
- destruct (M' (Z_to_bv 64 x)); [discriminate | exact H].
Qed.

Lemma fn_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) x x',
  aview tfibsegs H' m' x' = aview tfibsegs H m x ->
  mbyte tfibsegs (mrestrict H' m') x' = mbyte tfibsegs (mrestrict H m) x.
Proof.
intros H H' m m' x x' E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') x') as [b'|], (mbyte tfibsegs (mrestrict H m) x) as [b|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* a whole object of 56 visible, non-image bytes is a pj_rw object *)
Lemma fn_rw : forall (M : word -> option byte) v, v mod 8 = 0 -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  (forall x, v <= x < v + 56 -> ~ in_img tfibsegs x /\ exists b, mbyte tfibsegs M x = Some b) ->
  PjStruct.pj_rw tfibsegs M v.
Proof.
intros M v H8 H0 H1 H. split; [exact H8|]. split; [exact H0|]. split; [exact H1|].
intros x Hx. destruct (H x Hx) as (Hi & b & Hb). split.
- exact (fn_wr_of_mbyte M x b ltac:(lia) Hi Hb).
- exists b. exact Hb.
Qed.

Lemma fn_shadow_rng : forall x, 0 <= x < alloc_ceiling ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44 /\ 0 <= shadow_of_addr SHADOW_OFF x < alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _). pose proof (fsw_shadow_below x Hx) as Hb.
split; [|exact Hb]. unfold shadow_of_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

(* ---- AR's block geometry ---- *)
Definition fn_hm (ly : alayout) (S : astate) (x : Z) : Prop :=
  (exists p nn, In (p, nn) (ablocks B ly S) /\ p <= x < p + req_size nn) \/
  (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid).

Lemma fn_sep_blocks : forall ly S (W : world tfibsegs) mx md b m p k, AR tfibsegs B ly S W mx md ->
  In (b, m) (ablocks B ly S) -> In (p, k) (ablocks B ly S) -> (b, m) <> (p, k) ->
  zdisjoint (b, req_size m) (p, req_size k).
Proof.
intros ly S W mx md b m p k HAR H1 H2 Hne.
destruct (al_sep tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
exact (fn_pw_map_in _ (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) (p, k) Hp H1 H2 Hne).
Qed.

Lemma fn_sep_bf : forall ly S (W : world tfibsegs) mx md b m cid pos, AR tfibsegs B ly S W mx md ->
  In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  zdisjoint (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid).
Proof.
intros ly S W mx md b m cid pos HAR H1 H2.
destruct (al_sep tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md HAR) as [Hp _].
apply (fn_pw_cross _ _ _ _ Hp).
- exact (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) H1).
- exact (in_map (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) H2).
Qed.

Lemma fn_nodup_blocks : forall ly S (W : world tfibsegs) mx md, AR tfibsegs B ly S W mx md -> NoDup (ablocks B ly S).
Proof.
intros ly S W mx md HAR.
destruct (al_sep tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
apply (fn_pw_map_nodup _ (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ Hp).
intros [p k] Hin. destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md p k HAR Hin)
  as (_ & _ & _ & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as (R & _). cbn [fst snd]. lia.
Qed.

Lemma fn_blk_img : forall ly S (W : world tfibsegs) mx md p nn x, AR tfibsegs B ly S W mx md ->
  In (p, nn) (ablocks B ly S) -> p <= x < p + req_size nn -> ~ in_img tfibsegs x.
Proof.
intros ly S W mx md p nn x HAR Hin Hx.
refine (proj2 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md x HAR _)).
left. exists p, nn. split; [exact Hin | exact Hx].
Qed.

Lemma fn_blk_off : forall ly S (W : world tfibsegs) mx md p nn x, AR tfibsegs B ly S W mx md ->
  In (p, nn) (ablocks B ly S) -> p <= x < p + req_size nn -> x < 0x10000 \/ FS_IMG_END <= x.
Proof. intros ly S W mx md p nn x HAR Hin Hx. destruct (fsw_ablock_off_img B ly S W mx md p nn HAR Hin); lia. Qed.

Lemma fn_pobj_img : forall ly S (W : world tfibsegs) mx md m v, AR tfibsegs B ly S W mx md ->
  pobj tfibsegs B ly S W m v -> forall x, v <= x < v + 56 -> ~ in_img tfibsegs x.
Proof.
intros ly S W mx md m v HAR ([((cid & pos & Hin & _ & _ & F1 & F2) & _)|((b & mm & Hin & B1 & B2) & _)] & _) x Hx;
  refine (proj2 (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mx md x HAR _)).
- right. left. exists cid, pos. split; [exact Hin | lia].
- left. exists b, mm. split; [exact Hin | unfold HEAD in B1; lia].
Qed.

Lemma fn_pobj_hm : forall ly S (W : world tfibsegs) m v, pobj tfibsegs B ly S W m v ->
  forall x, v <= x < v + 56 -> fn_hm ly S x.
Proof.
intros ly S W m v ([((cid & pos & Hin & _ & _ & F1 & F2) & _)|((b & mm & Hin & B1 & B2) & _)] & _) x Hx.
- right. exists cid, pos. split; [exact Hin | lia].
- left. exists b, mm. split; [exact Hin | unfold HEAD in B1; lia].
Qed.

(* a placed object keeps its placement when its shadow bytes and its own writability are kept *)
Lemma fn_pobj_xfer : forall ly S (W : world tfibsegs) (m m' : word -> option byte) v, pobj tfibsegs B ly S W m v ->
  (forall x, v <= x < v + 56 ->
     aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W) m') (v + i)) ->
  pobj tfibsegs B ly S W m' v.
Proof.
intros ly S W m m' v ([(Hf & H8 & Hr)|(Hb & H8 & Hr)] & _) Hsh Hw; (split; [|exact Hw]).
- left. split; [exact Hf|]. split; [exact H8|]. intros x Hx. destruct (Hr x Hx) as (s & Es & Ok).
  exists s. rewrite (Hsh x Hx). split; [exact Es | exact Ok].
- right. split; [exact Hb|]. split; [exact H8|]. intros x Hx. destruct (Hr x Hx) as (s & Es & Ok).
  exists s. rewrite (Hsh x Hx). split; [exact Es | exact Ok].
Qed.

(* ================= the walk's data, as a Section of facts ================= *)
Section P.
Variables (ly1 ly3 ly4 : alayout) (S1 S3 S4 : astate) (W1 W3 W4 : world tfibsegs)
  (m1 m3 m4 m5 m6 m7 mx1 mx4 : word -> option byte) (md1 md4 : Model)
  (o k w num str kids keys n cap k' y' cap' a : Z) (ms : list (list Z * PjTree.jv)) (tv : PjTree.jv)
  (D Dw Di Dold Dnew U Ug : list (Z * Z)) (kname : list Z).

#[local] Abbreviation klen := (Z.of_nat (length kname)).
#[local] Abbreviation MR1 := (mrestrict (w_H W1) m1).
#[local] Abbreviation MR3 := (mrestrict (w_H W3) m3).
#[local] Abbreviation MR4 := (mrestrict (w_H W4) m4).
#[local] Abbreviation MR5 := (mrestrict (w_H W4) m5).
#[local] Abbreviation MR7 := (mrestrict (w_H W4) m7).
#[local] Abbreviation A1 := (ablocks B ly1 S1).
#[local] Abbreviation A3 := (ablocks B ly3 S3).
#[local] Abbreviation A4 := (ablocks B ly4 S4).
#[local] Abbreviation OS := (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap).
#[local] Abbreviation NS := (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap').
#[local] Abbreviation Do := (NS ++ Di ++ (a, Z.of_nat (length kname) + 1) :: Dw).
#[local] Abbreviation FPg := ([(o + 24, o + 40); (o + 48, o + 56)] ++ ablocks_fp (rd_hblocks OS) ++ FS_PSTAT_FP).

(* pj_set_spec's entry premises, carried to m1 (pj_get's return) *)
Hypothesis HTo : rtree tfibsegs B ly1 S1 W1 m1 o (PjTree.JObj ms) D.
Hypothesis HPo : pobj tfibsegs B ly1 S1 W1 m1 o.
Hypothesis HTw : rtree tfibsegs B ly1 S1 W1 m1 w tv Dw.
Hypothesis HPw : pobj tfibsegs B ly1 S1 W1 m1 w.
Hypothesis HDwD : forall bk, In bk Dw -> ~ In bk D.
Hypothesis HwD : forall x, w <= x < w + 56 -> ~ PjStruct.pj_foot o D x.
Hypothesis HDwo : PjStruct.pj_apart Dw o.
Hypothesis Hkfoot : forall x, k <= x < k + klen + 1 -> ~ PjStruct.pj_foot o D x /\ ~ PjStruct.pj_foot w Dw x.
Hypothesis Hkey : ~ In kname (map fst ms).
Hypothesis Hheads : incl (rd_heads OS) U.
Hypothesis HKk : cstr_kept B ly1 S1 U k kname.
Hypothesis HAR1 : AR tfibsegs B ly1 S1 W1 mx1 md1.
(* grow's return (m3) *)
Hypothesis Hgr : grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug.
Hypothesis Hgperm : Permutation (A3 ++ rd_hblocks Dold) (A1 ++ rd_hblocks Dnew).
Hypothesis HHo3 : PjStruct.pj_hdr tfibsegs MR3 o 6 num str k' y' n cap'.
Hypothesis Hsl3 : PjStruct.pj_slots_at (fun a0 kk => In (a0, kk) NS) 6 k' y' n cap'.
Hypothesis Hbo3 : rd_blocks_ok tfibsegs B ly3 S3 W3 m3 NS.
Hypothesis Hmvk : rd_moved tfibsegs W1 W3 m1 m3 kids k' (56 * cap).
Hypothesis Hmvy : rd_moved tfibsegs W1 W3 m1 m3 keys y' (8 * cap).
Hypothesis Hkeptg : forall x, ~ inFP FPg x ->
  ((exists p nn, In (p, nn) A1 /\ p <= x < p + req_size nn) \/
   (exists cid pos, In (cid, pos) (frames S1) /\
      frame_addr ly1 cid pos <= x < frame_addr ly1 cid pos + fs_frame_bytes cid)) ->
  MR3 (Z_to_bv 64 x) = MR1 (Z_to_bv 64 x).
Hypothesis Hfr3 : frames S3 = frames S1.
Hypothesis Hfa3 : forall cid pos, frame_addr ly3 cid pos = frame_addr ly1 cid pos.
(* fuzz_strdup's return (m4) *)
Hypothesis Hab4 : A4 = A3 ++ [(a - HEAD, klen + 1 + HEAD)].
Hypothesis Hrb4 : fs_rblock tfibsegs B ly4 S4 W4 m4 a (klen + 1).
Hypothesis Hzb4 : zbytes_at tfibsegs W4 m4 a (kname ++ [0]).
Hypothesis Hkepts : forall x, ~ inFP FS_PSTAT_FP x ->
  ((exists p nn, In (p, nn) A3 /\ p <= x < p + req_size nn) \/
   (exists cid pos, In (cid, pos) (frames S3) /\
      frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid)) ->
  MR4 (Z_to_bv 64 x) = MR3 (Z_to_bv 64 x).
Hypothesis Hfr4 : frames S4 = frames S1.
Hypothesis Hfa4 : forall cid pos, frame_addr ly4 cid pos = frame_addr ly1 cid pos.
Hypothesis HAR4 : AR tfibsegs B ly4 S4 W4 mx4 md4.
Hypothesis HPo4 : pobj tfibsegs B ly4 S4 W4 m4 o.
Hypothesis HPw4 : pobj tfibsegs B ly4 S4 W4 m4 w.
Hypothesis HK4 : cstr_ok tfibsegs W4 m4 k kname.
(* stage D's two stores (m5), __asan_memcpy (m6), __asan_memset (m7) *)
Hypothesis Hvs : val_mem tfibsegs MR5 (y' + 8 * n) 8 a.
Hypothesis Hv24 : val_mem tfibsegs MR5 (o + 24) 8 k'.
Hypothesis Hv32 : val_mem tfibsegs MR5 (o + 32) 8 y'.
Hypothesis Hv40 : val_mem tfibsegs MR5 (o + 40) 8 (n + 1).
Hypothesis Hv48 : val_mem tfibsegs MR5 (o + 48) 8 cap'.
Hypothesis Hgrow5 : forall x, 0 <= x < alloc_ceiling -> mbyte tfibsegs MR4 x <> None -> mbyte tfibsegs MR5 x <> None.
Hypothesis Hm5 : forall x, 0 <= x < alloc_ceiling -> ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
  m5 (Z_to_bv 64 x) = m4 (Z_to_bv 64 x).
Hypothesis Hcp6 : forall i, 0 <= i < 56 ->
  aview tfibsegs (w_H W4) m6 (k' + 56 * n + i) = aview tfibsegs (w_H W4) m5 (w + i).
Hypothesis Hm6 : forall x, 0 <= x < alloc_ceiling -> ~ (k' + 56 * n <= x < k' + 56 * n + 56) ->
  aview tfibsegs (w_H W4) m6 x = aview tfibsegs (w_H W4) m5 x.
Hypothesis Hz7 : forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m7 (w + i) = Some 0.
Hypothesis Hm7 : forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 56) ->
  aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m6 x.
(* obj opened at m1 (pj_set_shape.ps_node_open; pSf_post below derives these four) *)
Hypothesis HDi : D = parse_items_shape.pis_slots true kids keys cap ++ Di.
Hypothesis Hstr : str = 0.
Hypothesis Hn : n = Z.of_nat (length ms).
Hypothesis Hop : parse_items_shape.pis_open tfibsegs MR1 (fun a0 kk => In (a0, kk) D) o true num kids keys cap n
  (map snd ms) (map fst ms) Di.

(* ---- shapes and numbers ---- *)
Lemma P_slots_eq : parse_items_shape.pis_slots true kids keys cap = OS.
Proof. reflexivity. Qed.

Lemma P_len : Z.of_nat (length (map snd ms)) = n.
Proof. rewrite length_map. symmetry. exact Hn. Qed.

Lemma P_ncap : 0 <= n <= cap /\ cap <= 2 ^ 54.
Proof. pose proof Hop as (_ & _ & _ & (_ & Hc & _) & _). lia. Qed.

Lemma P_grow : (n < cap /\ k' = kids /\ y' = keys /\ cap' = cap /\ Dold = [] /\ Dnew = [] /\ Ug = U) \/
  (n = cap /\ cap' = ReaderRes.cap2 cap /\ Dold = OS /\ Dnew = [(k', 56 * cap'); (y', 8 * cap')]).
Proof.
destruct Hgr as [H|(E & Ec & Eo & _ & _ & _ & _ & En & _)]; [left; exact H|right].
split; [exact E|]. split; [exact Ec|]. split; [exact Eo|]. rewrite En. reflexivity.
Qed.

Lemma P_cap' : n < cap' /\ cap' <= 2 ^ 54.
Proof.
pose proof P_ncap as Hnc. pose proof Hsl3 as (_ & Hc & _).
destruct P_grow as [(H1 & _ & _ & E & _)|(E1 & E2 & _)].
- lia.
- rewrite E2 in Hc |- *. revert Hc. unfold ReaderRes.cap2. destruct (Z.eqb_spec cap 0); intros; lia.
Qed.

Lemma P_NS : NS = [(k', 56 * cap'); (y', 8 * cap')].
Proof.
pose proof P_cap' as Hc. pose proof P_ncap as Hnc. unfold ReaderRes.kids_blk, ReaderRes.keys_blk.
rewrite (proj2 (Z.eqb_neq cap' 0)) by lia. reflexivity.
Qed.

Lemma P_NSy_k : (y', 8 * cap') <> (k', 56 * cap').
Proof. pose proof P_cap'. pose proof P_ncap. intros E. injection E as _ E. lia. Qed.

Lemma P_inDi : forall e, In e Di -> In e D.
Proof. intros e He. rewrite HDi. apply in_or_app. right. exact He. Qed.

Lemma P_inOS : forall e, In e OS -> In e D.
Proof. intros e He. rewrite HDi, P_slots_eq. apply in_or_app. left. exact He. Qed.

Lemma P_ndDw : NoDup Dw.
Proof. destruct HTw as (HN & _). exact (fn_node_nodup _ _ _ _ _ _ HN). Qed.

Lemma P_old_notOS : forall e, In e (Di ++ Dw) -> ~ In e OS.
Proof.
intros e He Ho. apply in_app_or in He as [He|He].
- pose proof Hop as (ND & _). rewrite P_slots_eq in ND. exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ ND Ho He).
- exact (HDwD e He (P_inOS e Ho)).
Qed.

Lemma P_old_DDw : forall e, In e (Di ++ Dw) -> In e (D ++ Dw).
Proof.
intros e He. apply in_app_or in He as [He|He]; apply in_or_app; [left; exact (P_inDi e He) | right; exact He].
Qed.

(* the D / Dw blocks are reader blocks at m1 *)
Lemma P_hb_pos : forall e, In e (D ++ Dw) -> In (fn_hb e) A1 /\ fst e mod 16 = 0 /\ 0 < snd e /\
  val_mem tfibsegs MR1 (fst e - HEAD) 8 (snd e).
Proof.
intros [p kk] He. apply in_app_or in He as [He|He].
- destruct HTo as (_ & Hb & _). exact (Hb p kk He).
- destruct HTw as (_ & Hb & _). exact (Hb p kk He).
Qed.

(* ---- grow's freed (HO) and made (HN) blocks ---- *)
Lemma P_HO : forall q, In q (rd_hblocks Dold) -> exists e, In e OS /\ q = fn_hb e.
Proof.
intros q Hq. destruct P_grow as [(_ & _ & _ & _ & E & _)|(_ & _ & E & _)]; rewrite E in Hq.
- cbn in Hq. destruct Hq.
- unfold rd_hblocks in Hq. apply in_map_iff in Hq as (e & <- & He). exists e. split; [exact He | reflexivity].
Qed.

Lemma P_NScls : forall e, In e NS -> In e OS \/ In (fn_hb e) (rd_hblocks Dnew).
Proof.
intros e He. destruct P_grow as [(_ & E1 & E2 & E3 & _)|(_ & _ & _ & E)].
- left. rewrite <- E1, <- E2, <- E3. exact He.
- right. rewrite E. rewrite P_NS in He. exact (in_map fn_hb _ e He).
Qed.

Lemma P_nd4 : NoDup A4.
Proof. exact (fn_nodup_blocks ly4 S4 W4 mx4 md4 HAR4). Qed.

Lemma P_nd3 : NoDup A3.
Proof. pose proof P_nd4 as H. rewrite Hab4 in H. exact (parse_items_shape.pis_nodup_l _ _ _ H). Qed.

Lemma P_sd_new : ~ In (fn_hb (a, klen + 1)) A3.
Proof.
intros H. pose proof P_nd4 as N. rewrite Hab4 in N. apply (parse_items_shape.pis_nodup_app_disj _ _ _ _ N H).
left. reflexivity.
Qed.

Lemma P_sd_ne : forall e, In (fn_hb e) A3 -> e <> (a, klen + 1).
Proof. intros e H E. apply P_sd_new. rewrite <- E. exact H. Qed.

Lemma P_surv : forall q, In q A1 -> ~ In q (rd_hblocks Dold) -> In q A3 /\ ~ In q (rd_hblocks Dnew).
Proof. intros q H1 H0. exact (fn_surv _ _ _ _ q Hgperm P_nd3 H1 H0). Qed.

Lemma P_oldHO : forall e, In e (Di ++ Dw) -> ~ In (fn_hb e) (rd_hblocks Dold).
Proof.
intros e He Hq. destruct (P_HO _ Hq) as (e0 & H0 & E). apply fn_hb_inj in E. subst e0.
exact (P_old_notOS e He H0).
Qed.

Lemma P_old3 : forall e, In e (Di ++ Dw) -> In (fn_hb e) A3 /\ ~ In (fn_hb e) (rd_hblocks Dnew).
Proof.
intros e He. apply P_surv; [|exact (P_oldHO e He)].
exact (proj1 (P_hb_pos e (P_old_DDw e He))).
Qed.

Lemma P_NS3 : forall e, In e NS -> In (fn_hb e) A3.
Proof. intros [p kk] He. destruct (Hbo3 p kk He) as (Hin & _). exact Hin. Qed.

Lemma P_old_notNS : forall e, In e (Di ++ Dw) -> ~ In e NS.
Proof.
intros e He Hn'. destruct (P_NScls e Hn') as [Ho|Hq].
- exact (P_old_notOS e He Ho).
- exact (proj2 (P_old3 e He) Hq).
Qed.

(* ---- the new tree's blocks Do at fuzz_strdup's return ---- *)
Lemma P_Do4 : forall e, In e Do -> In (fn_hb e) A4 /\ fst e mod 16 = 0 /\ 0 < snd e.
Proof.
intros [p kk] He. rewrite Hab4. unfold fn_hb. cbn [fst snd].
apply in_app_or in He as [He|He].
- destruct (Hbo3 p kk He) as (Hin & Hal & Hk & _).
  split; [apply in_or_app; left; exact Hin | split; [exact Hal | exact Hk]].
- apply in_app_or in He as [He|He]; [|destruct He as [He|He]].
  + destruct (P_old3 (p, kk) (in_or_app _ _ _ (or_introl He))) as (Hin & _).
    destruct (P_hb_pos (p, kk) (in_or_app _ _ _ (or_introl (P_inDi _ He)))) as (_ & Hal & Hk & _).
    split; [apply in_or_app; left; exact Hin | split; [exact Hal | exact Hk]].
  + injection He as <- <-. destruct Hrb4 as (_ & Hal & Hk & _).
    split; [apply in_or_app; right; left; reflexivity | split; [exact Hal | exact Hk]].
  + destruct (P_old3 (p, kk) (in_or_app _ _ _ (or_intror He))) as (Hin & _).
    destruct (P_hb_pos (p, kk) (in_or_app _ _ _ (or_intror He))) as (_ & Hal & Hk & _).
    split; [apply in_or_app; left; exact Hin | split; [exact Hal | exact Hk]].
Qed.

Lemma P_NS_Do : forall e, In e NS -> In e Do.
Proof. intros e He. apply in_or_app. left. exact He. Qed.
Lemma P_old_Do : forall e, In e (Di ++ Dw) -> In e Do.
Proof.
intros e He. apply in_or_app. right. apply in_app_or in He as [He|He]; apply in_or_app;
  [left; exact He | right; right; exact He].
Qed.
Lemma P_sd_Do : In (a, klen + 1) Do.
Proof. apply in_or_app. right. apply in_or_app. right. left. reflexivity. Qed.
Lemma P_NSk_in : In (k', 56 * cap') Do.
Proof. apply in_or_app. left. rewrite P_NS. left. reflexivity. Qed.
Lemma P_NSy_in : In (y', 8 * cap') Do.
Proof. apply in_or_app. left. rewrite P_NS. right. left. reflexivity. Qed.

Lemma P_ndNS : NoDup NS.
Proof.
rewrite P_NS. pose proof P_NSy_k as Hne.
apply NoDup_ListNoDup.
apply List.NoDup_cons; [|apply List.NoDup_cons; [intros [] | apply List.NoDup_nil]].
intros [E|[]]. exact (Hne E).
Qed.

Lemma P_ndDo : NoDup Do.
Proof.
apply parse_items_shape.pis_nodup_app; [exact P_ndNS| |].
- apply parse_items_shape.pis_nodup_app.
  + pose proof Hop as (ND & _). exact (parse_items_shape.pis_nodup_r _ _ _ ND).
  + apply NoDup_ListNoDup. apply List.NoDup_cons; [|apply NoDup_ListNoDup; exact P_ndDw].
    intros Hin. apply (P_sd_ne (a, klen + 1)); [|reflexivity].
    exact (proj1 (P_old3 _ (in_or_app _ _ _ (or_intror Hin)))).
  + intros e He [E|He2].
    * apply (P_sd_ne e); [exact (proj1 (P_old3 e (in_or_app _ _ _ (or_introl He)))) | symmetry; exact E].
    * exact (HDwD e He2 (P_inDi e He)).
- intros e He He2. apply in_app_or in He2 as [He2|[E|He2]].
  + exact (P_old_notNS e (in_or_app _ _ _ (or_introl He2)) He).
  + apply (P_sd_ne e (P_NS3 e He)). symmetry. exact E.
  + exact (P_old_notNS e (in_or_app _ _ _ (or_intror He2)) He).
Qed.

(* two distinct blocks of Do are apart, head included *)
Lemma P_Do_disj : forall e1 e2 x, In e1 Do -> In e2 Do -> e1 <> e2 ->
  PjStruct.pj_holds (fn_hb e1) x -> PjStruct.pj_holds (fn_hb e2) x -> False.
Proof.
intros [p1 k1] [p2 k2] x H1 H2 Hne X1 X2.
destruct (P_Do4 _ H1) as (I1 & _ & K1). destruct (P_Do4 _ H2) as (I2 & _ & K2).
unfold fn_hb in I1, I2. cbn [fst snd] in I1, I2, K1, K2.
assert (Hne' : (p1 - HEAD, k1 + HEAD) <> (p2 - HEAD, k2 + HEAD)).
{ intros E. apply Hne. exact (fn_hb_inj (p1, k1) (p2, k2) E). }
pose proof (fn_sep_blocks _ _ _ _ _ _ _ _ _ HAR4 I1 I2 Hne') as Dj.
rewrite (fn_req_hb k1 K1), (fn_req_hb k2 K2) in Dj.
unfold zdisjoint, PjStruct.pj_holds, fn_hb in *. cbn [fst snd] in *. lia.
Qed.

Lemma P_Do_geo : forall e x, In e Do -> PjStruct.pj_holds (fn_hb e) x ->
  0 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros [p kk] x He Hh. destruct (P_Do4 _ He) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
unfold PjStruct.pj_holds, fn_hb in Hh. cbn [fst snd] in Hh.
assert (Hx : p - HEAD <= x < p - HEAD + req_size (kk + HEAD)) by (rewrite fn_req_hb by exact Hk; lia).
destruct (fsw_ablock_low B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as (L1 & L2 & _).
split; [lia|]. split; [exact (fn_blk_img ly4 S4 W4 mx4 md4 _ _ x HAR4 I4 Hx)|].
split; [apply fn_pstat_off; exact (fn_blk_off ly4 S4 W4 mx4 md4 _ _ x HAR4 I4 Hx)|].
exact (fsw_ablock_off_shadow B ly4 S4 W4 mx4 md4 _ _ HAR4 I4 x Hx).
Qed.

(* ---- the two objects: placed at m1, they lie apart from every block of Do (and from D / Dw at m1) ---- *)
Lemma P_objhome : forall v, pobj tfibsegs B ly1 S1 W1 m1 v ->
  (forall e x, In e (D ++ Dw) -> v <= x < v + 56 -> ~ PjStruct.pj_holds e x) ->
  (forall e x, In e (D ++ Dw) -> v <= x < v + 56 -> ~ PjStruct.pj_holds (fn_hb e) x) /\
  (forall x, v <= x < v + 56 -> fn_hm ly3 S3 x) /\
  (forall e x, In e Do -> v <= x < v + 56 -> ~ PjStruct.pj_holds (fn_hb e) x).
Proof.
intros v HP Hap.
assert (NOT : forall e b mm, In e (D ++ Dw) -> fn_hb e = (b, mm) -> b + HEAD <= v -> v + 56 <= b + req_size mm -> False).
{ intros [p kk] b mm He E B1 B2. destruct (P_hb_pos _ He) as (_ & _ & Hk & _). unfold fn_hb in E. cbn [fst snd] in E, Hk.
  injection E as E1 E2. rewrite <- E2 in B2. rewrite fn_req_hb in B2 by exact Hk.
  apply (Hap (p, kk) v He); [lia|]. unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
pose proof HP as ([HF|(HB & _)] & _).
- destruct HF as ((cid & pos & Hin & _ & _ & F1 & F2) & _).
  split; [|split].
  + intros [p kk] x He Hx Hh. destruct (P_hb_pos _ He) as (I1 & _ & Hk & _). unfold fn_hb in I1. cbn [fst snd] in I1, Hk.
    pose proof (fn_sep_bf ly1 S1 W1 mx1 md1 (p - HEAD) (kk + HEAD) cid pos HAR1 I1 Hin) as Dj.
    rewrite fn_req_hb in Dj by exact Hk. unfold zdisjoint, PjStruct.pj_holds, fn_hb in *. cbn [fst snd] in *. lia.
  + intros x Hx. right. exists cid, pos. rewrite Hfr3, Hfa3. split; [exact Hin | lia].
  + intros [p kk] x He Hx Hh. destruct (P_Do4 _ He) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
    assert (Hin4 : In (cid, pos) (frames S4)) by (rewrite Hfr4; exact Hin).
    pose proof (fn_sep_bf ly4 S4 W4 mx4 md4 (p - HEAD) (kk + HEAD) cid pos HAR4 I4 Hin4) as Dj.
    rewrite Hfa4, fn_req_hb in Dj by exact Hk. unfold zdisjoint, PjStruct.pj_holds, fn_hb in *. cbn [fst snd] in *. lia.
- destruct HB as (b & mm & Hin & B1 & B2).
  assert (NOTO : ~ In (b, mm) (rd_hblocks Dold)).
  { intros Hq. destruct (P_HO _ Hq) as (e0 & H0 & E0).
    exact (NOT e0 b mm (in_or_app _ _ _ (or_introl (P_inOS e0 H0))) (eq_sym E0) B1 B2). }
  destruct (P_surv _ Hin NOTO) as (I3 & NHN).
  assert (Hb4 : In (b, mm) A4) by (rewrite Hab4; apply in_or_app; left; exact I3).
  split; [|split].
  + intros [p kk] x He Hx Hh. destruct (P_hb_pos _ He) as (I1 & _ & Hk & _). unfold fn_hb in I1. cbn [fst snd] in I1, Hk.
    destruct (fn_zz_dec (p - HEAD, kk + HEAD) (b, mm)) as [E|E].
    * exact (NOT (p, kk) b mm He E B1 B2).
    * pose proof (fn_sep_blocks ly1 S1 W1 mx1 md1 _ _ _ _ HAR1 I1 Hin E) as Dj. rewrite fn_req_hb in Dj by exact Hk.
      unfold zdisjoint, PjStruct.pj_holds, fn_hb, HEAD in *. cbn [fst snd] in *. lia.
  + intros x Hx. left. exists b, mm. split; [exact I3 | unfold HEAD in B1; lia].
  + intros [p kk] x He Hx Hh. destruct (P_Do4 _ He) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
    destruct (fn_zz_dec (p - HEAD, kk + HEAD) (b, mm)) as [E|E].
    * exfalso. apply in_app_or in He as [He|He].
      -- destruct (P_NScls _ He) as [Ho|Hn'].
         ++ exact (NOT (p, kk) b mm (in_or_app _ _ _ (or_introl (P_inOS _ Ho))) E B1 B2).
         ++ apply NHN. rewrite <- E. exact Hn'.
      -- apply in_app_or in He as [He|[He|He]].
         ++ exact (NOT (p, kk) b mm (in_or_app _ _ _ (or_introl (P_inDi _ He))) E B1 B2).
         ++ injection He as <- <-. apply P_sd_new. unfold fn_hb. cbn [fst snd]. rewrite E. exact I3.
         ++ exact (NOT (p, kk) b mm (in_or_app _ _ _ (or_intror He)) E B1 B2).
    * pose proof (fn_sep_blocks ly4 S4 W4 mx4 md4 _ _ _ _ HAR4 I4 Hb4 E) as Dj. rewrite fn_req_hb in Dj by exact Hk.
      unfold zdisjoint, PjStruct.pj_holds, fn_hb, HEAD in *. cbn [fst snd] in *. lia.
Qed.

Lemma P_o_ap : forall e x, In e (D ++ Dw) -> o <= x < o + 56 -> ~ PjStruct.pj_holds e x.
Proof.
intros e x He Hx Hh. apply in_app_or in He as [He|He].
- pose proof Hop as (_ & HA & _). rewrite HDi in He. exact (HA e x He Hh Hx).
- exact (HDwo e x He Hh Hx).
Qed.

Lemma P_w_ap : forall e x, In e (D ++ Dw) -> w <= x < w + 56 -> ~ PjStruct.pj_holds e x.
Proof.
intros e x He Hx Hh. apply in_app_or in He as [He|He].
- apply (HwD x Hx). right. exists e. split; [exact He | exact Hh].
- destruct HTw as (HN & _). exact (parse_items_shape.pis_node_apart tfibsegs _ _ _ _ _ HN e x He Hh Hx).
Qed.

Lemma P_o1 : forall e x, In e (D ++ Dw) -> o <= x < o + 56 -> ~ PjStruct.pj_holds (fn_hb e) x.
Proof. exact (proj1 (P_objhome o HPo P_o_ap)). Qed.
Lemma P_o3 : forall x, o <= x < o + 56 -> fn_hm ly3 S3 x.
Proof. exact (proj1 (proj2 (P_objhome o HPo P_o_ap))). Qed.
Lemma P_o4 : forall e x, In e Do -> o <= x < o + 56 -> ~ PjStruct.pj_holds (fn_hb e) x.
Proof. exact (proj2 (proj2 (P_objhome o HPo P_o_ap))). Qed.
Lemma P_w1 : forall e x, In e (D ++ Dw) -> w <= x < w + 56 -> ~ PjStruct.pj_holds (fn_hb e) x.
Proof. exact (proj1 (P_objhome w HPw P_w_ap)). Qed.
Lemma P_w3 : forall x, w <= x < w + 56 -> fn_hm ly3 S3 x.
Proof. exact (proj1 (proj2 (P_objhome w HPw P_w_ap))). Qed.
Lemma P_w4 : forall e x, In e Do -> w <= x < w + 56 -> ~ PjStruct.pj_holds (fn_hb e) x.
Proof. exact (proj2 (proj2 (P_objhome w HPw P_w_ap))). Qed.

Lemma P_o_geo : forall x, o <= x < o + 56 ->
  0 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros x Hx. destruct (fsw_pobj_low B ly4 S4 W4 mx4 md4 m4 o HAR4 HPo4) as (L1 & L2).
split; [lia|]. split; [exact (fn_pobj_img ly4 S4 W4 mx4 md4 m4 o HAR4 HPo4 x Hx)|].
split; [apply fn_pstat_off; destruct (fsw_pobj_off_img B ly4 S4 W4 mx4 md4 m4 o HAR4 HPo4); lia|].
exact (fsw_pobj_off_shadow B ly4 S4 W4 mx4 md4 m4 o HAR4 HPo4 x Hx).
Qed.

Lemma P_w_geo : forall x, w <= x < w + 56 ->
  0 <= x < alloc_ceiling /\ ~ in_img tfibsegs x /\ ~ inFP FS_PSTAT_FP x /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44).
Proof.
intros x Hx. destruct (fsw_pobj_low B ly4 S4 W4 mx4 md4 m4 w HAR4 HPw4) as (L1 & L2).
split; [lia|]. split; [exact (fn_pobj_img ly4 S4 W4 mx4 md4 m4 w HAR4 HPw4 x Hx)|].
split; [apply fn_pstat_off; destruct (fsw_pobj_off_img B ly4 S4 W4 mx4 md4 m4 w HAR4 HPw4); lia|].
exact (fsw_pobj_off_shadow B ly4 S4 W4 mx4 md4 m4 w HAR4 HPw4 x Hx).
Qed.

(* the slot obj->keys[n] and the new kid obj->kids[n] lie in the new keys / kids blocks *)
Lemma P_S_hb : forall x, y' + 8 * n <= x < y' + 8 * n + 8 -> PjStruct.pj_holds (y', 8 * cap') x.
Proof. intros x Hx. pose proof P_cap'. pose proof P_ncap. unfold PjStruct.pj_holds. cbn [fst snd]. lia. Qed.
Lemma P_K_hb : forall x, k' + 56 * n <= x < k' + 56 * n + 56 -> PjStruct.pj_holds (k', 56 * cap') x.
Proof. intros x Hx. pose proof P_cap'. pose proof P_ncap. unfold PjStruct.pj_holds. cbn [fst snd]. lia. Qed.

Lemma P_nS_hb : forall e x, In e Do -> PjStruct.pj_holds (fn_hb e) x -> e <> (y', 8 * cap') ->
  ~ (y' + 8 * n <= x < y' + 8 * n + 8).
Proof.
intros e x He Hh Hne Hs. apply (P_Do_disj e (y', 8 * cap') x He P_NSy_in Hne Hh).
apply fn_holds_hb. exact (P_S_hb x Hs).
Qed.
Lemma P_nK_hb : forall e x, In e Do -> PjStruct.pj_holds (fn_hb e) x -> e <> (k', 56 * cap') ->
  ~ (k' + 56 * n <= x < k' + 56 * n + 56).
Proof.
intros e x He Hh Hne Hs. apply (P_Do_disj e (k', 56 * cap') x He P_NSk_in Hne Hh).
apply fn_holds_hb. exact (P_K_hb x Hs).
Qed.
Lemma P_nO_hb : forall e x, In e Do -> PjStruct.pj_holds (fn_hb e) x -> ~ (o + 24 <= x < o + 56).
Proof. intros e x He Hh Ho. apply (P_o4 e x He); [lia | exact Hh]. Qed.
Lemma P_nW_hb : forall e x, In e Do -> PjStruct.pj_holds (fn_hb e) x -> ~ (w <= x < w + 56).
Proof. intros e x He Hh Hw. exact (P_w4 e x He Hw Hh). Qed.

(* the key's bytes are apart from the new kids / keys blocks *)
Lemma P_str_NS : forall e x, In e NS -> k <= x < k + klen + 1 -> ~ PjStruct.pj_holds e x.
Proof.
intros [p kk] x He Hx Hh. destruct (P_NScls _ He) as [Ho|Hq].
- destruct (Hkfoot x Hx) as (F & _). apply F. right. exists (p, kk). split; [exact (P_inOS _ Ho) | exact Hh].
- destruct (P_Do4 (p, kk) (P_NS_Do _ He)) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
  unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
  destruct HKk as [(b & mm & Hin & K1 & K2 & Kav)|[Hro|(ps & Hfm & El)]].
  + assert (NOTO : ~ In (b, mm) (rd_hblocks Dold)).
    { intros Hq0. destruct (P_HO _ Hq0) as ([p0 k0] & H0 & E0). unfold fn_hb in E0. cbn [fst snd] in E0. injection E0 as Eb Em.
      pose proof (Hheads (p0 - HEAD, HEAD) (in_map (fun b0 : Z * Z => (fst b0 - HEAD, HEAD)) OS (p0, k0) H0)) as Hu.
      destruct (Kav _ Hu) as [Q|Q]; cbn [fst snd] in Q.
      - lia.
      - destruct (Hkfoot k ltac:(lia)) as (F & _). apply F. right. exists (p0, k0). split; [exact (P_inOS _ H0)|].
        unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
    destruct (P_surv _ Hin NOTO) as (I3 & NHN).
    assert (Hne : (p - HEAD, kk + HEAD) <> (b, mm)) by (intros E; apply NHN; rewrite <- E; exact Hq).
    assert (Hb4 : In (b, mm) A4) by (rewrite Hab4; apply in_or_app; left; exact I3).
    pose proof (fn_sep_blocks ly4 S4 W4 mx4 md4 _ _ _ _ HAR4 I4 Hb4 Hne) as Dj.
    rewrite fn_req_hb in Dj by exact Hk. pose proof (req_size_pos mm ltac:(lia)) as (_ & Rm).
    unfold zdisjoint, HEAD in *. cbn [fst snd] in Dj. lia.
  + destruct (fn_ro_range _ _ Hro) as (R1 & R2).
    pose proof (fsw_ablock_off_img B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as Q. rewrite fn_req_hb in Q by exact Hk.
    unfold HEAD in *. lia.
  + rewrite El in Hx. destruct (fn_fmt_range _ _ Hfm) as (R1 & R2).
    pose proof (fsw_ablock_off_img B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as Q. rewrite fn_req_hb in Q by exact Hk.
    unfold HEAD in *. lia.
Qed.

(* ---- the memory chain m1 -> m3 -> m4 -> m7 ---- *)
Lemma P_T47 : forall x, 0 <= x < alloc_ceiling -> ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
  ~ (k' + 56 * n <= x < k' + 56 * n + 56) -> ~ (w <= x < w + 56) ->
  aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m4 x.
Proof.
intros x Hx H1 H2 H3 H4. rewrite (Hm7 x Hx H4), (Hm6 x Hx H3).
unfold aview, mbyte, mrestrict. rewrite (Hm5 x Hx H1 H2). reflexivity.
Qed.

Lemma P_C47 : forall x, 0 <= x < alloc_ceiling -> ~ in_img tfibsegs x ->
  ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
  ~ (k' + 56 * n <= x < k' + 56 * n + 56) -> ~ (w <= x < w + 56) ->
  MR7 (Z_to_bv 64 x) = MR4 (Z_to_bv 64 x).
Proof.
intros x Hx Hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _).
apply (fsw_restrict_of_aview (w_H W4) (w_H W4) m4 m7 x); [lia | exact Hi | exact (P_T47 x Hx H1 H2 H3 H4)].
Qed.

Lemma P_C37 : forall x, 0 <= x < alloc_ceiling -> ~ in_img tfibsegs x ->
  ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
  ~ (k' + 56 * n <= x < k' + 56 * n + 56) -> ~ (w <= x < w + 56) ->
  ~ inFP FS_PSTAT_FP x -> fn_hm ly3 S3 x ->
  MR7 (Z_to_bv 64 x) = MR3 (Z_to_bv 64 x).
Proof.
intros x Hx Hi H1 H2 H3 H4 Hst H3h. rewrite (P_C47 x Hx Hi H1 H2 H3 H4). exact (Hkepts x Hst H3h).
Qed.

Lemma P_C17 : forall x, 0 <= x < alloc_ceiling -> ~ in_img tfibsegs x ->
  ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
  ~ (k' + 56 * n <= x < k' + 56 * n + 56) -> ~ (w <= x < w + 56) ->
  ~ inFP FS_PSTAT_FP x -> fn_hm ly3 S3 x -> fn_hm ly1 S1 x -> ~ inFP FPg x ->
  MR7 (Z_to_bv 64 x) = MR1 (Z_to_bv 64 x).
Proof.
intros x Hx Hi H1 H2 H3 H4 Hst H3h H1h Hfp. rewrite (P_C37 x Hx Hi H1 H2 H3 H4 Hst H3h). exact (Hkeptg x Hfp H1h).
Qed.

(* the D / Dw blocks are off grow's footprint *)
Lemma P_FPg_old : forall e x, In e (Di ++ Dw) -> PjStruct.pj_holds (fn_hb e) x -> ~ inFP FPg x.
Proof.
intros e x He Hh (r & Hr & Hx).
apply in_app_or in Hr as [Hr|Hr]; [|apply in_app_or in Hr as [Hr|Hr]].
- assert (Ho : o <= x < o + 56) by (destruct Hr as [E|[E|[]]]; subst r; cbn [fst snd] in Hx; lia).
  exact (P_o1 e x (P_old_DDw e He) Ho Hh).
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as (q & <- & Hq). unfold rd_hblocks in Hq.
  apply in_map_iff in Hq as (e0 & <- & H0). cbn [fst snd] in Hx.
  destruct e as [p kk], e0 as [p0 k0].
  destruct (P_hb_pos (p, kk) (P_old_DDw _ He)) as (I1 & _ & Hk & _).
  destruct (P_hb_pos (p0, k0) (in_or_app _ _ _ (or_introl (P_inOS _ H0)))) as (I0 & _ & Hk0 & _).
  unfold fn_hb in I1, I0. cbn [fst snd] in I1, I0, Hk, Hk0, Hx.
  assert (Hne : (p - HEAD, kk + HEAD) <> (p0 - HEAD, k0 + HEAD)).
  { intros E. pose proof (fn_hb_inj (p, kk) (p0, k0) E) as E'. rewrite E' in He. exact (P_old_notOS _ He H0). }
  pose proof (fn_sep_blocks ly1 S1 W1 mx1 md1 _ _ _ _ HAR1 I1 I0 Hne) as Dj.
  rewrite (fn_req_hb kk Hk), (fn_req_hb k0 Hk0) in Dj. rewrite (fn_req_hb k0 Hk0) in Hx.
  unfold zdisjoint, PjStruct.pj_holds, fn_hb in *. cbn [fst snd] in *. lia.
- destruct (P_Do_geo e x (P_old_Do e He) Hh) as (_ & _ & St & _). exact (St (ex_intro _ r (conj Hr Hx))).
Qed.

Lemma P_old_bytes : forall e x, In e (Di ++ Dw) -> PjStruct.pj_holds (fn_hb e) x ->
  MR7 (Z_to_bv 64 x) = MR1 (Z_to_bv 64 x).
Proof.
intros e x He Hh. pose proof (P_old_Do e He) as HeDo.
destruct (P_Do_geo e x HeDo Hh) as (Hx & Hi & Hst & _).
pose proof (P_old_notNS e He) as NNS.
apply P_C17; [exact Hx | exact Hi | | exact (P_nO_hb e x HeDo Hh) | | exact (P_nW_hb e x HeDo Hh) | exact Hst | | |
  exact (P_FPg_old e x He Hh)].
- apply (P_nS_hb e x HeDo Hh). intros E. apply NNS. rewrite E, P_NS. right. left. reflexivity.
- apply (P_nK_hb e x HeDo Hh). intros E. apply NNS. rewrite E, P_NS. left. reflexivity.
- left. destruct e as [p kk]. exists (p - HEAD), (kk + HEAD). destruct (P_old3 _ He) as (I3 & _). split; [exact I3|].
  destruct (P_hb_pos _ (P_old_DDw _ He)) as (_ & _ & Hk & _). cbn [fst snd] in Hk. rewrite fn_req_hb by exact Hk.
  unfold PjStruct.pj_holds, fn_hb in Hh. cbn [fst snd] in Hh. lia.
- left. destruct e as [p kk]. exists (p - HEAD), (kk + HEAD).
  destruct (P_hb_pos _ (P_old_DDw _ He)) as (I1 & _ & Hk & _). split; [exact I1|]. cbn [fst snd] in Hk.
  rewrite fn_req_hb by exact Hk. unfold PjStruct.pj_holds, fn_hb in Hh. cbn [fst snd] in Hh. lia.
Qed.

Lemma P_ns_bytes : forall e x, In e NS -> PjStruct.pj_holds (fn_hb e) x ->
  (e = (y', 8 * cap') -> x < y' + 8 * n) -> (e = (k', 56 * cap') -> x < k' + 56 * n) ->
  MR7 (Z_to_bv 64 x) = MR3 (Z_to_bv 64 x).
Proof.
intros e x He Hh Hy Hk. pose proof (P_NS_Do e He) as HeDo.
destruct (P_Do_geo e x HeDo Hh) as (Hx & Hi & Hst & _).
apply P_C37; [exact Hx | exact Hi | | exact (P_nO_hb e x HeDo Hh) | | exact (P_nW_hb e x HeDo Hh) | exact Hst |].
- intros Hs. destruct (fn_zz_dec e (y', 8 * cap')) as [E|E]; [specialize (Hy E); lia|].
  exact (P_nS_hb e x HeDo Hh E Hs).
- intros Hs. destruct (fn_zz_dec e (k', 56 * cap')) as [E|E]; [specialize (Hk E); lia|].
  exact (P_nK_hb e x HeDo Hh E Hs).
- left. destruct e as [p kk]. exists (p - HEAD), (kk + HEAD). split; [exact (P_NS3 _ He)|].
  destruct (P_Do4 _ HeDo) as (_ & _ & Hk0). cbn [fst snd] in Hk0. rewrite fn_req_hb by exact Hk0.
  unfold PjStruct.pj_holds, fn_hb in Hh. cbn [fst snd] in Hh. lia.
Qed.

Lemma P_sd_bytes : forall x, PjStruct.pj_holds (fn_hb (a, klen + 1)) x -> MR7 (Z_to_bv 64 x) = MR4 (Z_to_bv 64 x).
Proof.
intros x Hh. destruct (P_Do_geo _ x P_sd_Do Hh) as (Hx & Hi & _).
apply P_C47; [exact Hx | exact Hi | | exact (P_nO_hb _ x P_sd_Do Hh) | | exact (P_nW_hb _ x P_sd_Do Hh)].
- apply (P_nS_hb _ x P_sd_Do Hh). intros E. apply (P_sd_ne (y', 8 * cap')); [|symmetry; exact E].
  apply P_NS3. rewrite P_NS. right. left. reflexivity.
- apply (P_nK_hb _ x P_sd_Do Hh). intros E. apply (P_sd_ne (k', 56 * cap')); [|symmetry; exact E].
  apply P_NS3. rewrite P_NS. left. reflexivity.
Qed.

(* obj's first 24 bytes (type, num, str) are grow's; its last 32 are stage D's stores *)
Lemma P_o_low : forall x, o <= x < o + 24 -> MR7 (Z_to_bv 64 x) = MR3 (Z_to_bv 64 x).
Proof.
intros x Hx. destruct (P_o_geo x ltac:(lia)) as (Hc & Hi & Hst & _).
apply P_C37; [exact Hc | exact Hi | | lia | | | exact Hst | exact (P_o3 x ltac:(lia))].
- intros Hs. apply (P_o4 _ x P_NSy_in ltac:(lia)). apply fn_holds_hb. exact (P_S_hb x Hs).
- intros Hs. apply (P_o4 _ x P_NSk_in ltac:(lia)). apply fn_holds_hb. exact (P_K_hb x Hs).
- intros Hw. apply (HwD x Hw). left. lia.
Qed.

Lemma P_o_hi : forall x, o + 24 <= x < o + 56 -> mbyte tfibsegs MR7 x = mbyte tfibsegs MR5 x.
Proof.
intros x Hx. destruct (P_o_geo x ltac:(lia)) as (Hc & _).
apply (YCbq.mbyte_of_aview tfibsegs (w_H W4) (w_H W4) m5 m7 x).
rewrite (Hm7 x Hc), (Hm6 x Hc); [reflexivity| |].
- intros Hs. apply (P_o4 _ x P_NSk_in ltac:(lia)). apply fn_holds_hb. exact (P_K_hb x Hs).
- intros Hw. apply (HwD x Hw). left. lia.
Qed.

(* val's 56 bytes, kept from m1 to m4 *)
Lemma P_FPg_w : forall x, w <= x < w + 56 -> ~ inFP FPg x.
Proof.
intros x Hx (r & Hr & Hxr). apply in_app_or in Hr as [Hr|Hr]; [|apply in_app_or in Hr as [Hr|Hr]].
- apply (HwD x Hx). left. destruct Hr as [E|[E|[]]]; subst r; cbn [fst snd] in Hxr; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as (q & <- & Hq). unfold rd_hblocks in Hq.
  apply in_map_iff in Hq as (e0 & <- & H0). destruct e0 as [p0 k0]. cbn [fst snd] in Hxr.
  pose proof (in_or_app D Dw (p0, k0) (or_introl (P_inOS _ H0))) as HD0.
  destruct (P_hb_pos (p0, k0) HD0) as (_ & _ & Hk & _). cbn [fst snd] in Hk.
  rewrite fn_req_hb in Hxr by exact Hk.
  apply (P_w1 (p0, k0) x HD0 Hx). unfold PjStruct.pj_holds, fn_hb. cbn [fst snd]. lia.
- destruct (P_w_geo x Hx) as (_ & _ & St & _). exact (St (ex_intro _ r (conj Hr Hxr))).
Qed.

Lemma P_w14 : forall x, w <= x < w + 56 -> MR4 (Z_to_bv 64 x) = MR1 (Z_to_bv 64 x).
Proof.
intros x Hx. destruct (P_w_geo x Hx) as (_ & _ & St & _).
rewrite (Hkepts x St (P_w3 x Hx)). exact (Hkeptg x (P_FPg_w x Hx) (fn_pobj_hm ly1 S1 W1 m1 w HPw x Hx)).
Qed.

Lemma P_w5 : forall x, w <= x < w + 56 -> aview tfibsegs (w_H W4) m5 x = aview tfibsegs (w_H W4) m4 x.
Proof.
intros x Hx. destruct (P_w_geo x Hx) as (Hc & _).
unfold aview, mbyte, mrestrict. rewrite (Hm5 x Hc); [reflexivity| |].
- intros Hs. apply (P_w4 _ x P_NSy_in Hx). apply fn_holds_hb. exact (P_S_hb x Hs).
- intros Ho. apply (HwD x Hx). left. lia.
Qed.

Lemma P_w_present : forall x, w <= x < w + 56 -> mbyte tfibsegs MR1 x <> None.
Proof.
intros x Hx. destruct HTw as (HN & _).
pose proof (parse_items_shape.pis_node_rw tfibsegs _ _ _ _ _ HN) as (_ & (_ & _ & Hst)).
destruct (Hst x Hx) as (_ & b & Hb). assert (Hb' : mbyte tfibsegs MR1 x = Some b) by exact Hb.
rewrite Hb'. discriminate.
Qed.

Lemma P_w5_some : forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m5 (w + i) <> None.
Proof.
intros i Hi. rewrite (P_w5 (w + i) ltac:(lia)). intros E. apply fn_aview_none in E.
rewrite (fn_mbyte_eq _ _ _ (P_w14 (w + i) ltac:(lia))) in E. exact (P_w_present (w + i) ltac:(lia) E).
Qed.

(* the new kid obj->kids[n] holds val's 56 bytes at m7 *)
Lemma P_kid7 : forall i, 0 <= i < 56 -> mbyte tfibsegs MR7 (k' + 56 * n + i) = mbyte tfibsegs MR1 (w + i).
Proof.
intros i Hi.
assert (Hh : PjStruct.pj_holds (fn_hb (k', 56 * cap')) (k' + 56 * n + i))
  by (apply fn_holds_hb; apply P_K_hb; lia).
destruct (P_Do_geo _ _ P_NSk_in Hh) as (Hc & _).
rewrite <- (fn_mbyte_eq _ _ _ (P_w14 (w + i) ltac:(lia))).
apply fn_mbyte_of_aview2.
rewrite (Hm7 _ Hc (P_nW_hb _ _ P_NSk_in Hh)), (Hcp6 i Hi). exact (P_w5 (w + i) ltac:(lia)).
Qed.

(* the slot obj->keys[n] *)
Lemma P_slot7 : forall x, y' + 8 * n <= x < y' + 8 * n + 8 -> aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m5 x.
Proof.
intros x Hx. assert (Hh : PjStruct.pj_holds (fn_hb (y', 8 * cap')) x) by (apply fn_holds_hb; exact (P_S_hb x Hx)).
destruct (P_Do_geo _ _ P_NSy_in Hh) as (Hc & _).
rewrite (Hm7 x Hc (P_nW_hb _ _ P_NSy_in Hh)). apply Hm6; [exact Hc|].
exact (P_nK_hb _ _ P_NSy_in Hh P_NSy_k).
Qed.

(* any byte below the ceiling visible at m4 is visible at m7 *)
Lemma P_vis : forall x, 0 <= x < alloc_ceiling -> aview tfibsegs (w_H W4) m4 x <> None ->
  aview tfibsegs (w_H W4) m7 x <> None.
Proof.
intros x Hx H4.
assert (V5 : aview tfibsegs (w_H W4) m5 x <> None).
{ intros E. apply (Hgrow5 x Hx).
  - intros E4. apply H4. apply fn_aview_none. exact E4.
  - apply fn_aview_none. exact E. }
assert (V6 : aview tfibsegs (w_H W4) m6 x <> None).
{ destruct (Z_lt_dec x (k' + 56 * n)) as [K1|K1]; [rewrite (Hm6 x Hx ltac:(lia)); exact V5|].
  destruct (Z_lt_dec x (k' + 56 * n + 56)) as [K2|K2]; [|rewrite (Hm6 x Hx ltac:(lia)); exact V5].
  replace x with (k' + 56 * n + (x - (k' + 56 * n))) by lia.
  rewrite (Hcp6 (x - (k' + 56 * n)) ltac:(lia)). apply P_w5_some. lia. }
destruct (Z_lt_dec x w) as [L1|L1]; [rewrite (Hm7 x Hx ltac:(lia)); exact V6|].
destruct (Z_lt_dec x (w + 56)) as [L2|L2]; [|rewrite (Hm7 x Hx ltac:(lia)); exact V6].
replace x with (w + (x - w)) by lia. rewrite (Hz7 (x - w) ltac:(lia)). discriminate.
Qed.

(* a shadow byte below the ceiling is none of the written bytes *)
Lemma P_shadow_kept : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> 0 <= s < alloc_ceiling ->
  aview tfibsegs (w_H W4) m7 s = aview tfibsegs (w_H W4) m4 s.
Proof.
intros s Hs Hc. apply P_T47; [exact Hc | | | | ].
- intros Hx. destruct (P_Do_geo _ s P_NSy_in (fn_holds_hb _ _ (P_S_hb s Hx))) as (_ & _ & _ & Sh). exact (Sh Hs).
- intros Hx. destruct (P_o_geo s ltac:(lia)) as (_ & _ & _ & Sh). exact (Sh Hs).
- intros Hx. destruct (P_Do_geo _ s P_NSk_in (fn_holds_hb _ _ (P_K_hb s Hx))) as (_ & _ & _ & Sh). exact (Sh Hs).
- intros Hx. destruct (P_w_geo s Hx) as (_ & _ & _ & Sh). exact (Sh Hs).
Qed.

(* ================= the new tree ================= *)
Lemma P_kids_present : forall i, 0 <= i < 56 * n -> exists b, mbyte tfibsegs MR1 (kids + i) = Some b.
Proof.
intros i Hi. pose proof Hop as (_ & _ & _ & _ & _ & Hit). cbn [parse_items_shape.pis_items] in Hit.
destruct Hit as (_ & Hm). rewrite parse_items_shape.pis_combine_map in Hm.
assert (Q : 56 * (i / 56) <= i < 56 * (i / 56) + 56)
  by (pose proof (Z.mod_pos_bound i 56 ltac:(lia)); pose proof (Z.div_mod i 56 ltac:(lia)); lia).
assert (Hj : (Z.to_nat (i / 56) < length ms)%nat).
{ assert (0 <= i / 56) by (apply Z.div_pos; lia). rewrite Hn in Hi. lia. }
destruct (nth_error ms (Z.to_nat (i / 56))) as [[nm u]|] eqn:Ej; [|apply nth_error_None in Ej; lia].
destruct (pj_set_shape.ps_mems_split tfibsegs _ _ _ _ _ _ _ _ _ _ Hm Ej) as (Dpre & x & kk & Du & Dpost & _ & _ & _ & _ & HP & _).
pose proof (parse_items_shape.pis_node_rw tfibsegs _ _ _ _ _ HP) as (_ & (_ & _ & Hst)).
assert (Hr : kids + 56 * Z.of_nat (Z.to_nat (i / 56)) <= kids + i < kids + 56 * Z.of_nat (Z.to_nat (i / 56)) + 56).
{ rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
destruct (Hst (kids + i) Hr) as (_ & b & Hb). exists b. exact Hb.
Qed.

Lemma P_hdr7 : PjStruct.pj_hdr tfibsegs MR7 o 6 num 0 k' y' (n + 1) cap'.
Proof.
pose proof asan_consts as (C1 & _). pose proof P_cap' as Hc'. pose proof P_ncap as Hnc.
destruct (fsw_pobj_low B ly4 S4 W4 mx4 md4 m4 o HAR4 HPo4) as (L1 & L2).
pose proof HHo3 as (Hrw & Hty & Hnum & Hs & Hkd & Hky & _ & Hcp). rewrite Hstr in Hs.
assert (LOW : forall x, o <= x < o + 24 -> mbyte tfibsegs MR7 x = mbyte tfibsegs MR3 x)
  by (intros x Hx; exact (fn_mbyte_eq _ _ x (P_o_low x Hx))).
assert (HI : forall (off : Z) v, 24 <= off -> off + 8 <= 56 -> val_mem tfibsegs MR5 (o + off) 8 v ->
  val_mem tfibsegs MR7 (o + off) 8 v).
{ intros off v H1 H2 Hv. apply (fn_val_xfer _ _ _ _ _ Hv). intros j Hj. apply P_o_hi. lia. }
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- apply fn_rw; [exact (proj1 Hrw) | lia | lia|]. intros x Hx. split; [exact (proj1 (proj2 (P_o_geo x Hx)))|].
  destruct (Z_lt_dec x (o + 24)) as [L|L].
  + rewrite (LOW x ltac:(lia)). destruct Hrw as (_ & (_ & _ & Hst)). destruct (Hst x Hx) as (_ & b & Hb).
    exists b. exact Hb.
  + rewrite (P_o_hi x ltac:(lia)).
    destruct (Z_lt_dec x (o + 32)); [apply (fn_val_some _ _ _ _ Hv24); cbn; lia|].
    destruct (Z_lt_dec x (o + 40)); [apply (fn_val_some _ _ _ _ Hv32); cbn; lia|].
    destruct (Z_lt_dec x (o + 48)); [apply (fn_val_some _ _ _ _ Hv40); cbn; lia|].
    apply (fn_val_some _ _ _ _ Hv48); cbn; lia.
- apply fsw_val_pj_u32; [|lia|lia|lia]. apply (fn_val_xfer _ _ _ _ _ (fsw_pj_u32_val tfibsegs _ _ _ Hty)).
  intros j Hj. apply LOW. lia.
- apply (parse_items_shape.pis_u64_frame tfibsegs MR3 MR7 (o + 8) num Hnum). intros x Hx. apply LOW. lia.
- apply (parse_items_shape.pis_u64_frame tfibsegs MR3 MR7 (o + 16) 0 Hs). intros x Hx. apply LOW. lia.
- apply fsw_val_pj_u64; [exact (HI 24 k' ltac:(lia) ltac:(lia) Hv24) | exact (proj1 Hkd) | lia | lia].
- apply fsw_val_pj_u64; [exact (HI 32 y' ltac:(lia) ltac:(lia) Hv32) | exact (proj1 Hky) | lia | lia].
- apply fsw_val_pj_u64; [exact (HI 40 (n + 1) ltac:(lia) ltac:(lia) Hv40) | lia | lia | lia].
- apply fsw_val_pj_u64; [exact (HI 48 cap' ltac:(lia) ltac:(lia) Hv48) | exact (proj1 Hcp) | lia | lia].
Qed.

Lemma P_slots7 : PjStruct.pj_slots_at (fun a0 kk => In (a0, kk) Do) 6 k' y' (n + 1) cap'.
Proof.
pose proof P_cap' as Hc. pose proof P_ncap as Hnc. destruct Hsl3 as (Ht & (Hn1 & Hn2) & _ & _).
split; [exact Ht|]. split; [lia|]. split; [intros E; exfalso; lia|].
intros _. split; [exact P_NSk_in | intros _; exact P_NSy_in].
Qed.

Lemma P_same_old : forall b x, In b (Di ++ Dw) -> PjStruct.pj_holds b x -> parse_items_shape.pis_same tfibsegs MR1 MR7 x.
Proof.
intros b x Hb Hh. pose proof (P_old_bytes b x Hb (fn_holds_hb b x Hh)) as E.
split; [exact (fn_mbyte_eq _ _ x E) | intros Hw; exact (writable_at_eq tfibsegs MR1 MR7 x E Hw)].
Qed.

Lemma P_mvk7 : forall i, 0 <= i < 56 * n -> mbyte tfibsegs MR7 (k' + i) = mbyte tfibsegs MR1 (kids + i).
Proof.
intros i Hi. pose proof P_ncap as Hnc. pose proof P_cap' as Hc'.
rewrite <- (Hmvk i ltac:(lia)). apply fn_mbyte_eq.
apply (P_ns_bytes (k', 56 * cap') (k' + i)).
- rewrite P_NS. left. reflexivity.
- apply fn_holds_hb. unfold PjStruct.pj_holds. cbn [fst snd]. lia.
- intros E. exfalso. exact (P_NSy_k (eq_sym E)).
- intros _. lia.
Qed.

Lemma P_mvy7 : forall i, 0 <= i < 8 * n -> mbyte tfibsegs MR7 (y' + i) = mbyte tfibsegs MR1 (keys + i).
Proof.
intros i Hi. pose proof P_ncap as Hnc. pose proof P_cap' as Hc'.
rewrite <- (Hmvy i ltac:(lia)). apply fn_mbyte_eq.
apply (P_ns_bytes (y', 8 * cap') (y' + i)).
- rewrite P_NS. right. left. reflexivity.
- apply fn_holds_hb. unfold PjStruct.pj_holds. cbn [fst snd]. lia.
- intros _. lia.
- intros E. exfalso. exact (P_NSy_k E).
Qed.

Lemma P_kbnd : k' mod 8 = 0 /\ 0 <= k' /\ k' + 56 * cap' <= alloc_ceiling.
Proof.
destruct (P_Do4 _ P_NSk_in) as (I4 & Hal & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hal, Hk.
destruct (fsw_ablock_low B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as (L1 & L2 & _). rewrite fn_req_hb in L2 by exact Hk.
unfold HEAD in *. split; [|lia]. Z.div_mod_to_equations. lia.
Qed.

Lemma P_ybnd : 0 <= y' /\ y' + 8 * cap' <= alloc_ceiling.
Proof.
destruct (P_Do4 _ P_NSy_in) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
destruct (fsw_ablock_low B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as (L1 & L2 & _). rewrite fn_req_hb in L2 by exact Hk.
unfold HEAD in *. lia.
Qed.

Lemma P_abnd : 4096 <= a /\ a + klen + 1 <= alloc_ceiling.
Proof.
destruct (P_Do4 _ P_sd_Do) as (I4 & _ & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hk.
destruct (fsw_ablock_low B ly4 S4 W4 mx4 md4 _ _ HAR4 I4) as (L1 & L2 & _). rewrite fn_req_hb in L2 by exact Hk.
unfold HEAD in *. lia.
Qed.

Lemma P_open7 : parse_items_shape.pis_open tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) o true num k' y' cap' (n + 1)
  (map snd ms) (map fst ms) Di.
Proof.
pose proof P_ncap as Hnc. pose proof P_cap' as Hc'. pose proof asan_consts as (C1 & _).
pose proof P_kbnd as Kb. pose proof P_ybnd as Yb.
assert (ESL : parse_items_shape.pis_slots true k' y' cap' = NS) by reflexivity.
apply (parse_items_shape.pis_xfer tfibsegs MR1 (fun a0 kk => In (a0, kk) D) MR7 (fun a0 kk => In (a0, kk) Do) o true
  num kids keys cap n (map snd ms) (map fst ms) Di num k' y' cap' (n + 1) Hop).
- exact P_hdr7.
- exact P_slots7.
- intros E. discriminate E.
- rewrite ESL. pose proof P_ndDo as N. rewrite app_assoc in N. exact (parse_items_shape.pis_nodup_l _ _ _ N).
- rewrite ESL. intros b x Hb Hh Ho. exact (P_o4 b x (P_NS_Do b Hb) Ho (fn_holds_hb b x Hh)).
- intros a0 kk H. apply in_or_app. right. apply in_or_app. left. exact H.
- intros x (b & Hb & Hh). exact (P_same_old b x (in_or_app _ _ _ (or_introl Hb)) Hh).
- rewrite P_len. intros i Hi. exact (P_mvk7 i Hi).
- rewrite P_len. intros i Hi _. destruct (P_kids_present i Hi) as (b & Hb).
  assert (Hh : PjStruct.pj_holds (fn_hb (k', 56 * cap')) (k' + i))
    by (apply fn_holds_hb; unfold PjStruct.pj_holds; cbn [fst snd]; lia).
  destruct (P_Do_geo _ _ P_NSk_in Hh) as (_ & Hi' & _).
  apply (fn_wr_of_mbyte MR7 (k' + i) b); [lia | exact Hi' | rewrite (P_mvk7 i Hi); exact Hb].
- rewrite P_len. intros _. split; [exact (proj1 Kb)|]. split; [exact (proj1 (proj2 Kb))|]. lia.
- right. rewrite P_len. intros b x Hb Hh Hk.
  apply (P_Do_disj b (k', 56 * cap') x (P_old_Do b (in_or_app _ _ _ (or_introl Hb))) P_NSk_in).
  + intros E. apply (P_old_notNS b (in_or_app _ _ _ (or_introl Hb))). rewrite E, P_NS. left. reflexivity.
  + exact (fn_holds_hb b x Hh).
  + apply fn_holds_hb. unfold PjStruct.pj_holds. cbn [fst snd]. lia.
- intros _. rewrite P_len. split; [intros i Hi; exact (P_mvy7 i Hi) | intros _; lia].
Qed.

Lemma P_kid_node : PjStruct.pj_node tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) (k' + 56 * n) tv Dw.
Proof.
pose proof P_ncap as Hnc. pose proof P_cap' as Hc'. pose proof asan_consts as (C1 & _). pose proof P_kbnd as Kb.
destruct HTw as (HN & _).
apply (parse_items_shape.pis_node_xfer tfibsegs tv MR1 (fun a0 kk => In (a0, kk) Dw) MR7 (fun a0 kk => In (a0, kk) Do)
  w (k' + 56 * n) Dw HN).
- intros a0 kk H. exact (P_old_Do _ (in_or_app _ _ _ (or_intror H))).
- intros x (b & Hb & Hh). exact (P_same_old b x (in_or_app _ _ _ (or_intror Hb)) Hh).
- destruct Kb as (K8 & _). Z.div_mod_to_equations. lia.
- lia.
- lia.
- intros i Hi. exact (P_kid7 i Hi).
- intros i Hi _.
  assert (Hh : PjStruct.pj_holds (fn_hb (k', 56 * cap')) (k' + 56 * n + i))
    by (apply fn_holds_hb; apply P_K_hb; lia).
  destruct (P_Do_geo _ _ P_NSk_in Hh) as (_ & Hi' & _).
  destruct (mbyte tfibsegs MR1 (w + i)) as [b|] eqn:Eb; [|exfalso; exact (P_w_present (w + i) ltac:(lia) Eb)].
  apply (fn_wr_of_mbyte MR7 (k' + 56 * n + i) b); [lia | exact Hi' | rewrite (P_kid7 i Hi); exact Eb].
- intros b x Hb Hh Hk.
  apply (P_Do_disj b (k', 56 * cap') x (P_old_Do b (in_or_app _ _ _ (or_intror Hb))) P_NSk_in).
  + intros E. apply (P_old_notNS b (in_or_app _ _ _ (or_intror Hb))). rewrite E, P_NS. left. reflexivity.
  + exact (fn_holds_hb b x Hh).
  + apply fn_holds_hb. apply P_K_hb. lia.
Qed.

Lemma P_slot_u64 : PjStruct.pj_u64 tfibsegs MR7 (y' + 8 * n) a.
Proof.
pose proof P_abnd. pose proof P_ybnd. pose proof P_ncap. pose proof P_cap'. pose proof asan_consts as (C1 & _).
apply fsw_val_pj_u64; [|lia|lia|lia].
apply (fn_val_xfer _ _ _ _ _ Hvs). intros j Hj.
apply (YCbq.mbyte_of_aview tfibsegs (w_H W4) (w_H W4) m5 m7). apply P_slot7. lia.
Qed.

Lemma P_key_cstr : PjStruct.pj_cstr tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) a (klen + 1) kname.
Proof.
pose proof P_abnd as Ab. pose proof asan_consts as (C1 & _).
assert (G7 : garr8 tfibsegs MR7 a (kname ++ [0])).
{ apply (garr8_frame tfibsegs MR4 MR7 a (kname ++ [0]) Hzb4). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply fn_mbyte_eq. apply P_sd_bytes. unfold PjStruct.pj_holds, fn_hb, HEAD. cbn [fst snd]. lia. }
split; [exact P_sd_Do|]. split; [lia|]. split.
- destruct HK4 as ((Hg & Hnz) & _). pose proof (garr8_bytes_ok tfibsegs _ _ _ Hg) as Hok. unfold bytes_ok in Hok.
  apply Forall_app in Hok as [Hok _]. rewrite Forall_forall in Hok, Hnz |- *. intros c Hc.
  specialize (Hok c Hc). specialize (Hnz c Hc). lia.
- split; [lia|]. split; [rewrite length_map, length_app; cbn [length]; lia|].
  intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
  assert (Hi' : (i < length (kname ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  rewrite nth_error_map. rewrite (nth_error_nth' (kname ++ [0%Z]) 0%Z Hi').
  cbn [option_map].
  exact (garr8_mbyte tfibsegs MR7 a (kname ++ [0%Z]) i G7 Hi').
Qed.

Lemma P_snoc7 : parse_items_shape.pis_open tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) o true num k' y' cap' (n + 1)
  (map snd ms ++ [tv]) (map fst ms ++ [kname]) (Di ++ [(a, klen + 1)] ++ Dw).
Proof.
apply (parse_items_shape.pis_snoc tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) o true num k' y' cap' (n + 1)
  (map snd ms) (map fst ms) Di tv kname [(a, klen + 1)] Dw P_open7).
- rewrite P_len. exact P_kid_node.
- exists a, (klen + 1). split; [reflexivity|]. rewrite P_len. split; [exact P_slot_u64 | exact P_key_cstr].
- exact P_ndDo.
- intros b x Hb Hh Ho. apply (P_o4 b x); [| exact Ho | exact (fn_holds_hb b x Hh)].
  destruct Hb as [Hb|Hb]; [subst b; exact P_sd_Do | exact (P_old_Do b (in_or_app _ _ _ (or_intror Hb)))].
Qed.

Lemma P_node7 : PjStruct.pj_node tfibsegs MR7 (fun a0 kk => In (a0, kk) Do) o
  (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do.
Proof.
rewrite (pj_set_shape.ps_set_miss ms kname tv).
2: { intros nm' u Hin E. subst nm'. apply Hkey. apply in_map_iff. exists (kname, u). split; [reflexivity | exact Hin]. }
pose proof P_snoc7 as H.
replace (map snd ms ++ [tv]) with (map snd (ms ++ [(kname, tv)])) in H by (rewrite map_app; reflexivity).
replace (map fst ms ++ [kname]) with (map fst (ms ++ [(kname, tv)])) in H by (rewrite map_app; reflexivity).
change Do with (parse_items_shape.pis_slots true k' y' cap' ++ Di ++ [(a, klen + 1)] ++ Dw) at 2.
apply (pj_set_shape.ps_obj_node tfibsegs MR7 _ o (ms ++ [(kname, tv)]) (Di ++ [(a, klen + 1)] ++ Dw) num k' y'
  (n + 1) cap' H).
rewrite length_app. cbn [length]. lia.
Qed.

Lemma P_rbo7 : rd_blocks_ok tfibsegs B ly4 S4 W4 m7 Do.
Proof.
intros p kk He. destruct (P_Do4 (p, kk) He) as (I4 & Hal & Hk). unfold fn_hb in I4. cbn [fst snd] in I4, Hal, Hk.
split; [exact I4|]. split; [exact Hal|]. split; [exact Hk|].
assert (HH : forall j, (j < 8)%nat -> PjStruct.pj_holds (fn_hb (p, kk)) (p - HEAD + Z.of_nat j))
  by (intros j Hj; unfold PjStruct.pj_holds, fn_hb, HEAD; cbn [fst snd]; lia).
apply in_app_or in He as [He|He].
- destruct (Hbo3 p kk He) as (_ & _ & _ & Hv). apply (fn_val_xfer _ _ _ _ _ Hv). intros j Hj.
  apply fn_mbyte_eq. apply (P_ns_bytes (p, kk)); [exact He | exact (HH j Hj) | |].
  + intros E. injection E as E1 E2. unfold HEAD. pose proof P_ncap. lia.
  + intros E. injection E as E1 E2. unfold HEAD. pose proof P_ncap. lia.
- apply in_app_or in He as [He|[He|He]].
  + pose proof (in_or_app Di Dw (p, kk) (or_introl He)) as Ho.
    destruct (P_hb_pos (p, kk) (P_old_DDw _ Ho)) as (_ & _ & _ & Hv). apply (fn_val_xfer _ _ _ _ _ Hv). intros j Hj.
    apply fn_mbyte_eq. exact (P_old_bytes (p, kk) _ Ho (HH j Hj)).
  + injection He as <- <-. destruct Hrb4 as (_ & _ & _ & Hv). apply (fn_val_xfer _ _ _ _ _ Hv). intros j Hj.
    apply fn_mbyte_eq. exact (P_sd_bytes _ (HH j Hj)).
  + pose proof (in_or_app Di Dw (p, kk) (or_intror He)) as Ho.
    destruct (P_hb_pos (p, kk) (P_old_DDw _ Ho)) as (_ & _ & _ & Hv). apply (fn_val_xfer _ _ _ _ _ Hv). intros j Hj.
    apply fn_mbyte_eq. exact (P_old_bytes (p, kk) _ Ho (HH j Hj)).
Qed.

Lemma P_rtree7 : rtree tfibsegs B ly4 S4 W4 m7 o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do.
Proof. split; [exact P_node7 | split; [exact P_rbo7 | apply incl_refl]]. Qed.

(* ================= val, obj and the key at m7 ================= *)
Lemma P_zero7 : PjStruct.pj_zero tfibsegs MR7 w.
Proof.
pose proof asan_consts as (C1 & _). destruct (fsw_pobj_low B ly4 S4 W4 mx4 md4 m4 w HAR4 HPw4) as (L1 & L2).
assert (Z7 : forall x, w <= x < w + 56 -> mbyte tfibsegs MR7 x = Some (Z_to_bv 8 0)).
{ intros x Hx. replace x with (w + (x - w)) by lia. exact (fn_aview_some _ _ _ _ (Hz7 (x - w) ltac:(lia))). }
split.
- apply fn_rw; [|lia|lia|].
  + destruct HPw4 as ([(_ & H8 & _)|(_ & H8 & _)] & _); exact H8.
  + intros x Hx. split; [exact (proj1 (proj2 (P_w_geo x Hx))) | eexists; exact (Z7 x Hx)].
- split; [lia|]. split; [rewrite repeat_length; lia|].
  intros i Hi. rewrite repeat_length in Hi.
  assert (E : nth_error (repeat (Z_to_bv 8 0) 56) i = Some (Z_to_bv 8 0)) by (apply nth_error_repeat; exact Hi).
  rewrite E. exact (Z7 (w + Z.of_nat i) ltac:(lia)).
Qed.

Lemma P_pobj7o : pobj tfibsegs B ly4 S4 W4 m7 o.
Proof.
pose proof asan_consts as (C1 & _).
apply (fn_pobj_xfer ly4 S4 W4 m4 m7 o HPo4).
- intros x Hx. destruct (P_o_geo x Hx) as (Hc & _). destruct (fn_shadow_rng x Hc) as (R1 & R2).
  exact (P_shadow_kept _ R1 R2).
- intros i Hi. destruct (P_o_geo (o + i) ltac:(lia)) as (Hc & Hni & _).
  pose proof P_hdr7 as (Hrw & _). destruct Hrw as (_ & (_ & _ & Hst)).
  destruct (Hst (o + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

Lemma P_pobj7w : pobj tfibsegs B ly4 S4 W4 m7 w.
Proof.
pose proof asan_consts as (C1 & _).
apply (fn_pobj_xfer ly4 S4 W4 m4 m7 w HPw4).
- intros x Hx. destruct (P_w_geo x Hx) as (Hc & _). destruct (fn_shadow_rng x Hc) as (R1 & R2).
  exact (P_shadow_kept _ R1 R2).
- intros i Hi. pose proof P_zero7 as ((_ & (_ & _ & Hst)) & _).
  destruct (Hst (w + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

Lemma P_cstr7 : cstr_ok tfibsegs W4 m7 k kname.
Proof.
pose proof asan_consts as (C1 & _). pose proof alloc_ceiling_value as (_ & Hc4096).
pose proof HK4 as ((Hg & Hnz) & H4096 & Hhi & H32 & Ham & Hra & Hhv & Htl).
(* only `k + klen + 1 <= alloc_ceiling` is used below, so the proof is the same under S0's `+ 1` ceiling bound *)
assert (Hk1 : k + klen + 1 <= alloc_ceiling) by lia. clear Hhi.
assert (STR : forall x, k <= x < k + klen + 1 -> aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m4 x).
{ intros x Hx. destruct (Hkfoot x Hx) as (F1 & F2). apply P_T47; [lia | | | | ].
  - intros Hs. apply (P_str_NS (y', 8 * cap') x); [rewrite P_NS; right; left; reflexivity | exact Hx | exact (P_S_hb x Hs)].
  - intros Ho. apply F1. left. lia.
  - intros Hk. apply (P_str_NS (k', 56 * cap') x); [rewrite P_NS; left; reflexivity | exact Hx | exact (P_K_hb x Hk)].
  - intros Hw. apply F2. left. exact Hw. }
split; [split; [|exact Hnz]|].
- apply (garr8_frame tfibsegs MR4 MR7 k (kname ++ [0]) Hg). intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  apply (YCbq.mbyte_of_aview tfibsegs (w_H W4) (w_H W4) m4 m7 x). apply STR. lia.
- split; [exact H4096|]. split; [exact (proj1 (proj2 (proj2 HK4)))|]. split; [exact H32|]. split; [exact Ham|].
  split; [|split].
  + intros x Hx. destruct (Hra x Hx) as (sv & Esv & Ok). exists sv. split; [|exact Ok].
    destruct (fn_shadow_rng x ltac:(lia)) as (R1 & R2). rewrite (P_shadow_kept _ R1 R2). exact Esv.
  + intros s Hs. apply P_vis; [|exact (Hhv s Hs)].
    unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
  + intros x Hx. apply P_vis; [|exact (Htl x Hx)]. clear - Hx Hk1 Hc4096 H4096.
    Z.div_mod_to_equations. lia.
Qed.

(* ================= the post's data clauses ================= *)
Lemma P_main : exists Dr Do',
  Permutation D (Dold ++ Dr) /\ Permutation Do' (Dnew ++ (a, klen + 1) :: Dr ++ Dw) /\
  rtree tfibsegs B ly4 S4 W4 m7 o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do' /\
  PjStruct.pj_zero tfibsegs MR7 w /\
  pobj tfibsegs B ly4 S4 W4 m7 o /\ pobj tfibsegs B ly4 S4 W4 m7 w /\ cstr_ok tfibsegs W4 m7 k kname.
Proof.
assert (TAIL : rtree tfibsegs B ly4 S4 W4 m7 o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\
  PjStruct.pj_zero tfibsegs MR7 w /\
  pobj tfibsegs B ly4 S4 W4 m7 o /\ pobj tfibsegs B ly4 S4 W4 m7 w /\ cstr_ok tfibsegs W4 m7 k kname)
  by exact (conj P_rtree7 (conj P_zero7 (conj P_pobj7o (conj P_pobj7w P_cstr7)))).
destruct P_grow as [(Hlt & E1 & E2 & E3 & E4 & E5 & _)|(Heq & _ & E4 & E5)].
- exists D, Do. split; [rewrite E4; apply Permutation_refl|]. split; [|exact TAIL].
  rewrite E5, HDi, P_slots_eq, E1, E2, E3. cbn [app]. rewrite app_assoc.
  apply Permutation_sym. apply Permutation_middle.
- exists Di, Do. split; [rewrite E4, HDi, P_slots_eq; apply Permutation_refl|]. split; [|exact TAIL].
  rewrite E5, P_NS. cbn [app].
  apply Permutation_cons; [reflexivity|]. apply Permutation_cons; [reflexivity|].
  apply Permutation_sym. apply Permutation_middle.
Qed.

End P.

(* ================= pSf_post: the data side of pj_set_spec's post =================
   Premises: the byte facts pj_set's walk exports after each call (m1 at pj_get's return, m3 at grow's, m4 at
   fuzz_strdup's, m5 after stage D's two stores, m6 after __asan_memcpy, m7 after __asan_memset), and pj_set_spec's
   entry premises carried to m1. Beyond those byte facts it takes (each one a fact the walk holds at that point, by
   its journal / ARU):
   - HAR1, HAR4: AR at (ly1, S1) and (ly4, S4), any memory: AR's separation law is what puts two different live
     blocks apart, and fsw_ablock_* / fsw_pobj_* read the image / shadow / ceiling bounds off it;
   - Hfr3 / Hfa3, Hfr4 / Hfa4: the fake frames and their addresses are those of m1 at m3 and m4 (ajournal's frames
     clause and AR's layout law): obj and val may sit in check_round_trip's fake frame;
   - HPo4, HPw4, HK4: pobj obj / pobj val / cstr_ok key at m4: their SHADOW bytes, which the byte facts KEPT_g / KEPT_s
     (blocks and frames only) do not carry (pobj_kept_call / cstr_ok_kept_call over fuzz_strdup's own journal);
   - Hheads (pj_set_spec's `incl (rd_heads Dold0) U`): a key in a live block is not on a freed kids / keys head. *)
Lemma pSf_post : forall (ly1 ly3 ly4 : alayout) (S1 S3 S4 : astate) (W1 W3 W4 : world tfibsegs)
    (m1 m3 m4 m5 m6 m7 mx1 mx4 : word -> option byte) (md1 md4 : Model)
    (o k w num str kids keys n cap k' y' cap' a : Z) (ms : list (list Z * PjTree.jv)) (tv : PjTree.jv)
    (D Dw Dold Dnew U Ug : list (Z * Z)) (kname : list Z),
  let klen := Z.of_nat (length kname) in
  let Dold0 := ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap in
  (* ---- m1, pj_get's return, with pj_set_spec's entry premises ---- *)
  rtree tfibsegs B ly1 S1 W1 m1 o (PjTree.JObj ms) D -> pobj tfibsegs B ly1 S1 W1 m1 o ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W1) m1) o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
  incl (rd_heads Dold0) U ->
  rtree tfibsegs B ly1 S1 W1 m1 w tv Dw -> pobj tfibsegs B ly1 S1 W1 m1 w ->
  (forall bk, In bk Dw -> ~ In bk D) -> (forall x, w <= x < w + 56 -> ~ PjStruct.pj_foot o D x) ->
  PjStruct.pj_apart Dw o ->
  cstr_kept B ly1 S1 U k kname ->
  (forall x, k <= x < k + klen + 1 -> ~ PjStruct.pj_foot o D x /\ ~ PjStruct.pj_foot w Dw x) ->
  ~ In kname (map fst ms) ->
  AR tfibsegs B ly1 S1 W1 mx1 md1 ->
  (* ---- m3, grow's return ---- *)
  grow_res 6 n cap kids keys k' y' cap' Dold Dnew U Ug ->
  Permutation (ablocks B ly3 S3 ++ rd_hblocks Dold) (ablocks B ly1 S1 ++ rd_hblocks Dnew) ->
  PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) m3) o 6 num str k' y' n cap' ->
  PjStruct.pj_slots_at (fun a0 kk => In (a0, kk) (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap'))
    6 k' y' n cap' ->
  rd_blocks_ok tfibsegs B ly3 S3 W3 m3 (ReaderRes.kids_blk k' cap' ++ ReaderRes.keys_blk 6 y' cap') ->
  rd_moved tfibsegs W1 W3 m1 m3 kids k' (56 * cap) -> rd_moved tfibsegs W1 W3 m1 m3 keys y' (8 * cap) ->
  (forall x, ~ inFP ([(o + 24, o + 40); (o + 48, o + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) x ->
     ((exists p nn, In (p, nn) (ablocks B ly1 S1) /\ p <= x < p + req_size nn) \/
      (exists cid pos, In (cid, pos) (frames S1) /\
         frame_addr ly1 cid pos <= x < frame_addr ly1 cid pos + fs_frame_bytes cid)) ->
     mrestrict (w_H W3) m3 (Z_to_bv 64 x) = mrestrict (w_H W1) m1 (Z_to_bv 64 x)) ->
  frames S3 = frames S1 -> (forall cid pos, frame_addr ly3 cid pos = frame_addr ly1 cid pos) ->
  (* ---- m4, fuzz_strdup's return ---- *)
  ablocks B ly4 S4 = ablocks B ly3 S3 ++ [(a - HEAD, klen + 1 + HEAD)] ->
  fs_rblock tfibsegs B ly4 S4 W4 m4 a (klen + 1) -> zbytes_at tfibsegs W4 m4 a (kname ++ [0]) ->
  (forall x, ~ inFP FS_PSTAT_FP x ->
     ((exists p nn, In (p, nn) (ablocks B ly3 S3) /\ p <= x < p + req_size nn) \/
      (exists cid pos, In (cid, pos) (frames S3) /\
         frame_addr ly3 cid pos <= x < frame_addr ly3 cid pos + fs_frame_bytes cid)) ->
     mrestrict (w_H W4) m4 (Z_to_bv 64 x) = mrestrict (w_H W3) m3 (Z_to_bv 64 x)) ->
  frames S4 = frames S1 -> (forall cid pos, frame_addr ly4 cid pos = frame_addr ly1 cid pos) ->
  AR tfibsegs B ly4 S4 W4 mx4 md4 ->
  pobj tfibsegs B ly4 S4 W4 m4 o -> pobj tfibsegs B ly4 S4 W4 m4 w -> cstr_ok tfibsegs W4 m4 k kname ->
  (* ---- m5, stage D's stores (slot := y' + 8 * n) ---- *)
  val_mem tfibsegs (mrestrict (w_H W4) m5) (y' + 8 * n) 8 a ->
  val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 24) 8 k' ->
  val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 32) 8 y' ->
  val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 40) 8 (n + 1) ->
  val_mem tfibsegs (mrestrict (w_H W4) m5) (o + 48) 8 cap' ->
  (forall x, 0 <= x < alloc_ceiling ->
     mbyte tfibsegs (mrestrict (w_H W4) m4) x <> None -> mbyte tfibsegs (mrestrict (w_H W4) m5) x <> None) ->
  (forall x, 0 <= x < alloc_ceiling -> ~ (y' + 8 * n <= x < y' + 8 * n + 8) -> ~ (o + 24 <= x < o + 56) ->
     m5 (Z_to_bv 64 x) = m4 (Z_to_bv 64 x)) ->
  (* ---- m6, __asan_memcpy (k' + 56 * n, w, 56) ---- *)
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m6 (k' + 56 * n + i) = aview tfibsegs (w_H W4) m5 (w + i)) ->
  (forall x, 0 <= x < alloc_ceiling -> ~ (k' + 56 * n <= x < k' + 56 * n + 56) ->
     aview tfibsegs (w_H W4) m6 x = aview tfibsegs (w_H W4) m5 x) ->
  (* ---- m7, __asan_memset (w, 0, 56) ---- *)
  (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W4) m7 (w + i) = Some 0) ->
  (forall x, 0 <= x < alloc_ceiling -> ~ (w <= x < w + 56) ->
     aview tfibsegs (w_H W4) m7 x = aview tfibsegs (w_H W4) m6 x) ->
  exists Dr Do,
    Permutation D (Dold ++ Dr) /\ Permutation Do (Dnew ++ (a, klen + 1) :: Dr ++ Dw) /\
    rtree tfibsegs B ly4 S4 W4 m7 o (PjTree.JObj (PjTree.pj_set_model ms kname tv)) Do /\
    PjStruct.pj_zero tfibsegs (mrestrict (w_H W4) m7) w /\
    pobj tfibsegs B ly4 S4 W4 m7 o /\ pobj tfibsegs B ly4 S4 W4 m7 w /\ cstr_ok tfibsegs W4 m7 k kname.
Proof.
intros ly1 ly3 ly4 S1 S3 S4 W1 W3 W4 m1 m3 m4 m5 m6 m7 mx1 mx4 md1 md4 o k w num str kids keys n cap k' y' cap' a ms tv
  D Dw Dold Dnew U Ug kname klen Dold0
  HTo HPo HHo Hcap Hheads HTw HPw HDwD HwD HDwo HKk Hkfoot Hkey HAR1
  Hgr Hgperm HHo3 Hsl3 Hbo3 Hmvk Hmvy Hkeptg Hfr3 Hfa3
  Hab4 Hrb4 Hzb4 Hkepts Hfr4 Hfa4 HAR4 HPo4 HPw4 HK4
  Hvs Hv24 Hv32 Hv40 Hv48 Hgrow5 Hm5 Hcp6 Hm6 Hz7 Hm7.
pose proof HTo as (HN & _).
destruct (pj_set_shape.ps_node_open tfibsegs _ _ o ms D num str kids keys n cap HN HHo Hcap)
  as (Di & HDi & Hstr & Hn & Hop).
exact (P_main ly1 ly3 ly4 S1 S3 S4 W1 W3 W4 m1 m3 m4 m5 m6 m7 mx1 mx4 md1 md4 o k w num str kids keys n cap k' y' cap' a
  ms tv D Dw Di Dold Dnew U Ug kname
  HTo HPo HTw HPw HDwD HwD HDwo Hkfoot Hkey Hheads HKk HAR1
  Hgr Hgperm HHo3 Hsl3 Hbo3 Hmvk Hmvy Hkeptg Hfr3 Hfa3
  Hab4 Hrb4 Hzb4 Hkepts Hfr4 Hfa4 HAR4 HPo4 HPw4 HK4
  Hvs Hv24 Hv32 Hv40 Hv48 Hgrow5 Hm5 Hcp6 Hm6 Hz7 Hm7 HDi Hstr Hn Hop).
Qed.

End F.
