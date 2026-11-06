(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the walk of same at image A' (asan #102 pin 1be0f53d96cb9d6c, unstripped twin
   bff8519bbe3ea0e4): Section W (the walk's premises, each with its owner), Section E (one nesting level: the entry
   state, the invariant, the segment lemmas, the item loop), then same_holds_Ap, the kit's tsame_specX (PRH_FnEx.v :353, cut
   7cdbb61b5fa0) at PI_prog_A, by strong induction on the nesting.
   THE TWO DONORS. The instruction walk is the old-A walk lib/A/Prog/Wsame.v (a Theorem Labs lane's slice S9,
   a working branch 9a0674f0b5f2, old pin d83eb25d), relocated: A' same is the same code modulo
   19 words (lib/A/Prog/SameAp_defs.v's header), so each segment is Wsame's, with its pcs in SMA_AT form. The statement,
   kit and engine are the cut's, re-stated as a Theorem Labs lane's image-B' walk lib/B/Prog/SameB_walk.v
   (a working branch e95b6ce78e87) did for the four text changes from the old tsame_specX (PRH_FnEx blob
   76731d160419 :320) to the cut's (be1dd5ecaaf6 :353): prh_ledger carries most own; the guarded live-stack premise
   after fpre (HSUP); fpostm (the memnorm keep: sma_INV's sixth conjunct, each run's HMNP, the memnorm-keeping runtime
   rows astrcmp_realizes_xrom / abcmp_realizes_xm, the callee's keep through the induction hypothesis); S' = S
   (sma_INV's S1 = S). The names are Wsame's with s9_ -> sma_ (SameB's smb_ -> sma_). lib/A/Prog/SameAp_final.v states
   it at the instance of record. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YG0scf YGcfBlockRange.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
(* c-omx-alloc's engine leaf (blob 136e8c774182, origin/cold/c-omx-alloc-preset-s1b f027ed1fab66): astack_up_x and
   astack_up_journal_x *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import SameAp_kit SameAp_memA SameAp_memB SameAp_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_A.
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the non-primary room of the kit's texts (PRH_Base.v PrhRoomLive): same makes no allocator call, so the walk only
   carries room_live_cf S -> room_live_cf S' (S' = S) and holds at every instance (a8's prh_room_live_a8 among them) *)
Context {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator laws at the harness head length cf_head (YCbqG c3b5d0111037; field 14 alx_hshadow and field 15
   alx_blocks_tail are the laws the walk's trees need). OWNER the engine (c-omx-alloc); at the instance of record
   (SameAp_final.v) YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf *)
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
(* the image facts of B at the listing (YC1fP.v PALib: the .got slot of the shadow base and the cell it points at, at
   A_OBJ 0 / A_OBJ 12). OWNER the image instance; at the instance of record PALibA.palib_A *)
Hypothesis PAL : YC1fP.PALib (PI := PI_prog_A) B.
(* the runtime rows, MARKED TEXTS. strcmp: YGcallMxmn.v's read-only-premise row with the memnorm keep,
   astrcmp_realizes_xrom (OWNER a Theorem Labs lane, its row). bcmp: YGcallMxmn.v's abcmp_realizes_xm (OWNER a Theorem Labs lane, the
   interceptor row) *)
Hypothesis STRCMP : astrcmp_realizes_xrom rsegs B ARx A_prog_relro_lo A_prog_relro_hi SMA_STRCMP.
Hypothesis BCMP : abcmp_realizes_xm rsegs B ARx SMA_BCMP.
(* ARx refines the second allocator instance ARcf (h-mani-a8): true at ARx := ARcf and at ARcfx := ARcf /\ xs_placed_cf
   (proj1). It gives, by a8's YGcfBlockRange.v, a live block below cf_malloc_max and the user range of a live block,
   the real stack's 64-aligned top, and (YG0scf.v frame_facts_cf) 64-aligned fake frames. OWNER h-mani-a8 (ARcf) *)
Hypothesis SMA_CF : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> ARcf rsegs B ly S Hp W mem md.
Let SMA_BMAX : forall ly S Hp (W : world rsegs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < cf_malloc_max :=
  fun ly S Hp W mem md p n H Hin => ablock_n_lt_max_cf rsegs B ly S Hp W mem md p n (SMA_CF ly S Hp W mem md H) Hin.
Let SMA_STK64 : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0 :=
  fun ly S Hp W mem md H => stk_hi_mod64_cf rsegs B ly S Hp W mem md (SMA_CF ly S Hp W mem md H).
Lemma SMA_FR64 : forall ly S Hp (W : world rsegs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (SMA_CF _ _ _ _ _ _ HAR) as [M _].
destruct (frame_facts_cf B ly S Hp _ cid pos M Hin) as (_ & _ & _ & _ & FA & _ & _ & Hoff & _ & Hbytes & _).
split; [|exact Hbytes].
unfold page_aligned in FA. apply Z.mod_divide in FA as [qF HqF]; [|lia].
apply Z.mod_divide in Hoff as [qO HqO]; [|lia].
unfold frame_addr. rewrite HqF, HqO. replace (qF * 4096 + qO * 64) with ((qF * 64 + qO) * 64) by ring.
apply Z_mod_mult.
Qed.
Let SMA_GOTC : as_got_shadow B = SMA_GOT /\ as_shadow_cell B = SMA_CELL :=
  conj (YC1fP.pal_got_shadow _ PAL) (YC1fP.pal_cell _ PAL).
Let HSL : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd := A_prog_segs_low.
Let HWX : wx_segs_nowrap rsegs := A_prog_wx.
Local Notation PST := (prh_pst (PI := prh_img_A)).

(* the strcmp row's 8-byte slack past a string in a harness block of the ledger: the block's user range from a8's
   block_user_range_cf (the user pointer at least 16 bytes into its chunk) *)
Lemma sma_amr8 : forall ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 x k n0,
  prh_ledger (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S ->
  In (x, k) Lam -> 0 <= n0 <= k -> amem_range8 x n0.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 x k n0 HL HAR1 Hbl Hin Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@ASAN_CEIL_range rc) as CR.
pose proof (@cf_head_nonneg cp) as Hc0.
destruct HL as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (x, k) Hin) as (Hk & Hblk & _).
cbn [fst snd] in Hk, Hblk. rewrite <- Hbl in Hblk. unfold ablocks in Hblk.
apply in_map_iff in Hblk as ([p m] & Ep & Hpb). cbn [fst snd] in Ep. injection Ep as Ep Em.
destruct (block_user_range_cf rsegs B ly1 S1 Hp1 W1 mem1 md1 p m (SMA_CF _ _ _ _ _ _ HAR1) Hpb)
  as (Hm & [[L1 L2] | [H1 H2]]); rewrite Ep, Em in *.
- assert (R : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  unfold amem_range8. left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
- assert (R : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  unfold amem_range8. right. unfold kHighMemEnd, kHighMemBeg in *. lia.
Qed.


(* THE GUARDED LIVE-STACK PREMISE. The kit's tsame_specX (PRH_FnEx.v :353) carries, right after fpre,
     spZ regs <= pa -> YGcallStackUp.astack_up_x segs ly W (spZ regs) mem
   (Section E's HSUP). The A' walk does not use it: at the recursive call (SMA_AT 0x208 `jal same`) s0 holds 1
   (SMA_AT 0xac `li s0, 1`; the loop never writes s0; a is in s2), so the callee's frame chain is the one below
   YM05.alloc_ceiling, as in the old-A walk; the image-B' walk needs HSUP only because B' keeps a in s0 across that
   call. The recursive call gives the callee its own copy, vacuous there: a kid is in a block of Lam, below
   YM05.alloc_ceiling and so below the callee's sp (sma_kids' HSUPc). *)

Section E.
Variables (n : nat) (ly : alayout) (S : astate) (Hp : list Z) (W : world rsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (pa pb : Z) (ta tb : jv) (Da Db : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z).
Hypothesis HFPRE : fpre (PA := PI_prog_A) B ARx (STK_same n) ly S Hp W regs mem md ch.
Hypothesis HSUP : spZ regs <= pa -> astack_up_x rsegs ly W (spZ regs) mem.
Hypothesis H10 : getr regs 10 = w64 pa.
Hypothesis H11 : getr regs 11 = w64 pb.
Hypothesis HTA : prhex_tree (PA := PI_prog_A) ly S Lam W regs mem pa ta Da.
Hypothesis HTB : prhex_tree (PA := PI_prog_A) ly S Lam W regs mem pb tb Db.
Hypothesis HDEP : (depth ta <= n)%nat.
Hypothesis HFA : forall z, pj_footR pa Da z -> ~ (spZ regs - STK_same n <= z < spZ regs).
Hypothesis HFB : forall z, pj_footR pb Db z -> ~ (spZ regs - STK_same n <= z < spZ regs).
Hypothesis HLED : prh_ledger (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis IH : forall n', (n' < n)%nat -> tsame_specX (PA := PI_prog_A) B ARx SK n'.

(* the text's post Q (tsame_specX's, inside fpostm's memnorm keep) *)
Definition sma_Q : alayout -> astate -> list Z -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\ (ta = tb /\ getr regs' 10 = w64 1 \/ ta <> tb /\ getr regs' 10 = w64 0) /\
    pj_nodeR rsegs (mrestrict (w_H W') mem') (prh_lin Lam) pa ta Da /\
    pj_nodeR rsegs (mrestrict (w_H W') mem') (prh_lin Lam) pb tb Db /\
    Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger (PA := PI_prog_A) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Definition sma_POST : world rsegs -> config -> Prop :=
  fpostm (PA := PI_prog_A) B ARx SK (STK_same n) [] regs ly S Hp W mem md sma_Q.

(* what every point of the walk carries: the journal from the entry, the allocator state unchanged (same allocates
   nothing), the ledger at the current memory, and the memnorm keep from the entry memory; the trees, the roots'
   shadow and the read-only bytes follow from it (SameAp_memA.v) *)
Definition sma_INV (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world rsegs) (mem1 : word -> option byte)
  (md1 : Model) (k1 : Z) : Prop :=
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 /\
  S1 = S /\ Hp1 = Hp /\ ablocks B ly1 S1 = ablocks B ly S /\
  prh_ledger (PA := PI_prog_A) B ly1 S1 Hp1 W1 mem1 Lam peak cnt fail ran most own /\
  (YAkMemnorm.memnorm rsegs mem -> YAkMemnorm.memnorm rsegs mem1).

(* the invariant across a stretch that writes only at or above YM05.alloc_ceiling (a run of the frame): the journal is
   the stretch's, the ledger is kept below YM05.alloc_ceiling, the memnorm keep is the run's (memnorm_frame_of) *)
Lemma sma_inv_frame : forall ly1 S1 Hp1 W1 m md1 k1 m' md' (E : env) rs,
  sma_INV ly1 S1 Hp1 W1 m md1 k1 ->
  (YAkMemnorm.memnorm rsegs m -> frame_of E rs m m' -> YAkMemnorm.memnorm rsegs m') ->
  frame_of E rs m m' ->
  frame_of E rs (mrestrict (w_H W1) m) (mrestrict (w_H W1) m') ->
  (forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) ->
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 m' md' k1 ->
  sma_INV ly1 S1 Hp1 W1 m' md' k1.
Proof.
intros ly1 S1 Hp1 W1 m md1 k1 m' md' E rs (HJ0 & HS1 & HHp & Hbl & HL & HM) HMN HF HFr Hwb HJ'.
pose proof HJ0 as (HAR0 & _).
split; [exact HJ'|]. split; [exact HS1|]. split; [exact HHp|]. split; [exact Hbl|]. split.
- apply (smak_ledger_keep (PA := PI_prog_A) B ARx LAWS ly1 S1 Hp1 W1 m md1 m' Lam peak cnt fail ran most own HAR0 HL).
  intros a Ha. exact (smak_frame_below rsegs E rs (w_H W1) m m' HFr Hwb a Ha).
- intros Hm. exact (HMN (HM Hm) HF).
Qed.

(* the invariant across a runtime call (strcmp, bcmp): its journal, the view kept outside its stack window, which
   lies at or above YM05.alloc_ceiling, and the row's memnorm keep *)
Lemma sma_inv_ecall : forall ly1 S1 Hp1 W1 m md1 k1 m' md' lo hi,
  sma_INV ly1 S1 Hp1 W1 m md1 k1 ->
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 m' md' k1 ->
  YM05.alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview rsegs (w_H W1) m' a = aview rsegs (w_H W1) m a) ->
  (YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m') ->
  sma_INV ly1 S1 Hp1 W1 m' md' k1.
Proof.
intros ly1 S1 Hp1 W1 m md1 k1 m' md' lo hi (HJ0 & HS1 & HHp & Hbl & HL & HM) HJ' Hlo Hk HMN.
pose proof HJ0 as (HAR0 & _).
split; [exact HJ'|]. split; [exact HS1|]. split; [exact HHp|]. split; [exact Hbl|]. split.
- apply (smak_ledger_keep (PA := PI_prog_A) B ARx LAWS ly1 S1 Hp1 W1 m md1 m' Lam peak cnt fail ran most own HAR0 HL).
  intros a Ha. pose proof asan_consts as (C1 & _). apply mbyte_of_aview. apply Hk; lia.
- intros Hm. exact (HMN (HM Hm)).
Qed.

Lemma sma_stk : STK_same n = Z.of_nat (Datatypes.S n) * 128 + 2 * ESTACK.
Proof. reflexivity. Qed.
Lemma sma_stk' : forall k, STK_same k = Z.of_nat (Datatypes.S k) * 128 + 2 * ESTACK.
Proof. reflexivity. Qed.

Lemma sma_nodes : forall ly1 S1 Hp1 W1 mem1 md1 k1, sma_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  pj_nodeR rsegs (mrestrict (w_H W1) mem1) (prh_lin Lam) pa ta Da /\
  pj_nodeR rsegs (mrestrict (w_H W1) mem1) (prh_lin Lam) pb tb Db.
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & _ & Hbl & _). pose proof HFPRE as [(HAR & _) _].
split; eapply (sma_node_now (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64); eassumption.
Qed.

Lemma sma_ras : forall ly1 S1 Hp1 W1 mem1 md1 k1, sma_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF pa 56 /\
  range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF pb 56.
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & HHp & Hbl & _). pose proof HFPRE as [(HAR & _) _].
split; eapply (sma_ra_now (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64); eassumption.
Qed.

Lemma sma_ro : forall ly1 S1 Hp1 W1 mem1 md1 k1, sma_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  arodata_okP rsegs A_prog_relro_lo A_prog_relro_hi B (aview rsegs (w_H W1) mem1).
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & _ & _ & HL1 & _). pose proof HFPRE as [_ [HRO _]].
exact (sma_ro_now (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HRO HLED HL1 HJ).
Qed.

(* a root's header, named at the entry, is the same header at every later point *)
Lemma sma_hdr_now : forall p t D ty num str kids keys nn cap ly1 S1 Hp1 W1 mem1 md1 k1,
  prhex_tree (PA := PI_prog_A) ly S Lam W regs mem p t D ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) p ty num str kids keys nn cap ->
  sma_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  pj_hdrR rsegs (mrestrict (w_H W1) mem1) p ty num str kids keys nn cap.
Proof.
intros p t D ty num str kids keys nn cap ly1 S1 Hp1 W1 mem1 md1 k1 HT Hh (HJ & _ & _ & Hbl & _).
pose proof HFPRE as [(HAR & _) _].
apply (pj_hdrR_frame rsegs _ _ p ty num str kids keys nn cap Hh). intros z Hz.
destruct (sma_foot_keep (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64 _ ly S Hp W regs mem md Lam
  peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 z HAR HLED HT HJ Hbl (or_introl Hz)) as (Hni & Hz64 & E).
exact (sma_agree_of_aview rsegs (w_H W) (w_H W1) mem mem1 z Hz64 Hni E).
Qed.

Lemma sma_hdr_of_node : forall m Lb p t D, pj_nodeR rsegs m Lb p t D ->
  exists num str kids keys nn cap, pj_hdrR rsegs m p (tag t) num str kids keys nn cap.
Proof.
intros m Lb p t D H. destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & nn & cap & Hh & _);
  exists num, str, kids, keys, nn, cap; exact Hh.
Qed.

(* the n field a node holds: the item count of a container, 0 otherwise *)
Definition sma_len (t : jv) : Z :=
  match t with JArr l => Z.of_nat (length l) | JObj l => Z.of_nat (length l) | _ => 0 end.
Lemma sma_node_n : forall H m Lb p t D ty num str kids keys nn cap,
  pj_nodeR rsegs (mrestrict H m) Lb p t D -> pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  nn = sma_len t.
Proof.
intros H m Lb p t D ty num str kids keys nn cap HN (_ & _ & _ & _ & _ & _ & Hn & _).
assert (U : forall n', rd_u64 rsegs (mrestrict H m) (p + 40) n' -> n' = nn)
  by (intros n' Hn'; exact (proj1 (sma_num_eq rsegs H m (p + 40) (p + 40) n' nn Hn' Hn) (fun i _ => eq_refl))).
destruct t; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & _ & _ & _ & _ & Hn' & _) & F);
  rewrite <- (U n' Hn'); cbn [sma_len].
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & H0 & _); exact H0.
- destruct F as (_ & H0 & _); exact H0.
Qed.
(* two trees with the same tag at most 2 (null, false, true) are equal *)
Lemma sma_tag_scalar : forall t t', tag t = tag t' -> tag t <= 2 -> t = t'.
Proof. intros [] [] E H; cbn in E, H; try lia; try discriminate; reflexivity. Qed.
(* a number or string node: its str field holds its text as a C string of the block predicate *)
Lemma sma_node_str : forall H m Lb p t D ty num str kids keys nn cap,
  pj_nodeR rsegs (mrestrict H m) Lb p t D -> pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  tag t = 3 \/ tag t = 4 ->
  exists s k, pj_cstrR rsegs (mrestrict H m) Lb str k s /\ (t = JStr s \/ exists bits, t = JNum s bits /\ num = bits).
Proof.
intros H m Lb p t D ty num str kids keys nn cap HN (_ & _ & Hnum & Hstr & _) Ht.
assert (U16 : forall s', rd_u64 rsegs (mrestrict H m) (p + 16) s' -> s' = str)
  by (intros s' Hs'; exact (proj1 (sma_num_eq rsegs H m (p + 16) (p + 16) s' str Hs' Hstr) (fun i _ => eq_refl))).
assert (U8 : forall s', rd_u64 rsegs (mrestrict H m) (p + 8) s' -> s' = num)
  by (intros s' Hs'; exact (proj1 (sma_num_eq rsegs H m (p + 8) (p + 8) s' num Hs' Hnum) (fun i _ => eq_refl))).
destruct t as [| | | txt bits | s | items | members]; cbn [tag] in Ht; try lia; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & Hnum' & Hstr' & _) & F).
- destruct F as (Eb & _ & _ & _ & _ & k & Hc & _). exists txt, k.
  split; [rewrite <- (U16 str' Hstr'); exact Hc|]. right. exists bits. split; [reflexivity|].
  rewrite <- (U8 num' Hnum'). exact Eb.
- destruct F as (_ & _ & _ & _ & k & Hc & _). exists s, k.
  split; [rewrite <- (U16 str' Hstr'); exact Hc|]. left. reflexivity.
Qed.

(* where a root lies: inside [4096, 2 ^ 47), 8-aligned, outside the image, apart from the shadow band *)
Lemma sma_root : forall p t D, prhex_tree (PA := PI_prog_A) ly S Lam W regs mem p t D ->
  4096 <= p /\ p + 56 <= 2 ^ 47 /\ p mod 8 = 0 /\
  (forall x, p <= x < p + 56 -> ~ in_img rsegs x /\ (x < kLowShadowBeg \/ kHighMemBeg <= x)).
Proof.
intros p t D (Hn & Hh & Hr).
destruct HFPRE as [HPRE _].
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof (smak_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (sma_hdr_of_node _ _ _ _ _ Hn) as (num & str & kids & keys & nn & cap & ((Hal & _) & _)).
destruct Hh as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- destruct HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & _).
  cbn [fst snd] in *. pose proof (@cf_head_nonneg cp) as Hc0.
  destruct (alx_blocks rsegs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hcl & Happ & _).
  assert (Hmc : 0 <= m + cf_head) by lia.
  pose proof (req_size_pos (m + cf_head) Hmc) as [Hq1 Hq2].
  split; [lia|]. split; [lia|]. split; [exact Hal|].
  intros x Hx.
  assert (Hxr : b - cf_head <= x < b - cf_head + req_size (m + cf_head)) by lia.
  split.
  + exact (blk_img_x rsegs B ARx LAWS ly S Hp W mem md _ _ x HAR Hblk Hxr).
  + pose proof (in_app_addr _ _ x Happ Hxr) as Ha. unfold app_addr, ASAN_CEIL in Ha. lia.
- destruct (frames_bounds_x rsegs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  split; [lia|]. split; [lia|]. split; [exact Hal|].
  intros x Hx.
  assert (Hxr : frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid) by lia.
  split.
  + exact (frm_img_x rsegs B ARx LAWS ly S Hp W mem md cid pos x HAR Hin Hxr).
  + pose proof (in_app_addr _ _ x Hfa Hxr) as Ha. unfold app_addr, ASAN_CEIL in Ha. lia.
- pose proof Hstk as (_ & _ & Hlo & _ & _ & Hhi47 & _).
  split; [lia|]. split; [lia|]. split; [exact Hal|].
  intros x Hx. split; [intros Hi; pose proof (HSL x Hi); lia | right; lia].
Qed.

(* the entry state *)
Lemma sma_entry_ok : st_ok rsegs (Ereg regs [w64 SHADOW_OFF]) sma_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (SMA_AT 0)) mem (seg_rom rsegs))).
Proof.
destruct HFPRE as [HPRE _].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (smak_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof sma_stk as FS. unfold ESTACK in FS.
pose proof sma_obj_bounds as OB.
destruct (sma_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & _). destruct (sma_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & _).
destruct (alx_const rsegs B ARx LAWS ly S Hp W mem md HAR) as (Kc & _ & Kg & _).
destruct SMA_GOTC as [EG EC]. rewrite EG, EC in Kg. rewrite EC in Kc.
set (E := Ereg regs [w64 SHADOW_OFF]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)).
assert (E10 : ew E 10 = w64 pa) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 pb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
rewrite restrict_mkst_fx. unfold sma_ss0. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (region_ok_stack rsegs _ _ 2 (spZ regs) (-128) E2); [lia | lia |].
    intros a Ha. apply (apresent_writable rsegs). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val sma_got_r].
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (sma_chunk_cval rsegs E _ 0 SMA_GOT (SLit SMA_CELL) SMA_CELL).
    * reflexivity.
    * lia.
    * rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kg).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val sma_cell_r].
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (sma_chunk_cval rsegs E _ 0 SMA_CELL (SOff 32 0) SHADOW_OFF).
    * rewrite smak_SOff0. exact E32.
    * unfold SHADOW_OFF; lia.
    * rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kc).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val smak_fstk sma_got_r sma_cell_r].
  try change (Ereg regs [w64 SHADOW_OFF]) with E.
  rewrite E2.
  repeat split; lia.
- unfold sma_fs0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  try change (Ereg regs [w64 SHADOW_OFF]) with E.
  rewrite E2, E10, E11, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  repeat split; lia.
Qed.

(* the two roots' shadow entries of the token runner *)
Lemma sma_shok : forall E m, ew E 10 = w64 pa -> ew E 11 = w64 pb -> ew E 32 = w64 SHADOW_OFF ->
  range_addressable (rd_of rsegs m) SHADOW_OFF pa 56 -> range_addressable (rd_of rsegs m) SHADOW_OFF pb 56 ->
  sh_ok rsegs sma_Bx sma_SH E m.
Proof.
intros E m E10 E11 E32 Ra Rb.
destruct (sma_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4). destruct (sma_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4).
assert (UB : U E sma_Bx = SHADOW_OFF) by (unfold sma_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (UA : U E (SOff 10 0) = pa) by (apply (U_atom E 10 pa E10); lia).
assert (UBb : U E (SOff 11 0) = pb) by (apply (U_atom E 11 pb E11); lia).
unfold sh_ok, sma_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UB;
  change (Z.min 0 56) with 0; change (Z.max 0 56) with 56; rewrite Z.sub_0_r.
- rewrite UA, Z.add_0_r. split; [exact Ra|]. intros a Ha. destruct (Pa4 a ltac:(lia)) as [_ Hx].
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
- rewrite UBb, Z.add_0_r. split; [exact Rb|]. intros a Ha. destruct (Pb4 a ltac:(lia)) as [_ Hx].
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* the return at SMA_AT 0x140 (`ret`), a0 symbolic: the text's post *)
Lemma sma_ret_u : forall ly1 S1 Hp1 W1 md1 k1 E1 ss ms (r : Z) (extra : list word),
  sma_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  st_ok rsegs E1 ss (restrict (w_H W1) ms) -> ss_resv ss = None -> ss_pc ss = SMA_AT 0x140 ->
  env_agree 32 (Ereg regs extra) E1 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  U E1 (sr_get (ss_regs ss) 10) = r -> sr_get (ss_regs ss) 1 = SOff 1 0 ->
  (ta = tb /\ r = 1 \/ ta <> tb /\ r = 0) ->
  SRr rsegs W1 (mkCfg ms md1) sma_POST.
Proof.
intros ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs Hr10 Hr1 Hr.
pose proof HI as (HJ & HS1 & HHp & Hbl & HL1 & HMN).
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NA NB].
pose proof HFPRE as [(HAR & Hra & _) _].
eapply (SRr_ret_at rsegs A_prog_tbl A_prog_tbl_ok HWX W1 E1 ss ms md1 _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity |].
intros mat.
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss ms 1%bv HS), Hr1, smak_SOff0.
  destruct HEA as [HA _]. rewrite (HA 1%nat ltac:(lia)). exact (ew_Ereg_nat regs extra 1 1%bv eq_refl). }
assert (R10 : getr (ms_regs ms) 10 = w64 r).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss ms 10%bv HS).
  apply bv_eq. change (bv_unsigned (sv_denot E1 (sr_get (ss_regs ss) 10))) with (U E1 (sr_get (ss_regs ss) 10)).
  assert (Hr0 : 0 <= r < 2 ^ 64) by (destruct Hr as [[_ ->] | [_ ->]]; lia).
  rewrite Hr10. unfold w64. rewrite unsigned_lit_small by exact Hr0. reflexivity. }
rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra.
unfold sma_POST, fpostm, fpost, apost_base_x.
exists ly1, S1, Hp1, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md1) mat md1), k1.
split; [reflexivity|].
split; [apply (ajournal_x_materialize rsegs B _ ARx LAWS HSL); exact HJ|].
split; [exact (aregs_preserved_of_st_ok rsegs (w_H W1) E1 ss ms regs extra HS HEA Hcs)|].
unfold fQmn, sma_Q. split; [|exact HMN].
split; [intros Hrl; rewrite HS1; exact Hrl|].
split; [destruct Hr as [[Ht ->] | [Ht ->]]; [left | right]; split; assumption|].
split; [exact NA|]. split; [exact NB|]. split; [exact HHp|]. split; [exact HS1|]. split; [exact Hbl|]. exact HL1.
Qed.
(* the same, a0 a literal *)
Lemma sma_ret : forall ly1 S1 Hp1 W1 md1 k1 E1 ss ms (r : Z) (extra : list word),
  sma_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  st_ok rsegs E1 ss (restrict (w_H W1) ms) -> ss_resv ss = None -> ss_pc ss = SMA_AT 0x140 ->
  env_agree 32 (Ereg regs extra) E1 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 10 = SLit r -> sr_get (ss_regs ss) 1 = SOff 1 0 ->
  (ta = tb /\ r = 1 \/ ta <> tb /\ r = 0) ->
  SRr rsegs W1 (mkCfg ms md1) sma_POST.
Proof.
intros ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs Hr10 Hr1 Hr.
apply (sma_ret_u ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs); [| exact Hr1 | exact Hr].
rewrite Hr10. apply U_lit. destruct Hr as [[_ ->] | [_ ->]]; lia.
Qed.

(* after a hand load (continuation names ms' mat' HS Hm): the journal through the materializing step, the shadow
   entries and the sp fact at the havocked environment, the invariant at the (same) memory *)
Ltac sma_bk HS HJ SHOK Usp HI ms' mat' Hm :=
  let HJn := fresh "HJ" in let SHn := fresh "SHOK" in let Un := fresh "Usp" in
  pose proof (sma_aj_wvb (SK := SK) rsegs B PST ARx LAWS HSL
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ) as HJn;
  rewrite <- Hm in HJn; rewrite <- Hm in HI;
  lazymatch type of SHOK with sh_ok _ ?Bx ?SH _ _ =>
  lazymatch type of HS with st_ok _ (havoc ?E0 ?K ?ws) _ (restrict (w_H ?W') _) =>
    assert (SHn : sh_ok rsegs Bx SH (havoc E0 K ws) (mrestrict (w_H W') (ms_mem ms')))
      by (rewrite Hm; apply (sh_ok_agree rsegs Bx SH K E0);
          [apply env_agree_havoc | vm_compute; reflexivity | exact SHOK]);
    assert (Un : bv_unsigned (ew (havoc E0 K ws) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp)
  end end;
  clear HJ SHOK Usp; rename HJn into HJ; rename SHn into SHOK; rename Un into Usp.
(* a run of the token runner, then the invariant at the run's memory (its memnorm keep: the run's HMNP) *)
Ltac sma_inv_after HI HJ Usp Hc' :=
  let HI1 := fresh "HI" in
  lazymatch goal with HMNP0 : forall m', _ -> frame_of _ _ _ m' -> _ |- _ =>
  lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  match goal with HF0 : frame_of _ _ ?m0 _ |- _ =>
    lazymatch m0 with mrestrict _ _ => fail | _ => idtac end;
    pose proof (sma_inv_frame _ _ _ _ _ _ _ _ _ _ _ HI (HMNP0 _) HF0 HFr0 ltac:(sma_wb Usp Hc') HJ) as HI1;
    clear HMNP0
  end end end;
  repeat match goal with H0 : frame_of _ _ _ _ |- _ => clear H0 | H0 : mem_grows _ _ |- _ => clear H0 end;
  clear HI; rename HI1 into HI.
Ltac sma_step HS HJ SHOK HI Usp FS Hc' :=
  sma_run HS HJ SHOK; [ sma_awr Usp FS | sma_inv_after HI HJ Usp Hc' ].
Ltac sma_step_to HS HJ SHOK HI Usp FS Hc' stop :=
  sma_run_to HS HJ SHOK stop; [ sma_awr Usp FS | sma_inv_after HI HJ Usp Hc' ].
(* a run to the `ret` at SMA_AT 0x140 and the post through sma_ret, with a0 = r; left: the tree fact on r *)
Ltac sma_fin HS HJ SHOK HI Usp FS Hc' HAE r :=
  sma_step HS HJ SHOK HI Usp FS Hc';
  eapply (sma_ret _ _ _ _ _ _ _ _ _ r [w64 SHADOW_OFF] HI HS);
    [vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HAE
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
(* the same through sma_ret_u, a0 symbolic; left: the value of a0 (U ... = r), then the tree fact on r *)
Ltac sma_finu HS HJ SHOK HI Usp FS Hc' HAE r :=
  sma_step HS HJ SHOK HI Usp FS Hc';
  eapply (sma_ret_u _ _ _ _ _ _ _ _ _ r [w64 SHADOW_OFF] HI HS);
    [vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HAE
    | vm_compute; reflexivity | | vm_compute; reflexivity |];
    [ lazymatch goal with |- U ?Ef (sr_get ?rs ?rr) = _ =>
        let v := eval vm_compute in (sr_get rs rr) in change (sr_get rs rr) with v end | ].
(* the common preamble of the arm lemmas: the entry facts, and the register atoms below 32 of Ex read through HAE *)
Ltac sma_pre Ex HAE :=
  pose proof HFPRE as [HPRE [HRO _]];
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
  pose proof (smak_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0);
  pose proof sma_stk as FS; unfold ESTACK in FS;
  pose proof Hceil as Hc'; rewrite FS in Hc';
  destruct (sma_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4); destruct (sma_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4);
  pose proof (sma_tag_range ta) as TRa; pose proof (sma_tag_range tb) as TRb;
  assert (B0 : bv_signed (0%bv : bv 12) = 0) by reflexivity;
  assert (E10 : ew Ex 10 = w64 pa)
    by (destruct HAE as [HA _]; rewrite (HA 10%nat ltac:(lia)), (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10);
  assert (E11 : ew Ex 11 = w64 pb)
    by (destruct HAE as [HA _]; rewrite (HA 11%nat ltac:(lia)), (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
  assert (E3 : ew Ex 3 = w64 (as_gp B))
    by (destruct HAE as [HA _]; rewrite (HA 3%nat ltac:(lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp);
  assert (E4 : ew Ex 4 = w64 (as_tp B))
    by (destruct HAE as [HA _]; rewrite (HA 4%nat ltac:(lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).

(* the number arm, from SMA_AT 0xf0: both str fields, strcmp at SMA_AT 0xf8, bcmp at SMA_AT 0x268, `seqz` and the return *)
Lemma sma_num : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex sma_ssN (restrict (w_H W) ms) ->
  sma_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs sma_Bx sma_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> tag ta = 3 ->
  SRr rsegs W (mkCfg ms md4) sma_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 HhA0 HhB0
  Etag Ht3.
sma_pre Ex HAE. pose proof HI as (HJ & _).
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
pose proof sma_pc_bounds as PCB.
(* ---- SMA_AT 0xf0 ld a0, 0(a0) / SMA_AT 0xf4 ld a1, 0(a1): the two str fields (hand loads, atoms 37 / 38) ---- *)
sma_hl_ld HS4 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 16) strA.
{ sma_regv (SOff 10 16). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh5 math5 HS5 Hm5. clear HS4.
sma_bk HS5 HJ SHOK Usp HI mh5 math5 Hm5.
sma_step HS5 HJ SHOK HI Usp FS Hc'.
sma_hl_ld HS5 (11%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (pb + 16) strB.
{ sma_regv (SOff 11 16). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r.
  destruct (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh6 math6 HS6 Hm6. clear HS5.
sma_bk HS6 HJ SHOK Usp HI mh6 math6 Hm6.
sma_step HS6 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0xf8 jal strcmp: the call at the wrapper SMA_STRCMP (ra SMA_AT 0xfc), the two numbers' texts ---- *)
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA2.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB2.
destruct (sma_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NAc HhA2 (or_introl Ht3)) as (sA & kA & HcA & ShA).
destruct (sma_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NBc HhB2 (or_introl (eq_trans (eq_sym Etag) Ht3))) as (sB & kB & HcB & ShB).
pose proof HI as (HJc & HSc & HHpc & Hblc & _). pose proof HJc as (HARc & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E6 ss6 msc HS6 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMA_STRCMP) by (vm_compute; reflexivity);
  assert (A37 : ew E6 37 = Z_to_bv 64 strA) by (rewrite ew_havoc_old by lia; apply sma_ew_new1);
  assert (A38 : ew E6 38 = Z_to_bv 64 strB) by apply sma_ew_new1;
  assert (R10 : getr (ms_regs msc) 10 = w64 strA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 10%bv HS6); sma_regv (SOff 37 0);
        rewrite smak_SOff0; exact A37);
  assert (R11 : getr (ms_regs msc) 11 = w64 strB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 11%bv HS6); sma_regv (SOff 38 0);
        rewrite smak_SOff0; exact A38);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMA_AT 0xfc))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 1%bv HS6); sma_regv (SLit (SMA_AT 0xfc)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 3%bv HS6); sma_regv (SOff 3 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 4%bv HS6); sma_regv (SOff 4 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-128)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 2%bv HS6); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -128)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-128)))) with (U E6 (SOff 2 (-128)));
        pose proof asan_consts as (AC1b & _);
        rewrite (sma_U_off E6 2 (-128) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strA kA sA HLED HARc Hblc HHpc HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strB kB sB HLED HARc Hblc HHpc HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (sma_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx A_prog_relro_lo A_prog_relro_hi LAWS HSL
    SMA_STRCMP STRCMP W
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ strA strB
    (Z.of_nat (length sA)) (Z.of_nat (length sB)) (-128) (Z_to_bv 64 (SMA_AT 0xfc)) HJc R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strA kA (Z.of_nat (length sA) + 1) HLED
      HARc Hblc HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strB kB (Z.of_nat (length sB) + 1) HLED
      HARc Hblc HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMA_AT 0xfc: the invariant, the frame kept, the symbolic state resumed (atoms 39.., a0 = atom 43) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (sma_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -128 - 2 * ESTACK) (spZ regs + -128) HI HJ3
  ltac:(unfold ESTACK in *; lia) Hfr2 Hmn2) as HI3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ3 & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  assert (HKR : Forall (region_kept rsegs E6 (ms_mem (restrict (w_H W) MSC)) (mrestrict (w_H W) mem2)) (ss_mem ss6))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof sma_obj_bounds; apply mbyte_of_aview; apply Hfr2; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ3; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  pose proof (st_ok_after_call rsegs 39 E6 ss6 (restrict (w_H W) MSC) regs2 (mrestrict (w_H W) mem2) (ss_mem ss6)
    (SMA_AT 0xfc) HS6 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 39 (SMA_AT 0xfc)) in
  change (ss_after_call ss6 (ss_mem ss6) 39 (SMA_AT 0xfc)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMA_AT 0xfc)) (mrestrict (w_H W) mem2) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (SMA_AT 0xfc)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 39 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs sma_Bx sma_SH (havoc E6 39 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
    by (destruct (sma_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply sma_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32 | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb])
end.
clear HS6 HKR HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
sma_step HS7 HJ SHOK HI Usp FS Hc'.
(* the two trees are numbers; their texts are equal exactly when strcmp answered 0 *)
assert (TA : exists bA, ta = JNum sA bA)
  by (destruct ShA as [Ea | (bA & Ea & _)]; [rewrite Ea in Ht3; cbn in Ht3; lia | exists bA; exact Ea]).
assert (TB : exists bB, tb = JNum sB bB)
  by (destruct ShB as [Eb | (bB & Eb & _)]; [rewrite Eb in Etag; cbn in Etag; lia | exists bB; exact Eb]).
assert (Ev0 : v = w64 0 <-> sA = sB) by (rewrite Hcmp; exact (sma_str_eq rsegs (w_H W) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
assert (U43 : U (ltac:(lazymatch type of HS7 with st_ok _ ?E7 _ _ => exact E7 end)) (SOff 43 0) = bv_unsigned v)
  by (unfold U; rewrite smak_SOff0; change (bv_unsigned (getr regs2 10) = bv_unsigned v); rewrite Hv; reflexivity).
(* ---- SMA_AT 0xfc beqz a0: the texts differ -> 0 ---- *)
sma_branch HS7.
2: { intros Hc HS7. rewrite branch_eq_U, U43, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  sma_fin HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hc.
  destruct TA as (bA & EA). destruct TB as (bB & EB). rewrite EA, EB in Et. injection Et as Es _.
  rewrite (proj2 Ev0 Es). reflexivity. }
intros Hc HS7. rewrite branch_eq_U, U43, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
assert (Es : sA = sB) by (apply Ev0; apply bv_eq; rewrite Hc; reflexivity).
sma_step HS7 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0x268 jal bcmp: the call at the wrapper SMA_BCMP (ra SMA_AT 0x26c), the two num fields (8 bytes) ---- *)
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAb.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBb.
pose proof HI as (HJb & HSb & HHpb & Hblb & _).
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 (restrict _ ?msb) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E7 ss7 msb HS7 eq_refl) as Hshape7;
  assert (Epc7 : ss_pc ss7 = SMA_BCMP) by (vm_compute; reflexivity);
  assert (Q10 : getr (ms_regs msb) 10 = w64 (pa + 8))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 10%bv HS7); sma_regv (SOff 10 8); unfold w64;
        apply sma_denot_off; [rewrite !ew_havoc_old by lia; exact E10 | lia | lia]);
  assert (Q11 : getr (ms_regs msb) 11 = w64 (pb + 8))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 11%bv HS7); sma_regv (SOff 11 8); unfold w64;
        apply sma_denot_off; [rewrite !ew_havoc_old by lia; exact E11 | lia | lia]);
  assert (Q12 : getr (ms_regs msb) 12 = w64 8)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 12%bv HS7); sma_regv (SLit 8); reflexivity);
  assert (Q1 : getr (ms_regs msb) 1 = Z_to_bv 64 (SMA_AT 0x26c))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 1%bv HS7); sma_regv (SLit (SMA_AT 0x26c)); reflexivity);
  assert (Q3 : getr (ms_regs msb) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 3%bv HS7); sma_regv (SOff 3 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E3);
  assert (Q4 : getr (ms_regs msb) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 4%bv HS7); sma_regv (SOff 4 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E4);
  assert (Q2 : getr (ms_regs msb) 2 = sv_denot E7 (SOff 2 (-128)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 2%bv HS7); f_equal; vm_compute; reflexivity);
  assert (Qsp : spZ (ms_regs msb) = spZ regs + -128)
    by (unfold spZ; rewrite Q2; change (bv_unsigned (sv_denot E7 (SOff 2 (-128)))) with (U E7 (SOff 2 (-128)));
        pose proof asan_consts as (AC1b & _);
        rewrite (sma_U_off E7 2 (-128) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msb into MSB
end.
(* the bcmp row's per-window premises for both num fields (SameAp_memB.sma_num_ok) *)
pose proof (sma_num_ok (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64 _ ly S Hp W regs mem md Lam peak cnt fail
  ran most own pa ta Da _ _ _ _ _ _ _ (ms_regs MSB) HAR HLED HTA HJb Hblb HHpb
  ltac:(rewrite Qsp; unfold ESTACK in *; lia) ltac:(rewrite FS; lia)) as (NA0 & NA1 & NAsrc & NAw & NAam & NAra & NAhv).
pose proof (sma_num_ok (PA := PI_prog_A) B ARx SK LAWS SMA_BMAX SMA_STK64 SMA_FR64 _ ly S Hp W regs mem md Lam peak cnt fail
  ran most own pb tb Db _ _ _ _ _ _ _ (ms_regs MSB) HAR HLED HTB HJb Hblb HHpb
  ltac:(rewrite Qsp; unfold ESTACK in *; lia) ltac:(rewrite FS; lia)) as (NB0 & NB1 & NBsrc & NBw & NBam & NBra & NBhv).
rewrite Hshape7 at 1. rewrite Epc7.
eapply SRr_bind.
{ eapply (aj_bcmp_at_xm (SK := SK) rsegs B PST ARx LAWS HSL SMA_BCMP BCMP W
    (ms_regs MSB) (ms_mem MSB) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ (pa + 8) (pb + 8) 8 (-128)
    (Z_to_bv 64 (SMA_AT 0x26c)) HJb Q10 Q11 Q12).
  all: first
    [ assumption
    | (intros _; assumption)
    | reflexivity
    | (apply ret_ok_even; vm_compute; reflexivity)
    | (intros a Ha; pose proof (NAw a Ha) as Hw; rewrite Qsp in Hw; exact Hw)
    | (intros a Ha; pose proof (NBw a Ha) as Hw; rewrite Qsp in Hw; exact Hw)
    | (unfold ESTACK in *; rewrite ?FS; lia) ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v3 & -> & HJ4 & HP3 & Hv3 & Hcmp3 & Hfr3 & Hpres3 & Hmn3).
(* ---- back at SMA_AT 0x26c: the invariant, the frame kept, the symbolic state resumed (atoms 55.., a0 = atom 59) ---- *)
pose proof (sma_inv_ecall _ _ _ _ _ _ _ mem3 md3 (spZ regs + -128 - 2 * ESTACK) (spZ regs + -128) HI HJ4
  ltac:(unfold ESTACK in *; lia) Hfr3 Hmn3) as HI5.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ4 & _).
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 _ =>
  assert (HKR4 : Forall (region_kept rsegs E7 (ms_mem (restrict (w_H W) MSB)) (mrestrict (w_H W) mem3)) (ss_mem ss7))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof sma_obj_bounds; apply mbyte_of_aview; apply Hfr3; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ4; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 _ =>
  pose proof (st_ok_after_call rsegs 55 E7 ss7 (restrict (w_H W) MSB) regs3 (mrestrict (w_H W) mem3) (ss_mem ss7)
    (SMA_AT 0x26c) HS7 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP3 r Hr)) HKR4) as HS8;
  let ss8 := eval vm_compute in (ss_after_call ss7 (ss_mem ss7) 55 (SMA_AT 0x26c)) in
  change (ss_after_call ss7 (ss_mem ss7) 55 (SMA_AT 0x26c)) with ss8 in HS8;
  change (mkst regs3 (Z_to_bv 64 (SMA_AT 0x26c)) (mrestrict (w_H W) mem3) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 (SMA_AT 0x26c)) mem3 (seg_rom rsegs))) in HS8;
  assert (Usp4 : bv_unsigned (ew (havoc E7 55 (map (getr regs3) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK4 : sh_ok rsegs sma_Bx sma_SH (havoc E7 55 (map (getr regs3) CLOB)) (mrestrict (w_H W) mem3))
    by (destruct (sma_ras _ _ _ _ _ _ _ HI5) as [Ra Rb];
        apply sma_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32 | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (A59 : ew (havoc E7 55 (map (getr regs3) CLOB)) 59 = v3)
    by (rewrite <- Hv3; exact (ew_havoc_new E7 55 (map (getr regs3) CLOB) 4 (getr regs3 10) ltac:(cbn; lia)))
end.
clear HS7 HKR4 HJ SHOK Usp HI. rename HI5 into HI. rename HJ4 into HJ. rename SHOK4 into SHOK. rename Usp4 into Usp.
(* the trees are the numbers (sA, numA) and (sB, numB); their values are equal exactly when bcmp answered 0 *)
assert (NA : ta = JNum sA numA).
{ destruct ShA as [Ea | (bA & Ea & Eb)]; [rewrite Ea in Ht3; cbn in Ht3; lia|].
  rewrite Ea. f_equal. symmetry. exact Eb. }
assert (NB : tb = JNum sB numB).
{ destruct ShB as [Eb' | (bB & Eb' & Eb)]; [rewrite Eb' in Etag; cbn in Etag; lia|].
  rewrite Eb'. f_equal. symmetry. exact Eb. }
pose proof HhAb as (_ & _ & RnA & _). pose proof HhBb as (_ & _ & RnB & _).
assert (Ev3 : v3 = w64 0 <-> numA = numB)
  by (rewrite Hcmp3; exact (sma_num_eq rsegs (w_H W) (ms_mem MSB) (pa + 8) (pb + 8) numA numB RnA RnB)).
(* ---- SMA_AT 0x26c seqz s0, a0; j SMA_AT 0x104; mv a0, s0; ret: a0 = (v3 == 0) ---- *)
destruct (Z.eq_dec (bv_unsigned v3) 0) as [Hz | Hz].
- sma_finu HS8 HJ SHOK HI Usp FS Hc' HAE 1.
  + rewrite (sma_U_seqz _ _ _ A59), Hz. reflexivity.
  + left. split; [|reflexivity]. rewrite NA, NB, Es. f_equal. apply Ev3. apply bv_eq. rewrite Hz. reflexivity.
- sma_finu HS8 HJ SHOK HI Usp FS Hc' HAE 0.
  + rewrite (sma_U_seqz _ _ _ A59). destruct (Z.eqb_spec (bv_unsigned v3) 0); [contradiction | reflexivity].
  + right. split; [|reflexivity]. intros Et. apply Hz. rewrite NA, NB in Et. injection Et as _ Enum.
    rewrite (proj2 Ev3 Enum). reflexivity.
Qed.

(* the string arm, from SMA_AT 0x24c: both str fields, strcmp at SMA_AT 0x254 (ra SMA_AT 0x258), `seqz` and the return *)
Lemma sma_str : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex sma_ssS (restrict (w_H W) ms) ->
  sma_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs sma_Bx sma_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> tag ta = 4 ->
  SRr rsegs W (mkCfg ms md4) sma_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 HhA0 HhB0
  Etag Ht4.
sma_pre Ex HAE. pose proof HI as (HJ & _).
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
pose proof sma_pc_bounds as PCB.
(* ---- SMA_AT 0x24c ld a0, 0(a0) / SMA_AT 0x250 ld a1, 0(s1): the two str fields (hand loads, atoms 37 / 38) ---- *)
sma_hl_ld HS4 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 16) strA.
{ sma_regv (SOff 10 16). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh5 math5 HS5 Hm5. clear HS4.
sma_bk HS5 HJ SHOK Usp HI mh5 math5 Hm5.
sma_step HS5 HJ SHOK HI Usp FS Hc'.
sma_hl_ld HS5 (11%bv : bv 5) (9%bv : bv 5) (0%bv : bv 12) (pb + 16) strB.
{ sma_regv (SOff 11 16). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r.
  destruct (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh6 math6 HS6 Hm6. clear HS5.
sma_bk HS6 HJ SHOK Usp HI mh6 math6 Hm6.
sma_step HS6 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0x254 jal strcmp: the call at the wrapper SMA_STRCMP (ra SMA_AT 0x258), the two strings ---- *)
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA2.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB2.
destruct (sma_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NAc HhA2 (or_intror Ht4)) as (sA & kA & HcA & ShA).
destruct (sma_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NBc HhB2 (or_intror (eq_trans (eq_sym Etag) Ht4))) as (sB & kB & HcB & ShB).
pose proof HI as (HJc & HSc & HHpc & Hblc & _). pose proof HJc as (HARc & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E6 ss6 msc HS6 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMA_STRCMP) by (vm_compute; reflexivity);
  assert (A37 : ew E6 37 = Z_to_bv 64 strA) by (rewrite ew_havoc_old by lia; apply sma_ew_new1);
  assert (A38 : ew E6 38 = Z_to_bv 64 strB) by apply sma_ew_new1;
  assert (R10 : getr (ms_regs msc) 10 = w64 strA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 10%bv HS6); sma_regv (SOff 37 0);
        rewrite smak_SOff0; exact A37);
  assert (R11 : getr (ms_regs msc) 11 = w64 strB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 11%bv HS6); sma_regv (SOff 38 0);
        rewrite smak_SOff0; exact A38);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMA_AT 0x258))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 1%bv HS6); sma_regv (SLit (SMA_AT 0x258)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 3%bv HS6); sma_regv (SOff 3 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 4%bv HS6); sma_regv (SOff 4 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-128)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 2%bv HS6); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -128)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-128)))) with (U E6 (SOff 2 (-128)));
        pose proof asan_consts as (AC1b & _);
        rewrite (sma_U_off E6 2 (-128) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strA kA sA HLED HARc Hblc HHpc HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strB kB sB HLED HARc Hblc HHpc HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (sma_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx A_prog_relro_lo A_prog_relro_hi LAWS HSL
    SMA_STRCMP STRCMP W
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ strA strB
    (Z.of_nat (length sA)) (Z.of_nat (length sB)) (-128) (Z_to_bv 64 (SMA_AT 0x258)) HJc R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strA kA (Z.of_nat (length sA) + 1) HLED
      HARc Hblc HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strB kB (Z.of_nat (length sB) + 1) HLED
      HARc Hblc HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMA_AT 0x258: the invariant, the frame kept, the symbolic state resumed (atoms 39.., a0 = atom 43) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (sma_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -128 - 2 * ESTACK) (spZ regs + -128) HI HJ3
  ltac:(unfold ESTACK in *; lia) Hfr2 Hmn2) as HI3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ3 & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  assert (HKR : Forall (region_kept rsegs E6 (ms_mem (restrict (w_H W) MSC)) (mrestrict (w_H W) mem2)) (ss_mem ss6))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof sma_obj_bounds; apply mbyte_of_aview; apply Hfr2; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ3; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  pose proof (st_ok_after_call rsegs 39 E6 ss6 (restrict (w_H W) MSC) regs2 (mrestrict (w_H W) mem2) (ss_mem ss6)
    (SMA_AT 0x258) HS6 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 39 (SMA_AT 0x258)) in
  change (ss_after_call ss6 (ss_mem ss6) 39 (SMA_AT 0x258)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMA_AT 0x258)) (mrestrict (w_H W) mem2) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (SMA_AT 0x258)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 39 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs sma_Bx sma_SH (havoc E6 39 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
    by (destruct (sma_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply sma_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32 | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (A43 : ew (havoc E6 39 (map (getr regs2) CLOB)) 43 = v)
    by (rewrite <- Hv; exact (ew_havoc_new E6 39 (map (getr regs2) CLOB) 4 (getr regs2 10) ltac:(cbn; lia)))
end.
clear HS6 HKR HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
(* the two trees are strings; they are equal exactly when strcmp answered 0 *)
assert (SA : ta = JStr sA) by (destruct ShA as [Ea | (bA & Ea & _)]; [exact Ea | rewrite Ea in Ht4; cbn in Ht4; lia]).
assert (SB : tb = JStr sB)
  by (destruct ShB as [Eb | (bB & Eb & _)]; [exact Eb | rewrite Eb in Etag; cbn in Etag; lia]).
assert (Ev0 : v = w64 0 <-> sA = sB) by (rewrite Hcmp; exact (sma_str_eq rsegs (w_H W) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
(* ---- SMA_AT 0x258 j SMA_AT 0x26c; seqz s0, a0; j SMA_AT 0x104; mv a0, s0; ret: a0 = (v == 0) ---- *)
destruct (Z.eq_dec (bv_unsigned v) 0) as [Hz | Hz].
- sma_finu HS7 HJ SHOK HI Usp FS Hc' HAE 1.
  + rewrite (sma_U_seqz _ _ _ A43), Hz. reflexivity.
  + left. split; [|reflexivity]. rewrite SA, SB. f_equal. apply Ev0. apply bv_eq. rewrite Hz. reflexivity.
- sma_finu HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  + rewrite (sma_U_seqz _ _ _ A43). destruct (Z.eqb_spec (bv_unsigned v) 0); [contradiction | reflexivity].
  + right. split; [|reflexivity]. intros Et. apply Hz. rewrite SA, SB in Et. injection Et as Es.
    rewrite (proj2 Ev0 Es). reflexivity.
Qed.

(* two empty containers with the same tag are the same tree *)
Lemma sma_empty_eq : forall t u, tag t = tag u -> (tag t = 5 \/ tag t = 6) -> sma_len t = 0 -> sma_len u = 0 -> t = u.
Proof.
intros t u Et Hc Lt Lu.
destruct t as [| | | ? ? | ? | la | ma]; destruct u as [| | | ? ? | ? | lb | mb]; cbn [tag sma_len] in *; try lia.
- destruct la; [|cbn [length] in Lt; lia]. destruct lb; [reflexivity|cbn [length] in Lu; lia].
- destruct ma; [|cbn [length] in Lt; lia]. destruct mb; [reflexivity|cbn [length] in Lu; lia].
Qed.

(* ---- the loop of the container arm, SMA_AT 0x188 .. 0x220 ---- *)
Lemma sma_its_len : forall t, (tag t = 5 \/ tag t = 6) -> Z.of_nat (length (sma_its t)) = sma_len t.
Proof. intros [| | | ? ? | ? | l | l] H; cbn [tag] in H; try lia; cbn [sma_its sma_len]; [rewrite length_map|]; reflexivity. Qed.
(* item i of a container node: its kid is a node at kids + 56 i inside the kid array (a block of Lam); an object's
   key is a C string whose pointer is the 8 bytes at keys + 8 i *)
Lemma sma_node_item : forall (H : word -> bool) (m : word -> option byte) p t D ty num str kids keys nn cap i nm u,
  pj_nodeR rsegs (mrestrict H m) (prh_lin Lam) p t D ->
  pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  nth_error (sma_its t) i = Some (nm, u) ->
  In (kids, 56 * cap) Lam /\ 56 * Z.of_nat i + 56 <= 56 * cap /\
  (exists D1, incl D1 D /\ pj_nodeR rsegs (mrestrict H m) (prh_lin Lam) (kids + 56 * Z.of_nat i) u D1) /\
  (tag t = 6 -> In (keys, 8 * cap) Lam /\ 8 * Z.of_nat i + 8 <= 8 * cap /\
     exists x k, rd_u64 rsegs (mrestrict H m) (keys + 8 * Z.of_nat i) x /\
       pj_cstrR rsegs (mrestrict H m) (prh_lin Lam) x k nm).
Proof.
intros H m p t D ty num str kids keys nn cap i nm u HN Hh Ei.
pose proof Hh as (_ & _ & _ & _ & Rk & Rks & Rn & Rc).
assert (U : forall a v w, rd_u64 rsegs (mrestrict H m) a v -> rd_u64 rsegs (mrestrict H m) a w -> v = w)
  by (intros a v w Hv Hw; exact (proj1 (sma_num_eq rsegs H m a a v w Hv Hw) (fun _ _ => eq_refl))).
destruct t as [| | | ? ? | ? | items | members]; cbn [sma_its] in Ei; try (destruct i; discriminate).
- cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & _ & _ & Rk' & Rks' & Rn' & Rc') &
    _ & _ & Hn' & Hnc & Hcap & Di & ED & HIt).
  rewrite (U _ _ _ Rk' Rk) in *. rewrite (U _ _ _ Rc' Rc) in *.
  rewrite nth_error_map in Ei. destruct (nth_error items i) as [u'|] eqn:Eu; cbn in Ei; [|discriminate].
  injection Ei as E1 E2. subst u'.
  assert (Hi : (i < length items)%nat) by (apply nth_error_Some; congruence).
  destruct Hcap as [(Hc0 & _) | (Hc0 & Hl)]; [lia|].
  split; [exact Hl|]. split; [lia|].
  split; [| intros Ht; cbn in Ht; lia].
  destruct (sma_items_nth _ items kids Di i u HIt Eu) as (D1 & Hinc & HP).
  exists D1. split; [|exact HP]. rewrite ED. apply incl_appr. exact Hinc.
- cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & _ & _ & Rk' & Rks' & Rn' & Rc') &
    _ & Hn' & Hnc & Hcap & Di & ED & HMs).
  rewrite (U _ _ _ Rk' Rk) in *. rewrite (U _ _ _ Rks' Rks) in *. rewrite (U _ _ _ Rc' Rc) in *.
  assert (Hi : (i < length members)%nat) by (apply nth_error_Some; congruence).
  destruct Hcap as [(Hc0 & _) | (Hc0 & Hl & Hlk)]; [lia|].
  destruct (sma_mems_nth rsegs _ _ _ members kids keys Di i nm u HMs Ei) as (x & k & D1 & Hinc & Hxk & Rx & Hcs & HP).
  split; [exact Hl|]. split; [lia|].
  split; [exists D1; split; [rewrite ED; apply incl_appr; exact Hinc | exact HP]|].
  intros _. split; [exact Hlk|]. split; [lia|]. exists x, k. split; [exact Rx | exact Hcs].
Qed.

(* a byte of a block of Lam: in [4096, YM05.alloc_ceiling), outside the image, apart from the shadow band *)
Lemma sma_lam_app : forall ly1 S1 Hp1 W1 mem1 md1 a k x,
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S -> In (a, k) Lam -> a <= x < a + k ->
  4096 <= x < YM05.alloc_ceiling /\ ~ in_img rsegs x /\ (x < kLowShadowBeg \/ kHighMemBeg <= x).
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 a k x HAR1 Hbl Hin Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hm0 & Hblk & _).
cbn [fst snd] in *. pose proof (@cf_head_nonneg cp) as Hc0. rewrite <- Hbl in Hblk.
destruct (alx_blocks rsegs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ HAR1 Hblk) as (_ & H4096 & Hcl & Happ & _).
assert (Hmc : 0 <= k + cf_head) by lia.
pose proof (req_size_pos (k + cf_head) Hmc) as [Hq1 Hq2].
assert (Hxr : a - cf_head <= x < a - cf_head + req_size (k + cf_head)) by lia.
split; [lia|]. split.
- exact (blk_img_x rsegs B ARx LAWS ly1 S1 Hp1 W1 mem1 md1 _ _ x HAR1 Hblk Hxr).
- pose proof (in_app_addr _ _ x Happ Hxr) as Ha. unfold app_addr, ASAN_CEIL in Ha. lia.
Qed.
(* a block of Lam is 16-aligned, and its size is below cf_malloc_max *)
Lemma sma_lam_al : forall a k, In (a, k) Lam -> a mod 16 = 0.
Proof.
intros a k Hin. pose proof HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (_ & _ & _ & Hal & _). exact Hal.
Qed.
Lemma sma_lam_size : forall a k, In (a, k) Lam -> k + cf_head < cf_malloc_max.
Proof.
intros a k Hin. pose proof HFPRE as [(HAR & _) _]. pose proof HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (_ & Hblk & _). cbn [fst snd] in Hblk.
destruct (SMA_BMAX _ _ _ _ _ _ _ _ HAR Hblk) as [_ Hlt]. exact Hlt.
Qed.
(* the token runner's shadow entry for 8 bytes at x inside a block of Lam *)
Lemma sma_slot_shent : forall E ly1 S1 Hp1 W1 mem1 md1 k1 K x a k,
  sma_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ew E K = Z_to_bv 64 x -> ew E 32 = w64 SHADOW_OFF ->
  In (a, k) Lam -> a <= x -> x + 8 <= a + k ->
  shent_ok rsegs sma_Bx E (mrestrict (w_H W1) mem1) (mkSHE K 0 8).
Proof.
intros E ly1 S1 Hp1 W1 mem1 md1 k1 K x a k HI EK E32 Hin Hax Hxk.
pose proof HI as (HJ & _ & HHp & Hbl & _). pose proof HJ as (HAR1 & _).
pose proof (sma_lam_app _ _ _ _ _ _ a k x HAR1 Hbl Hin ltac:(lia)) as (Hx0 & _ & _).
pose proof (@alloc_ceiling_lt rc) as H47.
assert (UB : U E sma_Bx = SHADOW_OFF) by (unfold sma_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (UK : U E (SOff K 0) = x) by (apply (U_atom E K x EK); lia).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UK.
change (Z.min 0 8) with 0. change (Z.max 0 8) with 8. rewrite Z.sub_0_r, Z.add_0_r.
split.
- rewrite <- (aview_rd_of rsegs).
  exact (sma_slot_ra (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
    _ _ _ _ _ _ a k x 8 HLED HAR1 Hbl HHp Hin Hax ltac:(lia) Hxk).
- intros b Hb. destruct (sma_lam_app _ _ _ _ _ _ a k b HAR1 Hbl Hin ltac:(lia)) as (_ & _ & Hab).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* the facts on atoms 2, 10, 11, 32 hold in every valuation that keeps the entry's registers and the shadow offset *)
Lemma sma_factsL : forall Ex0 regsJ r i, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF ->
  facts_ok (sma_EL Ex0 regsJ r i) sma_fs0.
Proof.
intros Ex0 regsJ r i [HA1 HA2] E32.
pose proof sma_entry_ok as (_ & _ & _ & _ & _ & _ & _ & _ & HF0). change (ss_facts sma_ss0) with sma_fs0 in HF0.
apply (facts_ok_agree 33 (Ereg regs [w64 SHADOW_OFF]) _ sma_fs0); [| vm_compute; reflexivity | exact HF0].
split.
- intros k Hk. rewrite sma_EL_low by lia.
  destruct (Nat.eq_dec k 32) as [-> | Hk'].
  + rewrite E32. symmetry. exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0).
  + apply HA1. lia.
- unfold sma_EL, havoc. cbn [ed]. exact HA2.
Qed.

(* a state at the loop head or at the kids part, re-expressed in the canonical form *)
Lemma sma_canonL : forall Ex0 Ecur ss (ms : machine_state) (H : word -> bool) pc r i,
  st_ok rsegs Ecur ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  env_agree 40 Ex0 Ecur -> ss_mem ss = sma_frameL :: tl (ss_mem ss) -> sma_fixed_ok (ss_regs ss) = true ->
  getr (ms_regs ms) 23 = Z_to_bv 64 r -> getr (ms_regs ms) 24 = Z_to_bv 64 (8 * i) ->
  getr (ms_regs ms) 25 = Z_to_bv 64 (56 * i) ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF ->
  st_ok rsegs (sma_EL Ex0 (ms_regs ms) r i) (sma_ssL pc) (restrict H ms).
Proof.
intros Ex0 Ecur ss ms H pc r i HS Hrv Hpc HA Hm Hfix R23 R24 R25 HE0 E32.
assert (HCL : env_agree 40 Ecur (sma_EL Ex0 (ms_regs ms) r i)).
{ destruct HA as [HA1 HA2]. split.
  - intros k Hk. rewrite sma_EL_low by exact Hk. symmetry. exact (HA1 k Hk).
  - unfold sma_EL, havoc. cbn [ed]. symmetry. exact HA2. }
pose proof HS as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & _).
unfold sma_ssL. apply (sma_st_ok_canon rsegs Ecur _ ss (restrict H ms) pc sma_srL sma_rsL sma_fs0 HS Hpc Hrv).
- apply regs_ok_by_cases. intros rr Hin. unfold all_regs in Hin. cbn [In] in Hin.
  change (ms_regs (restrict H ms)) with (ms_regs ms) in *.
  repeat (destruct Hin as [<- | Hin]; [sma_regcase Hregs Hfix HCL R23 R24 R25 |]). destruct Hin.
- apply (mem_ok_agree rsegs 40 Ecur); [exact HCL | vm_compute; reflexivity |].
  rewrite Hm in Hmem. exact (sma_mem_ok_hd _ _ _ _ Hmem).
- apply sma_factsL; assumption.
Qed.
(* ---- the loop of the container arm ---- *)
Section CT.
Variables (numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB : Z).
Hypothesis HhA0 : pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA.
Hypothesis HhB0 : pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB.
Hypothesis Etag : tag ta = tag tb.
Hypothesis En : nA = nB.
Hypothesis Hcont : tag ta = 5 \/ tag ta = 6.

(* a canonical state at pc with r items left and i done gives the post *)
Definition sma_LH (pc : Z) (rr i : nat) : Prop :=
  forall Ex0 (ms : machine_state) ly1 S1 Hp1 W1 md1 k1,
  st_ok rsegs (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) (sma_ssL pc) (restrict (w_H W1) ms) ->
  sma_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF -> ew Ex0 33 = Z_to_bv 64 (tag ta) ->
  SRr rsegs W1 (mkCfg ms md1) sma_POST.
(* ... when r + i = n, r > 0 and the first i items are equal *)
Definition sma_LHp (pc : Z) (rr i : nat) : Prop :=
  (rr + i)%nat = Z.to_nat nA -> (0 < rr)%nat ->
  (forall j, (j < i)%nat -> nth_error (sma_its ta) j = nth_error (sma_its tb) j) -> sma_LH pc rr i.
(* the keys of item i are equal (objects) *)
Definition sma_KE (i : nat) : Prop :=
  tag ta = 6 -> option_map fst (nth_error (sma_its ta) i) = option_map fst (nth_error (sma_its tb) i).

(* the kids part SMA_AT 0x1e8: the kids of item i through the recursive call at SMA_AT 0x208, then the next item *)
Lemma sma_kids : forall rr i, ((1 < rr)%nat -> sma_LHp (SMA_AT 0x188) (rr - 1) (Datatypes.S i)) -> sma_KE i ->
  sma_LHp (SMA_AT 0x1e8) rr i.
Proof.
intros rr i Hnext KE Hri Hr0 Hpre Ex0 ms ly1 S1 Hp1 W1 md1 k1 HS HI HE0 E32 E33.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)))
  by (unfold sma_EL; env_agree_chain HE0).
sma_pre (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) HAE.
pose proof HI as (HJ & _).
assert (Usp : bv_unsigned (ew (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) 2) = spZ regs)
  by (destruct HAE as [HA _]; rewrite (HA 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32L : ew (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) 32 = w64 SHADOW_OFF)
  by (rewrite sma_EL_low by lia; exact E32).
assert (SHOK : sh_ok rsegs sma_Bx sma_SH (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) (mrestrict (w_H W1) (ms_mem ms)))
  by (destruct (sma_ras _ _ _ _ _ _ _ HI) as [Ra Rb]; apply sma_shok; [exact E10 | exact E11 | exact E32L
      | rewrite <- (aview_rd_of rsegs); exact Ra | rewrite <- (aview_rd_of rsegs); exact Rb]).
(* ---- SMA_AT 0x1e8..0x1f4: the shadow of a + 24 and b + 24; 0x1f8 ld a0, 0(s2) / 0x1fc ld a1, 0(s1): kids ---- *)
sma_step HS HJ SHOK HI Usp FS Hc'.
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
sma_hl_ld HS (10%bv : bv 5) (18%bv : bv 5) (0%bv : bv 12) (pa + 24) kidsA.
{ sma_regv (SOff 10 24). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh1 math1 HS1 Hm1. clear HS.
sma_bk HS1 HJ SHOK Usp HI mh1 math1 Hm1.
sma_hl_ld HS1 (11%bv : bv 5) (9%bv : bv 5) (0%bv : bv 12) (pb + 24) kidsB.
{ sma_regv (SOff 11 24). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r.
  destruct (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh2 math2 HS2 Hm2. clear HS1.
sma_bk HS2 HJ SHOK Usp HI mh2 math2 Hm2.
(* ---- SMA_AT 0x200 add a0, a0, s9; 0x204 add a1, a1, s9; 0x208 jal same ---- *)
sma_step_to HS2 HJ SHOK HI Usp FS Hc' (SMA_AT 0).
(* ---- item i of both trees ---- *)
pose proof (sma_its_len ta Hcont) as LtA. pose proof (sma_its_len tb ltac:(rewrite <- Etag; exact Hcont)) as LtB.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
destruct (nth_error (sma_its ta) i) as [[nmA uA]|] eqn:EiA; [|apply nth_error_None in EiA; lia].
destruct (nth_error (sma_its tb) i) as [[nmB uB]|] eqn:EiB; [|apply nth_error_None in EiB; lia].
assert (Hnm : nmA = nmB).
{ destruct Hcont as [H5 | H6].
  - rewrite (sma_its_key5 ta i nmA uA H5 EiA), (sma_its_key5 tb i nmB uB ltac:(lia) EiB). reflexivity.
  - pose proof (KE H6) as Hk. rewrite EiA, EiB in Hk. cbn in Hk. injection Hk as Hk. exact Hk. }
pose proof (sma_its_depth _ _ _ _ EiA) as DuA.
assert (Hn1 : (1 <= n)%nat) by lia.
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc HhAk EiA) as (LkA & BkA & (D1A & IncA & NkA) & _).
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc HhBk EiB) as (LkB & BkB & (D1B & IncB & NkB) & _).
pose proof HI as (HJc & HSI & HHpI & HblI & HLI & HMNI). pose proof HJc as (HARc & _).
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 (restrict _ ?mc) => rename mc into MC end.
destruct (sma_kid_tree (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MC) kidsA (56 * capA) i uA D1A HLED HARc HblI HHpI LkA BkA NkA) as (HTkA & HfA).
destruct (sma_kid_tree (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MC) kidsB (56 * capB) i uB D1B HLED HARc HblI HHpI LkB BkB NkB) as (HTkB & HfB).
pose proof (HfA (kidsA + 56 * Z.of_nat i) ltac:(left; lia)) as HkA.
pose proof (HfB (kidsB + 56 * Z.of_nat i) ltac:(left; lia)) as HkB.
pose proof (@alloc_ceiling_lt rc) as Hac47.
pose proof HhAk as (_ & _ & _ & _ & (RkA & _) & _). pose proof HhBk as (_ & _ & _ & _ & (RkB & _) & _).
(* ---- the registers at the call ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  assert (A58 : ew E2 58 = Z_to_bv 64 (56 * Z.of_nat i)) by (rewrite !ew_havoc_old by lia; apply sma_EL_i56);
  assert (A59 : ew E2 59 = Z_to_bv 64 kidsA) by (rewrite ew_havoc_old by lia; apply sma_ew_new1);
  assert (A60 : ew E2 60 = Z_to_bv 64 kidsB) by apply sma_ew_new1;
  assert (R10 : getr (ms_regs MC) 10 = w64 (kidsA + 56 * Z.of_nat i))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 10%bv HS2); sma_regv (SAlu ALU_ADD (SOff 58 0) (SOff 59 0));
        unfold w64; rewrite (Z.add_comm kidsA); apply sma_denot_add; [exact A58 | exact A59 | lia | lia | lia]);
  assert (R11 : getr (ms_regs MC) 11 = w64 (kidsB + 56 * Z.of_nat i))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 11%bv HS2); sma_regv (SAlu ALU_ADD (SOff 58 0) (SOff 60 0));
        unfold w64; rewrite (Z.add_comm kidsB); apply sma_denot_add; [exact A58 | exact A60 | lia | lia | lia]);
  assert (R1 : getr (ms_regs MC) 1 = Z_to_bv 64 (SMA_AT 0x20c))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 1%bv HS2); sma_regv (SLit (SMA_AT 0x20c)); reflexivity);
  assert (R8 : getr (ms_regs MC) 8 = w64 1)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 8%bv HS2); sma_regv (SLit 1); reflexivity);
  assert (R3 : getr (ms_regs MC) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 3%bv HS2); sma_regv (SOff 3 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs MC) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 4%bv HS2); sma_regv (SOff 4 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs MC) 2 = sv_denot E2 (SOff 2 (-128)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 2%bv HS2); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs MC) = spZ regs + -128)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E2 (SOff 2 (-128)))) with (U E2 (SOff 2 (-128)));
        pose proof asan_consts as (AC1b & _);
        rewrite (sma_U_off E2 2 (-128) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned)
end.
(* the return pc SMA_AT 0x20c: even, at least 4096, below the ceiling (fpre's raZ conjunct of the callee) *)
assert (Hraw32 : 4096 <= bv_unsigned (Z_to_bv 64 (SMA_AT 0x20c)) < 2 ^ 32)
  by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
assert (Praw : YK0s.ret_ok (Z_to_bv 64 (SMA_AT 0x20c))) by (apply ret_ok_even; vm_compute; reflexivity).
assert (Hraw4 : 4096 <= bv_unsigned (Z_to_bv 64 (SMA_AT 0x20c))) by lia.
(* the callee's sp is 128 below ours and the journal keeps the stack top: fpre's stack-top conjunct *)
assert (HSHc : spZ (ms_regs MC) + 64 <= ly_stk_hi ly1).
{ rewrite Rsp. pose proof HFPRE as (_ & _ & Hsh & _).
  destruct HJc as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _) & _). rewrite Ehi. lia. }
(* the callee's return address is SMA_AT 0x20c, below the ceiling *)
assert (HRAc : raZ (ms_regs MC) < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1. pose proof (@alloc_ceiling_value rc) as [[Hcm _] _]. lia. }
(* the rounding mode is 0 at the callee's entry: same runs no float instruction, so it is ours (fpre's FRM0-ENTRY) *)
assert (HFRMc : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & Hfrm); exact Hfrm).
(* the callee's frame chain: s0 = 1 at the call (SMA_AT 0x0ac `li s0, 1`, never written in the loop), below the
   ceiling, so the empty chain *)
assert (Hach : achain ly1 (aview rsegs (w_H W1) (ms_mem MC)) (spZ regs + -128) (s0Z (ms_regs MC)) []).
{ apply achain_low. unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia.
  pose proof (@alloc_ceiling_value rc) as [[Hcm _] _]. lia. }
pose proof (sma_ro _ _ _ _ _ _ _ HI) as HROc.
assert (HfwA : forall z, pj_footR (kidsA + 56 * Z.of_nat i) D1A z ->
  ~ (spZ (ms_regs MC) - STK_same (n - 1) <= z < spZ (ms_regs MC))).
{ intros z Hz. pose proof (HfA z Hz). rewrite Rsp, sma_stk'. unfold ESTACK in *. lia. }
assert (HfwB : forall z, pj_footR (kidsB + 56 * Z.of_nat i) D1B z ->
  ~ (spZ (ms_regs MC) - STK_same (n - 1) <= z < spZ (ms_regs MC))).
{ intros z Hz. pose proof (HfB z Hz). rewrite Rsp, sma_stk'. unfold ESTACK in *. lia. }
(* the callee's guarded premise is vacuous: its root kidsA + 56 i is in a block of Lam, below YM05.alloc_ceiling and so
   below its sp *)
assert (HSUPc : spZ (ms_regs MC) <= kidsA + 56 * Z.of_nat i -> astack_up_x rsegs ly1 W1 (spZ (ms_regs MC)) (ms_mem MC)).
{ intros Hle. exfalso. rewrite Rsp in Hle. unfold ESTACK in *. lia. }
(* ---- SMA_AT 0x208 jal same: the call through the induction hypothesis at nesting n - 1 (aj_call_x) ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
eapply SRr_bind;
[ eapply (aj_call_x (SK := SK) rsegs B PST ARx LAWS HSL W1 E2 ss2 MC _ (spZ regs) []
    ly S Hp W mem md [] ly1 S1 Hp1 _ _ (STK_same (n - 1)) [] (-128) (ew E2 2)
    (Z_to_bv 64 (SMA_AT 0x20c)) [] _ HS2 eq_refl HJc R2 eq_refl Usp eq_refl ltac:(lia)
    ltac:(rewrite sma_stk'; unfold ESTACK; lia) ltac:(rewrite !sma_stk'; unfold ESTACK; lia) R3 R4 R1 Praw
    Hraw4 Hach);
  [ intros HPc;
    pose proof (IH (n - 1) ltac:(lia) ly1 S1 Hp1 W1 (ms_regs MC) (ms_mem MC) _ []
      (kidsA + 56 * Z.of_nat i) (kidsB + 56 * Z.of_nat i) uA uB D1A D1B Lam peak cnt fail ran most own
      (conj HPc (conj HROc (conj HSHc (conj HRAc HFRMc)))) HSUPc
      R10 R11 HTkA HTkB ltac:(lia) HfwA HfwB HLI) as HSM;
    unfold cfg_at, fpostm, fpost in HSM;
    change (pa_sigma (PAImg := PI_prog_A) AS_same) with (ss_pc ss2) in HSM; exact HSM
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W3 c3 _ (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & kc & -> & HJ3 & HJ1 & HP3 &
  ((Hrk & Hres & HnA & HnB & EHp & ES2 & Ebl & HL3) & Hmn3)).
(* ---- back at SMA_AT 0x20c: the frame kept by the callee's journal inside the caller's; the invariant at W3 ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  assert (HKR3 : Forall (region_kept rsegs E2 (ms_mem (restrict (w_H W1) MC)) (mrestrict (w_H W3) mem3)) (ss_mem ss2))
end.
{ cbn [ss_mem restrict ms_mem]. constructor; [|constructor].
  eapply (region_kept_stack_sub_x (SK := SK) rsegs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc
    2%nat (-128) 0 (-128) 0 _ (spZ regs) _ _ _ _ _ _ _ _ _ _ _ HJ1 HJ3 Usp); lia. }
assert (HI3 : sma_INV ly2 S2 Hp2 W3 mem3 md3 (k1 + kc)).
{ split; [exact HJ3|]. split; [exact (eq_trans ES2 HSI)|]. split; [exact (eq_trans EHp HHpI)|].
  split; [exact (eq_trans Ebl HblI)|]. split; [exact HL3|]. intros Hm. exact (Hmn3 (HMNI Hm)). }
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  pose proof (st_ok_after_call rsegs 61 E2 ss2 (restrict (w_H W1) MC) regs3 (mrestrict (w_H W3) mem3) (ss_mem ss2)
    (SMA_AT 0x20c) HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP3 r Hr)) HKR3) as HS3;
  let ss3 := eval vm_compute in (ss_after_call ss2 (ss_mem ss2) 61 (SMA_AT 0x20c)) in
  change (ss_after_call ss2 (ss_mem ss2) 61 (SMA_AT 0x20c)) with ss3 in HS3;
  change (mkst regs3 (Z_to_bv 64 (SMA_AT 0x20c)) (mrestrict (w_H W3) mem3) (seg_rom rsegs)) with
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (SMA_AT 0x20c)) mem3 (seg_rom rsegs))) in HS3;
  assert (Usp3 : bv_unsigned (ew (havoc E2 61 (map (getr regs3) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs sma_Bx sma_SH (havoc E2 61 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3))
    by (destruct (sma_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply sma_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32L | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (U65 : U (havoc E2 61 (map (getr regs3) CLOB)) (SOff 65 0) = bv_unsigned (getr regs3 10))
    by (unfold U; rewrite smak_SOff0; f_equal; exact (ew_havoc_new E2 61 (map (getr regs3) CLOB) 4 (getr regs3 10) ltac:(cbn; lia)))
end.
clear HS2 HKR3 HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
(* ---- SMA_AT 0x20c beqz a0: the kids differ -> 0 ---- *)
sma_branch HS3.
{ intros Hc HS3. rewrite branch_eq_U, U65, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (Hne : uA <> uB)
    by (destruct Hres as [(_ & Hv) | (Hne & _)]; [rewrite Hv in Hc; vm_compute in Hc; discriminate Hc | exact Hne]).
  sma_fin HS3 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hne. rewrite Et in EiA. rewrite EiA in EiB.
  injection EiB as _ Eu. exact Eu. }
intros Hc HS3. rewrite branch_eq_U, U65, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
assert (Heq : uA = uB)
  by (destruct Hres as [(Heq & _) | (_ & Hv)]; [exact Heq | rewrite Hv in Hc; vm_compute in Hc; congruence]).
assert (Hpre' : forall j, (j < Datatypes.S i)%nat -> nth_error (sma_its ta) j = nth_error (sma_its tb) j).
{ intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne]; [rewrite EiA, EiB, Hnm, Heq; reflexivity | apply Hpre; lia]. }
(* ---- SMA_AT 0x210..0x218: s7 - 1, s9 + 56, s8 + 8; 0x21c beqz s7: the last item -> 1 ---- *)
sma_step HS3 HJ SHOK HI Usp FS Hc'.
pose proof HhA0 as (_ & _ & _ & _ & _ & _ & (RnA & _) & _).
lazymatch type of HS3 with st_ok _ ?E3 _ _ =>
  assert (U56 : U E3 (SOff 56 (-1)) = Z.of_nat rr - 1)
    by (rewrite (sma_U_off E3 56 (-1) (Z.of_nat rr)); [lia | rewrite !ew_havoc_old by lia; apply sma_EL_r | lia | lia])
end.
sma_branch HS3.
{ intros Hc1 HS3. rewrite branch_eq_U, U56, U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1.
  sma_fin HS3 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply sma_its_inj; [exact Etag | exact Hcont |].
  apply sma_list_eq_nth; [lia |]. intros j Hj. apply Hpre'. lia. }
intros Hc1 HS3. rewrite branch_eq_U, U56, U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1.
(* ---- SMA_AT 0x220 j 0x188: the next loop head, in the canonical form ---- *)
sma_step_to HS3 HJ SHOK HI Usp FS Hc' (SMA_AT 0x188).
assert (HE40 : env_agree 40 Ex0 (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)))
  by (unfold sma_EL; apply env_agree_havoc).
lazymatch type of HS3 with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
  assert (HL' : st_ok rsegs (sma_EL Ex0 (ms_regs mb) (Z.of_nat (rr - 1)) (Z.of_nat (Datatypes.S i))) (sma_ssL (SMA_AT 0x188))
    (restrict (w_H W3) mb));
  [ apply (sma_canonL Ex0 Eb ssb mb (w_H W3) (SMA_AT 0x188) _ _ HS3); [reflexivity | vm_compute; reflexivity
      | env_agree_chain HE40 | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 23%bv HS3); sma_regv (SOff 56 (-1));
        rewrite (sma_denot_off Eb 56 (-1) (Z.of_nat rr)); [f_equal; lia | rewrite !ew_havoc_old by lia; apply sma_EL_r
          | lia | lia]
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 24%bv HS3); sma_regv (SOff 57 8);
        rewrite (sma_denot_off Eb 57 8 (8 * Z.of_nat i)); [f_equal; lia | rewrite !ew_havoc_old by lia; apply sma_EL_i8
          | lia | lia]
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 25%bv HS3); sma_regv (SOff 58 56);
        rewrite (sma_denot_off Eb 58 56 (56 * Z.of_nat i)); [f_equal; lia | rewrite !ew_havoc_old by lia; apply sma_EL_i56
          | lia | lia]
      | exact HE0 | exact E32 ]
  | apply (Hnext ltac:(lia) ltac:(lia) ltac:(lia) Hpre' Ex0 mb ly2 S2 Hp2 W3 _ _ HL' HI HE0 E32 E33) ]
end.
Qed.

(* the loop head SMA_AT 0x188: an array goes straight to its kids part; an object first compares key i *)
Lemma sma_head : forall rr i, (sma_KE i -> sma_LHp (SMA_AT 0x1e8) rr i) -> sma_LHp (SMA_AT 0x188) rr i.
Proof.
intros rr i Hkids Hri Hr0 Hpre Ex0 ms ly1 S1 Hp1 W1 md1 k1 HS HI HE0 E32 E33.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)))
  by (unfold sma_EL; env_agree_chain HE0).
sma_pre (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) HAE.
pose proof HI as (HJ & _).
assert (Usp : bv_unsigned (ew (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) 2) = spZ regs)
  by (destruct HAE as [HA _]; rewrite (HA 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32L : ew (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) 32 = w64 SHADOW_OFF)
  by (rewrite sma_EL_low by lia; exact E32).
assert (SHOK : sh_ok rsegs sma_Bx sma_SH (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) (mrestrict (w_H W1) (ms_mem ms)))
  by (destruct (sma_ras _ _ _ _ _ _ _ HI) as [Ra Rb]; apply sma_shok; [exact E10 | exact E11 | exact E32L
      | rewrite <- (aview_rd_of rsegs); exact Ra | rewrite <- (aview_rd_of rsegs); exact Rb]).
assert (HE40 : env_agree 40 Ex0 (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)))
  by (unfold sma_EL; apply env_agree_havoc).
assert (A33L : ew (sma_EL Ex0 (ms_regs ms) (Z.of_nat rr) (Z.of_nat i)) 33 = Z_to_bv 64 (tag ta))
  by (rewrite sma_EL_low by lia; exact E33).
(* ---- SMA_AT 0x188 li a0, 6; SMA_AT 0x18c bne s6, a0: an array goes to SMA_AT 0x1e8 ---- *)
sma_step HS HJ SHOK HI Usp FS Hc'.
sma_branch HS.
{ intros Hc HS. rewrite branch_ne_U, (U_atom _ 33 (tag ta) ltac:(try (rewrite !ew_havoc_old by lia); exact A33L) ltac:(lia)),
    U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  sma_step_to HS HJ SHOK HI Usp FS Hc' (SMA_AT 0x1e8).
  lazymatch type of HS with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
    assert (HL' : st_ok rsegs (sma_EL Ex0 (ms_regs mb) (Z.of_nat rr) (Z.of_nat i)) (sma_ssL (SMA_AT 0x1e8))
      (restrict (w_H W1) mb));
    [ apply (sma_canonL Ex0 Eb ssb mb (w_H W1) (SMA_AT 0x1e8) _ _ HS); [vm_compute; reflexivity | vm_compute; reflexivity
        | env_agree_chain HE40 | vm_compute; reflexivity | vm_compute; reflexivity
        | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 23%bv HS); sma_regv (SOff 56 0); rewrite smak_SOff0;
          try (rewrite !ew_havoc_old by lia); apply sma_EL_r
        | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 24%bv HS); sma_regv (SOff 57 0); rewrite smak_SOff0;
          try (rewrite !ew_havoc_old by lia); apply sma_EL_i8
        | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 25%bv HS); sma_regv (SOff 58 0); rewrite smak_SOff0;
          try (rewrite !ew_havoc_old by lia); apply sma_EL_i56
        | exact HE0 | exact E32 ]
    | apply (Hkids ltac:(intros H6; exfalso; lia) Hri Hr0 Hpre Ex0 mb ly1 S1 Hp1 W1 _ _ HL' HI HE0 E32 E33) ]
  end. }
intros Hc HS. rewrite branch_ne_U, (U_atom _ 33 (tag ta) ltac:(try (rewrite !ew_havoc_old by lia); exact A33L) ltac:(lia)),
  U_lit in Hc by lia.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Ht6.
(* ---- an object: key i ---- *)
pose proof (sma_its_len ta Hcont) as LtA. pose proof (sma_its_len tb ltac:(rewrite <- Etag; exact Hcont)) as LtB.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
destruct (nth_error (sma_its ta) i) as [[nmA uA]|] eqn:EiA; [|apply nth_error_None in EiA; lia].
destruct (nth_error (sma_its tb) i) as [[nmB uB]|] eqn:EiB; [|apply nth_error_None in EiB; lia].
pose proof (@alloc_ceiling_lt rc) as Hac47.
(* ---- SMA_AT 0x190..0x198: the shadow of a + 32, a + 32 from 16(sp); SMA_AT 0x19c ld a0, 0(a0): keys of a (hand
   load) ---- *)
sma_step HS HJ SHOK HI Usp FS Hc'.
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
sma_hl_ld HS (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 32) keysA.
{ sma_regv (SOff 10 32). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh1 math1 HS1 Hm1. clear HS.
sma_bk HS1 HJ SHOK Usp HI mh1 math1 Hm1.
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc HhAk EiA) as (_ & _ & _ & HkeyA).
destruct (HkeyA Ht6) as (LkeyA & BkeyA & _ & _ & _ & _).
pose proof HI as (HJc & _ & HHpc & Hblc & _). pose proof HJc as (HARc & _).
pose proof (sma_lam_app _ _ _ _ _ _ keysA (8 * capA) (keysA + 8 * Z.of_nat i) HARc Hblc LkeyA ltac:(lia))
  as (HsA & _ & _).
pose proof (sma_lam_app _ _ _ _ _ _ keysA (8 * capA) (keysA + 8 * Z.of_nat i + 7) HARc Hblc LkeyA ltac:(lia))
  as (HsA7 & _ & _).
pose proof HhAk as (_ & _ & _ & _ & _ & (RksA & _) & _).
(* ---- SMA_AT 0x1a0 add a0, a0, s8: the slot of key i of a, named (atom 60) with its shadow entry ---- *)
sma_step_to HS1 HJ SHOK HI Usp FS Hc' (SMA_AT 0x1a4).
lazymatch type of HS1 with st_ok _ ?E1 ?ss1 (restrict _ ?m1) =>
  pose proof (sma_rebind E1 ss1 (w_H W1) m1 60 10%bv (Z_to_bv 64 (keysA + 8 * Z.of_nat i)) HS1 eq_refl
    ltac:(vm_compute; reflexivity) eq_refl
    ltac:(rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss1 m1 10%bv HS1);
          sma_regv (SAlu ALU_ADD (SOff 57 0) (SOff 59 0)); rewrite (Z.add_comm keysA);
          apply sma_denot_add; [rewrite !ew_havoc_old by lia; apply sma_EL_i8
            | try (rewrite !ew_havoc_old by lia); apply sma_ew_new1 | lia | lia | lia])) as HSr;
  let ssr := eval vm_compute in (set_regs_pc ss1 [(10%bv, SOff 60 0)] (ss_pc ss1)) in
  change (set_regs_pc ss1 [(10%bv, SOff 60 0)] (ss_pc ss1)) with ssr in HSr;
  pose proof (sma_st_ok_add_atom rsegs _ _ _ 60 (mkAF 4096 (2 ^ 47 - 8) 0) HSr
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite sma_ew_new1, unsigned_lit_small by lia;
          change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)) as HSr2;
  let ssr2 := eval vm_compute in (add_atom ssr 60 (mkAF 4096 (2 ^ 47 - 8) 0)) in
  change (add_atom ssr 60 (mkAF 4096 (2 ^ 47 - 8) 0)) with ssr2 in HSr2;
  assert (Uspr : bv_unsigned (ew (havoc E1 60 [Z_to_bv 64 (keysA + 8 * Z.of_nat i)]) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOKr : sh_ok rsegs sma_Bx (sma_SH ++ [mkSHE 60 0 8]) (havoc E1 60 [Z_to_bv 64 (keysA + 8 * Z.of_nat i)])
    (mrestrict (w_H W1) (ms_mem m1)))
    by (unfold sh_ok; apply Forall_app; split;
        [ apply (sh_ok_agree rsegs sma_Bx sma_SH 60 E1); [apply env_agree_havoc | vm_compute; reflexivity | exact SHOK]
        | apply Forall_cons; [| apply Forall_nil];
          apply (sma_slot_shent _ _ _ _ _ _ _ _ 60 (keysA + 8 * Z.of_nat i) keysA (8 * capA) HI);
          [apply sma_ew_new1 | rewrite !ew_havoc_old by lia; exact E32L | exact LkeyA | lia | lia] ])
end.
clear HS1 HSr SHOK Usp. rename HSr2 into HS1. rename SHOKr into SHOK. rename Uspr into Usp.
(* ---- SMA_AT 0x1a4..0x1b8: the shadow of the slot and of b + 32; b + 32 from 8(sp); SMA_AT 0x1c0 ld a1, 0(a1): keys
   of b ---- *)
sma_step HS1 HJ SHOK HI Usp FS Hc'.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
sma_hl_ld HS1 (11%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (pb + 32) keysB.
{ sma_regv (SOff 11 32). apply sma_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhBc as (_ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh2 math2 HS2 Hm2. clear HS1.
sma_bk HS2 HJ SHOK Usp HI mh2 math2 Hm2.
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc2 NBc2].
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc2 HhBk EiB) as (_ & _ & _ & HkeyB).
destruct (HkeyB ltac:(lia)) as (LkeyB & BkeyB & _ & _ & _ & _).
pose proof HI as (HJc2 & _ & HHpc2 & Hblc2 & _). pose proof HJc2 as (HARc2 & _).
pose proof (sma_lam_app _ _ _ _ _ _ keysB (8 * capB) (keysB + 8 * Z.of_nat i) HARc2 Hblc2 LkeyB ltac:(lia))
  as (HsB & _ & _).
pose proof (sma_lam_app _ _ _ _ _ _ keysB (8 * capB) (keysB + 8 * Z.of_nat i + 7) HARc2 Hblc2 LkeyB ltac:(lia))
  as (HsB7 & _ & _).
pose proof HhBk as (_ & _ & _ & _ & _ & (RksB & _) & _).
(* ---- SMA_AT 0x1c4 add a1, a1, s8: the slot of key i of b, named (atom 62) with its shadow entry ---- *)
sma_step_to HS2 HJ SHOK HI Usp FS Hc' (SMA_AT 0x1c8).
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 (restrict _ ?m2) =>
  pose proof (sma_rebind E2 ss2 (w_H W1) m2 62 11%bv (Z_to_bv 64 (keysB + 8 * Z.of_nat i)) HS2 eq_refl
    ltac:(vm_compute; reflexivity) eq_refl
    ltac:(rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 m2 11%bv HS2);
          sma_regv (SAlu ALU_ADD (SOff 57 0) (SOff 61 0)); rewrite (Z.add_comm keysB);
          apply sma_denot_add; [rewrite !ew_havoc_old by lia; apply sma_EL_i8
            | try (rewrite !ew_havoc_old by lia); apply sma_ew_new1 | lia | lia | lia])) as HSr;
  let ssr := eval vm_compute in (set_regs_pc ss2 [(11%bv, SOff 62 0)] (ss_pc ss2)) in
  change (set_regs_pc ss2 [(11%bv, SOff 62 0)] (ss_pc ss2)) with ssr in HSr;
  pose proof (sma_st_ok_add_atom rsegs _ _ _ 62 (mkAF 4096 (2 ^ 47 - 8) 0) HSr
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite sma_ew_new1, unsigned_lit_small by lia;
          change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)) as HSr2;
  let ssr2 := eval vm_compute in (add_atom ssr 62 (mkAF 4096 (2 ^ 47 - 8) 0)) in
  change (add_atom ssr 62 (mkAF 4096 (2 ^ 47 - 8) 0)) with ssr2 in HSr2;
  assert (Uspr : bv_unsigned (ew (havoc E2 62 [Z_to_bv 64 (keysB + 8 * Z.of_nat i)]) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOKr : sh_ok rsegs sma_Bx ((sma_SH ++ [mkSHE 60 0 8]) ++ [mkSHE 62 0 8])
    (havoc E2 62 [Z_to_bv 64 (keysB + 8 * Z.of_nat i)]) (mrestrict (w_H W1) (ms_mem m2)))
    by (unfold sh_ok; apply Forall_app; split;
        [ apply (sh_ok_agree rsegs sma_Bx (sma_SH ++ [mkSHE 60 0 8]) 62 E2);
            [apply env_agree_havoc | vm_compute; reflexivity | exact SHOK]
        | apply Forall_cons; [| apply Forall_nil];
          apply (sma_slot_shent _ _ _ _ _ _ _ _ 62 (keysB + 8 * Z.of_nat i) keysB (8 * capB) HI);
          [apply sma_ew_new1 | rewrite !ew_havoc_old by lia; exact E32L | exact LkeyB | lia | lia] ])
end.
clear HS2 HSr SHOK Usp. rename HSr2 into HS2. rename SHOKr into SHOK. rename Uspr into Usp.
(* ---- SMA_AT 0x1c8..0x1d4: the shadow of b's slot; SMA_AT 0x1d8 ld a0, 0(a0) / SMA_AT 0x1dc ld a1, 0(a1): the key
   pointers ---- *)
sma_step HS2 HJ SHOK HI Usp FS Hc'.
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc3 NBc3].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk3.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc3 HhAk3 EiA) as (_ & _ & _ & HkeyA3).
destruct (HkeyA3 Ht6) as (_ & _ & xA' & kA' & RxA' & HcA').
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk3.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc3 HhBk3 EiB) as (_ & _ & _ & HkeyB3).
destruct (HkeyB3 ltac:(lia)) as (_ & _ & xB' & kB' & RxB' & HcB').
sma_hl_ld HS2 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (keysA + 8 * Z.of_nat i) xA'.
{ sma_regv (SOff 60 0). rewrite smak_SOff0. try (rewrite !ew_havoc_old by lia). apply sma_ew_new1. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct RxA' as (_ & Hv). exact Hv. }
{ destruct RxA' as (Hv & _). exact Hv. }
intros mh3 math3 HS3 Hm3. clear HS2.
sma_bk HS3 HJ SHOK Usp HI mh3 math3 Hm3.
sma_hl_ld HS3 (11%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (keysB + 8 * Z.of_nat i) xB'.
{ sma_regv (SOff 62 0). rewrite smak_SOff0. try (rewrite !ew_havoc_old by lia). apply sma_ew_new1. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. rewrite Hm3. destruct RxB' as (_ & Hv). exact Hv. }
{ destruct RxB' as (Hv & _). exact Hv. }
intros mh4 math4 HS4 Hm4. clear HS3.
sma_bk HS4 HJ SHOK Usp HI mh4 math4 Hm4.
(* ---- SMA_AT 0x1e0 jal strcmp: the run keeps every byte below YM05.alloc_ceiling (the key slots, the key strings) ---- *)
rewrite <- Hm3, <- Hm4 in RxA', RxB'.
sma_run HS4 HJ SHOK; [ sma_awr Usp FS | ].
lazymatch goal with HFr0 : frame_of ?Ef ?rsf (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  pose proof (smak_frame_below rsegs Ef rsf (w_H W1) m0 m1 HFr0 ltac:(sma_wb Usp Hc')) as HBk;
  assert (RxA2 : rd_u64 rsegs (mrestrict (w_H W1) m1) (keysA + 8 * Z.of_nat i) xA')
    by (destruct RxA' as (Hr & Hv); split; [exact Hr|];
        apply (smak_val_mem_keep (PA := PI_prog_A) _ _ _ _ _ Hv); intros q Hq; apply HBk; lia);
  assert (RxB2 : rd_u64 rsegs (mrestrict (w_H W1) m1) (keysB + 8 * Z.of_nat i) xB')
    by (destruct RxB' as (Hr & Hv); split; [exact Hr|];
        apply (smak_val_mem_keep (PA := PI_prog_A) _ _ _ _ _ Hv); intros q Hq; apply HBk; lia)
end.
sma_inv_after HI HJ Usp Hc'.
(* the two keys at the current memory: their pointers are the loaded xA', xB' *)
destruct (sma_nodes _ _ _ _ _ _ _ HI) as [NAc4 NBc4].
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk4.
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk4.
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc4 HhAk4 EiA) as (_ & _ & _ & HkeyA4).
destruct (HkeyA4 Ht6) as (_ & _ & xA & kA & RxA & HcA).
destruct (sma_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc4 HhBk4 EiB) as (_ & _ & _ & HkeyB4).
destruct (HkeyB4 ltac:(lia)) as (_ & _ & xB & kB & RxB & HcB).
assert (ExA : xA = xA') by exact (proj1 (sma_num_eq rsegs _ _ _ _ xA xA' RxA RxA2) (fun _ _ => eq_refl)).
assert (ExB : xB = xB') by exact (proj1 (sma_num_eq rsegs _ _ _ _ xB xB' RxB RxB2) (fun _ _ => eq_refl)).
subst xA' xB'.
pose proof HI as (HJk & HSk & HHpk & Hblk & _). pose proof HJk as (HARk & _).
lazymatch type of HS4 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) E6 ss6 msc HS4 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMA_STRCMP) by (vm_compute; reflexivity);
  assert (R10 : getr (ms_regs msc) 10 = w64 xA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 10%bv HS4); sma_regv (SOff 63 0);
        rewrite smak_SOff0; try (rewrite !ew_havoc_old by lia); apply sma_ew_new1);
  assert (R11 : getr (ms_regs msc) 11 = w64 xB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 11%bv HS4); sma_regv (SOff 64 0);
        rewrite smak_SOff0; try (rewrite !ew_havoc_old by lia); apply sma_ew_new1);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMA_AT 0x1e4))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 1%bv HS4); sma_regv (SLit (SMA_AT 0x1e4)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 3%bv HS4); sma_regv (SOff 3 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 4%bv HS4); sma_regv (SOff 4 0);
        rewrite smak_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-128)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 2%bv HS4); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -128)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-128)))) with (U E6 (SOff 2 (-128)));
        pose proof asan_consts as (AC1b & _);
        rewrite (sma_U_off E6 2 (-128) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) xA kA nmA HLED HARk Hblk HHpk HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (sma_str_ok (PA := PI_prog_A) B ARx LAWS SMA_BMAX SMA_STK64 SMA_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) xB kB nmB HLED HARk Hblk HHpk HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (sma_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx A_prog_relro_lo A_prog_relro_hi LAWS HSL
    SMA_STRCMP STRCMP W1
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 _ _ xA xB
    (Z.of_nat (length nmA)) (Z.of_nat (length nmB)) (-128) (Z_to_bv 64 (SMA_AT 0x1e4)) HJk R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ xA kA (Z.of_nat (length nmA) + 1) HLED
      HARk Hblk HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (sma_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ xB kB (Z.of_nat (length nmB) + 1) HLED
      HARk Hblk HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMA_AT 0x1e4: the invariant, the frame kept, the symbolic state resumed (atoms 65.., a0 = atom 69) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (sma_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -128 - 2 * ESTACK) (spZ regs + -128) HI HJ3
  ltac:(unfold ESTACK in *; lia) Hfr2 Hmn2) as HI3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ3 & _).
lazymatch type of HS4 with st_ok _ ?E6 ?ss6 _ =>
  assert (HKR : Forall (region_kept rsegs E6 (ms_mem (restrict (w_H W1) MSC)) (mrestrict (w_H W1) mem2)) (ss_mem ss6))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      apply mbyte_of_aview; apply Hfr2; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ3; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS4 with st_ok _ ?E6 ?ss6 _ =>
  pose proof (st_ok_after_call rsegs 65 E6 ss6 (restrict (w_H W1) MSC) regs2 (mrestrict (w_H W1) mem2) (ss_mem ss6)
    (SMA_AT 0x1e4) HS4 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 65 (SMA_AT 0x1e4)) in
  change (ss_after_call ss6 (ss_mem ss6) 65 (SMA_AT 0x1e4)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMA_AT 0x1e4)) (mrestrict (w_H W1) mem2) (seg_rom rsegs)) with
    (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 (SMA_AT 0x1e4)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 65 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs sma_Bx sma_SH (havoc E6 65 (map (getr regs2) CLOB)) (mrestrict (w_H W1) mem2))
    by (destruct (sma_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply sma_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32L | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (U69 : U (havoc E6 65 (map (getr regs2) CLOB)) (SOff 69 0) = bv_unsigned v)
    by (unfold U; rewrite smak_SOff0; rewrite <- Hv;
        f_equal; exact (ew_havoc_new E6 65 (map (getr regs2) CLOB) 4 (getr regs2 10) ltac:(cbn; lia)))
end.
clear HS4 HKR HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
assert (Ev0 : v = w64 0 <-> nmA = nmB)
  by (rewrite Hcmp; exact (sma_str_eq rsegs (w_H W1) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
(* ---- SMA_AT 0x1e4 bnez a0: the keys differ -> 0 ---- *)
sma_branch HS7.
{ intros Hc HS7. rewrite branch_ne_U, U69, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  sma_fin HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hc.
  assert (Hnm : nmA = nmB) by (rewrite Et in EiA; rewrite EiA in EiB; injection EiB as Enm _; exact Enm).
  rewrite (proj2 Ev0 Hnm). reflexivity. }
intros Hc HS7. rewrite branch_ne_U, U69, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
assert (Hnm : nmA = nmB) by (apply Ev0; apply bv_eq; rewrite Hc; reflexivity).
(* ---- to the kids part SMA_AT 0x1e8, in the canonical form ---- *)
sma_step_to HS7 HJ SHOK HI Usp FS Hc' (SMA_AT 0x1e8).
lazymatch type of HS7 with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
  assert (HL' : st_ok rsegs (sma_EL Ex0 (ms_regs mb) (Z.of_nat rr) (Z.of_nat i)) (sma_ssL (SMA_AT 0x1e8))
    (restrict (w_H W1) mb));
  [ apply (sma_canonL Ex0 Eb ssb mb (w_H W1) (SMA_AT 0x1e8) _ _ HS7); [vm_compute; reflexivity | vm_compute; reflexivity
      | env_agree_chain HE40 | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 23%bv HS7); sma_regv (SOff 56 0); rewrite smak_SOff0;
        try (rewrite !ew_havoc_old by lia); apply sma_EL_r
      | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 24%bv HS7); sma_regv (SOff 57 0); rewrite smak_SOff0;
        try (rewrite !ew_havoc_old by lia); apply sma_EL_i8
      | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 25%bv HS7); sma_regv (SOff 58 0); rewrite smak_SOff0;
        try (rewrite !ew_havoc_old by lia); apply sma_EL_i56
      | exact HE0 | exact E32 ]
  | apply (Hkids ltac:(intros _; rewrite EiA, EiB; cbn; f_equal; exact Hnm) Hri Hr0 Hpre Ex0 mb ly1 S1 Hp1 W1 _ _ HL' HI
      HE0 E32 E33) ]
end.
Qed.

Lemma sma_loop : forall rr i, sma_LHp (SMA_AT 0x188) rr i.
Proof.
induction rr as [|rr IHr]; intros i.
- intros _ Hr0. lia.
- apply sma_head. intros KE. apply sma_kids; [|exact KE].
  intros Hlt. replace (Datatypes.S rr - 1)%nat with rr by lia. apply IHr.
Qed.
End CT.

(* the container arm, from SMA_AT 0x144: n = 0 -> 1, else the loop from SMA_AT 0x188 (sma_loop) *)
Lemma sma_cont : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex sma_ssC (restrict (w_H W) ms) ->
  sma_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs sma_Bx sma_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF -> ew Ex 33 = Z_to_bv 64 (tag ta) ->
  ew Ex 35 = Z_to_bv 64 nA -> ew Ex 36 = Z_to_bv 64 nB ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> nA = nB -> (tag ta = 5 \/ tag ta = 6) ->
  SRr rsegs W (mkCfg ms md4) sma_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 A33' A35 A36
  HhA0 HhB0 Etag En Hcont.
sma_pre Ex HAE. pose proof HI as (HJ & _).
pose proof HhA0 as (_ & _ & _ & _ & _ & _ & (RnA & _) & _).
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
(* ---- SMA_AT 0x144 beqz s7 (s7 = n): no items -> 1 ---- *)
sma_branch HS4.
{ intros Hc HS4. rewrite branch_eq_U, (U_atom _ 35 nA A35 ltac:(lia)), U_lit in Hc by lia.
  apply Z.eqb_eq in Hc.
  sma_fin HS4 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply sma_empty_eq; [exact Etag | exact Hcont | lia | lia]. }
intros Hc HS4. rewrite branch_eq_U, (U_atom _ 35 nA A35 ltac:(lia)), U_lit in Hc by lia.
apply Z.eqb_neq in Hc. rename Hc into Hn0.
(* ---- SMA_AT 0x148 .. 0x184: the loop's set-up, to the loop head SMA_AT 0x188 ---- *)
sma_step_to HS4 HJ SHOK HI Usp FS Hc' (SMA_AT 0x188).
(* the first arrival at the loop head, in the canonical form: r = n, i = 0 *)
lazymatch type of HS4 with st_ok _ ?E4 ?ss4 (restrict _ ?msL) =>
  assert (HL0 : st_ok rsegs (sma_EL Ex (ms_regs msL) nA 0) (sma_ssL (SMA_AT 0x188)) (restrict (w_H W) msL));
  [ apply (sma_canonL Ex E4 ss4 msL (w_H W) (SMA_AT 0x188) nA 0 HS4); [vm_compute; reflexivity | vm_compute; reflexivity
      | env_agree_chain (env_agree_refl 40 Ex) | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 23%bv HS4); sma_regv (SOff 35 0);
        rewrite smak_SOff0; try (rewrite !ew_havoc_old by lia); exact A35
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 24%bv HS4); sma_regv (SLit 0); reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 25%bv HS4); sma_regv (SLit 0); reflexivity
      | exact HAE | exact E32 ]
  | eapply (sma_loop numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HhA0 HhB0 Etag En Hcont (Z.to_nat nA) 0
      ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) Ex msL ly S Hp W);
    [ rewrite Z2Nat.id by lia; exact HL0 | exact HI | exact HAE | exact E32 | exact A33' ] ]
end.
Qed.

(* the dispatch on the tag from SMA_AT 0xb4: the scalar arm (tag <= 2 -> 1) here, the number arm sma_num, the string arm
   sma_str, the container arm sma_cont *)
Lemma sma_disp : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex sma_ssD (restrict (w_H W) ms) ->
  sma_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs sma_Bx sma_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF -> ew Ex 33 = Z_to_bv 64 (tag ta) ->
  ew Ex 35 = Z_to_bv 64 nA -> ew Ex 36 = Z_to_bv 64 nB ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> nA = nB ->
  SRr rsegs W (mkCfg ms md4) sma_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 A33' A35 A36
  HhA0 HhB0 Etag En.
sma_pre Ex HAE. pose proof HI as (HJ & _).
assert (Ht7 : tag ta = 0 \/ tag ta = 1 \/ tag ta = 2 \/ tag ta = 3 \/ tag ta = 4 \/ tag ta = 5 \/ tag ta = 6) by lia.
assert (Ut5 : U Ex (SOff 33 (-5)) = (tag ta - 5) mod 2 ^ 64).
{ unfold U. rewrite denot_SOff, A33', unsigned_lit_small by lia. unfold zcanon, M64, bv_wrap. reflexivity. }
(* ---- SMA_AT 0xb4 bgeu s0, a0 (s0 = 1, a0 = tag - 5): an array or an object ---- *)
sma_branch HS4.
{ intros Hc HS4. rewrite branch_geu_U, U_lit, Ut5 in Hc by lia.
  assert (Hcont : tag ta = 5 \/ tag ta = 6)
    by (destruct Ht7 as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]; rewrite Ht in Hc |- *; vm_compute in Hc; first [discriminate Hc | lia]).
  clear Hc.
  sma_step HS4 HJ SHOK HI Usp FS Hc'.
  lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
    assert (HS4' : st_ok sg Ey sma_ssC m) by (replace sma_ssC with ss by (vm_compute; reflexivity); exact HS4) end.
  exact (sma_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
    ltac:(try (rewrite !ew_havoc_old by lia); exact E32) A33' A35 A36 HhA0 HhB0 Etag En Hcont). }
intros Hc HS4. rewrite branch_geu_U, U_lit, Ut5 in Hc by lia.
assert (Hle4 : tag ta <= 4)
  by (destruct Ht7 as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]; rewrite Ht in Hc |- *; vm_compute in Hc; first [discriminate Hc | lia]).
clear Hc.
sma_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0xbc beq s6, a0 (a0 = 4): a string ---- *)
sma_branch HS4.
{ intros Hc HS4. rewrite branch_eq_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
  apply Z.eqb_eq in Hc. rename Hc into Ht4.
  sma_step HS4 HJ SHOK HI Usp FS Hc'.
  lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
    assert (HS4' : st_ok sg Ey sma_ssS m) by (replace sma_ssS with ss by (vm_compute; reflexivity); exact HS4) end.
  exact (sma_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
    ltac:(try (rewrite !ew_havoc_old by lia); exact E32) HhA0 HhB0 Etag Ht4). }
intros Hc HS4. rewrite branch_eq_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
apply Z.eqb_neq in Hc. rename Hc into Hn4.
sma_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0xc4 bne s6, a0 (a0 = 3): null, false or true -> 1 ---- *)
sma_branch HS4.
{ intros Hc HS4. rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  sma_fin HS4 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply sma_tag_scalar; [exact Etag | lia]. }
intros Hc HS4. rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Ht3.
(* ---- the number arm ---- *)
sma_step HS4 HJ SHOK HI Usp FS Hc'.
lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
  assert (HS4' : st_ok sg Ey sma_ssN m) by (replace sma_ssN with ss by (vm_compute; reflexivity); exact HS4) end.
exact (sma_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
  ltac:(try (rewrite !ew_havoc_old by lia); exact E32) HhA0 HhB0 Etag Ht3).
Qed.


(* the entry: both tags, both n fields, then the dispatch *)
Theorem sma_same_entry : SRr rsegs W (cfg_at rsegs (pa_sigma (PAImg := PI_prog_A) AS_same) regs mem md) sma_POST.
Proof.
pose proof HFPRE as [HPRE [HRO _]].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (smak_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof sma_stk as FS. unfold ESTACK in FS.
pose proof Hceil as Hc'. rewrite FS in Hc'.
assert (EPC : pa_sigma (PAImg := PI_prog_A) AS_same = SMA_AT 0) by (unfold SMA_AT; vm_compute; reflexivity).
unfold cfg_at. rewrite EPC. change (w64 (SMA_AT 0)) with (Z_to_bv 64 (SMA_AT 0)).
pose proof sma_entry_ok as HS.
pose proof (ajournal_x_init (SK := SK) rsegs B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
set (E := Ereg regs [w64 SHADOW_OFF]) in HS.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)).
assert (E10 : ew E 10 = w64 pa) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 pb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (SHOK : sh_ok rsegs sma_Bx sma_SH E (mrestrict (w_H W) mem)).
{ apply sma_shok; [exact E10 | exact E11 | exact E32 | |]; rewrite <- (aview_rd_of rsegs);
    [exact (proj1 (proj2 (proj2 HTA))) | exact (proj1 (proj2 (proj2 HTB)))]. }
(* ---- SMA_AT 0x0 .. 0x64: the frame, the shadow base from the .got, both roots' shadow checks ---- *)
sma_run HS HJ SHOK.
{ sma_awr E2 FS. }
(* ---- the two roots' headers, named at the entry ---- *)
destruct (sma_hdr_of_node _ _ _ _ _ (proj1 HTA)) as (numA & strA & kidsA & keysA & nA & capA & HhA0).
destruct (sma_hdr_of_node _ _ _ _ _ (proj1 HTB)) as (numB & strB & kidsB & keysB & nB & capB & HhB0).
destruct (sma_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4). destruct (sma_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4).
assert (B0 : bv_signed (0%bv : bv 12) = 0) by reflexivity.
(* ---- the invariant after the first run: the run wrote only the frame, above YM05.alloc_ceiling ---- *)
assert (HI : sma_INV ly S Hp W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) 0).
{ split; [exact HJ|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - apply (smak_ledger_keep (PA := PI_prog_A) B ARx LAWS ly S Hp W mem md (ms_mem ms) Lam peak cnt fail ran most own
      HAR HLED).
    intros a Ha. refine (smak_frame_below rsegs E _ (w_H W) mem (ms_mem ms) HFr _ a Ha).
    intros x (r & Hin & Hx). vm_compute in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
      try rewrite E2 in Hx; lia|]). destruct Hin.
  - intros Hm. exact (HMNP _ Hm HF). }
clear HF HFr HG HMNP.
(* ---- SMA_AT 0x68 lw s6, 0(s2): the tag of a (hand load, atom 33; s2 = a) ---- *)
sma_hl_lw HS (22%bv : bv 5) (18%bv : bv 5) pa (tag ta).
{ sma_regv (SOff 10 0). rewrite smak_SOff0, E10. reflexivity. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as (_ & (_ & Hv) & _).
  exact Hv. }
{ pose proof (sma_tag_range ta). lia. }
intros ms1 mat1 HS1 Hm1. clear HS.
pose proof E2 as Usp.
sma_bk HS1 HJ SHOK Usp HI ms1 mat1 Hm1.
(* ---- SMA_AT 0x6c: b's shadow check, decided in the run ---- *)
sma_step HS1 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0x70 lw a0, 0(s1): the tag of b (hand load, atom 34; s1 = b) ---- *)
sma_hl_lw HS1 (10%bv : bv 5) (9%bv : bv 5) pb (tag tb).
{ sma_regv (SOff 11 0). rewrite smak_SOff0, ew_havoc_old by lia. rewrite E11. reflexivity. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & (_ & Hv) & _).
  exact Hv. }
{ pose proof (sma_tag_range tb). lia. }
intros ms2 mat2 HS2 Hm2. clear HS1.
sma_bk HS2 HJ SHOK Usp HI ms2 mat2 Hm2.
sma_step HS2 HJ SHOK HI Usp FS Hc'.
lazymatch type of HS2 with st_ok _ ?E2' _ _ =>
  assert (A33 : ew E2' 33 = Z_to_bv 64 (tag ta)) by (rewrite ew_havoc_old by lia; apply sma_ew_new1);
  assert (A34 : ew E2' 34 = Z_to_bv 64 (tag tb)) by apply sma_ew_new1
end.
pose proof (sma_tag_range ta) as TRa. pose proof (sma_tag_range tb) as TRb.
(* ---- SMA_AT 0x74 bne s6, a0: the tags differ -> 0 ---- *)
sma_branch HS2.
{ intros Hc HS2.
  rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33 ltac:(lia)), (U_atom _ 34 (tag tb) A34 ltac:(lia)) in Hc.
  sma_fin HS2 HJ SHOK HI Usp FS Hc' (env_agree_refl 32 E) 0.
  right. split; [|reflexivity]. intros ->. rewrite Z.eqb_refl in Hc. discriminate Hc. }
intros Hc HS2.
rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33 ltac:(lia)), (U_atom _ 34 (tag tb) A34 ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Etag.
(* ---- SMA_AT 0x78 .. 0x9c: the shadow checks of a + 40 and b + 40, decided in the run ---- *)
sma_step HS2 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0xa0 ld s7, 0(a0): a's n (hand load, atom 35; a0 = a + 40) ---- *)
pose proof (sma_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA1.
sma_hl_ld HS2 (23%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 40) nA.
{ sma_regv (SOff 10 40). apply sma_denot_off; [rewrite !ew_havoc_old by lia; exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhA1 as (_ & _ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhA1 as (_ & _ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh3 math3 HS3 Hm3. clear HS2.
sma_bk HS3 HJ SHOK Usp HI mh3 math3 Hm3.
sma_step HS3 HJ SHOK HI Usp FS Hc'.
(* ---- SMA_AT 0xa4 ld a0, 0(a1): b's n (hand load, atom 36; a1 = b + 40) ---- *)
pose proof (sma_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB1.
sma_hl_ld HS3 (10%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (pb + 40) nB.
{ sma_regv (SOff 11 40). apply sma_denot_off; [rewrite !ew_havoc_old by lia; exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhB1 as (_ & _ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhB1 as (_ & _ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh4 math4 HS4 Hm4. clear HS3.
sma_bk HS4 HJ SHOK Usp HI mh4 math4 Hm4.
sma_step HS4 HJ SHOK HI Usp FS Hc'.
(* the n fields are the trees' item counts (read at the entry memory) *)
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (sma_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
pose proof HhA0 as (_ & _ & _ & _ & _ & _ & (RnA & _) & _). pose proof HhB0 as (_ & _ & _ & _ & _ & _ & (RnB & _) & _).
lazymatch type of HS4 with st_ok _ ?E4 _ _ =>
  assert (A35 : ew E4 35 = Z_to_bv 64 nA) by (rewrite ew_havoc_old by lia; apply sma_ew_new1);
  assert (A36 : ew E4 36 = Z_to_bv 64 nB) by apply sma_ew_new1;
  assert (A33' : ew E4 33 = Z_to_bv 64 (tag ta)) by (rewrite !ew_havoc_old by lia; apply sma_ew_new1)
end.
(* ---- SMA_AT 0xa8 bne s7, a0: the n fields differ -> 0 ---- *)
sma_branch HS4.
{ intros Hc HS4.
  rewrite branch_ne_U, (U_atom _ 35 nA A35 ltac:(lia)), (U_atom _ 36 nB A36 ltac:(lia)) in Hc.
  sma_fin HS4 HJ SHOK HI Usp FS Hc' (env_agree_refl 32 E) 0.
  right. split; [|reflexivity]. intros Et. subst tb. rewrite LnA, LnB, Z.eqb_refl in Hc. discriminate Hc. }
intros Hc HS4.
rewrite branch_ne_U, (U_atom _ 35 nA A35 ltac:(lia)), (U_atom _ 36 nB A36 ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into En.
(* ---- SMA_AT 0xac .. 0xb0: s0 = 1, a0 = tag - 5 ---- *)
sma_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- from here on: the dispatch on the tag (sma_disp), at the state sma_ssD ---- *)
lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
  assert (HS4' : st_ok sg Ey sma_ssD m) by (replace sma_ssD with ss by (vm_compute; reflexivity); exact HS4) end.
exact (sma_disp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain (env_agree_refl 32 E))
  ltac:(rewrite !ew_havoc_old by lia; exact E32) A33' A35 A36 HhA0 HhB0 Etag En).
Qed.

End E.

(* The kit's tsame_specX at every nesting: sma_same_entry at nesting n, its recursive calls through nestings below n *)
Theorem same_holds_Ap : forall n, tsame_specX (PA := PI_prog_A) B ARx SK n.
Proof.
intros n. induction n as [n IHn] using (well_founded_ind lt_wf).
unfold tsame_specX.
intros ly S Hp W regs mem md ch pa pb ta tb Da Db Lam peak cnt fail ran most own HF HUP H10 H11 HTA HTB HD HFA HFB HL.
eapply sma_same_entry; eassumption.
Qed.
End W.
