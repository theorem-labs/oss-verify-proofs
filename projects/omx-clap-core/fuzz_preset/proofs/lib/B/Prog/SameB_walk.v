(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the walk of same at image B' (asan-ubsan #102 pin d663f82d7f48, twin
   c90d4fa54d43): Section W (the walk's premises, each with its owner), Section E (one nesting level: the entry state,
   the invariant, the segment lemmas, the item loop), then same_holds_B, the batch kit's tsame_specX (PRH_FnEx.v :353, cut
   7cdbb61b5fa0) at PI_prog_B, by strong induction on the nesting. The image numbers, the
   computed segment states and the run tactics are lib/B/Prog/SameB_defs.v's; the header there gives the port, the
   segment structure and every UBSan / ASan check branch with how it is shown not taken. lib/B/Prog/SameB_final.v
   states it at the instance of record. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import SameB_kit SameB_memA SameB_memB SameB_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the non-primary room of the kit's texts (PRH_Base.v PrhRoomLive): same makes no allocator call, so the walk only
   carries room_live_cf S -> room_live_cf S' (S' = S) and holds at every instance (a8's prh_room_live_a8 among them) *)
Context {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator laws at the harness head length cf_head (YCbqG c3b5d0111037; field 14 alx_hshadow and field 15
   alx_blocks_tail are the laws the walk's trees need). OWNER the engine (c-omx-alloc); at the instance of record
   PALibB.exvi_eh_laws *)
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
(* the image facts of B at the listing (YC1fP.v PALib: the .got slot of the shadow base and the cell it points at, at
   A_OBJ 0 / A_OBJ 12). OWNER the image instance (h-rw-man-5); at the instance of record PALibB.exvi_eh_palib *)
Hypothesis PAL : YC1fP.PALib (PI := PI_prog_B) B.
(* the runtime rows, MARKED TEXTS. strcmp: YGcallMxmn.v's read-only-premise row with the memnorm keep,
   astrcmp_realizes_xrom (OWNER c-libc-stdio, its row; the same text as ExvB_Stmt.v's EXV_HYP eh_strcmp). bcmp:
   YGcallMxmn.v's abcmp_realizes_xm (OWNER c-asan, the interceptor row; EXV_HYP eh_bcmp) *)
Hypothesis STRCMP : astrcmp_realizes_xrom rsegs B ARx B_prog_relro_lo B_prog_relro_hi SMB_STRCMP.
Hypothesis BCMP : abcmp_realizes_xm rsegs B ARx SMB_BCMP.
(* ARx refines the second allocator instance ARcf (h-mani-a8): true at ARx := ARcf and at ARcfx := ARcf /\ xs_placed_cf
   (proj1). It gives, by a8's YGcfBlockRange.v, a live block below cf_malloc_max and the user range of a live block,
   the real stack's 64-aligned top, and (YG0scf.v frame_facts_cf) 64-aligned fake frames. OWNER h-mani-a8 (ARcf) *)
Hypothesis SMB_CF : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> ARcf rsegs B ly S Hp W mem md.
Let SMB_BMAX : forall ly S Hp (W : world rsegs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n < cf_malloc_max :=
  fun ly S Hp W mem md p n H Hin => ablock_n_lt_max_cf rsegs B ly S Hp W mem md p n (SMB_CF ly S Hp W mem md H) Hin.
Let SMB_STK64 : forall ly S Hp (W : world rsegs) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0 :=
  fun ly S Hp W mem md H => stk_hi_mod64_cf rsegs B ly S Hp W mem md (SMB_CF ly S Hp W mem md H).
Lemma SMB_FR64 : forall ly S Hp (W : world rsegs) mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (SMB_CF _ _ _ _ _ _ HAR) as [M _].
destruct (frame_facts_cf B ly S Hp _ cid pos M Hin) as (_ & _ & _ & _ & FA & _ & _ & Hoff & _ & Hbytes & _).
split; [|exact Hbytes].
unfold page_aligned in FA. apply Z.mod_divide in FA as [qF HqF]; [|lia].
apply Z.mod_divide in Hoff as [qO HqO]; [|lia].
unfold frame_addr. rewrite HqF, HqO. replace (qF * 4096 + qO * 64) with ((qF * 64 + qO) * 64) by ring.
apply Z_mod_mult.
Qed.
Let SMB_GOTC : as_got_shadow B = SMB_GOT /\ as_shadow_cell B = SMB_CELL :=
  conj (YC1fP.pal_got_shadow _ PAL) (YC1fP.pal_cell _ PAL).
Let HSL : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd := B_prog_segs_low.
Let HWX : wx_segs_nowrap rsegs := B_prog_wx.
Local Notation PST := (prh_pst (PI := prh_img_B)).

(* the strcmp row's 8-byte slack past a string in a harness block of the ledger: the block's user range from a8's
   block_user_range_cf (the user pointer at least 16 bytes into its chunk) *)
Lemma smb_amr8 : forall ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 x k n0,
  prh_ledger (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ARx ly1 S1 Hp1 W1 mem1 md1 -> ablocks B ly1 S1 = ablocks B ly S ->
  In (x, k) Lam -> 0 <= n0 <= k -> amem_range8 x n0.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own ly1 S1 Hp1 W1 mem1 md1 x k n0 HL HAR1 Hbl Hin Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@ASAN_CEIL_range rc) as CR.
pose proof (@cf_head_nonneg cp) as Hc0.
destruct HL as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (x, k) Hin) as (Hk & Hblk & _).
cbn [fst snd] in Hk, Hblk. rewrite <- Hbl in Hblk. unfold ablocks in Hblk.
apply in_map_iff in Hblk as ([p m] & Ep & Hpb). cbn [fst snd] in Ep. injection Ep as Ep Em.
destruct (block_user_range_cf rsegs B ly1 S1 Hp1 W1 mem1 md1 p m (SMB_CF _ _ _ _ _ _ HAR1) Hpb)
  as (Hm & [[L1 L2] | [H1 H2]]); rewrite Ep, Em in *.
- assert (R : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  unfold amem_range8. left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
- assert (R : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  unfold amem_range8. right. unfold kHighMemEnd, kHighMemBeg in *. lia.
Qed.

(* THE GUARDED LIVE-STACK PREMISE. The batch kit's tsame_specX (PRH_FnEx.v :353) carries, right after fpre,
     spZ regs <= pa -> YGcallStackUp.astack_up_x segs ly W (spZ regs) mem
   The batch kit KEPT the premise this walk had as its twin tsame_specX_FIX (the STOP of 2026-10-29, the kit owner's ruling 22:20Z), in
   a Theorem Labs lane's astack_up_x form (convertible to the twin's `forall a, spZ regs <= a < ly_top ly -> apresent (w_H W)
   mem a`), so the walk now proves the kit text itself and the twin is gone.
   WHY THE WALK NEEDS IT: B' same keeps a in s0 across its recursive call (same+0x2ec `jal same`, s0 = a since the
   prologue), so the callee's afn_pre_x asks a frame chain at pa (YCbqG.v achain, via aj_call_x). The text admits a
   root on the real stack above the entry sp (prhex_home's third case); there the unwinder (YG00.v fpchain) reads the
   words from pa - 16 up to ly_top, and afn_pre_x makes present only the window below sp: HSUP, carried to the call by
   astack_up_journal_x, gives the rest (smb_chain_pa). The recursive call discharges the callee's premise vacuously:
   a kid is in a block of Lam, below YM05.alloc_ceiling and so below the callee's sp (HSUPc in the kid loop). *)

Section E.
Variables (n : nat) (ly : alayout) (S : astate) (Hp : list Z) (W : world rsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (pa pb : Z) (ta tb : jv) (Da Db : list (Z * Z))
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z).
Hypothesis HFPRE : fpre (PA := PI_prog_B) B ARx (STK_same n) ly S Hp W regs mem md ch.
Hypothesis HSUP : spZ regs <= pa -> astack_up_x rsegs ly W (spZ regs) mem.
Hypothesis H10 : getr regs 10 = w64 pa.
Hypothesis H11 : getr regs 11 = w64 pb.
Hypothesis HTA : prhex_tree (PA := PI_prog_B) ly S Lam W regs mem pa ta Da.
Hypothesis HTB : prhex_tree (PA := PI_prog_B) ly S Lam W regs mem pb tb Db.
Hypothesis HDEP : (depth ta <= n)%nat.
Hypothesis HFA : forall z, pj_footR pa Da z -> ~ (spZ regs - STK_same n <= z < spZ regs).
Hypothesis HFB : forall z, pj_footR pb Db z -> ~ (spZ regs - STK_same n <= z < spZ regs).
Hypothesis HLED : prh_ledger (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis IH : forall n', (n' < n)%nat -> tsame_specX (PA := PI_prog_B) B ARx SK n'.

(* the text's post Q (tsame_specX's, inside fpostm's memnorm keep) *)
Definition smb_Q : alayout -> astate -> list Z -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\ (ta = tb /\ getr regs' 10 = w64 1 \/ ta <> tb /\ getr regs' 10 = w64 0) /\
    pj_nodeR rsegs (mrestrict (w_H W') mem') (prh_lin Lam) pa ta Da /\
    pj_nodeR rsegs (mrestrict (w_H W') mem') (prh_lin Lam) pb tb Db /\
    Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger (PA := PI_prog_B) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Definition smb_POST : world rsegs -> config -> Prop :=
  fpostm (PA := PI_prog_B) B ARx SK (STK_same n) [] regs ly S Hp W mem md smb_Q.

(* what every point of the walk carries: the journal from the entry, the allocator state unchanged (same allocates
   nothing), the ledger at the current memory, and the memnorm keep from the entry memory; the trees, the roots'
   shadow and the read-only bytes follow from it (SameB_memA.v) *)
Definition smb_INV (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world rsegs) (mem1 : word -> option byte)
  (md1 : Model) (k1 : Z) : Prop :=
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 /\
  S1 = S /\ Hp1 = Hp /\ ablocks B ly1 S1 = ablocks B ly S /\
  prh_ledger (PA := PI_prog_B) B ly1 S1 Hp1 W1 mem1 Lam peak cnt fail ran most own /\
  (YAkMemnorm.memnorm rsegs mem -> YAkMemnorm.memnorm rsegs mem1).

(* the invariant across a stretch that writes only at or above YM05.alloc_ceiling (a run of the frame): the journal is
   the stretch's, the ledger is kept below YM05.alloc_ceiling, the memnorm keep is the run's (memnorm_frame_of) *)
Lemma smb_inv_frame : forall ly1 S1 Hp1 W1 m md1 k1 m' md' (E : env) rs,
  smb_INV ly1 S1 Hp1 W1 m md1 k1 ->
  (YAkMemnorm.memnorm rsegs m -> frame_of E rs m m' -> YAkMemnorm.memnorm rsegs m') ->
  frame_of E rs m m' ->
  frame_of E rs (mrestrict (w_H W1) m) (mrestrict (w_H W1) m') ->
  (forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) ->
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 m' md' k1 ->
  smb_INV ly1 S1 Hp1 W1 m' md' k1.
Proof.
intros ly1 S1 Hp1 W1 m md1 k1 m' md' E rs (HJ0 & HS1 & HHp & Hbl & HL & HM) HMN HF HFr Hwb HJ'.
pose proof HJ0 as (HAR0 & _).
split; [exact HJ'|]. split; [exact HS1|]. split; [exact HHp|]. split; [exact Hbl|]. split.
- apply (smbk_ledger_keep (PA := PI_prog_B) B ARx LAWS ly1 S1 Hp1 W1 m md1 m' Lam peak cnt fail ran most own HAR0 HL).
  intros a Ha. exact (smbk_frame_below rsegs E rs (w_H W1) m m' HFr Hwb a Ha).
- intros Hm. exact (HMN (HM Hm) HF).
Qed.

(* the invariant across a runtime call (strcmp, bcmp): its journal, the view kept outside its stack window, which
   lies at or above YM05.alloc_ceiling, and the row's memnorm keep *)
Lemma smb_inv_ecall : forall ly1 S1 Hp1 W1 m md1 k1 m' md' lo hi,
  smb_INV ly1 S1 Hp1 W1 m md1 k1 ->
  ajournal_x (SK := SK) rsegs B PST ARx (STK_same n) (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 W1 m' md' k1 ->
  YM05.alloc_ceiling <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview rsegs (w_H W1) m' a = aview rsegs (w_H W1) m a) ->
  (YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m') ->
  smb_INV ly1 S1 Hp1 W1 m' md' k1.
Proof.
intros ly1 S1 Hp1 W1 m md1 k1 m' md' lo hi (HJ0 & HS1 & HHp & Hbl & HL & HM) HJ' Hlo Hk HMN.
pose proof HJ0 as (HAR0 & _).
split; [exact HJ'|]. split; [exact HS1|]. split; [exact HHp|]. split; [exact Hbl|]. split.
- apply (smbk_ledger_keep (PA := PI_prog_B) B ARx LAWS ly1 S1 Hp1 W1 m md1 m' Lam peak cnt fail ran most own HAR0 HL).
  intros a Ha. pose proof asan_consts as (C1 & _). apply mbyte_of_aview. apply Hk; lia.
- intros Hm. exact (HMN (HM Hm)).
Qed.

Lemma smb_stk : STK_same n = Z.of_nat (Datatypes.S n) * 160 + 2 * ESTACK.
Proof. reflexivity. Qed.
Lemma smb_stk' : forall k, STK_same k = Z.of_nat (Datatypes.S k) * 160 + 2 * ESTACK.
Proof. reflexivity. Qed.

Lemma smb_nodes : forall ly1 S1 Hp1 W1 mem1 md1 k1, smb_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  pj_nodeR rsegs (mrestrict (w_H W1) mem1) (prh_lin Lam) pa ta Da /\
  pj_nodeR rsegs (mrestrict (w_H W1) mem1) (prh_lin Lam) pb tb Db.
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & _ & Hbl & _). pose proof HFPRE as [(HAR & _) _].
split; eapply (smb_node_now (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64); eassumption.
Qed.

Lemma smb_ras : forall ly1 S1 Hp1 W1 mem1 md1 k1, smb_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF pa 56 /\
  range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF pb 56.
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & HHp & Hbl & _). pose proof HFPRE as [(HAR & _) _].
split; eapply (smb_ra_now (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64); eassumption.
Qed.

Lemma smb_ro : forall ly1 S1 Hp1 W1 mem1 md1 k1, smb_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  arodata_okP rsegs B_prog_relro_lo B_prog_relro_hi B (aview rsegs (w_H W1) mem1).
Proof.
intros ly1 S1 Hp1 W1 mem1 md1 k1 (HJ & _ & _ & _ & HL1 & _). pose proof HFPRE as [_ [HRO _]].
exact (smb_ro_now (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HRO HLED HL1 HJ).
Qed.

(* a root's header, named at the entry, is the same header at every later point *)
Lemma smb_hdr_now : forall p t D ty num str kids keys nn cap ly1 S1 Hp1 W1 mem1 md1 k1,
  prhex_tree (PA := PI_prog_B) ly S Lam W regs mem p t D ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) p ty num str kids keys nn cap ->
  smb_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  pj_hdrR rsegs (mrestrict (w_H W1) mem1) p ty num str kids keys nn cap.
Proof.
intros p t D ty num str kids keys nn cap ly1 S1 Hp1 W1 mem1 md1 k1 HT Hh (HJ & _ & _ & Hbl & _).
pose proof HFPRE as [(HAR & _) _].
apply (pj_hdrR_frame rsegs _ _ p ty num str kids keys nn cap Hh). intros z Hz.
destruct (smb_foot_keep (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64 _ ly S Hp W regs mem md Lam
  peak cnt fail ran most own p t D ly1 S1 Hp1 W1 mem1 md1 k1 z HAR HLED HT HJ Hbl (or_introl Hz)) as (Hni & Hz64 & E).
exact (smb_agree_of_aview rsegs (w_H W) (w_H W1) mem mem1 z Hz64 Hni E).
Qed.

Lemma smb_hdr_of_node : forall m Lb p t D, pj_nodeR rsegs m Lb p t D ->
  exists num str kids keys nn cap, pj_hdrR rsegs m p (tag t) num str kids keys nn cap.
Proof.
intros m Lb p t D H. destruct t; cbn [pj_nodeR] in H; destruct H as (_ & _ & num & str & kids & keys & nn & cap & Hh & _);
  exists num, str, kids, keys, nn, cap; exact Hh.
Qed.

(* the n field a node holds: the item count of a container, 0 otherwise *)
Definition smb_len (t : jv) : Z :=
  match t with JArr l => Z.of_nat (length l) | JObj l => Z.of_nat (length l) | _ => 0 end.
Lemma smb_node_n : forall H m Lb p t D ty num str kids keys nn cap,
  pj_nodeR rsegs (mrestrict H m) Lb p t D -> pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  nn = smb_len t.
Proof.
intros H m Lb p t D ty num str kids keys nn cap HN (_ & _ & _ & _ & _ & _ & Hn & _).
assert (U : forall n', rd_u64 rsegs (mrestrict H m) (p + 40) n' -> n' = nn)
  by (intros n' Hn'; exact (proj1 (smb_num_eq rsegs H m (p + 40) (p + 40) n' nn Hn' Hn) (fun i _ => eq_refl))).
destruct t; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & _ & _ & _ & _ & Hn' & _) & F);
  rewrite <- (U n' Hn'); cbn [smb_len].
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & H0 & _); exact H0.
- destruct F as (_ & _ & H0 & _); exact H0.
- destruct F as (_ & H0 & _); exact H0.
Qed.
(* two trees with the same tag at most 2 (null, false, true) are equal *)
Lemma smb_tag_scalar : forall t t', tag t = tag t' -> tag t <= 2 -> t = t'.
Proof. intros [] [] E H; cbn in E, H; try lia; try discriminate; reflexivity. Qed.
(* a number or string node: its str field holds its text as a C string of the block predicate *)
Lemma smb_node_str : forall H m Lb p t D ty num str kids keys nn cap,
  pj_nodeR rsegs (mrestrict H m) Lb p t D -> pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  tag t = 3 \/ tag t = 4 ->
  exists s k, pj_cstrR rsegs (mrestrict H m) Lb str k s /\ (t = JStr s \/ exists bits, t = JNum s bits /\ num = bits).
Proof.
intros H m Lb p t D ty num str kids keys nn cap HN (_ & _ & Hnum & Hstr & _) Ht.
assert (U16 : forall s', rd_u64 rsegs (mrestrict H m) (p + 16) s' -> s' = str)
  by (intros s' Hs'; exact (proj1 (smb_num_eq rsegs H m (p + 16) (p + 16) s' str Hs' Hstr) (fun i _ => eq_refl))).
assert (U8 : forall s', rd_u64 rsegs (mrestrict H m) (p + 8) s' -> s' = num)
  by (intros s' Hs'; exact (proj1 (smb_num_eq rsegs H m (p + 8) (p + 8) s' num Hs' Hnum) (fun i _ => eq_refl))).
destruct t as [| | | txt bits | s | items | members]; cbn [tag] in Ht; try lia; cbn [pj_nodeR] in HN;
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & Hnum' & Hstr' & _) & F).
- destruct F as (Eb & _ & _ & _ & _ & k & Hc & _). exists txt, k.
  split; [rewrite <- (U16 str' Hstr'); exact Hc|]. right. exists bits. split; [reflexivity|].
  rewrite <- (U8 num' Hnum'). exact Eb.
- destruct F as (_ & _ & _ & _ & k & Hc & _). exists s, k.
  split; [rewrite <- (U16 str' Hstr'); exact Hc|]. left. reflexivity.
Qed.

(* where a root lies: inside [4096, 2 ^ 47), 8-aligned, outside the image, apart from the shadow band *)
Lemma smb_root : forall p t D, prhex_tree (PA := PI_prog_B) ly S Lam W regs mem p t D ->
  4096 <= p /\ p + 56 <= 2 ^ 47 /\ p mod 8 = 0 /\
  (forall x, p <= x < p + 56 -> ~ in_img rsegs x /\ (x < kLowShadowBeg \/ kHighMemBeg <= x)).
Proof.
intros p t D (Hn & Hh & Hr).
destruct HFPRE as [HPRE _].
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof (smbk_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (smb_hdr_of_node _ _ _ _ _ Hn) as (num & str & kids & keys & nn & cap & ((Hal & _) & _)).
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
Lemma smb_entry_ok : st_ok rsegs (Ereg regs [w64 SHADOW_OFF]) smb_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (SMB_AT 0)) mem (seg_rom rsegs))).
Proof.
destruct HFPRE as [HPRE _].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (smbk_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof smb_stk as FS. unfold ESTACK in FS.
pose proof smb_obj_bounds as OB.
destruct (smb_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & _). destruct (smb_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & _).
destruct (alx_const rsegs B ARx LAWS ly S Hp W mem md HAR) as (Kc & _ & Kg & _).
destruct SMB_GOTC as [EG EC]. rewrite EG, EC in Kg. rewrite EC in Kc.
set (E := Ereg regs [w64 SHADOW_OFF]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)).
assert (E10 : ew E 10 = w64 pa) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 pb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
rewrite restrict_mkst_fx. unfold smb_ss0. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (region_ok_stack rsegs _ _ 2 (spZ regs) (-160) E2); [lia | lia |].
    intros a Ha. apply (apresent_writable rsegs). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val smb_got_r].
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (smb_chunk_cval rsegs E _ 0 SMB_GOT (SLit SMB_CELL) SMB_CELL).
    * reflexivity.
    * lia.
    * rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kg).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val smb_cell_r].
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. apply (smb_chunk_cval rsegs E _ 0 SMB_CELL (SOff 32 0) SHADOW_OFF).
    * rewrite smbk_SOff0. exact E32.
    * unfold SHADOW_OFF; lia.
    * rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs (w_H W) mem _ _ Kc).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val smbk_fstk smb_got_r smb_cell_r].
  try change (Ereg regs [w64 SHADOW_OFF]) with E.
  rewrite E2.
  repeat split; lia.
- unfold smb_fs0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  try change (Ereg regs [w64 SHADOW_OFF]) with E.
  rewrite E2, E10, E11, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  repeat split; lia.
Qed.

(* the two roots' shadow entries of the token runner *)
Lemma smb_shok : forall E m, ew E 10 = w64 pa -> ew E 11 = w64 pb -> ew E 32 = w64 SHADOW_OFF ->
  range_addressable (rd_of rsegs m) SHADOW_OFF pa 56 -> range_addressable (rd_of rsegs m) SHADOW_OFF pb 56 ->
  sh_ok rsegs smb_Bx smb_SH E m.
Proof.
intros E m E10 E11 E32 Ra Rb.
destruct (smb_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4). destruct (smb_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4).
assert (UB : U E smb_Bx = SHADOW_OFF) by (unfold smb_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (UA : U E (SOff 10 0) = pa) by (apply (U_atom E 10 pa E10); lia).
assert (UBb : U E (SOff 11 0) = pb) by (apply (U_atom E 11 pb E11); lia).
unfold sh_ok, smb_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite UB;
  change (Z.min 0 56) with 0; change (Z.max 0 56) with 56; rewrite Z.sub_0_r.
- rewrite UA, Z.add_0_r. split; [exact Ra|]. intros a Ha. destruct (Pa4 a ltac:(lia)) as [_ Hx].
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
- rewrite UBb, Z.add_0_r. split; [exact Rb|]. intros a Ha. destruct (Pb4 a ltac:(lia)) as [_ Hx].
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* the return at SMB_AT 0x158 (`ret`), a0 symbolic: the text's post *)
Lemma smb_ret_u : forall ly1 S1 Hp1 W1 md1 k1 E1 ss ms (r : Z) (extra : list word),
  smb_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  st_ok rsegs E1 ss (restrict (w_H W1) ms) -> ss_resv ss = None -> ss_pc ss = SMB_AT 0x158 ->
  env_agree 32 (Ereg regs extra) E1 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  U E1 (sr_get (ss_regs ss) 10) = r -> sr_get (ss_regs ss) 1 = SOff 1 0 ->
  (ta = tb /\ r = 1 \/ ta <> tb /\ r = 0) ->
  SRr rsegs W1 (mkCfg ms md1) smb_POST.
Proof.
intros ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs Hr10 Hr1 Hr.
pose proof HI as (HJ & HS1 & HHp & Hbl & HL1 & HMN).
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NA NB].
pose proof HFPRE as [(HAR & Hra & _) _].
eapply (SRr_ret_at rsegs B_prog_tbl B_prog_tbl_ok HWX W1 E1 ss ms md1 _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity |].
intros mat.
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss ms 1%bv HS), Hr1, smbk_SOff0.
  destruct HEA as [HA _]. rewrite (HA 1%nat ltac:(lia)). exact (ew_Ereg_nat regs extra 1 1%bv eq_refl). }
assert (R10 : getr (ms_regs ms) 10 = w64 r).
{ rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss ms 10%bv HS).
  apply bv_eq. change (bv_unsigned (sv_denot E1 (sr_get (ss_regs ss) 10))) with (U E1 (sr_get (ss_regs ss) 10)).
  assert (Hr0 : 0 <= r < 2 ^ 64) by (destruct Hr as [[_ ->] | [_ ->]]; lia).
  rewrite Hr10. unfold w64. rewrite unsigned_lit_small by exact Hr0. reflexivity. }
rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra.
unfold smb_POST, fpostm, fpost, apost_base_x.
exists ly1, S1, Hp1, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md1) mat md1), k1.
split; [reflexivity|].
split; [apply (ajournal_x_materialize rsegs B _ ARx LAWS HSL); exact HJ|].
split; [exact (aregs_preserved_of_st_ok rsegs (w_H W1) E1 ss ms regs extra HS HEA Hcs)|].
unfold fQmn, smb_Q. split; [|exact HMN].
split; [intros Hrl; rewrite HS1; exact Hrl|].
split; [destruct Hr as [[Ht ->] | [Ht ->]]; [left | right]; split; assumption|].
split; [exact NA|]. split; [exact NB|]. split; [exact HHp|]. split; [exact HS1|]. split; [exact Hbl|]. exact HL1.
Qed.
(* the same, a0 a literal *)
Lemma smb_ret : forall ly1 S1 Hp1 W1 md1 k1 E1 ss ms (r : Z) (extra : list word),
  smb_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  st_ok rsegs E1 ss (restrict (w_H W1) ms) -> ss_resv ss = None -> ss_pc ss = SMB_AT 0x158 ->
  env_agree 32 (Ereg regs extra) E1 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  sr_get (ss_regs ss) 10 = SLit r -> sr_get (ss_regs ss) 1 = SOff 1 0 ->
  (ta = tb /\ r = 1 \/ ta <> tb /\ r = 0) ->
  SRr rsegs W1 (mkCfg ms md1) smb_POST.
Proof.
intros ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs Hr10 Hr1 Hr.
apply (smb_ret_u ly1 S1 Hp1 W1 md1 k1 E1 ss ms r extra HI HS Hrv Hpc HEA Hcs); [| exact Hr1 | exact Hr].
rewrite Hr10. apply U_lit. destruct Hr as [[_ ->] | [_ ->]]; lia.
Qed.

(* after a hand load (continuation names ms' mat' HS Hm): the journal through the materializing step, the shadow
   entries and the sp fact at the havocked environment, the invariant at the (same) memory *)
Ltac smb_bk HS HJ SHOK Usp HI ms' mat' Hm :=
  let HJn := fresh "HJ" in let SHn := fresh "SHOK" in let Un := fresh "Usp" in
  pose proof (smb_aj_wvb (SK := SK) rsegs B PST ARx LAWS HSL
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
Ltac smb_inv_after HI HJ Usp Hc' :=
  let HI1 := fresh "HI" in
  lazymatch goal with HMNP0 : forall m', _ -> frame_of _ _ _ m' -> _ |- _ =>
  lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  match goal with HF0 : frame_of _ _ ?m0 _ |- _ =>
    lazymatch m0 with mrestrict _ _ => fail | _ => idtac end;
    pose proof (smb_inv_frame _ _ _ _ _ _ _ _ _ _ _ HI (HMNP0 _) HF0 HFr0 ltac:(smb_wb Usp Hc') HJ) as HI1;
    clear HMNP0
  end end end;
  repeat match goal with H0 : frame_of _ _ _ _ |- _ => clear H0 | H0 : mem_grows _ _ |- _ => clear H0 end;
  clear HI; rename HI1 into HI.
Ltac smb_step HS HJ SHOK HI Usp FS Hc' :=
  smb_run HS HJ SHOK; [ smb_awr Usp FS | smb_inv_after HI HJ Usp Hc' ].
Ltac smb_step_to HS HJ SHOK HI Usp FS Hc' stop :=
  smb_run_to HS HJ SHOK stop; [ smb_awr Usp FS | smb_inv_after HI HJ Usp Hc' ].
(* a run to the `ret` at SMB_AT 0x158 and the post through smb_ret, with a0 = r; left: the tree fact on r *)
Ltac smb_fin HS HJ SHOK HI Usp FS Hc' HAE r :=
  smb_step HS HJ SHOK HI Usp FS Hc';
  eapply (smb_ret _ _ _ _ _ _ _ _ _ r [w64 SHADOW_OFF] HI HS);
    [vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HAE
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
(* the same through smb_ret_u, a0 symbolic; left: the value of a0 (U ... = r), then the tree fact on r *)
Ltac smb_finu HS HJ SHOK HI Usp FS Hc' HAE r :=
  smb_step HS HJ SHOK HI Usp FS Hc';
  eapply (smb_ret_u _ _ _ _ _ _ _ _ _ r [w64 SHADOW_OFF] HI HS);
    [vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HAE
    | vm_compute; reflexivity | | vm_compute; reflexivity |];
    [ lazymatch goal with |- U ?Ef (sr_get ?rs ?rr) = _ =>
        let v := eval vm_compute in (sr_get rs rr) in change (sr_get rs rr) with v end | ].
(* the common preamble of the arm lemmas: the entry facts, and the register atoms below 32 of Ex read through HAE *)
Ltac smb_pre Ex HAE :=
  pose proof HFPRE as [HPRE [HRO _]];
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
  pose proof (smbk_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0);
  pose proof smb_stk as FS; unfold ESTACK in FS;
  pose proof Hceil as Hc'; rewrite FS in Hc';
  destruct (smb_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4); destruct (smb_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4);
  pose proof (smb_tag_range ta) as TRa; pose proof (smb_tag_range tb) as TRb;
  assert (B0 : bv_signed (0%bv : bv 12) = 0) by reflexivity;
  assert (E10 : ew Ex 10 = w64 pa)
    by (destruct HAE as [HA _]; rewrite (HA 10%nat ltac:(lia)), (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10);
  assert (E11 : ew Ex 11 = w64 pb)
    by (destruct HAE as [HA _]; rewrite (HA 11%nat ltac:(lia)), (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
  assert (E3 : ew Ex 3 = w64 (as_gp B))
    by (destruct HAE as [HA _]; rewrite (HA 3%nat ltac:(lia)), (ew_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp);
  assert (E4 : ew Ex 4 = w64 (as_tp B))
    by (destruct HAE as [HA _]; rewrite (HA 4%nat ltac:(lia)), (ew_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp).

(* the number arm, from SMB_AT 0x108: both str fields, strcmp (ra SMB_AT 0x114), then on equal texts bcmp of the two
   num fields (ra SMB_AT 0x36c), `seqz` and the return *)
Lemma smb_num : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex smb_ssN (restrict (w_H W) ms) ->
  smb_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs smb_Bx smb_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> tag ta = 3 ->
  SRr rsegs W (mkCfg ms md4) smb_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 HhA0 HhB0
  Etag Ht3.
smb_pre Ex HAE. pose proof HI as (HJ & _).
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
pose proof smb_pc_bounds as PCB.
(* ---- SMB_AT 0x108 ld a0, 0(a0) / SMB_AT 0x10c ld a1, 0(a1): the two str fields (hand loads, atoms 37 / 38) ---- *)
smb_hl_ld HS4 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 16) strA.
{ smb_regv (SOff 10 16). apply smb_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh5 math5 HS5 Hm5. clear HS4.
smb_bk HS5 HJ SHOK Usp HI mh5 math5 Hm5.
smb_step HS5 HJ SHOK HI Usp FS Hc'.
smb_hl_ld HS5 (11%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (pb + 16) strB.
{ smb_regv (SOff 11 16). apply smb_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r.
  destruct (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh6 math6 HS6 Hm6. clear HS5.
smb_bk HS6 HJ SHOK Usp HI mh6 math6 Hm6.
smb_step HS6 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0x110 jal strcmp: the call at the wrapper SMB_STRCMP (ra SMB_AT 0x114), the two numbers' texts ---- *)
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA2.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB2.
destruct (smb_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NAc HhA2 (or_introl Ht3)) as (sA & kA & HcA & ShA).
destruct (smb_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NBc HhB2 (or_introl (eq_trans (eq_sym Etag) Ht3))) as (sB & kB & HcB & ShB).
pose proof HI as (HJc & HSc & HHpc & Hblc & _). pose proof HJc as (HARc & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E6 ss6 msc HS6 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMB_STRCMP) by (vm_compute; reflexivity);
  assert (A37 : ew E6 37 = Z_to_bv 64 strA) by (rewrite ew_havoc_old by lia; apply smb_ew_new1);
  assert (A38 : ew E6 38 = Z_to_bv 64 strB) by apply smb_ew_new1;
  assert (R10 : getr (ms_regs msc) 10 = w64 strA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 10%bv HS6); smb_regv (SOff 37 0);
        rewrite smbk_SOff0; exact A37);
  assert (R11 : getr (ms_regs msc) 11 = w64 strB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 11%bv HS6); smb_regv (SOff 38 0);
        rewrite smbk_SOff0; exact A38);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMB_AT 0x114))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 1%bv HS6); smb_regv (SLit (SMB_AT 0x114)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 3%bv HS6); smb_regv (SOff 3 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 4%bv HS6); smb_regv (SOff 4 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-160)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 2%bv HS6); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -160)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-160)))) with (U E6 (SOff 2 (-160)));
        pose proof asan_consts as (AC1b & _);
        rewrite (smb_U_off E6 2 (-160) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strA kA sA HLED HARc Hblc HHpc HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strB kB sB HLED HARc Hblc HHpc HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (smb_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx B_prog_relro_lo B_prog_relro_hi LAWS HSL
    SMB_STRCMP STRCMP W
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ strA strB
    (Z.of_nat (length sA)) (Z.of_nat (length sB)) (-160) (Z_to_bv 64 (SMB_AT 0x114)) HJc R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strA kA (Z.of_nat (length sA) + 1) HLED
      HARc Hblc HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strB kB (Z.of_nat (length sB) + 1) HLED
      HARc Hblc HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMB_AT 0x114: the invariant, the frame kept, the symbolic state resumed (atoms 39.., a0 = atom 43) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (smb_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -160 - 2 * ESTACK) (spZ regs + -160) HI HJ3
  ltac:(unfold ESTACK in *; lia) Hfr2 Hmn2) as HI3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ3 & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  assert (HKR : Forall (region_kept rsegs E6 (ms_mem (restrict (w_H W) MSC)) (mrestrict (w_H W) mem2)) (ss_mem ss6))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof smb_obj_bounds; apply mbyte_of_aview; apply Hfr2; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ3; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  pose proof (st_ok_after_call rsegs 39 E6 ss6 (restrict (w_H W) MSC) regs2 (mrestrict (w_H W) mem2) (ss_mem ss6)
    (SMB_AT 0x114) HS6 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 39 (SMB_AT 0x114)) in
  change (ss_after_call ss6 (ss_mem ss6) 39 (SMB_AT 0x114)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMB_AT 0x114)) (mrestrict (w_H W) mem2) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (SMB_AT 0x114)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 39 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs smb_Bx smb_SH (havoc E6 39 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
    by (destruct (smb_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply smb_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
          | rewrite !ew_havoc_old by lia; exact E32 | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb])
end.
clear HS6 HKR HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
smb_step HS7 HJ SHOK HI Usp FS Hc'.
(* the two trees are numbers; their texts are equal exactly when strcmp answered 0 *)
assert (TA : exists bA, ta = JNum sA bA)
  by (destruct ShA as [Ea | (bA & Ea & _)]; [rewrite Ea in Ht3; cbn in Ht3; lia | exists bA; exact Ea]).
assert (TB : exists bB, tb = JNum sB bB)
  by (destruct ShB as [Eb | (bB & Eb & _)]; [rewrite Eb in Etag; cbn in Etag; lia | exists bB; exact Eb]).
assert (Ev0 : v = w64 0 <-> sA = sB) by (rewrite Hcmp; exact (smb_str_eq rsegs (w_H W) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
assert (U43 : U (ltac:(lazymatch type of HS7 with st_ok _ ?E7 _ _ => exact E7 end)) (SOff 43 0) = bv_unsigned v)
  by (unfold U; rewrite smbk_SOff0; change (bv_unsigned (getr regs2 10) = bv_unsigned v); rewrite Hv; reflexivity).
(* ---- SMB_AT 0x114 beqz a0: the texts differ -> 0 ---- *)
smb_branch HS7.
2: { intros Hc HS7. rewrite branch_eq_U, U43, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  smb_fin HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hc.
  destruct TA as (bA & EA). destruct TB as (bB & EB). rewrite EA, EB in Et. injection Et as Es _.
  rewrite (proj2 Ev0 Es). reflexivity. }
intros Hc HS7. rewrite branch_eq_U, U43, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
assert (Es : sA = sB) by (apply Ev0; apply bv_eq; rewrite Hc; reflexivity).
smb_step HS7 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0x368 jal bcmp: the call at the wrapper SMB_BCMP (ra SMB_AT 0x36c), the two num fields (8 bytes) ---- *)
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAb.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBb.
pose proof HI as (HJb & HSb & HHpb & Hblb & _).
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 (restrict _ ?msb) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E7 ss7 msb HS7 eq_refl) as Hshape7;
  assert (Epc7 : ss_pc ss7 = SMB_BCMP) by (vm_compute; reflexivity);
  assert (Q10 : getr (ms_regs msb) 10 = w64 (pa + 8))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 10%bv HS7); smb_regv (SOff 10 8); unfold w64;
        apply smb_denot_off; [rewrite !ew_havoc_old by lia; exact E10 | lia | lia]);
  assert (Q11 : getr (ms_regs msb) 11 = w64 (pb + 8))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 11%bv HS7); smb_regv (SOff 11 8); unfold w64;
        apply smb_denot_off; [rewrite !ew_havoc_old by lia; exact E11 | lia | lia]);
  assert (Q12 : getr (ms_regs msb) 12 = w64 8)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 12%bv HS7); smb_regv (SLit 8); reflexivity);
  assert (Q1 : getr (ms_regs msb) 1 = Z_to_bv 64 (SMB_AT 0x36c))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 1%bv HS7); smb_regv (SLit (SMB_AT 0x36c)); reflexivity);
  assert (Q3 : getr (ms_regs msb) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 3%bv HS7); smb_regv (SOff 3 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E3);
  assert (Q4 : getr (ms_regs msb) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 4%bv HS7); smb_regv (SOff 4 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E4);
  assert (Q2 : getr (ms_regs msb) 2 = sv_denot E7 (SOff 2 (-160)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E7 ss7 msb 2%bv HS7); f_equal; vm_compute; reflexivity);
  assert (Qsp : spZ (ms_regs msb) = spZ regs + -160)
    by (unfold spZ; rewrite Q2; change (bv_unsigned (sv_denot E7 (SOff 2 (-160)))) with (U E7 (SOff 2 (-160)));
        pose proof asan_consts as (AC1b & _);
        rewrite (smb_U_off E7 2 (-160) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msb into MSB
end.
(* the bcmp row's per-window premises for both num fields (SameB_memB.smb_num_ok) *)
pose proof (smb_num_ok (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64 _ ly S Hp W regs mem md Lam peak cnt fail
  ran most own pa ta Da _ _ _ _ _ _ _ (ms_regs MSB) HAR HLED HTA HJb Hblb HHpb
  ltac:(rewrite Qsp; unfold ESTACK in *; lia) ltac:(rewrite FS; lia)) as (NA0 & NA1 & NAsrc & NAw & NAam & NAra & NAhv).
pose proof (smb_num_ok (PA := PI_prog_B) B ARx SK LAWS SMB_BMAX SMB_STK64 SMB_FR64 _ ly S Hp W regs mem md Lam peak cnt fail
  ran most own pb tb Db _ _ _ _ _ _ _ (ms_regs MSB) HAR HLED HTB HJb Hblb HHpb
  ltac:(rewrite Qsp; unfold ESTACK in *; lia) ltac:(rewrite FS; lia)) as (NB0 & NB1 & NBsrc & NBw & NBam & NBra & NBhv).
rewrite Hshape7 at 1. rewrite Epc7.
eapply SRr_bind.
{ eapply (aj_bcmp_at_xm (SK := SK) rsegs B PST ARx LAWS HSL SMB_BCMP BCMP W
    (ms_regs MSB) (ms_mem MSB) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ (pa + 8) (pb + 8) 8 (-160)
    (Z_to_bv 64 (SMB_AT 0x36c)) HJb Q10 Q11 Q12).
  all: first
    [ assumption
    | (intros _; assumption)
    | reflexivity
    | (apply ret_ok_even; vm_compute; reflexivity)
    | (intros a Ha; pose proof (NAw a Ha) as Hw; rewrite Qsp in Hw; exact Hw)
    | (intros a Ha; pose proof (NBw a Ha) as Hw; rewrite Qsp in Hw; exact Hw)
    | (unfold ESTACK in *; rewrite ?FS; lia) ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v3 & -> & HJ4 & HP3 & Hv3 & Hcmp3 & Hfr3 & Hpres3 & Hmn3).
(* ---- back at SMB_AT 0x36c: the invariant, the frame kept, the symbolic state resumed (atoms 55.., a0 = atom 59) ---- *)
pose proof (smb_inv_ecall _ _ _ _ _ _ _ mem3 md3 (spZ regs + -160 - 2 * ESTACK) (spZ regs + -160) HI HJ4
  ltac:(unfold ESTACK in *; lia) Hfr3 Hmn3) as HI5.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ4 & _).
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 _ =>
  assert (HKR4 : Forall (region_kept rsegs E7 (ms_mem (restrict (w_H W) MSB)) (mrestrict (w_H W) mem3)) (ss_mem ss7))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof smb_obj_bounds; apply mbyte_of_aview; apply Hfr3; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ4; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS7 with st_ok _ ?E7 ?ss7 _ =>
  pose proof (st_ok_after_call rsegs 55 E7 ss7 (restrict (w_H W) MSB) regs3 (mrestrict (w_H W) mem3) (ss_mem ss7)
    (SMB_AT 0x36c) HS7 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP3 r Hr)) HKR4) as HS8;
  let ss8 := eval vm_compute in (ss_after_call ss7 (ss_mem ss7) 55 (SMB_AT 0x36c)) in
  change (ss_after_call ss7 (ss_mem ss7) 55 (SMB_AT 0x36c)) with ss8 in HS8;
  change (mkst regs3 (Z_to_bv 64 (SMB_AT 0x36c)) (mrestrict (w_H W) mem3) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 (SMB_AT 0x36c)) mem3 (seg_rom rsegs))) in HS8;
  assert (Usp4 : bv_unsigned (ew (havoc E7 55 (map (getr regs3) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK4 : sh_ok rsegs smb_Bx smb_SH (havoc E7 55 (map (getr regs3) CLOB)) (mrestrict (w_H W) mem3))
    by (destruct (smb_ras _ _ _ _ _ _ _ HI5) as [Ra Rb];
        apply smb_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
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
  by (rewrite Hcmp3; exact (smb_num_eq rsegs (w_H W) (ms_mem MSB) (pa + 8) (pb + 8) numA numB RnA RnB)).
(* ---- SMB_AT 0x36c seqz s1, a0; j SMB_AT 0x11c; mv a0, s1; ret: a0 = (v3 == 0) ---- *)
destruct (Z.eq_dec (bv_unsigned v3) 0) as [Hz | Hz].
- smb_finu HS8 HJ SHOK HI Usp FS Hc' HAE 1.
  + rewrite (smb_U_seqz _ _ _ A59), Hz. reflexivity.
  + left. split; [|reflexivity]. rewrite NA, NB, Es. f_equal. apply Ev3. apply bv_eq. rewrite Hz. reflexivity.
- smb_finu HS8 HJ SHOK HI Usp FS Hc' HAE 0.
  + rewrite (smb_U_seqz _ _ _ A59). destruct (Z.eqb_spec (bv_unsigned v3) 0); [contradiction | reflexivity].
  + right. split; [|reflexivity]. intros Et. apply Hz. rewrite NA, NB in Et. injection Et as _ Enum.
    rewrite (proj2 Ev3 Enum). reflexivity.
Qed.

(* the string arm, from SMB_AT 0x34c: both str fields, strcmp (ra SMB_AT 0x358), `seqz` and the return *)
Lemma smb_str : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex smb_ssS (restrict (w_H W) ms) ->
  smb_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs smb_Bx smb_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> tag ta = 4 ->
  SRr rsegs W (mkCfg ms md4) smb_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 HhA0 HhB0
  Etag Ht4.
smb_pre Ex HAE. pose proof HI as (HJ & _).
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
pose proof smb_pc_bounds as PCB.
(* ---- SMB_AT 0x34c ld a0, 0(a0) / SMB_AT 0x350 ld a1, 0(s6): the two str fields (hand loads, atoms 37 / 38) ---- *)
smb_hl_ld HS4 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 16) strA.
{ smb_regv (SOff 10 16). apply smb_denot_off; [try (rewrite !ew_havoc_old by lia); exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh5 math5 HS5 Hm5. clear HS4.
smb_bk HS5 HJ SHOK Usp HI mh5 math5 Hm5.
smb_step HS5 HJ SHOK HI Usp FS Hc'.
smb_hl_ld HS5 (11%bv : bv 5) (22%bv : bv 5) (0%bv : bv 12) (pb + 16) strB.
{ smb_regv (SOff 11 16). apply smb_denot_off; [try (rewrite !ew_havoc_old by lia); exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r.
  destruct (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh6 math6 HS6 Hm6. clear HS5.
smb_bk HS6 HJ SHOK Usp HI mh6 math6 Hm6.
smb_step HS6 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0x354 jal strcmp: the call at the wrapper SMB_STRCMP (ra SMB_AT 0x358), the two strings ---- *)
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA2.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB2.
destruct (smb_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NAc HhA2 (or_intror Ht4)) as (sA & kA & HcA & ShA).
destruct (smb_node_str _ _ _ _ _ _ _ _ _ _ _ _ _ NBc HhB2 (or_intror (eq_trans (eq_sym Etag) Ht4))) as (sB & kB & HcB & ShB).
pose proof HI as (HJc & HSc & HHpc & Hblc & _). pose proof HJc as (HARc & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E6 ss6 msc HS6 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMB_STRCMP) by (vm_compute; reflexivity);
  assert (A37 : ew E6 37 = Z_to_bv 64 strA) by (rewrite ew_havoc_old by lia; apply smb_ew_new1);
  assert (A38 : ew E6 38 = Z_to_bv 64 strB) by apply smb_ew_new1;
  assert (R10 : getr (ms_regs msc) 10 = w64 strA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 10%bv HS6); smb_regv (SOff 37 0);
        rewrite smbk_SOff0; exact A37);
  assert (R11 : getr (ms_regs msc) 11 = w64 strB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 11%bv HS6); smb_regv (SOff 38 0);
        rewrite smbk_SOff0; exact A38);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMB_AT 0x358))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 1%bv HS6); smb_regv (SLit (SMB_AT 0x358)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 3%bv HS6); smb_regv (SOff 3 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E3);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 4%bv HS6); smb_regv (SOff 4 0);
        rewrite smbk_SOff0, !ew_havoc_old by lia; exact E4);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-160)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W) E6 ss6 msc 2%bv HS6); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -160)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-160)))) with (U E6 (SOff 2 (-160)));
        pose proof asan_consts as (AC1b & _);
        rewrite (smb_U_off E6 2 (-160) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strA kA sA HLED HARc Hblc HHpc HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) strB kB sB HLED HARc Hblc HHpc HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (smb_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx B_prog_relro_lo B_prog_relro_hi LAWS HSL
    SMB_STRCMP STRCMP W
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ _ strA strB
    (Z.of_nat (length sA)) (Z.of_nat (length sB)) (-160) (Z_to_bv 64 (SMB_AT 0x358)) HJc R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strA kA (Z.of_nat (length sA) + 1) HLED
      HARc Hblc HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ strB kB (Z.of_nat (length sB) + 1) HLED
      HARc Hblc HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMB_AT 0x358: the invariant, the frame kept, the symbolic state resumed (atoms 39.., a0 = atom 43) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (smb_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -160 - 2 * ESTACK) (spZ regs + -160) HI HJ3
  ltac:(unfold ESTACK in *; lia) Hfr2 Hmn2) as HI3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ3 & _).
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  assert (HKR : Forall (region_kept rsegs E6 (ms_mem (restrict (w_H W) MSC)) (mrestrict (w_H W) mem2)) (ss_mem ss6))
end.
{ apply Forall_forall. intros r Hr. vm_compute in Hr.
  repeat (destruct Hr as [Hr | Hr]; [subst r; split;
    [ intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite Usp in Ha;
      pose proof smb_obj_bounds; apply mbyte_of_aview; apply Hfr2; unfold ESTACK in *; lia
    | intros a Ha _; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; try rewrite Usp in Ha;
      apply apresent_writable; apply HpresJ3; unfold ESTACK in *; lia ] |]).
  destruct Hr. }
lazymatch type of HS6 with st_ok _ ?E6 ?ss6 _ =>
  pose proof (st_ok_after_call rsegs 39 E6 ss6 (restrict (w_H W) MSC) regs2 (mrestrict (w_H W) mem2) (ss_mem ss6)
    (SMB_AT 0x358) HS6 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 39 (SMB_AT 0x358)) in
  change (ss_after_call ss6 (ss_mem ss6) 39 (SMB_AT 0x358)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMB_AT 0x358)) (mrestrict (w_H W) mem2) (seg_rom rsegs)) with
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (SMB_AT 0x358)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 39 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs smb_Bx smb_SH (havoc E6 39 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
    by (destruct (smb_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply smb_shok; [rewrite !ew_havoc_old by lia; exact E10 | rewrite !ew_havoc_old by lia; exact E11
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
assert (Ev0 : v = w64 0 <-> sA = sB) by (rewrite Hcmp; exact (smb_str_eq rsegs (w_H W) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
(* ---- SMB_AT 0x358 j SMB_AT 0x36c; seqz s1, a0; j SMB_AT 0x11c; mv a0, s1; ret: a0 = (v == 0) ---- *)
destruct (Z.eq_dec (bv_unsigned v) 0) as [Hz | Hz].
- smb_finu HS7 HJ SHOK HI Usp FS Hc' HAE 1.
  + rewrite (smb_U_seqz _ _ _ A43), Hz. reflexivity.
  + left. split; [|reflexivity]. rewrite SA, SB. f_equal. apply Ev0. apply bv_eq. rewrite Hz. reflexivity.
- smb_finu HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  + rewrite (smb_U_seqz _ _ _ A43). destruct (Z.eqb_spec (bv_unsigned v) 0); [contradiction | reflexivity].
  + right. split; [|reflexivity]. intros Et. apply Hz. rewrite SA, SB in Et. injection Et as Es.
    rewrite (proj2 Ev0 Es). reflexivity.
Qed.

(* two empty containers with the same tag are the same tree *)
Lemma smb_empty_eq : forall t u, tag t = tag u -> (tag t = 5 \/ tag t = 6) -> smb_len t = 0 -> smb_len u = 0 -> t = u.
Proof.
intros t u Et Hc Lt Lu.
destruct t as [| | | ? ? | ? | la | ma]; destruct u as [| | | ? ? | ? | lb | mb]; cbn [tag smb_len] in *; try lia.
- destruct la; [|cbn [length] in Lt; lia]. destruct lb; [reflexivity|cbn [length] in Lu; lia].
- destruct ma; [|cbn [length] in Lt; lia]. destruct mb; [reflexivity|cbn [length] in Lu; lia].
Qed.

(* ---- the loop of the container arm, SMB_AT 0x1bc .. 0x310 ---- *)
Lemma smb_its_len : forall t, (tag t = 5 \/ tag t = 6) -> Z.of_nat (length (smb_its t)) = smb_len t.
Proof. intros [| | | ? ? | ? | l | l] H; cbn [tag] in H; try lia; cbn [smb_its smb_len]; [rewrite length_map|]; reflexivity. Qed.

(* item i of a container node: its kid is a node at kids + 56 i inside the kid array (a block of Lam); an object's
   key is a C string whose pointer is the 8 bytes at keys + 8 i *)
Lemma smb_node_item : forall (H : word -> bool) (m : word -> option byte) p t D ty num str kids keys nn cap i nm u,
  pj_nodeR rsegs (mrestrict H m) (prh_lin Lam) p t D ->
  pj_hdrR rsegs (mrestrict H m) p ty num str kids keys nn cap ->
  nth_error (smb_its t) i = Some (nm, u) ->
  In (kids, 56 * cap) Lam /\ 56 * Z.of_nat i + 56 <= 56 * cap /\
  (exists D1, incl D1 D /\ pj_nodeR rsegs (mrestrict H m) (prh_lin Lam) (kids + 56 * Z.of_nat i) u D1) /\
  (tag t = 6 -> In (keys, 8 * cap) Lam /\ 8 * Z.of_nat i + 8 <= 8 * cap /\
     exists x k, rd_u64 rsegs (mrestrict H m) (keys + 8 * Z.of_nat i) x /\
       pj_cstrR rsegs (mrestrict H m) (prh_lin Lam) x k nm).
Proof.
intros H m p t D ty num str kids keys nn cap i nm u HN Hh Ei.
pose proof Hh as (_ & _ & _ & _ & Rk & Rks & Rn & Rc).
assert (U : forall a v w, rd_u64 rsegs (mrestrict H m) a v -> rd_u64 rsegs (mrestrict H m) a w -> v = w)
  by (intros a v w Hv Hw; exact (proj1 (smb_num_eq rsegs H m a a v w Hv Hw) (fun _ _ => eq_refl))).
destruct t as [| | | ? ? | ? | items | members]; cbn [smb_its] in Ei; try (destruct i; discriminate).
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
  destruct (smb_items_nth _ items kids Di i u HIt Eu) as (D1 & Hinc & HP).
  exists D1. split; [|exact HP]. rewrite ED. apply incl_appr. exact Hinc.
- cbn [pj_nodeR] in HN.
  destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & (_ & _ & _ & _ & Rk' & Rks' & Rn' & Rc') &
    _ & Hn' & Hnc & Hcap & Di & ED & HMs).
  rewrite (U _ _ _ Rk' Rk) in *. rewrite (U _ _ _ Rks' Rks) in *. rewrite (U _ _ _ Rc' Rc) in *.
  assert (Hi : (i < length members)%nat) by (apply nth_error_Some; congruence).
  destruct Hcap as [(Hc0 & _) | (Hc0 & Hl & Hlk)]; [lia|].
  destruct (smb_mems_nth rsegs _ _ _ members kids keys Di i nm u HMs Ei) as (x & k & D1 & Hinc & Hxk & Rx & Hcs & HP).
  split; [exact Hl|]. split; [lia|].
  split; [exists D1; split; [rewrite ED; apply incl_appr; exact Hinc | exact HP]|].
  intros _. split; [exact Hlk|]. split; [lia|]. exists x, k. split; [exact Rx | exact Hcs].
Qed.

(* a byte of a block of Lam: in [4096, YM05.alloc_ceiling), outside the image, apart from the shadow band *)
Lemma smb_lam_app : forall ly1 S1 Hp1 W1 mem1 md1 a k x,
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
Lemma smb_lam_al : forall a k, In (a, k) Lam -> a mod 16 = 0.
Proof.
intros a k Hin. pose proof HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (_ & _ & _ & Hal & _). exact Hal.
Qed.
Lemma smb_lam_size : forall a k, In (a, k) Lam -> k + cf_head < cf_malloc_max.
Proof.
intros a k Hin. pose proof HFPRE as [(HAR & _) _]. pose proof HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (_ & Hblk & _). cbn [fst snd] in Hblk.
destruct (SMB_BMAX _ _ _ _ _ _ _ _ HAR Hblk) as [_ Hlt]. exact Hlt.
Qed.
(* the token runner's shadow entry for 8 bytes at x inside a block of Lam *)
Lemma smb_slot_shent : forall E ly1 S1 Hp1 W1 mem1 md1 k1 K x a k,
  smb_INV ly1 S1 Hp1 W1 mem1 md1 k1 ->
  ew E K = Z_to_bv 64 x -> ew E 32 = w64 SHADOW_OFF ->
  In (a, k) Lam -> a <= x -> x + 8 <= a + k ->
  shent_ok rsegs smb_Bx E (mrestrict (w_H W1) mem1) (mkSHE K 0 8).
Proof.
intros E ly1 S1 Hp1 W1 mem1 md1 k1 K x a k HI EK E32 Hin Hax Hxk.
pose proof HI as (HJ & _ & HHp & Hbl & _). pose proof HJ as (HAR1 & _).
pose proof (smb_lam_app _ _ _ _ _ _ a k x HAR1 Hbl Hin ltac:(lia)) as (Hx0 & _ & _).
pose proof (@alloc_ceiling_lt rc) as H47.
assert (UB : U E smb_Bx = SHADOW_OFF) by (unfold smb_Bx; apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
assert (UK : U E (SOff K 0) = x) by (apply (U_atom E K x EK); lia).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite UB, UK.
change (Z.min 0 8) with 0. change (Z.max 0 8) with 8. rewrite Z.sub_0_r, Z.add_0_r.
split.
- rewrite <- (aview_rd_of rsegs).
  exact (smb_slot_ra (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
    _ _ _ _ _ _ a k x 8 HLED HAR1 Hbl HHp Hin Hax ltac:(lia) Hxk).
- intros b Hb. destruct (smb_lam_app _ _ _ _ _ _ a k b HAR1 Hbl Hin ltac:(lia)) as (_ & _ & Hab).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* a root at or above YM05.alloc_ceiling is on the real stack (a Lam block and a fake frame end below it) *)
Lemma smb_root_stack : forall p t D, prhex_tree (PA := PI_prog_B) ly S Lam W regs mem p t D ->
  YM05.alloc_ceiling <= p -> spZ regs <= p /\ p + 56 <= ly_stk_hi ly.
Proof.
intros p t D (_ & Hh & _) Hpc. pose proof HFPRE as [(HAR & _) _].
destruct Hh as [(b & m & Hin & Hb1 & Hb2) | [(cid & pos & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- pose proof HLED as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & _).
  cbn [fst snd] in *. pose proof (@cf_head_nonneg cp) as Hc0.
  destruct (alx_blocks rsegs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hcl & _).
  assert (Hmc : 0 <= m + cf_head) by lia. pose proof (req_size_pos (m + cf_head) Hmc) as [Hq1 Hq2]. lia.
- destruct (frames_bounds_x rsegs B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hfc & _). lia.
- split; assumption.
Qed.

(* THE CHAIN AT pa for the recursive call (s0 = a there): below the ceiling achain_low; on the real stack (then
   spZ regs <= pa) the unwinder's walk from pa reads only present words (HSUP, as astack_up_x at the entry sp,
   carried to the call state by astack_up_journal_x) *)
Lemma smb_chain_pa : forall ly1 S1 Hp1 W1 m1 md1 k1, smb_INV ly1 S1 Hp1 W1 m1 md1 k1 ->
  exists ch1, achain ly1 (aview rsegs (w_H W1) m1) (spZ regs + -160) pa ch1.
Proof.
intros ly1 S1 Hp1 W1 m1 md1 k1 (HJ & _).
pose proof HJ as (HAR1 & Hlle & _).
destruct Hlle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof HFPRE as [HPRE _]. pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hcl & Hlo & _ & _ & _ & Htop & Htophi).
pose proof smb_stk as FS. unfold ESTACK in FS.
destruct (smb_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & _).
apply smb_achain_ex; [exact Pa3|].
intros Hc Ht. destruct (smb_root_stack _ _ _ HTA Hc) as [Hs1 Hs2].
pose proof (astack_up_journal_x rsegs B PST ARx HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HSUP Hs1)) as HUP1.
split; [lia|].
intros a Ha1 Ha2. apply smb_rdword_some. intros k Hk.
assert (Hpr : apresent (w_H W1) m1 (a + k)) by (apply HUP1; lia).
pose proof (aview_some_of_apresent rsegs _ _ _ Hpr) as Hs.
destruct (aview rsegs (w_H W1) m1 (a + k)) as [v|] eqn:Ev; [|contradiction].
exists v. split; [reflexivity|]. exact (smb_aview_nonneg _ _ _ _ _ Ev).
Qed.

(* the facts of the canonical loop state hold in every valuation that keeps the entry's registers and the shadow
   offset, at a count i with 56 i below 2 ^ 30 *)
Lemma smb_factsL : forall Ex0 regsJ i, env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF ->
  0 <= i -> 56 * i < 2 ^ 30 -> facts_ok (smb_EL Ex0 regsJ i) smb_fsL.
Proof.
intros Ex0 regsJ i [HA1 HA2] E32 Hi0 Hi.
pose proof smb_entry_ok as (_ & _ & _ & _ & _ & _ & _ & _ & HF0). change (ss_facts smb_ss0) with smb_fs0 in HF0.
assert (HF1 : facts_ok (smb_EL Ex0 regsJ i) smb_fs0).
{ apply (facts_ok_agree 33 (Ereg regs [w64 SHADOW_OFF]) _ smb_fs0); [| vm_compute; reflexivity | exact HF0].
  split.
  - intros k Hk. rewrite smb_EL_low by lia. destruct (Nat.eq_dec k 32) as [-> | Hk'].
    + rewrite E32. symmetry. exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0).
    + apply HA1. lia.
  - unfold smb_EL, havoc. cbn [ed]. exact HA2. }
destruct HF1 as (HAt & _). unfold smb_fsL. split; [|split; exact I]. cbn [f_atoms].
apply smb_atoms_ok_app; [exact HAt|].
cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite smb_EL_i, smb_EL_i8, smb_EL_i56.
rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 3) with 8.
repeat split; try lia; try apply Z.mod_1_r.
- rewrite Z.mul_comm. apply Z_mod_mult.
- replace (56 * i) with (7 * i * 8) by ring. apply Z_mod_mult.
Qed.

(* a state at the loop head or at the kids part, re-expressed in the canonical form *)
Lemma smb_canonL : forall Ex0 Ecur ss (ms : machine_state) (H : word -> bool) pc i,
  st_ok rsegs Ecur ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  env_agree 40 Ex0 Ecur -> ss_mem ss = smb_frameL :: tl (ss_mem ss) -> smb_fixed_ok (ss_regs ss) = true ->
  getr (ms_regs ms) 19 = Z_to_bv 64 i -> getr (ms_regs ms) 26 = Z_to_bv 64 (8 * i) ->
  getr (ms_regs ms) 27 = Z_to_bv 64 (56 * i) ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF -> 0 <= i -> 56 * i < 2 ^ 30 ->
  st_ok rsegs (smb_EL Ex0 (ms_regs ms) i) (smb_ssL pc) (restrict H ms).
Proof.
intros Ex0 Ecur ss ms H pc i HS Hrv Hpc HA Hm Hfix R19 R26 R27 HE0 E32 Hi0 Hi.
assert (HCL : env_agree 40 Ecur (smb_EL Ex0 (ms_regs ms) i)).
{ destruct HA as [HA1 HA2]. split.
  - intros k Hk. rewrite smb_EL_low by exact Hk. symmetry. exact (HA1 k Hk).
  - unfold smb_EL, havoc. cbn [ed]. symmetry. exact HA2. }
pose proof HS as (_ & _ & _ & _ & _ & _ & Hregs & Hmem & _).
unfold smb_ssL. apply (smb_st_ok_canon rsegs Ecur _ ss (restrict H ms) pc smb_srL smb_rsL smb_fsL HS Hpc Hrv).
- apply regs_ok_by_cases. intros rr Hin. unfold all_regs in Hin. cbn [In] in Hin.
  change (ms_regs (restrict H ms)) with (ms_regs ms) in *.
  repeat (destruct Hin as [<- | Hin]; [smb_regcase Hregs Hfix HCL R19 R26 R27 |]). destruct Hin.
- apply (mem_ok_agree rsegs 40 Ecur); [exact HCL | vm_compute; reflexivity |].
  rewrite Hm in Hmem. exact (smb_mem_ok_hd _ _ _ _ Hmem).
- apply smb_factsL; assumption.
Qed.

(* the value of an atom in a valuation the walk has built: a fresh hand-loaded / rebound atom, a loop counter, or an
   older atom under the havocs *)
Ltac smb_ew :=
  first [ apply smb_ew_new1 | apply smb_EL_i | apply smb_EL_i8 | apply smb_EL_i56 | assumption
        | (rewrite ew_havoc_old by lia; smb_ew) ].
(* a fact on a fresh hand-loaded atom k holding v *)
Ltac smb_fact HS k f v :=
  lazymatch type of HS with st_ok ?sg ?Ek ?ssk ?mk =>
    let HSa := fresh "HSa" in
    assert (HSa : st_ok sg Ek (add_atom ssk k f) mk)
      by (apply (smb_st_ok_add_atom sg Ek ssk mk k f HS);
          unfold afact_ok; cbn [af_lo af_hi af_al2];
          replace (ew Ek k) with (Z_to_bv 64 v) by (symmetry; smb_ew);
          rewrite unsigned_lit_small by lia; change (2 ^ 0) with 1; change (2 ^ 3) with 8;
          repeat split; first [lia | apply Z.mod_1_r | (apply smb_mod8_of16; assumption)]);
    let ssa := eval vm_compute in (add_atom ssk k f) in change (add_atom ssk k f) with ssa in HSa;
    clear HS; rename HSa into HS
  end.
(* the canonical form at pc with the counters unchanged (atoms 56 / 57 / 58 in s3 / s10 / s11) *)
Ltac smb_canon0 Ex0 Eb ssb mb W1 HSb HE40 HE0 E32 pc :=
  apply (smb_canonL Ex0 Eb ssb mb (w_H W1) pc _ HSb);
  [ vm_compute; reflexivity | vm_compute; reflexivity | env_agree_chain HE40 | vm_compute; reflexivity
  | vm_compute; reflexivity
  | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 19%bv HSb); smb_regv (SOff 56 0); rewrite smbk_SOff0; smb_ew
  | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 26%bv HSb); smb_regv (SOff 57 0); rewrite smbk_SOff0; smb_ew
  | rewrite (st_ok_restrict_reg rsegs (w_H W1) Eb ssb mb 27%bv HSb); smb_regv (SOff 58 0); rewrite smbk_SOff0; smb_ew
  | exact HE0 | exact E32 | lia | lia ].

Section CT.
Variables (numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB : Z).
Hypothesis HhA0 : pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA.
Hypothesis HhB0 : pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB.
Hypothesis Etag : tag ta = tag tb.
Hypothesis En : nA = nB.
Hypothesis Hcont : tag ta = 5 \/ tag ta = 6.

(* the counter bound: item i < n lies in the kid array (kidsA, 56 capA), a block of Lam below cf_malloc_max *)
Lemma smb_ibound : forall i : nat, (i < Z.to_nat nA)%nat -> 56 * Z.of_nat i + 56 < 2 ^ 30.
Proof.
intros i Hi.
pose proof (smb_its_len ta Hcont) as LtA.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
destruct (nth_error (smb_its ta) i) as [[nm u]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nm u (proj1 HTA) HhA0 Ei) as (Lk & Bk & _).
pose proof (smb_lam_size _ _ Lk). pose proof (@YG08cf.cf_malloc_max_bound cp). pose proof (@cf_head_nonneg cp). lia.
Qed.

(* a canonical state at pc with i items done gives the post *)
Definition smb_LH (pc : Z) (i : nat) : Prop :=
  forall Ex0 (ms : machine_state) ly1 S1 Hp1 W1 md1 k1,
  st_ok rsegs (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) (smb_ssL pc) (restrict (w_H W1) ms) ->
  smb_INV ly1 S1 Hp1 W1 (ms_mem ms) md1 k1 ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex0 -> ew Ex0 32 = w64 SHADOW_OFF ->
  SRr rsegs W1 (mkCfg ms md1) smb_POST.
(* ... when rr + i = n, rr > 0 and the first i items are equal *)
Definition smb_LHp (pc : Z) (rr i : nat) : Prop :=
  (rr + i)%nat = Z.to_nat nA -> (0 < rr)%nat ->
  (forall j, (j < i)%nat -> nth_error (smb_its ta) j = nth_error (smb_its tb) j) -> smb_LH pc i.
(* the keys of item i are equal (objects) *)
Definition smb_KE (i : nat) : Prop :=
  tag ta = 6 -> option_map fst (nth_error (smb_its ta) i) = option_map fst (nth_error (smb_its tb) i).

(* the kids part SMB_AT 0x278: the kids of item i through the recursive call at SMB_AT 0x2ec, then n again and the
   next item *)
Lemma smb_kids : forall rr i, ((1 < rr)%nat -> smb_LHp (SMB_AT 0x1bc) (rr - 1) (Datatypes.S i)) -> smb_KE i ->
  smb_LHp (SMB_AT 0x278) rr i.
Proof.
intros rr i Hnext KE Hri Hr0 Hpre Ex0 ms ly1 S1 Hp1 W1 md1 k1 HS HI HE0 E32.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)))
  by (unfold smb_EL; env_agree_chain HE0).
smb_pre (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) HAE.
pose proof HI as (HJ & _).
assert (Usp : bv_unsigned (ew (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) 2) = spZ regs)
  by (destruct HAE as [HA _]; rewrite (HA 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32L : ew (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) 32 = w64 SHADOW_OFF)
  by (rewrite smb_EL_low by lia; exact E32).
assert (SHOK : sh_ok rsegs smb_Bx smb_SH (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) (mrestrict (w_H W1) (ms_mem ms)))
  by (destruct (smb_ras _ _ _ _ _ _ _ HI) as [Ra Rb]; apply smb_shok; [exact E10 | exact E11 | exact E32L
      | rewrite <- (aview_rd_of rsegs); exact Ra | rewrite <- (aview_rd_of rsegs); exact Rb]).
assert (HE40 : env_agree 40 Ex0 (smb_EL Ex0 (ms_regs ms) (Z.of_nat i))) by (unfold smb_EL; apply env_agree_havoc).
pose proof (smb_ibound i ltac:(lia)) as IB.
pose proof (smb_ibound (Z.to_nat nA - 1) ltac:(lia)) as IBn.
pose proof (@alloc_ceiling_lt rc) as Hac47.
pose proof smb_pc_bounds as PCB.
(* ---- item i of both trees ---- *)
pose proof (smb_its_len ta Hcont) as LtA. pose proof (smb_its_len tb ltac:(rewrite <- Etag; exact Hcont)) as LtB.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
destruct (nth_error (smb_its ta) i) as [[nmA uA]|] eqn:EiA; [|apply nth_error_None in EiA; lia].
destruct (nth_error (smb_its tb) i) as [[nmB uB]|] eqn:EiB; [|apply nth_error_None in EiB; lia].
assert (Hnm : nmA = nmB).
{ destruct Hcont as [H5 | H6].
  - rewrite (smb_its_key5 ta i nmA uA H5 EiA), (smb_its_key5 tb i nmB uB ltac:(lia) EiB). reflexivity.
  - pose proof (KE H6) as Hk. rewrite EiA, EiB in Hk. cbn in Hk. injection Hk as Hk. exact Hk. }
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA (proj1 HTA) HhA0 EiA) as (LkA0 & BkA0 & _).
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB (proj1 HTB) HhB0 EiB) as (LkB0 & BkB0 & _).
pose proof (smb_lam_app _ _ _ _ _ _ kidsA _ kidsA HAR eq_refl LkA0 ltac:(lia)) as (HkA0 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ kidsB _ kidsB HAR eq_refl LkB0 ltac:(lia)) as (HkB0 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ kidsA _ (kidsA + 56 * Z.of_nat i + 55) HAR eq_refl LkA0 ltac:(lia)) as (HkA1 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ kidsB _ (kidsB + 56 * Z.of_nat i + 55) HAR eq_refl LkB0 ltac:(lia)) as (HkB1 & _ & _).
(* ---- SMB_AT 0x278..0x27c: the shadow of a + 24; 0x280 a + 24 from 48(sp); 0x284 ld a0, 0(a0): kids of a (atom 59) ---- *)
smb_step HS HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
smb_hl_ld HS (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 24) kidsA.
{ smb_regv (SOff 10 24). apply smb_denot_off; [smb_ew | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAc as (_ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh1 math1 HS1 Hm1. clear HS.
smb_bk HS1 HJ SHOK Usp HI mh1 math1 Hm1.
smb_fact HS1 59%nat (mkAF 4096 (2 ^ 47) 0) kidsA.
(* ---- 0x288..0x2a0: 56 i, kids + 56 i, the null check (decided); 0x2a4 bltu a2, a0 (kids + 56 i < kids): not taken ---- *)
smb_step HS1 HJ SHOK HI Usp FS Hc'.
smb_branch HS1.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ltu_U, (smb_U_add_mul56 Ek 56 59 (Z.of_nat i) kidsA ltac:(smb_ew) ltac:(smb_ew) ltac:(lia) ltac:(lia)
      ltac:(lia)), (U_atom Ek 59 kidsA ltac:(smb_ew) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc. lia. }
intros _ HS1.
(* ---- 0x2a8..0x2bc: the overflow check of i * 56: not taken ---- *)
smb_step HS1 HJ SHOK HI Usp FS Hc'.
smb_branch HS1.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ne_U, (smb_U_mulh56 Ek 56 (Z.of_nat i) ltac:(smb_ew) ltac:(lia) ltac:(lia)), U_lit in Hc by lia end.
  cbn in Hc. discriminate Hc. }
intros _ HS1.
(* ---- 0x2c0..0x2c4: the shadow of b + 24; 0x2c8 ld a2, 0(s6): kids of b (atom 60) ---- *)
smb_step HS1 HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBc.
smb_hl_ld HS1 (12%bv : bv 5) (22%bv : bv 5) (0%bv : bv 12) (pb + 24) kidsB.
{ smb_regv (SOff 11 24). apply smb_denot_off; [smb_ew | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhBc as (_ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBc as (_ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh2 math2 HS2 Hm2. clear HS1.
smb_bk HS2 HJ SHOK Usp HI mh2 math2 Hm2.
smb_fact HS2 60%nat (mkAF 4096 (2 ^ 47) 0) kidsB.
(* ---- 0x2cc add a1, a1, a2; 0x2d0 bltu a1, a2 (kids + 56 i < kids, b): not taken ---- *)
smb_step HS2 HJ SHOK HI Usp FS Hc'.
smb_branch HS2.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ltu_U, (smb_U_add_mul56 Ek 56 60 (Z.of_nat i) kidsB ltac:(smb_ew) ltac:(smb_ew) ltac:(lia) ltac:(lia)
      ltac:(lia)), (U_atom Ek 60 kidsB ltac:(smb_ew) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc. lia. }
intros _ HS2.
(* ---- 0x2d4..0x2e0: the null check (decided); 0x2e4 / 0x2e8 the kid addresses; 0x2ec jal same ---- *)
smb_step_to HS2 HJ SHOK HI Usp FS Hc' (SMB_AT 0).
pose proof (smb_its_depth _ _ _ _ EiA) as DuA.
assert (Hn1 : (1 <= n)%nat) by lia.
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NAc NBc].
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk.
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc HhAk EiA) as (LkA & BkA & (D1A & IncA & NkA) & _).
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc HhBk EiB) as (LkB & BkB & (D1B & IncB & NkB) & _).
pose proof HI as (HJc & HSI & HHpI & HblI & HLI & HMNI). pose proof HJc as (HARc & _).
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 (restrict _ ?mc) => rename mc into MC end.
destruct (smb_kid_tree (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MC) kidsA (56 * capA) i uA D1A HLED HARc HblI HHpI LkA BkA NkA) as (HTkA & HfA).
destruct (smb_kid_tree (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MC) kidsB (56 * capB) i uB D1B HLED HARc HblI HHpI LkB BkB NkB) as (HTkB & HfB).
(* ---- the registers at the call ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  assert (R10 : getr (ms_regs MC) 10 = w64 (kidsA + 56 * Z.of_nat i))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 10%bv HS2); smb_regv (SAlu ALU_ADD (SOff 58 0) (SOff 59 0));
        unfold w64; rewrite (Z.add_comm kidsA); apply smb_denot_add; [smb_ew | smb_ew | lia | lia | lia]);
  assert (R11 : getr (ms_regs MC) 11 = w64 (kidsB + 56 * Z.of_nat i))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 11%bv HS2); smb_regv (SAlu ALU_ADD (SOff 58 0) (SOff 60 0));
        unfold w64; rewrite (Z.add_comm kidsB); apply smb_denot_add; [smb_ew | smb_ew | lia | lia | lia]);
  assert (R1 : getr (ms_regs MC) 1 = Z_to_bv 64 (SMB_AT 0x2f0))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 1%bv HS2); smb_regv (SLit (SMB_AT 0x2f0)); reflexivity);
  assert (R8w : getr (ms_regs MC) 8 = w64 pa)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 8%bv HS2); smb_regv (SOff 10 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R8 : s0Z (ms_regs MC) = pa) by (unfold s0Z; rewrite R8w; unfold w64; apply unsigned_lit_small; lia);
  assert (R3 : getr (ms_regs MC) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 3%bv HS2); smb_regv (SOff 3 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R4 : getr (ms_regs MC) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 4%bv HS2); smb_regv (SOff 4 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R2 : getr (ms_regs MC) 2 = sv_denot E2 (SOff 2 (-160)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 MC 2%bv HS2); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs MC) = spZ regs + -160)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E2 (SOff 2 (-160)))) with (U E2 (SOff 2 (-160)));
        pose proof asan_consts as (AC1b & _);
        rewrite (smb_U_off E2 2 (-160) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned)
end.
assert (Praw : YK0s.ret_ok (Z_to_bv 64 (SMB_AT 0x2f0))) by (apply ret_ok_even; vm_compute; reflexivity).
assert (Hraw4 : 4096 <= bv_unsigned (Z_to_bv 64 (SMB_AT 0x2f0)))
  by (unfold SMB_AT in *; rewrite unsigned_lit_small by lia; lia).
(* the callee's sp is 160 below ours and the journal keeps the stack top: fpre's stack-top conjunct *)
assert (HSHc : spZ (ms_regs MC) + 64 <= ly_stk_hi ly1).
{ rewrite Rsp. pose proof HFPRE as (_ & _ & Hsh & _).
  destruct HJc as (_ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _) & _). rewrite Ehi. lia. }
(* the callee's return address is the listing's SMB_AT 0x2f0, below the ceiling *)
assert (HRAc : raZ (ms_regs MC) < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1. unfold SMB_AT in *. rewrite unsigned_lit_small by lia.
  pose proof (@alloc_ceiling_value rc) as [[Hcm _] _]. lia. }
(* the rounding mode is 0 at the callee's entry: same runs no float instruction, so it is ours (fpre's FRM0-ENTRY) *)
assert (HFRMc : YK0o.frm_zero (@YK11.fp_csr fx)) by (destruct HFPRE as (_ & _ & _ & _ & Hfrm); exact Hfrm).
destruct (smb_chain_pa _ _ _ _ _ _ _ HI) as (ch1 & Hach). rewrite <- R8 in Hach.
pose proof (smb_ro _ _ _ _ _ _ _ HI) as HROc.
assert (HfwA : forall z, pj_footR (kidsA + 56 * Z.of_nat i) D1A z ->
  ~ (spZ (ms_regs MC) - STK_same (n - 1) <= z < spZ (ms_regs MC))).
{ intros z Hz. pose proof (HfA z Hz). rewrite Rsp, smb_stk'. unfold ESTACK in *. lia. }
assert (HfwB : forall z, pj_footR (kidsB + 56 * Z.of_nat i) D1B z ->
  ~ (spZ (ms_regs MC) - STK_same (n - 1) <= z < spZ (ms_regs MC))).
{ intros z Hz. pose proof (HfB z Hz). rewrite Rsp, smb_stk'. unfold ESTACK in *. lia. }
(* the callee's guarded premise is vacuous: its root kidsA + 56 i is in a block of Lam, below YM05.alloc_ceiling and so
   below its sp *)
assert (HSUPc : spZ (ms_regs MC) <= kidsA + 56 * Z.of_nat i -> astack_up_x rsegs ly1 W1 (spZ (ms_regs MC)) (ms_mem MC)).
{ intros Hle. exfalso. rewrite Rsp in Hle. unfold ESTACK in *. lia. }
(* ---- SMB_AT 0x2ec jal same: the call through the induction hypothesis at nesting n - 1 (aj_call_x) ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
eapply SRr_bind;
[ eapply (aj_call_x (SK := SK) rsegs B PST ARx LAWS HSL W1 E2 ss2 MC _ (spZ regs) []
    ly S Hp W mem md [] ly1 S1 Hp1 _ _ (STK_same (n - 1)) [] (-160) (ew E2 2)
    (Z_to_bv 64 (SMB_AT 0x2f0)) ch1 _ HS2 eq_refl HJc R2 eq_refl Usp eq_refl ltac:(lia)
    ltac:(rewrite smb_stk'; unfold ESTACK; lia) ltac:(rewrite !smb_stk'; unfold ESTACK; lia) R3 R4 R1 Praw
    Hraw4 Hach);
  [ intros HPc;
    pose proof (IH (n - 1) ltac:(lia) ly1 S1 Hp1 W1 (ms_regs MC) (ms_mem MC) _ ch1
      (kidsA + 56 * Z.of_nat i) (kidsB + 56 * Z.of_nat i) uA uB D1A D1B Lam peak cnt fail ran most own
      (conj HPc (conj HROc (conj HSHc (conj HRAc HFRMc)))) HSUPc
      R10 R11 HTkA HTkB ltac:(lia) HfwA HfwB HLI) as HSM;
    unfold cfg_at, fpostm, fpost in HSM;
    change (pa_sigma (PAImg := PI_prog_B) AS_same) with (ss_pc ss2) in HSM; exact HSM
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W3 c3 _ (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & kc & -> & HJ3 & HJ1 & HP3 &
  ((Hrk & Hres & HnA & HnB & EHp & ES2 & Ebl & HL3) & Hmn3)).
(* ---- back at SMB_AT 0x2f0: the frame kept by the callee's journal inside the caller's; the invariant at W3 ---- *)
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  assert (HKR3 : Forall (region_kept rsegs E2 (ms_mem (restrict (w_H W1) MC)) (mrestrict (w_H W3) mem3)) (ss_mem ss2))
end.
{ cbn [ss_mem restrict ms_mem]. constructor; [|constructor].
  eapply (region_kept_stack_sub_x (SK := SK) rsegs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc
    2%nat (-160) 0 (-160) 0 _ (spZ regs) _ _ _ _ _ _ _ _ _ _ _ HJ1 HJ3 Usp); lia. }
assert (HI3 : smb_INV ly2 S2 Hp2 W3 mem3 md3 (k1 + kc)).
{ split; [exact HJ3|]. split; [exact (eq_trans ES2 HSI)|]. split; [exact (eq_trans EHp HHpI)|].
  split; [exact (eq_trans Ebl HblI)|]. split; [exact HL3|]. intros Hm. exact (Hmn3 (HMNI Hm)). }
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 _ =>
  pose proof (st_ok_after_call rsegs 61 E2 ss2 (restrict (w_H W1) MC) regs3 (mrestrict (w_H W3) mem3) (ss_mem ss2)
    (SMB_AT 0x2f0) HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP3 r Hr)) HKR3) as HS3;
  let ss3 := eval vm_compute in (ss_after_call ss2 (ss_mem ss2) 61 (SMB_AT 0x2f0)) in
  change (ss_after_call ss2 (ss_mem ss2) 61 (SMB_AT 0x2f0)) with ss3 in HS3;
  change (mkst regs3 (Z_to_bv 64 (SMB_AT 0x2f0)) (mrestrict (w_H W3) mem3) (seg_rom rsegs)) with
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (SMB_AT 0x2f0)) mem3 (seg_rom rsegs))) in HS3;
  assert (Usp3 : bv_unsigned (ew (havoc E2 61 (map (getr regs3) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs smb_Bx smb_SH (havoc E2 61 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3))
    by (destruct (smb_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply smb_shok; [smb_ew | smb_ew | smb_ew | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (U65 : U (havoc E2 61 (map (getr regs3) CLOB)) (SOff 65 0) = bv_unsigned (getr regs3 10))
    by (unfold U; rewrite smbk_SOff0; f_equal; exact (ew_havoc_new E2 61 (map (getr regs3) CLOB) 4 (getr regs3 10) ltac:(cbn; lia)))
end.
clear HS2 HKR3 HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
(* ---- SMB_AT 0x2f0 beqz a0: the kids differ -> 0 ---- *)
smb_branch HS3.
{ intros Hc HS3. rewrite branch_eq_U, U65, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (Hne : uA <> uB)
    by (destruct Hres as [(_ & Hv) | (Hne & _)]; [rewrite Hv in Hc; vm_compute in Hc; discriminate Hc | exact Hne]).
  smb_fin HS3 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hne. rewrite Et in EiA. rewrite EiA in EiB.
  injection EiB as _ Eu. exact Eu. }
intros Hc HS3. rewrite branch_eq_U, U65, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
assert (Heq : uA = uB)
  by (destruct Hres as [(Heq & _) | (_ & Hv)]; [exact Heq | rewrite Hv in Hc; vm_compute in Hc; congruence]).
assert (Hpre' : forall j, (j < Datatypes.S i)%nat -> nth_error (smb_its ta) j = nth_error (smb_its tb) j).
{ intros j Hj. destruct (Nat.eq_dec j i) as [-> | Hne]; [rewrite EiA, EiB, Hnm, Heq; reflexivity | apply Hpre; lia]. }
(* ---- 0x2f4..0x2f8: the shadow of a + 40; 0x2fc ld a0, 0(s2): a's n again (hand load, atom 77) ---- *)
smb_step HS3 HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAn.
smb_hl_ld HS3 (10%bv : bv 5) (18%bv : bv 5) (0%bv : bv 12) (pa + 40) nA.
{ smb_regv (SOff 10 40). apply smb_denot_off; [smb_ew | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAn as (_ & _ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAn as (_ & _ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh4 math4 HS4 Hm4. clear HS3.
smb_bk HS4 HJ SHOK Usp HI mh4 math4 Hm4.
(* ---- 0x300..0x308: i + 1, 56 (i + 1), 8 (i + 1); 0x30c bgeu s3, a0: the last item -> 1 ---- *)
smb_step HS4 HJ SHOK HI Usp FS Hc'.
smb_branch HS4.
{ intros Hc1 HS4.
  lazymatch type of HS4 with st_ok _ ?Ek _ _ =>
    rewrite branch_geu_U, (smb_U_off Ek 56 1 (Z.of_nat i) ltac:(smb_ew) ltac:(lia) ltac:(lia)),
      (U_atom Ek 77 nA ltac:(smb_ew) ltac:(lia)) in Hc1 end.
  apply negb_true_iff, Z.ltb_ge in Hc1.
  smb_fin HS4 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply smb_its_inj; [exact Etag | exact Hcont |].
  apply smb_list_eq_nth; [lia |]. intros j Hj. apply Hpre'. lia. }
intros Hc1 HS4.
lazymatch type of HS4 with st_ok _ ?Ek _ _ =>
  rewrite branch_geu_U, (smb_U_off Ek 56 1 (Z.of_nat i) ltac:(smb_ew) ltac:(lia) ltac:(lia)),
    (U_atom Ek 77 nA ltac:(smb_ew) ltac:(lia)) in Hc1 end.
apply negb_false_iff, Z.ltb_lt in Hc1.
pose proof (smb_ibound (Datatypes.S i) ltac:(lia)) as IB'.
(* ---- 0x310 j 0x1bc: the next loop head, in the canonical form ---- *)
smb_step_to HS4 HJ SHOK HI Usp FS Hc' (SMB_AT 0x1bc).
lazymatch type of HS4 with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
  assert (HL' : st_ok rsegs (smb_EL Ex0 (ms_regs mb) (Z.of_nat (Datatypes.S i))) (smb_ssL (SMB_AT 0x1bc))
    (restrict (w_H W3) mb));
  [ apply (smb_canonL Ex0 Eb ssb mb (w_H W3) (SMB_AT 0x1bc) _ HS4); [vm_compute; reflexivity | vm_compute; reflexivity
      | env_agree_chain HE40 | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 19%bv HS4); smb_regv (SOff 56 1);
        rewrite (smb_denot_off Eb 56 1 (Z.of_nat i)); [f_equal; lia | smb_ew | lia | lia]
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 26%bv HS4); smb_regv (SOff 57 8);
        rewrite (smb_denot_off Eb 57 8 (8 * Z.of_nat i)); [f_equal; lia | smb_ew | lia | lia]
      | rewrite (st_ok_restrict_reg rsegs (w_H W3) Eb ssb mb 27%bv HS4); smb_regv (SOff 58 56);
        rewrite (smb_denot_off Eb 58 56 (56 * Z.of_nat i)); [f_equal; lia | smb_ew | lia | lia]
      | exact HE0 | exact E32 | lia | lia ]
  | apply (Hnext ltac:(lia) ltac:(lia) ltac:(lia) Hpre' Ex0 mb ly2 S2 Hp2 W3 _ _ HL' HI HE0 E32) ]
end.
Qed.

(* the loop head SMB_AT 0x1bc: the tag of a again; an array goes to its kids part SMB_AT 0x278, an object first
   compares key i (strcmp at SMB_AT 0x270) *)
Lemma smb_head : forall rr i, (smb_KE i -> smb_LHp (SMB_AT 0x278) rr i) -> smb_LHp (SMB_AT 0x1bc) rr i.
Proof.
intros rr i Hkids Hri Hr0 Hpre Ex0 ms ly1 S1 Hp1 W1 md1 k1 HS HI HE0 E32.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)))
  by (unfold smb_EL; env_agree_chain HE0).
smb_pre (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) HAE.
pose proof HI as (HJ & _).
assert (Usp : bv_unsigned (ew (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) 2) = spZ regs)
  by (destruct HAE as [HA _]; rewrite (HA 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32L : ew (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) 32 = w64 SHADOW_OFF)
  by (rewrite smb_EL_low by lia; exact E32).
assert (SHOK : sh_ok rsegs smb_Bx smb_SH (smb_EL Ex0 (ms_regs ms) (Z.of_nat i)) (mrestrict (w_H W1) (ms_mem ms)))
  by (destruct (smb_ras _ _ _ _ _ _ _ HI) as [Ra Rb]; apply smb_shok; [exact E10 | exact E11 | exact E32L
      | rewrite <- (aview_rd_of rsegs); exact Ra | rewrite <- (aview_rd_of rsegs); exact Rb]).
assert (HE40 : env_agree 40 Ex0 (smb_EL Ex0 (ms_regs ms) (Z.of_nat i))) by (unfold smb_EL; apply env_agree_havoc).
pose proof (smb_ibound i ltac:(lia)) as IB.
pose proof (@alloc_ceiling_lt rc) as Hac47.
pose proof smb_pc_bounds as PCB.
(* ---- SMB_AT 0x1bc..0x1c0: the shadow of a's tag; 0x1c4 lw a0, 0(s0): the tag of a again (hand load, atom 59) ---- *)
smb_step HS HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAc.
smb_hl_lw HS (10%bv : bv 5) (8%bv : bv 5) pa (tag ta).
{ smb_regv (SOff 10 0). rewrite smbk_SOff0. smb_ew. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAc as (_ & (_ & Hv) & _). exact Hv. }
{ pose proof (smb_tag_range ta). lia. }
intros mh0 math0 HSq Hm0. clear HS.
smb_bk HSq HJ SHOK Usp HI mh0 math0 Hm0.
smb_step HSq HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0x1cc bne a0, a1 (a1 = 6): an array goes to SMB_AT 0x278 ---- *)
smb_branch HSq.
{ intros Hc HSq.
  lazymatch type of HSq with st_ok _ ?Ek _ _ =>
    rewrite branch_ne_U, (U_atom Ek 59 (tag ta) ltac:(smb_ew) ltac:(lia)), U_lit in Hc by lia end.
  apply negb_true_iff, Z.eqb_neq in Hc.
  smb_step_to HSq HJ SHOK HI Usp FS Hc' (SMB_AT 0x278).
  lazymatch type of HSq with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
    assert (HL' : st_ok rsegs (smb_EL Ex0 (ms_regs mb) (Z.of_nat i)) (smb_ssL (SMB_AT 0x278)) (restrict (w_H W1) mb));
    [ smb_canon0 Ex0 Eb ssb mb W1 HSq HE40 HE0 E32 (SMB_AT 0x278)
    | apply (Hkids ltac:(intros H6; exfalso; lia) Hri Hr0 Hpre Ex0 mb ly1 S1 Hp1 W1 _ _ HL' HI HE0 E32) ]
  end. }
intros Hc HSq.
lazymatch type of HSq with st_ok _ ?Ek _ _ =>
  rewrite branch_ne_U, (U_atom Ek 59 (tag ta) ltac:(smb_ew) ltac:(lia)), U_lit in Hc by lia end.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Ht6.
(* ---- an object: key i ---- *)
pose proof (smb_its_len ta Hcont) as LtA. pose proof (smb_its_len tb ltac:(rewrite <- Etag; exact Hcont)) as LtB.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
destruct (nth_error (smb_its ta) i) as [[nmA uA]|] eqn:EiA; [|apply nth_error_None in EiA; lia].
destruct (nth_error (smb_its tb) i) as [[nmB uB]|] eqn:EiB; [|apply nth_error_None in EiB; lia].
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA (proj1 HTA) HhA0 EiA) as (_ & _ & _ & HkeyA0).
destruct (HkeyA0 Ht6) as (LkeyA & BkeyA & _).
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB (proj1 HTB) HhB0 EiB) as (_ & _ & _ & HkeyB0).
destruct (HkeyB0 ltac:(lia)) as (LkeyB & BkeyB & _).
pose proof (smb_lam_al _ _ LkeyA) as AlA. pose proof (smb_lam_al _ _ LkeyB) as AlB.
pose proof (smb_lam_app _ _ _ _ _ _ keysA _ keysA HAR eq_refl LkeyA ltac:(lia)) as (HsA0 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ keysA _ (keysA + 8 * Z.of_nat i) HAR eq_refl LkeyA ltac:(lia)) as (HsA & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ keysA _ (keysA + 8 * Z.of_nat i + 7) HAR eq_refl LkeyA ltac:(lia)) as (HsA7 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ keysB _ keysB HAR eq_refl LkeyB ltac:(lia)) as (HsB0 & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ keysB _ (keysB + 8 * Z.of_nat i) HAR eq_refl LkeyB ltac:(lia)) as (HsB & _ & _).
pose proof (smb_lam_app _ _ _ _ _ _ keysB _ (keysB + 8 * Z.of_nat i + 7) HAR eq_refl LkeyB ltac:(lia)) as (HsB7 & _ & _).
(* ---- SMB_AT 0x1d0..0x1dc: the shadow of a + 32, a + 32 from 40(sp); 0x1e0 ld a1, 0(a0): keys of a (atom 60) ---- *)
smb_step HSq HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk.
smb_hl_ld HSq (11%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pa + 32) keysA.
{ smb_regv (SOff 10 32). apply smb_denot_off; [smb_ew | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhAk as (_ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhAk as (_ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh1 math1 HS1 Hm1. clear HSq.
smb_bk HS1 HJ SHOK Usp HI mh1 math1 Hm1.
smb_fact HS1 60%nat (mkAF 4096 (2 ^ 47) 3) keysA.
(* ---- SMB_AT 0x1e4 add a0, a1, s10: the slot of key i of a, named (atom 61) with its shadow entry ---- *)
smb_step_to HS1 HJ SHOK HI Usp FS Hc' (SMB_AT 0x1e8).
lazymatch type of HS1 with st_ok _ ?E1 ?ss1 (restrict _ ?m1) =>
  pose proof (smb_rebind E1 ss1 (w_H W1) m1 61 10%bv (Z_to_bv 64 (keysA + 8 * Z.of_nat i)) HS1 eq_refl
    ltac:(vm_compute; reflexivity) eq_refl
    ltac:(rewrite (st_ok_restrict_reg rsegs (w_H W1) E1 ss1 m1 10%bv HS1);
          smb_regv (SAlu ALU_ADD (SOff 57 0) (SOff 60 0)); rewrite (Z.add_comm keysA);
          apply smb_denot_add; [smb_ew | smb_ew | lia | lia | lia])) as HSr;
  let ssr := eval vm_compute in (set_regs_pc ss1 [(10%bv, SOff 61 0)] (ss_pc ss1)) in
  change (set_regs_pc ss1 [(10%bv, SOff 61 0)] (ss_pc ss1)) with ssr in HSr;
  pose proof (smb_st_ok_add_atom rsegs _ _ _ 61 (mkAF 4096 (2 ^ 47 - 8) 0) HSr
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite smb_ew_new1, unsigned_lit_small by lia;
          change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)) as HSr2;
  let ssr2 := eval vm_compute in (add_atom ssr 61 (mkAF 4096 (2 ^ 47 - 8) 0)) in
  change (add_atom ssr 61 (mkAF 4096 (2 ^ 47 - 8) 0)) with ssr2 in HSr2;
  assert (Uspr : bv_unsigned (ew (havoc E1 61 [Z_to_bv 64 (keysA + 8 * Z.of_nat i)]) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOKr : sh_ok rsegs smb_Bx (smb_SH ++ [mkSHE 61 0 8]) (havoc E1 61 [Z_to_bv 64 (keysA + 8 * Z.of_nat i)])
    (mrestrict (w_H W1) (ms_mem m1)))
    by (unfold sh_ok; apply Forall_app; split;
        [ apply (sh_ok_agree rsegs smb_Bx smb_SH 61 E1); [apply env_agree_havoc | vm_compute; reflexivity | exact SHOK]
        | apply Forall_cons; [| apply Forall_nil];
          apply (smb_slot_shent _ _ _ _ _ _ _ _ 61 (keysA + 8 * Z.of_nat i) keysA (8 * capA) HI);
          [apply smb_ew_new1 | smb_ew | exact LkeyA | lia | lia] ])
end.
clear HS1 HSr SHOK Usp. rename HSr2 into HS1. rename SHOKr into SHOK. rename Uspr into Usp.
(* ---- SMB_AT 0x1e8 bltu a0, a1 (the slot below the array): not taken ---- *)
smb_branch HS1.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ltu_U, (U_atom Ek 61 (keysA + 8 * Z.of_nat i) ltac:(smb_ew) ltac:(lia)),
      (U_atom Ek 60 keysA ltac:(smb_ew) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc. lia. }
intros _ HS1.
(* ---- SMB_AT 0x1ec..0x1fc: the null checks (decided); 0x200..0x208 the alignment of the slot: not taken ---- *)
smb_step HS1 HJ SHOK HI Usp FS Hc'.
smb_branch HS1.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ne_U, (smb_U_and7 Ek 57 60 (8 * Z.of_nat i) keysA ltac:(smb_ew) ltac:(smb_ew) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(apply smb_mod8_add8; apply smb_mod8_of16; exact AlA)), U_lit in Hc by lia end.
  cbn in Hc. discriminate Hc. }
intros _ HS1.
(* ---- SMB_AT 0x20c..0x224: the shadow of the slot and of b + 32; 0x228 b + 32 from 24(sp); 0x22c ld a2, 0(a1): keys
   of b (atom 62) ---- *)
smb_step HS1 HJ SHOK HI Usp FS Hc'.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk.
smb_hl_ld HS1 (12%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (pb + 32) keysB.
{ smb_regv (SOff 11 32). apply smb_denot_off; [smb_ew | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhBk as (_ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhBk as (_ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh2 math2 HS2 Hm2. clear HS1.
smb_bk HS2 HJ SHOK Usp HI mh2 math2 Hm2.
smb_fact HS2 62%nat (mkAF 4096 (2 ^ 47) 3) keysB.
(* ---- SMB_AT 0x230 add a1, a2, s10: the slot of key i of b, named (atom 63) with its shadow entry ---- *)
smb_step_to HS2 HJ SHOK HI Usp FS Hc' (SMB_AT 0x234).
lazymatch type of HS2 with st_ok _ ?E2 ?ss2 (restrict _ ?m2) =>
  pose proof (smb_rebind E2 ss2 (w_H W1) m2 63 11%bv (Z_to_bv 64 (keysB + 8 * Z.of_nat i)) HS2 eq_refl
    ltac:(vm_compute; reflexivity) eq_refl
    ltac:(rewrite (st_ok_restrict_reg rsegs (w_H W1) E2 ss2 m2 11%bv HS2);
          smb_regv (SAlu ALU_ADD (SOff 57 0) (SOff 62 0)); rewrite (Z.add_comm keysB);
          apply smb_denot_add; [smb_ew | smb_ew | lia | lia | lia])) as HSr;
  let ssr := eval vm_compute in (set_regs_pc ss2 [(11%bv, SOff 63 0)] (ss_pc ss2)) in
  change (set_regs_pc ss2 [(11%bv, SOff 63 0)] (ss_pc ss2)) with ssr in HSr;
  pose proof (smb_st_ok_add_atom rsegs _ _ _ 63 (mkAF 4096 (2 ^ 47 - 8) 0) HSr
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite smb_ew_new1, unsigned_lit_small by lia;
          change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)) as HSr2;
  let ssr2 := eval vm_compute in (add_atom ssr 63 (mkAF 4096 (2 ^ 47 - 8) 0)) in
  change (add_atom ssr 63 (mkAF 4096 (2 ^ 47 - 8) 0)) with ssr2 in HSr2;
  assert (Uspr : bv_unsigned (ew (havoc E2 63 [Z_to_bv 64 (keysB + 8 * Z.of_nat i)]) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOKr : sh_ok rsegs smb_Bx ((smb_SH ++ [mkSHE 61 0 8]) ++ [mkSHE 63 0 8])
    (havoc E2 63 [Z_to_bv 64 (keysB + 8 * Z.of_nat i)]) (mrestrict (w_H W1) (ms_mem m2)))
    by (unfold sh_ok; apply Forall_app; split;
        [ apply (sh_ok_agree rsegs smb_Bx (smb_SH ++ [mkSHE 61 0 8]) 63 E2);
            [apply env_agree_havoc | vm_compute; reflexivity | exact SHOK]
        | apply Forall_cons; [| apply Forall_nil];
          apply (smb_slot_shent _ _ _ _ _ _ _ _ 63 (keysB + 8 * Z.of_nat i) keysB (8 * capB) HI);
          [apply smb_ew_new1 | smb_ew | exact LkeyB | lia | lia] ])
end.
clear HS2 HSr SHOK Usp. rename HSr2 into HS2. rename SHOKr into SHOK. rename Uspr into Usp.
(* ---- SMB_AT 0x234 bltu a1, a2: not taken ---- *)
smb_branch HS2.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ltu_U, (U_atom Ek 63 (keysB + 8 * Z.of_nat i) ltac:(smb_ew) ltac:(lia)),
      (U_atom Ek 62 keysB ltac:(smb_ew) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc. lia. }
intros _ HS2.
(* ---- SMB_AT 0x238..0x248: the null checks (decided); 0x24c..0x254 the alignment of b's slot: not taken ---- *)
smb_step HS2 HJ SHOK HI Usp FS Hc'.
smb_branch HS2.
{ intros Hc HSx. exfalso.
  lazymatch type of HSx with st_ok _ ?Ek _ _ =>
    rewrite branch_ne_U, (smb_U_and7 Ek 57 62 (8 * Z.of_nat i) keysB ltac:(smb_ew) ltac:(smb_ew) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(apply smb_mod8_add8; apply smb_mod8_of16; exact AlB)), U_lit in Hc by lia end.
  cbn in Hc. discriminate Hc. }
intros _ HS2.
(* ---- SMB_AT 0x258..0x264: the shadow of b's slot; 0x268 ld a0, 0(a0) / 0x26c ld a1, 0(a1): the key pointers ---- *)
smb_step HS2 HJ SHOK HI Usp FS Hc'.
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NAc3 NBc3].
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk3.
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc3 HhAk3 EiA) as (_ & _ & _ & HkeyA3).
destruct (HkeyA3 Ht6) as (_ & _ & xA' & kA' & RxA' & HcA').
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk3.
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc3 HhBk3 EiB) as (_ & _ & _ & HkeyB3).
destruct (HkeyB3 ltac:(lia)) as (_ & _ & xB' & kB' & RxB' & HcB').
smb_hl_ld HS2 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (keysA + 8 * Z.of_nat i) xA'.
{ smb_regv (SOff 61 0). rewrite smbk_SOff0. smb_ew. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct RxA' as (_ & Hv). exact Hv. }
{ destruct RxA' as (Hv & _). exact Hv. }
intros mh3 math3 HS3 Hm3. clear HS2.
smb_bk HS3 HJ SHOK Usp HI mh3 math3 Hm3.
smb_hl_ld HS3 (11%bv : bv 5) (11%bv : bv 5) (0%bv : bv 12) (keysB + 8 * Z.of_nat i) xB'.
{ smb_regv (SOff 63 0). rewrite smbk_SOff0. smb_ew. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. rewrite Hm3. destruct RxB' as (_ & Hv). exact Hv. }
{ destruct RxB' as (Hv & _). exact Hv. }
intros mh4 math4 HS4 Hm4. clear HS3.
smb_bk HS4 HJ SHOK Usp HI mh4 math4 Hm4.
(* ---- SMB_AT 0x270 jal strcmp: the run keeps every byte below YM05.alloc_ceiling (the key slots, the key strings) ---- *)
rewrite <- Hm3, <- Hm4 in RxA', RxB'.
smb_run HS4 HJ SHOK; [ smb_awr Usp FS | ].
lazymatch goal with HFr0 : frame_of ?Ef ?rsf (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
  pose proof (smbk_frame_below rsegs Ef rsf (w_H W1) m0 m1 HFr0 ltac:(smb_wb Usp Hc')) as HBk;
  assert (RxA2 : rd_u64 rsegs (mrestrict (w_H W1) m1) (keysA + 8 * Z.of_nat i) xA')
    by (destruct RxA' as (Hr & Hv); split; [exact Hr|];
        apply (smbk_val_mem_keep (PA := PI_prog_B) _ _ _ _ _ Hv); intros q Hq; apply HBk; lia);
  assert (RxB2 : rd_u64 rsegs (mrestrict (w_H W1) m1) (keysB + 8 * Z.of_nat i) xB')
    by (destruct RxB' as (Hr & Hv); split; [exact Hr|];
        apply (smbk_val_mem_keep (PA := PI_prog_B) _ _ _ _ _ Hv); intros q Hq; apply HBk; lia)
end.
smb_inv_after HI HJ Usp Hc'.
(* the two keys at the current memory: their pointers are the loaded xA', xB' *)
destruct (smb_nodes _ _ _ _ _ _ _ HI) as [NAc4 NBc4].
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhAk4.
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhBk4.
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmA uA NAc4 HhAk4 EiA) as (_ & _ & _ & HkeyA4).
destruct (HkeyA4 Ht6) as (_ & _ & xA & kA & RxA & HcA).
destruct (smb_node_item _ _ _ _ _ _ _ _ _ _ _ _ i nmB uB NBc4 HhBk4 EiB) as (_ & _ & _ & HkeyB4).
destruct (HkeyB4 ltac:(lia)) as (_ & _ & xB & kB & RxB & HcB).
assert (ExA : xA = xA') by exact (proj1 (smb_num_eq rsegs _ _ _ _ xA xA' RxA RxA2) (fun _ _ => eq_refl)).
assert (ExB : xB = xB') by exact (proj1 (smb_num_eq rsegs _ _ _ _ xB xB' RxB RxB2) (fun _ _ => eq_refl)).
subst xA' xB'.
pose proof HI as (HJk & HSk & HHpk & Hblk & _). pose proof HJk as (HARk & _).
lazymatch type of HS4 with st_ok _ ?E6 ?ss6 (restrict _ ?msc) =>
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) E6 ss6 msc HS4 eq_refl) as Hshape;
  assert (Epc : ss_pc ss6 = SMB_STRCMP) by (vm_compute; reflexivity);
  assert (R10 : getr (ms_regs msc) 10 = w64 xA)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 10%bv HS4); smb_regv (SOff 64 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R11 : getr (ms_regs msc) 11 = w64 xB)
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 11%bv HS4); smb_regv (SOff 65 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (SMB_AT 0x274))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 1%bv HS4); smb_regv (SLit (SMB_AT 0x274)); reflexivity);
  assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 3%bv HS4); smb_regv (SOff 3 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 4%bv HS4); smb_regv (SOff 4 0);
        rewrite smbk_SOff0; smb_ew);
  assert (R2 : getr (ms_regs msc) 2 = sv_denot E6 (SOff 2 (-160)))
    by (rewrite (st_ok_restrict_reg rsegs (w_H W1) E6 ss6 msc 2%bv HS4); f_equal; vm_compute; reflexivity);
  assert (Rsp : spZ (ms_regs msc) = spZ regs + -160)
    by (unfold spZ; rewrite R2; change (bv_unsigned (sv_denot E6 (SOff 2 (-160)))) with (U E6 (SOff 2 (-160)));
        pose proof asan_consts as (AC1b & _);
        rewrite (smb_U_off E6 2 (-160) (spZ regs)); [reflexivity | | lia | lia];
        rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
  rename msc into MSC
end.
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) xA kA nmA HLED HARk Hblk HHpk HcA ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XA0 & XA1 & XA2 & XA3 & XAfb & XAsrc & XAlo & XAam & XAra & XAhv & XAtl).
pose proof (smb_str_ok (PA := PI_prog_B) B ARx LAWS SMB_BMAX SMB_STK64 SMB_FR64 ly S Hp W mem Lam peak cnt fail ran most own
  _ _ _ _ _ _ (ms_regs MSC) xB kB nmB HLED HARk Hblk HHpk HcB ltac:(rewrite Rsp; unfold ESTACK in *; lia))
  as (XB0 & XB1 & XB2 & XB3 & XBfb & XBsrc & XBlo & XBam & XBra & XBhv & XBtl).
pose proof (smb_ro _ _ _ _ _ _ _ HI) as Hrod.
rewrite Hshape at 1. rewrite Epc.
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) rsegs B PST ARx B_prog_relro_lo B_prog_relro_hi LAWS HSL
    SMB_STRCMP STRCMP W1
    (ms_regs MSC) (ms_mem MSC) _ (spZ regs) [] ly S Hp W mem md [] ly1 S1 Hp1 _ _ xA xB
    (Z.of_nat (length nmA)) (Z.of_nat (length nmB)) (-160) (Z_to_bv 64 (SMB_AT 0x274)) HJk R10 R11);
  try eassumption; try (unfold ESTACK in *; lia).
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha Hw. pose proof (XAlo a Ha). unfold ESTACK in *. lia.
  - intros a Ha Hw. pose proof (XBlo a Ha). unfold ESTACK in *. lia.
  - destruct HcA as (HlA & HkA & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ xA kA (Z.of_nat (length nmA) + 1) HLED
      HARk Hblk HlA ltac:(lia)).
  - destruct HcB as (HlB & HkB & _).
    exact (smb_amr8 ly S Hp W mem Lam peak cnt fail ran most own _ _ _ _ _ _ xB kB (Z.of_nat (length nmB) + 1) HLED
      HARk Hblk HlB ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* ---- back at SMB_AT 0x274: the invariant, the frame kept, the symbolic state resumed (atoms 66.., a0 = atom 70) ---- *)
pose proof asan_consts as (AC1 & _).
pose proof (smb_inv_ecall _ _ _ _ _ _ _ mem2 md2 (spZ regs + -160 - 2 * ESTACK) (spZ regs + -160) HI HJ3
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
  pose proof (st_ok_after_call rsegs 66 E6 ss6 (restrict (w_H W1) MSC) regs2 (mrestrict (w_H W1) mem2) (ss_mem ss6)
    (SMB_AT 0x274) HS4 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS7;
  let ss7 := eval vm_compute in (ss_after_call ss6 (ss_mem ss6) 66 (SMB_AT 0x274)) in
  change (ss_after_call ss6 (ss_mem ss6) 66 (SMB_AT 0x274)) with ss7 in HS7;
  change (mkst regs2 (Z_to_bv 64 (SMB_AT 0x274)) (mrestrict (w_H W1) mem2) (seg_rom rsegs)) with
    (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 (SMB_AT 0x274)) mem2 (seg_rom rsegs))) in HS7;
  assert (Usp3 : bv_unsigned (ew (havoc E6 66 (map (getr regs2) CLOB)) 2) = spZ regs)
    by (rewrite ew_havoc_old by lia; exact Usp);
  assert (SHOK3 : sh_ok rsegs smb_Bx smb_SH (havoc E6 66 (map (getr regs2) CLOB)) (mrestrict (w_H W1) mem2))
    by (destruct (smb_ras _ _ _ _ _ _ _ HI3) as [Ra Rb];
        apply smb_shok; [smb_ew | smb_ew | smb_ew | rewrite <- (aview_rd_of rsegs); exact Ra
          | rewrite <- (aview_rd_of rsegs); exact Rb]);
  assert (U70 : U (havoc E6 66 (map (getr regs2) CLOB)) (SOff 70 0) = bv_unsigned v)
    by (unfold U; rewrite smbk_SOff0; rewrite <- Hv;
        f_equal; exact (ew_havoc_new E6 66 (map (getr regs2) CLOB) 4 (getr regs2 10) ltac:(cbn; lia)))
end.
clear HS4 HKR HJ SHOK Usp HI. rename HI3 into HI. rename HJ3 into HJ. rename SHOK3 into SHOK. rename Usp3 into Usp.
assert (Ev0 : v = w64 0 <-> nmA = nmB)
  by (rewrite Hcmp; exact (smb_str_eq rsegs (w_H W1) (ms_mem MSC) _ _ _ _ _ _ _ HcA HcB)).
(* ---- SMB_AT 0x274 bnez a0: the keys differ -> 0 ---- *)
smb_branch HS7.
{ intros Hc HS7. rewrite branch_ne_U, U70, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  smb_fin HS7 HJ SHOK HI Usp FS Hc' HAE 0.
  right. split; [|reflexivity]. intros Et. apply Hc.
  assert (Hnm : nmA = nmB) by (rewrite Et in EiA; rewrite EiA in EiB; injection EiB as Enm _; exact Enm).
  rewrite (proj2 Ev0 Hnm). reflexivity. }
intros Hc HS7. rewrite branch_ne_U, U70, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
assert (Hnm : nmA = nmB) by (apply Ev0; apply bv_eq; rewrite Hc; reflexivity).
(* ---- to the kids part SMB_AT 0x278, in the canonical form ---- *)
smb_step_to HS7 HJ SHOK HI Usp FS Hc' (SMB_AT 0x278).
lazymatch type of HS7 with st_ok _ ?Eb ?ssb (restrict _ ?mb) =>
  assert (HL' : st_ok rsegs (smb_EL Ex0 (ms_regs mb) (Z.of_nat i)) (smb_ssL (SMB_AT 0x278)) (restrict (w_H W1) mb));
  [ smb_canon0 Ex0 Eb ssb mb W1 HS7 HE40 HE0 E32 (SMB_AT 0x278)
  | apply (Hkids ltac:(intros _; rewrite EiA, EiB; cbn; f_equal; exact Hnm) Hri Hr0 Hpre Ex0 mb ly1 S1 Hp1 W1 _ _ HL' HI
      HE0 E32) ]
end.
Qed.

Lemma smb_loop : forall rr i, smb_LHp (SMB_AT 0x1bc) rr i.
Proof.
induction rr as [|rr IHr]; intros i.
- intros _ Hr0. lia.
- apply smb_head. intros KE. apply smb_kids; [|exact KE].
  intros Hlt. replace (Datatypes.S rr - 1)%nat with rr by lia. apply IHr.
Qed.

End CT.

(* the container arm, from SMB_AT 0x15c: n = 0 -> 1, else the loop from SMB_AT 0x1bc *)
Lemma smb_cont : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex smb_ssC (restrict (w_H W) ms) ->
  smb_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs smb_Bx smb_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF -> ew Ex 33 = Z_to_bv 64 (tag ta) ->
  ew Ex 35 = Z_to_bv 64 nA -> ew Ex 36 = Z_to_bv 64 nB ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> nA = nB -> (tag ta = 5 \/ tag ta = 6) ->
  SRr rsegs W (mkCfg ms md4) smb_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 A33' A35 A36
  HhA0 HhB0 Etag En Hcont.
smb_pre Ex HAE. pose proof HI as (HJ & _).
pose proof HhA0 as (_ & _ & _ & _ & _ & _ & (RnA & _) & _).
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
(* ---- SMB_AT 0x15c beqz a3 (a3 = n): no items -> 1 ---- *)
smb_branch HS4.
{ intros Hc HS4. rewrite branch_eq_U, (U_atom _ 35 nA A35 ltac:(lia)), U_lit in Hc by lia.
  apply Z.eqb_eq in Hc.
  smb_fin HS4 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply smb_empty_eq; [exact Etag | exact Hcont | lia | lia]. }
intros Hc HS4. rewrite branch_eq_U, (U_atom _ 35 nA A35 ltac:(lia)), U_lit in Hc by lia.
apply Z.eqb_neq in Hc. rename Hc into Hn0.
(* ---- SMB_AT 0x160-0x1b8: the loop's set-up, to the loop head SMB_AT 0x1bc ---- *)
smb_step_to HS4 HJ SHOK HI Usp FS Hc' (SMB_AT 0x1bc).
(* the first arrival at the loop head, in the canonical form: i = 0 *)
lazymatch type of HS4 with st_ok _ ?E4 ?ss4 (restrict _ ?msL) =>
  assert (HL0 : st_ok rsegs (smb_EL Ex (ms_regs msL) 0) (smb_ssL (SMB_AT 0x1bc)) (restrict (w_H W) msL));
  [ apply (smb_canonL Ex E4 ss4 msL (w_H W) (SMB_AT 0x1bc) 0 HS4); [vm_compute; reflexivity | vm_compute; reflexivity
      | env_agree_chain (env_agree_refl 40 Ex) | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 19%bv HS4); smb_regv (SLit 0); reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 26%bv HS4); smb_regv (SLit 0); reflexivity
      | rewrite (st_ok_restrict_reg rsegs (w_H W) E4 ss4 msL 27%bv HS4); smb_regv (SLit 0); reflexivity
      | exact HAE | exact E32 | lia | lia ]
  | eapply (smb_loop numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HhA0 HhB0 Etag En Hcont (Z.to_nat nA) 0
      ltac:(lia) ltac:(lia) ltac:(intros j Hj; lia) Ex msL ly S Hp W);
    [ exact HL0 | exact HI | exact HAE | exact E32 ] ]
end.
Qed.

(* the dispatch on the tag from SMB_AT 0xcc: the scalar arm (tag <= 2 -> 1) here, the number arm smb_num, the string
   arm smb_str, the container arm smb_cont *)
Lemma smb_disp : forall (Ex : env) (ms : machine_state) md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB,
  st_ok rsegs Ex smb_ssD (restrict (w_H W) ms) ->
  smb_INV ly S Hp W (ms_mem ms) md4 k4 ->
  sh_ok rsegs smb_Bx smb_SH Ex (mrestrict (w_H W) (ms_mem ms)) ->
  bv_unsigned (ew Ex 2) = spZ regs ->
  env_agree 32 (Ereg regs [w64 SHADOW_OFF]) Ex ->
  ew Ex 32 = w64 SHADOW_OFF -> ew Ex 33 = Z_to_bv 64 (tag ta) ->
  ew Ex 35 = Z_to_bv 64 nA -> ew Ex 36 = Z_to_bv 64 nB ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pa (tag ta) numA strA kidsA keysA nA capA ->
  pj_hdrR rsegs (mrestrict (w_H W) mem) pb (tag tb) numB strB kidsB keysB nB capB ->
  tag ta = tag tb -> nA = nB ->
  SRr rsegs W (mkCfg ms md4) smb_POST.
Proof.
intros Ex ms md4 k4 numA strA kidsA keysA nA capA numB strB kidsB keysB nB capB HS4 HI SHOK Usp HAE E32 A33' A35 A36
  HhA0 HhB0 Etag En.
smb_pre Ex HAE. pose proof HI as (HJ & _).
assert (Ht7 : tag ta = 0 \/ tag ta = 1 \/ tag ta = 2 \/ tag ta = 3 \/ tag ta = 4 \/ tag ta = 5 \/ tag ta = 6) by lia.
assert (Ut5 : U Ex (SOff 33 (-5)) = (tag ta - 5) mod 2 ^ 64).
{ unfold U. rewrite denot_SOff, A33', unsigned_lit_small by lia. unfold zcanon, M64, bv_wrap. reflexivity. }
(* ---- SMB_AT 0xcc bgeu s1, a0 (s1 = 1, a0 = tag - 5): an array or an object ---- *)
smb_branch HS4.
{ intros Hc HS4. rewrite branch_geu_U, U_lit, Ut5 in Hc by lia.
  assert (Hcont : tag ta = 5 \/ tag ta = 6)
    by (destruct Ht7 as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]; rewrite Ht in Hc |- *; vm_compute in Hc; first [discriminate Hc | lia]).
  clear Hc.
  smb_step HS4 HJ SHOK HI Usp FS Hc'.
  lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
    assert (HS4' : st_ok sg Ey smb_ssC m) by (replace smb_ssC with ss by (vm_compute; reflexivity); exact HS4) end.
  exact (smb_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
    ltac:(try (rewrite !ew_havoc_old by lia); exact E32) A33' A35 A36 HhA0 HhB0 Etag En Hcont). }
intros Hc HS4. rewrite branch_geu_U, U_lit, Ut5 in Hc by lia.
assert (Hle4 : tag ta <= 4)
  by (destruct Ht7 as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]; rewrite Ht in Hc |- *; vm_compute in Hc; first [discriminate Hc | lia]).
clear Hc.
smb_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0xd4 beq a2, a0 (a0 = 4): a string ---- *)
smb_branch HS4.
{ intros Hc HS4. rewrite branch_eq_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
  apply Z.eqb_eq in Hc. rename Hc into Ht4.
  smb_step HS4 HJ SHOK HI Usp FS Hc'.
  lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
    assert (HS4' : st_ok sg Ey smb_ssS m) by (replace smb_ssS with ss by (vm_compute; reflexivity); exact HS4) end.
  exact (smb_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
    ltac:(try (rewrite !ew_havoc_old by lia); exact E32) HhA0 HhB0 Etag Ht4). }
intros Hc HS4. rewrite branch_eq_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
apply Z.eqb_neq in Hc. rename Hc into Hn4.
smb_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0xdc bne a2, a0 (a0 = 3): null, false or true -> 1 ---- *)
smb_branch HS4.
{ intros Hc HS4. rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  smb_fin HS4 HJ SHOK HI Usp FS Hc' HAE 1.
  left. split; [|reflexivity]. apply smb_tag_scalar; [exact Etag | lia]. }
intros Hc HS4. rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33' ltac:(lia)), U_lit in Hc by lia.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Ht3.
(* ---- the number arm ---- *)
smb_step HS4 HJ SHOK HI Usp FS Hc'.
lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
  assert (HS4' : st_ok sg Ey smb_ssN m) by (replace smb_ssN with ss by (vm_compute; reflexivity); exact HS4) end.
exact (smb_num _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain HAE)
  ltac:(try (rewrite !ew_havoc_old by lia); exact E32) HhA0 HhB0 Etag Ht3).
Qed.

(* the entry: both tags, both n fields, then the dispatch *)
Theorem smb_entry : SRr rsegs W (cfg_at rsegs (pa_sigma (PAImg := PI_prog_B) AS_same) regs mem md) smb_POST.
Proof.
pose proof HFPRE as [HPRE [HRO _]].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (smbk_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof smb_stk as FS. unfold ESTACK in FS.
pose proof Hceil as Hc'. rewrite FS in Hc'.
assert (EPC : pa_sigma (PAImg := PI_prog_B) AS_same = SMB_AT 0) by (unfold SMB_AT; vm_compute; reflexivity).
unfold cfg_at. rewrite EPC. change (w64 (SMB_AT 0)) with (Z_to_bv 64 (SMB_AT 0)).
pose proof smb_entry_ok as HS.
pose proof (ajournal_x_init (SK := SK) rsegs B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
set (E := Ereg regs [w64 SHADOW_OFF]) in HS.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs [w64 SHADOW_OFF] 0)).
assert (E10 : ew E 10 = w64 pa) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 pb) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (SHOK : sh_ok rsegs smb_Bx smb_SH E (mrestrict (w_H W) mem)).
{ apply smb_shok; [exact E10 | exact E11 | exact E32 | |]; rewrite <- (aview_rd_of rsegs);
    [exact (proj1 (proj2 (proj2 HTA))) | exact (proj1 (proj2 (proj2 HTB)))]. }
smb_run HS HJ SHOK.
{ smb_awr E2 FS. }
(* ---- the two roots' headers, named at the entry ---- *)
destruct (smb_hdr_of_node _ _ _ _ _ (proj1 HTA)) as (numA & strA & kidsA & keysA & nA & capA & HhA0).
destruct (smb_hdr_of_node _ _ _ _ _ (proj1 HTB)) as (numB & strB & kidsB & keysB & nB & capB & HhB0).
destruct (smb_root _ _ _ HTA) as (Pa1 & Pa2 & Pa3 & Pa4). destruct (smb_root _ _ _ HTB) as (Pb1 & Pb2 & Pb3 & Pb4).
assert (B0 : bv_signed (0%bv : bv 12) = 0) by reflexivity.
(* ---- the invariant after the first run: the run wrote only the frame, above YM05.alloc_ceiling ---- *)
assert (HI : smb_INV ly S Hp W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) 0).
{ split; [exact HJ|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - apply (smbk_ledger_keep (PA := PI_prog_B) B ARx LAWS ly S Hp W mem md (ms_mem ms) Lam peak cnt fail ran most own
      HAR HLED).
    intros a Ha. refine (smbk_frame_below rsegs E _ (w_H W) mem (ms_mem ms) HFr _ a Ha).
    intros x (r & Hin & Hx). vm_compute in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
      try rewrite E2 in Hx; lia|]). destruct Hin.
  - intros Hm. exact (HMNP _ Hm HF). }
clear HF HFr HG HMNP.
(* ---- SMB_AT 0x80 lw a2, 0(s0): the tag of a (hand load, atom 33) ---- *)
smb_hl_lw HS (12%bv : bv 5) (8%bv : bv 5) pa (tag ta).
{ smb_regv (SOff 10 0). rewrite smbk_SOff0, E10. reflexivity. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as (_ & (_ & Hv) & _).
  exact Hv. }
{ pose proof (smb_tag_range ta). lia. }
intros ms1 mat1 HS1 Hm1. clear HS.
pose proof E2 as Usp.
smb_bk HS1 HJ SHOK Usp HI ms1 mat1 Hm1.
smb_step HS1 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0x88 lw a0, 0(s6): the tag of b (hand load, atom 34) ---- *)
smb_hl_lw HS1 (10%bv : bv 5) (22%bv : bv 5) pb (tag tb).
{ smb_regv (SOff 11 0). rewrite smbk_SOff0, ew_havoc_old by lia. rewrite E11. reflexivity. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as (_ & (_ & Hv) & _).
  exact Hv. }
{ pose proof (smb_tag_range tb). lia. }
intros ms2 mat2 HS2 Hm2. clear HS1.
smb_bk HS2 HJ SHOK Usp HI ms2 mat2 Hm2.
smb_step HS2 HJ SHOK HI Usp FS Hc'.
lazymatch type of HS2 with st_ok _ ?E2' _ _ =>
  assert (A33 : ew E2' 33 = Z_to_bv 64 (tag ta)) by (rewrite ew_havoc_old by lia; apply smb_ew_new1);
  assert (A34 : ew E2' 34 = Z_to_bv 64 (tag tb)) by apply smb_ew_new1
end.
pose proof (smb_tag_range ta) as TRa. pose proof (smb_tag_range tb) as TRb.
(* ---- SMB_AT 0x8c bne a2, a0: the tags differ -> 0 ---- *)
smb_branch HS2.
{ intros Hc HS2.
  rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33 ltac:(lia)), (U_atom _ 34 (tag tb) A34 ltac:(lia)) in Hc.
  smb_fin HS2 HJ SHOK HI Usp FS Hc' (env_agree_refl 32 E) 0.
  right. split; [|reflexivity]. intros ->. rewrite Z.eqb_refl in Hc. discriminate Hc. }
intros Hc HS2.
rewrite branch_ne_U, (U_atom _ 33 (tag ta) A33 ltac:(lia)), (U_atom _ 34 (tag tb) A34 ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Etag.
smb_step HS2 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0xb8 ld a3, 0(s2): a's n (hand load, atom 35) ---- *)
pose proof (smb_hdr_now pa ta Da _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTA HhA0 HI) as HhA1.
smb_hl_ld HS2 (13%bv : bv 5) (18%bv : bv 5) (0%bv : bv 12) (pa + 40) nA.
{ smb_regv (SOff 10 40). apply smb_denot_off; [rewrite !ew_havoc_old by lia; exact E10 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhA1 as (_ & _ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhA1 as (_ & _ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh3 math3 HS3 Hm3. clear HS2.
smb_bk HS3 HJ SHOK Usp HI mh3 math3 Hm3.
smb_step HS3 HJ SHOK HI Usp FS Hc'.
(* ---- SMB_AT 0xbc ld a0, 0(a0): b's n (hand load, atom 36) ---- *)
pose proof (smb_hdr_now pb tb Db _ _ _ _ _ _ _ _ _ _ _ _ _ _ HTB HhB0 HI) as HhB1.
smb_hl_ld HS3 (10%bv : bv 5) (10%bv : bv 5) (0%bv : bv 12) (pb + 40) nB.
{ smb_regv (SOff 11 40). apply smb_denot_off; [rewrite !ew_havoc_old by lia; exact E11 | lia | lia]. }
{ lia. } { rewrite B0; lia. } { rewrite B0; lia. }
{ rewrite B0, Z.add_0_r. destruct HhB1 as (_ & _ & _ & _ & _ & _ & (_ & Hv) & _). exact Hv. }
{ destruct HhB1 as (_ & _ & _ & _ & _ & _ & (Hv & _) & _). exact Hv. }
intros mh4 math4 HS4 Hm4. clear HS3.
smb_bk HS4 HJ SHOK Usp HI mh4 math4 Hm4.
smb_step HS4 HJ SHOK HI Usp FS Hc'.
(* the n fields are the trees' item counts (read at the entry memory) *)
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTA) HhA0) as LnA.
pose proof (smb_node_n _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HTB) HhB0) as LnB.
pose proof HhA0 as (_ & _ & _ & _ & _ & _ & (RnA & _) & _). pose proof HhB0 as (_ & _ & _ & _ & _ & _ & (RnB & _) & _).
lazymatch type of HS4 with st_ok _ ?E4 _ _ =>
  assert (A35 : ew E4 35 = Z_to_bv 64 nA) by (rewrite ew_havoc_old by lia; apply smb_ew_new1);
  assert (A36 : ew E4 36 = Z_to_bv 64 nB) by apply smb_ew_new1;
  assert (A33' : ew E4 33 = Z_to_bv 64 (tag ta)) by (rewrite !ew_havoc_old by lia; apply smb_ew_new1)
end.
(* ---- SMB_AT 0xc0 bne a3, a0: the n fields differ -> 0 ---- *)
smb_branch HS4.
{ intros Hc HS4.
  rewrite branch_ne_U, (U_atom _ 35 nA A35 ltac:(lia)), (U_atom _ 36 nB A36 ltac:(lia)) in Hc.
  smb_fin HS4 HJ SHOK HI Usp FS Hc' (env_agree_refl 32 E) 0.
  right. split; [|reflexivity]. intros Et. subst tb. rewrite LnA, LnB, Z.eqb_refl in Hc. discriminate Hc. }
intros Hc HS4.
rewrite branch_ne_U, (U_atom _ 35 nA A35 ltac:(lia)), (U_atom _ 36 nB A36 ltac:(lia)) in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into En.
smb_step HS4 HJ SHOK HI Usp FS Hc'.
(* ---- from here on: the dispatch on the tag (smb_disp), at the state smb_ssD ---- *)
lazymatch type of HS4 with st_ok ?sg ?Ey ?ss ?m =>
  assert (HS4' : st_ok sg Ey smb_ssD m) by (replace smb_ssD with ss by (vm_compute; reflexivity); exact HS4) end.
exact (smb_disp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS4' HI SHOK Usp ltac:(env_agree_chain (env_agree_refl 32 E))
  ltac:(rewrite !ew_havoc_old by lia; exact E32) A33' A35 A36 HhA0 HhB0 Etag En).
Qed.

End E.

(* The batch kit's tsame_specX at every nesting: smb_entry at nesting n, its recursive calls through nestings below n *)
Theorem same_holds_B : forall n, tsame_specX (PA := PI_prog_B) B ARx SK n.
Proof.
intros n. induction n as [n IHn] using (well_founded_ind lt_wf).
unfold tsame_specX.
intros ly S Hp W regs mem md ch pa pb ta tb Da Db Lam peak cnt fail ran most own HF HUP H10 H11 HTA HTB HD HFA HFB HL.
eapply smb_entry; eassumption.
Qed.
End W.
