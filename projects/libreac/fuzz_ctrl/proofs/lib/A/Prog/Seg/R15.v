(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 783 of its 813 lines of code are new or changed and 366 lines of the source are left out. *)
(* Segment R15 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): Inv_A817c8 -> Inv_A81924.
   At 0x817c8 the result register a0 of reac_ctrl_identity_fragment is 0, so the branch `beqz a0,8191c` is taken
   (0x817cc, the j to before_abort, is NOT reached); at 0x8191c `mv a0,s8` loads s8 = Phi_r into a0 and `jal
   wrapper_free` (0x53378 = as_free ASYMS) releases the harness buffer (phi, rnb g b).  The free-call continuation
   r_free_cont runs `mv a0,s8 ; jal wrapper_free` to the free entry, applies the frame's free contract (AC.aa_free,
   AC.AK_FREE) whose a_call_post drops the block (phi, rnb g b) from the heap list and keeps every frame byte
   (a_laws_not_owned for the frame / its shadow / the saved registers / the spill / the window; a_laws_client for the
   sink cells and the shadow of the frame_AG globals; frame_facts for RELRO; the free window [sp-4096, sp) by
   Tac_slot.sl_frame_apart_win, the rest by position), moves FRA to the empty harness list by Tac_slot.sl_mid,
   keeps OURb and the round-trip bytes of turn (S b) as frame bytes, keeps OUTA (out[]'s 1492 bytes addressable) by
   Tac_slot.outa_call, and re-establishes the official cut Inv_A81924_at (hb = []).
   R16 and R20 reuse r_free_cont for the same call.  Push 5c: the call's a_call_pre is fra_call_pre (FRA + ENT),
   so the old local FREE_PRE and the local entry cut Inv_A817c8f_at are gone; seg_R15 runs on the official cut
   Inv_A817c8_at (push 6c); ENT moves across the call with ent_mat / ent_call. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* ===== Lib-level runs ===== *)

(* 0x817c8 beqz a0,8191c (a0 = 0 so taken; registers and memory unchanged). *)
Lemma r15_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 0 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ->.
  step. if_true. apply evt_done. reflexivity.
Qed.

(* 0x8191c mv a0,s8 ; 0x81920 jal wrapper_free (0x53378); ra := 0x81924, a0 := s8. *)
Lemma rfree_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => exists a0',
         ms' = MS (mkR (Z_to_bv 64 0x81924) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x53378) fc None m (seg_rom rsegs) /\ a0' = s8)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step. step. apply evt_done. eexists. split; reflexivity.
Qed.

(* ===== Lengths of the round-trip model (port of U Tac_u2m u2_fg_st_len / u2_RS_len) ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.

Lemma r15_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

Lemma r15_RS_len : forall inp b, length (RID inp b) = 38%nat /\ length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RID, RFG. induction b as [|b [IH1 IH2]]; [split; reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact (conj IH1 IH2)|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - split; [|exact IH2]. unfold rp_id. destruct (RcReply.ir _ _); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact (conj IH1 IH2)].
    split.
    + unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH1 | exact IH1].
    + apply r15_fg_st_len; [exact IH2 | apply fr50_length].
Qed.

(* ===== The free-call continuation and seg_R15 ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require BzBridge KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt2_b2 Tac_rt_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_cls.
From Stdlib Require Import Permutation.
(* Qualified: `Require BzBridge KindBGlue` above loads the image-independent lib/Reusable/YK11, after which the
   short name YK11 is that one, and its getr / mkst / FPState are NOT the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section R15W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r15_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC.a_in_img a /\ ~ AC.a_on_img_page a /\
    ~ AC.a_in_fs AC.ASYMS mem a.
Proof. exact (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r15_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + AC.FS_SIZE -> app_mem a.
Proof. exact (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r15_law_mat_le : forall H mem md md', AsanLift.mat_le md md' ->
  (law_AH H mem md -> law_AH H mem md') /\ (forall a, law_own H mem md' a <-> law_own H mem md a) /\
  law_lo mem md' = law_lo mem md /\ law_hi mem md' = law_hi mem md.
Proof. exact (AC.a_laws_mat_le _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r15_law_not_owned : forall H mem md a, law_AH H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/ law_lo mem md <= a < APPMEM_END) ->
  ~ law_own H mem md a /\ ~ law_own H mem md (shadow_addr a).
Proof. exact (AC.a_laws_not_owned _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r15_law_client : forall H mem md a, law_AH H mem md ->
  (AC.in_blocks AC.a_client a -> ~ law_own H mem md a) /\
  (AC.a_in_img a -> ~ law_own H mem md (shadow_addr a)) /\
  (AC.as_tp AC.ASYMS <= a < AC.as_tp AC.ASYMS + 8 -> law_own H mem md a).
Proof. exact (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* Where a frame byte lies (FRA's location disjunction made uniform). *)
Definition r15_loc (mem : word -> option byte) (md : Model) (a : Z) : Prop :=
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/
  (AC.a_in_fs AC.ASYMS mem a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).

(* bytes_at survives a memory change that keeps each byte of its range. *)
Lemma r15_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs HK (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  change (mbyte rsegs mem' (a + Z.of_nat i) = mbyte rsegs mem (a + Z.of_nat i)).
  apply HK. lia.
Qed.

(* mrd at (wa a) and mbyte at a are the same lookup (bridges Lib.Frame.stk to the contract's mbyte). *)
Lemma r15_mrd_mbyte : forall (m : word -> option byte) a, mrd rsegs m (wa a) = mbyte rsegs m a.
Proof. intros m a. reflexivity. Qed.

(* addressable survives a memory change that keeps the shadow byte of each byte of the range. *)
Lemma r15_addr_keep : forall (m m' : word -> option byte) a n,
  addressable m a n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (a + i)) = mbyte rsegs m (shadow_addr (a + i))) ->
  addressable m' a n.
Proof.
  intros m m' a n (H1 & H2 & H3 & H) K. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Hap & bb & Hrd & Hok). split; [exact Hap|].
  exists bb. split; [|exact Hok].
  change (mbyte rsegs m' (shadow_addr (a + i)) = Some bb). rewrite (K i Hi). exact Hrd.
Qed.

(* One CB cell's rw_cells survives a memory change that keeps each byte of its range and its writability. *)
Lemma r15_rwcb_keep : forall (mem mem' : word -> option byte) a n bs,
  (forall x, a <= x < a + Z.of_nat n ->
     mbyte rsegs mem' x = mbyte rsegs mem x /\ (writable_at rsegs mem x -> writable_at rsegs mem' x)) ->
  rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs].
Proof.
  intros mem mem' a n bs HK ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (r15_bkeep mem mem'); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (proj1 (HK x Hx)).
  - destruct Hw as (Hw0 & Hw1 & Hw). cbn [cells_size csize] in Hw0, Hw1, Hw |- *.
    split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (proj2 (HK (a + i) ltac:(lia)) (Hw i Hi)).
Qed.

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability.
   R16 / R20 use it too. *)
Lemma r15_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap.  R16 uses it
   too. *)
Lemma r15_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

(* An address range covered by one image segment is in the image (checked by computation). *)
Lemma r15_img_cover : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true ->
  forall a, lo <= a < hi -> AC.a_in_img a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

(* The registered globals of frame_AG lie in the image's segments and in [0x21140, 0x9f8e8) (checked by
   computation; the same check as a Theorem Labs lane's R7.v r7_ag_img / r7_ag_range). *)
Lemma r15_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => existsb (fun s => (Z.of_N (seg_base s) <=? fst p) &&
                   (fst p + snd p <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin). apply existsb_exists in Hall as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists s. split; [exact Hs | lia].
Qed.

Lemma r15_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* A spill's own base is the FRA base: both are read off register 9, and the spilled word's 8 bytes bound the
   base's representative, so the two agree as integers, not only mod 2 ^ 64. *)
Lemma r15_spill_A : forall (regs : bvmap 5 word) (m : word -> option byte) (off w A0 Af : Z),
  rg regs 9 Af -> HIGHMEM_BEG <= Af -> Af + 312 <= 2 ^ 64 -> 0 <= off <= 304 ->
  rg regs 9 A0 -> q64 m (A0 + off) w -> A0 = Af.
Proof.
  intros regs m off w A0 Af HAf Hlo Hhi Hoff HA0 HQ.
  unfold rg in HAf, HA0. rewrite HAf in HA0.
  apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap in HA0.
  rewrite (Z.mod_small Af (2 ^ 64)) in HA0 by (unfold HIGHMEM_BEG in Hlo; lia).
  unfold q64 in HQ. apply bytes_at_bound in HQ. rewrite length_le8 in HQ.
  unfold HIGHMEM_BEG in Hlo. revert HA0 HQ. Z.div_mod_to_equations. lia.
Qed.

(* r_free_cont: from the state at 0x8191c with s8 = phi, FRA and ENT with hb1 phi (rnb g b), RB at (S b), to
   Inv_A81924_at.  R15 / R16 / R20 reach 0x8191c and call this.  The free call's a_call_pre is fra_call_pre.
   OUTA crosses the call by outa_call: the free touches only the heap block.  The spill premises, PRO and the last
   three are the facts R21 reads at 0x81924 (official push 13B body): the spills at [A + 128], [A + 104],
   [A + 96], [A + 64], [A + 112], [A + 144] = fr + 2688, [A + 192] = fr + 2768, [A + 280] = fr + 3040,
   [A + 240] = fr + 3056 and [A + 152] = S(fr) + 68, PRO (the prologue spills, our[]'s 6 addressable bytes and the
   input block), s5 = fr + 2176, the frame cells at fr + 2688 (38 bytes), fr + 2768 (72), fr + 3040 (1) and
   fr + 3056 (32) readable and writable, the 38 addressable bytes of the id record and RXS.  The free call keeps
   them: registers 9 and 21 are callee-saved, the spill bytes lie at or above sp (sp <= A) and so outside the free
   window [sp - 4096, sp), the cells, the id record and our[] are inside the frame, whose bytes, writability and
   shadow bytes are kept, and the input block is a block of the entry heap, live before and after the free and
   apart from the freed block (a_laws_disjoint), so neither its bytes nor its shadow bytes are the allocator's. *)
Lemma r_free_cont : forall b,
  Hat B APIf ra (Inv_A81924_at (fx := fx) B APIf ra) b ->
  forall g regs mem md fr phi,
    FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
    ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md ->
    g_n g < 2 ^ 26 ->
    RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs mem ->
    rg regs 24 phi ->
    OUTA fr mem ->
    spill regs mem 128 (fr + 544) ->
    PRO g fr regs mem ->
    spill regs mem 104 0x21140 ->
    spill regs mem 96 0x1234 ->
    spill regs mem 64 0xe38f0000 ->
    rg regs 21 (fr + 2176) ->
    spill regs mem 112 (mrow (g_in g)) ->
    spill regs mem 144 (fr + 2688) ->
    spill regs mem 192 (fr + 2768) ->
    (exists idb, rw_cells rsegs mem (fr + 2688) [CB 38 idb]) ->
    (exists junk, rw_cells rsegs mem (fr + 2768) [CB 72 junk]) ->
    spill regs mem 280 (fr + 3040) ->
    spill regs mem 240 (fr + 3056) ->
    (exists jy, rw_cells rsegs mem (fr + 3040) [CB 1 jy]) ->
    (exists junk, rw_cells rsegs mem (fr + 3056) [CB 32 junk]) ->
    spill regs mem 152 (Sfr fr + 68) ->
    addressable mem (fr + 2176) 38 ->
    RXS g fr regs mem ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x8191c) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g regs mem md fr phi HFRA HENT Hgn HRB Hr24 HOUTA
    Hs128 HPRO Hs104 Hs96 Hs64 Hr21 Hs112 Hs144 Hs208 HRWid HRWjk Hs280 Hs240 HRWjy HRWsc Hs152 HAid
    HRXS.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRELRO_img & Hown & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  (* the frame is apart from the free window [sp - 4096, sp) *)
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as Hapart.
  destruct (r15_RS_len (g_in g) (S b)) as (LID & LFG).
  pose proof HRB as (Hb6 & Hcur & Hour & Hr23 & Hidb & Hfgb).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAmod & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (Eerr : AC.a_errno AC.ASYMS = 0x5db76c) by reflexivity.
  assert (Eoom : AC.as_oom AC.ASYMS = 0x12aae0) by reflexivity.
  assert (HKF : AC.AK_FREE = 4096) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (Hspapp : sp < APPMEM_END) by lia.
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH).
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (HAfb : 0 <= Af + 304 /\ Af + 312 <= 2 ^ 64).
  { pose proof Hspill as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (HAfr : 0 <= Af < 2 ^ 64) by lia.
  rewrite Haspz in Hapart.
  (* the freed block (phi, rnb g b) is a live block; its end is <= stklo and its bytes are not in FS *)
  assert (Hblkle : phi + rnb g b <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
                   (forall a, phi <= a < phi + rnb g b -> ~ AC.a_in_fs AC.ASYMS mem a)).
  { destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
      (or_introl eq_refl)) as (_ & _ & Hle & _ & Hbyte).
    split; [exact Hle|]. intros a Ha. exact (proj2 (proj2 (proj2 (proj2 (Hbyte a Ha))))). }
  destruct Hblkle as (Hblkle & Hblkfs).
  (* a side-stack byte lies above the image and below stklo *)
  assert (FSC : forall a, 0 <= a < 2 ^ 64 -> AC.a_in_fs AC.ASYMS mem a ->
             AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ app_mem a).
  { intros a Ha (bb & Hbb & Hwm & Hb1 & Hb2).
    destruct (r15_law_fs_place _ mem md bb HAH Hwm Hbb) as (Hg & Hfsk & _ & Hfsa).
    split; [lia|]. apply Hfsa. lia. }
  (* every frame byte is located and application memory *)
  assert (FRAME : forall a, fr <= a < fr + FRAME_BYTES -> r15_loc mem md a /\ app_mem a).
  { intros a Ha. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha) as Hr. split; [left; exact Hr|]. unfold app_mem. right. lia.
    - destruct (FSC fr ltac:(lia) (Hfs fr ltac:(lia))) as (Hfr1 & _).
      destruct (FSC a ltac:(lia) (Hfs a Ha)) as (Ha1 & Ha2).
      split; [right; split; [exact (Hfs a Ha) | exact Ha1] | exact Ha2]. }
  (* a located byte is disjoint from the freed block *)
  assert (BLKDJ : forall a, r15_loc mem md a -> ~ (phi <= a < phi + rnb g b)).
  { intros a Hl [Ha1 Ha2]. destruct Hl as [Hs | [Hfs _]].
    - lia.
    - exact (Hblkfs a (conj Ha1 Ha2) Hfs). }
  (* an image byte is disjoint from the freed block (block bytes are not in the image) *)
  assert (NBLK : forall a, AC.a_in_img a -> ~ (phi <= a < phi + rnb g b)).
  { intros a Himg Hb. destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
      (or_introl eq_refl)) as (_ & _ & _ & _ & Hbyte).
    destruct (Hbyte a Hb) as (_ & _ & Hni & _). exact (Hni Himg). }
  (* a shadow byte is disjoint from the freed block (block bytes are application memory) *)
  assert (NBLKsh : forall a, in_shadow a -> ~ (phi <= a < phi + rnb g b)).
  { intros a Hshd Hb. destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
      (or_introl eq_refl)) as (_ & _ & _ & _ & Hbyte).
    destruct (Hbyte a Hb) as (Happ & _). exact (app_not_shadow a Happ Hshd). }
  rewrite SEGS.
  (* run mv a0,s8 ; jal wrapper_free to the free entry 0x53378 *)
  apply (sl_run_lib regs (Z_to_bv 64 0x8191c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x53378 /\ mem' = mem /\ getr R 1 = Z_to_bv 64 0x81924 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 10 = getr regs 24)
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply rfree_evt.
    - intros ms' (a0' & -> & Ha0'). do 3 eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]).
      rewrite Ha0'. reflexivity. }
  intros R pc' mem' regs_free md1
    (Hpc & Hmem & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K10)
    Hreg Hmat.
  subst pc' mem'.
  assert (E1 : getr regs_free 1 = Z_to_bv 64 0x81924) by (rewrite Hreg; exact K1).
  assert (E2 : getr regs_free 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs_free 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs_free 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs_free 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs_free 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs_free 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs_free 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs_free 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs_free 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs_free 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs_free 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs_free 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E10 : getr regs_free 10 = Z_to_bv 64 phi).
  { unfold rg in Hr24. rewrite <- Hr24, Hreg. exact K10. }
  assert (Hasp'' : AC.aspZ regs_free = sp).
  { unfold AC.aspZ. rewrite E2. exact Haspz. }
  (* FRA at the free entry (regs_free, mem, md1) *)
  assert (HFRA1 : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs_free mem md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs_free mem md md1 HFRA E2 E3 E4 E8 E9 E19 E26 Hmat).
  (* ENT at the free entry (mem is unchanged by beqz; md moved by mat_le) *)
  assert (HENT1 : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md1).
  { eapply ent_mat; [exact HENT | exact Hmat]. }
  (* a_call_pre at the free entry from fra_call_pre *)
  assert (Hpre1 : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
      (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_FREE
      (hb1 phi (rnb g b) ++ g_H g) regs_free mem md1).
  { eapply fra_call_pre.
    - exact HFRA1.
    - exact HENT1.
    - rewrite E1. apply YK0s.ret_ok_even. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. reflexivity.
    - unfold FN_STACK, AF.SLOT_STACK, AC.AK_FREE; lia. }
  destruct (r15_law_mat_le (hb1 phi (rnb g b) ++ g_H g) mem md md1 Hmat)
    as (HAHm & _ & Hstkeq1 & _).
  pose proof (HAHm HAH) as HAH1.
  (* the free contract's per-class premises (generation N.1 afree_at): Bc = Tac_cls.Bc_of BE for ENT's own witness
     BE (Tac_cls.sl_free_cls); the call heap hb1 phi (rnb g b) ++ g_H g is (phi, rnb g b) :: g_H g, afree_at's
     H1 ++ (p, n) :: H2 with H1 = [] and H2 = g_H g *)
  destruct (Tac_cls.sl_free_cls APIf g (hb1 phi (rnb g b)) mem md1 phi (rnb g b) HENT1)
    as (BE & _ & _ & Hcls & Hroom).
  (* apply the free contract *)
  eapply SR_bind.
  { apply (AC.aa_free AC.ASYMS AsanRTInv.RT API [] (g_H g) regs_free mem md1 phi (rnb g b) (Tac_cls.Bc_of BE)
             Hpre1 E10 Hcls Hroom). }
  intros c' (regs' & mem' & md'' & Ec' & Hcp & Herrk).
  subst c'. rewrite E1.
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  pose proof (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hfk.
  pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinw.
  pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinp.
  pose proof Hcp as Hmod; apply AC.a_call_post_model in Hmod.
  assert (Htp16 : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  rewrite Eerr, Eoom in Hfk.
  assert (F2 : getr regs' 2 = getr regs_free 2) by exact (Hkept 2 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F3 : getr regs' 3 = getr regs_free 3) by exact (Hkept 3 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F4 : getr regs' 4 = getr regs_free 4) by exact (Hkept 4 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F8 : getr regs' 8 = getr regs_free 8) by exact (Hkept 8 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F9 : getr regs' 9 = getr regs_free 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F19 : getr regs' 19 = getr regs_free 19) by exact (Hkept 19 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F21 : getr regs' 21 = getr regs_free 21) by exact (Hkept 21 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F22 : getr regs' 22 = getr regs_free 22) by exact (Hkept 22 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F23 : getr regs' 23 = getr regs_free 23) by exact (Hkept 23 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F24 : getr regs' 24 = getr regs_free 24) by exact (Hkept 24 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F25 : getr regs' 25 = getr regs_free 25) by exact (Hkept 25 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F26 : getr regs' 26 = getr regs_free 26) by exact (Hkept 26 ltac:(unfold AC.a_callee_saved; lia)).
  assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem a -> AC.a_in_fs AC.ASYMS mem' a).
  { intros a (bb & Hbb & Hwm & Hb). exists bb. split; [exact Hbb|]. split; [|exact Hb].
    intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
  (* a byte not owned (before/after), off the free window, errno, the flag and the freed block, is kept *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb1 phi (rnb g b) ++ g_H g) mem md1 a ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem' md'' a ->
      ~ (sp - 4096 <= a < sp) -> ~ (0x5db76c <= a < 0x5db76c + 4) -> a <> 0x12aae0 ->
      ~ (phi <= a < phi + rnb g b) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho1 Ho2 Hw He Hoo Hnt. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo | exact Hnt].
    unfold AC.a_window. rewrite HKF, Hasp''. exact Hw. }
  (* a located byte and its shadow are not the allocator's, before or after *)
  assert (LOC : forall a, r15_loc mem md a ->
      0 <= a < 2 ^ 64 /\ AC.GT <= a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb1 phi (rnb g b) ++ g_H g) mem md1 a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb1 phi (rnb g b) ++ g_H g) mem md1 (shadow_addr a) /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem' md'' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem' md'' (shadow_addr a)).
  { intros a Hl.
    assert (Hpl : AC.in_blocks (hb1 phi (rnb g b) ++ g_H g) a \/ AC.in_slack (hb1 phi (rnb g b) ++ g_H g) a \/
                  AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md1 <= a < APPMEM_END).
    { rewrite Hstkeq1. destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]. }
    assert (Hql : AC.in_blocks (g_H g) a \/ AC.in_slack (g_H g) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md'' <= a < APPMEM_END).
    { rewrite Hsk', Hstkeq1. destruct Hl as [Hs|[Hfs _]];
        [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
    destruct (r15_law_not_owned _ mem md1 a HAH1 Hpl) as (N1 & N2).
    destruct (r15_law_not_owned _ mem' md'' a HAH' Hql) as (N3 & N4).
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3 | exact N4]. }
  assert (KLOC : forall a, r15_loc mem md a -> ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hl Hw. destruct (LOC a Hl) as (Hr & Hg & N1 & _ & N3 & _).
    apply KEEP; [exact Hr | exact N1 | exact N3 | exact Hw | lia | lia | exact (BLKDJ a Hl)]. }
  assert (KST : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END -> ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hs Hw. apply KLOC; [left; exact Hs | exact Hw]. }
  assert (KSH : forall a, r15_loc mem md a -> app_mem a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hl Hap. destruct (LOC a Hl) as (_ & _ & _ & N2 & _ & N4).
    pose proof (shadow_of_app a Hap) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
    pose proof (NBLKsh (shadow_addr a) Hsh1) as Hnb.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
    refine (proj1 (KEEP _ _ N2 N4 _ _ _ Hnb)); lia. }
  (* PRO's input block (push 13B): a block of the entry heap, live before and after the free (a_laws_not_owned
     keeps it and its shadow bytes off the allocator's bytes), below stklo, off the image and apart from the freed
     block (a_laws_disjoint); so the free keeps its bytes and its shadow bytes *)
  assert (KIN : forall a, In (g_p g, g_n g) (g_H g) -> g_p g <= a < g_p g + g_n g ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hin Ha.
    assert (Hin' : In (g_p g, g_n g) (hb1 phi (rnb g b) ++ g_H g)) by (apply in_or_app; right; exact Hin).
    destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md1 (g_p g) (g_n g) HAH1 Hin')
      as (_ & Hp4k & Hle & _ & Hbyte).
    destruct (Hbyte a Ha) as (Happ & _ & Himg_a & _ & _).
    rewrite Hstkeq1 in Hle.
    assert (Hnf : ~ (phi <= a < phi + rnb g b)).
    { intros Hphib. destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md1 phi (rnb g b) (g_p g) (g_n g)
                             HAH1 Hin) as [Hd|Hd]; lia. }
    assert (Hpl : AC.in_blocks (hb1 phi (rnb g b) ++ g_H g) a \/ AC.in_slack (hb1 phi (rnb g b) ++ g_H g) a \/
                  AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md1 <= a < APPMEM_END)
      by (left; exists (g_p g), (g_n g); split; [exact Hin' | exact Ha]).
    assert (Hql : AC.in_blocks (g_H g) a \/ AC.in_slack (g_H g) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md'' <= a < APPMEM_END)
      by (left; exists (g_p g), (g_n g); split; [exact Hin | exact Ha]).
    destruct (r15_law_not_owned _ mem md1 a HAH1 Hpl) as (N1 & N2).
    destruct (r15_law_not_owned _ mem' md'' a HAH' Hql) as (N3 & N4).
    assert (Happ' : 0 <= a < APPMEM_END)
      by (clear - Happ; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; lia).
    split.
    - refine (proj1 (KEEP a _ N1 N3 _ _ _ Hnf)); [lia | lia | |].
      + intros He. apply Himg_a. apply errno_in_img. rewrite Eerr. exact He.
      + intros He. apply Himg_a. rewrite He, <- Eoom. exact oom_in_img.
    - pose proof (shadow_of_app a Happ) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
      pose proof (NBLKsh (shadow_addr a) Hsh1) as Hnb.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
      refine (proj1 (KEEP _ _ N2 N4 _ _ _ Hnb)); lia. }
  assert (KFR : forall a, fr <= a < fr + FRAME_BYTES -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (KLOC a Hl (Hapart a Ha))). }
  assert (KFRW : forall a, fr <= a < fr + FRAME_BYTES ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a -> writable_at rsegs mem' a)).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & _). destruct (KLOC a Hl (Hapart a Ha)) as (Em & Ew).
    split; [exact Em | exact (proj1 Ew)]. }
  assert (KCL : forall a, 0x5db770 <= a < 0x5fd0f0 -> AC.in_blocks AC.a_client a ->
      mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha Hcl.
    assert (Himg : AC.a_in_img a).
    { apply (r15_img_cover 0x5db770 0x5fd0f0); [vm_compute; reflexivity | exact Ha]. }
    refine (proj1 (KEEP a _ _ _ _ _ _ (NBLK a Himg))); [lia | | | lia | lia | lia].
    - exact (proj1 (r15_law_client _ mem md1 a HAH1) Hcl).
    - exact (proj1 (r15_law_client _ mem' md'' a HAH') Hcl). }
  (* the shadow byte of a registered global (an image byte, its shadow in the low shadow) is not the allocator's,
     before or after, and is not in the freed block *)
  assert (KAG : forall a, in_globals AF.frame_AG a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hin. pose proof (r15_ag_img a Hin) as Himg. pose proof (r15_ag_range a Hin) as Hr.
    assert (Hsa : 0x7fff8000 + 16936 <= shadow_addr a <= 0x7fff8000 + 81693).
    { unfold shadow_addr, ASAN_K.
      pose proof (Z.div_le_mono 0x21140 a 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_le_mono a 0x9f8e8 8 ltac:(lia) ltac:(lia)) as D2.
      change (0x21140 / 8) with 16936 in D1. change (0x9f8e8 / 8) with 81693 in D2. lia. }
    assert (Hshd : in_shadow (shadow_addr a)) by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END; left; lia).
    refine (proj1 (KEEP _ _ _ _ _ _ _ (NBLKsh _ Hshd))); [lia | | | lia | lia | lia].
    - exact (proj1 (proj2 (r15_law_client _ mem md1 a HAH1)) Himg).
    - exact (proj1 (proj2 (r15_law_client _ mem' md'' a HAH')) Himg). }
  (* the entry-anchored slot window [S - SLOT_STACK, S) stays present and writable: the free window [sp - 4096, sp)
     by a_call_post, every other byte (real stack, above stklo) by KST *)
  assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct Hwin as (Hlo & Hhi & Hw). split; [exact Hlo|]. split; [exact Hhi|].
    intros a Ha. destruct (Z_lt_le_dec a (sp - 4096)) as [Hlt|Hge].
    - destruct (Hw a Ha) as (Hwv & bb & Hmrd).
      destruct (KST a ltac:(lia) ltac:(lia)) as (Hmb & Hwr).
      split.
      + exact (proj1 Hwr Hwv).
      + exists bb. rewrite r15_mrd_mbyte, Hmb, <- r15_mrd_mbyte. exact Hmrd.
    - destruct (Z_lt_le_dec a sp) as [Hlt2|Hge2].
      + split.
        * apply Hwinw. unfold AC.a_window. rewrite HKF, Hasp''. lia.
        * destruct (Hwinp a ltac:(unfold AC.a_window; rewrite HKF, Hasp''; lia)) as (bb & Hmb).
          exists bb. rewrite r15_mrd_mbyte. exact Hmb.
      + destruct (Hw a Ha) as (Hwv & bb & Hmrd).
        destruct (KST a ltac:(lia) ltac:(lia)) as (Hmb & Hwr).
        split.
        * exact (proj1 Hwr Hwv).
        * exists bb. rewrite r15_mrd_mbyte, Hmb, <- r15_mrd_mbyte. exact Hmrd. }
  rewrite <- SEGS. apply Hexit.
  unfold Inv_A81924_at, CUTST.
  exists regs', mem', md'', fr.
  split; [reflexivity|].
  (* the free's touched region is the heap block (phi, rnb g b), which is below stklo (so below S), off the image
     (block bytes are not image bytes) and off the entry blocks (a_laws_disjoint) *)
  assert (HTO : forall a, phi <= a < phi + rnb g b ->
            app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
  { intros a Ha.
    destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md1 phi (rnb g b)
                HAH1 (or_introl eq_refl)) as (_ & _ & Hle & _ & Hbyte).
    destruct (Hbyte a Ha) as (Happ & _ & Himg_a & _ & _).
    rewrite Hstkeq1 in Hle.
    split; [exact Happ|].
    split; [lia|].
    split; [exact Himg_a|].
    intros (p & n & Hinp & Hr).
    destruct (AC.a_laws_disjoint _ _ _ _ _ ALAWS [] (g_H g) mem md1 phi (rnb g b) p n HAH1 Hinp)
      as [Hd|Hd]; lia. }
  (* ENT at (mem', md'') from HENT1 via ent_call *)
  assert (HENT' : ENT (fx := fx) APIf g [] mem' md'').
  { eapply ent_call.
    - exact HENT1.
    - exact HFRA1.
    - exact Hcp.
    - unfold AC.AK_FREE, FN_STACK, AF.SLOT_STACK; lia.
    - exact HTO.
    - exact Herrk. }
  (* OUTA at mem' via outa_call (out[] is frame memory, its shadow bytes are not the allocator's) *)
  assert (HOUT' : OUTA fr mem').
  { exact (outa_call B APIf ra g fr (hb1 phi (rnb g b)) _ regs_free mem md1 regs' mem' md'' _ AC.AK_FREE
             HFRA1 Hcp ltac:(unfold AC.AK_FREE, FN_STACK, AF.SLOT_STACK; lia) HTO HOUTA). }
  split; [|split; [exact HENT'|]].
  { apply (sl_mid B APIf ra g fr (hb1 phi (rnb g b)) [] regs_free mem md1
      regs' mem' md'' (fun a => phi <= a < phi + rnb g b) AC.AK_FREE HFRA1 Hcp).
    - cbn. lia.
    - (* sink_none mem' md'' *)
      destruct Hsn as ((Hthm & Hlkm) & Hhdm & Hfd).
      split; [split|split].
      + eapply YI14.val_mem_frame; [|exact Hthm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. exists 0x5db840, 131728. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + eapply YI14.val_mem_frame; [|exact Hlkm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + intros k Hk. rewrite <- (Hhdm k Hk). rewrite SEGS, Hhead.
        apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
        unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
      + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd.
        change (m_fds (with_vm_backing lz mt (with_vmmaps vm' md1))) with (m_fds md1).
        rewrite (sl_mat_fds md md1 Hmat). exact Hfd.
    - (* G_img_c mem' (RELRO) *)
      intros a Hin. pose proof (Hgimg a Hin) as E. rewrite SEGS in E |- *. rewrite <- E.
      assert (Har : 0x9e348 <= a < 0xa07c8).
      { destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        repeat (destruct Hil as [Ex|Hil]; [injection Ex as <- <-; lia|]); destruct Hil. }
      refine (proj1 (KEEP a _ _ _ _ _ _ _)); [lia | | | lia | lia | lia |].
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
      + (* ~ freed block: RELRO is in the image, block bytes are not *)
        intros Hblk_a.
        destruct (r15_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
          (or_introl eq_refl)) as (_ & _ & _ & _ & Hbyte).
        destruct (Hbyte a Hblk_a) as (_ & _ & Himg & _). exact (Himg (HRELRO_img a Hin)).
    - (* q64 mem' fr header *)
      unfold q64 in *. apply (r15_bkeep mem mem'); [|exact Hhdr1].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - unfold q64 in *. apply (r15_bkeep mem mem'); [|exact Hhdr2].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - (* spill *)
      intros A0 HA0 HA0r.
      assert (EA0 : A0 = Af).
      { rewrite E9 in HA0. unfold rg in Hr9f. rewrite Hr9f in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r15_bkeep mem mem'); [|exact Hspill].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - (* selector *)
      intros A0 HA0 HA0r v Hv.
      assert (EA0 : A0 = Af).
      { rewrite E9 in HA0. unfold rg in Hr9f. rewrite Hr9f in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r15_bkeep mem mem'); [|exact Hv].
        rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - (* fr reload spill at [A + 16] *)
      intros A0 HA0 HA0r.
      assert (EA0 : A0 = Af).
      { rewrite E9 in HA0. unfold rg in Hr9f. rewrite Hr9f in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r15_bkeep mem mem'); [|exact Hfr24].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - (* shadow *)
      destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (r15_bkeep mem mem'); [|exact Hshb]. rewrite Hshl. intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))).
      { unfold shadow_addr at 1. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      destruct (FRAME _ Hin) as (Hl & Hap).
      rewrite Ex. exact (KSH _ Hl Hap).
    - (* saved registers *)
      apply (r15_bkeep mem mem'); [|exact Hsaved]. intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - exact HWIN'.
    - (* the frame_AG globals stay addressable: their shadow bytes are kept (KAG) *)
      intros a Hin. destruct (HAG a Hin) as (Ha0' & Hn0 & Hend & Hb).
      split; [exact Ha0'|]. split; [exact Hn0|]. split; [exact Hend|].
      intros i Hi. destruct (Hb i Hi) as (Hap & bb & Hrd & Hok). split; [exact Hap|].
      exists bb. split; [|exact Hok].
      assert (Hin' : in_globals AF.frame_AG (a + i)) by (replace (a + i) with a by lia; exact Hin).
      change (mbyte rsegs mem' (shadow_addr (a + i)) = Some bb). rewrite (KAG _ Hin'). exact Hrd.
    - (* the slot window outside the frame stays addressable: each such byte's shadow byte is kept (KSH, the
         byte is at or above stklo on the real arm and in the side stack on the other) *)
      intros a Hwin_a Hnf.
      assert (Haddr_a : addressable mem a 1) by exact (HWA a Hwin_a Hnf).
      assert (H01 : 0 <= 0 < 1) by lia.
      assert (Hap : app_mem a).
      { destruct Haddr_a as (_ & _ & _ & Hab). destruct (Hab 0 H01) as (Hx & _).
        rewrite Z.add_0_r in Hx. exact Hx. }
      assert (Hloc_a : r15_loc mem md a) by (left; split; lia).
      apply (r15_addr_keep mem mem' a 1 Haddr_a).
      intros i Hi. assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
      exact (KSH a Hloc_a Hap).
    - (* FSREC: the tp word is kept (a_call_post_tp); the class-6 flag byte and the slot's last word are
         side-stack bytes, below stklo and so off the free window, hence kept (KLOC) *)
      intros (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail).
      destruct (r15_law_fs_place _ mem md FS HAH Htp HFSr) as (_ & HFSlo & _ & _).
      assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
      assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
      assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
      assert (Hj' : 0 <= j < 256) by (rewrite <- HM6; exact Hj).
      assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
      assert (Hfrv : fr = FS + 6328320 + j * 4096)
        by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
      assert (KFS : forall a, FS <= a < FS + AC.FS_SIZE -> mbyte rsegs mem' a = mbyte rsegs mem a).
      { intros a Ha.
        assert (Hfsa : AC.a_in_fs AC.ASYMS mem a)
          by (exists FS; split; [exact HFSr | split; [exact Htp | exact Ha]]).
        destruct (FSC a ltac:(lia) Hfsa) as (Hga & _).
        refine (proj1 (KLOC a (or_intror (conj Hfsa Hga)) _)). lia. }
      exists FS, j.
      split; [intros k Hk; rewrite (Htp16 (Z.of_nat k) ltac:(lia)); exact (Htp k Hk)|].
      split; [exact HFSr|]. split; [exact Hj|]. split; [exact Hfr|].
      split.
      + apply (r15_bkeep mem mem'); [|exact Hflag]. cbn [length]. intros x Hx. apply KFS. lia.
      + apply (r15_bkeep mem mem'); [|exact Htail]. rewrite length_le8. intros x Hx. apply KFS.
        rewrite HB6 in Hx. lia.
    - exact F2.
    - exact F3.
    - exact F4.
    - exact F8.
    - exact F9.
    - exact F19.
    - exact F26. }
  (* the 0x81924 body: g_n, b<=6, reg23=b, OURb, OUTA, RB (S b), and the facts R21 reads at 0x81924 *)
  split; [exact Hgn|].
  split; [exact Hb6|].
  split; [unfold rg in *; rewrite F23, E23; exact Hr23|].
  split.
  { unfold OURb in *. apply (r15_bkeep mem mem'); [|exact Hour]. rewrite OUR_length. intros x Hx. apply KFR. lia. }
  split; [exact HOUT'|].
  (* a spill is kept: register 9 is callee-saved, and the spilled word sits at or above sp (sp <= A), so outside
     the free window [sp - 4096, sp), and at or above the real stack's bottom *)
  assert (HAflo : HIGHMEM_BEG <= Af) by lia.
  assert (KSP : forall off w, 0 <= off <= 304 -> spill regs mem off w -> spill regs' mem' off w).
  { intros off w Hoff (A0 & HA0 & HQ).
    assert (EA : A0 = Af) by exact (r15_spill_A regs mem off w A0 Af Hr9f HAflo (proj2 HAfb) Hoff HA0 HQ).
    subst A0. unfold spill. exists Af. split.
    - unfold rg in *. rewrite F9, E9. exact Hr9f.
    - unfold q64 in *. apply (r15_bkeep mem mem'); [|exact HQ].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))). }
  (* RB g fr b (RID (S b)) (RFG (S b)) regs' mem' *)
  split.
  { unfold RB. split; [exact Hb6|].
    split.
    { destruct Hcur as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite F22, E22; exact Hc22 | rewrite F25, E25; exact Hc25]. }
    split.
    { unfold OURb in *. apply (r15_bkeep mem mem'); [|exact Hour]. rewrite OUR_length. intros x Hx. apply KFR. lia. }
    split; [unfold rg in *; rewrite F23, E23; exact Hr23|].
    split.
    { unfold IDBr in *. apply (r15_bkeep mem mem'); [|exact Hidb]. rewrite LID. intros x Hx. apply KFR. lia. }
    { unfold FGBr in *. apply (r15_bkeep mem mem'); [|exact Hfgb]. rewrite LFG. intros x Hx. apply KFR. lia. } }
  split; [exact (KSP 128 _ ltac:(lia) Hs128)|].
  (* PRO: the spills by KSP, our[]'s 6 bytes and the input block's shadow bytes by KSH / KIN, its bytes by KIN *)
  split.
  { apply (r15_pro_keep g fr regs regs' mem mem' (fun off v Ho H => KSP off v ltac:(lia) H)); [| | | exact HPRO].
    - intros HA6. apply (r15_addr_keep mem mem' (fr + 2624) 6 HA6).
      intros i Hi. destruct (FRAME (fr + 2624 + i) ltac:(lia)) as (Hl & Hap). exact (KSH _ Hl Hap).
    - intros Hin HIN. apply (r15_bkeep mem mem'); [|exact HIN]. intros x Hx. rewrite <- g_n_len in Hx.
      exact (proj1 (KIN x (Hin ltac:(lia)) Hx)).
    - intros Hin HA. apply (r15_addr_keep mem mem' (g_p g) (g_n g) HA).
      intros i Hi. exact (proj2 (KIN (g_p g + i) Hin ltac:(lia))). }
  split; [exact (KSP 104 _ ltac:(lia) Hs104)|].
  split; [exact (KSP 96 _ ltac:(lia) Hs96)|].
  split; [exact (KSP 64 _ ltac:(lia) Hs64)|].
  split; [unfold rg in *; rewrite F21, E21; exact Hr21|].
  split; [exact (KSP 112 _ ltac:(lia) Hs112)|].
  split; [exact (KSP 144 _ ltac:(lia) Hs144)|].
  split; [exact (KSP 192 _ ltac:(lia) Hs208)|].
  split.
  { destruct HRWid as (idb & HRWi). exists idb. apply (r15_rwcb_keep mem mem'); [|exact HRWi].
    intros x Hx. apply KFRW. lia. }
  split.
  { destruct HRWjk as (junk & Hjk). exists junk. apply (r15_rwcb_keep mem mem'); [|exact Hjk].
    intros x Hx. apply KFRW. lia. }
  split; [exact (KSP 280 _ ltac:(lia) Hs280)|].
  split; [exact (KSP 240 _ ltac:(lia) Hs240)|].
  split.
  { destruct HRWjy as (jy & HRWy). exists jy. apply (r15_rwcb_keep mem mem'); [|exact HRWy].
    intros x Hx. apply KFRW. lia. }
  split.
  { destruct HRWsc as (junk & HRWs). exists junk. apply (r15_rwcb_keep mem mem'); [|exact HRWs].
    intros x Hx. apply KFRW. lia. }
  split; [exact (KSP 152 _ ltac:(lia) Hs152)|].
  (* the id record's 38 bytes stay addressable: they are frame bytes, whose shadow bytes the free call keeps *)
  split.
  { apply (r15_addr_keep mem mem' (fr + 2176) 38 HAid).
    intros i Hi. destruct (FRAME (fr + 2176 + i) ltac:(lia)) as (Hl & Hap). exact (KSH _ Hl Hap). }
  (* RXS (push 10): the spills by KSP, the fragment record's 72 bytes are frame bytes whose shadow is kept *)
  apply (r15_rxs_keep g fr regs regs' mem mem' (fun off v Ho H => KSP off v ltac:(lia) H)); [|exact HRXS].
  intros HA72. apply (r15_addr_keep mem mem' (fr + 2256) 72 HA72).
  intros i Hi. destruct (FRAME (fr + 2256 + i) ltac:(lia)) as (Hl & Hap). exact (KSH _ Hl Hap).
Qed.

(* seg_R15: 0x817c8 beqz a0,8191c (a0 = 0 taken), then the free-call continuation; the official cut carries FRA
   and ENT (push 5c, CUTST). *)
Lemma seg_R15 : forall b : nat,
  Hat B APIf ra (Inv_A81924_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A817c8_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    ((Hgn & Hb6 & HHB & Hr23 & Hour & Hout & Hcur) & HRB & Hr24 & Ha0 &
     Hs128 & HPRO & Hs104 & Hs96 & Hs64 & Hr21 & Hs112 & Hs144 & Hs208 & HRWid & HRWjk & Hs280 & Hs240 &
     HRWjy & HRWsc & Hs152 & HAid & HRXS)).
  subst c.
  pose proof (proj1 FF) as SEGS.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x817c8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8191c /\ mem' = mem /\
       getr R 1 = getr regs 1 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  { pose proof HFRA as HF2.
    destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _). exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply r15_evt. exact Ha0.
    - intros ms' ->. do 3 eexists. repeat (split; [reflexivity|]). reflexivity. }
  intros R pc' mem' regs'' md1
    (Hpc & Hmem & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26)
    Hreg Hmat.
  subst pc' mem'.
  assert (E1 : getr regs'' 1 = getr regs 1) by (rewrite Hreg; exact K1).
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  (* FRA at (regs'', mem, md1) *)
  assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem md md1 HFRA E2 E3 E4 E8 E9 E19 E26 Hmat).
  (* ENT at (regs'', mem, md1) via ent_mat *)
  assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md1).
  { eapply ent_mat; [exact HENT | exact Hmat]. }
  (* RB at (regs'', mem) (beqz leaves memory and the RB registers unchanged) *)
  assert (HRB'' : RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs'' mem).
  { destruct HRB as (Rb6 & Rcur & Rour & Rr23 & Ridb & Rfgb).
    split; [exact Rb6|].
    split.
    { destruct Rcur as (Rc0 & Rc22 & Rc25). unfold CUR, rg in *.
      split; [exact Rc0|]. split; [rewrite E22; exact Rc22 | rewrite E25; exact Rc25]. }
    split; [exact Rour|].
    split; [unfold rg in *; rewrite E23; exact Rr23|].
    split; [exact Ridb | exact Rfgb]. }
  assert (Hr24'' : rg regs'' 24 phi) by (unfold rg in *; rewrite E24; exact Hr24).
  (* the carried facts R21 reads at 0x81924: the beqz writes neither memory nor registers 9 and 21 *)
  assert (KSP'' : forall off w, spill regs mem off w -> spill regs'' mem off w).
  { intros off w (A0 & HA0 & HQ). exists A0. split; [unfold rg in *; rewrite E9; exact HA0 | exact HQ]. }
  assert (Hr21'' : rg regs'' 21 (fr + 2176)) by (unfold rg in *; rewrite E21; exact Hr21).
  assert (Hs144'' : spill regs'' mem 144 (fr + 2688)) by exact (KSP'' 144 _ Hs144).
  assert (Hs208'' : spill regs'' mem 192 (fr + 2768)) by exact (KSP'' 192 _ Hs208).
  assert (Hs152'' : spill regs'' mem 152 (Sfr fr + 68)) by exact (KSP'' 152 _ Hs152).
  rewrite <- SEGS.
  exact (r_free_cont b Hexit g regs'' mem md1 fr phi HFRA'' HENT'' Hgn HRB'' Hr24'' Hout
           (KSP'' 128 _ Hs128)
           (r15_pro_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H) (fun _ H => H)
              (fun _ H => H) HPRO)
           (KSP'' 104 _ Hs104) (KSP'' 96 _ Hs96) (KSP'' 64 _ Hs64)
           Hr21'' (KSP'' 112 _ Hs112) Hs144'' Hs208'' HRWid HRWjk (KSP'' 280 _ Hs280) (KSP'' 240 _ Hs240)
           HRWjy HRWsc Hs152'' HAid
           (r15_rxs_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H) HRXS)).
Qed.

End R15W.
