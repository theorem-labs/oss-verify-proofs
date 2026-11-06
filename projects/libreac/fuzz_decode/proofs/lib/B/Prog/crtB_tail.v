(* crtB_tail: the last piece of the cgif-form walk of check_round_trip (image B, fuzz_decode.asan-ubsan), the
   statement crtB_tail_stmt of lib/B/Prog/crtB_cuts.v: from the cut CRT_RET_BCMP (bcmp has answered 0) to the
   statement's post dec_crt_post (lib/B/Prog/check_round_trip_cg.v:133).

   The run (offsets from the entry, crtB_iface.v names; in the donor record on a working branch at dc455613c81,
   lib/B/Prog/crt_glue.v and crt_segs_F.v walk the same code at the same addresses in the old form):
     CRT_RET_BCMP  (+0x298)  `bnez a0` not taken, a0 = s0 = R, `jal free`   crtB_segs.v crt_seg7_F
     free(R)                 afree04_rule, return to CRT_RET_FREE1
     CRT_RET_FREE1 (+0x2a4)  a0 = s5 = Q, `jal free`                         crtB_segs.v crt_seg8_F
     free(Q)                 afree04_rule, return to CRT_RET_FREE2
     CRT_RET_FREE2 (+0x2ac)  the epilogue (a0 = P from 48(sp), ra and s0 .. s11 from the frame, sp += 160) and
                             the tail `j free` at +0x2e8                     crtB_segs.v crt_seg9_F
     free(P)                 afree04_rule, return to the caller's ra: dec_crt_post.
   Every footprint run is carried into SRr by crtB_walk.v crtB_run; the memory glue is crtB_glue.v.

   The journal: the cut's crtB_mid gives the INNER journal started at the entry (stack window
   [spZ regs - DEC_CRT_STK, spZ regs), no footprint, no frame of its own); each free extends it by one event
   (3 -> 4 -> 5 -> 6), and at the end lib/Reusable/YCbq.v:725 ajournal_sub composes it with the caller's journal
   (k + DEC_CRT_EV) and YCbq.v:973 acall_kept_of_journal gives the post's acall_kept.

   The traces of the three frees (afree04_rule's universe premise, YC5d.v:86): the two `jal free` see s0 = R, a
   block below alloc_ceiling and so below sp, hence the empty chain (achain_low) and the traces dec_crt_ufix fixes
   (DEC_CRT_RA_FREE1, DEC_CRT_RA_FREE2); the tail free sees the entry's ra, sp and s0, restored by the epilogue,
   hence the entry chain ch (carried to the current state by the inner journal, which keeps every byte at or above
   the entry sp) and crtB_pre's trace fact. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss ExecF CrtBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit crtB_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_iface check_round_trip_cg crtB_cuts crtB_walk crtB_glue.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.
Module CS := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.crtB_segs.

(* ---- small facts ---- *)

(* The trace a call records (YCbq.v:317 call_trace0) is the statement's dec_utrace of ra :: the chain's spine. *)
Lemma crtT_trace : forall pc0 regs ch, call_trace0 pc0 regs ch = dec_utrace pc0 (raZ regs :: spine ch).
Proof.
  intros pc0 regs ch. unfold call_trace0, unwind_of_chain, dec_utrace, spine.
  f_equal. f_equal. cbn [flat_map map]. f_equal.
  induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|].
  cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

(* The entry is a code address of the image (vm_compute of the listing's address). *)
Lemma crtT_entry_rng : 4096 <= CRT_ENTRY <= 2 ^ 32.
Proof. unfold CRT_ENTRY. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma crtT_spZ : forall (r : bvmap 5 word) z, YKK.getr r (Z_to_bv 5 2) = w64 z -> 0 <= z < 2 ^ 64 -> spZ r = z.
Proof.
  intros r z H Hz. unfold spZ. change (bv_unsigned (YKK.getr r (Z_to_bv 5 2)) = z). rewrite H.
  unfold w64. apply unsigned_lit. exact Hz.
Qed.

Lemma crtT_raZ : forall (r : bvmap 5 word) z, YKK.getr r (Z_to_bv 5 1) = w64 z -> 0 <= z < 2 ^ 64 -> raZ r = z.
Proof.
  intros r z H Hz. unfold raZ. change (bv_unsigned (YKK.getr r (Z_to_bv 5 1)) = z). rewrite H.
  unfold w64. apply unsigned_lit. exact Hz.
Qed.

Lemma crtT_s0Z : forall (r : bvmap 5 word) z, YKK.getr r (Z_to_bv 5 8) = w64 z -> 0 <= z < 2 ^ 64 -> s0Z r = z.
Proof.
  intros r z H Hz. unfold s0Z. change (bv_unsigned (YKK.getr r (Z_to_bv 5 8)) = z). rewrite H.
  unfold w64. apply unsigned_lit. exact Hz.
Qed.

(* A free rule's block split (YC5d.v:94) removes the freed block from a permutation of the block list. *)
Lemma crtT_perm_free : forall (bl bl' l1 l2 L : list (Z * Z)) x,
  Permutation bl (x :: L) -> bl = l1 ++ x :: l2 -> bl' = l1 ++ l2 -> Permutation bl' L.
Proof.
  intros bl bl' l1 l2 L x HP E1 E2. subst bl bl'. apply Permutation_sym.
  apply (@Permutation_cons_app_inv _ L l1 l2 x). apply Permutation_sym. exact HP.
Qed.

(* A register of a state read off a footprint run's final state (crtB_walk.v crtB_ms_reg). *)
Ltac crtT_reg RX r := etransitivity; [exact (RX (Z_to_bv 5 r) eq_refl) |].
Ltac crtT_same RX := lazymatch goal with
  | |- YKK.getr _ (Z_to_bv 5 ?r) = _ => etransitivity; [exact (RX (Z_to_bv 5 r) eq_refl) | reflexivity]
  end.

Section CrtTail.
Context {rc : YM05.RunCeil}.
Local Abbreviation sink := dec_B_sink_head.
Local Abbreviation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Local Abbreviation ajournalB := (@ajournal rc sink segs B).

(* The conjuncts of a journal (YCbq.v:350-372) the piece reads. *)
Lemma crtT_j : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournalB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  AR segs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
  frames S' = own ++ frames S /\ st_nev S' <= st_nev S + k /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  astk_ok STK ly sp0.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (H1 & H2 & _ & _ & _ & H6 & H7 & _ & H9 & _ & _ & _ & _ & H14 & H15 & _ & _).
  exact (conj H1 (conj H2 (conj H6 (conj H7 (conj H9 (conj H14 H15)))))).
Qed.

(* A footprint run that writes nothing moves the journal only by the materialized model (YCbq.v:636). *)
Lemma crtT_j_sbm : AR_laws segs B -> forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  ajournalB STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  ajournalB STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros LAWS STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  apply (@ajournal_exec rc sink segs B LAWS crtB_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k
           memc mdc' (fun _ => False) HJ).
  - intros x _. reflexivity.
  - intros x Hx. exact Hx.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* A block of an AR state's block list occurs once (YCbq.v:712 sep_blocks_pos: two occurrences would overlap). *)
Lemma crtT_notin : AR_laws segs B -> forall ly S (W : world segs) mem md x L,
  AR segs B ly S W mem md -> Permutation (ablocks B ly S) (x :: L) -> 0 <= snd x -> ~ In x L.
Proof.
  intros LAWS ly S W mem md x L HAR HP Hn Hin.
  apply in_split in Hin as (L1 & L2 & ->).
  assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in x (Permutation_sym HP)); left; reflexivity).
  apply in_split in Hx as (a1 & a2 & Ea).
  rewrite Ea in HP.
  pose proof (Permutation_cons_app_inv a1 a2 (Permutation_sym HP)) as HP2.
  assert (Hx2 : In x (a1 ++ a2)) by (apply (Permutation_in x HP2); apply in_or_app; right; left; reflexivity).
  pose proof (req_size_pos (snd x) Hn) as Hr.
  apply in_app_or in Hx2 as [Hx2 | Hx2]; apply in_split in Hx2 as (b1 & b2 & ->).
  - rewrite <- app_assoc in Ea. cbn [app] in Ea.
    pose proof (sep_blocks_pos segs B LAWS ly S W mem md x x b1 b2 a2 HAR Ea) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
  - pose proof (sep_blocks_pos segs B LAWS ly S W mem md x x a1 b1 b2 HAR Ea) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* The frame (20 words at [A, A + 160)) survives a call whose acall_kept window ends at or below A. *)
Lemma crtT_frame_call : forall (W W' : world segs) mem mem' A cs slo shi E lyc Sc,
  rw_cells rsegs mem A cs -> Z.of_nat (cells_size cs) = 160 ->
  acall_kept segs B lyc Sc W mem W' mem' slo shi E ->
  (forall a, A <= a < A + 160 -> apresent (w_H W) mem a /\ apresent (w_H W') mem' a) ->
  YM05.alloc_ceiling <= A -> shi <= A -> A + 160 <= 2 ^ 64 ->
  rw_cells rsegs mem' A cs.
Proof.
  intros W W' mem mem' A cs slo shi E lyc Sc HR Hsz (K1 & _) HP HA Hs HB.
  apply (crtB_rw_cells_kept W W' mem mem' A cs HR). rewrite Hsz. intros a Ha.
  destruct (HP a Ha) as (P1 & P2).
  split; [exact P1|]. split; [exact P2|]. apply K1; lia.
Qed.

(* ---- the piece ---- *)
Theorem crtB_tail : crtB_tail_stmt B MT RO_RD.
Proof.
  intros RULES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
    ly1 S1 W1 mem1 md1 regs1 P Q R fx1 v0 v8 v16 v32 v40 HPRE HMID HREGS HA0 HS0 HFR HBLK HFRM.
  destruct RULES as (_ & HPF & _ & LAWS & HML & HUF & _ & RF & _ & _ & _).
  destruct HUF as (_ & _ & _ & HUF1 & HUF2).
  destruct HPRE as (HJ0 & Hretok & Hra4096 & Hgp & Htp & _ & _ & _ & _ & Hch & _ & Hstk1 & Hstk2 & _ & Hnch & Hns
    & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _ & Hmo & Hcost & Htr & _ & _).
  destruct HMID as (HJ1 & _ & HMO1 & _).
  destruct HREGS as (Rsp & Rgp & Rtp & _ & Rs5 & _).
  destruct HBLK as (HPERM & HP0 & HQ0 & HR0).
  unfold crtB_frame in HFR.
  change (YKK.getr regs1 (Z_to_bv 5 10) = w64 0) in HA0.
  change (YKK.getr regs1 (Z_to_bv 5 8) = w64 R) in HS0.
  change (YKK.getr regs1 (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)) in Rsp.
  change (YKK.getr regs1 (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)) in Rgp.
  change (YKK.getr regs1 (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)) in Rtp.
  change (YKK.getr regs1 (Z_to_bv 5 21) = w64 Q) in Rs5.
  change (YKK.getr regs (Z_to_bv 5 3) = w64 (as_gp B)) in Hgp.
  change (YKK.getr regs (Z_to_bv 5 4) = w64 (as_tp B)) in Htp.
  pose proof (crtT_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (HAR0 & _ & _ & HNEV0 & _ & _ & _).
  pose proof (crtT_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (HAR1 & HLY1 & _ & HNEV1 & _ & HPR1 & HSTK1).
  destruct HSTK1 as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
  pose proof crtT_entry_rng as HENT.
  pose proof (@alloc_ceiling_lt rc) as HCL.
  pose proof asan_consts as (HAC & _).
  assert (ESTK : DEC_CRT_STK = 16544) by reflexivity.
  assert (EFR : CRT_FRAME = 160) by reflexivity.
  assert (EAS : ASTACK = 16384) by reflexivity.
  assert (EEV : DEC_CRT_EV = 6) by reflexivity.
  assert (EF1 : CRT_RET_FREE1 = CRT_ENTRY + 676) by reflexivity.
  assert (EF2 : CRT_RET_FREE2 = CRT_ENTRY + 684) by reflexivity.
  assert (HNN : 1 <= nch * ns) by nia.
  pose proof (mo_free_nonneg MT HML) as HMF.
  unfold dec_crt_cost in Hcost. unfold crtB_acc3 in HMO1.

  (* ---- CRT_RET_BCMP: `bnez a0` not taken, a0 = R, `jal free` ---- *)
  eapply (@crtB_run fx1 W1 regs1 mem1 md1 CRT_RET_BCMP).
  { unfold LCK.ms_of_regs. rewrite HA0. apply CS.crt_seg7_F. }
  intros msA mdA (ms0 & E0 & HeqA) HsbmA. subst ms0.
  pose proof (@crtB_ms_shape fx1 _ _ _ msA HeqA) as EA.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ msA r HeqA) as RA.
  set (regsA := ms_regs msA) in *.
  assert (A1 : YKK.getr regsA (Z_to_bv 5 1) = w64 CRT_RET_FREE1) by (crtT_reg RA 1; reflexivity).
  assert (A2 : YKK.getr regsA (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)) by (crtT_reg RA 2; exact Rsp).
  assert (A3 : YKK.getr regsA (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)) by (crtT_reg RA 3; exact Rgp).
  assert (A4 : YKK.getr regsA (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)) by (crtT_reg RA 4; exact Rtp).
  assert (A8 : YKK.getr regsA (Z_to_bv 5 8) = w64 R) by (crtT_reg RA 8; exact HS0).
  assert (A10 : YKK.getr regsA (Z_to_bv 5 10) = w64 R) by (crtT_reg RA 10; exact HS0).
  assert (A21 : YKK.getr regsA (Z_to_bv 5 21) = w64 Q) by (crtT_reg RA 21; exact Rs5).
  pose proof (crtT_j_sbm LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdA HJ1 HsbmA) as HJ1'.
  assert (HinR : In (R, 3 * (nch * ns)) (ablocks B ly1 S1))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
  pose proof (al_blocks segs B LAWS ly1 S1 W1 mem1 md1 R (3 * (nch * ns)) HAR1 HinR) as (_ & HR4096 & HRceil & _).
  pose proof (req_size_pos (3 * (nch * ns)) ltac:(lia)) as HRsz.
  pose proof (crtT_notin LAWS ly1 S1 W1 mem1 md1 _ _ HAR1 HPERM ltac:(cbn [snd]; lia)) as NR.
  assert (USPA : spZ regsA = spZ regs - CRT_FRAME) by (apply crtT_spZ; [exact A2 | lia]).
  assert (URAA : raZ regsA = CRT_RET_FREE1) by (apply crtT_raZ; [exact A1 | lia]).
  rewrite EA. unfold CRT_FREE. rewrite <- HPF.
  eapply SRr_bind.
  { apply (RF fx1 W1 regsA mem1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 mdA 3 R (3 * (nch * ns))
             (-160) (w64 CRT_RET_FREE1) []).
    - exact HJ1'.
    - exact HinR.
    - exact A10.
    - rewrite USPA. lia.
    - reflexivity.
    - lia.
    - lia.
    - exact (eq_trans A3 Hgp).
    - exact (eq_trans A4 Htp).
    - exact A1.
    - unfold CRT_RET_FREE1. vm_compute. reflexivity.
    - lia.
    - apply (achain_chain_pre ly1 _ (spZ regsA) R [] regsA).
      + apply achain_low. lia.
      + rewrite USPA. lia.
      + apply crtT_s0Z; [exact A8 | lia].
      + rewrite URAA. lia.
    - rewrite crtT_trace, URAA. exact HUF1.
    - intros Hin. exfalso. apply NR. right. right. exact Hin.
    - apply (mok_station MT Sc S1 T _ (mo_free MT) HML Hmo HMO1); lia. }
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HPRES2 & (l1 & l2 & EL1 & EL2) & _ & HKEPT2 & HMO2).
  subst c2.
  pose proof (crtT_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & HNEV2 & _ & HPR2 & _).
  pose proof (crtT_perm_free _ _ _ _ _ _ HPERM EL1 EL2) as HPERM2.
  pose proof (crtT_frame_call W1 W2 mem1 mem2 _ _ _ _ _ _ _ HFR eq_refl HKEPT2) as HFR2.
  specialize (HFR2 ltac:(intros a Ha; split; [apply HPR1 | apply HPR2]; lia) ltac:(lia) ltac:(lia) ltac:(lia)).

  (* ---- CRT_RET_FREE1: a0 = Q, `jal free` ---- *)
  eapply (@crtB_run fx1 W2 regs2 mem2 md2 CRT_RET_FREE1).
  { unfold LCK.ms_of_regs. apply CS.crt_seg8_F. }
  intros msB mdB (ms0 & E0 & HeqB) HsbmB. subst ms0.
  pose proof (@crtB_ms_shape fx1 _ _ _ msB HeqB) as EB.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ msB r HeqB) as RB.
  set (regsB := ms_regs msB) in *.
  assert (B1 : YKK.getr regsB (Z_to_bv 5 1) = w64 CRT_RET_FREE2) by (crtT_reg RB 1; reflexivity).
  assert (B2 : YKK.getr regsB (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)).
  { crtT_reg RB 2. change (YKK.getr regs2 (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME)).
    rewrite (HPRES2 2 ltac:(unfold acallee_saved; lia)). exact A2. }
  assert (B3 : YKK.getr regsB (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)).
  { crtT_reg RB 3. change (YKK.getr regs2 (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)).
    rewrite (HPRES2 3 ltac:(unfold acallee_saved; lia)). exact A3. }
  assert (B4 : YKK.getr regsB (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)).
  { crtT_reg RB 4. change (YKK.getr regs2 (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)).
    rewrite (HPRES2 4 ltac:(unfold acallee_saved; lia)). exact A4. }
  assert (B8 : YKK.getr regsB (Z_to_bv 5 8) = w64 R).
  { crtT_reg RB 8. change (YKK.getr regs2 (Z_to_bv 5 8) = w64 R).
    rewrite (HPRES2 8 ltac:(unfold acallee_saved; lia)). exact A8. }
  assert (B10 : YKK.getr regsB (Z_to_bv 5 10) = w64 Q).
  { crtT_reg RB 10. change (YKK.getr regs2 (Z_to_bv 5 21) = w64 Q).
    rewrite (HPRES2 21 ltac:(unfold acallee_saved; lia)). exact A21. }
  pose proof (crtT_j_sbm LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdB HJ2 HsbmB) as HJ2'.
  assert (HinQ : In (Q, 8 * nch) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym HPERM2)); left; reflexivity).
  pose proof (crtT_notin LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HPERM2 ltac:(cbn [snd]; lia)) as NQ.
  assert (USPB : spZ regsB = spZ regs - CRT_FRAME) by (apply crtT_spZ; [exact B2 | lia]).
  assert (URAB : raZ regsB = CRT_RET_FREE2) by (apply crtT_raZ; [exact B1 | lia]).
  rewrite EB. unfold CRT_FREE. rewrite <- HPF.
  eapply SRr_bind.
  { apply (RF fx1 W2 regsB mem2 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly2 S2 mdB (3 + 1) Q (8 * nch)
             (-160) (w64 CRT_RET_FREE2) []).
    - exact HJ2'.
    - exact HinQ.
    - exact B10.
    - rewrite USPB. lia.
    - reflexivity.
    - lia.
    - lia.
    - exact (eq_trans B3 Hgp).
    - exact (eq_trans B4 Htp).
    - exact B1.
    - unfold CRT_RET_FREE2. vm_compute. reflexivity.
    - lia.
    - apply (achain_chain_pre ly2 _ (spZ regsB) R [] regsB).
      + apply achain_low. lia.
      + rewrite USPB. lia.
      + apply crtT_s0Z; [exact B8 | lia].
      + rewrite URAB. lia.
    - rewrite crtT_trace, URAB. exact HUF2.
    - intros Hin. exfalso. apply NQ. right. exact Hin.
    - apply (mok_station MT Sc S2 T _ (mo_free MT) HML Hmo (mle_station MT Sc S1 S2 _ _ HML HMO1 HMO2)); lia. }
  intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJ3 & HPRES3 & (m1 & m2 & EM1 & EM2) & _ & HKEPT3 & HMO3).
  subst c3.
  pose proof (crtT_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (HAR3 & HLY3 & _ & HNEV3 & HK3 & HPR3 & _).
  destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & HTOP3 & _).
  pose proof (crtT_perm_free _ _ _ _ _ _ HPERM2 EM1 EM2) as HPERM3.
  pose proof (crtT_frame_call W2 W3 mem2 mem3 _ _ _ _ _ _ _ HFR2 eq_refl HKEPT3) as HFR3.
  specialize (HFR3 ltac:(intros a Ha; split; [apply HPR2 | apply HPR3]; lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (U3 : bv_unsigned (YKK.getr regs3 (Z_to_bv 5 2)) = spZ regs - CRT_FRAME).
  { rewrite (HPRES3 2 ltac:(unfold acallee_saved; lia)), B2. unfold w64. apply unsigned_lit. lia. }

  (* ---- CRT_RET_FREE2: the epilogue and the tail `j free` ---- *)
  eapply (@crtB_run fx1 W3 regs3 mem3 md3 CRT_RET_FREE2).
  { unfold LCK.ms_of_regs. eapply CS.crt_seg9_F.
    - rewrite U3. exact HFR3.
    - rewrite U3. apply (crtB_rng_of_apresent W3 mem3); [lia | lia |].
      intros a Ha. apply HPR3. lia. }
  intros msC mdC (ms0 & E0 & HeqC) HsbmC. subst ms0.
  pose proof (@crtB_ms_shape fx1 _ _ _ msC HeqC) as EC.
  pose proof (fun r => crtB_ms_reg _ _ _ _ _ _ _ msC r HeqC) as RC.
  set (regsC := ms_regs msC) in *.
  assert (C1 : YKK.getr regsC (Z_to_bv 5 1) = YKK.getr regs (Z_to_bv 5 1)) by (crtT_reg RC 1; reflexivity).
  assert (C2 : YKK.getr regsC (Z_to_bv 5 2) = w64 (spZ regs)).
  { crtT_reg RC 2. change (Z_to_bv 64 (bv_unsigned (YKK.getr regs3 (Z_to_bv 5 2)) + 160) = w64 (spZ regs)).
    rewrite U3. unfold w64. f_equal. lia. }
  assert (C3 : YKK.getr regsC (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)).
  { crtT_reg RC 3. change (YKK.getr regs3 (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3)).
    rewrite (HPRES3 3 ltac:(unfold acallee_saved; lia)). exact B3. }
  assert (C4 : YKK.getr regsC (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)).
  { crtT_reg RC 4. change (YKK.getr regs3 (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4)).
    rewrite (HPRES3 4 ltac:(unfold acallee_saved; lia)). exact B4. }
  assert (C8 : YKK.getr regsC (Z_to_bv 5 8) = YKK.getr regs (Z_to_bv 5 8)) by (crtT_reg RC 8; reflexivity).
  assert (C10 : YKK.getr regsC (Z_to_bv 5 10) = w64 P) by (crtT_reg RC 10; reflexivity).
  assert (USPC : spZ regsC = spZ regs) by (apply crtT_spZ; [exact C2 | lia]).
  assert (URAC : raZ regsC = raZ regs).
  { unfold raZ. change (bv_unsigned (YKK.getr regsC (Z_to_bv 5 1)) = bv_unsigned (YKK.getr regs (Z_to_bv 5 1))).
    rewrite C1. reflexivity. }
  assert (US0C : s0Z regsC = s0Z regs).
  { unfold s0Z. change (bv_unsigned (YKK.getr regsC (Z_to_bv 5 8)) = bv_unsigned (YKK.getr regs (Z_to_bv 5 8))).
    rewrite C8. reflexivity. }
  pose proof (crtT_j_sbm LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mdC HJ3 HsbmC) as HJ3'.
  assert (HinP : In (P, 4 * (nch * ns)) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPERM3)); left; reflexivity).
  pose proof (crtT_notin LAWS ly3 S3 W3 mem3 md3 _ _ HAR3 HPERM3 ltac:(cbn [snd]; lia)) as NP.
  rewrite EC. unfold CRT_FREE. rewrite <- HPF.
  eapply SRr_mono.
  { apply (RF fx1 W3 regsC mem3 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly3 S3 mdC (3 + 1 + 1) P
             (4 * (nch * ns)) 0 (YKK.getr regs 1) ch).
    - exact HJ3'.
    - exact HinP.
    - exact C10.
    - rewrite USPC. lia.
    - reflexivity.
    - lia.
    - lia.
    - exact (eq_trans C3 Hgp).
    - exact (eq_trans C4 Htp).
    - exact C1.
    - exact Hretok.
    - lia.
    - apply (achain_chain_pre ly3 _ (spZ regs) (s0Z regs) ch regsC).
      + apply (achain_ly_top lyc ly3); [exact HTOP3 |].
        apply (achain_kept lyc (aview segs (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
        intros a Ha. apply HK3; lia.
      + rewrite USPC. lia.
      + exact US0C.
      + rewrite URAC. exact Hra4096.
    - rewrite crtT_trace, URAC. exact Htr.
    - intros Hin. exfalso. exact (NP Hin).
    - apply (mok_station MT Sc S3 T _ (mo_free MT) HML Hmo
               (mle_station MT Sc S2 S3 _ _ HML (mle_station MT Sc S1 S2 _ _ HML HMO1 HMO2) HMO3)); lia. }
  intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HJ4 & HPRES4 & (n1 & n2 & EN1 & EN2) & _ & _ & HMO4).
  pose proof (crtT_perm_free _ _ _ _ _ _ HPERM3 EN1 EN2) as HPERM4.
  pose proof (crtT_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (_ & _ & HFRS4 & _ & _ & _ & _).

  (* ---- the post ---- *)
  hnf. exists fx1, ly4, S4, regs4, mem4, md4.
  split; [exact Ec4|].
  split; [exact HFRM|].
  split.
  { replace (k + DEC_CRT_EV) with (k + (3 + 1 + 1 + 1)) by lia.
    apply (@ajournal_sub rc sink segs B LAWS crtB_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             DEC_CRT_STK (spZ regs) [] [] ly4 S4 W4 mem4 md4 (3 + 1 + 1 + 1) HJ0 HJ4 Hstk1 Hstk2).
    intros a (r & Hr & _). destruct Hr. }
  split.
  { intros r Hr. rewrite (HPRES4 r Hr).
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
    destruct Hr' as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]; subst r.
    - rewrite C2. unfold w64, spZ. exact (Z_to_bv_bv_unsigned (YKK.getr regs (Z_to_bv 5 2))).
    - exact C3.
    - exact C4.
    - exact C8.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC.
    - crtT_same RC. }
  split; [exact HFRS4|].
  split; [exact HPERM4|].
  split.
  { apply (@acall_kept_of_journal rc sink segs B crtB_segs_low DEC_CRT_STK (spZ regs) [] [] lyc Sc W memc mdc ly4 S4 W4 mem4
             md4 (3 + 1 + 1 + 1) (fun _ => False) HJ4 HAR0).
    - intros a (r & Hr & _). destruct Hr.
    - intros b m i Hin _ _. apply (Permutation_in _ (Permutation_sym HPERM4)). exact Hin.
    - exact sink_closed_nil. }
  apply (mle_weaken MT Sc S4 _ _ HML
           (mle_station MT Sc S3 S4 _ _ HML
              (mle_station MT Sc S2 S3 _ _ HML (mle_station MT Sc S1 S2 _ _ HML HMO1 HMO2) HMO3) HMO4)).
  unfold dec_crt_cost. lia.
Qed.
End CrtTail.
