(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the walk of diginet_decoder_init (src/diginet_decode.c:11-18) on the UBSan
   image, at 0x13f84 (24 words, 32-byte frame), against lib/U/Prog/diginet_decoder_init_c.v.
   23 of the 24 words are walked: the prologue (0x13f84-0x13f90: sp -= 32, ra / s0 / s1 to sp + 0x18 / 0x10 / 8),
   the two checks of d (0x13f94-0x13fa0), the call of diginet_cursor_init (d, body, len) (0x13fa4-0x13fb4), the
   test of p (0x13fb8), the call of diginet_personality_of (DIGINET_DESK_CONTROL24) when p is NULL (0x13fbc-0x13fc4),
   the store of the pointer at d + 32 (0x13fc8) and the epilogue (0x13fcc-0x13fdc).
   Unwalked arms:
   - 0x13f94 `beqz a0` taken (d == NULL, to the epilogue at 0x13fcc): not taken by the premise d <> 0;
   - 0x13fa0 `bnez a0` taken, to the unimp at 0x13fe0 (the UBSan alignment check of d, 0x13f9c `andi a0, a0, 7`):
     not taken by the premise d mod 8 = 0 (land7_mod8); the unimp at 0x13fe0 is the one word not walked.
   Callees: diginet_cursor_init (0x13bbc) through the premise diginet_cursor_init_contract (its walk is not in this
   unit yet), with its 25 bytes split off the decoder's 40 by DgnCellsU.v's rw_cells_split and joined again by
   rw_cells_join; diginet_personality_of (0x13dcc) through lib/U/Prog/diginet_personality_of.v's
   diginet_personality_of_holds. The decoder may lie in the caller's stack below the frame, so the stack fact is
   carried over the cursor_init call by stk_transport_cells (the bytes the callee wrote are readable), not by the
   kit's disjoint transport. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout DgnCellsU
  diginet_cursor_init_c diginet_cursor_init diginet_personality_of_c diginet_personality_of diginet_decoder_init_c.
Import ListNotations.
Open Scope Z_scope.

(* 0x13f9c `andi a0, a0, 7`: the low three bits of d *)
Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* A stack region keeps its stk fact over a callee that wrote only bytes outside it or bytes an rw_cells fact of
   the callee's result covers. *)
Lemma stk_transport_cells : forall W m m' lo hi A cs,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' -> rw_cells rsegs m' A cs ->
  (forall x, lo <= x < hi -> outside W x \/ A <= x < A + Z.of_nat (cells_size cs)) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi A cs (H1 & H2 & H) Hm Hw HC Hcase. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hcase a Ha) as [Ho | Hin].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - destruct (stk_of_rw_cells rsegs m' A cs HC) as (_ & _ & S). destruct (S a Hin) as [_ HS]. exact HS.
Qed.

(* 0x13fc8-0x13fdc, the join of the two paths: `sd s1, 0x20(s0)` stores d->p into the decoder's last 8 bytes, then
   ra, s0, s1 come back from the frame, sp += 32 and ret; the 25 cursor bytes and the 15 bytes after them join into
   decoder_cells *)
Local Ltac dinit_tail MU WM MI FR ST CC PJ hi :=
  step;
  do 5 step;
  apply evt_done; cbv beta;
  do 16 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split;
  [ release_frame FR ST hi; exact ST
  | unfold decoder_cells; apply rw_cells_join; [exact CC | exact PJ] ].

Theorem diginet_decoder_init_holds_of : diginet_cursor_init_contract -> diginet_decoder_init_contract.
Proof.
  intros ICI.
  unfold diginet_decoder_init_contract, DIGINET_DECODER_INIT, DIGINET_DECODER_INIT_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    d body len lo p dj HD0 HAL HB0 HBR HLR HP DJ ST HLO HDJ MI.
  pose proof (rw_cells_bound rsegs m d [CB 40 dj] DJ) as DB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in DB.
  pose proof ST as (Hlo0 & Hsp64 & _).
  pose proof (bv_unsigned_in_range _ sp) as RSP.
  (* the decoder's 40 bytes as the cursor's 25, its 7 padding bytes and the 8 of d->p *)
  apply (rw_cells_split_CB rsegs m d [] 40 dj [] [25%nat; 7%nat; 8%nat]) in DJ; [|reflexivity].
  cbn [app mk_CB_cells] in DJ.
  destruct (rw_cells_split m d [CB 25 (firstn 25 dj)]
              [CB 7 (firstn 7 (skipn 25 dj)); CB 8 (firstn 8 (skipn 7 (skipn 25 dj)))] DJ) as [CJ PJ].
  clear DJ. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PJ.
  pose proof (munch_refl [(d, d + 40); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  (* 0x13f84-0x13f90: the frame, with ra, s0, s1 saved in it *)
  do 4 step.
  assert (UD : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (L7 : Z.land d 7 = 0) by (rewrite land7_mod8; exact HAL).
  (* 0x13f94 `beqz a0`: d <> 0 *)
  step. unfold bv_eqb; rewrite UD. if_false.
  (* 0x13f98 `mv s0, a0`; 0x13f9c `andi a0, a0, 7`; 0x13fa0 `bnez a0` (the UBSan trap at 0x13fe0): d mod 8 = 0 *)
  step. step.
  rewrite ?UD, ?L7.
  step. if_false.
  (* 0x13fa4-0x13fb4: s1 = p, then diginet_cursor_init (d, body, len) over the decoder's first 25 bytes *)
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut;
    (* the contract's a2 is bound but named nowhere in its states: any word *)
    [ eapply (ICI _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  m1 d body len (firstn 25 dj));
      [ lia | exact HAL | lia | lia | exact CJ | assumption ]
    | intros ms' (a2' & a3' & m2 & -> & MUc & WMc & MIc & CC) ];
    assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -32));
    [ apply (stk_transport_cells [(d, d + 25)] m1 m2 lo _ d _ ST MUc WMc CC);
      intros x _; cbn [outside cursor_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
      destruct (Z.ltb_spec x d) as [L1|L1]; [left; split; [lia|exact I]|];
      destruct (Z.ltb_spec x (d + 25)) as [L2|L2]; [right; lia | left; split; [lia|exact I]]
    | clear ST; rename ST2 into ST;
      transport_after_call rsegs m1 m2 MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv rsegs m1 |- _ => clear H end; try clear m1 ]
  end.
  replace (ret_pc (Z_to_bv 64 0x13fb8)) with (Z_to_bv 64 0x13fb8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* body <> 0: the cursor's len is len *)
  rewrite (proj2 (Z.eqb_neq body 0) HB0) in CC. cbv beta iota in CC.
  rename MIc into MI. unfold cursor_cells in CC. change (Z.of_nat 25) with 25 in PJ.
  (* 0x13fb8 `bnez s1`: p *)
  step.
  destruct HP as [-> | HPS].
  - (* p == NULL: 0x13fbc `li a0, 1`, 0x13fc0 jal diginet_personality_of, 0x13fc4 `mv s1, a0` *)
    if_false.
    do 2 step.
    eapply evt_cut; [apply diginet_personality_of_holds |].
    intros ms' [a1'' ->].
    replace (ret_pc (Z_to_bv 64 0x13fc4)) with (Z_to_bv 64 0x13fc4)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step.
    dinit_tail MU WM MI FR ST CC PJ (bv_unsigned sp).
  - (* p is &personalities[0] or &personalities[1]: to 0x13fc8 *)
    destruct HPS as [-> | ->]; if_true; dinit_tail MU WM MI FR ST CC PJ (bv_unsigned sp).
Qed.

(* the closed walk: diginet_cursor_init's own walk (lib/U/Prog/diginet_cursor_init.v, relocated from fuzz_frame)
   discharges the callee contract *)
Theorem diginet_decoder_init_holds : diginet_decoder_init_contract.
Proof. exact (diginet_decoder_init_holds_of diginet_cursor_init_holds). Qed.
