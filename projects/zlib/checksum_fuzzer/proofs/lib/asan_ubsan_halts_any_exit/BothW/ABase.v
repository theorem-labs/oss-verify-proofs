(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).


Definition AMALLOC_SYM : Z := 0x5293c.
Definition AFREE_SYM : Z := 0x52938.
Definition AMALLOC_PC : Z := 0x52bd8.
Definition AFREE_PC : Z := 0x52a78.
Definition AMALLOC_STACK : Z := 4096.
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x5d4a90.
Definition AREQMAX : Z := 2^29 - 2^16.
Definition UDEPTH : nat := 28%nat.

Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x5f7000.
Definition ARELRO_LO : Z := 0x99000.
Definition ARELRO_HI : Z := 0x9b000.

Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
End ABLK.

Definition artcells (m : amem) : Prop :=
     rw_cells bsegs m 0x998b8 [C8 (Z_to_bv 64 0x1315a0)]
  /\ rw_cells bsegs m 0x998c8 [C8 (Z_to_bv 64 0x133628); C8 (Z_to_bv 64 0x9f2f8); C8 (Z_to_bv 64 0xa1af8);
                                C8 (Z_to_bv 64 0xa27e8); C8 (Z_to_bv 64 0xa27f0); C8 (Z_to_bv 64 0xa27e0)]
  /\ rw_cells bsegs m 0x9a440 [C8 (Z_to_bv 64 0xa27d9)]
  /\ rw_cells bsegs m 0x9b730 [C8 (Z_to_bv 64 0x92c08); C8 (Z_to_bv 64 0x9300c)]
  /\ rw_cells bsegs m 0xa1af8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xa1b00 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0xa27d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xa27e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa135c [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xa27fc [C4 (Z_to_bv 64 30)]
  /\ rw_cells bsegs m 0x1315a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x133648 [C8 (Z_to_bv 64 0x1e00010000)]
  /\ rw_cells bsegs m 0x1336a0 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells bsegs m 0x9b628 [C8 (Z_to_bv 64 0x92558); C8 (Z_to_bv 64 0x8f448)]
  /\ rw_cells bsegs m 0x9b5f8 [C8 (Z_to_bv 64 0x92b0c)]
  /\ rw_cells bsegs m 0x9b608 [C8 (Z_to_bv 64 0x9830c)]
  /\ rw_cells bsegs m 0x9b610 [C8 (Z_to_bv 64 0x8f1c0)]
  /\ rw_cells bsegs m 0x9b6e0 [C8 (Z_to_bv 64 0x93494)]
  /\ rw_cells bsegs m 0x9b5f8 [C8 (Z_to_bv 64 0x92b0c)]
  /\ rw_cells bsegs m 0x133678 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells bsegs m 0x133720 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells bsegs m 0x9f358 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x131598 [C4 (Z_to_bv 64 0)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

Definition AINSTANCE : Z := 0x9e498.
Definition AFLAGS : Z := 0x9f2f8.
Definition AINITED : Z := 0xa27d8.
Definition ACANPOISON : Z := 0xa135c.
Definition APGSZ : Z := 0x1315a0.
Definition ATSDI : Z := 0xa1360.
Definition ATSDK : Z := 0xa1364.
Definition ATP88 : Z := 0x5d4a38.
Definition ATSD : Z := 0x5f5e38.
Definition GOT_PGSZ : Z := 0x998b8.


Record alayout := mkALayout {
  al_V : nat -> Z;
  al_w : bool;
  al_U : list (list Z)
}.
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.
Definition AUMAX : Z := 4096.

Inductive abkind := ABHeap (p : aptr) | ABFake (cls : Z).
Record ablock := mkABlock { ab_kind : abkind; ab_addr : Z; ab_size : Z }.
Notation HB p A n := (mkABlock (ABHeap p) A n).

Definition in_block (LB : list ablock) (a : Z) : Prop :=
  exists b, In b LB /\ ab_addr b <= a < ab_addr b + ab_size b.
Definition in_fake (LB : list ablock) (a : Z) : Prop :=
  exists cls A n, In (mkABlock (ABFake cls) A n) LB /\ A <= a < A + n.

Definition abkind_eqb (k k' : abkind) : bool :=
  match k, k' with
  | ABHeap p, ABHeap p' => (p =? p')%N
  | ABFake c, ABFake c' => c =? c'
  | _, _ => false
  end.
Definition lb_remove (p : aptr) (LB : list ablock) : list ablock :=
  filter (fun b => negb (abkind_eqb (ab_kind b) (ABHeap p))) LB.
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.

Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).


Inductive uchain (m : amem) (top pc : Z) : Z -> Z -> nat -> list Z -> Prop :=
| uc_stop : forall prev frame k,
    ~ (prev < frame /\ frame < top - 16 /\ frame mod 8 = 0 /\ (0 < k)%nat) ->
    uchain m top pc prev frame k []
| uc_lowpc : forall prev frame k fp ra,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at bsegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at bsegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    4096 <= ra < 2^64 -> 0 <= fp < 2^64 ->
    uchain m top pc frame fp (if ra =? pc then k else Nat.pred k) tr ->
    uchain m top pc prev frame k ((if ra =? pc then [] else [ra]) ++ tr).

Lemma uchain_frame : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr ->
  (forall a, frame - 16 <= a < top -> m' (wa a) = m (wa a)) ->
  uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H. induction H as [prev frame k Hn | prev frame k fp ra H1 H2 H3 H4 B1 B2 Hra | prev frame k fp ra tr H1 H2 H3 H4 B1 B2 Hra Hfp HC IH]; intros HM.
  - apply uc_stop. exact Hn.
  - eapply uc_lowpc; eauto.
    + destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
  - eapply uc_step; eauto.
    + destruct B1 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct B2 as (X & Y & B). split; [exact X|]. split; [exact Y|]. intros i Hi. rewrite <- (B i Hi). unfold mrd. rewrite HM; [reflexivity|]. rewrite length_le8 in Hi. lia.
    + destruct (Z_lt_le_dec frame fp) as [LT|GE].
      * apply IH. intros a Ha. apply HM. lia.
      *
        inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed.

