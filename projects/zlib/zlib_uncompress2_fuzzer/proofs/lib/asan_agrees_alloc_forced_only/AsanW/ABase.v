(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).


Definition AMALLOC_SYM : Z := 0x5e8e4.
Definition AFREE_SYM : Z := 0x5e8e0.
Definition AMALLOC_PC : Z := 0x5eb88.
Definition AFREE_PC : Z := 0x5ea28.
Definition AMALLOC_STACK : Z := 4096.
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x65ba78.
Definition AREQMAX : Z := 2^29 - 2^16.
Definition UDEPTH : nat := 28%nat.

Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x67e000.
Definition ARELRO_LO : Z := 0xcc000.
Definition ARELRO_HI : Z := 0xd1000.

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
Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
  intros W a n FW H1 H2. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr, sclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. lia. Qed.
End ABLK.

Definition artcells (m : amem) : Prop :=
     rw_cells asegs m 0xd00a0 [C8 (Z_to_bv 64 0x168360)]
  /\ rw_cells asegs m 0xd00b0 [C8 (Z_to_bv 64 0x16a3e8); C8 (Z_to_bv 64 0xd60b8); C8 (Z_to_bv 64 0xd88b8);
                                C8 (Z_to_bv 64 0xd95a8); C8 (Z_to_bv 64 0xd95b0); C8 (Z_to_bv 64 0xd95a0)]
  /\ rw_cells asegs m 0xd0c28 [C8 (Z_to_bv 64 0xd9599)]
  /\ rw_cells asegs m 0xd1f70 [C8 (Z_to_bv 64 0xc63fc); C8 (Z_to_bv 64 0xc6800)]
  /\ rw_cells asegs m 0xd88b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xd88c0 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xd9598 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd95a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xd811c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd95bc [C4 (Z_to_bv 64 30)]
  /\ rw_cells asegs m 0x168360 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x16a408 [C8 (Z_to_bv 64 0x1e00010000)]
  /\ rw_cells asegs m 0x16a460 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells asegs m 0xd1e60 [C8 (Z_to_bv 64 0xc5d48); C8 (Z_to_bv 64 0xc2c38)]
  /\ rw_cells asegs m 0xd1e30 [C8 (Z_to_bv 64 0xc6300)]
  /\ rw_cells asegs m 0xd1e40 [C8 (Z_to_bv 64 0xcbb00)]
  /\ rw_cells asegs m 0xd1e48 [C8 (Z_to_bv 64 0xc2a04)]
  /\ rw_cells asegs m 0xd1f20 [C8 (Z_to_bv 64 0xc6c88)]
  /\ rw_cells asegs m 0xd1e30 [C8 (Z_to_bv 64 0xc6300)]
  /\ rw_cells asegs m 0x16a438 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells asegs m 0x16a4e0 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells asegs m 0xd6118 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x168358 [C4 (Z_to_bv 64 0)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

Definition AINSTANCE : Z := 0xd5258.
Definition AFLAGS : Z := 0xd60b8.
Definition ACFLAGS : Z := 0x16a3e8.
Definition AINITED : Z := 0xd9598.
Definition ACANPOISON : Z := 0xd811c.
Definition APGSZ : Z := 0x168360.
Definition ATSDI : Z := 0xd8120.
Definition ATSDK : Z := 0xd8124.
Definition ATP88 : Z := 0x65ba20.
Definition ATSD : Z := 0x67ce20.
Definition GOT_PGSZ : Z := 0xd00a0.
Definition GOT_CFLAGS : Z := 0xd00b0.


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
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
    0 <= ra < 4096 ->
    uchain m top pc prev frame k []
| uc_step : forall prev frame k fp ra tr,
    prev < frame -> frame < top - 16 -> frame mod 8 = 0 -> (0 < k)%nat ->
    bytes_at asegs m (frame - 16) (le8 (Z_to_bv 64 fp)) ->
    bytes_at asegs m (frame - 8) (le8 (Z_to_bv 64 ra)) ->
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

