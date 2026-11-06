(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMALLOC_SYM : Z := 0x54f6c.    (* [comment removed for export] *)
Definition AFREE_SYM : Z := 0x54f68.      (* [comment removed for export] *)
Definition AMALLOC_PC : Z := 0x55208.     (* [comment removed for export] *)
Definition AFREE_PC : Z := 0x550a8.       (* [comment removed for export] *)
Definition AMALLOC_STACK : Z := 4096.     (* [comment removed for export] *)
Definition AFREE_STACK : Z := 4096.
Definition ATP : Z := 0x6072b0.           (* [comment removed for export] *)
Definition AERRNO : Z := ATP - 164.       (* [comment removed for export] *)
Definition AREQMAX : Z := 10 * 2^26 + 2^12.    (* [comment removed for export] *)
Definition UDEPTH : nat := 28%nat.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.
Definition AIMG_HI : Z := 0x629000.
Definition ARELRO_LO : Z := 0xcb000.
Definition ARELRO_HI : Z := 0xcd000.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KLS : Z := 0x7fff7000.
Definition sclr (a n : Z) : Prop := a + n <= KLS \/ 0x10007fff8000 <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).
Section ABLK. Context {rc : runConstT}.
Definition ablk (lo hi : Z) : Prop := (AIMG_HI <= lo /\ hi <= KLS) \/ (0x10007fff8000 <= lo /\ hi <= ATOP).

Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= ATOP /\ hi + 8 <= 2^47.
Proof. intros lo hi H. atop_facts. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= ATOP.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_kend : forall lo hi, ablk lo hi -> hi + 8 <= KEND.
Proof. intros lo hi H. apply ablk_lin in H. unfold KEND. tauto. Qed.
Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, sclr in *. lia. Qed.
Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_app_blk : forall lo hi, ablk lo hi -> lo <= hi -> app_blk lo hi.
Proof. intros lo hi H LE. atop_facts. unfold ablk, app_blk, AIMG_HI, KLS, KLOW, KHIGH, KEND in *. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLS <= a < 0x10007fff8000 -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLS in *. lia. Qed.
Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLS \/ 0x10007fff8000 <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.
(* [comment removed for export] *)
Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (shad AIMG_HI <= shad lo /\ shad hi <= shad KLS) \/ (HSH_LO <= shad lo /\ shad hi < HSH_HI).
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_LO, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> shad AIMG_HI <= shad lo /\ shad hi < HSH_HI.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF, HSH_HI in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= shad lo \/ shad (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. atop_facts. rewrite !shad_div. unfold ablk, AIMG_HI, KLS, ASHOFF in *.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Definition wclr (iv : Z * Z) : Prop := AIMG_HI <= fst iv /\ sclr (fst iv) (snd iv - fst iv).
Lemma wclr_high : forall lo hi, 0x10007fff8000 <= lo -> wclr (lo, hi).
Proof. intros lo hi H. unfold wclr, sclr, AIMG_HI. cbn [fst snd]. lia. Qed.
Lemma wclr_ablk : forall lo hi a b, ablk lo hi -> lo <= a -> b <= hi -> wclr (a, b).
Proof. intros lo hi a b H A B. unfold wclr, sclr, ablk, AIMG_HI, KLS in *. cbn [fst snd]. lia. Qed.
Lemma wclr_outside_band : forall W x, Forall wclr W -> KLS <= x < 0x10007fff8000 -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr, sclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma wclr_outside_img : forall W x, Forall wclr W -> x < AIMG_HI -> outside W x.
Proof.
  intros W x FW Hx. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l H1 H2]; subst.
  unfold wclr in H1. cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2].
Qed.
Lemma wclr_disjoint_band : forall W a n, Forall wclr W -> KLS <= a -> a + n <= 0x10007fff8000 -> disjoint_from W a n.
Proof.
  intros W a n FW H1 H2. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr, sclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
Lemma wclr_disjoint_img : forall W a n, Forall wclr W -> a + n <= AIMG_HI -> disjoint_from W a n.
Proof.
  intros W a n FW H. induction W as [|[lo hi] W IH]; [exact I|]. inversion FW as [|y l F1 F2]; subst.
  unfold wclr in F1. cbn [fst snd] in F1. cbn. split; [lia| apply IH; exact F2].
Qed.
(* [comment removed for export] *)
Lemma shad_in_band : forall a, 0 <= a < 2^47 -> KLS + 4096 <= shad a < 0x10007fff8000.
Proof. intros a H. rewrite shad_div. unfold KLS, ASHOFF. Z.div_mod_to_equations. lia. Qed.
End ABLK.

(* [comment removed for export] *)
Definition artcells (m : amem) : Prop :=
     rw_cells bsegs m 0xcb980 [C8 (Z_to_bv 64 0x163da0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcb990 [C8 (Z_to_bv 64 0x165e28); C8 (Z_to_bv 64 0xd1af8); C8 (Z_to_bv 64 0xd42f8);
                                C8 (Z_to_bv 64 0xd4fe8); C8 (Z_to_bv 64 0xd4ff0); C8 (Z_to_bv 64 0xd4fe0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcc508 [C8 (Z_to_bv 64 0xd4fd9)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd848 [C8 (Z_to_bv 64 0xc4ccc); C8 (Z_to_bv 64 0xc50d0)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd42f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd4300 [C4 (Z_to_bv 64 1)]                                          (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd4fd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd4fe0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd3b5c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd4ffc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x163da0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x165e48 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x165ea0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd740 [C8 (Z_to_bv 64 0xc461c); C8 (Z_to_bv 64 0xc150c)]         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd7f8 [C8 (Z_to_bv 64 0xc5558)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd720 [C8 (Z_to_bv 64 0xca3d0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd728 [C8 (Z_to_bv 64 0xc1284)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd7f8 [C8 (Z_to_bv 64 0xc5558)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd710 [C8 (Z_to_bv 64 0xc4bd0)]                                   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x165e78 [C8 (Z_to_bv 64 4294967296)]                                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x165f20 [C8 (Z_to_bv 64 0x101010101010101)]                          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd1b58 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x163d98 [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AINSTANCE : Z := 0xd0c98.     (* [comment removed for export] *)
Definition AFLAGS : Z := 0xd1af8.        (* [comment removed for export] *)
Definition ACFLAGS : Z := 0x165e28.       (* [comment removed for export] *)
Definition AINITED : Z := 0xd4fd8.       (* [comment removed for export] *)
Definition ACANPOISON : Z := 0xd3b5c.    (* [comment removed for export] *)
Definition AMCTXSZ : Z := 0xd4ffc.       (* [comment removed for export] *)
Definition ASHBASE : Z := 0xd42f8.       (* [comment removed for export] *)
Definition AMIDBEG : Z := 0xd4fe8.       (* [comment removed for export] *)
Definition AMIDEND : Z := 0xd4ff0.       (* [comment removed for export] *)
Definition AHIGHEND : Z := 0xd4fe0.      (* [comment removed for export] *)
Definition AREALMEMSET : Z := 0xcd850.   (* [comment removed for export] *)
Definition AMEMSET : Z := 0xc50d0.
Definition APGSZ : Z := 0x163da0.         (* [comment removed for export] *)
Definition ATSDI : Z := 0xd3b60.         (* [comment removed for export] *)
Definition ATSDK : Z := 0xd3b64.         (* [comment removed for export] *)
Definition ATP88 : Z := 0x607258.         (* [comment removed for export] *)
Definition ATSD : Z := 0x628658.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GOT_PGSZ : Z := 0xcb980.      (* [comment removed for export] *)
Definition GOT_CFLAGS : Z := 0xcb990.    (* [comment removed for export] *)
Definition GOT_FLAGS : Z := 0xcb998.     (* [comment removed for export] *)
Definition GOT_SHBASE : Z := 0xcb9a0.    (* [comment removed for export] *)
Definition GOT_MIDBEG : Z := 0xcb9a8.    (* [comment removed for export] *)
Definition GOT_MIDEND : Z := 0xcb9b0.    (* [comment removed for export] *)
Definition GOT_HIGHEND : Z := 0xcb9b8.   (* [comment removed for export] *)
Definition GOT_REALMEMSET : Z := 0xcb9c0. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  al_V : nat -> Z;            (* [comment removed for export] *)
  al_w : bool;                (* [comment removed for export] *)
  al_U : list (list Z)        (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition al_sp0 (L : alayout) : Z := 32768 * al_V L 0%nat + 16 * al_V L 6%nat.       (* [comment removed for export] *)
Definition al_top (L : alayout) : Z := page_round_up_Z (al_sp0 L - 0xa0).              (* [comment removed for export] *)
Definition al_bot (L : alayout) : Z := al_top L - 0x800000.                             (* [comment removed for export] *)
Definition al_t (L : alayout) : Z := 4096 * al_V L 240%nat.                             (* [comment removed for export] *)
Definition al_ctx (L : alayout) : Z := 4096 * al_V L 241%nat.                           (* [comment removed for export] *)
Definition al_space_beg (L : alayout) : Z := 4096 * (al_V L 221%nat - al_V L 222%nat) + 0x10000.
Definition al_ptr_array (L : alayout) : Z := 4096 * al_V L 239%nat.
Definition al_nodes (L : alayout) : Z := 4096 * al_V L 485%nat.                         (* [comment removed for export] *)
Definition al_store (L : alayout) : Z := 4096 * al_V L 486%nat.                         (* [comment removed for export] *)
Definition al_fake (L : alayout) : Z := 4096 * al_V L 406%nat.                          (* [comment removed for export] *)
Definition AUMAX : Z := 4096.                                                           (* [comment removed for export] *)

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
(* [comment removed for export] *)
Definition hb_ids (LB : list ablock) : list aptr :=
  flat_map (fun b => match ab_kind b with ABHeap p => [p] | ABFake _ => [] end) LB.

(* [comment removed for export] *)
Definition ablock_range {rc : runConstT} (A n : Z) : Prop :=
  ablk A (A + n) /\ 0 <= n /\ A + n <= ATOP /\ A mod 16 = 0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ablock_shadow (m : amem) (A n : Z) : Prop :=
  forall g, 0 <= g -> 8 * g < n ->
    m (wa (shad A + g)) = Some (Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
      * (* [comment removed for export] *)
        inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
Qed.

