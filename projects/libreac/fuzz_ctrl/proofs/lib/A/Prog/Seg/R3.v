(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 866 of its 1005 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Segment R3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x8152c, 0x81574], Inv_A8152c -> Inv_A81578.
   rule 24: no function proved (a slot segment).  With s3 = S(fr) the code marks round-trip frame variables usable in
   the frame shadow (plan-asan FP.4): out[]'s last granule (S(fr) + 254 = 04, 0x81544), id at fr + 2176
   (S(fr) + 272 .. 276 = 00 00 00 00 06) and frag at fr + 2256 (S(fr) + 282 .. 290 = 00 x 9); then it calls
   reac_identity_init(s5 = fr + 2176) (INIT@0x81574), which zeroes the 38 id bytes.  r3_evt is the Lib-level run of
   the 19 instructions plus the call by its contract; seg_R3 lifts it to the cuts.  The write set of the segment is
   the 37 frame-shadow bytes [S(fr) + 254, S(fr) + 291), the callee's stack window [sp - 2224, sp) and the id bytes. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_identity_init_c.
Import ListNotations.
Open Scope Z_scope.

Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.

(* ---- byte and shadow helpers ---- *)

Lemma r3_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite MState.unsigned_lit by lia. reflexivity. Qed.

Lemma r3_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* A one-byte store `sb r,o(s3)` writes `le1 r`; the engine records it in the shadow cells once it is a byte list. *)
Ltac r3_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (r3_le1_lit z) by lia; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (r3_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac r3_sb := step; r3_fix.

Lemma r3_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r3_ba_sub : forall m A bs k j, bytes_at rsegs m A bs -> (k + j <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma r3_rd_rw : forall m A n l x, rw_cells rsegs m A [CB n l] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A n l x ((Hwf & Hb) & _) Hx. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb.
  rewrite app_nil_r in Hb. destruct Hwf as (Hl & _).
  apply (r3_ba_rd m A l x Hb). rewrite Hl. exact Hx.
Qed.

Lemma r3_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma r3_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r3_sh_add : forall p i, p mod 8 = 0 -> 0 <= i -> shadow_addr (p + i) = shadow_addr p + i / 8.
Proof. intros p i Hp Hi. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma r3_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  rewrite r3_sh_add by lia.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply r3_nth_repeat. exact Hk.
Qed.

(* The shadow of r < 8 bytes at p (p mod 8 = 0) is the byte r. *)
Lemma r3_addr_r : forall m p r (b : byte), 0 <= p -> p mod 8 = 0 -> 0 < r < 8 -> bv_signed b = r ->
  p + r <= APPMEM_END -> (forall i, 0 <= i < r -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) [b] -> addressable m p r.
Proof.
  intros m p r b Hp Hp8 Hr Hb Hpe Happ (_ & _ & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists b. split.
  - rewrite r3_sh_add by lia. replace (i / 8) with 0 by (symmetry; apply Z.div_small; lia).
    pose proof (H 0%nat ltac:(cbn; lia)) as E. cbn [Z.of_nat nth_error] in E. exact E.
  - right. rewrite Hb. assert (Hm : (p + i) mod 8 = i) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma r3_addr_cat : forall m p n k, addressable m p n -> addressable m (p + n) k -> addressable m p (n + k).
Proof.
  intros m p n k (H1 & H2 & H3 & H) (K1 & K2 & K3 & K). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [Hl|Hg]; [apply H; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply K. lia.
Qed.

Lemma r3_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma r3_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r3_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma r3_C1 : forall l, cells_wf (map C1 l) /\ cells_bytes (map C1 l) = l /\ cells_size (map C1 l) = length l.
Proof.
  induction l as [|b l (H1 & H2 & H3)]; cbn [map cells_wf cell_wf cells_bytes cbytes cells_size csize length];
    [split; [exact I | split; reflexivity]|].
  split; [split; [exact I | exact H1]|]. split; [cbn [app]; rewrite H2; reflexivity | rewrite H3; reflexivity].
Qed.

Lemma r3_rw_C1 : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A (map C1 l).
Proof.
  intros m A l Hb Hw. destruct (r3_C1 l) as (H1 & H2 & H3).
  split; [split; [exact H1 | rewrite H2; exact Hb] | rewrite H3; exact Hw].
Qed.

Lemma r3_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r3_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r3_not_out : forall lo1 hi1 lo2 hi2 lo3 hi3 x, ~ outside [(lo1, hi1); (lo2, hi2); (lo3, hi3)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2 \/ lo3 <= x < hi3.
Proof. intros lo1 hi1 lo2 hi2 lo3 hi3 x H. cbn [outside] in H. lia. Qed.


(* ---- the read-only image and the normalized memory ----
   Push 5b: a cut carries ro_agree, not mem_inv, but reac_identity_init's contract (like every callee's) asks
   for mem_inv.  The whole run is therefore done on `normalize rsegs m` (which has mem_inv by construction) and
   brought back with ms_rel / ro_same (MemNorm.evt_normalize, as a1_req_evt in Seg/A1.v).  Each memory premise
   crosses mem_rel: bytes_at and mrd are unchanged by the normalization, and a cell that is written (wr_at,
   stk, shadow_rw) is at no read-only address, since every segment of the image ends below GT = 0x5fe000 and
   both the shadow and the frame lie above it. *)
Definition r3_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma r3_rsegs_low : r3_tops rsegs 6283264 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r3_find_below : forall segs top x n s,
  r3_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r3_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r3_notro : forall a, 6283264 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [exfalso|reflexivity].
  unfold ro_addr in E.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|discriminate E].
  destruct (r3_find_below rsegs 6283264 (bv_unsigned (wa a)) 1 s r3_rsegs_low Es ltac:(lia)) as [L|L];
    [|discriminate L].
  rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma r3_notro_w : forall x : word, 6283264 <= bv_unsigned x -> ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:Es; [|reflexivity].
  destruct (r3_find_below rsegs 6283264 (bv_unsigned x) 1 s r3_rsegs_low Es ltac:(lia)) as [L|L];
    [lia | discriminate L].
Qed.

(* ro_agree survives a run whose write set is at no read-only address (here: the frame shadow, the callee's
   stack window and the identity record, all above the image's top). *)
Lemma r3_ro_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> ro_addr rsegs x = false) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Ha.
  destruct (r3_out_dec W (bv_unsigned a)) as [Ho|Hno].
  - unfold mrd. rewrite (MU a Ho). exact (HRO a Ha).
  - rewrite (HW a Hno) in Ha. discriminate Ha.
Qed.

Lemma r3_notro_shadow : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. apply r3_notro. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia.
Qed.

Lemma r3_stk_norm : forall m m0 lo hi, mem_rel rsegs m m0 ->
  (forall x, lo <= x < hi -> ro_addr rsegs (wa x) = false) -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi REL HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (HR a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r3_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r3_sw_norm : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (r3_notro_shadow a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r3_sw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL (r3_notro_shadow a Ha)). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r3_ac_norm : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma r3_ac_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma r3_rw_norm : forall m m0 A cs, mem_rel rsegs m m0 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m0 A cs.
Proof.
  intros m m0 A cs REL HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj1 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_norm rsegs m m0 A _ REL Hw HR).
Qed.

Lemma r3_rw_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs REL ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

Lemma r3_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n REL (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

(* ---- the run: 2 li, the 15 shadow stores, mv a0,s5, and jal reac_identity_init by its contract.
   The cut gives ro_agree, not mem_inv (push 5b), so the call runs on the normalized memory
   (MemNorm.evt_normalize, as a1_req_evt in Seg/A1.v).  The 15 stores keep ro_agree (r3_ro_munch: every
   written byte is a shadow byte), every premise of the contract crosses mem_rel, and the post comes back
   with ms_rel / ro_same. ---- *)
Lemma r3_evt : RII.reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh idp lo : Z) (xs idb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s5 = Z_to_bv 64 idp ->
    RT_HI <= Sh -> 6283264 <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv ->
    spv <= APPMEM_END ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> 6283264 <= idp ->
    idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    length xs = 37%nat -> rw_cells rsegs m (Sh + 254) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] ->
    ro_agree rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81578) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = s2 /\ getr R 21 = s5 /\
         munch [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
         bytes_at rsegs m' (Sh + 254) [Z_to_bv 8 4] /\
         bytes_at rsegs m' (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m' (Sh + 282) (repeat (Z_to_bv 8 0) 9))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8152c) fc None m (seg_rom rsegs)).
Proof.
 
  intros INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh idp lo xs idb -> -> -> HSrt HShGT HSlo HHM HLO HAE HSid Hidrt HidGT Hid8 Hshid Hidapp Hsep
    Hxs CH RWid HRO ST HAC HSW.
  unfold RII.reac_identity_init_contract, RII.REAC_IDENTITY_INIT, RII.REAC_IDENTITY_INIT_K in INIT.
  do 37 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 254) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m idp _ RWid) as Hidb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hidb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  pose proof (Hidapp (idp + 38) ltac:(lia)) as Hidhi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hidhi.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  r3_sb. r3_sb. r3_sb. r3_sb. r3_sb.
  r3_sb. r3_sb. r3_sb. r3_sb. r3_sb.
  r3_sb. r3_sb. r3_sb. r3_sb. r3_sb.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : shadow_rw m1).
  { apply (r3_shadow_rw _ m m1 HSW MU WM). intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 254) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 291)) as [H2|H2]|].
    - right. apply (r3_ba_rd m1 (Sh + 254) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hin. exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha).
    - left. cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
      intros Hin. exact (app_not_shadow a (Hidapp a ltac:(lia)) Ha). }
  assert (HA1a : addressable m1 idp 32).
  { apply (r3_addr_z m1 idp 4 32); [reflexivity | lia | exact Hid8 | unfold APPMEM_END; lia
      | intros i Hi; apply Hidapp; lia |].
    rewrite Hshid. pose proof (r3_ba_sub _ _ _ 18 4 HbC ltac:(cbn [length]; lia)) as H4.
    cbn [firstn skipn] in H4. replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in H4 by lia. exact H4. }
  assert (HA1b : addressable m1 (idp + 32) 6).
  { apply (r3_addr_r m1 (idp + 32) 6 (Z_to_bv 8 6)); [lia | Z.div_mod_to_equations; lia | lia | reflexivity
      | unfold APPMEM_END; lia | intros i Hi; apply Hidapp; lia |].
    rewrite r3_sh_add by lia. rewrite Hshid. change (32 / 8) with 4.
    pose proof (r3_ba_sub _ _ _ 22 1 HbC ltac:(cbn [length]; lia)) as H1.
    cbn [firstn skipn] in H1. replace (Sh + 254 + Z.of_nat 22) with (Sh + 272 + 4) in H1 by lia. exact H1. }
  pose proof (r3_addr_cat m1 idp 32 6 HA1a HA1b) as HA1.
  (* the 15 shadow stores keep ro_agree; the call needs mem_inv, so it runs on the normalized memory *)
  assert (RO1 : ro_agree rsegs m1).
  { apply (r3_ro_munch _ m m1 HRO MU). intros x Hx. apply r3_not_out in Hx.
    apply r3_notro_w. unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in *. lia. }
  pose proof (mem_rel_normalize rsegs m1 RO1) as REL1.
  assert (RWidn : rw_cells rsegs (normalize rsegs m1) idp [CB 38 idb]).
  { apply (r3_rw_norm m1 _ idp _ REL1); [|exact RWid].
    intros i Hi. cbn [cells_size csize] in Hi. apply r3_notro. lia. }
  assert (STn : stk rsegs (normalize rsegs m1) lo spv).
  { apply (r3_stk_norm m1 _ lo spv REL1); [|exact ST]. intros x Hx. apply r3_notro. lia. }
  pose proof (r3_ac_norm m1 _ REL1 HAC1) as ACn.
  pose proof (r3_sw_norm m1 _ REL1 HSW1) as SWn.
  pose proof (r3_addr_rel m1 _ idp 38 REL1 HA1) as HA1n.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m1 (seg_rom rsegs) ltac:(vm_compute; reflexivity) RO1).
    eapply INIT with (lo := lo) (id := idp) (idb := idb).
    - reflexivity.
    - lia.
    - intros _. split; [Z.div_mod_to_equations; lia | exact RWidn].
    - apply mem_inv_normalize.
    - rewrite MState.unsigned_lit by lia. exact STn.
    - rewrite MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite MState.unsigned_lit by lia. unfold APPMEM_END. lia.
    - exact ACn.
    - exact SWn.
    - intros _. split; [exact HA1n | right; apply Hidapp; lia].
    - intros _. right. unfold RT_HI. lia.
    - intros _. rewrite MState.unsigned_lit by lia. exact Hsep. }
  intros ms' (s0' & PO & MR & RS).
  unfold RII.reac_identity_init_post, RII.reac_identity_init_W, RII.REAC_IDENTITY_INIT_K,
    RII.REAC_IDENTITY_INIT_FRAME in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & HZ).
  subst s0'.
  specialize (HZ ltac:(lia)).
  rewrite MState.unsigned_lit in MU2, ST2 by lia.
  (* back to the real memory: ms_rel relates it to the normalized run's, ro_same keeps the image bytes *)
  replace (ret_pc (Z_to_bv 64 0x81578)) with (Z_to_bv 64 0x81578) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' m' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  pose proof (ro_agree_same rsegs m1 m' RO1 RS) as RO2.
  pose proof (munch_rel rsegs _ m1 (normalize rsegs m1) m' m0' REL1 Hmem RS MU2) as MU2r.
  pose proof (wmono_rel rsegs m1 (normalize rsegs m1) m' m0' REL1 Hmem RS WM2) as WM2r.
  pose proof (r3_stk_back m' m0' lo spv Hmem ST2) as ST2r.
  pose proof (r3_ac_back m' m0' Hmem AC2) as AC2r.
  pose proof (r3_sw_back m' m0' Hmem SW2) as SW2r.
  pose proof (r3_rw_back m' m0' idp _ Hmem HZ) as HZr.
  clear MU2 WM2 MI2 ST2 AC2 SW2 HZ.
  rename MU2r into MU2. rename WM2r into WM2. rename ST2r into ST2. rename AC2r into AC2.
  rename SW2r into SW2. rename HZr into HZ.
  assert (Hsub : sub_fp [(spv - 2224, spv); (idp, idp + 38)]
                   [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (Hdj : forall k n, 0 <= k -> k + n <= 37 ->
            disjoint_from [(spv - 2224, spv); (idp, idp + 38)] (Sh + 254 + k) n).
  { intros k n Hk Hkn. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  pose proof (r3_ba_sub _ _ _ 0 1 HbC ltac:(cbn [length]; lia)) as B0.
  pose proof (r3_ba_sub _ _ _ 18 5 HbC ltac:(cbn [length]; lia)) as B18.
  pose proof (r3_ba_sub _ _ _ 28 9 HbC ltac:(cbn [length]; lia)) as B28.
  cbn [firstn skipn] in B0, B18, B28.
  replace (Sh + 254 + Z.of_nat 0) with (Sh + 254) in B0 by lia.
  replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in B18 by lia.
  replace (Sh + 254 + Z.of_nat 28) with (Sh + 282) in B28 by lia.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B0 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 254) with (Sh + 254 + 0) by lia; apply Hdj; lia)) as B0'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B18 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 272) with (Sh + 254 + 18) by lia; apply Hdj; lia)) as B18'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B28 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 282) with (Sh + 254 + 28) by lia; apply Hdj; lia)) as B28'.
  subst R'.
  apply evt_done. do 2 eexists. split; [unfold MS; subst; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact RO2|]. split; [exact ST2|]. split; [exact AC2|]. split; [exact SW2|].
  split; [exact HZ|]. split; [exact B0'|]. split; [exact B18' | exact B28'].
Qed.

(* ---- seg_R3 on the cuts.  The run is sl_run_lib (Tac_b5.v) feeding r3_evt; FRA is moved across the write set
   (frame shadow + callee window + id) by r3_fra (sl_fr_meta of Tac_slot.v with the callee window allowed: RT by
   RT_meta_write, the S-anchored window by r3_stk_tr), the heap invariant by a_laws_store (real arm: every written
   byte is a_store_ok) or Tac_fs.a_fs_ok_store_AH (side arm: the frame and its shadow are in the FakeStack and its
   shadow), and the model by sl_fra_move. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs RcPro.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Open Scope Z_scope.

Lemma r3_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r3_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k).
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr k Happ Hk. rewrite <- r3_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma r3_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8). *)
Lemma r3_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* A spill cell [A + off] read through the spill base held in s1 (R2.v's r2_spill_A). *)
Lemma r3_spill_A : forall regs m A off v, rg regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v Hr HA0 Hoff HA1 (A0 & HA & Hq).
  assert (E : A0 = A).
  { pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A0 A HA Hr) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    Z.div_mod_to_equations. lia. }
  subst A0. exact Hq.
Qed.

(* The exit's copy of an entry spill / frame cell the run does not write: s1 is kept (E9), the run's munch MU
   misses the cell (lia on the context's separations). *)
Ltac r3_keep_spill Hs :=
  lazymatch type of Hs with
  | spill ?regs ?m ?off ?v =>
      match goal with
      | Hr : rg regs 9 ?A, E9 : getr ?regs' 9 = getr regs 9, MU : LF.munch _ m ?m' |- _ =>
          let Hq := fresh "Hq" in
          pose proof (r3_spill_A regs m A off v Hr ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hq;
          exists A; split; [unfold rg in *; rewrite E9; exact Hr|];
          unfold q64 in Hq |- *; eapply fl_bytes; [exact Hq | exact MU |]; rewrite length_le8;
          let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx; cbn [LF.outside]; repeat split; lia
      end
  end.
Ltac r3_keep_cells Hc :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  destruct Hc as (k & Hk); exists k;
  lazymatch type of Hk with
  | rw_cells _ ?m _ _ =>
      match goal with
      | MU : LF.munch ?W m ?m', WM : LF.wmono _ m ?m' |- _ =>
          apply (rw_cells_transport rsegs W m m' _ _ Hk MU WM)
      end
  end;
  cbn [cells_size csize disjoint_from]; repeat split; lia.

Section R3.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INIT : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_identity_init_c.reac_identity_init_contract.

(* The cuts are SlotInv.v's own (push 8, e2cbb53991f): Inv_A8152c is R2's exit, Inv_A81578 is R4's entry.  Entry:
   CUR g 7 (s6 = p + 7, s9 = n - 7, untouched here), the spill [A + 48] = fr + 2256, and out[]'s first 1488 bytes
   addressable (the 0x81528 fill), which with the store S(fr) + 254 = 04 at 0x81544 makes all 1492 bytes of out[]
   addressable.  Both cuts carry the spills [A + 128] = fr + 544, [A + 168] = fr + 2624, [A + 152] = S(fr) + 68,
   [A + 144] = fr + 2688, [A + 192] = fr + 2768: they sit at or above A >= fr + FRAME_BYTES, A >= sp, so the run (frame
   shadow, callee window, id) keeps them; likewise the two frame records at fr + 2688 / fr + 2768 (above the id
   record), s5 = fr + 2176 and s2 = mrow (reac_identity_init keeps both), and our[]'s 6 bytes addressable (their
   shadow byte S(fr) + 328 is above the stores S(fr) + 254 .. 290).  The exit has no
   `FGBr g fr (RFG (g_in g) 0)` (only R4's memset at 0x81584 writes those 72 bytes) and carries the three
   buffers this segment makes addressable (out[] 1492, id 38, frag 72, the last being R4's memset premise). *)

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (low image, frame header, the
   spills [A + 16, A + 32) and [A + 304, A + 312), the saved registers) and keeps every shadow byte readable (so
   RT_meta_write), given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still
   backed and still addressable outside the frame, the FakeStack frame record of the side arm, and the frame_AG
   globals still addressable.  W may contain shadow bytes AND the callee window, which is why neither
   Tac_slot.sl_fr_meta (frame + its shadow only) nor Tac_slot.sl_fr_cl (no shadow write) covers this segment. *)
Lemma r3_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 32 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AFw.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AFw.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' Hrec' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold ACw.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r3_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes no app byte outside the frame body
   below the real stack's low end, and nothing in the low image: the tp word is in the low image, and the
   class-6 flag byte and the slot's last word are inside the FakeStack, which a_laws_fs_place puts entirely
   below stklo.  (Tac_slot.fsrec_munch asks for EVERY app byte outside the frame body to be unwritten, which a
   segment that writes a callee stack window cannot give; the stklo bound is what this lane needs.) *)
Lemma r3_fsrec : forall hb mem mem' md W fr,
  FSREC fr mem ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  LF.munch W mem mem' ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, app_mem x -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
     x < ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md -> LF.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HWlo HW.
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS hb mem md FS HAH Htp HFSr) as (HGTb & HFSend & _ & Happ).
  assert (HFSZ : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= ACw.as_tp ACw.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold ACw.as_tp, ACw.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by lia.
      apply HWlo. unfold ACw.as_tp, ACw.ASYMS. cbn. lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [|lia|lia].
    replace x with (SMC.fs_flag FS 6 j) by lia. apply Happ. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HW; [|rewrite HB6 in *; lia|rewrite HB6 in *; lia].
    apply Happ. rewrite HB6 in *. lia. }
Qed.

Lemma seg_R3 : Hcut B APIf ra (Inv_A81578 B APIf ra) -> Hcut B APIf ra (Inv_A8152c B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & H21 & HCUR & H48 & Hout & H128 &
    HPRO & H152 & H144 & H208 & Hidr & Hjnk & H280 & H240 & Hjy & Hscr & H56 & H88 & H80 & H72 & H192 & H216 &
    H18).
  subst c.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : ACw.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ ACw.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, ACw.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hw HFSr)
        as (HGT & _ & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : ACw.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  assert (HSf8 : 8 * (Sfr fr - ASAN_K) = fr) by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  unfold ACw.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* separations of the frame shadow, the frame, the callee window *)
  assert (HSfrD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  (* the 37 frame-shadow cells the stores hit, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  pose proof (r3_ba_sub mem (Sfr fr) sh 254 37 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 254) with (Sfr fr + 254) in Hxs by lia.
  assert (Hxl : length (firstn 37 (skipn 254 sh)) = 37%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs mem (Sfr fr + 254) (map C1 (firstn 37 (skipn 254 sh)))).
  { apply r3_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 37) with 37.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 254 + i)).
    { replace (Sfr fr + 254 + i) with (Sfr fr + (254 + i)) by lia. apply r3_fsh; [exact Happ' | lia]. }
    exact (proj1 (AsanRTInv.RT_shadow_rw _ _ _ HRT _ Hin)). }
  (* the frame is readable and writable; the id bytes as one cell *)
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_state _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hw HFSr) as (Hok & _).
      destruct Hok as (Hok1 & _). destruct (Hok1 a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  destruct (stk_split rsegs mem fr (fr + 2176) (fr + FRAME_BYTES) Hfstk ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs mem (fr + 2176) (fr + 2214) (fr + FRAME_BYTES) Hfs2 ltac:(lia)) as (Hids & _).
  destruct (stk_bytes rsegs mem (fr + 2176) (fr + 2214) Hids ltac:(lia)) as (idb & Hidl & Hidb).
  assert (RWid : rw_cells rsegs mem (fr + 2176) [CB 38 idb]).
  { replace 38%nat with (length idb) by lia. apply r3_rw_CB; [exact Hidb|].
    replace (Z.of_nat (length idb)) with (fr + 2214 - (fr + 2176)) by lia. exact (r3_wr_stk _ _ _ Hids). }
  (* r3_evt's arithmetic premises *)
  assert (P1 : RT_HI <= Sfr fr) by (unfold RT_HI; lia).
  assert (P1b : 6283264 <= Sfr fr) by lia.
  assert (P2 : Sfr fr + FRAME_SHADOW <= sp - FN_STACK) by lia.
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2224 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P6 : Sfr fr + FRAME_SHADOW <= fr + 2176 \/ fr + 2176 + 38 <= Sfr fr) by lia.
  assert (P7 : RT_HI <= fr + 2176) by (unfold RT_HI; lia).
  assert (P7b : 6283264 <= fr + 2176) by lia.
  assert (P8 : (fr + 2176) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (P9 : shadow_addr (fr + 2176) = Sfr fr + 272)
    by (replace (fr + 2176) with (fr + 8 * 272) by lia; apply r3_sh8).
  assert (P10 : forall a, fr + 2176 <= a <= fr + 2176 + 38 -> app_mem a) by (intros a Ha; apply Happ'; lia).
  assert (P11 : fr + 2176 + 38 <= sp - 2224 \/ sp <= fr + 2176) by lia.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  unfold rg in Hr19, H21, H18.
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x8152c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81578 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 22 = getr regs 22 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 18 = getr regs 18 /\ getr R 21 = getr regs 21 /\
       LF.munch [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] mem mem' /\
       LF.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
       asan_cells mem' /\ shadow_rw mem' /\
       rw_cells rsegs mem' (fr + 2176) [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
       bytes_at rsegs mem' (Sfr fr + 254) [Z_to_bv 8 4] /\
       bytes_at rsegs mem' (Sfr fr + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
       bytes_at rsegs mem' (Sfr fr + 282) (repeat (Z_to_bv 8 0) 9))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply (r3_evt INIT) with (spv := sp) (Sh := Sfr fr) (idp := fr + 2176) (lo := sp - FN_STACK)
        (xs := firstn 37 (skipn 254 sh)) (idb := idb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P22' & P25' & P26' & P18' & P21' &
                  MUq & WMq & ROq & STq & ACq & SWq & RWq & Bq0 & Bq18 & Bq28).
      exists R, (Z_to_bv 64 0x81578), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P22'|].
      split; [exact P25'|]. split; [exact P26'|]. split; [exact P18'|]. split; [exact P21'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq|]. split; [exact STq|].
      split; [exact ACq|]. split; [exact SWq|]. split; [exact RWq|].
      split; [exact Bq0|]. split; [exact Bq18 | exact Bq28].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K18 & K21 & MU & WM & RO' & ST' & AC' & SW' & RWid' &
       B0 & B18 & B28) Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    (* every written byte is readable after the run *)
    assert (RDW : forall x,
              ~ LF.outside [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r3_not_out in Hx. destruct Hx as [Hx|[Hx|Hx]].
      - assert (Hin : in_shadow x).
        { replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
        exact (proj2 (SW' x Hin)).
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - apply (r3_rd_rw mem' (fr + 2176) 38 _ x RWid'). lia. }
    (* the heap invariant and stklo after the run, by arm *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (HAHS : ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                   (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                              ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                   ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                   ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs Hrec]]]].
      - (* real arm: every written byte is a_store_ok *)
        assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x)
            as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
          - exfalso. apply Hnok. apply r3_not_out in Hno. destruct Hno as [Hx1|[Hx1|Hx1]].
            + right; right; right. exists (fr + 8 * (x - Sfr fr)). split; [rewrite r3_sh8; lia|].
              right; left. apply Hreal. lia.
            + right; left. lia.
            + right; left. apply Hreal. lia. }
        exact (ACw.a_laws_store _ _ _ _ _ ALAWS ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: the frame and its shadow are the FakeStack's *)
        destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
        pose proof (Hfsb FS HwFS HFSr) as HFSfr.
        destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FS HAH HwFS HFSr)
          as (HGTFS & HFSend & _ & HFSapp).
        assert (HFS64 : FS + ACw.FS_SIZE <= 2 ^ 64).
        { pose proof (HFSapp (FS + ACw.FS_SIZE - 1) ltac:(lia)) as H.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] q)
            as [Ho|Hno].
          - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exact (RDW q Hno). }
        assert (Hmeta : forall q, fs_meta FS q ->
                  LF.outside [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] q).
        { intros q Hq. pose proof (r3_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFSapp; lia).
          cbn [LF.outside]. split; [|split; [lia | split; [lia | exact I]]].
          intros Hin. apply (app_not_shadow q Hqa).
          replace q with (Sfr fr + (q - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + ACw.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] q)
            as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r3_not_out in Hno. destruct Hno as [Hx1|[Hx1|Hx1]].
            + apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite r3_sh8; lia].
            + apply Hnok. right; left. lia.
            + apply Hnfs. lia. }
        exact (a_fs_ok_store_AH _ _ _ _ _
                 [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
                 ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree). }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HSHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r3_ag_range a Ha) as Har.
      apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               mem mem' a 1 (HAG a Ha) MU). intros i Hi.
      replace (a + i) with a by lia.
      assert (Hsa : 2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* the slot window outside the frame stays addressable: its shadow bytes are outside the write set (the
       frame's own 392 shadow bytes are the only shadow W touches, and an app byte is never a shadow byte) *)
    assert (HWA' : forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
                     addressable mem' a 1).
    { intros a H1 H2.
      apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               mem mem' a 1 (HWA a H1 H2) MU). intros i Hi.
      replace (a + i) with a by lia.
      assert (Happa : app_mem a) by (unfold app_mem; right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      assert (Hsh' : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
      assert (Hdf : shadow_addr a < Sfr fr \/ Sfr fr + FRAME_SHADOW <= shadow_addr a)
        by (unfold Sfr, shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
      assert (Hn2 : ~ (sp - 2224 <= shadow_addr a < sp)).
      { intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh'].
        unfold app_mem. right. lia. }
      assert (Hn3 : ~ (fr + 2176 <= shadow_addr a < fr + 2176 + 38)).
      { intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh']. apply Happ'. lia. }
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* the side-arm FakeStack record: its cells are below stklo, so below the callee window, and they are app
       bytes outside the frame body, so outside the frame-shadow and id parts of W *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec0.
      apply (r3_fsrec ([] ++ g_H g) mem mem' md
        [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] fr Hrec0 HAH MU).
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hap Hnfr Hlo2.
        assert (Hn1 : ~ (Sfr fr + 254 <= x < Sfr fr + 291)).
        { intros Hin. apply (app_not_shadow x Hap).
          replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
        cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r3_fra g fr [] regs regs'' mem mem' md
               [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               HFRA MU WM RO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
        try assumption.
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx.
        destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x)
          as [Ho|Hno]; [left; exact Ho | right; exact (RDW x Hno)]. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    (* ENT across the same write, then across the model step *)
    assert (HENT' : ENT APIf g [] mem' md').
    { apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
      apply (ent_store B APIf ra g fr [] regs mem mem' md
               [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] HENT HFRA MU).
      - intros x Hx.
        destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x)
          as [Ho|Hno]; [left; exact Ho|].
        apply r3_not_out in Hno. destruct Hno as [Hx1|[Hx1|Hx1]].
        + right; right; right. lia.
        + right; left. lia.
        + right; right; left. lia.
      - exact HSTK'.
      - exact HSHI'.
      - intros a _ Hown. exact (proj2 (HOWN' a) Hown). }
    (* the exit cut *)
    destruct H48 as (A0 & HA0 & Hq48).
    assert (HA0e : A0 = A).
    { pose proof Hq48 as Hb48. unfold q64 in Hb48. apply bytes_at_bound in Hb48. rewrite length_le8 in Hb48.
      pose proof (rg_eq64 regs 9 A0 A HA0 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
      Z.div_mod_to_equations. lia. }
    subst A0.
    destruct H128 as (A1 & HA1 & Hq128).
    assert (HA1e : A1 = A).
    { pose proof Hq128 as Hb128. unfold q64 in Hb128. apply bytes_at_bound in Hb128. rewrite length_le8 in Hb128.
      pose proof (rg_eq64 regs 9 A1 A HA1 Hr9) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
      Z.div_mod_to_equations. lia. }
    subst A1.
    assert (Hout1 : addressable mem' (fr + 544) 1488).
    { apply (r3_addr_keep _ mem mem' _ _ Hout MU). intros i Hi.
      rewrite r3_sh_add by (Z.div_mod_to_equations; lia).
      replace (fr + 544) with (fr + 8 * 68) by lia. rewrite r3_sh8.
      assert (Hi8 : 0 <= i / 8 < 186) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    assert (Hout2 : addressable mem' (fr + 2032) 4).
    { apply (r3_addr_r mem' (fr + 2032) 4 (Z_to_bv 8 4)); [lia | Z.div_mod_to_equations; lia | lia | reflexivity
        | lia | intros i Hi; apply Happ'; lia |].
      replace (fr + 2032) with (fr + 8 * 254) by lia. rewrite r3_sh8. exact B0. }
    assert (Hid1 : addressable mem' (fr + 2176) 32).
    { apply (r3_addr_z mem' (fr + 2176) 4 32); [reflexivity | lia | exact P8 | lia | intros i Hi; apply Happ'; lia |].
      rewrite P9. pose proof (r3_ba_sub mem' _ _ 0 4 B18 ltac:(cbn [length]; lia)) as H4.
      cbn [firstn skipn Z.of_nat] in H4. rewrite Z.add_0_r in H4. exact H4. }
    assert (Hid2 : addressable mem' (fr + 2176 + 32) 6).
    { apply (r3_addr_r mem' (fr + 2176 + 32) 6 (Z_to_bv 8 6)); [lia | Z.div_mod_to_equations; lia | lia
        | reflexivity | lia | intros i Hi; apply Happ'; lia |].
      replace (fr + 2176 + 32) with (fr + 8 * 276) by lia. rewrite r3_sh8.
      pose proof (r3_ba_sub mem' _ _ 4 1 B18 ltac:(cbn [length]; lia)) as H6.
      cbn [firstn skipn] in H6. change (Z.of_nat 4) with 4 in H6.
      replace (Sfr fr + 272 + 4) with (Sfr fr + 276) in H6 by lia. exact H6. }
    assert (Hfg : addressable mem' (fr + 2256) 72).
    { apply (r3_addr_z mem' (fr + 2256) 9 72); [reflexivity | lia | Z.div_mod_to_equations; lia | lia
        | intros i Hi; apply Happ'; lia |].
      replace (fr + 2256) with (fr + 8 * 282) by lia. rewrite r3_sh8. exact B28. }
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    split.
    { unfold IDBr. change (RID (g_in g) 0) with (repeat (Z_to_bv 8 0) 38).
      destruct RWid' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    split.
    { exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq48 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    split; [exact (r3_addr_cat mem' (fr + 544) 1488 4 Hout1
                     ltac:(replace (fr + 544 + 1488) with (fr + 2032) by lia; exact Hout2))|].
    split; [exact (r3_addr_cat mem' (fr + 2176) 32 6 Hid1 Hid2)|].
    split; [exact Hfg|].
    split.
    { exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq128 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* PRO (push 13B): the eight spills and our[]'s shadow byte S(fr) + 328 are off the write set, whose three
       parts (frame shadow, callee window, id record) are RcPro.rc_away *)
    split.
    { apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO MU Hr9 ltac:(lia) ltac:(lia) E9).
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros i Hi.
        assert (Hs : Sfr fr + 328 <= shadow_addr (fr + 2624 + i) < Sfr fr + 330).
        { unfold Sfr, shadow_addr. clear - HFRAMEb HFRAMEs Hi. Z.div_mod_to_equations. lia. }
        cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - intros x Hx. apply r3_not_out in Hx. destruct Hx as [Hx|[Hx|Hx]].
        + apply (rc_away_fsh B APIf ra g fr [] regs mem md x HFRA). lia.
        + apply (rc_away_hi B APIf ra g fr [] regs mem md x HFRA). lia.
        + apply (rc_away_frame B APIf ra g fr [] regs mem md x HFRA). lia. }
    (* s5, the spills [A + 152], [A + 144], [A + 192], [A + 280], [A + 240], the four frame cells at fr + 2688,
       fr + 2768, fr + 3040, fr + 3056, s2 = mrow and our[]'s 6 bytes: none is in the write set (the call keeps
       s2 and s5) *)
    split; [unfold rg; rewrite E21; exact H21|].
    split; [r3_keep_spill H152|]. split; [r3_keep_spill H144|]. split; [r3_keep_spill H208|].
    split; [r3_keep_cells Hidr|]. split; [r3_keep_cells Hjnk|].
    split; [r3_keep_spill H280|]. split; [r3_keep_spill H240|].
    split; [r3_keep_cells Hjy|]. split; [r3_keep_cells Hscr|].
    split; [r3_keep_spill H56|]. split; [r3_keep_spill H88|]. split; [r3_keep_spill H80|].
    split; [r3_keep_spill H72|]. split; [r3_keep_spill H192|]. split; [r3_keep_spill H216|].
    unfold rg; rewrite E18; exact H18.
Qed.

End R3.
