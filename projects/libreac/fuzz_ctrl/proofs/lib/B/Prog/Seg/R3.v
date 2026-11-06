(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 877 of its 1007 lines of code are new or changed and 1072 lines of the source are left out. *)
(* Segment R3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81640, 0x81688],
   19 instructions, cut Inv_B81640 (v1.9 pc 0x81640) -> cut Inv_B8168c (v1.9 pc 0x8168c) (plan-asan-ubsan.md
   section 2, row R3; section 4, INIT = reac_identity_init, 0x87de8).  Re-fit of the v1.8 proof
   (a working branch c439fa41c5b) onto the v1.9.0 bytes and a Theorem Labs lane's v1.9 cut bundle (the identity-buffer spill
   [A+136] -> [A+144]; the cut names are still the v1.8 names).
   rule 24: no function proved (a slot segment).  With s3 = S(fr) the code marks round-trip frame variables usable
   in the frame shadow (plan-asan FP.4): out[]'s last granule (S(fr) + 254 = 04, 0x81658), id at fr + 2176
   (S(fr) + 272 .. 276 = 00 00 00 00 06, 0x8165c .. 0x8166c) and frag at fr + 2256 (S(fr) + 282 .. 290 = 00 x 9,
   0x81648 .. 0x81654 and 0x81670 .. 0x81680); then it reloads the identity buffer base [A + 144] = fr + 2176
   (0x81684 ld a0,144(s1); spilled at 0x81534) and calls reac_identity_init (INIT@0x81688), which zeroes the 38
   id bytes.  The range has no instrumented shadow check and no UBSan trap.  r3_evt is the Lib-level run of the
   19 instructions with the call taken on its lib/B contract (a Section hypothesis, never its code); seg_R3 lifts
   it to the cuts.  The contract needs mem_inv, so the run is stepped on the normalized memory (MemNorm) and
   carried back to the real memory by evt_normalize + AsanLift.evt_SR_canon_lazy (r3_run).  The write set of the
   segment is the 37 frame-shadow bytes [S(fr) + 254, S(fr) + 291), the callee's stack window [sp - 2224, sp) and
   the id bytes.
   The cuts are SlotInv.v's official Inv_B81640 / Inv_B8168c (a Theorem Labs lane's v1.9 bundle; adopted from this
   segment's local cuts in deafd437a0): entry with CUR g 7 regs (s7 / s8, set in R1, not written here) and the spill
   [A + 112] = fr + 2256 (0x814c0, read by R4 at 0x81690); exit without FGBr g fr (RFG (g_in g) 0) (the 72 zero
   bytes at fr + 2256 are written only by R4's checked_memset at 0x81698, after this exit) but with
   addressable m (fr + 2256) 72 (R4's memset premise, made true here by S(fr) + 282 .. 290 = 0).  The exit also
   gets the two addressable ranges this segment's own shadow stores create: out[]'s 1492 bytes at fr + 544 (the
   entry's 1488, whose shadow S(fr) + 68 .. 253 the run does not write, plus the last granule's 4 from S(fr) + 254
   = 04) and the 38-byte id record at fr + 2176 (S(fr) + 272 .. 276 = 00 00 00 00 06, r3_id_addr).  Both cuts also
   carry ENT (the entry relation, moved across the run by ent_store and across the model step by ent_mat) and the
   spills [A + 312] = fr + 544, [A + 264] = fr + 2624, [A + 56] = fr + 3040, [A + 184] = fr + 2368,
   [A + 144] = fr + 2176 and [A + 8] = S(fr) + 68, which this segment only carries: no instruction of
   [0x81640, 0x81688) writes them, and they are above the spill base A >= fr + 3136 >= sp, outside the write set.
   Likewise carried: s2 = mrow (rg regs 18; neither the stores nor the callee write it) and our[]'s 6 addressable
   bytes at fr + 2624 (shadow S(fr) + 328, outside the written S(fr) + 254 .. 290), the A4 spills [A + 96],
   [A + 120], [A + 240], [A + 232], [A + 224], [A + 176], [A + 208], [A + 64] (adopt 5 / 6 of a working branch; above the spill
   base, outside the write set) and FRA's input facts (the input bytes at p, and for n > 0 the live addressable
   block (p, n)): the block is app memory below stklo and off the frame (fra_in_apart), so neither it nor its
   shadow is written (fra_in_keep_sh).  On FRA's side arm the FakeStack frame record FSREC is kept by Tac_slot's
   fsrec_keep_app_lo. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_init_c.
Import ListNotations.
Open Scope Z_scope.

Module RII := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_init_c.

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

(* The id record at idp (idp mod 8 = 0): its shadow S(idp) .. S(idp) + 4 = 00 00 00 00 06 (R3's stores 0x8165c ..
   0x8166c) makes its 38 bytes addressable (32 whole granules + 6). *)
Lemma r3_id_addr : forall m idp, 0 <= idp -> idp mod 8 = 0 -> idp + 38 <= APPMEM_END ->
  (forall i, 0 <= i < 38 -> app_mem (idp + i)) ->
  bytes_at rsegs m (shadow_addr idp) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
  addressable m idp 38.
Proof.
  intros m idp H0 H8 He Happ Hb.
  pose proof (r3_ba_sub m _ _ 0 4 Hb ltac:(cbn [length]; lia)) as B4.
  pose proof (r3_ba_sub m _ _ 4 1 Hb ltac:(cbn [length]; lia)) as B1.
  cbn [firstn skipn] in B4, B1. change (Z.of_nat 0) with 0 in B4. change (Z.of_nat 4) with 4 in B1.
  rewrite Z.add_0_r in B4.
  apply (r3_addr_cat m idp 32 6).
  - apply (r3_addr_z m idp 4 32); [reflexivity | lia | exact H8 | lia | intros i Hi; apply Happ; lia | exact B4].
  - apply (r3_addr_r m (idp + 32) 6 (Z_to_bv 8 6)); [lia | Z.div_mod_to_equations; lia | lia | reflexivity | lia
      | intros i Hi; replace (idp + 32 + i) with (idp + (32 + i)) by lia; apply Happ; lia |].
    rewrite r3_sh_add by lia. change (32 / 8) with 4. exact B1.
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

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma r3_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

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

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r3_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- the run: 2 li, the 15 shadow stores, ld a0,144(s1), and jal reac_identity_init by its contract ---- *)
Lemma r3_evt : RII.reac_identity_init_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp lo : Z) (xs idb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 152 <= 2 ^ 64 ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    length xs = 37%nat -> rw_cells rsegs m (Sh + 254) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> ro_cells rsegs m (Ab + 144) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8168c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
         bytes_at rsegs m' (Sh + 254) [Z_to_bv 8 4] /\
         bytes_at rsegs m' (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
         bytes_at rsegs m' (Sh + 282) (repeat (Z_to_bv 8 0) 9))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81640) fc None m (seg_rom rsegs)).
Proof.
  intros INIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp lo xs idb -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HSid Hidrt Hid8 Hshid Hidapp Hsep
    Hxs CH RWid RO144 HMI ST HAC HSW.
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
  assert (HA1 : addressable m1 idp 38).
  { apply r3_id_addr; [lia | exact Hid8 | unfold APPMEM_END; lia | intros i Hi; apply Hidapp; lia |].
    rewrite Hshid. pose proof (r3_ba_sub _ _ _ 18 5 HbC ltac:(cbn [length]; lia)) as H5.
    cbn [firstn skipn] in H5. replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in H5 by lia. exact H5. }
  eapply evt_cut.
  { eapply INIT with (lo := lo) (id := idp) (idb := idb).
    - reflexivity.
    - lia.
    - intros _. split; [Z.div_mod_to_equations; lia | exact RWid].
    - exact HMI.
    - rewrite MState.unsigned_lit by lia. exact ST.
    - rewrite MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG. lia.
    - rewrite MState.unsigned_lit by lia. unfold APPMEM_END. lia.
    - exact HAC1.
    - exact HSW1.
    - intros _. split; [exact HA1 | right; apply Hidapp; lia].
    - intros _. right. unfold RT_HI. lia.
    - intros _. rewrite MState.unsigned_lit by lia. exact Hsep. }
  intros ms' PO.
  unfold RII.reac_identity_init_post, RII.reac_identity_init_W, RII.REAC_IDENTITY_INIT_K,
    RII.REAC_IDENTITY_INIT_FRAME in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & HZ).
  subst ms'.
  specialize (HZ ltac:(lia)).
  rewrite MState.unsigned_lit in MU2, ST2 by lia.
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
  replace (ret_pc (Z_to_bv 64 0x8168c)) with (Z_to_bv 64 0x8168c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact AC2|]. split; [exact SW2|].
  split; [exact HZ|]. split; [exact B0'|]. split; [exact B18' | exact B28'].
Qed.

(* ---- seg_R3 on the cuts.  The run is r3_run feeding r3_evt on the normalized memory; FRA is moved across the
   write set (frame shadow + callee window + id) by r3_fra (sl_fr_meta of Tac_slot.v with the callee window
   allowed: RT by RT_meta_write, the S-anchored window by r3_stk_tr), the heap invariant by a_laws_store (real
   arm: every written byte is a_store_ok) or Tac_fs.a_fs_ok_store_AH (side arm: the frame and its shadow are in
   the FakeStack and its shadow), and the model by sl_fra_move. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

Lemma r3_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r3_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r3_m8 : forall fr k, fr mod 32 = 0 -> (fr + 8 * k) mod 8 = 0.
Proof. intros fr k H. Z.div_mod_to_equations. lia. Qed.

(* A byte whose shadow byte is one of the frame's 392 is a frame byte (the frame covers whole granules). *)
Lemma r3_sh_fr : forall fr x, fr mod 32 = 0 -> Sfr fr <= shadow_addr x < Sfr fr + 392 -> fr <= x < fr + 3136.
Proof. intros fr x Hfr Hx. unfold Sfr, shadow_addr in Hx. Z.div_mod_to_equations. lia. Qed.

Lemma r3_fsh : forall fr k, (forall a, fr <= a < fr + 3136 -> app_mem a) -> 0 <= k < 392 -> in_shadow (Sfr fr + k).
Proof. intros fr k Happ Hk. rewrite <- r3_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma r3_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The instrumented globals of the image lie below GT = 0x5fe000, so their shadow bytes are the first 785408 bytes
   of the low shadow. *)
Lemma r3_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r3_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r3_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma r3_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The spill base named by a spill conjunct is the A of register 9. *)
Lemma r3_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* PRA (adopt 9 of a working branch: A4's frame-loop pointer spills; v1.9: eleven conjuncts, [A+168] = fr + 2880 twice) is
   carried by any map that carries each of its spills. *)
Lemma r3_pra : forall fr (regs regs' : bvmap 5 word) m m',
  (forall off v, In off [136; 280; 168; 192; 200; 216; 104; 288; 296; 304] ->
     spill regs m off v -> spill regs' m' off v) ->
  PRA fr regs m -> PRA fr regs' m'.
Proof.
  intros fr regs regs' m m' K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold PRA.
  split; [apply K; [cbn [In]; lia | exact H1]|]. split; [apply K; [cbn [In]; lia | exact H2]|].
  split; [apply K; [cbn [In]; lia | exact H3]|]. split; [apply K; [cbn [In]; lia | exact H4]|].
  split; [apply K; [cbn [In]; lia | exact H5]|]. split; [apply K; [cbn [In]; lia | exact H6]|].
  split; [apply K; [cbn [In]; lia | exact H7]|]. split; [apply K; [cbn [In]; lia | exact H8]|].
  split; [apply K; [cbn [In]; lia | exact H9]|]. split; [apply K; [cbn [In]; lia | exact H10]|].
  apply K; [cbn [In]; lia | exact H11].
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image ---- *)

Lemma r3_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r3_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r3_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r3_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r3_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r3_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r3_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r3_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r3_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r3_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r3_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r3_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r3_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r3_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r3_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r3_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r3_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r3_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* ---- the run lemma: an evt on the normalized memory, lifted to SR on the real configuration ---- *)
Section Run.
Context {fx : FPState}.

Lemma r3_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r3_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.

Section R3.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee, taken on its lib/B contract (reac_identity_init_c.v), never on its code. *)
Hypothesis INIT : RII.reac_identity_init_contract.

(* The inner lists of the allocator laws this file reads, taken apart once each and picked by statement, not by
   position (a Theorem Labs lane 15:32Z: append-only at every level; a new generation touches these lemmas, not every site). *)
Lemma r3_fsp : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as P.
  decompose [and] P. split; [assumption | split; assumption].
Qed.

Lemma r3_fsok : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem md FS HAH Hw HFS.
  assert (Hok : AC.a_fs_ok mem FS)
    by (decompose [and ex] (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
          H mem md FS HAH Hw HFS); assumption).
  unfold AC.a_fs_ok in Hok. destruct Hok as (Hok1 & _). exact Hok1.
Qed.

Lemma r3_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros H mem mem' md HAH Hmc Hwrit.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hwrit)
    as P.
  decompose [and] P. split; [assumption | split; [assumption | split; assumption]].
Qed.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (low image, frame header, the
   spills [A + 40] / [A + 48] / [A + 336], the saved registers) and keeps every shadow byte readable (so
   RT_meta_write), given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still
   backed, the frame_AG globals still addressable and the side arm's FakeStack frame record FSREC kept
   (fsrec_keep_app_lo).  W may contain shadow bytes and the callee window. *)
Lemma r3_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = 392%nat) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HREC' HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
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
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split; [|exact (HREC' Hrec)]].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
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
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact HIN1' | exact HIN2'].
Qed.

Lemma seg_R3 : Hcut B APIf ra (Inv_B8168c B APIf ra) -> Hcut B APIf ra (Inv_B81640 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HCUR & HOUR & H144 & H112 & H312 & H264 &
                    H56 & H184 & HOUT & H8 & H18 & H2624 & H96 & H120 & H240 & H232 & H224 & H176 & H208 & H64 &
                    HPRA & H152 & H160).
  subst c.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2224 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the spills name the spill base A of register 9 *)
  destruct H144 as (A1 & HA1 & Hq144).
  assert (HA1e : A1 = A)
    by (apply (r3_spill_A regs mem 144 (fr + 2176) A A1 HA1 Hq144 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A1.
  destruct H112 as (A2 & HA2 & Hq112).
  assert (HA2e : A2 = A)
    by (apply (r3_spill_A regs mem 112 (fr + 2256) A A2 HA2 Hq112 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  destruct H312 as (A3 & HA3 & Hq312).
  assert (HA3e : A3 = A)
    by (apply (r3_spill_A regs mem 312 (fr + 544) A A3 HA3 Hq312 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A3.
  destruct H264 as (A4 & HA4 & Hq264).
  assert (HA4e : A4 = A)
    by (apply (r3_spill_A regs mem 264 (fr + 2624) A A4 HA4 Hq264 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  destruct H56 as (A5 & HA5 & Hq56).
  assert (HA5e : A5 = A)
    by (apply (r3_spill_A regs mem 56 (fr + 3040) A A5 HA5 Hq56 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A5.
  destruct H184 as (A6 & HA6 & Hq184).
  assert (HA6e : A6 = A)
    by (apply (r3_spill_A regs mem 184 (fr + 2368) A A6 HA6 Hq184 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A6.
  destruct H8 as (A7 & HA7 & Hq8).
  assert (HA7e : A7 = A)
    by (apply (r3_spill_A regs mem 8 (Sfr fr + 68) A A7 HA7 Hq8 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A7.
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + 3136 -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r3_fsp _ mem md FSb HAH Hw HFSr) as (HGT & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + 3136 -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  pose proof (r3_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* separations of the frame shadow, the frame, the callee window, the spill base *)
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (r3_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (r3_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (r3_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  (* the 37 frame-shadow cells the stores hit, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite HFSv in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (r3_ba_sub mem (Sfr fr) sh 254 37 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 254) with (Sfr fr + 254) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 37 (skipn 254 sh)) = 37%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 254) (map C1 (firstn 37 (skipn 254 sh)))).
  { apply r3_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 37) with 37.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 254 + i)).
    { replace (Sfr fr + 254 + i) with (Sfr fr + (254 + i)) by lia. apply r3_fsh; [exact Happ' | lia]. }
    exact (proj1 (HSW0 _ Hin)). }
  (* the frame is readable and writable; the id bytes as one cell *)
  assert (Hfrd : forall a, fr <= a < fr + 3136 -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r3_fsok _ mem md FSb HAH Hw HFSr a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + 3136)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  pose proof (r3_stk_rel mem (normalize rsegs mem) fr (fr + 3136) HR0 ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 2176) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs _ (fr + 2176) (fr + 2214) (fr + 3136) Hfs2 ltac:(lia)) as (Hids & _).
  destruct (stk_bytes rsegs _ (fr + 2176) (fr + 2214) Hids ltac:(lia)) as (idb & Hidl & Hidb).
  assert (RWid : rw_cells rsegs (normalize rsegs mem) (fr + 2176) [CB 38 idb]).
  { replace 38%nat with (length idb) by lia. apply r3_rw_CB; [exact Hidb|].
    replace (Z.of_nat (length idb)) with (fr + 2214 - (fr + 2176)) by lia. exact (r3_wr_stk _ _ _ Hids). }
  (* the identity buffer base spilled at [A + 144], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 144) [C8 (Z_to_bv 64 (fr + 2176))]).
  { apply r3_ro8. unfold q64 in Hq144. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq144). }
  (* r3_evt's arithmetic premises *)
  assert (P1 : RT_HI <= Sfr fr) by (unfold RT_HI; lia).
  assert (P2 : Sfr fr + 392 <= sp - FN_STACK) by lia.
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2224 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P5b : A + 152 <= 2 ^ 64) by lia.
  assert (P6 : Sfr fr + 392 <= fr + 2176 \/ fr + 2176 + 38 <= Sfr fr) by lia.
  assert (P7 : RT_HI <= fr + 2176) by (unfold RT_HI; lia).
  assert (P8 : (fr + 2176) mod 8 = 0) by (replace (fr + 2176) with (fr + 8 * 272) by lia; apply r3_m8; exact Hfrm).
  assert (P9 : shadow_addr (fr + 2176) = Sfr fr + 272)
    by (replace (fr + 2176) with (fr + 8 * 272) by lia; apply r3_sh8).
  assert (P10 : forall a, fr + 2176 <= a <= fr + 2176 + 38 -> app_mem a) by (intros a Ha; apply Happ'; lia).
  assert (P11 : fr + 2176 + 38 <= sp - 2224 \/ sp <= fr + 2176) by lia.
  unfold rg in Hr19, Hr9.
  rewrite SEGS.
  apply (r3_run regs (Z_to_bv 64 0x81640) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x8168c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\ getr R 23 = getr regs 23 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       LF.munch [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
         (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       rw_cells rsegs m0' (fr + 2176) [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
       bytes_at rsegs m0' (Sfr fr + 254) [Z_to_bv 8 4] /\
       bytes_at rsegs m0' (Sfr fr + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
       bytes_at rsegs m0' (Sfr fr + 282) (repeat (Z_to_bv 8 0) 9))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r3_mkR_of.
    eapply evt_mono.
    + apply (r3_evt INIT) with (spv := sp) (Sh := Sfr fr) (Ab := A) (idp := fr + 2176) (lo := sp - FN_STACK)
        (xs := firstn 37 (skipn 254 sh)) (idb := idb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P18' & P19' & P23' & P25' & P26' &
                  MUq & WMq & MIq & STq & ACq & SWq & RWq & Bq0 & Bq18 & Bq28).
      exists R, (Z_to_bv 64 0x8168c), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P18'|]. split; [exact P19'|]. split; [exact P23'|].
      split; [exact P25'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq|]. split; [exact RWq|].
      split; [exact Bq0|]. split; [exact Bq18 | exact Bq28].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K23 & K25 & K26 & MU0 & WM0 & ST0' & SW0' & RW0' & B0q & B18q &
       B28q)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r3_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) ST0') as ST'.
    pose proof (r3_srw_back mem' m0' HRel SW0') as SW'.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B0q) as B0.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B18q) as B18.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B28q) as B28.
    assert (HidZ : bytes_at rsegs mem' (fr + 2176) (repeat (Z_to_bv 8 0) 38)).
    { destruct RW0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* every written byte is readable after the run *)
    assert (RDW : forall x,
              ~ LF.outside [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r3_not_out in Hx. destruct Hx as [Hx|[Hx|Hx]].
      - assert (Hin : in_shadow x).
        { replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
        exact (proj2 (SW' x Hin)).
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
      - apply (r3_ba_rd mem' (fr + 2176) _ x HidZ). rewrite repeat_length. lia. }
    (* the heap invariant and stklo after the run, by arm *)
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
    assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                   (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                   AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
      - (* real arm: every written byte is a_store_ok *)
        assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
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
        destruct (r3_store ([] ++ g_H g) mem mem' md HAH Hmc Hwrit)
          as (HAH' & Hown' & Hstk' & Hhi').
        split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi'].
      - (* side arm: the frame and its shadow are the FakeStack's *)
        destruct (Hfs (fr + 3135) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
        pose proof (Hfsb FS HwFS HFSr) as HFSfr.
        destruct (r3_fsp ([] ++ g_H g) mem md FS HAH HwFS HFSr)
          as (HGTFS & HFSend & HFSapp).
        assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
        { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H.
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
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] q)
            as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r3_not_out in Hno. destruct Hno as [Hx1|[Hx1|Hx1]].
            + apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite r3_sh8; lia].
            + apply Hnok. right; left. lia.
            + apply Hnfs. lia. }
        destruct (a_fs_ok_store_AH _ _ _ _ _
                    [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
                    ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree)
          as (HAH' & Hown' & Hstk' & Hhi').
        split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi']. }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = 392%nat).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + 392 - Sfr fr) with 392 by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r3_sa_lo a (r3_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               mem mem' a 1 (HAG a Ha) MU). intros i Hi.
      replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* the slot window outside the frame is still addressable: a window byte's shadow byte is not written *)
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      assert (Hsa : 2147450880 <= shadow_addr a < 17592186044416 + 2147450880).
      { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
      assert (Hsf : shadow_addr a < Sfr fr + 254 \/ Sfr fr + 291 <= shadow_addr a).
      { unfold Sfr, shadow_addr. revert Ha2 Hfrm. clear. intros H1 H2.
        Z.div_mod_to_equations. lia. }
      apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi.
      replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* FRA's input facts: the input block is app memory below stklo <= S - SLOT_STACK < sp - 2224 and off the
       frame (fra_in_apart), so it is not the frame shadow, the callee window or the id record; its shadow bytes
       are below HIGHMEM_BEG <= sp - FN_STACK, not frame bytes, and not the frame's shadow (whole granules) *)
    assert (HIN' : bytes_at rsegs mem' (g_p g) (g_in g) /\
              (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g))).
    { apply (fra_in_keep_sh g mem mem' [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               Hinb Hinblk MU).
      intros x Hx.
      destruct (fra_in_apart B APIf ra g fr [] regs mem md HFRA x Hx) as (Happx & Hxlo & Hnfr & _).
      pose proof (shadow_of_app x Happx) as Hsx.
      assert (Hsnf : ~ (Sfr fr <= shadow_addr x < Sfr fr + 392)) by (intro Hs; exact (Hnfr (r3_sh_fr fr x Hfrm Hs))).
      pose proof Hsx as Hsx'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsx'.
      split.
      - cbn [LF.outside]. split; [|split; [lia | split; [lia | exact I]]].
        intros Hs. apply (app_not_shadow x Happx).
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia].
      - cbn [LF.outside]. split; [lia | split; [lia | split; [|exact I]]].
        intros Hf. exact (app_not_shadow (shadow_addr x) (Happ' _ ltac:(lia)) Hsx). }
    destruct HIN' as (HIN1' & HIN2').
    (* ENT across the run (the writes are the frame shadow, the callee window and the frame) and the model step *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              LF.outside [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x \/
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + 3136) \/
              (Sfr fr <= x < Sfr fr + 392)).
    { intros x Hx.
      destruct (r3_out_dec [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)] x)
        as [Ho|Hno]; [left; exact Ho|].
      apply r3_not_out in Hno. destruct Hno as [Hx1|[Hx1|Hx1]].
      - right; right; right. lia.
      - right; left. lia.
      - right; right; left. lia. }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    assert (HENT' : ENT APIf g [] mem' md).
    { eapply ent_store with
        (W := [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]);
        try exact FF; try exact HENT; try exact HFRA; try exact MU; try exact HWcases;
        try exact HSTK'; try exact HHI'; try exact HOWNk. }
    assert (HENT'' : ENT APIf g [] mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the side arm's FakeStack frame record: the run writes no app byte below stklo off the frame
       (fsrec_keep_app_lo states the UL engine's munch / outside: fr_munch_ul / fr_outside_lib convert) *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. eapply fsrec_keep_app_lo; [exact Hrec | exact HAH | exact (proj1 (fr_munch_ul _ _ _) MU) |].
      intros x Hxa Hxlo Hxf. apply (proj2 (fr_outside_lib _ _)).
      cbn [LF.outside]. split; [|split; [lia | split; [lia | exact I]]].
      intros Hin. apply (app_not_shadow x Hxa).
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r3_fsh; [exact Happ' | lia]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r3_fra g fr [] regs regs'' mem mem' md
               [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
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
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    split.
    { unfold IDBr. change (RID (g_in g) 0) with (repeat (Z_to_bv 8 0) 38). exact HidZ. }
    split.
    { apply (r3_addr_z mem' (fr + 2256) 9 72); [reflexivity | lia
        | replace (fr + 2256) with (fr + 8 * 282) by lia; apply r3_m8; exact Hfrm | lia
        | intros i Hi; apply Happ'; lia |].
      replace (fr + 2256) with (fr + 8 * 282) by lia. rewrite r3_sh8. exact B28. }
    (* the spills: at A + off >= A, above the frame shadow, the callee window and the frame (A >= S(fr) + 392,
       A >= sp, A >= fr + 3136), so outside the write set *)
    assert (KS : forall off v, 0 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    assert (KSp : forall off v, 0 <= off <= 312 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A' & HA' & Hq).
      assert (HAe : A' = A)
        by (apply (r3_spill_A regs mem off v A A' HA' Hq Hr9); unfold APPMEM_END in HAPP; lia).
      subst A'. exact (KS off v ltac:(lia) Hq). }
    split; [exact (KS 112 _ ltac:(lia) Hq112)|].
    split; [exact (KS 312 _ ltac:(lia) Hq312)|].
    split; [exact (KS 264 _ ltac:(lia) Hq264)|].
    split; [exact (KS 56 _ ltac:(lia) Hq56)|].
    split; [exact (KS 184 _ ltac:(lia) Hq184)|].
    split.
    { (* out[]'s 1492 bytes: the entry's 1488 (shadow S(fr) + 68 .. S(fr) + 253, not written) and the last
         granule's 4 (S(fr) + 254 = 04, 0x81658) *)
      change 1492 with (1488 + 4). apply (r3_addr_cat mem' (fr + 544) 1488 4).
      - apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
                 mem mem' (fr + 544) 1488 HOUT MU). intros i Hi.
        assert (Hs : Sfr fr + 68 <= shadow_addr (fr + 544 + i) < Sfr fr + 254).
        { unfold Sfr, shadow_addr. revert Hi Hfrm. clear. intros H1 H2. Z.div_mod_to_equations. lia. }
        cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]].
      - replace (fr + 544 + 1488) with (fr + 8 * 254) by lia.
        apply (r3_addr_r mem' (fr + 8 * 254) 4 (Z_to_bv 8 4)); [lia | apply r3_m8; exact Hfrm | lia | reflexivity
          | lia | intros i Hi; apply Happ'; lia |].
        rewrite r3_sh8. exact B0. }
    split.
    { (* the id record's 38 bytes (S(fr) + 272 .. 276 = 00 00 00 00 06, 0x8165c .. 0x8166c) *)
      apply r3_id_addr; [lia | exact P8 | lia | intros i Hi; apply Happ'; lia | rewrite P9; exact B18]. }
    split; [exact (KS 144 _ ltac:(lia) Hq144)|].
    split; [exact (KS 8 _ ltac:(lia) Hq8)|].
    split; [unfold rg in *; rewrite E18; exact H18|].
    (* our[]'s 6 bytes at fr + 2624: their shadow byte S(fr) + 328 is not written *)
    split.
    { apply (r3_addr_keep [(Sfr fr + 254, Sfr fr + 291); (sp - 2224, sp); (fr + 2176, fr + 2176 + 38)]
               mem mem' (fr + 2624) 6 H2624 MU). intros i Hi.
      assert (Hs : shadow_addr (fr + 2624 + i) = Sfr fr + 328).
      { unfold Sfr, shadow_addr. revert Hi Hfrm. clear. intros H1 H2. Z.div_mod_to_equations. lia. }
      rewrite Hs. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | exact I]]]. }
    (* the A4 spills (adopt 5 / 6 / 9 of a working branch), above the write set *)
    split; [exact (KSp 96 _ ltac:(lia) H96)|].
    split; [exact (KSp 120 _ ltac:(lia) H120)|].
    split; [exact (KSp 240 _ ltac:(lia) H240)|].
    split; [exact (KSp 232 _ ltac:(lia) H232)|].
    split; [exact (KSp 224 _ ltac:(lia) H224)|].
    split; [exact (KSp 176 _ ltac:(lia) H176)|].
    split; [exact (KSp 208 _ ltac:(lia) H208)|].
    split; [exact (KSp 64 _ ltac:(lia) H64)|].
    split.
    { apply (r3_pra fr regs regs'' mem mem'); [|exact HPRA].
      intros off v Hin Hs. apply (KSp off v); [clear -Hin; cbn [In] in Hin; lia | exact Hs]. }
    split; [exact (KSp 152 _ ltac:(lia) H152)|].
    (* [A + 160] = fr + 32 (v1.9.0's A4 store, appended last to the cuts), above the write set *)
    exact (KSp 160 _ ltac:(lia) H160).
Qed.

End R3.
