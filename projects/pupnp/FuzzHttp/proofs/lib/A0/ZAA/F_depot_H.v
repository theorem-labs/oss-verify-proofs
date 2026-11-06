(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import ADepot.
Import ListNotations.
Open Scope Z_scope.

Section H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (TR : Z) (m : mem) (ws : list word) (tr : list Z).
  Hypothesis BUF : u64arr asegs m TR ws.
  Hypothesis TRW : firstn (length tr) ws = map wz tr.
  Hypothesis LEN : (length tr <= length ws)%nat.
  Hypothesis RNG : Forall (fun x => 0 <= x < 2^64) tr.
  Notation n := (Z.of_nat (length tr)).

  Notation ST pc x11 x12 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz MM_M) x11 x12 a3 (wz (TR + 8 * n)) x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz pc) fc None m (seg_rom asegs)).

  Definition hl_post : machine_state -> Prop :=
    fun ms' => exists (hv x15 x16 : word), ms' = ST 0x78608 (wz (TR + 8 * n)) hv x15 x16
      /\ bv_unsigned hv = fold_left mm_add tr (mm_init n).

  #[using="ws tr LEN"] Lemma firstn_S_nth : forall (l : list Z) i, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l 0].
  Proof.
    induction l as [|x l IHl]; intros i Hi; cbn in Hi; [lia|]. destruct i; [reflexivity|].
    change (x :: firstn (S i) l = x :: (firstn i l ++ [nth i l 0])). f_equal. apply IHl. lia.
  Qed.
  #[using="ws tr LEN"] Lemma fold_last : forall (l : list Z) i v, S i = length l -> fold_left mm_add l v = mm_add (fold_left mm_add (firstn i l) v) (nth i l 0).
  Proof.
    induction l as [|x l IH]; intros i v H; cbn in H; [lia|]. destruct i as [|i].
    - destruct l; [reflexivity| cbn in H; lia].
    - cbn [fold_left firstn nth]. apply IH. lia.
  Qed.

  #[using="ws BUF TRW LEN RNG"] Lemma hash_loop : forall (K : nat) (i : nat) (hv : word) x15 x16,
    (length tr - i)%nat = K -> (i < length tr)%nat ->
    bv_unsigned hv = fold_left mm_add (firstn i tr) (mm_init n) ->
    evt asegs hl_post (ST 0x785e4 (wz (TR + 8 * Z.of_nat i)) hv x15 x16).
  Proof.
    induction K as [|K IH]; intros i hv x15 x16 HK Hi Hh; [lia|].
    pose proof (u64arr_bound asegs _ _ _ BUF) as BB.
    assert (NTH : nth_error ws i = Some (wz (nth i tr 0))).
    { rewrite <- (firstn_skipn (length tr) ws), TRW. rewrite nth_error_app1 by (rewrite length_map; lia).
      rewrite nth_error_map. rewrite (nth_error_nth' tr 0 Hi). reflexivity. }
    pose proof (u64arr_read asegs m TR ws (Z.of_nat i) (wz (nth i tr 0)) (wa (TR + 8 * Z.of_nat i)) BUF ltac:(rewrite Nat2Z.id; exact NTH) ltac:(lia) eq_refl) as HR.
    assert (KR : 0 <= nth i tr 0 < 2^64). { apply (Forall_nth (fun x => 0 <= x < 2^64) tr); [exact RNG| exact Hi]. }
    zstep.
    do 7 zstep.
    assert (STEP : forall x, bv_unsigned (Z_to_bv 64 x) = (x mod M64)).
    { intros x. rewrite Z_to_bv_unsigned. reflexivity. }
    zstep.
    if_cases KB; zify_cond KB.
    -
      replace (TR + 8 * Z.of_nat i + 8) with (TR + 8 * Z.of_nat (S i)) by lia.
      eapply (IH (S i)); [lia| lia|].
      rewrite (firstn_S_nth tr i Hi), fold_left_app. cbn [fold_left]. rewrite <- Hh. unfold mm_add. rewrite STEP. reflexivity.
    -
      apply evt_done. unfold hl_post.
      replace (TR + 8 * Z.of_nat i + 8) with (TR + 8 * n) by lia.
      eexists _, _, _. split; [reflexivity|].
      rewrite (fold_last tr i (mm_init n)) by lia. rewrite <- Hh. unfold mm_add. rewrite STEP. reflexivity.
  Qed.
End H.

Lemma srliw16_small : forall s, 0 <= s < 2^16 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 16) = 0.
Proof.
  intros s Hs. unfold bv_wrap. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Section FL.
  Context {HC : HasCeiling}.
  Variable L : dlayout.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 HV s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (hs : list Z) (h : Z).
  Hypothesis DLO : dl_ok L.
  Hypothesis HVh : bv_unsigned HV = h.
  Hypothesis NR : nodesrep L m hs.
  Hypothesis M1 : rw_cells asegs m DM1 [C8 (wz (DN0 L))].
  Hypothesis RNG : Forall (fun x => 0 <= x < 2^64) hs.
  Hypothesis NB : 16 * (zlen hs + 1) <= 2^20.
  Notation b := (bkt h).

  Notation STf pc x10 x11 x12 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 HV s4 s5 (wz 65535) s7 (wz DM1) s9 s10 s11 t3 t4 t5 t6)
        F_ (wz pc) fc None m (seg_rom asegs)).

  Definition fl_post (r : Z) : machine_state -> Prop :=
    fun ms' => (r = 0 /\ exists x10 x12, ms' = STf 0x786cc x10 (wz 0) x12)
            \/ (r <> 0 /\ exists x11, ms' = STf 0x78778 (wz r) x11 (wz (hnth hs r))).

  #[using="HC L DLO HVh NR M1 RNG NB"] Lemma find_loop : forall (K : nat) (k f : nat) (s : Z) x10 x12,
    K = k -> (k <= length hs)%nat -> (k <= f)%nat -> s = head_of (firstn k hs) b ->
    evt asegs (fl_post (find_fuel (S f) hs k b h)) (STf 0x78674 x10 (wz s) x12).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros k f s x10 x12 HK Hk Hf Hs. subst K.
    unfold dl_ok in DLO. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (head_of_bound (firstn k hs) b) as SB. unfold zlen in SB. rewrite firstn_length_le in SB by lia. rewrite <- Hs in SB.
    unfold zlen in NB.
    cbn [find_fuel]. rewrite <- Hs.
    zstep. if_cases K0; zify_cond K0.
    -
      replace (s =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      apply evt_done. left. split; [reflexivity|]. exists x10, x12. replace s with 0 by lia. reflexivity.
    - replace (s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      assert (S0 : s <> 0) by lia.
      destruct (head_of_prefix hs k b Hk) as (R & LNK & HN); [rewrite <- Hs; exact S0|]. rewrite <- Hs in R, LNK, HN.
      destruct (NR s ltac:(unfold zlen; lia)) as [sid ND].
      pose proof (head_of_bound (firstn (Z.to_nat (s - 1)) hs) b) as LB. unfold zlen in LB. rewrite firstn_length_le in LB by lia. rewrite <- LNK in LB.
      assert (HR : 0 <= hnth hs s < 2^64). { unfold hnth. apply (Forall_nth (fun x => 0 <= x < 2^64) hs); [exact RNG| lia]. }
      zstep.
      zstep.
      rewrite (srliw16_small s) by lia.
      zstep. zstep.
      replace (DM1 + Z.shiftl 0 3) with DM1 by reflexivity.
      zstep.
      zstep. if_cases KD; zify_cond KD. { exfalso. revert KD DLO. clear. intros. lia. }
      zstep. zstep.
      rewrite (Z.mod_small s 4294967296) by lia.
      zstep.
      change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. rewrite (Z.mod_small s (2^16)) by lia.
      zstep.   rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
      zstep.
      replace (DN0 L + s * 16) with (DN0 L + 16 * s) by lia.
      set (nd := DN0 L + 16 * s) in *. assert (Hnd : nd = DN0 L + 16 * s) by reflexivity. clearbody nd.
      zstep.
      zstep.
      rewrite (sx32_lit (lnk hs s)) by lia.
      zstep. if_cases KH; zify_cond KH.
      +
        replace (hnth hs s =? h) with false by (symmetry; apply Z.eqb_neq; rewrite <- HVh; lia).
        destruct f as [|f']; [lia|].
        eapply (IH (Z.to_nat (s - 1)) ltac:(lia) (Z.to_nat (s - 1)) f' (lnk hs s) (wz s) (wz (hnth hs s)) eq_refl ltac:(lia) ltac:(lia) LNK).
      +
        replace (hnth hs s =? h) with true by (symmetry; apply Z.eqb_eq; rewrite <- HVh; lia).
        zstep.
        apply evt_done. right. split; [exact S0|]. exists (wz (lnk hs s)). reflexivity.
  Qed.
End FL.
