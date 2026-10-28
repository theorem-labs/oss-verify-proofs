(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_prep H_scanner_get_token H_ListFind H_list_access H_ListAddTail H_freelist
     H_membuffer_init H_membuffer_destroy H_membuffer_assign H_membuffer_append H_membuffer_append_str H_map_str_to_int H_vfmatch_A H_vfmatch_F H_match.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parse_headers_entry := 0x14c4c%Z.
Notation FMT_HDR := 0x102e5%Z.
Notation TAB_HDR := 0x2b1a8%Z.
Notation ZERO_ADDR := 0x3b700%Z.
Notation COMMA_ADDR := 0x10362%Z.
Ltac sstep := step; fix_lit_store.
Lemma le1_lit : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.
Lemma Z_to_bv8_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Ltac ph_b2z :=
  repeat match goal with |- context [Z.b2z (?a <? ?b)] =>
    first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ] end;
  cbn [Z.b2z]; try change (Z.lxor 1 0) with 1; try change (Z.lxor 0 1) with 1; try change (Z.lxor 1 1) with 0; try change (Z.lxor 0 0) with 0.

Definition phFS (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Notation SCc S MB cur := ([C8 (wz MB); C8 (wz cur); C4 (wz 0)]).

Section SEGS.
Context {HCEIL : HasCeiling}.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation L := (P + 288)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 144 <= q)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 240 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^63)%Z.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5 s6 s7 (wz 4) s9 (wz (-1)) (wz (-104)) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  #[using="QLO LO0 QP PHI"] Lemma ph_entry : forall (cur : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    stk rsegs m lo (q + 240) -> mem_inv rsegs m ->
    rw_cells rsegs m S (SCc S MB cur) -> (0 <= cur < 2^64)%Z -> (P mod 8 = 0)%Z ->
    evt rsegs (fun ms' => exists m' (j0 : list byte) (j68 : list byte),
        ms' = MS (mkR (wz 0x14cac) (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz S) (wz (q + 32)) (wz (q + 12)) a3 a4 a5 a6 a7 s2 s3 s4 (wz cur) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz sgt_entry) fc None m' (seg_rom rsegs)
        /\ munch [(q, q + 240)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo q
        /\ rw_cells rsegs m' q [CB 12 j0] /\ (exists ty, rw_cells rsegs m' (q + 12) [C4 ty])
        /\ (exists a b, rw_cells rsegs m' (q + 16) [C8 a; C8 b]) /\ (exists a b, rw_cells rsegs m' (q + 32) [C8 a; C8 b])
        /\ (exists ja id, rw_cells rsegs m' (q + 48) [CB 16 ja; C4 id]) /\ rw_cells rsegs m' (q + 68) [CB 68 j68]
        /\ rw_cells rsegs m' (q + 136) (phFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells rsegs m' S (SCc S MB cur))
      (MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parse_headers_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI SC CUR P8. unfold parse_headers_entry, sgt_entry.
    pose proof (munch_refl [(q, q + 240)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (E : bv_unsigned (wz (q + 240)) = q + 240) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 240%nat ST. rewrite !E in *.
    replace (q + 240 + -240)%Z with q in FR by lia. replace (q + 240 + -240)%Z with q in ST by lia.
    do 14 sstep. ub_null. zstep. ub_align. zstep. zstep. zstep. zstep. zstep. zstep.
    name_junk FR. splitcb FR 0%nat [12; 4; 16; 16; 20; 68]%nat. name_junk FR.
    recell FR 1%nat. splitcb FR 2%nat [8; 8]%nat. recell FR 2%nat. recell FR 3%nat.
    splitcb FR 4%nat [8; 8]%nat. recell FR 4%nat. recell FR 5%nat. splitcb FR 6%nat [16; 4]%nat. recell FR 7%nat.
    split_chunk FR 1%nat Q0 R1. split_chunk R1 1%nat Q12 R2. split_chunk R2 2%nat Q16 R3. split_chunk R3 2%nat Q32 R4.
    split_chunk R4 2%nat Q48 R5. split_chunk R5 1%nat Q68 FSH.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q16|]. split; [do 2 eexists; exact Q32|].
    split; [do 2 eexists; exact Q48|]. split; [exact Q68|]. split; [exact FSH| exact SC].
  Qed.

  Definition phFX (m : mem) : Prop :=
    (exists j0, rw_cells rsegs m q [CB 12 j0]) /\ (exists ty, rw_cells rsegs m (q + 12) [C4 ty])
    /\ (exists a b, rw_cells rsegs m (q + 16) [C8 a; C8 b]) /\ (exists a b, rw_cells rsegs m (q + 32) [C8 a; C8 b])
    /\ (exists ja id, rw_cells rsegs m (q + 48) [CB 16 ja; C4 id]) /\ (exists j68, rw_cells rsegs m (q + 68) [CB 68 j68]).

  #[using="QLO"] Lemma ph_epi : forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 136) (phFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> phFX m ->
    evt rsegs (fun ms' => ms' = MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom rsegs)
                          /\ stk rsegs m lo (q + 240))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (wz 0x14f7c) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX. unfold phFS in FSH.
    destruct FX as ([j0 Q0] & [ty Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & id & Q48) & [j68 Q68]).
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    do 13 zstep. zstep. zstep.
    eapply stk_release in Q0; [| exact ST| lia]. clear ST. release_all_ lo.
    apply evt_done. split; [reflexivity|]. lazymatch goal with H : stk rsegs m lo _ |- _ => exact H end.
  Qed.

  #[using="Type"] Lemma ph_e2 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        (r = 4 /\ ms' = MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz 64696) (wz 175292) a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5 s6 s7 (wz 4) s9 (wz (-1)) (wz (-104)) t3 t4 t5 t6)
                             F (wz 0x14cec) fc None m (seg_rom rsegs))
        \/ (r <> 4 /\ ms' = MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz 4) s9 s10 s11 t3 t4 t5 t6)
                             F (wz 0x14f38) fc None m (seg_rom rsegs)))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x14cac) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. if_cases K; zify_cond K.
    - apply evt_done. right. split; [lia| reflexivity].
    - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. left. split; [lia|]. reflexivity.
  Qed.

  #[using="Type"] Lemma ph_head : forall (cur : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m S (SCc S MB cur) -> (0 <= cur < 2^64)%Z ->
    evt rsegs (fun ms' => ms' = PRS sgt_entry (wz 0x14ce8) t0 t1 t2 (wz S) (wz (q + 32)) (wz (q + 12)) a3 a4 a5 a6 a7 (wz cur) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14cd4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI SC CUR. unfold sgt_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma ph_h2 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' => ms' = PRS (if r =? 4 then 0x14cec else 0x14f38) x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14ce8 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - replace (r =? 4) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. reflexivity.
    - replace (r =? 4) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  Qed.

  #[using="QLO QP PHI"] Lemma ph_restore_exit : forall (cur0 curx r : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 x18 x19 x20 s6' s7' s8' s9' s10' s11' (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 136) (phFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> phFX m ->
    rw_cells rsegs m S (SCc S MB curx) -> (0 <= cur0 < 2^64)%Z -> (0 <= curx < 2^64)%Z ->
    evt rsegs (fun ms' => exists m', ms' = MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom rsegs)
                          /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                          /\ stk rsegs m' lo (q + 240) /\ rw_cells rsegs m' S (SCc S MB cur0))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 (wz cur0) s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
          F (wz 0x14f38) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX SC CUR0 CURX. unfold phFS in FSH.
    destruct FX as ([j0 Q0] & [ty Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & id & Q48) & [j68 Q68]).
    pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    sstep. zstep.
    eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
      split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
      split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
    cbv beta. intros ms' [-> ST']. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="Type"] Lemma u64arr_read4 : forall m A ws (i : Z) w a,
    u64arr rsegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
    ov_read_bytes rsegs m a 4 = Some (le4 w).
  Proof.
    intros m A ws i w a [Hb _] Hn Hi ->.
    destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
    replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
    rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 4 Hb).
    2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
    rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
    rewrite firstn_app. replace (firstn 4 (le8 w)) with (le4 w) by reflexivity.
    rewrite length_le8. replace (4 - 8)%nat with 0%nat by reflexivity. rewrite firstn_O, app_nil_r. reflexivity.
  Qed.

  Variable ws : list word.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, (0 <= i < 33)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.

  #[using="ws WSL"] Lemma ph_core1 : forall (ty : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 12) [C4 (wz ty)] -> (0 <= ty <= 5)%Z ->
    evt rsegs (fun ms' =>
        (ty = 0 /\ ms' = PRS match_entry (wz 0x14d04) t0 t1 t2 (wz S) (wz FMT_HDR) (wz (q + 16)) a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (ty <> 0 /\ ms' = PRS 0x14f40 x1 t0 t1 t2 (wz ty) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x14cec x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TYC TYR. unfold match_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. rewrite (sx32_lit ty) by lia. zstep. if_cases K; zify_cond K.
    - apply evt_done. right. split; [lia| reflexivity].
    - zstep. zstep. zstep. zstep. apply evt_done. left. split; [lia| reflexivity].
  Qed.

  Definition notid_r (ty isreq meth : Z) : Z := if ty =? 2 then (if (negb (isreq =? 0)) && (meth =? 4) then 0 else 4)%bool else 3.
  Definition notid_pos (ty isreq meth pos : Z) : Z := if ty =? 2 then (if (negb (isreq =? 0)) && (meth =? 4) then 4 else 3)%bool else pos.
  #[using="QLO QP PHI ws WSL"] Lemma ph_notid : forall (ty isreq meth err hack pos entp clen csz esp : Z) (majw minw padw : word) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 s5' s6' s7' s8' s9' s10' s11' (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 136) (phFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> phFX m ->
    rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> (0 <= meth < 2^31)%Z ->
    rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 majw; C4 minw; C4 padw] -> (0 <= isreq <= 1)%Z ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp) -> (0 <= pos <= 4)%Z ->
    (1 <= ty <= 5)%Z ->
    evt rsegs (fun ms' => exists a1' m', ms' = MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0 s1 (wz (notid_r ty isreq meth)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom rsegs)
                          /\ munch [(P + 448, P + 452)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                          /\ stk rsegs m' lo (q + 240)
                          /\ rw_cells rsegs m' (P + 440) (p_ctl_cells err hack (notid_pos ty isreq meth pos) entp clen csz esp))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) (wz ty) a1 a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
          F (wz 0x14f40) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX K1C METH K3C ISR K5 POS TYR. unfold phFS in FSH. unfold p_ctl_cells in *.
    destruct FX as ([j0 Q0] & [tyq Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & id & Q48) & [j68 Q68]).
    pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold notid_r, notid_pos.
    zstep. zstep. if_cases K; zify_cond K.
    -
      replace (ty =? 2) with false by (symmetry; apply Z.eqb_neq; lia).
      zstep. zstep.
      eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
        split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
        split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
      cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact K5.
    - replace (ty =? 2) with true by (symmetry; apply Z.eqb_eq; lia).
      zstep. rewrite (sx32_lit isreq) by lia. zstep. if_cases K2; zify_cond K2.
      +
        replace (isreq =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb andb].
        zstep. sstep. zstep.
        eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
          split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
          split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
        cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
      + replace (isreq =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb andb].
        zstep. rewrite (sx32_lit meth) by lia. zstep. zstep. if_cases K4; zify_cond K4.
        *   replace (meth =? 4) with false by (symmetry; apply Z.eqb_neq; lia).
          zstep. sstep. zstep.
          eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
            split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
            split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
          cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
        * replace (meth =? 4) with true by (symmetry; apply Z.eqb_eq; lia).
          zstep. sstep. zstep.
          eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
            split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
            split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
          cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="ws WSL"] Lemma ph_m2 : forall (r T tl : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 32) [C8 (wz T); C8 (wz tl)] -> (0 <= r <= 5)%Z -> (0 <= T < 2^64)%Z -> (0 <= tl < 2^64)%Z ->
    evt rsegs (fun ms' =>
        (r = 4 /\ ms' = PRS map_str_to_int_entry (wz 0x14d20) t0 t1 t2 (wz T) (wz tl) (wz TAB_HDR) (wz 33) (wz 0) a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (r <> 4 /\ ms' = PRS 0x14f38 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x14d04 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TC RR TR TLR. unfold map_str_to_int_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - apply evt_done. right. split; [lia| reflexivity].
    - do 6 zstep. apply evt_done. left. split; [lia| reflexivity].
  Qed.

  #[using="lo QLO LO0 QP PHI WSL HID"] Lemma ph_idx : forall (idx meth : Z) (ja : list byte) (idw : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u64arr rsegs m TAB_HDR ws ->
    rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> (0 <= meth < 2^31)%Z ->
    rw_cells rsegs m (q + 48) [CB 16 ja; C4 idw] ->
    (idx = -1 \/ 0 <= idx < 33)%Z ->
    evt rsegs (fun ms' => exists m',
        (idx = -1 /\ ms' = PRS 0x14d80 x1 t0 t1 t2 (wz idx) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
        \/ (exists id meth', 0 <= idx < 33 /\ nth_error ws (Z.to_nat (2 * idx + 1)) = Some (wz id) /\ 0 <= id < 64 /\ meth' = (if id =? 19 then 11 else meth)
             /\ ms' = PRS ListFind_entry (wz 0x14d68) t0 t1 t2 (wz L) (wz 0) (wz (q + 48)) a3 a4 a5 a6 a7 s5 s6 s7 (wz id) t3 t4 t5 t6 gp tp F fc m'
             /\ munch [(P + 4, P + 8); (q + 48, q + 68)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
             /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')] /\ rw_cells rsegs m' (q + 48) [CB 16 ja; C4 (wz id)]
             /\ u64arr rsegs m' TAB_HDR ws))%Z
      (PRS 0x14d20 x1 t0 t1 t2 (wz idx) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TAB K1C METH TMP IDX. unfold ListFind_entry.
    pose proof (munch_refl [(P + 4, P + 8); (q + 48, q + 68)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct IDX as [-> | IR].
    - zstep. lit_branch. apply evt_done. exists m. left. split; [lia|]. split; [| reflexivity]. reflexivity.
    - zstep. if_cases K; zify_cond K; [lia|]. destruct (HID idx IR) as (id & HN & IDR).
      pose proof (u64arr_read4 m TAB_HDR ws (2 * idx + 1) (wz id) (Z_to_bv 64 (TAB_HDR + Z.shiftl idx 4 + 8)) TAB HN ltac:(lia)
                    ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
      zstep. step. ubr. zstep. zstep.
      step. let KU := fresh "KU" in if_cases KU; zify_cond KU; ub_land KU;
        [exfalso; rewrite ?Z.shiftl_mul_pow2 in KU by lia; change 18446744073709551615 with (Z.ones 64) in KU; rewrite Z.land_ones in KU by lia; lia| try clear KU].
      zstep. zstep. zstep. rewrite (sx32_lit id) by lia. zstep. zstep. if_cases K2; zify_cond K2.
      + sstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. right. exists id, meth.
        replace (id =? 19) with false by (symmetry; apply Z.eqb_neq; lia).
        split; [lia|]. split; [exact HN|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        repeat (split; [eassumption|]). eassumption.
      + zstep. sstep. sstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. right. exists id, 11.
        replace (id =? 19) with true by (symmetry; apply Z.eqb_eq; lia).
        split; [lia|]. split; [exact HN|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="ws WSL"] Lemma ph_lf2 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> (0 <= r < 2^64)%Z -> (r mod 8 = 0)%Z ->
    (r = 0 \/ exists pv nx it, rw_cells rsegs m r (node_cells pv nx it) /\ it <> 0 /\ 0 <= it < 2^64)%Z ->
    evt rsegs (fun ms' =>
        (r = 0 /\ ms' = PRS 0x14e7c x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 0) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (exists pv nx it, r <> 0 /\ rw_cells rsegs m r (node_cells pv nx it) /\ it <> 0 /\ 0 <= it < 2^64
             /\ ms' = PRS 0x14e30 x1 t0 t1 t2 (wz r) (wz 0) a2 a3 a4 a5 a6 a7 (wz it) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m))%Z
      (PRS 0x14d68 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI RR R8 NODE. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - zstep. zstep. lit_branch. apply evt_done. left. split; [lia| reflexivity].
    - destruct NODE as [->|(pv & nx & it & NC & ITNZ & ITR)]; [exfalso; lia|]. unfold node_cells in NC.
      zstep. replace (Z.land r 7) with 0 by (rewrite land7_mod8; lia). zstep. lit_branch.
      zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      apply evt_done. right. exists pv, nx, it. split; [lia|]. split; [exact NC|]. split; [lia|]. split; [lia|]. reflexivity.
  Qed.

  #[using="QLO QP PHI ws WSL"] Lemma ph_unk1 : forall (A T tl : Z) (bs : list byte) (b : byte) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8arr rsegs m A bs -> nth_error bs (Z.to_nat (T + tl - A)) = Some b ->
    (A <= T)%Z -> (0 <= tl)%Z -> (T + tl - A < Z.of_nat (length bs))%Z -> (A + Z.of_nat (length bs) <= lo)%Z ->
    rw_cells rsegs m (q + 32) [C8 (wz T); C8 (wz tl)] -> (0 < T)%Z ->
    evt rsegs (fun ms' => exists m',
        ms' = PRS ListHead_entry (wz 0x14db8) t0 t1 t2 (wz L) (wz T) (wz 1) (wz 0) a4 a5 a6 a7 s5 (wz T) s7 (wz (bv_unsigned b)) t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(T + tl, T + tl + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ u8arr rsegs m' A (upd bs (Z.to_nat (T + tl - A)) (Z_to_bv 8 0)))
      (PRS 0x14d80 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI ARR HB AT TL IB BLO TC T0. unfold ListHead_entry.
    pose proof (munch_refl [(T + tl, T + tl + 1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (u8arr_bound rsegs _ _ _ ARR) as AB. pose proof (byte_range b) as BR.
    pose proof (u8arr_read rsegs _ A bs (T + tl - A) b (Z_to_bv 64 (T + tl)) ARR HB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    pose proof (u8arr_store_ok rsegs _ _ _ (T + tl - A)%Z (wa (T + tl)) ARR ltac:(lia) ltac:(f_equal; lia)) as SOK.
    zstep. zstep. zstep. step. ubr. zstep. zstep. zstep. step. ph_b2z. lit_branch. step. ubr.
    zstep. zstep. rewrite (le1_lit 0) by lia.
    pose proof (u8arr_write rsegs _ _ _ (T + tl - A)%Z (Z_to_bv 8 0) ARR ltac:(lia)) as ARR2.
    replace (A + (T + tl - A))%Z with (T + tl)%Z in ARR2 by lia. clear ARR RD. store_done.
    zstep. zstep. zstep. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ARR2.
  Qed.

  #[using="ws WSL"] Lemma ph_unk2 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' =>
        (r = 0 /\ ms' = PRS 0x14e00 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz 0) s6 (wz r) s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (r <> 0 /\ ms' = PRS 0x14dc0 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 (wz r) s9 t3 t4 t5 t6 gp tp F fc m))%Z
      (PRS 0x14db8 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. if_cases K; zify_cond K.
    - zstep. apply evt_done. left. split; [lia| reflexivity].
    - apply evt_done. right. split; [lia| reflexivity].
  Qed.

  #[using="QLO QP PHI ws WSL"] Lemma ph_unk3 : forall (A T tl h : Z) (bs : list byte) (b : byte) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u8arr rsegs m A bs -> (A <= T + tl)%Z -> (T + tl - A < Z.of_nat (length bs))%Z -> (A + Z.of_nat (length bs) <= lo)%Z ->
    (0 <= h < 2^64)%Z -> rw_cells rsegs m (q + 32) [C8 (wz T); C8 (wz tl)] -> (0 < T)%Z -> (0 <= tl)%Z ->
    evt rsegs (fun ms' => exists m',
        ms' = PRS (if h =? 0 then 0x14e7c else 0x14e30) x1 t0 t1 t2 (wz (T + tl)) (wz T) (wz 1) (wz 0) a4 a5 a6 a7 (wz h) s6 s7 (wz (-1)) t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(T + tl, T + tl + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ u8arr rsegs m' A (upd bs (Z.to_nat (T + tl - A)) b))
      (PRS 0x14e00 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz h) s6 s7 (wz (bv_unsigned b)) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI ARR AE IB BLO HR TC T0 TL.
    pose proof (munch_refl [(T + tl, T + tl + 1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (u8arr_bound rsegs _ _ _ ARR) as AB. pose proof (byte_range b) as BR.
    pose proof (u8arr_store_ok rsegs _ _ _ (T + tl - A)%Z (wa (T + tl)) ARR ltac:(lia) ltac:(f_equal; lia)) as SOK.
    zstep. zstep. zstep. step. ubr. zstep. zstep. zstep. step. ph_b2z. lit_branch. step. ubr.
    zstep. rewrite (le1_lit (bv_unsigned b)) by lia. rewrite Z_to_bv8_unsigned.
    pose proof (u8arr_write rsegs _ _ _ (T + tl - A)%Z b ARR ltac:(lia)) as ARR2.
    replace (A + (T + tl - A))%Z with (T + tl)%Z in ARR2 by lia. clear ARR. store_done.
    zstep. zstep. if_cases K; zify_cond K.
    - replace (h =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ARR2.
    - replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. exact ARR2.
  Qed.

  #[using="ws WSL"] Lemma ph_ex1 : forall (H l : Z) (hb : word) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 hb; C8 (wz l)] -> (0 <= l < 2^64)%Z -> (0 <= H /\ H + 88 < 2^64)%Z -> (H mod 8 = 0)%Z ->
    evt rsegs (fun ms' =>
        (l = 0 /\ ms' = PRS 0x14cd4 x1 t0 t1 t2 (wz l) a1 a2 a3 a4 a5 a6 a7 (wz H) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (l <> 0 /\ ms' = PRS membuffer_append_str_entry (wz 0x14e54) t0 t1 t2 (wz (H + 24)) (wz COMMA_ADDR) a2 a3 a4 a5 a6 a7 (wz (H + 24)) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m))%Z
      (PRS 0x14e30 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz H) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI HV LR HR H8. unfold membuffer_append_str_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. if_cases K; zify_cond K.
    - apply evt_done. left. split; [lia| reflexivity].
    - ub_align. zstep. zstep. zstep. zstep. zstep. apply evt_done. right. split; [lia| reflexivity].
  Qed.

  #[using="ws WSL"] Lemma ph_ex2 : forall (r1 V hb l : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz hb); C8 (wz l)] -> (0 <= l < 2^64)%Z -> (0 <= hb < 2^64)%Z -> (0 <= V < 2^64)%Z ->
    evt rsegs (fun ms' => ms' = PRS membuffer_append_entry (wz 0x14e68) t0 t1 t2 (wz V) (wz hb) (wz l) a3 a4 a5 a6 a7 (wz V) (wz r1) s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14e54 x1 t0 t1 t2 (wz r1) a1 a2 a3 a4 a5 a6 a7 (wz V) s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI HV LR HBR VR. unfold membuffer_append_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma ph_ex3 : forall (r1 r2 : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (r1 = 0 \/ r1 = -104)%Z -> (r2 = 0 \/ r2 = -104)%Z ->
    evt rsegs (fun ms' =>
        (r1 = 0 /\ r2 = 0 /\ ms' = PRS 0x14cd4 x1 t0 t1 t2 (wz r2) a1 a2 a3 a4 a5 a6 a7 s5 (wz r1) s7 s9 t3 t4 t5 t6 gp tp F fc m)
        \/ ((r1 = -104 \/ r2 = -104) /\ ms' = PRS 0x14f2c x1 t0 t1 t2 (wz r2) a1 a2 a3 a4 a5 a6 a7 s5 (wz r1) s7 s9 t3 t4 t5 t6 gp tp F fc m))%Z
      (PRS 0x14e68 x1 t0 t1 t2 (wz r2) a1 a2 a3 a4 a5 a6 a7 s5 (wz r1) s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros R1 R2. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct R1 as [-> | ->]; destruct R2 as [-> | ->].
    - zstep. lit_branch. zstep. lit_branch. apply evt_done. left. repeat split; reflexivity.
    - zstep. lit_branch. zstep. lit_branch. zstep. apply evt_done. right. split; [right; reflexivity| reflexivity].
    - zstep. lit_branch. apply evt_done. right. split; [left; reflexivity| reflexivity].
    - zstep. lit_branch. apply evt_done. right. split; [left; reflexivity| reflexivity].
  Qed.

  #[using="QLO QP PHI ws WSL"] Lemma ph_err : forall (err hack pos entp clen csz esp : Z) ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      x1 s5' s6' s7' s8' s9' s10' s11' (F : bvmap 5 word) fc m,
    stk rsegs m lo q -> mem_inv rsegs m -> rw_cells rsegs m (q + 136) (phFS ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) -> phFX m ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz esp) ->
    evt rsegs (fun ms' => exists m', ms' = MS (mkR ra (wz (q + 240)) gp tp t0 t1 t2 s0 s1 (wz 3) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom rsegs)
                          /\ munch [(P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                          /\ stk rsegs m' lo (q + 240) /\ rw_cells rsegs m' (P + 440) (p_ctl_cells 500 hack pos entp clen csz esp))
      (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
          F (wz 0x14f2c) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros ST MI FSH FX K5. unfold phFS in FSH. unfold p_ctl_cells in *.
    destruct FX as ([j0 Q0] & [ty Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & id & Q48) & [j68 Q68]).
    pose proof (munch_refl [(P + 440, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. sstep. zstep. zstep. zstep.
    eapply evt_cut. { eapply ph_epi; try eassumption. unfold phFX.
      split; [eexists; eassumption|]. split; [eexists; eassumption|]. split; [do 2 eexists; eassumption|].
      split; [do 2 eexists; eassumption|]. split; [do 2 eexists; eassumption| eexists; eassumption]. }
    cbv beta. intros ms' [-> ST']. apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  #[using="Type"] Lemma ph_new1 : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x180f0 (wz 0x14e84) t0 t1 t2 (wz 88) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14e7c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="QLO ws WSL"] Lemma ph_new2 : forall (H T tl hb l : Z) (junk : list byte) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz hb); C8 (wz l)] -> (0 <= l < 2^64)%Z -> (0 <= hb < 2^64)%Z ->
    (0 <= T < 2^64)%Z -> (0 <= tl < 2^64)%Z -> (0 <= H < 2^64)%Z -> rw_cells rsegs m (q + 32) [C8 (wz T); C8 (wz tl)] ->
    (H <> 0 -> rw_cells rsegs m H [CB 88 junk] /\ H mod 16 = 0 /\ H + 88 <= lo)%Z ->
    evt rsegs (fun ms' => exists m',
        (H = 0 /\ ms' = PRS 0x14f2c x1 t0 t1 t2 (wz H) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
        \/ (exists (hb' l' : Z) (j0 : list byte) t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6', H <> 0
             /\ ms' = PRS membuffer_assign_entry (wz 0x14ed8) t0' t1' t2' (wz (H + 56)) (wz T) (wz tl) a3' a4' a5' a6' a7' (wz H) (wz (H + 56)) (wz (H + 24)) s9 t3' t4' t5' t6' gp tp F fc m'
             /\ munch [(H + 24, H + 88); (q + 16, q + 32)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
             /\ rw_cells rsegs m' H [CB 24 j0] /\ rw_cells rsegs m' (H + 24) (mbuf_cells 0 0 0) /\ rw_cells rsegs m' (H + 56) (mbuf_cells 0 0 0)
             /\ rw_cells rsegs m' (q + 16) [C8 (wz hb'); C8 (wz l')]
             /\ ((l = 0 /\ hb' = ZERO_ADDR /\ l' = 1) \/ (l <> 0 /\ hb' = hb /\ l' = l))))%Z
      (PRS 0x14e84 x1 t0 t1 t2 (wz H) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI HV LR HBR TR TLR HR TC HB. unfold membuffer_assign_entry.
    pose proof (munch_refl [(H + 24, H + 88); (q + 16, q + 32)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - apply evt_done. exists m. left. split; [lia|]. split; [reflexivity| reflexivity].
    - destruct (HB ltac:(lia)) as (BLK & AL & BLO).
      assert (H8 : (H mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      splitcb BLK 0%nat [24; 32; 32]%nat. name_junk BLK. split_chunk BLK 1%nat B0 R1. split_chunk R1 1%nat B24 B56.
      replace (H + Z.of_nat 24)%Z with (H + 24)%Z in B24 by lia. replace (H + Z.of_nat 24 + Z.of_nat 32)%Z with (H + 56)%Z in B56 by lia.
      zstep. ub_align. zstep. zstep. zstep.
      call (membuffer_init_spec (H + 56)). all: side (first [exact B56| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
      rename MI0 into MI. rename POST into NBC. unfold mbuf_cells in NBC.
      replace (ret_pc (Z_to_bv 64 0x14ea0)) with (Z_to_bv 64 0x14ea0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep.
      call (membuffer_init_spec (H + 24)). all: side (first [exact B24| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
      rename MI0 into MI. rename POST into VBC. unfold mbuf_cells in VBC.
      replace (ret_pc (Z_to_bv 64 0x14eac)) with (Z_to_bv 64 0x14eac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. if_cases K2; zify_cond K2.
      +   zstep. zstep. zstep. zstep. apply evt_done. eexists. right.
        exists hb, l, jk. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [lia|]. split; [reflexivity|]. repeat (split; [eassumption|]). right. repeat split; lia.
      +   zstep. zstep. sstep. zstep. sstep. zstep. zstep. zstep. zstep. apply evt_done. eexists. right.
        exists ZERO_ADDR, 1, jk. repeat (lazymatch goal with |- ex _ => eexists end).
        split; [lia|]. split; [reflexivity|]. repeat (split; [eassumption|]). left. repeat split; lia.
  Qed.

  #[using="ws WSL"] Lemma ph_new5 : forall (r H hb l : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 16) [C8 (wz hb); C8 (wz l)] -> (0 <= l < 2^64)%Z -> (0 <= hb < 2^64)%Z ->
    (0 <= H /\ H + 88 < 2^64)%Z -> (r = 0 \/ r = -104)%Z ->
    evt rsegs (fun ms' =>
        (r <> 0 /\ ms' = PRS 0x14f14 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) s9 t3 t4 t5 t6 gp tp F fc m)
        \/ (r = 0 /\ ms' = PRS membuffer_assign_entry (wz 0x14eec) t0 t1 t2 (wz (H + 24)) (wz hb) (wz l) a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) s9 t3 t4 t5 t6 gp tp F fc m))%Z
      (PRS 0x14ed8 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI HV LR HBR HR RR. unfold membuffer_assign_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct RR as [-> | ->].
    - zstep. lit_branch. zstep. zstep. zstep. zstep. apply evt_done. right. split; [reflexivity| reflexivity].
    - zstep. lit_branch. apply evt_done. left. split; [lia| reflexivity].
  Qed.

  #[using="ws WSL"] Lemma ph_new6 : forall (r H nA nlen ncap id : Z) (j0 : list byte) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m H [CB 24 j0] -> rw_cells rsegs m (H + 56) (mbuf_cells nA nlen ncap) ->
    (0 <= nA < 2^64)%Z -> (0 <= nlen < 2^64)%Z -> (16 <= H /\ H + 88 <= lo)%Z -> (H mod 8 = 0)%Z -> (r = 0 \/ r = -104)%Z -> (-1 <= id < 64)%Z ->
    evt rsegs (fun ms' => exists m',
        (r <> 0 /\ ms' = PRS 0x14f14 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) (wz id) t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
        \/ (exists pad, r = 0 /\ ms' = PRS ListAddTail_entry (wz 0x14f10) t0 t1 t2 (wz L) (wz H) a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) (wz id) t3 t4 t5 t6 gp tp F fc m'
             /\ munch [(H, H + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
             /\ rw_cells rsegs m' H [C8 (wz nA); C8 (wz nlen); C4 (wz id); C4 pad]
             /\ rw_cells rsegs m' (H + 56) (mbuf_cells nA nlen ncap)))%Z
      (PRS 0x14eec x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) (wz id) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI HB NBC NAR NLR HR AL RR IDR. unfold ListAddTail_entry, mbuf_cells in *.
    pose proof (munch_refl [(H, H + 24)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct RR as [-> | ->].
    - zstep. lit_branch.
      splitcb HB 0%nat [8; 8; 4; 4]%nat. name_junk HB. recell HB 0%nat. recell HB 1%nat. recell HB 2%nat. recell HB 3%nat.
      zstep. zstep. sstep. sstep. sstep. zstep. zstep. zstep. apply evt_done. eexists. right. eexists. split; [reflexivity|]. split; [reflexivity|].
      repeat (split; [eassumption|]). eassumption.
    - zstep. lit_branch. apply evt_done. eexists. left. split; [lia|]. split; reflexivity.
  Qed.

  #[using="ws WSL"] Lemma ph_new7 : forall (r : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' => ms' = PRS (if r =? 0 then 0x14f14 else 0x14cd4) x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14f10 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros RR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K.
    - replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. reflexivity.
    - replace (r =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma ph_clean1 : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS membuffer_destroy_entry (wz 0x14f1c) t0 t1 t2 s7 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14f14 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof. intros until m. unfold membuffer_destroy_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. zstep. apply evt_done. reflexivity. Qed.
  #[using="Type"] Lemma ph_clean2 : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS membuffer_destroy_entry (wz 0x14f24) t0 t1 t2 s6 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14f1c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof. intros until m. unfold membuffer_destroy_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. zstep. apply evt_done. reflexivity. Qed.
  #[using="Type"] Lemma ph_clean3 : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS 0x17fb0 (wz 0x14f2c) t0 t1 t2 s5 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x14f24 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m).
  Proof. intros until m. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM. zstep. zstep. apply evt_done. reflexivity. Qed.
End SEGS.

