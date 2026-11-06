(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1009 of its 1131 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Segment A3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): cut Inv_B810c4 (v1.9 pc
   0x810c4) -> cut Inv_B81220 (0x81220): the frame header writes and the first 255 of the 392 shadow
   bytes of the side-stack frame area (plan-asan-ubsan 3.3, A3).
     810c4: sd   s9,336(s1)      (the frame base fr spilled to [A + 336])
     810ec: sd   a0,0(s9)        (the sink head word 0x41b58ab3)
     810f0: sd   a1,8(s9)        (the description word 0x17e9c)
     810f4: sd   a2,16(s9)       (the entry word 0x81018 = AF.ENTRY)
     810d4/810fc: srli s3,s9,3 ; add s3,s3,s10   (s3 = S(fr), the frame's shadow base)
     81100..8120c: 68 one-byte shadow stores sb s4/s5/a0,k(s3) (k = 0..67), the in-scope / out-of-scope marks
     8121c: jal  55144           (meta_fill_f8: the out[] shadow fill, 187 bytes from S(fr) + 68 to 0xf8)
   Every write of the run is the spill word [A + 336, A + 344), the frame header [fr, fr + 24) or a frame shadow
   byte in [S(fr), S(fr) + 392), so FRA is assembled at 0x81220 from the pre-frame state (PREF) with sl_fr_of. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Cells Step Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.

(* ---- The image's read-only addresses all lie below GT (the end of its writable data), so no store of this
   segment (frame, spill, shadow) can touch one: ro_agree survives every write. ---- *)
Definition a3_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma a3_find_below : forall segs top x n s,
  a3_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold a3_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma a3_tops_GT : a3_tops rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a3_ro_below : forall x, LM.ro_addr rsegs x = true -> bv_unsigned x < AC.GT.
Proof.
  intros x H. unfold LM.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate H].
  destruct (a3_find_below rsegs AC.GT (bv_unsigned x) 1 s a3_tops_GT E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

Lemma a3_ro_write : forall (m : word -> option byte) (a : Z) (bs : list byte),
  ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> AC.GT <= a ->
  ro_agree rsegs (write_to_mem m (LM.wa a) bs).
Proof.
  intros m a bs HRO Ha Hl HG x Hx.
  pose proof (a3_ro_below x Hx) as Hlt.
  unfold LM.mrd. rewrite (LM.write_to_mem_spec bs m a x Ha Hl).
  destruct (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + Z.of_nat (length bs)))%bool eqn:E.
  - exfalso. apply andb_prop in E as [E1 _]. apply Z.leb_le in E1. lia.
  - exact (HRO x Hx).
Qed.

Lemma a3_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- The library engine's run (the callee contracts) lifts into the UL engine: the two msteps are the same
   relation on the same step function. ---- *)
Lemma a3_lib_msteps : forall s s', LE.msteps rsegs s s' -> msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [exact Hs | exact IH].
Qed.

Lemma a3_lib_evt : forall Q s, LE.evt rsegs Q s -> evt rsegs Q s.
Proof. intros Q s (s' & H & HQ). exists s'. split; [exact (a3_lib_msteps _ _ H) | exact HQ]. Qed.

(* ---- Shadow-byte bookkeeping along the 68 one-byte stores and the fill call. ---- *)
Definition a3_J (m0 : word -> option byte) (Sh : Z) (m : word -> option byte) : Prop :=
  munch [(Sh, Sh + 392)] m0 m /\ wmono rsegs m0 m /\ shadow_rw m /\ ro_agree rsegs m.

Lemma a3_J_init : forall m Sh, shadow_rw m -> ro_agree rsegs m -> a3_J m Sh m.
Proof.
  intros m Sh HSW HRO. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; assumption.
Qed.

Lemma a3_in_sh : forall Sh x, (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) -> Sh <= x < Sh + 392 ->
  in_shadow x.
Proof. intros Sh x H Hx. replace x with (Sh + (x - Sh)) by lia. apply H. lia. Qed.

Lemma a3_J_store_ok : forall m0 Sh m a, a3_J m0 Sh m -> in_shadow a -> store_ok rsegs m (LM.wa a) 1 = true.
Proof.
  intros m0 Sh m a (_ & _ & HSW & _) Ha.
  pose proof (in_shadow_range a Ha) as Hr.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (HSW a Ha)). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma a3_J_store : forall m0 Sh m a bs, a3_J m0 Sh m -> Sh <= a < Sh + 392 -> in_shadow a ->
  length bs = 1%nat -> a3_J m0 Sh (write_to_mem m (LM.wa a) bs).
Proof.
  intros m0 Sh m a bs HJ Hin Ha Hl.
  pose proof (in_shadow_range a Ha) as Hr.
  pose proof (a3_J_store_ok m0 Sh m a HJ Ha) as HS.
  destruct HJ as (MU & WM & HSW & HRO).
  assert (HGT : AC.GT <= a).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AC.GT in Ha |- *. lia. }
  split; [|split; [|split]].
  - apply munch_write; [exact MU | lia | rewrite Hl; lia | rewrite Hl; cbn [inside]; left; lia].
  - apply wmono_write. exact WM.
  - intros x Hx. pose proof (in_shadow_range x Hx) as Hxr. split.
    + apply wview_write_mono. exact (proj1 (HSW x Hx)).
    + unfold LM.mrd. rewrite (LM.write_to_mem_spec bs m a (LM.wa x)) by (rewrite ?Hl; lia).
      rewrite LM.wa_unsigned by lia.
      destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:E.
      * apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. rewrite Hl in E2.
        assert (x = a) by lia. subst x. rewrite Z.sub_diag.
        destruct bs as [|b [|b1 bs']]; cbn in Hl; try discriminate. exists b. reflexivity.
      * destruct (proj2 (HSW x Hx)) as (b & Hb). unfold LM.mrd in Hb. exists b. exact Hb.
  - apply a3_ro_write; [exact HRO | lia | rewrite Hl; lia | exact HGT].
Qed.

(* n bytes from a, all shadow bytes of a memory with shadow_rw, are present. *)
Lemma a3_sh_bytes : forall m a (n : nat), shadow_rw m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists sh, bytes_at rsegs m a sh /\ length sh = n.
Proof.
  intros m a n HSW HS Ha Hn.
  exists (map (fun i : nat => match mrd rsegs m (wa (a + Z.of_nat i)) with
                              | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  assert (HL : length (map (fun i : nat => match mrd rsegs m (wa (a + Z.of_nat i)) with
                                           | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)) = n)
    by (rewrite length_map, length_seq; reflexivity).
  split; [|exact HL].
  unfold bytes_at. split; [exact Ha|]. split; [rewrite HL; exact Hn|].
  intros i Hi. rewrite HL in Hi.
  rewrite nth_error_map.
  rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
  destruct (HSW (a + Z.of_nat i) (HS (Z.of_nat i) ltac:(lia))) as (_ & b & Hb).
  assert (Hb' : mrd rsegs m (wa (a + Z.of_nat i)) = Some b) by exact Hb.
  rewrite Hb'. reflexivity.
Qed.

(* and as one writable library cell, the destination form of the fill contract. *)
Lemma a3_rw_of_shadow : forall m a (n : nat), shadow_rw m ->
  (forall i, 0 <= i < Z.of_nat n -> in_shadow (a + i)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  exists junk, LSt.rw_cells rsegs m a [LC.CB n junk].
Proof.
  intros m a n HSW HS Ha Hn.
  destruct (a3_sh_bytes m a n HSW HS Ha Hn) as (sh & Hb & Hl).
  exists sh. split; [split|].
  - cbn [LC.cells_wf LC.cell_wf]. split; [exact Hl | exact I].
  - cbn [LC.cells_bytes LC.cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [LC.cells_size LC.csize]. rewrite Nat.add_0_r. split; [exact Ha|]. split; [exact Hn|].
    intros i Hi. exact (proj1 (HSW (a + i) (HS i Hi))).
Qed.

(* shadow_rw across the fill call: it writes [Q, Q + N) and leaves those N bytes present. *)
Lemma a3_shadow_rw_call : forall m m' Q N bs, shadow_rw m -> munch [(Q, Q + N)] m m' -> wmono rsegs m m' ->
  LSt.rw_cells rsegs m' Q [LC.CB (Z.to_nat N) bs] -> 0 <= N -> shadow_rw m'.
Proof.
  intros m m' Q N bs HSW MU WM RW HN x Hx. pose proof (in_shadow_range x Hx) as Hxr.
  split; [exact (WM (LM.wa x) (proj1 (HSW x Hx)))|].
  destruct RW as ((Hwf & Hb) & _). cbn [LC.cells_wf LC.cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [LC.cells_bytes LC.cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct (Z.lt_ge_cases x Q) as [Hlt|Hge]; [|destruct (Z.lt_ge_cases x (Q + N)) as [Hlt2|Hge2]].
  - destruct (proj2 (HSW x Hx)) as (b & Hb0). exists b. unfold LM.mrd in *. rewrite MU; [exact Hb0|].
    rewrite LM.wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
  - destruct Hb as (HQ0 & _ & Hb).
    assert (Hi : (Z.to_nat (x - Q) < length bs)%nat) by (rewrite Hl; lia).
    pose proof (Hb _ Hi) as E. rewrite Z2Nat.id in E by lia. replace (Q + (x - Q)) with x in E by lia.
    destruct (nth_error bs (Z.to_nat (x - Q))) as [b|] eqn:En; [exists b; exact E|].
    apply nth_error_None in En. lia.
  - destruct (proj2 (HSW x Hx)) as (b & Hb0). exists b. unfold LM.mrd in *. rewrite MU; [exact Hb0|].
    rewrite LM.wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* The normalized memory the callee contract runs on keeps the shadow cells and the runtime cells. *)
Lemma a3_sh_norm : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m HRO HSW x Hx.
  pose proof (in_shadow_range x Hx) as Hr.
  assert (Hro : LM.ro_addr rsegs (LM.wa x) = false).
  { destruct (LM.ro_addr rsegs (LM.wa x)) eqn:E; [|reflexivity].
    exfalso. pose proof (a3_ro_below _ E) as Hlt. rewrite LM.wa_unsigned in Hlt by lia.
    unfold AC.GT in Hlt.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx. lia. }
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  destruct (HSW x Hx) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) (LM.wa x) REL Hro). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) (LM.wa x) REL). exact Hb.
Qed.

Lemma a3_asan_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in H |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  repeat (split; [apply bytes_at_normalize; assumption|]).
  apply bytes_at_normalize; assumption.
Qed.

Ltac a3_keep_one MU Hout :=
  eapply fl_bytes;
  [ eassumption | exact MU |
    intros x Hx; apply Hout; revert Hx;
    rewrite ?length_le8, ?length_le4; cbn [length];
    unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND,
           GOT_HIEND, MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET,
           GOT_REAL_MEMSET, AC.GT; lia ].

(* The runtime cells sit below GT, so a write above GT keeps them. *)
Lemma a3_asan_keep : forall W m m', asan_cells m -> munch W m m' ->
  (forall x, 0 <= x < AC.GT -> outside W x) -> asan_cells m'.
Proof.
  intros W m m' H MU Hout. unfold asan_cells in H |- *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17).
  repeat (split; [solve [a3_keep_one MU Hout]|]).
  a3_keep_one MU Hout.
Qed.

Lemma a3_rw_rel : forall m m0 a n bs, mem_rel rsegs m m0 ->
  LSt.rw_cells rsegs m0 a [LC.CB n bs] -> LSt.rw_cells rsegs m a [LC.CB n bs].
Proof.
  intros m m0 a n bs REL ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ REL) Hb).
  - exact (wr_at_rel rsegs m m0 a _ REL Hw).
Qed.

(* mkR_of made concrete, so that the run lemmas' register file is the engine's mkR. *)
Lemma a3_mkR_of : forall regs, Regs6ss.mkR_of regs = mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
  (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
  (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
  (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma a3_store_ok_at : forall m a n k (j : nat) b,
  wr_at rsegs m a n -> 0 <= k -> k + Z.of_nat j <= n -> b = a + k ->
  store_ok rsegs m (wa b) j = true.
Proof. intros m a n k j b H Hk Hj ->. exact (wr_at_store_ok rsegs m a n k j H Hk Hj). Qed.

(* One frame-shadow store `sb r,k(s3)` (s3 = Sh): store_ok from the invariant, one step, the invariant again. *)
Ltac a3_sb Sh k :=
  lazymatch goal with
  | HJ : a3_J ?m0 Sh ?mc, HSH : forall i, 0 <= i < 392 -> in_shadow (Sh + i) |- _ =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mc (wa (Sh + k)) 1 = true)
        by (exact (a3_J_store_ok m0 Sh mc (Sh + k) HJ (HSH k ltac:(lia))));
      step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?aa ?bb) _) =>
          let HJ' := fresh "HJn" in
          assert (HJ' : a3_J m0 Sh (write_to_mem mc aa bb))
            by (apply (a3_J_store m0 Sh mc (Sh + k) bb HJ);
                [ lia | exact (HSH k ltac:(lia))
                | first [ reflexivity | apply length_le1 | apply length_Z_to_le_bytes ] ]);
          clear HS; clear HJ;
          let m' := fresh "mc" in
          set (m' := write_to_mem mc aa bb) in *; clearbody m'
      end
  end.

(* ---- The run from 0x81100 (the first shadow store) to the return at 0x81220. ---- *)
Lemma a3_evt_mid : SS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh : Z),
    s3 = Z_to_bv 64 Sh -> s4 = Z_to_bv 64 (-8) -> s5 = Z_to_bv 64 (-14) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sh + i)) ->
    shadow_rw m -> ro_agree rsegs m -> asan_cells m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81220) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 Sh /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sh + 68) /\
         munch [(Sh, Sh + 392)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81100) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh -> -> -> HSH HSW HRO HAC.
  unfold SS.asan_set_shadow_f8_contract, SS.asan_set_shadow_contract, SS.ASAN_SET_SHADOW_F8 in SET.
  cbv zeta in SET.
  pose proof (HSH 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HSH 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sh)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sh + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  assert (HGT : AC.GT <= Sh) by (unfold AC.GT, LOWMEM_END in *; lia).
  (* numeric forms, so that the bound side conditions below are plain arithmetic *)
  unfold LOWMEM_END in HSlo. unfold HIGHMEM_BEG in HShi. unfold AC.GT in HGT.
  pose proof (a3_J_init m Sh HSW HRO) as HJ.
  (* the 68 frame-shadow stores *)
  a3_sb Sh 4. a3_sb Sh 5. a3_sb Sh 6. a3_sb Sh 7.
  a3_sb Sh 0. a3_sb Sh 1. a3_sb Sh 2. a3_sb Sh 3.
  a3_sb Sh 12. a3_sb Sh 13. a3_sb Sh 14. a3_sb Sh 15.
  a3_sb Sh 8. a3_sb Sh 9. a3_sb Sh 10. a3_sb Sh 11.
  a3_sb Sh 20. a3_sb Sh 21. a3_sb Sh 22. a3_sb Sh 23.
  a3_sb Sh 16. a3_sb Sh 17. a3_sb Sh 18. a3_sb Sh 19.
  a3_sb Sh 28. a3_sb Sh 29. a3_sb Sh 30. a3_sb Sh 31.
  a3_sb Sh 24. a3_sb Sh 25. a3_sb Sh 26. a3_sb Sh 27.
  a3_sb Sh 36. a3_sb Sh 37. a3_sb Sh 38. a3_sb Sh 39.
  a3_sb Sh 32. a3_sb Sh 33. a3_sb Sh 34. a3_sb Sh 35.
  a3_sb Sh 44. a3_sb Sh 45. a3_sb Sh 46. a3_sb Sh 47.
  a3_sb Sh 40. a3_sb Sh 41. a3_sb Sh 42. a3_sb Sh 43.
  a3_sb Sh 52. a3_sb Sh 53. a3_sb Sh 54. a3_sb Sh 55.
  a3_sb Sh 48. a3_sb Sh 49. a3_sb Sh 50. a3_sb Sh 51.
  a3_sb Sh 60. a3_sb Sh 61. a3_sb Sh 62. a3_sb Sh 63.
  a3_sb Sh 56. a3_sb Sh 57. a3_sb Sh 58. a3_sb Sh 59.
  a3_sb Sh 64. a3_sb Sh 65. a3_sb Sh 66. a3_sb Sh 67.
  (* 0x81210..0x8121c: addi s11,s3,68 ; li a1,187 ; mv a0,s11 ; jal 55144 *)
  step. step. step.
  step.
  lazymatch goal with
  | HJ : a3_J m Sh ?mcx |- _ => pose proof HJ as HJf; set (mf := mcx) in *
  end.
  pose proof HJf as (MUc & WMc & SWc & ROc).
  assert (ACc : asan_cells mf)
    by (apply (a3_asan_keep [(Sh, Sh + 392)] m mf HAC MUc);
        intros x Hx; cbn [outside]; split; [unfold AC.GT in *; lia | exact I]).
  eapply evt_cut.
  - apply a3_lib_evt.
    eapply (MemNorm.evt_normalize rsegs _ _ F _ fc None mf (seg_rom rsegs) a3_wx ROc).
    destruct (a3_rw_of_shadow (normalize rsegs mf) (Sh + 68) (Z.to_nat 187) (a3_sh_norm mf ROc SWc)
                ltac:(intros i Hi; apply (a3_in_sh Sh _ HSH); lia) ltac:(lia) ltac:(lia)) as (junk & RWj).
    eapply SET with (junk := junk).
    + rewrite !MState.unsigned_lit by lia.
      intros i Hi. apply (a3_in_sh Sh _ HSH). lia.
    + rewrite !MState.unsigned_lit by lia. exact RWj.
    + exact (a3_asan_norm mf ROc ACc).
    + exact (mem_inv_normalize rsegs mf).
  -
  intros ms' (s0' & HQ & REL & SAME).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E0 & MU & WM & MI & RW).
  destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  subst s0'.
  cbn [LMS.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]
    in E1, E2, E3, E4, E5, E6, E7, E8.
  rewrite !MState.unsigned_lit in MU, RW by lia.
  rewrite (LMS.ret_pc_even 0x81220 ltac:(lia) ltac:(reflexivity)) in E3.
  apply evt_done.
  assert (Ems : ms' = MS (ms_regs ms') F (Z_to_bv 64 0x81220) fc None (ms_mem ms') (seg_rom rsegs)).
  { destruct ms' as [R' F' pcv' svc' rv' fc' mm' ro'];
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom]
      in E1, E2, E3, E4, E5, E6, E7 |- *;
    subst; reflexivity. }
  (* the memory of the callee's run, moved back off the normalized memory *)
  assert (MU' : munch [(Sh + 68, Sh + 68 + 187)] mf (ms_mem ms')).
  { eapply (munch_rel rsegs [(Sh + 68, Sh + 68 + 187)] mf (normalize rsegs mf) (ms_mem ms') m0');
      [ apply mem_rel_normalize; exact ROc | exact E8 | exact SAME | exact MU ]. }
  assert (WM' : wmono rsegs mf (ms_mem ms')).
  { eapply (wmono_rel rsegs mf (normalize rsegs mf) (ms_mem ms') m0');
      [ apply mem_rel_normalize; exact ROc | exact E8 | exact SAME | exact WM ]. }
  assert (RO' : ro_agree rsegs (ms_mem ms')) by exact (ro_agree_same rsegs mf (ms_mem ms') ROc SAME).
  assert (RW' : LSt.rw_cells rsegs (ms_mem ms') (Sh + 68)
                  [LC.CB (Z.to_nat 187) (repeat (Z_to_bv 8 248) (Z.to_nat 187))])
    by exact (a3_rw_rel (ms_mem ms') m0' (Sh + 68) (Z.to_nat 187) _ E8 RW).
  assert (SW' : shadow_rw (ms_mem ms'))
    by exact (a3_shadow_rw_call mf (ms_mem ms') (Sh + 68) 187 _ SWc MU' WM' RW' ltac:(lia)).
  exists (ms_regs ms'), (ms_mem ms').
  split; [exact Ems|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split; [rewrite E1; reflexivity|].
  split.
  { eapply munch_trans; [exact MUc|].
    eapply (munch_weaken [(Sh + 68, Sh + 68 + 187)] [(Sh, Sh + 392)]); [| exact MU'].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m mf (ms_mem ms') WMc WM')|].
  split; [exact RO' | exact SW'].
Qed.

(* An application-memory write (the spill word, the frame header) keeps every shadow cell. *)
Lemma a3_sh_app_write : forall m a bs, shadow_rw m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ in_shadow x) ->
  shadow_rw (write_to_mem m (LM.wa a) bs).
Proof.
  intros m a bs HSW Ha Hl Hns x Hx.
  pose proof (in_shadow_range x Hx) as Hr.
  destruct (HSW x Hx) as (Hw & b & Hb). split.
  - apply wview_write_mono. exact Hw.
  - exists b. unfold LM.mrd in *.
    rewrite (LM.write_to_mem_spec bs m a (LM.wa x) Ha Hl).
    rewrite LM.wa_unsigned by lia.
    destruct (Z.leb a x && Z.ltb x (a + Z.of_nat (length bs)))%bool eqn:E.
    + exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      exact (Hns x ltac:(lia) Hx).
    + exact Hb.
Qed.

(* ---- The whole segment run: 0x810c4 (the spill of the frame base) to the return at 0x81220. ---- *)
Lemma a3_evt : SS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr : Z),
    s1 = Z_to_bv 64 A -> s9 = Z_to_bv 64 fr -> s10 = Z_to_bv 64 ASAN_K ->
    AC.GT <= fr -> fr + 3136 <= A -> HIGHMEM_BEG <= A -> A + 344 <= 2 ^ 64 ->
    (fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
    (forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)) ->
    wr_at rsegs m fr 24 -> wr_at rsegs m (A + 336) 8 ->
    shadow_rw m -> ro_agree rsegs m -> asan_cells m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81220) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 20 = Z_to_bv 64 (-8) /\
         getr R 21 = Z_to_bv 64 (-14) /\ getr R 22 = s6 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 (Sfr fr + 68) /\
         munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\
         q64 m' (A + 336) fr /\ q64 m' fr 0x41b58ab3 /\ q64 m' (fr + 8) 0x17e9c /\ q64 m' (fr + 16) AF.ENTRY)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x810c4) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr -> -> -> HfrGT HfrA HAhi HA64 Hfrsep HSH HWh HWs HSW HRO HAC.
  pose proof (HSH 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HSH 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sfr fr + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  unfold LOWMEM_END in HSlo, Hfrsep. unfold HIGHMEM_BEG in HShi, HAhi, Hfrsep. unfold AC.GT in HfrGT.
  assert (Hsh_app : forall x, in_shadow x -> 2147450880 <= x /\ x < 17594333495296)
    by (intros x Hx; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx; lia).
  (* 0x810c4: sd s9,336(s1) -- the frame base spilled to [A + 336] *)
  assert (HS1 : store_ok rsegs m (wa (A + 336)) 8 = true)
    by (eapply (a3_store_ok_at m (A + 336) 8 0 8%nat); [exact HWs | lia | cbn; lia | lia]).
  step.
  set (m1 := write_to_mem m (Z_to_bv 64 (A + 336)) (le8 (Z_to_bv 64 fr))) in *.
  assert (MU1 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m1).
  { unfold m1. apply munch_write;
      [apply munch_refl | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; left; lia]. }
  assert (WM1 : wmono rsegs m m1) by (unfold m1; apply wmono_write, wmono_refl).
  assert (RO1 : ro_agree rsegs m1)
    by (unfold m1; apply a3_ro_write; [exact HRO | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (SW1 : shadow_rw m1).
  { unfold m1. apply a3_sh_app_write; [exact HSW | lia | rewrite length_le8; lia|].
    rewrite length_le8. intros x Hx Hin. destruct (Hsh_app x Hin). lia. }
  assert (Q336 : q64 m1 (A + 336) fr)
    by (unfold q64, m1; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh1 : wr_at rsegs m1 fr 24) by (unfold m1; apply wr_at_write; exact HWh).
  clearbody m1. clear HS1.
  (* the nine register instructions 0x810c8-0x810e8 *)
  do 9 step.
  (* 0x810ec: sd a0,0(s9) -- the sink head word *)
  assert (HS2 : store_ok rsegs m1 (wa fr) 8 = true)
    by (eapply (a3_store_ok_at m1 fr 24 0 8%nat); [exact HWh1 | lia | cbn; lia | lia]).
  step.
  set (m2 := write_to_mem m1 (Z_to_bv 64 fr) (le8 (Z_to_bv 64 1102416563))) in *.
  assert (MU2 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m2).
  { unfold m2. apply munch_write;
      [exact MU1 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM2 : wmono rsegs m m2) by (unfold m2; apply wmono_write, WM1).
  assert (RO2 : ro_agree rsegs m2)
    by (unfold m2; apply a3_ro_write; [exact RO1 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (SW2 : shadow_rw m2).
  { unfold m2. apply a3_sh_app_write; [exact SW1 | lia | rewrite length_le8; lia|].
    rewrite length_le8. intros x Hx Hin. destruct (Hsh_app x Hin). lia. }
  assert (Q336b : q64 m2 (A + 336) fr).
  { unfold q64, m2. apply bytes_at_write_other;
      [exact Q336 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0 : q64 m2 fr 0x41b58ab3)
    by (unfold q64, m2; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh2 : wr_at rsegs m2 fr 24) by (unfold m2; apply wr_at_write; exact HWh1).
  clearbody m2. clear HS2.
  (* 0x810f0: sd a1,8(s9) -- the description word *)
  assert (HS3 : store_ok rsegs m2 (wa (fr + 8)) 8 = true)
    by (eapply (a3_store_ok_at m2 fr 24 8 8%nat); [exact HWh2 | lia | cbn; lia | lia]).
  step.
  set (m3 := write_to_mem m2 (Z_to_bv 64 (fr + 8)) (le8 (Z_to_bv 64 97948))) in *.
  assert (MU3 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m3).
  { unfold m3. apply munch_write;
      [exact MU2 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM3 : wmono rsegs m m3) by (unfold m3; apply wmono_write, WM2).
  assert (RO3 : ro_agree rsegs m3)
    by (unfold m3; apply a3_ro_write; [exact RO2 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (SW3 : shadow_rw m3).
  { unfold m3. apply a3_sh_app_write; [exact SW2 | lia | rewrite length_le8; lia|].
    rewrite length_le8. intros x Hx Hin. destruct (Hsh_app x Hin). lia. }
  assert (Q336c : q64 m3 (A + 336) fr).
  { unfold q64, m3. apply bytes_at_write_other;
      [exact Q336b | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0b : q64 m3 fr 0x41b58ab3).
  { unfold q64, m3. apply bytes_at_write_other;
      [exact Qh0 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh8 : q64 m3 (fr + 8) 0x17e9c)
    by (unfold q64, m3; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (HWh3 : wr_at rsegs m3 fr 24) by (unfold m3; apply wr_at_write; exact HWh2).
  clearbody m3. clear HS3.
  (* 0x810f4: sd a2,16(s9) -- the entry word *)
  assert (HS4 : store_ok rsegs m3 (wa (fr + 16)) 8 = true)
    by (eapply (a3_store_ok_at m3 fr 24 16 8%nat); [exact HWh3 | lia | cbn; lia | lia]).
  step.
  set (m4 := write_to_mem m3 (Z_to_bv 64 (fr + 16)) (le8 (Z_to_bv 64 528408))) in *.
  assert (MU4 : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m4).
  { unfold m4. apply munch_write;
      [exact MU3 | lia | rewrite length_le8; lia | rewrite length_le8; cbn [inside]; right; left; lia]. }
  assert (WM4 : wmono rsegs m m4) by (unfold m4; apply wmono_write, WM3).
  assert (RO4 : ro_agree rsegs m4)
    by (unfold m4; apply a3_ro_write; [exact RO3 | lia | rewrite length_le8; lia | unfold AC.GT; lia]).
  assert (SW4 : shadow_rw m4).
  { unfold m4. apply a3_sh_app_write; [exact SW3 | lia | rewrite length_le8; lia|].
    rewrite length_le8. intros x Hx Hin. destruct (Hsh_app x Hin). lia. }
  assert (Q336d : q64 m4 (A + 336) fr).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Q336c | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh0c : q64 m4 fr 0x41b58ab3).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Qh0b | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh8b : q64 m4 (fr + 8) 0x17e9c).
  { unfold q64, m4. apply bytes_at_write_other;
      [exact Qh8 | lia | rewrite length_le8; lia | rewrite !length_le8; lia]. }
  assert (Qh16 : q64 m4 (fr + 16) AF.ENTRY)
    by (unfold q64, m4, AF.ENTRY; apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (AC4 : asan_cells m4).
  { apply (a3_asan_keep [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m m4 HAC MU4).
    intros x Hx. cbn [outside]. unfold AC.GT in Hx.
    split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  clearbody m4. clear HS4.
  (* 0x810f8: li a0,-15 ; 0x810fc: add s3,s3,s10 (s3 = S(fr)) *)
  step. step.
  eapply evt_cut.
  - eapply (a3_evt_mid SET) with (Sh := Sfr fr).
    + rewrite !MState.unsigned_lit by (try unfold ASAN_K; lia).
      rewrite Z.shiftr_div_pow2 by lia. unfold Sfr, shadow_addr. reflexivity.
    + reflexivity.
    + reflexivity.
    + exact HSH.
    + exact SW4.
    + exact RO4.
    + exact AC4.
  - intros ms' (R & m' & Ems & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G24 & G25 & G26 & G27 &
                MUm & WMm & ROm & SWm).
    apply evt_done.
    assert (MUw : munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] m4 m').
    { eapply (munch_weaken [(Sfr fr, Sfr fr + 392)]); [| exact MUm].
      unfold sub_fp. cbn [outside]. intros x (_ & _ & Hx & _). split; [exact Hx | exact I]. }
    exists R, m'.
    split; [exact Ems|].
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G9|].
    split; [exact G18|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21|]. split; [exact G22|].
    split; [exact G24|]. split; [exact G25|]. split; [exact G26|]. split; [exact G27|].
    split; [exact (munch_trans _ m m4 m' MU4 MUw)|].
    split; [exact (wmono_trans rsegs m m4 m' WM4 WMm)|].
    split; [exact ROm|].
    split; [exact SWm|].
    split.
    { unfold q64 in Q336d |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Q336d | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    split.
    { unfold q64 in Qh0c |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh0c | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    split.
    { unfold q64 in Qh8b |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh8b | exact MUm|].
      rewrite length_le8. intros x Hx. split; [lia | exact I]. }
    { unfold q64 in Qh16 |- *.
      eapply (fl_bytes [(Sfr fr, Sfr fr + 392)] m4 m'); [exact Qh16 | exact MUm|].
      rewrite length_le8. intros x Hx. split; [unfold AF.ENTRY in Hx; lia | exact I]. }
Qed.

(* ---- Helpers for the cut-level lemma. ---- *)

(* No address of the image's registered globals reaches GT. *)
Lemma a3_AG_below : forall a, in_globals AF.frame_AG a -> a < AC.GT.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hb : forallb (fun p => Z.ltb (fst p + snd p) AC.GT) AF.frame_AG = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb _ Hin). cbn [fst snd] in Hb. apply Z.ltb_lt in Hb. lia.
Qed.

(* An address is in one of the segment's three written ranges, or outside all of them. *)
Lemma a3_split3 : forall lo1 hi1 lo2 hi2 lo3 hi3 x,
  (lo1 <= x < hi1) \/ (lo2 <= x < hi2) \/ (lo3 <= x < hi3) \/
  outside [(lo1, hi1); (lo2, hi2); (lo3, hi3)] x.
Proof.
  intros lo1 hi1 lo2 hi2 lo3 hi3 x.
  destruct (Z_le_gt_dec lo1 x) as [P1|P1]; destruct (Z_lt_ge_dec x hi1) as [Q1|Q1];
  destruct (Z_le_gt_dec lo2 x) as [P2|P2]; destruct (Z_lt_ge_dec x hi2) as [Q2|Q2];
  destruct (Z_le_gt_dec lo3 x) as [P3|P3]; destruct (Z_lt_ge_dec x hi3) as [Q3|Q3];
  try (left; lia); try (right; left; lia); try (right; right; left; lia);
  (right; right; right; cbn [outside]; split; [lia|]; split; [lia|]; split; [lia | exact I]).
Qed.

(* The frame-shadow byte x is the shadow byte of the frame byte fr + 8 (x - S(fr)). *)
Lemma a3_sfr_shadow : forall fr x, x = shadow_addr (fr + 8 * (x - Sfr fr)).
Proof.
  intros fr x. unfold Sfr, shadow_addr.
  replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with (fr + (x - (fr / 8 + ASAN_K)) * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* Two word_mem values at the same address agree modulo 2^64. *)
Lemma a3_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864). *)
Lemma a3_fs_meta_range : forall FS q, Tac_fs.fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (Tac_fs.fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (Tac_fs.a_fs_flag_range FS c j Hc Hj)).
Qed.

(* Above GT the image has no bytes, so a present read is a present raw byte. *)
Lemma a3_seg_rom_none : forall x, AC.GT <= x -> x < 2 ^ 64 -> LP.seg_rom rsegs (LM.wa x) = None.
Proof.
  intros x H1 H2. assert (H1' : 6283264 <= x) by (unfold AC.GT in H1; lia).
  apply seg_rom_unmapped.
  destruct (find_segment rsegs (bv_unsigned (LM.wa x)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (a3_find_below rsegs AC.GT (bv_unsigned (LM.wa x)) 1 s a3_tops_GT E ltac:(lia)) as [L|L];
    [rewrite LM.wa_unsigned in L by lia; unfold AC.GT in L; lia | discriminate L].
Qed.

Lemma a3_raw_of_mrd : forall m x b, AC.GT <= x -> x < 2 ^ 64 -> LM.mrd rsegs m (LM.wa x) = Some b ->
  m (LM.wa x) = Some b.
Proof.
  intros m x b H1 H2 H. unfold LM.mrd in H. destruct (m (LM.wa x)) as [c|] eqn:E; [exact H|].
  rewrite (a3_seg_rom_none x H1 H2) in H. discriminate H.
Qed.

(* and the bytes of a stored word are present. *)
Lemma a3_raw_of_q64 : forall m a v x, q64 m a v -> AC.GT <= a -> a + 8 <= 2 ^ 64 -> a <= x < a + 8 ->
  exists b, m (LM.wa x) = Some b.
Proof.
  intros m a v x (H0 & H1 & H) Ha Ha8 Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(rewrite length_le8; lia)) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error (LM.le8 (Z_to_bv 64 v)) (Z.to_nat (x - a))) as [b|] eqn:N.
  - exists b. apply (a3_raw_of_mrd m x b ltac:(lia) ltac:(lia) E).
  - exfalso. apply nth_error_None in N. rewrite length_le8 in N. lia.
Qed.

Lemma a3_mbyte_of_q64 : forall m a v x, q64 m a v -> a <= x < a + 8 -> exists b, mbyte rsegs m x = Some b.
Proof.
  intros m a v x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - a)) ltac:(rewrite length_le8; lia)) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error (LM.le8 (Z_to_bv 64 v)) (Z.to_nat (x - a))) as [b|] eqn:N.
  - exists b. exact E.
  - exfalso. apply nth_error_None in N. rewrite length_le8 in N. lia.
Qed.

(* A byte off the frame has its shadow byte off the frame's 392 (the frame covers whole granules). *)
Lemma a3_shadow_off : forall fr b, fr mod 8 = 0 -> 0 <= fr -> 0 <= b -> ~ (fr <= b < fr + 3136) ->
  ~ (Sfr fr <= shadow_addr b < Sfr fr + 392).
Proof.
  intros fr b Hfr8 Hfr0 Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- The segment lemma: the A3 cut (v1.9 pc 0x810c4) reaches the first FRA cut (v1.9 pc 0x81220). ---- *)
Section A3seg.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* meta_fill_f8 (0x55144): the out[] shadow fill, proved in lib/B/Prog/asan_set_shadow.v. *)
Hypothesis SHf8 : SS.asan_set_shadow_f8_contract.

(* FSREC across a run whose writes miss every app byte below stklo outside the frame [fr, fr + 3136): the tp word
   is in the image (below GT), the class-6 flag byte fs_flag FS 6 j = FS + 36352 + j lies below the frame
   (fr = FS + 6328320 + j * 4096) and the slot's last word fr + 4088 lies above it, both in the FakeStack, which
   a_laws_fs_place puts in app memory below stklo. *)
Lemma a3_fsrec_keep : forall hb mem mem' md W fr,
  FSREC fr mem ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) hb mem md ->
  munch W mem mem' ->
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr <= x < fr + 3136) -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros hb mem mem' md W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) HAH MU HW.
  destruct (lw_fs_place _ hb mem md FS HAH Htp HFSr) as [HGTb Hend _ Happ].
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) hb mem md HAH) as Hhi.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hap : app_mem (AC.as_tp AC.ASYMS + Z.of_nat k))
      by (unfold app_mem, LOWMEM_END, AC.as_tp, AC.ASYMS; cbn; left; lia).
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx.
      apply HW; [exact Hap | unfold AC.as_tp, AC.ASYMS, HIGHMEM_BEG in *; cbn in *; lia
                | unfold AC.as_tp, AC.ASYMS; cbn; lia]. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply (fl_bytes W mem mem'); [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HW; [| lia | lia].
    apply Happ. lia. }
  { eapply (fl_bytes W mem mem'); [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. rewrite HB6 in Hx. apply HW; [| lia | lia].
    apply Happ. lia. }
Qed.

Lemma seg_A3 : Hcut B APIf ra (Inv_B81220 B APIf ra) -> Hcut B APIf ra (Inv_B810c4 B APIf ra).
Proof.
  intros Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & A & fr & sp & s8 & Ec & HPREF & HENT & Hr25 & Hfrm & Hr24 & Hfrr & HfrA &
                    Hs8 & Hr22 & Hr18 & Hloc).
  subst c. rewrite SEGS.
  unfold FRAME_BYTES in HfrA, Hloc.
  pose proof HPREF as (HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & Hr4 & Hr8 & Hr9 &
                       Hr3 & Hr26 & HAm & HAS & HAlo464 & Hspa & HA448 & HS4 & HAPP & Hwin & Hsaved & Herrno &
                       HAG & Hwinad & HShi1 & HShi2 & HShi3 & Hn & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (Hstkhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS (g_H g) mem md HAH).
  pose proof Hwin as Hwin0. unfold stk in Hwin0. destruct Hwin0 as (Hw0 & Hw1 & Hwv).
  assert (HAhi : HIGHMEM_BEG <= A) by lia.
  assert (HA64 : A + 344 <= 2 ^ 64) by lia.
  assert (HGThi : AC.GT < HIGHMEM_BEG) by (unfold AC.GT, HIGHMEM_BEG; lia).
  (* the two arms, with the side arm's FakeStack base identified once *)
  assert (ARM :
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr /\ fr + 3136 <= APPMEM_END /\ s8 = 0 /\ sp = fr /\
     (forall a, fr <= a < fr + 3136 -> AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END))
    \/ (exists FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ AC.GT <= FS /\
          (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\ FS + 6328320 <= fr /\
          fr + 3136 <= FS + AC.FS_SIZE /\ s8 = fr /\ sp = A /\
          (forall a, fr <= a < fr + 3136 -> AC.a_in_fs AC.ASYMS mem a) /\ FSREC fr mem)).
  { destruct Hloc as [(Hs80 & Hspfr & Hreal)|(Hs8fr & Hspa2 & Hfsb & Hfs & Hrec)].
    - left. pose proof (Hreal (fr + 3135) ltac:(lia)) as Hr3039. pose proof (Hreal fr ltac:(lia)) as Hr0.
      split; [lia|]. split; [lia|]. split; [exact Hs80|]. split; [exact Hspfr | exact Hreal].
    - right.
      pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as HFSC.
      destruct HFSC as (_ & _ & _ & _ & (FSw & HFSb & Hfsok) & _).
      apply bytes_at_le8_word in HFSb.
      pose proof (u64_range FSw) as HFSr.
      destruct Hfsok as (HF0 & _ & HFGT & HFapp).
      unfold AsanRT.RT_GT in HFGT.
      exists (bv_unsigned FSw).
      assert (Hid : forall a0, fr <= a0 < fr + 3136 -> bv_unsigned FSw <= a0 < bv_unsigned FSw + AC.FS_SIZE).
      { intros a0 Ha0. specialize (Hfs a0 Ha0). unfold AC.a_in_fs in Hfs.
        destruct Hfs as (b & Hbr & Hwm & Hb2).
        change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP in Hwm.
        pose proof (a3_wm_congr mem AsanRT.RT_TP b (bv_unsigned FSw) Hwm HFSb) as Hcong.
        rewrite (Z.mod_small b (2 ^ 64)) in Hcong by lia.
        rewrite (Z.mod_small (bv_unsigned FSw) (2 ^ 64)) in Hcong by lia.
        subst b. exact Hb2. }
      pose proof (Hid fr ltac:(lia)) as Hidfr. pose proof (Hid (fr + 3135) ltac:(lia)) as Hidtop.
      split; [change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; exact HFSb|].
      split; [lia|].
      split; [unfold AC.GT; lia|].
      split; [intros a0 Ha0; apply HFapp; unfold AC.FS_SIZE in Ha0; unfold RT_FS_SIZE; lia|].
      split; [apply Hfsb; [change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; exact HFSb | lia]|].
      split; [unfold AC.FS_SIZE in *; lia|].
      split; [exact Hs8fr|]. split; [exact Hspa2|]. split; [exact Hfs | exact Hrec]. }
  (* the frame is application memory, above GT, and in one half of it *)
  assert (Happ : forall a0, fr <= a0 < fr + 3136 -> app_mem a0).
  { intros a0 Ha0. destruct ARM as [(Hlo & Hhi & _ & _ & Hreal)|(FS & _ & _ & _ & HFapp & Hmeta & Hhi2 & _ & _ & _)].
    - specialize (Hreal a0 Ha0). right. unfold APPMEM_END, HIGHMEM_BEG in *. lia.
    - apply HFapp. lia. }
  assert (HfrGT : AC.GT <= fr).
  { destruct ARM as [(Hlo & _ & _ & _ & _)|(FS & _ & _ & HfsGT & _ & Hmeta & _ & _ & _ & _)];
      [unfold AC.GT, HIGHMEM_BEG in *; lia | lia]. }
  assert (Hfrsep : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ fr ltac:(lia)) as Ha1. pose proof (Happ (fr + 3135) ltac:(lia)) as Ha2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha1, Ha2 |- *.
    destruct Ha1 as [Ha1|Ha1]; destruct Ha2 as [Ha2|Ha2]; [left; lia | left; lia | right; lia | right; lia]. }
  (* the 392 frame shadow bytes are shadow bytes *)
  assert (HshIS : forall i, 0 <= i < 392 -> in_shadow (Sfr fr + i)).
  { intros i Hi. pose proof (a3_sfr_shadow fr (Sfr fr + i)) as E.
    replace (Sfr fr + i - Sfr fr) with i in E by lia.
    rewrite E. apply shadow_of_app. apply Happ. unfold Sfr, shadow_addr in *. lia. }
  pose proof (HshIS 0 ltac:(lia)) as Hin0. rewrite Z.add_0_r in Hin0.
  pose proof (HshIS 391 ltac:(lia)) as Hin379.
  assert (HSlo : LOWMEM_END <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0 |- *; lia).
  assert (HShi : Sfr fr + 392 <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin379 |- *; lia).
  (* numeric forms of the four range bounds, so that the side conditions below are plain arithmetic *)
  assert (HfrN : 6283264 <= fr) by (unfold AC.GT in HfrGT; lia).
  assert (HAN : 17594333495296 <= A) by (unfold HIGHMEM_BEG in HAhi; lia).
  assert (HShN1 : 2147450880 <= Sfr fr) by (unfold LOWMEM_END in HSlo; lia).
  assert (HShN2 : Sfr fr + 392 <= 17594333495296) by (unfold HIGHMEM_BEG in HShi; lia).
  assert (HsepN : fr + 3136 <= 2147450880 \/ 17594333495296 <= fr)
    by (unfold LOWMEM_END, HIGHMEM_BEG in Hfrsep; exact Hfrsep).
  (* the two store targets of the segment are writable *)
  assert (HWs : wr_at rsegs mem (A + 336) 8).
  { split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hwv (A + 336 + i) ltac:(lia))). }
  assert (HWh : wr_at rsegs mem fr 24).
  { split; [lia|]. split; [lia|]. intros i Hi.
    destruct ARM as [(Hlo & Hhi & Hs80 & Hspfr & Hreal)|(FS & Hwm & Hfsr & HfsGT & HFapp & Hmeta & Hhi2 & _ & _ & _)].
    - exact (proj1 (Hwv (fr + i) ltac:(lia))).
    - exact (proj1 (lw_fs_bytes mem FS (lw_fs_ok _ (g_H g) mem md FS HAH Hwm Hfsr) (fr + i)
                      ltac:(unfold AC.FS_SIZE in *; lia))). }
  (* run the segment *)
  apply (sl_run regs (Z_to_bv 64 0x810c4) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81220 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 20 = Z_to_bv 64 (-8) /\ getr R 21 = Z_to_bv 64 (-14) /\
       getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 27 = Z_to_bv 64 (Sfr fr + 68) /\
       munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ shadow_rw mem' /\
       q64 mem' (A + 336) fr /\ q64 mem' fr 0x41b58ab3 /\ q64 mem' (fr + 8) 0x17e9c /\
       q64 mem' (fr + 16) AF.ENTRY)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite a3_mkR_of.
    eapply evt_mono.
    + apply (a3_evt SHf8) with (A := A) (fr := fr).
      * exact Hr9.
      * exact Hr25.
      * exact Hr26.
      * exact HfrGT.
      * exact HfrA.
      * exact HAhi.
      * exact HA64.
      * exact Hfrsep.
      * exact HshIS.
      * exact HWh.
      * exact HWs.
      * exact (AsanRTInv.RT_shadow_rw _ _ _ HRT).
      * exact Hro.
      * exact (AsanRTInv.RT_cells _ _ _ HRT).
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P24 & P25 & P26 & P27 &
                  MUq & WMq & ROq & SWq & Q1 & Q2 & Q3 & Q4).
      exists R, (Z_to_bv 64 0x81220), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P18|]. split; [exact P19|]. split; [exact P20|]. split; [exact P21|].
      split; [exact P22|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|]. split; [exact P27|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq|]. split; [exact SWq|].
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3 | exact Q4].
  - (* the continuation: assemble FRAS at 0x81220 *)
    intros R pc' mem' regs'' md' (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR18 & HR19 & HR20 & HR21 & HR22 & HR24 &
      HR25 & HR26 & HR27 & MU & WM & RO' & SW' & Q336 & Qh0 & Qh8 & Qh16) Hreg Hmat.
    subst pc'. rewrite <- SEGS. apply Hbc.
    (* the bytes below GT are untouched *)
    assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < AC.GT -> mbyte sg mem' x = mbyte sg mem x).
    { intros sg x H0 H1. unfold mbyte. rewrite MU; [reflexivity|].
      rewrite MState.unsigned_lit by (unfold AC.GT in H1; lia).
      cbn [outside]. unfold AC.GT in H1. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
      by (intros x Hx Hwx; exact (WM (Z_to_bv 64 x) Hwx)).
    (* presence of every byte the segment wrote *)
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb).
      destruct (a3_split3 (A + 336) (A + 344) fr (fr + 24) (Sfr fr) (Sfr fr + 392) q) as [H1|[H2|[H3|Ho]]].
      - exact (a3_mbyte_of_q64 mem' (A + 336) fr q Q336 ltac:(lia)).
      - destruct (Z_lt_ge_dec q (fr + 8)) as [Hc1|Hc1];
          [exact (a3_mbyte_of_q64 mem' fr 0x41b58ab3 q Qh0 ltac:(lia))|].
        destruct (Z_lt_ge_dec q (fr + 16)) as [Hc2|Hc2];
          [exact (a3_mbyte_of_q64 mem' (fr + 8) 0x17e9c q Qh8 ltac:(lia))
          |exact (a3_mbyte_of_q64 mem' (fr + 16) AF.ENTRY q Qh16 ltac:(lia))].
      - destruct (proj2 (SW' q (a3_in_sh (Sfr fr) q HshIS H3))) as (b' & Hb'). exists b'. exact Hb'.
      - exists b. unfold mbyte in Hb |- *. rewrite MU; [exact Hb|].
        rewrite MState.unsigned_lit by lia. exact Ho. }
    (* the heap invariant and the stack low bound across the writes *)
    assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem' md /\
                    (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem' md a <->
                               AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (g_H g) mem md a) /\
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct ARM as [(Hlo & Hhi & Hs80 & Hspfr & Hreal)
                      |(FS & Hwm & Hfsr & HfsGT & HFapp & Hmeta & Hhi2 & Hs8f & Hspa2 & Hfs)].
      - assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                  ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (a3_split3 (A + 336) (A + 344) fr (fr + 24) (Sfr fr) (Sfr fr + 392) x) as [H1|[H2|[H3|Ho]]].
          - exfalso. apply Hnok. right. left. lia.
          - exfalso. apply Hnok. right. left. pose proof (Hreal x ltac:(lia)). lia.
          - exfalso. apply Hnok. right. right. right. exists (fr + 8 * (x - Sfr fr)).
            split; [exact (a3_sfr_shadow fr x)|]. right. left.
            pose proof (Hreal (fr + 8 * (x - Sfr fr)) ltac:(lia)). lia.
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho. }
        destruct (lw_store _ (g_H g) mem mem' md HAH Hmc Hwrit) as [L1 L2 L3 L4].
        exact (conj L1 (conj L2 (conj L3 L4))).
      - assert (Hmetaout : forall q, Tac_fs.fs_meta FS q ->
                  outside [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] q).
        { intros q Hq. pose proof (a3_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFapp; unfold AC.FS_SIZE in *; lia).
          cbn [outside]. split; [lia|]. split; [lia|]. split; [|exact I].
          intro Hin380. exact (app_not_shadow q Hqa (a3_in_sh (Sfr fr) q HshIS Hin380)). }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (a3_split3 (A + 336) (A + 344) fr (fr + 24) (Sfr fr) (Sfr fr + 392) q) as [H1|[H2|[H3|Ho]]].
          - exfalso. apply Hnok. right. left. lia.
          - exfalso. apply Hnfs. lia.
          - exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
            split; [lia | exact (a3_sfr_shadow fr q)].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho. }
        exact (Tac_fs.a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] (g_H g) mem mem' md FS
                    ALAWS HAH Hwm Hfsr ltac:(pose proof (HFapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as Hft;
                                             unfold app_mem, APPMEM_END in Hft; lia)
                    MU Hwrit Hpres Hmetaout Hagree). }
    destruct AHSTK as (HAH' & HOWN' & HSTK' & HSTKHI').
    destruct (lw_mat_le (APIf rc) (g_H g) mem' md md' Hmat) as [HAHm _ Hstklo_eq _].
    (* the segment's three written ranges, as an outside-W test *)
    assert (HW3 : forall x, 0 <= x < 2 ^ 64 ->
              ~ (A + 336 <= x < A + 344) -> ~ (fr <= x < fr + 24) -> ~ (Sfr fr <= x < Sfr fr + 392) ->
              outside [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] x).
    { intros x Hx H1 H2 H3. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                     replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
    pose proof (a3_shadow_off fr) as Hshfr.
    (* PREF's input facts across the run (de2516edf5): for n > 0 the input block is a live entry block, so
       each of its bytes is app memory below stklo <= S - SLOT_STACK < A and off the frame (real arm: stklo <= fr;
       side arm: not in the FakeStack, which holds the frame), and neither it nor its shadow byte is one of the
       three written ranges (fra_in_keep_sh). *)
    assert (HIN' : bytes_at rsegs mem' (g_p g) (g_in g) /\
              (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g))).
    { apply (fra_in_keep_sh g mem mem' [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)]
               Hinb Hinblk MU).
      intros x Hx.
      destruct (Hinblk ltac:(lia)) as (Hin & _).
      destruct (lw_blocks _ (g_H g) mem md (g_p g) (g_n g) HAH Hin) as [_ _ Hend _ Hall].
      destruct (Hall x Hx) as (Happx & _ & _ & _ & Hnfs).
      assert (Hxr : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx; lia).
      assert (Hnb : ~ (fr <= x < fr + 3136)).
      { destruct ARM as [(Hlo & _)|(FS & _ & _ & _ & _ & _ & _ & _ & _ & Hfs & _)]; [lia|].
        intro Hf. exact (Hnfs (Hfs x Hf)). }
      pose proof (shadow_of_app x Happx) as Hsx.
      pose proof Hsx as Hsx'.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsx'.
      split.
      - apply HW3; [exact Hxr | lia | lia |].
        intro Hs. exact (app_not_shadow x Happx (a3_in_sh (Sfr fr) x HshIS Hs)).
      - apply HW3.
        + lia.
        + lia.
        + intro Hf. exact (app_not_shadow (shadow_addr x) (Happ (shadow_addr x) ltac:(lia)) Hsx).
        + exact (Hshfr x Hfr8 ltac:(lia) ltac:(lia) Hnb). }
    (* ENT across the run: none of the addresses the entry relation speaks of (the bytes of an entry block the
       target does not keep, the image, the stack at or above S, the shadow bytes of those, and the shadow bytes of
       those entry blocks) is one of the segment's three written ranges. *)
    assert (HENT1 : ENT APIf g [] mem' md).
    { eapply ent_munch with (W := [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)]) (mem := mem).
      - exact HENT.
      - exact HAH.
      - exact MU.
      - intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hshk]]]].
        + destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
          destruct (lw_blocks _ (g_H g) mem md q k HAH Hin) as [_ Hq4 Hend _ Hall].
          destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
          assert (Hqr : 0 <= q + i < 2 ^ 64)
            by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
          apply HW3; [exact Hqr | lia | |].
          * destruct ARM as [(Hlo & _)|(FS & _ & _ & _ & _ & _ & _ & _ & _ & Hfs & _)]; [lia|].
            intro Hf. exact (Hnfs (Hfs (q + i) ltac:(lia))).
          * intro Hs. exact (app_not_shadow (q + i) Happq (a3_in_sh (Sfr fr) (q + i) HshIS Hs)).
        + pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
          assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
          apply HW3; [lia | lia | lia |].
          intro Hs. exact (app_not_shadow x Happx (a3_in_sh (Sfr fr) x HshIS Hs)).
        + assert (Happx : app_mem x) by (unfold app_mem, HIGHMEM_BEG; right; lia).
          apply HW3; [lia | lia | lia |].
          intro Hs. exact (app_not_shadow x Happx (a3_in_sh (Sfr fr) x HshIS Hs)).
        + assert (Hb0 : 0 <= b)
            by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
          assert (Hnb : ~ (fr <= b < fr + 3136))
            by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
          assert (Happb : app_mem b).
          { destruct Hor as [Hi|Hr];
              [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X; unfold app_mem, LOWMEM_END; left; lia
              |unfold app_mem, HIGHMEM_BEG; right; lia]. }
          pose proof (shadow_of_app b Happb) as Hsb.
          pose proof Hsb as Hsb'.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
          apply HW3.
          * lia.
          * lia.
          * intro Hf. exact (app_not_shadow (shadow_addr b) (Happ (shadow_addr b) ltac:(lia)) Hsb).
          * exact (Hshfr b Hfr8 ltac:(lia) Hb0 Hnb).
        + (* the shadow byte of a byte of an entry block the target does not keep: that byte is app memory below
             stklo and off the frame *)
          destruct Hshk as (q & k & i & Hin & Hni & Hi & ->).
          destruct (lw_blocks _ (g_H g) mem md q k HAH Hin) as [_ Hq4 Hend _ Hall].
          destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
          assert (Hb0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
          assert (Hnb : ~ (fr <= q + i < fr + 3136)).
          { destruct ARM as [(Hlo & _)|(FS & _ & _ & _ & _ & _ & _ & _ & _ & Hfs & _)]; [lia|].
            intro Hf. exact (Hnfs (Hfs (q + i) Hf)). }
          pose proof (shadow_of_app (q + i) Happq) as Hsq.
          pose proof Hsq as Hsq'.
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsq'.
          apply HW3.
          * lia.
          * lia.
          * intro Hf. exact (app_not_shadow (shadow_addr (q + i)) (Happ (shadow_addr (q + i)) ltac:(lia)) Hsq).
          * exact (Hshfr (q + i) Hfr8 ltac:(lia) Hb0 Hnb).
      - exact HSTK'.
      - exact HSTKHI'.
      - intros a Hia Ho. exact (proj2 (HOWN' a) Ho). }
    assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    exists regs'', mem', md', fr, s8.
    split; [reflexivity|].
    split; [|split; [exact HENT'|]].
    + (* FRAS g fr [] regs'' mem' md' s8 *)
      exists A, sp.
      split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md'
                       [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] HRT MU WM
                       ltac:(unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
                               RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO,
                               RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN;
                             unfold AC.GT in HfrGT; unfold LOWMEM_END in HSlo; unfold HIGHMEM_BEG in HAhi;
                             cbn [disjoint_from]; repeat split; (lia || exact I))
                       ltac:(intros a Ha; exact (proj2 (SW' a Ha))))|].
      split; [exact (HAHm HAH')|].
      split; [exact RO'|].
      split.
      { destruct Hsn as (Hcse & Hohd & Hfd).
        pose proof FF as (_ & _ & _ & _ & Hhead & Hlock & Hthr & _).
        split; [|split].
        - destruct Hcse as (Hthrm & Hlockm). split.
          + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
              [rewrite Hthr in Hx; cbn in Hx; lia | rewrite Hthr in Hx; cbn in Hx; unfold AC.GT; lia].
          + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
              [rewrite Hlock in Hx; cbn in Hx; lia | rewrite Hlock in Hx; cbn in Hx; unfold AC.GT; lia].
        - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; unfold AC.GT; lia].
        - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
      split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
      split.
      { intros a Hin. rewrite KBlo.
        - exact (Hgimg a Hin).
        - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
          destruct Hil as [E|[]]; injection E as <- <-; lia.
        - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
          destruct Hil as [E|[]]; injection E as <- <-; unfold AC.GT; lia. }
      split; [rewrite Hreg, HR2; exact Hr2|].
      split; [exact Hspm|].
      split; [unfold AC.aspZ in *; rewrite Hreg, HR2; exact Haspz|].
      split; [rewrite Hstklo_eq, HSTK'; exact Hstklo|].
      split; [rewrite Hreg, HR4; exact Hr4|].
      split; [unfold rg in *; rewrite Hreg, HR8; exact Hr8|].
      split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|].
      split; [rewrite Hreg, HR3; exact Hr3|].
      split; [unfold rg; rewrite Hreg; exact HR19|].
      split; [unfold rg in *; rewrite Hreg, HR26; exact Hr26|].
      split; [exact Hfrm|].
      split; [exact Hs8|].
      split; [exact HAm|].
      split; [exact HAS|].
      split; [exact Hspa|].
      split; [exact HfrA|].
      split; [exact HA448|].
      split; [exact HS4|].
      split; [exact HAPP|].
      split; [exact Q336|].
      split.
      { destruct ARM as [(Hlo & Hhi & Hs80 & Hspfr & Hreal)
                        |(FS & Hwm & Hfsr & HfsGT & HFapp & Hmetafs & Hhi2 & Hs8f & Hspa2 & Hfs & Hrec)].
        - left. split; [exact Hs80|]. split; [exact Hspfr|].
          intros a Ha. rewrite Hstklo_eq, HSTK'. exact (Hreal a Ha).
        - right. split; [exact Hs8f|]. split.
          + intros FS' Hwm' Hfsr'.
            assert (Hwmb : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS').
            { intros k Hk. rewrite <- (KBlo rsegs (AC.as_tp AC.ASYMS + Z.of_nat k));
                [exact (Hwm' k Hk)
                | change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; unfold AsanRT.RT_TP; lia
                | change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; unfold AsanRT.RT_TP, AC.GT; lia]. }
            assert (HFSeq : FS' = FS).
            { pose proof (a3_wm_congr mem (AC.as_tp AC.ASYMS) FS' FS Hwmb Hwm) as Hcong.
              rewrite (Z.mod_small FS' (2 ^ 64)) in Hcong by lia.
              rewrite (Z.mod_small FS (2 ^ 64)) in Hcong by lia. exact Hcong. }
            subst FS'. exact Hmetafs.
          + split.
            * intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hwmb & Hb2).
              exists b. split; [exact Hbr|]. split; [|exact Hb2].
              intros k Hk. rewrite (KBlo rsegs (AC.as_tp AC.ASYMS + Z.of_nat k));
                [exact (Hwmb k Hk)
                | change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; unfold AsanRT.RT_TP; lia
                | change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; unfold AsanRT.RT_TP, AC.GT; lia].
            * (* the frame record: no written range holds an app byte below stklo off the frame *)
              refine (a3_fsrec_keep (g_H g) mem mem' md _ fr Hrec HAH MU _).
              intros x Hxa Hxlo Hxf.
              apply HW3.
              -- unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa. lia.
              -- lia.
              -- lia.
              -- intro Hs. exact (app_not_shadow x Hxa (a3_in_sh (Sfr fr) x HshIS Hs)). }
      split; [exact Qh0|].
      split; [exact Qh16|].
      split.
      { destruct (a3_sh_bytes mem' (Sfr fr) 392 SW'
                    ltac:(intros i Hi; apply HshIS; lia)
                    ltac:(unfold LOWMEM_END in HSlo; lia)
                    ltac:(unfold HIGHMEM_BEG in HShi; lia)) as (sh & Hshb & Hshl).
        exists sh. split; [exact Hshb | rewrite FRAME_SHADOW_val; exact Hshl]. }
      split.
      { eapply (LF.stk_transport rsegs [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] mem mem'
                  (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | exact MU | exact WM |].
        intros x Hx.
        destruct (a3_split3 (A + 336) (A + 344) fr (fr + 24) (Sfr fr) (Sfr fr + 392) x) as [H1|[H2|[H3|Ho]]].
        - right. exact (a3_raw_of_q64 mem' (A + 336) fr x Q336 ltac:(unfold AC.GT; lia) ltac:(lia) ltac:(lia)).
        - right. destruct (Z_lt_ge_dec x (fr + 8)) as [Hc1|Hc1];
            [exact (a3_raw_of_q64 mem' fr 0x41b58ab3 x Qh0 HfrGT ltac:(lia) ltac:(lia))|].
          destruct (Z_lt_ge_dec x (fr + 16)) as [Hc2|Hc2];
            [exact (a3_raw_of_q64 mem' (fr + 8) 0x17e9c x Qh8 ltac:(lia) ltac:(lia) ltac:(lia))
            |exact (a3_raw_of_q64 mem' (fr + 16) AF.ENTRY x Qh16 ltac:(lia) ltac:(lia) ltac:(lia))].
        - exfalso. unfold HIGHMEM_BEG in HShi, Hstkhigh. lia.
        - left. exact Ho. }
      split.
      { eapply (fl_bytes [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] mem mem');
          [exact Hsaved | exact MU |].
        intros x Hx. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
        split; [lia|]. split; [lia|]. split; [unfold HIGHMEM_BEG in HShi, Hstkhigh; lia | exact I]. }
      split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
      split.
      { intros a Hin. pose proof (a3_AG_below a Hin) as Halt.
        destruct (HAG a Hin) as (G1 & G2 & G3 & G4).
        split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
        intros i Hi. assert (Hi0 : i = 0) by lia. subst i.
        destruct (G4 0 ltac:(lia)) as (Happa & b & Hb & Hok).
        split; [exact Happa|]. exists b. split; [|exact Hok].
        assert (Emem : mem' (LM.wa (shadow_addr (a + 0))) = mem (LM.wa (shadow_addr (a + 0)))).
        { apply MU. rewrite LM.wa_unsigned
            by (unfold shadow_addr, ASAN_K, AC.GT in *; Z.div_mod_to_equations; lia).
          cbn [outside].
          unfold AC.GT in Halt, HfrGT. unfold HIGHMEM_BEG in HAhi, Hfrsep. unfold LOWMEM_END in Hfrsep.
          unfold Sfr, shadow_addr, ASAN_K in *.
          split; [Z.div_mod_to_equations; lia|].
          split; [Z.div_mod_to_equations; lia|].
          split; [Z.div_mod_to_equations; lia | exact I]. }
        unfold LM.mrd in Hb |- *. rewrite Emem. exact Hb. }
      split.
      { intros a Ha Hnfr.
        pose proof (Hwinad a Ha) as Hada.
        pose proof (addr1_app mem a Hada) as Happa.
        apply (addr1_munch [(A + 336, A + 344); (fr, fr + 24); (Sfr fr, Sfr fr + 392)] mem mem' a MU);
          [| exact Hada].
        pose proof (shadow_of_app a Happa) as Hsa.
        pose proof Hsa as Hsa'.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsa'.
        apply HW3.
        - lia.
        - lia.
        - intro Hf. exact (app_not_shadow (shadow_addr a) (Happ (shadow_addr a) ltac:(lia)) Hsa).
        - apply (Hshfr a Hfr8 ltac:(lia));
            [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happa; lia | exact Hnfr]. }
      split; [exact HShi1|].
      split; [exact HShi2|].
      split; [exact HShi3|].
      split; [cbn; lia|].
      split; [exact Hlive | exact HIN'].
    + (* the cut's own register content *)
      split; [exact Hn|].
      split; [unfold rg; rewrite Hreg; exact HR20|].
      split; [unfold rg; rewrite Hreg; exact HR21|].
      split; [unfold rg in *; rewrite Hreg, HR24; exact Hr24|].
      split; [unfold rg in *; rewrite Hreg, HR25; exact Hr25|].
      split; [unfold rg in *; rewrite Hreg, HR22; exact Hr22|].
      split; [unfold rg in *; rewrite Hreg, HR18; exact Hr18|].
      unfold rg. rewrite Hreg. exact HR27.
Qed.

End A3seg.
