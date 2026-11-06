(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 462 of its 587 lines of code are new or changed and 1077 lines of the source are left out. *)
(* Segment R2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x814f8, 0x81528], Inv_A814f8 -> Inv_A8152c.
   rule 24: no function proved (a slot segment).  After reac_box_catalogue(s2 = fr + 2656) the code checks the
   result a0 = BOX_CATALOGUE != 0 (0x814f8, the abort branch 0x814fc not taken) and the count [s2] = 11 != 0 (0x81504,
   the abort branch 0x81508 not taken), computes s2 = CAT + 296 * ((s7 >> 1) mod 11), and calls
   meta_fill_00(a0 = [A + 152] = S(fr) + 68, a1 = 186) (__asan_set_shadow_00 at 0x81528, SH00@0x54ec8), which marks
   out[]'s first 1488 bytes (fr + 544 .. fr + 2031) usable: S(fr) + 68 .. S(fr) + 253 = 00.  r2_evt is the Lib-level
   run of the 11 instructions plus the call by its contract; seg_R2 lifts it to the cuts.  The write set of the
   segment is the 186 frame-shadow bytes [S(fr) + 68, S(fr) + 254). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_set_shadow_c.
Import ListNotations.
Open Scope Z_scope.

Module SSH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_c.

(* ---- byte and shadow helpers (as R3.v) ---- *)

Lemma r2_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r2_ba_sub : forall m A bs k j, bytes_at rsegs m A bs -> (k + j <= length bs)%nat ->
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

Lemma r2_rd_rw : forall m A n l x, rw_cells rsegs m A [CB n l] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A n l x ((Hwf & Hb) & _) Hx. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb.
  rewrite app_nil_r in Hb. destruct Hwf as (Hl & _).
  apply (r2_ba_rd m A l x Hb). rewrite Hl. exact Hx.
Qed.

Lemma r2_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma r2_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r2_sh_add : forall p i, p mod 8 = 0 -> 0 <= i -> shadow_addr (p + i) = shadow_addr p + i / 8.
Proof. intros p i Hp Hi. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma r2_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  rewrite r2_sh_add by lia.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply r2_nth_repeat. exact Hk.
Qed.

Lemma r2_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma r2_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r2_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r2_ro8 : forall m A (v : word), bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof.
  intros m A v Hb. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma r2_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r2_not_out : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof. intros lo hi x H. cbn [outside] in H. lia. Qed.

(* A shadow address is at no read-only image address: every segment of the image ends below LOWMEM_END, and the
   shadow starts above it.  (Tac_b5's sl_ro_lo / sl_shadow_not_ro, restated here: that file imports the UL
   stepping engine, which this half of the file must not see.) *)
Definition r2_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma r2_rsegs_low : r2_tops rsegs LOWMEM_END = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r2_find_below : forall segs top x n s,
  r2_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r2_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r2_shadow_not_ro : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [exfalso|reflexivity].
  unfold ro_addr in E.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|discriminate E].
  destruct (r2_find_below rsegs LOWMEM_END (bv_unsigned (wa a)) 1 s r2_rsegs_low Es ltac:(lia)) as [L|L];
    [|discriminate L].
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  rewrite wa_unsigned in L by lia. unfold LOWMEM_END in L. lia.
Qed.

(* asan_cells crosses the normalization: every conjunct is a bytes_at, and bytes_at reads through mrd, which
   normalize keeps (the read-only bytes it drops from the map are the ROM's own, by ro_agree). *)
Lemma r2_ac_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply bytes_at_normalize; assumption|]).
  apply bytes_at_normalize; assumption.
Qed.

(* remu with a non-zero divisor (AxSymExec3Sound.u_remu64). *)
Lemma r2_remu_u : forall x y : word, bv_unsigned y <> 0 ->
  bv_unsigned (LinuxProcessSemantics.Riscv.Sem.mul_div LinuxProcessSemantics.Riscv.Instr.M_REMU x y) =
  bv_unsigned x mod bv_unsigned y.
Proof.
  intros x y Hy. unfold LinuxProcessSemantics.Riscv.Sem.mul_div.
  replace (bv_unsigned y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_modu_unsigned.
Qed.

(* The row pointer 0x8150c .. 0x8151c forms: s2 = CAT + 296 * ((s7 >> 1) mod 11). *)
Ltac r2_bnd := change (2 ^ 64) with 18446744073709551616; Z.div_mod_to_equations; lia.
Ltac r2_row_tac :=
  symmetry;
  repeat first
    [ rewrite r2_remu_u by (rewrite MState.unsigned_lit by lia; lia)
    | rewrite Z.shiftr_div_pow2 by lia
    | rewrite Z.pow_1_r
    | match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (MState.unsigned_lit z) by r2_bnd end ];
  f_equal; Z.div_mod_to_equations; lia.

(* ---- the run: bnez a0 (taken), ld a1,0(s2), bnez a1 (taken), the row index arithmetic, li a1,186,
   ld a0,152(s1), and jal meta_fill_00 by the __asan_set_shadow_00 contract.
   The cut gives ro_agree, not mem_inv (push 5b), so the call runs on the normalized memory
   (MemNorm.evt_normalize, as a1_req_evt in Seg/A1.v): its premises cross mem_rel (bytes_at_normalize,
   wr_at_norm, the shadow bytes being at no read-only address), mem_inv of `normalize m` is
   mem_inv_normalize, and the post comes back with ms_rel / ro_same, which carry munch, wmono, ro_agree and
   the written cells to the real memory. ---- *)
Lemma r2_evt : SSH.asan_set_shadow_00_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c Q md : Z) (junk : list byte),
    a0 = Z_to_bv 64 0x9e800 -> s1 = Z_to_bv 64 A -> s2 = Z_to_bv 64 c ->
    s7 = Z_to_bv 64 md -> 0 <= md < 256 ->
    0 <= Q -> Q + 186 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    ro_cells rsegs m (A + 152) [C8 (Z_to_bv 64 Q)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    asan_cells m -> ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8152c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (0x9e800 + 296 * ((md / 2) mod 11)) /\
         munch [(Q, Q + 186)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x814f8) fc None m (seg_rom rsegs)).
Proof.
  intros SH0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A c Q md junk -> -> -> -> Hmd HQ0 HQb RC R152 HQsh CHQ HAC HRO.
  unfold SSH.asan_set_shadow_00_contract, SSH.asan_set_shadow_contract, SSH.ASAN_SET_SHADOW_00 in SH0.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  (* the 186 written bytes are shadow bytes, so none of them is at a read-only address *)
  assert (NR : forall i, 0 <= i < 186 -> ro_addr rsegs (wa (Q + i)) = false)
    by (intros i Hi; apply r2_shadow_not_ro; apply HQsh; lia).
  assert (CHQn : rw_cells rsegs (normalize rsegs m) Q [CB 186 junk]).
  { destruct CHQ as ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
    - exact (bytes_at_normalize rsegs m _ _ HRO Hb).
    - cbn [cells_size csize] in Hw |- *. rewrite Nat.add_0_r in Hw |- *.
      exact (wr_at_norm rsegs m _ Q (Z.of_nat 186) REL Hw (fun i Hi => NR i ltac:(cbn in Hi; lia))). }
  step. try if_true.
  step. step. try if_true.
  step. step. step. step. step.
  match goal with
  | |- context [Z_to_bv 64 (649216 + bv_unsigned (LinuxProcessSemantics.Riscv.Sem.mul_div ?o ?u ?v) * 296)] =>
      replace (Z_to_bv 64 (649216 + bv_unsigned (LinuxProcessSemantics.Riscv.Sem.mul_div o u v) * 296))
        with (Z_to_bv 64 (0x9e800 + 296 * ((md / 2) mod 11))) by r2_row_tac
  end.
  step. step.
  step.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO).
    eapply SH0 with (junk := junk); cbv zeta.
    - rewrite !MState.unsigned_lit by lia. intros i Hi. apply HQsh. lia.
    - rewrite !MState.unsigned_lit by lia. exact CHQn.
    - exact (r2_ac_norm m HRO HAC).
    - apply mem_inv_normalize. }
  intros ms' (s0' & PO & MR & RS). unfold SSH.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU & WM & MI' & RW').
  subst s0'.
  rewrite !MState.unsigned_lit in MU, RW' by lia.
  replace (ret_pc (Z_to_bv 64 0x8152c)) with (Z_to_bv 64 0x8152c) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' mem' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  assert (RO' : ro_agree rsegs mem') by exact (ro_agree_same rsegs m mem' HRO RS).
  apply evt_done. exists R', mem'.
  split; [unfold MS; subst; reflexivity|].
  subst R'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m _ mem' m0' REL Hmem RS MU)|].
  split; [exact (wmono_rel rsegs m _ mem' m0' REL Hmem RS WM)|].
  split; [exact RO'|].
  destruct RW' as ((Hwf' & Hb') & Hw'). split; [split; [exact Hwf'|]|].
  - exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ Hmem) Hb').
  - exact (wr_at_rel rsegs mem' m0' _ _ Hmem Hw').
Qed.

(* ---- seg_R2 on the cuts.  The run is sl_run_lib (Tac_b5.v) feeding r2_evt; FRA is moved across the write set
   (the 186 frame-shadow bytes) by the canonical Tac_slot.sl_fr_meta, the heap invariant by a_laws_store (real
   arm: every written byte is the shadow of a frame byte, so a_store_ok) or Tac_fs.a_fs_ok_store_AH (side arm:
   the frame shadow is the FakeStack's shadow), and the model by sl_fra_move. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs RcPro.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

Lemma r2_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r2_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k).
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr k Happ Hk. rewrite <- r2_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma r2_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8). *)
Lemma r2_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* A spill cell [A + off] read through the spill base held in s1. *)
Lemma r2_spill_A : forall regs m A off v, rg regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v Hr HA0 Hoff HA1 (A0 & HA & Hq).
  assert (E : A0 = A).
  { pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A0 A HA Hr) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    Z.div_mod_to_equations. lia. }
  subst A0. exact Hq.
Qed.

(* The mode byte in[6] (0 below 7 input bytes) is a byte value. *)
Lemma r2_mode_rng : forall inp, 0 <= mode inp < 256.
Proof.
  intros inp. unfold mode, inb. destruct (7 <=? nlen inp); [|lia].
  pose proof (bv_unsigned_in_range 8 (RcIdentModel.nthb inp (Z.to_nat 6))) as H.
  unfold bv_modulus in H. cbn in H. first [exact H | unfold RcIdentModel.bz; lia].
Qed.

Section R2.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis SH00 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_c.asan_set_shadow_00_contract.

(* The cuts are SlotInv.v's own (push 8, e2cbb53991f).  Entry Inv_A814f8: the catalogue result a0 = CAT, the
   frame-shadow pointer spill [A + 152] = S(fr) + 68 that the 0x81528 fill reads, s2 = fr + 2656 with the catalogue
   count [s2] = CAT_N = 11 (so the branch 0x81508 is not taken), s5 = fr + 2176, CUR g 7, s7 = mode, our[]'s 6
   bytes addressable, and the spills [A + 48], [A + 128], [A + 168], [A + 144], [A + 192] and the two frame
   records this segment does not write.  Exit Inv_A8152c = R3's entry: the same minus the catalogue facts and s7,
   plus s2 = mrow (0x8150c .. 0x8151c: CAT + 296 * ((s7 >> 1) mod 11); meta_fill_00 keeps s2) and out[]'s first
   1488 bytes addressable by the fill S(fr) + 68 .. 253 = 00 (our[]'s shadow byte S(fr) + 328 is outside it).
   FRA moves with the canonical Tac_slot.sl_fr_meta (the frame-shadow write), ENT with ent_store + ent_mat. *)
Lemma seg_R2 : Hcut B APIf ra (Inv_A8152c B APIf ra) -> Hcut B APIf ra (Inv_A814f8 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Ha0 & HOUR & H152 & H18 & Hcnt & H21 & HCUR &
    H48 & H128 & HPRO & H23 & H144 & H208 & Hidb & Hjnk & H280 & H240 & Hjy & Hscr &
    H56 & H88 & H80 & H72 & H192 & H216).
  subst c.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
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
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the frame is application memory above the image *)
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HSf8 : 8 * (Sfr fr - ASAN_K) = fr) by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
  unfold ACw.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* separations of the frame shadow, the frame, the spill area *)
  assert (HSfrD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  (* the 186 frame-shadow cells the fill writes, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  pose proof (r2_ba_sub mem (Sfr fr) sh 68 186 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 68) with (Sfr fr + 68) in Hxs by lia.
  assert (Hxl : length (firstn 186 (skipn 68 sh)) = 186%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs mem (Sfr fr + 68) [CB 186 (firstn 186 (skipn 68 sh))]).
  { replace (CB 186 (firstn 186 (skipn 68 sh)))
      with (CB (length (firstn 186 (skipn 68 sh))) (firstn 186 (skipn 68 sh))) by (rewrite Hxl; reflexivity).
    apply r2_rw_CB; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 186) with 186.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 68 + i)).
    { replace (Sfr fr + 68 + i) with (Sfr fr + (68 + i)) by lia. apply r2_fsh; [exact Happ' | lia]. }
    exact (proj1 (AsanRTInv.RT_shadow_rw _ _ _ HRT _ Hin)). }
  assert (HQsh : forall i, 0 <= i < 186 -> in_shadow (Sfr fr + 68 + i)).
  { intros i Hi. replace (Sfr fr + 68 + i) with (Sfr fr + (68 + i)) by lia. apply r2_fsh; [exact Happ' | lia]. }
  assert (HQ0 : 0 <= Sfr fr + 68) by lia.
  assert (HQb : Sfr fr + 68 + 186 <= 2 ^ 64) by lia.
  (* the two cells the run loads: the catalogue count [s2] and the frame-shadow pointer [A + 152] *)
  assert (RC : ro_cells rsegs mem (fr + 2656) [C8 (Z_to_bv 64 11)]).
  { apply r2_ro8. unfold q64, CAT_N in Hcnt. exact Hcnt. }
  assert (R152 : ro_cells rsegs mem (A + 152) [C8 (Z_to_bv 64 (Sfr fr + 68))]).
  { apply r2_ro8. exact (r2_spill_A regs mem A 152 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H152). }
  pose proof (r2_spill_A regs mem A 48 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H48) as Hq48.
  pose proof (r2_spill_A regs mem A 128 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H128) as Hq128.
  pose proof (r2_spill_A regs mem A 144 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H144) as Hq144.
  pose proof (r2_spill_A regs mem A 192 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H208) as Hq208.
  pose proof (r2_mode_rng (g_in g)) as Hmd.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  unfold a0v, rg, CAT in Ha0.
  unfold rg in Hr9, Hr19, H21, H18, H23.
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x814f8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8152c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 18 = Z_to_bv 64 (mrow (g_in g)) /\
       LF.munch [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' /\
       LF.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       rw_cells rsegs mem' (Sfr fr + 68) [CB 186 (repeat (Z_to_bv 8 0) 186)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply (r2_evt SH00) with (A := A) (c := fr + 2656) (Q := Sfr fr + 68) (md := mode (g_in g))
        (junk := firstn 186 (skipn 68 sh)).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P21' & P22' & P25' & P26' & P18' &
                  MUq & WMq & ROq & RWq).
      exists R, (Z_to_bv 64 0x8152c), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P21'|].
      split; [exact P22'|]. split; [exact P25'|]. split; [exact P26'|]. split; [exact P18'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq | exact RWq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K18 & MU & WM & RO' & RW') Hreg Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E18 : getr regs'' 18 = Z_to_bv 64 (mrow (g_in g))) by (rewrite Hreg; exact K18).
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(Sfr fr + 68, Sfr fr + 68 + 186)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r2_not_out in Hx. apply (r2_rd_rw mem' (Sfr fr + 68) 186 _ x RW'). lia. }
    assert (SW' : shadow_rw mem').
    { apply (r2_shadow_rw [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' (AsanRTInv.RT_shadow_rw _ _ _ HRT) MU WM).
      intros a Ha. destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186)] a) as [Ho|Hno];
        [left; exact Ho | right; exact (RDW a Hno)]. }
    (* the heap invariant, the owned cells and the stack bounds after the run, by arm *)
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
      - (* real arm: every written byte is the shadow of a frame byte, so a_store_ok *)
        assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186)] x) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
          - exfalso. apply Hnok. apply r2_not_out in Hno.
            right; right; right. exists (fr + 8 * (x - Sfr fr)). split; [rewrite r2_sh8; lia|].
            right; left. apply Hreal. lia. }
        exact (ACw.a_laws_store _ _ _ _ _ ALAWS ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: the frame shadow is the FakeStack's shadow *)
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
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186)] q) as [Ho|Hno].
          - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exact (RDW q Hno). }
        assert (Hmeta : forall q, fs_meta FS q -> LF.outside [(Sfr fr + 68, Sfr fr + 68 + 186)] q).
        { intros q Hq. pose proof (r2_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFSapp; lia).
          cbn [LF.outside]. split; [|exact I].
          intros Hin. apply (app_not_shadow q Hqa).
          replace q with (Sfr fr + (q - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + ACw.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186)] q) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r2_not_out in Hno.
            apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite r2_sh8; lia]. }
        exact (a_fs_ok_store_AH _ _ _ _ _ [(Sfr fr + 68, Sfr fr + 68 + 186)]
                 ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree). }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HSHI').
    (* the new 392-byte frame shadow *)
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r2_ag_range a Ha) as Har.
      apply (r2_addr_keep [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' a 1 (HAG a Ha) MU). intros i Hi.
      replace (a + i) with a by lia.
      assert (Hsa : 2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      cbn [LF.outside]. split; [lia | exact I]. }
    (* FRA across the frame-shadow write: the canonical sl_fr_meta *)
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs'' mem mem' md
               [(Sfr fr + 68, Sfr fr + 68 + 186)] HFRA MU WM RO').
      - unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        cbn [disjoint_from]. repeat split; first [exact I | lia].
      - exact HAH'.
      - exact HSTK'.
      - exact Happ'.
      - unfold ACw.GT. lia.
      - exact Hshnew.
      - intros x Hx Hb Hs. cbn [LF.outside]. split; [lia | exact I].
      - intros A' HA' HA'r x Hx. cbn [LF.outside].
        assert (EA : A' = A) by (rewrite <- HbvA, HA'; symmetry; apply MState.unsigned_lit; exact HA'r).
        subst A'. split; [lia | exact I].
      - intros x Hx. cbn [LF.outside]. split; [lia | exact I].
      - intros A' HA' HA'r x Hx. cbn [LF.outside].
        assert (EA : A' = A) by (rewrite <- HbvA, HA'; symmetry; apply MState.unsigned_lit; exact HA'r).
        subst A'. split; [lia | exact I].
      - intros x Hx. left. cbn [LF.outside]. split; [lia | exact I].
      - exact HAG'.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    (* ENT across the same write, then across the model step *)
    assert (HENT' : ENT APIf g [] mem' md').
    { apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
      apply (ent_store B APIf ra g fr [] regs mem mem' md
               [(Sfr fr + 68, Sfr fr + 68 + 186)] HENT HFRA MU).
      - intros x Hx. destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186)] x) as [Ho|Hno];
          [left; exact Ho|]. apply r2_not_out in Hno. right; right; right. lia.
      - exact HSTK'.
      - exact HSHI'.
      - intros a _ Hown. exact (proj2 (HOWN' a) Hown). }
    (* out[]'s first 1488 bytes: the fill S(fr) + 68 .. 253 = 00 *)
    assert (Hout : addressable mem' (fr + 544) 1488).
    { apply (r2_addr_z mem' (fr + 544) 186 1488); [reflexivity | lia | Z.div_mod_to_equations; lia | lia
        | intros i Hi; apply Happ'; lia |].
      replace (fr + 544) with (fr + 8 * 68) by lia. rewrite r2_sh8.
      destruct RW' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split; [unfold rg; rewrite E21; exact H21|].
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq48 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split; [exact Hout|].
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq128 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    (* PRO (push 13B): the eight spills and our[]'s shadow byte S(fr) + 328 are off the fill, and the fill is
       frame shadow, which the input block shares no granule with (RcPro.rc_away_fsh) *)
    split.
    { apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO MU Hr9 ltac:(lia) ltac:(lia) E9).
      - intros x Hx. cbn [LF.outside]. split; [lia | exact I].
      - intros i Hi. cbn [LF.outside]. split; [|exact I].
        assert (Hs : Sfr fr + 328 <= shadow_addr (fr + 2624 + i)).
        { unfold Sfr, shadow_addr. clear - HFRAMEb HFRAMEs Hi. Z.div_mod_to_equations. lia. }
        lia.
      - intros x Hx. apply r2_not_out in Hx. apply (rc_away_fsh B APIf ra g fr [] regs mem md x HFRA). lia. }
    (* the spills [A + 152], [A + 144], [A + 192] and the two frame records: the fill writes none of them *)
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      pose proof (r2_spill_A regs mem A 152 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H152) as Hq152.
      unfold q64 in *. eapply fl_bytes; [exact Hq152 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq144 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq208 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { destruct Hidb as (idb & Hidb). exists idb.
      apply (rw_cells_transport rsegs [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' _ _ Hidb MU WM).
      cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
    split.
    { destruct Hjnk as (jk & Hjk). exists jk.
      apply (rw_cells_transport rsegs [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' _ _ Hjk MU WM).
      cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
    (* push 9: the code / scratch pointer spills [A + 280], [A + 240] and their cells, outside the fill *)
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      pose proof (r2_spill_A regs mem A 280 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H280) as Hq.
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      pose proof (r2_spill_A regs mem A 240 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H240) as Hq.
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | exact I]. }
    split.
    { destruct Hjy as (jy & Hjy). exists jy.
      apply (rw_cells_transport rsegs [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' _ _ Hjy MU WM).
      cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
    split.
    { destruct Hscr as (js & Hjs). exists js.
      apply (rw_cells_transport rsegs [(Sfr fr + 68, Sfr fr + 68 + 186)] mem mem' _ _ Hjs MU WM).
      cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
    (* push 10: R1's [A + 56] / [A + 88] / [A + 80] / [A + 72] and A4's [A + 200] / [A + 216], outside the fill *)
    do 6 (split; [
      lazymatch goal with
      | |- spill _ _ ?off _ =>
          let Hs := match goal with
                    | H : spill regs mem off _ |- _ => H
                    end in
          exists A; split; [unfold rg; rewrite E9; exact Hr9|];
          let Hq := fresh "Hq" in
          pose proof (r2_spill_A regs mem A off _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hq;
          unfold q64 in Hq |- *; eapply fl_bytes; [exact Hq | exact MU |]; rewrite length_le8;
          let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx; cbn [LF.outside]; split; [lia | exact I]
      end|]).
    (* s2 = mrow (0x8151c; meta_fill_00 keeps s2) *)
    unfold rg; exact E18.
Qed.

End R2.
