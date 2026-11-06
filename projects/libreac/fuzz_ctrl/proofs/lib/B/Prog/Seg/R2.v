(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 741 of its 860 lines of code are new or changed and 892 lines of the source are left out. *)
(* Segment R2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x815fc, 0x8163c],
   17 instructions, cut Inv_B815fc (v1.9 pc 0x815fc) -> cut Inv_B81640 (v1.9 pc 0x81640) (plan-asan-ubsan.md
   section 2, row R2; section 4, SH00 = __asan_set_shadow_00).  Re-fit of the v1.8 proof
   (a working branch ebc9154f47d) onto the v1.9.0 bytes and cuts; the only code change is the end of the
   run (v1.8 0x815a8 `sd s11,24(s1)` is gone; the fill's base is s11, spilled to [A + 8], no longer s9 to [A + 16]).
   rule 24: no function proved (a slot segment).  After reac_box_catalogue(a0 = s4 = fr + 2656) the code checks the
   result a0 = BOX_CATALOGUE = CAT <> 0 (0x815fc, the abort branch 0x81600 to 0x82fa4 not taken) and the catalogue
   count [s4] = 11 <> 0 (0x81604 / 0x81608, the abort branch 0x8160c to 0x82fa4 not taken), computes the row offset
   a1 = 296 * ((s6 >> 1) mod 11) and the UBSan wrap test `bgeu ~CAT, a1` (0x81624, T04: a1 <= 2960, so the branch
   to the trap 0x82fa0 at 0x81628 is not taken), sets s2 = CAT + a1 = mrow (0x8162c, with s6 = mode), spills
   s11 = S(fr) + 68 to [A + 8] (0x81634), and calls meta_fill_00(a0 = s11, a1 = 186) (__asan_set_shadow_00 at
   0x8163c), which writes S(fr) + 68 .. S(fr) + 253 = 00, so out[]'s first 1488 bytes at fr + 544 are
   addressable.  r2_evt is the Lib-level run of the 16 instructions and the call taken on its lib/B contract (a
   Section hypothesis, never its code); r2_main lifts it to the cuts.  The contract needs mem_inv, which no cut
   carries, so the run is stepped on the normalized memory (MemNorm) and carried back to the real memory by
   evt_normalize + AsanLift.evt_SR_canon_lazy from ro_agree (r2_run).  The write set of the segment is the 186
   frame-shadow bytes [S(fr) + 68, S(fr) + 254) and the spill bytes [A + 8, A + 16).  The code-byte pointer
   [A + 56] = fr + 3040 is a spill already at the entry cut and is only carried.
   Cuts: entry and exit are SlotInv.v's official Inv_B815fc (which carries s6 = mode, rg regs 22 (mode (g_in g)),
   set by R1's tail 0x815d8 lbu s6,0(s6) and read here to form s2 = mrow) and Inv_B81640.  ENT moves across the run
   by ent_store and across the model step by ent_mat; on FRA's side arm the FakeStack frame record FSREC is kept by
   Tac_slot's fsrec_keep_app_lo (the run writes no app byte below stklo: the spill bytes are in the slot window);
   FRA's input-block facts are kept because the input block is app memory below stklo apart from the frame
   (SlotInv.v fra_in_apart), so neither it nor its shadow bytes are written. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c SlotModel.
Import ListNotations.
Open Scope Z_scope.

Module SSH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.
Module Y14 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK14.

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

Lemma r2_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
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

Lemma r2_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma r2_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma r2_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma r2_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r2_not_out : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof. intros lo1 hi1 lo2 hi2 x H. cbn [outside] in H. lia. Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r2_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The row index of 0x81614 `remu a1,a2,a1` with the count a1 = 11 is below 11. *)
Lemma r2_remu11 : forall x : word, 0 <= bv_unsigned (Sem.mul_div Instr.M_REMU x (Z_to_bv 64 11)) < 11.
Proof.
  intros x.
  rewrite Y14.m_remu by (rewrite MState.unsigned_lit by lia; lia).
  rewrite Y14.v_remu_small by (rewrite MState.unsigned_lit by lia; lia).
  rewrite MState.unsigned_lit by lia. apply Z.mod_pos_bound. lia.
Qed.

(* T04, the UBSan wrap test 0x81624 `bgeu a2,a1` with a2 = ~CAT = 2^64 - 1 - CAT (0x81620 `not a2,a0`, a0 = CAT) and
   a1 = 296 * row: the row offset is at most 2960, far below ~CAT, so the branch is taken and the trap 0x82fa0
   (0x81628) is not reached.  k is the literal the run computes for ~CAT; it is pinned to CAT by the premise. *)
Lemma r2_wrap : forall (k : Z) (x : word), k = 2 ^ 64 - 1 - SlotModel.CAT ->
  negb (bv_ltu (Z_to_bv 64 k)
          (Z_to_bv 64 (bv_unsigned (Sem.mul_div Instr.M_REMU x (Z_to_bv 64 11)) * 296))) = true.
Proof.
  intros k x Hk. pose proof (r2_remu11 x) as H.
  assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold SlotModel.CAT in Hk.
  unfold bv_ltu. rewrite !MState.unsigned_lit by lia.
  apply Bool.negb_true_iff. apply Z.ltb_ge. lia.
Qed.

Lemma r2_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma r2_sh_add : forall p i, p mod 8 = 0 -> 0 <= i -> shadow_addr (p + i) = shadow_addr p + i / 8.
Proof. intros p i Hp Hi. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes (R3.v's r3_addr_z). *)
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

(* 0x81610 `srli a2,s6,0x1`: the value is s6 / 2. *)
Lemma r2_srl1 : forall s : word, bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned s) 1)) = bv_unsigned s / 2.
Proof.
  intros s. pose proof (bv_unsigned_in_range 64 s) as R. unfold bv_modulus in R.
  assert (HP : 2 ^ 64 = 18446744073709551616) by reflexivity.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  apply MState.unsigned_lit. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* The catalogue row register s2 after 0x8162c `add s2,a0,a1` (a0 = CAT, a1 = 296 * ((s6 >> 1) remu 11)): read the
   register off the final mkR and normalize the remu / srli values. *)
Ltac r2_s2 :=
  lazymatch goal with
  | |- getr (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _) _ = _ => change (getr _ _) with v
  end;
  rewrite ?Y14.m_remu by (rewrite MState.unsigned_lit by lia; lia);
  rewrite ?Y14.v_remu_small by (rewrite MState.unsigned_lit by lia; lia);
  rewrite ?(MState.unsigned_lit 11) by lia;
  rewrite ?r2_srl1;
  f_equal; lia.

(* ---- the run: bnez a0 (taken), ld a1,0(s4), bnez a1 (taken), the row offset arithmetic, the UBSan wrap test
   (taken), add s2, li a1,186, sd s11,8(s1), mv a0,s11, and jal meta_fill_00 by the __asan_set_shadow_00 contract.
   v1.9: no store between the count test and the arithmetic (v1.8's 0x815a8 `sd s11,24(s1)` is gone), and the
   fill's base Q is in s11, spilled to [A + 8] (v1.8: s9, to [A + 16]). ---- *)
Lemma r2_evt : SSH.asan_set_shadow_00_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab c Q : Z) (junk jsp : list byte),
    a0 = Z_to_bv 64 SlotModel.CAT -> s1 = Z_to_bv 64 Ab -> s4 = Z_to_bv 64 c -> s11 = Z_to_bv 64 Q ->
    RT_HI <= Q -> Q + 186 <= Ab + 8 -> Ab + 16 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    rw_cells rsegs m (Ab + 8) [CB 8 jsp] -> stk rsegs m (Ab + 8) (Ab + 16) ->
    asan_cells m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81640) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (SlotModel.CAT + 296 * ((bv_unsigned s6 / 2) mod 11)) /\
         munch [(Q, Q + 186); (Ab + 8, Ab + 16)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)] /\ stk rsegs m' (Ab + 8) (Ab + 16) /\
         bytes_at rsegs m' (Ab + 8) (le8 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815fc) fc None m (seg_rom rsegs)).
Proof.
  intros SH0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab c Q junk jsp -> -> -> -> HQrt HQA HA64 RC HQsh CHQ CHS STS HAC HMI.
  (* the run computes with the catalogue address's value (a0 = CAT, the reac_box_catalogue result) *)
  unfold SlotModel.CAT.
  unfold SSH.asan_set_shadow_00_contract, SSH.asan_set_shadow_contract, SSH.ASAN_SET_SHADOW_00 in SH0.
  pose proof (rw_cells_bound rsegs m Q _ CHQ) as HQb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HQb.
  unfold RT_HI in HQrt.
  pose proof (munch_refl [(Q, Q + 186); (Ab + 8, Ab + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815fc bnez a0 (a0 = BOX_CATALOGUE <> 0) *)
  step. if_true.
  (* 0x81604 ld a1,0(s4) = 11; 0x81608 bnez a1 (taken: 0x81610) *)
  step. step. if_true.
  (* 0x81610 srli; 0x81614 remu; 0x81618 li a2,296; 0x8161c mul; 0x81620 not a2,a0; 0x81624 bgeu a2,a1 (T04) *)
  step. step. step. step. step. step.
  lazymatch goal with
  | |- context [Sem.mul_div Instr.M_REMU ?x (Z_to_bv 64 11)] =>
      rewrite (r2_wrap _ x) by (unfold SlotModel.CAT; reflexivity)
  end.
  cbv iota.
  (* 0x8162c add s2,a0,a1; 0x81630 li a1,186; 0x81634 sd s11,8(s1); 0x81638 mv a0,s11; 0x8163c jal meta_fill_00 *)
  step. step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  (* the spill word [A + 8] = s11 the store left in the spill cell *)
  pose proof (proj2 (proj1 CHS)) as B11. cbn [cells_bytes cbytes] in B11. rewrite ?app_nil_r in B11.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  eapply evt_cut.
  { eapply SH0 with (junk := junk); cbv zeta.
    - rewrite !MState.unsigned_lit by lia. intros i Hi. apply HQsh. lia.
    - rewrite !MState.unsigned_lit by lia. eassumption.
    - exact HAC1.
    - exact HMI. }
  intros ms' PO. unfold SSH.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & RW2).
  subst ms'.
  rewrite !MState.unsigned_lit in MU2, RW2 by lia.
  assert (Hsub : sub_fp [(Q, Q + 186)] [(Q, Q + 186); (Ab + 8, Ab + 16)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  pose proof (stk_transport_disjoint rsegs [(Q, Q + 186)] m1 m' (Ab + 8) (Ab + 16) STS MU2 WM2
    ltac:(cbn [disjoint_from]; repeat split; first [exact I | lia])) as STf.
  pose proof (bytes_at_transport rsegs [(Q, Q + 186)] m1 m' _ _ B11 MU2
    ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; cbn [disjoint_from]; repeat split; first [exact I | lia]))
    as B11'.
  replace (ret_pc (Z_to_bv 64 0x81640)) with (Z_to_bv 64 0x81640)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 9 (split; [reflexivity|]).
  split; [r2_s2|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact RW2|]. split; [exact STf | exact B11'].
Qed.

(* ---- the cut level.  The run is r2_run feeding r2_evt on the normalized memory; FRA is moved across the write
   set (frame shadow + the spill bytes [A + 8, A + 16)) by r2_fra (RT by RT_meta_write, the S-anchored window by
   r2_stk_tr), the heap invariant by SlotInv's lw_store (real arm: every written byte is a_store_ok) or
   Tac_fs.a_fs_ok_store_AH (side arm: the frame shadow is the FakeStack's shadow, the spill bytes are stack), ENT by
   ent_store / ent_mat, and the model by sl_fra_move.  The frame size is SlotInv's FRAME_BYTES / FRAME_SHADOW. *)
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

Lemma r2_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r2_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r2_m8 : forall fr k, fr mod 32 = 0 -> (fr + 8 * k) mod 8 = 0.
Proof. intros fr k H. Z.div_mod_to_equations. lia. Qed.

(* s6 = mode is a byte. *)
Lemma r2_mode : forall inp, 0 <= mode inp < 256.
Proof.
  intros inp. unfold mode, inb. destruct (7 <=? nlen inp); [|lia].
  match goal with |- 0 <= ?f ?b < 256 => pose proof (bv_unsigned_in_range 8 b) as R end.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma r2_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Happ Hk. rewrite <- r2_sh8. apply shadow_of_app. apply Happ. lia.
Qed.

Lemma r2_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
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
Lemma r2_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r2_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r2_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma r2_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The spill base named by a spill conjunct is the A of register 9. *)
Lemma r2_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image ---- *)

Lemma r2_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r2_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r2_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r2_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r2_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r2_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r2_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r2_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r2_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r2_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r2_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r2_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r2_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r2_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r2_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* ---- the run lemma: an evt on the normalized memory, lifted to SR on the real configuration (R3.v's r3_run) ---- *)
Section Run.
Context {fx : FPState}.

Lemma r2_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r2_wx Hro HE)
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

Section R2.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee, taken on its lib/B contract (asan_set_shadow_c.v), never on its code. *)
Hypothesis SH00 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.asan_set_shadow_00_contract.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (low image, frame header, the
   spills [A + 40] / [A + 48] / [A + 336], the saved registers) and keeps every shadow byte readable (so
   RT_meta_write), given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still
   backed, the frame_AG globals still addressable, the side arm's FakeStack frame record FSREC kept
   (fsrec_keep_app_lo) and FRA's input facts after the run (the input bytes at p and, for n > 0, their
   addressability; membership in g_H g reads the ghost only).  W may contain shadow bytes and the callee window. *)
Lemma r2_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  bytes_at rsegs mem' (g_p g) (g_in g) ->
  (0 < g_n g -> addressable mem' (g_p g) (g_n g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HREC' Hinb' Hinad' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
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
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
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
  split; [exact (r2_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|]. split; [exact Hinb'|].
  intros Hn. split; [exact (proj1 (Hinblk Hn)) | exact (Hinad' Hn)].
Qed.

(* The segment from the real configuration at 0x815fc: FRA, ENT and the official Inv_B815fc body (with s6 = mode,
   rg regs 22 (mode (g_in g)): 0x815d8 lbu s6,0(s6) in R1's tail, not written again before 0x815fc; s11 = S(fr) + 68,
   rg regs 27, the fill's base) give the official exit Inv_B81640 at 0x81640. *)
Lemma r2_main : forall g regs mem md fr,
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md ->
  g_n g < 2 ^ 26 -> a0v regs CAT -> OURb g fr mem -> rg regs 27 (Sfr fr + 68) -> CUR g 7 regs ->
  spill regs mem 144 (fr + 2176) -> spill regs mem 112 (fr + 2256) ->
  spill regs mem 312 (fr + 544) -> spill regs mem 264 (fr + 2624) ->
  rg regs 20 (fr + 2656) -> q64 mem (fr + 2656) CAT_N -> spill regs mem 56 (fr + 3040) ->
  spill regs mem 184 (fr + 2368) -> addressable mem (fr + 2624) 6 ->
  spill regs mem 96 (decl_slot fr) -> spill regs mem 120 (fr + 2528) ->
  spill regs mem 240 (fr + 2448) -> spill regs mem 232 (fr + 2464) -> spill regs mem 224 (fr + 2496) ->
  spill regs mem 176 (fr + 2688) -> spill regs mem 208 (fr + 2768) -> spill regs mem 64 (fr + 3056) ->
  PRA fr regs mem -> spill regs mem 152 (fr + 64) ->
  rg regs 22 (mode (g_in g)) -> spill regs mem 160 (fr + 32) ->
  Hcut B APIf ra (Inv_B81640 B APIf ra) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x815fc) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g regs mem md fr HFRA HENT Hgn Ha0 HOUR H27 HCUR H144 H112 H312 H264 H20 Hcnt H56 H184 H2624 H96
    H120 H240 H232 H224 H176 H208 H64 HPRA H152 H22 H160 Hexit.
  pose proof (proj1 FF) as SEGS.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof (fra_in_apart B APIf ra g fr [] regs mem md HFRA) as Hinap.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the spills name the spill base A of register 9 *)
  destruct H144 as (A1 & HA1 & Hq144).
  assert (HA1e : A1 = A)
    by (apply (r2_spill_A regs mem 144 (fr + 2176) A A1 HA1 Hq144 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A1.
  destruct H112 as (A2 & HA2 & Hq112).
  assert (HA2e : A2 = A)
    by (apply (r2_spill_A regs mem 112 (fr + 2256) A A2 HA2 Hq112 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  destruct H312 as (A3 & HA3 & Hq312).
  assert (HA3e : A3 = A)
    by (apply (r2_spill_A regs mem 312 (fr + 544) A A3 HA3 Hq312 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A3.
  destruct H264 as (A4 & HA4 & Hq264).
  assert (HA4e : A4 = A)
    by (apply (r2_spill_A regs mem 264 (fr + 2624) A A4 HA4 Hq264 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  destruct H184 as (A6 & HA6 & Hq184).
  assert (HA6e : A6 = A)
    by (apply (r2_spill_A regs mem 184 (fr + 2368) A A6 HA6 Hq184 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A6.
  destruct H96 as (A7 & HA7 & Hq96).
  assert (HA7e : A7 = A)
    by (apply (r2_spill_A regs mem 96 (decl_slot fr) A A7 HA7 Hq96 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A7.
  destruct H120 as (A8 & HA8 & Hq120).
  assert (HA8e : A8 = A)
    by (apply (r2_spill_A regs mem 120 (fr + 2528) A A8 HA8 Hq120 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A8.
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      pose proof (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr) as FPb.
      pose proof (@lwf_gt _ _ _ _ FPb) as HGT.
      split; [apply (@lwf_app _ _ _ _ FPb); lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  pose proof (r2_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  (* separations of the frame shadow, the frame, the spill base *)
  assert (HSfrD : Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) by lia.
  assert (HShm : Sfr fr + FRAME_SHADOW <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + FRAME_SHADOW <= A) by lia.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (r2_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (r2_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  (* the 186 frame-shadow cells the fill writes, read + writable *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite HFSv in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (r2_ba_sub mem (Sfr fr) sh 68 186 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 68) with (Sfr fr + 68) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 186 (skipn 68 sh)) = 186%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (HQsh : forall i, 0 <= i < 186 -> in_shadow (Sfr fr + 68 + i)).
  { intros i Hi. replace (Sfr fr + 68 + i) with (Sfr fr + (68 + i)) by lia. apply r2_fsh; [exact Happ' | lia]. }
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 68) [CB 186 (firstn 186 (skipn 68 sh))]).
  { replace (CB 186 (firstn 186 (skipn 68 sh)))
      with (CB (length (firstn 186 (skipn 68 sh))) (firstn 186 (skipn 68 sh))) by (rewrite Hxl; reflexivity).
    apply r2_rw_CB; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 186) with 186.
    split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (HSW0 _ (HQsh i Hi))). }
  (* the spill bytes [A + 8, A + 16) the `sd s11,8(s1)` writes: inside the S-anchored window *)
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 8) (g_S g) Hwin ltac:(lia)) as (_ & Hw8).
  destruct (stk_split rsegs mem (A + 8) (A + 16) (g_S g) Hw8 ltac:(lia)) as (Hsp8 & _).
  pose proof (r2_stk_rel mem (normalize rsegs mem) (A + 8) (A + 16) HR0 ltac:(lia) Hsp8) as ST8.
  destruct (stk_bytes rsegs _ (A + 8) (A + 16) ST8 ltac:(lia)) as (jsp & Hjl & Hjb).
  assert (RW8 : rw_cells rsegs (normalize rsegs mem) (A + 8) [CB 8 jsp]).
  { replace 8%nat with (length jsp) by lia. apply r2_rw_CB; [exact Hjb|].
    replace (Z.of_nat (length jsp)) with (A + 16 - (A + 8)) by lia. exact (r2_wr_stk _ _ _ ST8). }
  (* the catalogue count [s4] read by `ld a1,0(s4)` *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (fr + 2656) [C8 (Z_to_bv 64 11)]).
  { apply r2_ro8. unfold q64, CAT_N in Hcnt. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hcnt). }
  (* r2_evt's arithmetic premises *)
  assert (P1 : RT_HI <= Sfr fr + 68) by (unfold RT_HI; lia).
  assert (P2 : Sfr fr + 68 + 186 <= A + 8) by lia.
  assert (P3 : A + 16 <= 2 ^ 64) by lia.
  unfold a0v, rg in Ha0.
  unfold rg in Hr19, Hr9, H27, H20, H22.
  rewrite SEGS.
  apply (r2_run regs (Z_to_bv 64 0x815fc) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81640 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 23 = getr regs 23 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 18 = Z_to_bv 64 (CAT + 296 * ((bv_unsigned (getr regs 22) / 2) mod 11)) /\
       LF.munch [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\
       rw_cells rsegs m0' (Sfr fr + 68) [CB 186 (repeat (Z_to_bv 8 0) 186)] /\
       stk rsegs m0' (A + 8) (A + 16) /\
       bytes_at rsegs m0' (A + 8) (le8 (getr regs 27)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r2_mkR_of.
    eapply evt_mono.
    + apply (r2_evt SH00) with (Ab := A) (c := fr + 2656) (Q := Sfr fr + 68)
        (junk := firstn 186 (skipn 68 sh)) (jsp := jsp).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P23' & P25' & P26' & P18' &
                  MUq & WMq & RWq & STq & B8q).
      exists R, (Z_to_bv 64 0x81640), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P23'|].
      split; [exact P25'|]. split; [exact P26'|]. split; [exact P18'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact RWq|]. split; [exact STq | exact B8q].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K23 & K25 & K26 & K18 & MU0 & WM0 & RW0' & ST0' & B8q)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
    pose proof (r2_stk_back mem' m0' (A + 8) (A + 16) HRel ltac:(lia) ST0') as ST'.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B8q) as B8.
    assert (HQZ : bytes_at rsegs mem' (Sfr fr + 68) (repeat (Z_to_bv 8 0) 186)).
    { destruct RW0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] x -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r2_not_out in Hx. destruct Hx as [Hx|Hx].
      - apply (r2_ba_rd mem' (Sfr fr + 68) _ x HQZ). rewrite repeat_length. lia.
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    assert (SW' : shadow_rw mem').
    { apply (r2_shadow_rw [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] mem mem' (AsanRTInv.RT_shadow_rw _ _ _ HRT) MU WM).
      intros a Ha. destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] a) as [Ho|Hno]; [left; exact Ho | right; exact (RDW a Hno)]. }
    (* the heap invariant, the ownership and the stack bounds after the run, by arm *)
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
      - (* real arm: every written byte is a_store_ok (frame shadow, or stack above stklo) *)
        assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok.
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] x) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
          - exfalso. apply Hnok. apply r2_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + right; right; right. exists (fr + 8 * (x - Sfr fr)). split; [rewrite r2_sh8; lia|].
              right; left. apply Hreal. lia.
            + right; left. lia. }
        pose proof (lw_store (APIf rc) ([] ++ g_H g) mem mem' md HAH Hmc Hwrit) as LST.
        split; [exact (@lws_ah _ _ _ _ _ LST)|]. split; [exact (@lws_own _ _ _ _ _ LST)|].
        split; [exact (@lws_lo _ _ _ _ _ LST) | exact (@lws_hi _ _ _ _ _ LST)].
      - (* side arm: the frame shadow is the FakeStack's shadow; the spill bytes are stack *)
        destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
        pose proof (Hfsb FS HwFS HFSr) as HFSfr.
        pose proof (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FS HAH HwFS HFSr) as FPS.
        pose proof (@lwf_gt _ _ _ _ FPS) as HGTFS. pose proof (@lwf_end _ _ _ _ FPS) as HFSend.
        pose proof (@lwf_app _ _ _ _ FPS) as HFSapp.
        assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
        { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] q) as [Ho|Hno].
          - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exact (RDW q Hno). }
        assert (Hmeta : forall q, fs_meta FS q -> LF.outside [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] q).
        { intros q Hq. pose proof (r2_fs_meta_range FS q Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFSapp; lia).
          cbn [LF.outside]. split; [|split; [lia | exact I]].
          intros Hin. apply (app_not_shadow q Hqa).
          replace q with (Sfr fr + (q - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] q) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r2_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite r2_sh8; lia].
            + apply Hnok. right; left. lia. }
        destruct (a_fs_ok_store_AH _ _ _ _ _ [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)]
                    ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree)
          as (HAH' & Hown' & Hstk' & Hhi').
        split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi']. }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia.
      reflexivity. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r2_sa_lo a (r2_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (r2_addr_keep [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the slot window outside the frame is still addressable: a window byte's shadow byte is not written *)
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      assert (Hsa : 2147450880 <= shadow_addr a < 17592186044416 + 2147450880).
      { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
      assert (Hsf : shadow_addr a < Sfr fr + 68 \/ Sfr fr + 68 + 186 <= shadow_addr a).
      { rewrite HFBv in Ha2. unfold Sfr, shadow_addr. revert Ha2 Hfrm. clear. intros H1 H2.
        Z.div_mod_to_equations. lia. }
      apply (r2_addr_keep [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi.
      replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* ENT across the run (the writes are the frame shadow and the slot window) and the model step *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              LF.outside [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] x \/
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] x) as [Ho|Hno]; [left; exact Ho|].
      apply r2_not_out in Hno. destruct Hno as [Hx1|Hx1].
      - right; right; right. lia.
      - right; left. lia. }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    assert (HENT' : ENT APIf g [] mem' md).
    { eapply ent_store with (W := [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)]);
        try exact FF; try exact HENT; try exact HFRA; try exact MU; try exact HWcases;
        try exact HSTK'; try exact HHI'; try exact HOWNk. }
    assert (HENT'' : ENT APIf g [] mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the side arm's FakeStack frame record: the run writes no app byte below stklo off the frame (the spill
       bytes are in the slot window, above stklo; the shadow bytes are not app memory) *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. eapply fsrec_keep_app_lo; [exact Hrec | exact HAH | exact (proj1 (fr_munch_ul _ _ _) MU) |].
      intros x Hxa Hxlo Hxf. apply (proj2 (fr_outside_lib _ _)).
      cbn [LF.outside]. split; [|split; [lia | exact I]].
      intros Hin. apply (app_not_shadow x Hxa).
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
    (* FRA's input facts: the input block is app memory below stklo <= sp - FN_STACK < A + 8 and apart from the
       frame (fra_in_apart), so neither its bytes nor (fr mod 32 = 0) its shadow bytes are in the write set *)
    assert (HINB' : bytes_at rsegs mem' (g_p g) (g_in g)).
    { eapply fl_bytes; [exact Hinb | exact MU |]. intros x Hx.
      destruct (Hinap x ltac:(unfold g_n, nlen; lia)) as (Hxa & Hxlo & _ & _).
      cbn [LF.outside]. split; [|split; [lia | exact I]].
      intros Hin. apply (app_not_shadow x Hxa).
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r2_fsh; [exact Happ' | lia]. }
    assert (HINAD' : 0 < g_n g -> addressable mem' (g_p g) (g_n g)).
    { intros Hn. destruct (Hinblk Hn) as (_ & HADp).
      apply (r2_addr_keep [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] mem mem' (g_p g) (g_n g) HADp MU).
      intros i Hi. destruct (Hinap (g_p g + i) ltac:(lia)) as (Hxa & _ & Hxf & _).
      assert (Hx0 : 0 <= g_p g + i < 140737488355328)
        by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
      assert (Hsa : 2147450880 <= shadow_addr (g_p g + i) < 17592186044416 + 2147450880).
      { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
      assert (Hsf : shadow_addr (g_p g + i) < Sfr fr + 68 \/ Sfr fr + 68 + 186 <= shadow_addr (g_p g + i)).
      { rewrite HFBv in Hxf. unfold Sfr, shadow_addr. revert Hxf Hfrm. clear. intros H1 H2.
        Z.div_mod_to_equations. lia. }
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r2_fra g fr [] regs regs'' mem mem' md [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)]
               HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
        try assumption.
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx.
        destruct (r2_out_dec [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] x) as [Ho|Hno]; [left; exact Ho | right; exact (RDW x Hno)]. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAm); try reflexivity. exact Hmat. }
    (* the spills: at A + off >= A + 16, above the frame shadow and the written spill bytes [A + 8, A + 16) *)
    assert (KS : forall off v, 16 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the same from a spill conjunct (its base is the A of register 9: r2_spill_A) *)
    assert (KSs : forall off v, 16 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A9 & HA9 & Hq9).
      assert (HA9e : A9 = A)
        by (apply (r2_spill_A regs mem off v A A9 HA9 Hq9 Hr9); unfold APPMEM_END in HAPP; lia).
      subst A9. exact (KS off v ltac:(lia) Hq9). }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E23; exact Hc23 | rewrite E25; exact Hc25]. }
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KS 144 _ ltac:(lia) Hq144)|].
    split; [exact (KS 112 _ ltac:(lia) Hq112)|].
    split; [exact (KS 312 _ ltac:(lia) Hq312)|].
    split; [exact (KS 264 _ ltac:(lia) Hq264)|].
    (* [A + 56] = fr + 3040, the code-byte pointer: a spill at the entry cut already (v1.8 stored the pointer to
       [A + 24] in this segment, 0x815a8) *)
    split; [exact (KSs 56 _ ltac:(lia) H56)|].
    split; [exact (KS 184 _ ltac:(lia) Hq184)|].
    split.
    { (* out[]'s first 1488 bytes: their shadow S(fr) + 68 .. S(fr) + 253 is 00 after the fill *)
      apply (r2_addr_z mem' (fr + 544) 186 1488); [reflexivity | lia
        | replace (fr + 544) with (fr + 8 * 68) by lia; apply r2_m8; exact Hfrm | lia
        | intros i Hi; apply Happ'; lia |].
      replace (fr + 544) with (fr + 8 * 68) by lia. rewrite r2_sh8. exact HQZ. }
    split.
    { (* [A + 8] = s11 = S(fr) + 68 (0x81634 sd s11,8(s1)) *)
      exists A. split; [unfold rg; rewrite E9; exact Hr9|]. unfold q64. rewrite <- H27. exact B8. }
    split.
    { (* s2 = CAT + 296 * ((mode >> 1) mod 11) = mrow (0x8162c add s2,a0,a1) *)
      unfold rg. rewrite Hreg, K18, H22.
      rewrite MState.unsigned_lit by (pose proof (r2_mode (g_in g)); lia).
      unfold mrow, istar, CAT_ROW, CAT_N. reflexivity. }
    split.
    { (* our[]'s 6 bytes at fr + 2624: their shadow byte S(fr) + 328 is not written *)
      apply (r2_addr_keep [(Sfr fr + 68, Sfr fr + 68 + 186); (A + 8, A + 16)] mem mem' (fr + 2624) 6 H2624 MU). intros i Hi.
      assert (Hs : shadow_addr (fr + 2624 + i) = Sfr fr + 328).
      { unfold Sfr, shadow_addr. revert Hi Hfrm. clear. intros H1 H2. Z.div_mod_to_equations. lia. }
      rewrite Hs. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KS 96 _ ltac:(lia) Hq96)|]. split; [exact (KS 120 _ ltac:(lia) Hq120)|].
    (* adopt 6: the reply-slot spills [A + 240] / [A + 232] / [A + 224], the record spills [A + 176] / [A + 208]
       and [A + 64] = fr + 3056, all stored in A4 and above the written spill bytes [A + 8, A + 16) *)
    split; [exact (KSs 240 _ ltac:(lia) H240)|]. split; [exact (KSs 232 _ ltac:(lia) H232)|].
    split; [exact (KSs 224 _ ltac:(lia) H224)|]. split; [exact (KSs 176 _ ltac:(lia) H176)|].
    split; [exact (KSs 208 _ ltac:(lia) H208)|]. split; [exact (KSs 64 _ ltac:(lia) H64)|].
    (* adopt 9: PRA (A4's spills at [A + 104] .. [A + 304], eleven conjuncts, [A + 168] = fr + 2880 twice),
       [A + 152] = fr + 64 and [A + 160] = fr + 32, above [A + 8, A + 16) *)
    split.
    { destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b). unfold PRA.
      split; [exact (KSs 136 _ ltac:(lia) P136)|]. split; [exact (KSs 280 _ ltac:(lia) P280)|].
      split; [exact (KSs 168 _ ltac:(lia) P168)|]. split; [exact (KSs 192 _ ltac:(lia) P192)|].
      split; [exact (KSs 200 _ ltac:(lia) P200)|]. split; [exact (KSs 216 _ ltac:(lia) P216)|].
      split; [exact (KSs 104 _ ltac:(lia) P104)|]. split; [exact (KSs 288 _ ltac:(lia) P288)|].
      split; [exact (KSs 296 _ ltac:(lia) P296)|]. split; [exact (KSs 304 _ ltac:(lia) P304)|].
      exact (KSs 168 _ ltac:(lia) P168b). }
    split; [exact (KSs 152 _ ltac:(lia) H152)|].
    exact (KSs 160 _ ltac:(lia) H160).
Qed.

(* S_R2 (forms-asan-ubsan.md), on SlotInv.v's official cuts. *)
Lemma seg_R2 : Hcut B APIf ra (Inv_B81640 B APIf ra) -> Hcut B APIf ra (Inv_B815fc B APIf ra).
Proof.
  intros Hexit g c (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Ha0 & HOUR & H27 & HCUR & H144 & H112 &
                    H312 & H264 & H20 & Hcnt & H56 & H184 & H2624 & H96 & H120 & H240 & H232 & H224 & H176 &
                    H208 & H64 & HPRA & H152 & H22 & H160).
  subst c.
  exact (r2_main g regs mem md fr HFRA HENT Hgn Ha0 HOUR H27 HCUR H144 H112 H312 H264 H20 Hcnt H56 H184 H2624
           H96 H120 H240 H232 H224 H176 H208 H64 HPRA H152 H22 H160 Hexit).
Qed.

End R2.
