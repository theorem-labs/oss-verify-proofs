(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Segment R4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x8168c, 0x81698],
   4 instructions, cut Inv_B8168c (v1.9 pc 0x8168c) -> cut Inv_B8169c (v1.9 pc 0x8169c) (R4 (plan-asan-ubsan.md
   section 2 (a working note, not in this delivery)); section 4, MSET = checked_memset, 0x52600).  Re-fit of the v1.8 proof (a working branch
   c439fa41c5b) onto the v1.9.0 bytes and a Theorem Labs lane's v1.9 cut bundle; the cut names are still the v1.8 names.
   rule 24: no function proved (a slot segment).  The code sets a2 = 72 (0x8168c li a2,72), reloads the fragment
   record address [A + 112] = fr + 2256 (0x81690 ld a0,112(s1); spilled at 0x814c0), sets a1 = 0 (0x81694 li a1,0)
   and calls checked_memset (MSET@0x81698), which writes 72 zero bytes at fr + 2256.  The range has no instrumented
   shadow check and no UBSan trap.  r4_evt is the Lib-level run of the 4 instructions with the call taken on its
   lib/B contract asan_memset_c.v (a Section hypothesis, never its code); seg_R4 lifts it to the cuts.  The contract
   needs mem_inv, so the run is stepped on the normalized memory (MemNorm) and carried back to the real memory by
   evt_normalize + AsanLift.evt_SR_canon_lazy (r4_run), as in R3.  The write set of the segment is the fragment
   record [fr + 2256, fr + 2328) and the callee's stack window [sp - 2208, sp); neither holds a shadow byte.  The
   entry cut's addressable m (fr + 2256) 72 is the memset premise; the exit cut's FGBr g fr (RFG (g_in g) 0) is the
   contract's 72 zero bytes (RFG _ 0 = z72).  The cuts are SlotInv.v's official Inv_B8168c / Inv_B8169c (a Theorem Labs lane's v1.9
   bundle): checked_memset takes no side-stack package, and the exit carries none (the R6 call site rebuilds
   build_as's from FRA).  The exit's spills, out[] / our[] / the identity record addressable are carried from the
   entry (the write set holds no spill and no shadow byte); FRA's input facts are kept by fra_in_keep (the input
   block is app memory below stklo and off the frame, fra_in_apart); the row-name clause (a catalogue row with a
   name: the name's bytes, name_ok, addressable, below GT) is image data, read off the exit memory by r4_rowname
   (by computation on the 11 catalogue rows: the name bytes are read-only image bytes, ro_agree, inside one
   registered global, FRA's frame_AG addressability). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memset_c.
Import ListNotations.
Open Scope Z_scope.

Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* ---- byte, stack and cell helpers ---- *)

Lemma r4_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r4_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma r4_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r4_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma r4_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma r4_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma r4_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r4_not_out : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof. intros lo1 hi1 lo2 hi2 x H. cbn [outside] in H. lia. Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r4_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- the run: li a2,72; ld a0,112(s1); li a1,0; jal checked_memset by its contract ---- *)
Lemma r4_evt : MSC.asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Ab fg lo : Z) (fgb : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 Ab ->
    HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    0 <= Ab -> Ab + 120 <= 2 ^ 64 ->
    RT_HI <= fg -> app_mem (fg + 7) -> app_mem (fg + 72) ->
    (fg + 72 <= spv - 2208 \/ spv <= fg) ->
    rw_cells rsegs m fg [CB 72 fgb] -> ro_cells rsegs m (Ab + 112) [C8 (Z_to_bv 64 fg)] ->
    addressable m fg 72 ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8169c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(fg, fg + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' fg [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8168c) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Ab fg lo fgb -> -> HHM HLO HAE HA0 HA64 Hfrt Hf7 Hf72 Hsep RW RO ADR HMI ST HAC HSW.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  pose proof (rw_cells_bound rsegs m fg _ RW) as Hfb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hfb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 fg) = fg) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET with (junk := fgb) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 72)) with 72.
    - exact RW.
    - lia.
    - exact ADR.
    - unfold end_in_app. right. exact Hf72.
    - right. exact Hf7.
    - right. unfold RT_HI. lia.
    - lia.
    - exact ST.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact HAC.
    - exact HSW.
    - exact HMI. }
  intros ms' PO. unfold MSC.asan_memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms'.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 72)) with 72 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 72) with 72%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  replace (ret_pc (Z_to_bv 64 0x8169c)) with (Z_to_bv 64 0x8169c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact AC2|]. split; [exact SW2 | exact RW2].
Qed.

(* ---- seg_R4 on the cuts.  The run is r4_run feeding r4_evt on the normalized memory; FRA is moved across the
   write set (fragment record + callee window) by r4_fra (R3's r3_fra: RT by RT_meta_write, the S-anchored window
   by r4_stk_tr), the heap invariant by a_laws_store (real arm: every written byte is a_store_ok) or
   Tac_fs.a_fs_ok_store_AH (side arm: the frame is in the FakeStack), and the model by sl_fra_move.  Both cuts
   also carry ENT (the entry relation, moved across the run by ent_store and across the model step by ent_mat)
   and the spills [A + 312] = fr + 544 / [A + 264] = fr + 2624, which this segment only carries: no instruction
   of [0x8168c, 0x81698) writes them and they lie above the spill base A >= fr + 3136 >= sp, outside the write
   set (the fragment record and the callee's stack window). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

Lemma r4_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r4_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma r4_fsh : forall fr k, (forall a, fr <= a < fr + 3136 -> app_mem a) -> 0 <= k < 392 -> in_shadow (Sfr fr + k).
Proof. intros fr k Happ Hk. rewrite <- r4_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma r4_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
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
Lemma r4_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) r4_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma r4_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The spill base named by a spill conjunct is the A of register 9. *)
Lemma r4_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* PRA (adopt 9 of a working branch: A4's frame-loop pointer spills; v1.9: eleven conjuncts, [A+168] = fr + 2880 twice) is
   carried by any map that carries each of its spills. *)
Lemma r4_pra : forall fr (regs regs' : bvmap 5 word) m m',
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

Lemma r4_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r4_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r4_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r4_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r4_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r4_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r4_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r4_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r4_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r4_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* addressable reads only shadow bytes through mrd, which mem_rel keeps. *)
Lemma r4_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* ---- the catalogue row name (the row-name clause of Inv_B8169c) as image data ---- *)
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.

(* name_ok, decided. *)
Definition r4_nokb (nb : list byte) : bool :=
  (1 <=? length nb)%nat && (length nb <=? 16)%nat &&
  forallb (fun i => negb (bv_unsigned (nth i nb (Z_to_bv 8 0)) =? 0)) (seq 0 (pred (length nb))) &&
  ((length nb =? 16)%nat || (bv_unsigned (nth (pred (length nb)) nb (Z_to_bv 8 0)) =? 0)).

Lemma r4_nokb_ok : forall nb, r4_nokb nb = true -> RBx.name_ok nb.
Proof.
  intros nb H. unfold r4_nokb in H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Nat.leb_le in H1, H2. split; [lia|]. split.
  - intros i Hi. rewrite forallb_forall in H3. specialize (H3 i ltac:(apply in_seq; lia)).
    apply negb_true_iff in H3. apply Z.eqb_neq in H3. exact H3.
  - apply orb_true_iff in H4 as [H4|H4]; [left; apply Nat.eqb_eq in H4; exact H4 | right; apply Z.eqb_eq in H4; exact H4].
Qed.

(* [p, p + n) inside one registered global below GT, decided. *)
Definition r4_agb (p n : Z) : bool :=
  existsb (fun q => (0 <=? fst q) && (fst q <=? p) && (p + n <=? fst q + snd q) && (fst q + snd q <=? AC.GT))
    AF.frame_AG.

Lemma r4_addr_of1 : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn He H. split; [exact Hp|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & HA). pose proof (HA 0 ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. exact Hb.
Qed.

Lemma r4_agb_ok : forall m p n, (forall a, in_globals AF.frame_AG a -> addressable m a 1) -> 0 <= n ->
  r4_agb p n = true -> addressable m p n.
Proof.
  intros m p n HAG Hn H. unfold r4_agb in H. apply existsb_exists in H as ([lo len] & Hin & Hc).
  cbn [fst snd] in Hc. apply andb_true_iff in Hc as [Hc H4]. apply andb_true_iff in Hc as [Hc H3].
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1, H2, H3, H4.
  apply r4_addr_of1; [lia | exact Hn | unfold AC.GT, APPMEM_END in *; lia |].
  intros i Hi. apply HAG. exists lo, len. split; [exact Hin | lia].
Qed.

(* The image bytes image_bytes reads are the segments' bytes, so a read-only range of them is in every memory
   that agrees with the read-only segments (R5's r5_image_nth / r5_ro_bytes). *)
Lemma r4_image_nth : forall n A bs, LImg.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  assert (Hs : LImg.image_bytes rsegs A (S n) =
               match seg_rom rsegs (wa A), LImg.image_bytes rsegs (A + 1) n with
               | Some b, Some bs => Some (b :: bs)
               | _, _ => None
               end) by reflexivity.
  rewrite Hs in H. clear Hs.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:Eb;
    destruct (LImg.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E;
    cbv beta iota in H; try discriminate H.
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply IH; [exact E | lia].
Qed.

Lemma r4_ro_bytes : forall mem A n bs,
  ro_agree rsegs mem ->
  (forall i, (i < n)%nat -> ro_addr rsegs (wa (A + Z.of_nat i)) = true) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  LImg.image_bytes rsegs A n = Some bs -> bytes_at rsegs mem A bs.
Proof.
  intros mem A n bs HRO Hro HA0 HAn Him.
  pose proof (LImg.image_bytes_length rsegs n A bs Him) as Hlen.
  split; [exact HA0|]. split; [rewrite Hlen; exact HAn|].
  intros i Hi. rewrite Hlen in Hi.
  transitivity (seg_rom rsegs (wa (A + Z.of_nat i))).
  - exact (HRO _ (Hro i Hi)).
  - exact (r4_image_nth n A bs Him i Hi).
Qed.

Definition r4_imgb (a : Z) (nb : list byte) : bool :=
  match LImg.image_bytes rsegs a (length nb) with
  | Some bs => if list_eq_dec (@bv_eq_dec 8) bs nb then true else false
  | None => false
  end.

Lemma r4_imgb_ok : forall a nb, r4_imgb a nb = true -> LImg.image_bytes rsegs a (length nb) = Some nb.
Proof.
  intros a nb H. unfold r4_imgb in H. destruct (LImg.image_bytes rsegs a (length nb)) as [bs|]; [|discriminate].
  destruct (list_eq_dec (@bv_eq_dec 8) bs nb) as [->|]; [reflexivity | discriminate].
Qed.

(* The checks on a row name at a: name_ok, 0 < a, below GT, inside one registered global, read-only, and the
   image's bytes. *)
Definition r4_nmb (a : Z) : bool :=
  r4_nokb (img_cstr a 16) && (0 <? a) && (a + Z.of_nat (length (img_cstr a 16)) <=? AC.GT) &&
  r4_agb a (Z.of_nat (length (img_cstr a 16))) &&
  forallb (fun k => ro_addr rsegs (wa (a + Z.of_nat k))) (seq 0 (length (img_cstr a 16))) &&
  r4_imgb a (img_cstr a 16).

Lemma r4_nmb_ok : forall m a, ro_agree rsegs m -> (forall x, in_globals AF.frame_AG x -> addressable m x 1) ->
  r4_nmb a = true ->
  RBx.name_ok (img_cstr a 16) /\ bytes_at rsegs m a (img_cstr a 16) /\
  addressable m a (Z.of_nat (length (img_cstr a 16))) /\ 0 < a /\
  a + Z.of_nat (length (img_cstr a 16)) <= AC.GT.
Proof.
  intros m a HRO HAG H. unfold r4_nmb in H.
  apply andb_true_iff in H as [H Him]. apply andb_true_iff in H as [H Hro].
  apply andb_true_iff in H as [H Hag]. apply andb_true_iff in H as [H Hgt].
  apply andb_true_iff in H as [Hok Hpos].
  apply Z.ltb_lt in Hpos. apply Z.leb_le in Hgt.
  split; [exact (r4_nokb_ok _ Hok)|].
  split.
  { apply (r4_ro_bytes m a (length (img_cstr a 16)) _ HRO); [| lia | unfold AC.GT in Hgt; lia | exact (r4_imgb_ok _ _ Him)].
    intros i Hi. rewrite forallb_forall in Hro. apply Hro. apply in_seq. lia. }
  split; [exact (r4_agb_ok m a (Z.of_nat (length (img_cstr a 16))) HAG ltac:(lia) Hag)|].
  split; [exact Hpos | exact Hgt].
Qed.

Definition r4_rowb (i : Z) : bool :=
  (RS6.has (rowb i) =? 0) || (RS6.rname (rowb i) =? 0) || r4_nmb (RS6.rname (rowb i)).

(* By computation on the 11 rows of BOX_CATALOGUE. *)
Lemma r4_rows_ok : forallb r4_rowb [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = true.
Proof. vm_compute. reflexivity. Qed.

(* The row-name clause of Inv_B8169c / RBE in every memory with the image's read-only bytes and the registered
   globals addressable (FRA gives both). *)
Lemma r4_rowname : forall (m : word -> option byte) inp,
  ro_agree rsegs m -> (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  RS6.has (rt_mb inp) <> 0 /\ RS6.rname (rt_mb inp) <> 0 ->
  RBx.name_ok (rt_nb inp) /\ bytes_at rsegs m (RS6.rname (rt_mb inp)) (rt_nb inp) /\
  addressable m (RS6.rname (rt_mb inp)) (Z.of_nat (length (rt_nb inp))) /\
  0 < RS6.rname (rt_mb inp) /\ RS6.rname (rt_mb inp) + Z.of_nat (length (rt_nb inp)) <= AC.GT.
Proof.
  intros m inp HRO HAG (H1 & H2). unfold rt_nb. unfold rt_mb in *.
  assert (Hi : 0 <= istar inp < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hin : In (istar inp) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
  pose proof (proj1 (forallb_forall _ _) r4_rows_ok _ Hin) as Hb. unfold r4_rowb in Hb.
  apply orb_true_iff in Hb as [Hb|Hb]; [apply orb_true_iff in Hb as [Hb|Hb]|].
  - apply Z.eqb_eq in Hb. contradiction.
  - apply Z.eqb_eq in Hb. contradiction.
  - exact (r4_nmb_ok m _ HRO HAG Hb).
Qed.

(* ---- the run lemma: an evt on the normalized memory, lifted to SR on the real configuration ---- *)
Section Run.
Context {fx : FPState}.

Lemma r4_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r4_wx Hro HE)
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

Section R4.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee checked_memset (MSET@0x81698), taken on its lib/B contract (asan_memset_c.v), never on its
   code. *)
Hypothesis MSET : MSC.asan_memset_contract.

(* The inner lists of the allocator laws this file reads, taken apart once each and picked by statement, not by
   position (a Theorem Labs lane 15:32Z: append-only at every level; a new generation touches these lemmas, not every site). *)
Lemma r4_fsp : forall H mem md FS,
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

Lemma r4_fsok : forall H mem md FS,
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

Lemma r4_store : forall H mem mem' md,
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
   spills [A + 40, A + 56) / [A + 336], the saved registers) and keeps every shadow byte readable (so RT_meta_write),
   given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still backed, and the
   frame_AG globals still addressable (R3's r3_fra).  W may contain frame bytes and the callee window. *)
Lemma r4_fra : forall g fr hb regs regs' mem mem' md W,
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
    HWsaved HWwin HAG' HWA' HFSR HIN1' HIN2' E2 E3 E4 E8 E9 E19 E26.
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
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
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
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HFSR Hfsrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r4_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
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

Lemma seg_R4 : Hcut B APIf ra (Inv_B8169c B APIf ra) -> Hcut B APIf ra (Inv_B8168c B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HCUR & HOUR & HIDB & HADR & H112 &
                    H312 & H264 & H56 & H184 & HAD544 & HAD2176 & H144 & H8 & Hr18 & HAD2624 &
                    H96 & H120 & H240 & H232 & H224 & H176 & H208 & H64 & HPRA & H152 & H160).
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
  pose proof (Hplace 2208 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the spill names the spill base A of register 9 *)
  destruct H112 as (A2 & HA2 & Hq112).
  assert (HA2e : A2 = A)
    by (apply (r4_spill_A regs mem 112 (fr + 2256) A A2 HA2 Hq112 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  destruct H312 as (A3 & HA3 & Hq312).
  assert (HA3e : A3 = A)
    by (apply (r4_spill_A regs mem 312 (fr + 544) A A3 HA3 Hq312 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A3.
  destruct H264 as (A4 & HA4 & Hq264).
  assert (HA4e : A4 = A)
    by (apply (r4_spill_A regs mem 264 (fr + 2624) A A4 HA4 Hq264 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  destruct H56 as (A5 & HA5 & Hq56).
  assert (HA5e : A5 = A)
    by (apply (r4_spill_A regs mem 56 (fr + 3040) A A5 HA5 Hq56 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A5.
  destruct H184 as (A6 & HA6 & Hq184).
  assert (HA6e : A6 = A)
    by (apply (r4_spill_A regs mem 184 (fr + 2368) A A6 HA6 Hq184 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A6.
  destruct H144 as (A7 & HA7 & Hq144).
  assert (HA7e : A7 = A)
    by (apply (r4_spill_A regs mem 144 (fr + 2176) A A7 HA7 Hq144 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A7.
  destruct H8 as (A8 & HA8 & Hq8).
  assert (HA8e : A8 = A)
    by (apply (r4_spill_A regs mem 8 (Sfr fr + 68) A A8 HA8 Hq8 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A8.
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + 3136 -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r4_fsp _ mem md FSb HAH Hw HFSr) as (HGT & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + 3136 -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  pose proof (r4_sf8 fr Hfrm) as HSf8.
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
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (r4_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (r4_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (r4_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  (* the frame is readable and writable; the 72 fragment-record bytes as one cell *)
  assert (Hfrd : forall a, fr <= a < fr + 3136 -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (r4_fsok _ mem md FSb HAH Hw HFSr a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + 3136)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  pose proof (r4_stk_rel mem (normalize rsegs mem) fr (fr + 3136) HR0 ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 2256) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs _ (fr + 2256) (fr + 2328) (fr + 3136) Hfs2 ltac:(lia)) as (Hfgs & _).
  destruct (stk_bytes rsegs _ (fr + 2256) (fr + 2328) Hfgs ltac:(lia)) as (fgb & Hfgl & Hfgb).
  assert (RWfg : rw_cells rsegs (normalize rsegs mem) (fr + 2256) [CB 72 fgb]).
  { replace 72%nat with (length fgb) by lia. apply r4_rw_CB; [exact Hfgb|].
    replace (Z.of_nat (length fgb)) with (fr + 2328 - (fr + 2256)) by lia. exact (r4_wr_stk _ _ _ Hfgs). }
  (* the fragment record address spilled at [A + 112], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 112) [C8 (Z_to_bv 64 (fr + 2256))]).
  { apply r4_ro8. unfold q64 in Hq112. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq112). }
  (* the memset premise of the entry cut, on the normalized memory *)
  pose proof (r4_addr_rel mem (normalize rsegs mem) (fr + 2256) 72 HR0 HADR) as ADR0.
  (* r4_evt's arithmetic premises *)
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2208 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P6 : 0 <= A) by lia.
  assert (P6b : A + 120 <= 2 ^ 64) by lia.
  assert (P7 : RT_HI <= fr + 2256) by (unfold RT_HI; lia).
  assert (P8 : app_mem (fr + 2256 + 7)) by (apply Happ'; lia).
  assert (P9 : app_mem (fr + 2256 + 72)) by (apply Happ'; lia).
  assert (P10 : fr + 2256 + 72 <= sp - 2208 \/ sp <= fr + 2256) by lia.
  unfold rg in Hr9.
  rewrite SEGS.
  apply (r4_run regs (Z_to_bv 64 0x8168c) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x8169c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       LF.munch [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       rw_cells rsegs m0' (fr + 2256) [CB 72 (repeat (Z_to_bv 8 0) 72)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r4_mkR_of.
    eapply evt_mono.
    + apply (r4_evt MSET) with (spv := sp) (Ab := A) (fg := fr + 2256) (lo := sp - FN_STACK) (fgb := fgb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P18' & P19' & P23' & P25' & P26' &
                  MUq & WMq & MIq & STq & ACq & SWq & RWq).
      exists R, (Z_to_bv 64 0x8169c), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P18'|]. split; [exact P19'|].
      split; [exact P23'|]. split; [exact P25'|]. split; [exact P26'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq | exact RWq].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K23 & K25 & K26 & MU0 & WM0 & ST0' & SW0' & RW0')
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
    pose proof (r4_stk_back mem' m0' (sp - FN_STACK) sp HRel ltac:(lia) ST0') as ST'.
    pose proof (r4_srw_back mem' m0' HRel SW0') as SW'.
    assert (HfgZ : bytes_at rsegs mem' (fr + 2256) (repeat (Z_to_bv 8 0) 72)).
    { destruct RW0' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      exact (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) Hb). }
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r4_not_out in Hx. destruct Hx as [Hx|Hx].
      - apply (r4_ba_rd mem' (fr + 2256) _ x HfgZ). rewrite repeat_length. lia.
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
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
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
          - exfalso. apply Hnok. apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + right; left. apply Hreal. lia.
            + right; left. lia. }
        destruct (r4_store ([] ++ g_H g) mem mem' md HAH Hmc Hwrit)
          as (HAH' & Hown' & Hstk' & Hhi').
        split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi'].
      - (* side arm: the frame is the FakeStack's *)
        destruct (Hfs (fr + 3135) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
        pose proof (Hfsb FS HwFS HFSr) as HFSfr.
        destruct (r4_fsp ([] ++ g_H g) mem md FS HAH HwFS HFSr)
          as (HGTFS & HFSend & HFSapp).
        assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
        { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q Hq (b & Hb).
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q) as [Ho|Hno].
          - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exact (RDW q Hno). }
        assert (Hmeta : forall q, fs_meta FS q ->
                  LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q).
        { intros q Hq. pose proof (r4_fs_meta_range FS q Hq) as Hqr.
          cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + AC.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + apply Hnfs. lia.
            + apply Hnok. right; left. lia. }
        destruct (a_fs_ok_store_AH _ _ _ _ _ [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]
                    ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree)
          as (HAH' & Hown' & Hstk' & Hhi').
        split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi']. }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = 392%nat).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r4_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + 392 - Sfr fr) with 392 by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r4_sa_lo a (r4_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
      apply (r4_addr_keep [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the slot window outside the frame is still addressable: no shadow byte is written *)
    assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      assert (Hsa : 2147450880 <= shadow_addr a < 17592186044416 + 2147450880).
      { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
      apply (r4_addr_keep [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' a 1 (HWA a Ha1 Ha2) MU).
      intros i Hi. replace (a + i) with a by lia.
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* ENT across the run (the writes are the fragment record and the callee window) and the model step *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x \/
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + 3136) \/
              (Sfr fr <= x < Sfr fr + 392)).
    { intros x Hx.
      destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno]; [left; exact Ho|].
      apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
      - right; right; left. lia.
      - right; left. lia. }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    assert (HENT' : ENT APIf g [] mem' md).
    { eapply ent_store with (W := [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]);
        try exact FF; try exact HENT; try exact HFRA; try exact MU; try exact HWcases;
        try exact HSTK'; try exact HHI'; try exact HOWNk. }
    assert (HENT'' : ENT APIf g [] mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* FSREC (side arm): the run writes nothing below stklo outside the frame body *)
    assert (HFSR : FSREC fr mem -> FSREC fr mem').
    { intros Hf. eapply fsrec_munch_lo with (W := [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]);
        [exact Hf | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |].
      intros x Hx Hnf. apply (proj2 (fr_outside_lib _ _)).
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* FRA's input facts: the input block is app memory below stklo <= S - SLOT_STACK < sp - 2208 and off the
       frame (fra_in_apart); the write set is app memory (fra_in_keep) *)
    assert (HAW : all_app [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]).
    { cbn [all_app]. split; [intros a Ha; apply Happ'; lia|].
      split; [intros a Ha; unfold app_mem; right; lia | exact I]. }
    assert (HINo : forall x, g_p g <= x < g_p g + g_n g ->
              LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x).
    { intros x Hx.
      destruct (fra_in_apart B APIf ra g fr [] regs mem md HFRA x Hx) as (_ & Hxlo & Hnfr & _).
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    destruct (fra_in_keep g mem mem' [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] Hinb Hinblk MU HAW
                (fun x Hx => proj2 (fr_outside_lib _ _) (HINo x Hx))) as (HIN1' & HIN2').
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r4_fra g fr [] regs regs'' mem mem' md [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]
               HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
        try assumption.
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. rewrite HbvA in Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx.
        destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno];
          [left; exact Ho | right; exact (RDW x Hno)]. }
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
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { unfold IDBr in *. change (RID (g_in g) 0) with (repeat (Z_to_bv 8 0) 38) in HIDB |- *.
      eapply fl_bytes; [exact HIDB | exact MU |]. rewrite repeat_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { unfold FGBr. change (RFG (g_in g) 0) with (repeat (Z_to_bv 8 0) 72). exact HfgZ. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq312 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq264 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq56 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq184 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq144 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq8 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [unfold rg in *; rewrite E18; exact Hr18|].
    split; [exact (sl_addr_keep mem mem' [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] (fr + 2624) 6
                     HAD2624 MU HAW)|].
    split; [unfold OUTA; exact (sl_addr_keep mem mem' [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]
                                  (fr + 544) 1492 HAD544 MU HAW)|].
    (* the A4 spills (adopt 5 / 6 / 9 of a working branch), above the write set *)
    assert (KSp : forall off v, 0 <= off <= 312 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A' & HA' & Hq).
      assert (HAe : A' = A)
        by (apply (r4_spill_A regs mem off v A A' HA' Hq Hr9); unfold APPMEM_END in HAPP; lia).
      subst A'. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (KSp 96 _ ltac:(lia) H96)|].
    split; [exact (KSp 120 _ ltac:(lia) H120)|].
    split; [exact (KSp 240 _ ltac:(lia) H240)|].
    split; [exact (KSp 232 _ ltac:(lia) H232)|].
    split; [exact (KSp 224 _ ltac:(lia) H224)|].
    split; [exact (KSp 176 _ ltac:(lia) H176)|].
    split; [exact (KSp 208 _ ltac:(lia) H208)|].
    split; [exact (KSp 64 _ ltac:(lia) H64)|].
    split.
    { apply (r4_pra fr regs regs'' mem mem'); [|exact HPRA].
      intros off v Hin Hs. apply (KSp off v); [clear -Hin; cbn [In] in Hin; lia | exact Hs]. }
    split; [exact (KSp 152 _ ltac:(lia) H152)|].
    (* [A + 112] = fr + 2256 (A4's 0x814c0), which the ld at 0x81690 read: the run does not store to (s1) *)
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq112 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the identity record's 38 bytes: their shadow bytes are not written *)
    split; [exact (sl_addr_keep mem mem' [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] (fr + 2176) 38
                     HAD2176 MU HAW)|].
    (* the fragment record's 72 bytes (adopt 10): the memset writes no shadow byte *)
    split; [exact (sl_addr_keep mem mem' [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] (fr + 2256) 72
                     HADR MU HAW)|].
    (* the row-name clause: image data, read off mem' (r4_rowname) *)
    split; [exact (r4_rowname mem' (g_in g) HRO' HAG')|].
    (* [A + 160] = fr + 32 (v1.9.0's A4 store, appended last to the cuts), above the write set *)
    exact (KSp 160 _ ltac:(lia) H160).
Qed.

End R4.
