(* Segment R4 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81578, 0x81584], Inv_A81578 -> Inv_A81588.
   rule 24: no function proved (a slot segment).  Four instructions: li a2,72 ; ld a0,48(s1) ; li a1,0 ;
   jal checked_memset (MSET@0x81584).  The spill [A + 48] holds fr + 2256 (0x814e0), so the call zeroes the 72
   fragment-record bytes at fr + 2256, which R3 marked usable in the frame shadow (S(fr) + 282 .. 290 = 00).
   r4_evt is the Lib-level run of the four instructions plus the call by its asan contract; seg_R4 lifts it to the
   cuts.  The write set of the segment is the fragment record [fr + 2256, fr + 2328) and the callee's stack window
   [sp - 2208, sp).  Ubsan twin: lib/U/Prog/Seg/R03.v (a working branch). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memset_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- byte, cell and footprint helpers (local copies of R3.v's) ---- *)

Lemma r4_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma r4_rd_rw : forall m A n l x, rw_cells rsegs m A [CB n l] -> A <= x < A + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A n l x ((Hwf & Hb) & _) Hx. cbn [cells_wf cell_wf cells_bytes cbytes] in Hwf, Hb.
  rewrite app_nil_r in Hb. destruct Hwf as (Hl & _).
  apply (r4_ba_rd m A l x Hb). rewrite Hl. exact Hx.
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

(* ---- the read-only image and the normalized memory ----
   Push 5b: a cut carries ro_agree, not mem_inv, but checked_memset's contract asks for mem_inv.  The call is
   therefore run on `normalize rsegs m` (which has mem_inv by construction) and brought back with ms_rel /
   ro_same (MemNorm.evt_normalize, as a1_req_evt in Seg/A1.v).  Each memory premise crosses mem_rel: bytes_at
   and mrd are unchanged by the normalization, and every cell the callee writes is at no read-only address,
   since every segment of the image ends below GT = 0x5fe000 and both the frame and the stack lie above it. *)
Definition r4_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma r4_rsegs_low : r4_tops rsegs 6283264 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r4_find_below : forall segs top x n s,
  r4_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r4_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r4_notro : forall a, 6283264 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. destruct (ro_addr rsegs (wa a)) eqn:E; [exfalso|reflexivity].
  unfold ro_addr in E.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:Es; [|discriminate E].
  destruct (r4_find_below rsegs 6283264 (bv_unsigned (wa a)) 1 s r4_rsegs_low Es ltac:(lia)) as [L|L];
    [|discriminate L].
  rewrite wa_unsigned in L by lia. lia.
Qed.

Lemma r4_notro_shadow : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. apply r4_notro. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia.
Qed.

Lemma r4_stk_norm : forall m m0 lo hi, mem_rel rsegs m m0 ->
  (forall x, lo <= x < hi -> ro_addr rsegs (wa x) = false) -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi REL HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (HR a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r4_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r4_sw_norm : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 _ REL (r4_notro_shadow a Ha)). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r4_sw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL HS a Ha. destruct (HS a Ha) as (Hv & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL (r4_notro_shadow a Ha)). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma r4_ac_norm : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj1 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma r4_ac_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in H |- *.
  do 16 (destruct H as (? & H)).
  do 16 (split; [apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption|]).
  apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

Lemma r4_rw_norm : forall m m0 A cs, mem_rel rsegs m m0 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs m0 A cs.
Proof.
  intros m m0 A cs REL HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj1 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_norm rsegs m m0 A _ REL Hw HR).
Qed.

Lemma r4_rw_back : forall m m0 A cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs REL ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 _ _ REL) Hb).
  - exact (wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

Lemma r4_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n REL (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

(* ---- the run: li a2,72 ; ld a0,48(s1) ; li a1,0 ; jal checked_memset by its asan contract.
   The cut gives ro_agree, not mem_inv (push 5b), so the call runs on the normalized memory
   (MemNorm.evt_normalize, as a1_req_evt in Seg/A1.v): its premises cross mem_rel, mem_inv of
   `normalize m` is mem_inv_normalize, and the post comes back with ms_rel / ro_same. ---- *)
Lemma r4_evt : asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A D lo : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> 0 <= D < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    rw_cells rsegs m (A + 48) [C8 (Z_to_bv 64 D)] ->
    rw_cells rsegs m D [CB 72 junk] -> addressable m D 72 -> end_in_app D 72 ->
    app_mem (D + 7) -> (D + 72 <= RT_LO \/ RT_HI <= D) -> (D + 72 <= spv - 2208 \/ spv <= D) ->
    6283264 <= D -> 6283264 <= lo ->
    stk rsegs m lo spv -> lo + 2208 <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81588) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 19 = s3 /\
         getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 18 = s2 /\ getr R 21 = s5 /\
         munch [(D, D + 72); (spv - 2208, spv)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
         rw_cells rsegs m' D [CB 72 (repeat (Z_to_bv 8 0) 72)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81578) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A D lo junk -> -> HA HD Hspv HLD RW HAD HE HA7 HRT HSEP HDGT HLGT ST HLO HHM HAE HAC HSW HRO.
  unfold asan_memset_contract, ASAN_MEMSET_K in MSET. cbv zeta in MSET.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (RWn : rw_cells rsegs (normalize rsegs m) D [CB 72 junk]).
  { apply (r4_rw_norm m _ D _ REL); [|exact RW].
    intros i Hi. cbn [cells_size csize] in Hi. apply r4_notro.
    pose proof (rw_cells_bound rsegs m D _ RW) as Hb.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hb. lia. }
  assert (STn : stk rsegs (normalize rsegs m) lo spv).
  { apply (r4_stk_norm m _ lo spv REL); [|exact ST]. intros x Hx. apply r4_notro. lia. }
  pose proof (r4_ac_norm m _ REL HAC) as ACn.
  pose proof (r4_sw_norm m _ REL HSW) as SWn.
  pose proof (r4_addr_rel m _ D 72 REL HAD) as HADn.
  step. step. step. step.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO).
    eapply MSET with (junk := junk) (lo := lo).
    - rewrite !MState.unsigned_lit by lia. exact RWn.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by lia. exact HADn.
    - rewrite !MState.unsigned_lit by lia. exact HE.
    - rewrite !MState.unsigned_lit by lia. right. exact HA7.
    - rewrite !MState.unsigned_lit by lia. exact HRT.
    - rewrite !MState.unsigned_lit by lia. exact HSEP.
    - rewrite !MState.unsigned_lit by lia. exact STn.
    - rewrite !MState.unsigned_lit by lia. lia.
    - exact HHM.
    - rewrite !MState.unsigned_lit by lia. exact HAE.
    - exact ACn.
    - exact SWn.
    - apply mem_inv_normalize. }
  intros ms' (s0' & PO & MR & RS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MUc & WMc & MIc & STc & RWc & HAC' & HSW').
  subst s0'.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply MState.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  unfold ASAN_MEMSET_K in MUc, STc.
  rewrite ED in MUc. rewrite E72 in MUc. rewrite Esp in MUc. rewrite Esp in STc.
  rewrite !MState.unsigned_lit in RWc by lia.
  change (Z.to_nat 72) with 72%nat in RWc. change (0 mod 256) with 0 in RWc.
  replace (ret_pc (Z_to_bv 64 0x81588)) with (Z_to_bv 64 0x81588) in MR
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct ms' as [R' F' pc' svc' resv' fc' mem' rom'].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  apply evt_done. exists R', mem'.
  split; [unfold MS; subst; reflexivity|].
  subst R'.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) mem' m0' REL Hmem RS MUc)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mem' m0' REL Hmem RS WMc)|].
  split; [exact (ro_agree_same rsegs m mem' HRO RS)|].
  split; [exact (r4_stk_back mem' m0' lo spv Hmem STc)|].
  split; [exact (r4_ac_back mem' m0' Hmem HAC')|].
  split; [exact (r4_sw_back mem' m0' Hmem HSW') | exact (r4_rw_back mem' m0' D _ Hmem RWc)].
Qed.

(* ---- seg_R4 on the cuts.  The run is sl_run_lib (Tac_b5.v) feeding r4_evt; FRA is moved across the write set
   (fragment record + callee window, both application memory) by the canonical Tac_slot.sl_fr_cl, the heap
   invariant by a_laws_store (real arm: every written byte is a_store_ok) or Tac_fs.a_fs_ok_store_AH (side arm:
   the frame is in the FakeStack), and the model by sl_fra_move. *)
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

Lemma r4_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma r4_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW -> in_shadow (Sfr fr + k).
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr k Happ Hk. rewrite <- r4_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma r4_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8). *)
Lemma r4_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* A spill read off the spill base A held in register 9 (both name the same 64-bit value). *)
Lemma r4_spillA : forall (regs : bvmap 5 word) m off v A, rg regs 9 A -> 0 <= A -> 0 <= off ->
  A + off + 8 <= 2 ^ 64 -> spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m off v A Hr HA Hoff HAo (A0 & HA0 & Hq).
  assert (HA0e : A0 = A); [|subst A0; exact Hq].
  pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
  pose proof (rg_eq64 regs 9 A0 A HA0 Hr) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* An addressable range stays addressable across a run that writes only application memory: its shadow bytes are
   not application memory. *)
Lemma r4_addr_keep_app : forall m m' p n lo1 hi1 lo2 hi2, addressable m p n ->
  munch [(lo1, hi1); (lo2, hi2)] m m' ->
  (forall a, lo1 <= a < hi1 -> app_mem a) -> (forall a, lo2 <= a < hi2 -> app_mem a) -> addressable m' p n.
Proof.
  intros m m' p n lo1 hi1 lo2 hi2 HA MU H1 H2.
  apply (r4_addr_keep _ m m' p n HA MU). intros i Hi.
  destruct HA as (_ & _ & _ & H). destruct (H i Hi) as (Ha & _).
  pose proof (shadow_of_app _ Ha) as Hs.
  cbn [outside]. split; [intros Hin; exact (app_not_shadow _ (H1 _ Hin) Hs)|].
  split; [intros Hin; exact (app_not_shadow _ (H2 _ Hin) Hs) | exact I].
Qed.

(* The exit's copy of an entry spill / frame cell the run does not write: s1 is kept (E9), the run's munch MU
   misses the cell (lia on the context's separations). *)
Ltac r4_keep_spill Hs :=
  lazymatch type of Hs with
  | spill ?regs ?m ?off ?v =>
      match goal with
      | Hr : rg regs 9 ?A, E9 : getr ?regs' 9 = getr regs 9, MU : LF.munch _ m ?m' |- _ =>
          let Hq := fresh "Hq" in
          pose proof (r4_spillA regs m off v A Hr ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hq;
          exists A; split; [unfold rg in *; rewrite E9; exact Hr|];
          unfold q64 in Hq |- *; eapply fl_bytes; [exact Hq | exact MU |]; rewrite length_le8;
          let x := fresh "x" in let Hx := fresh "Hx" in
          intros x Hx; cbn [LF.outside]; repeat split; lia
      end
  end.
Ltac r4_keep_cells Hc :=
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

Section R4.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MSET : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memset_c.asan_memset_contract.

(* The cuts are SlotInv.v's own (push 9, 8fc81dafc88): Inv_A81578 is R3's exit, Inv_A81588 is R5's entry.  Both
   carry the spills [A + 128] = fr + 544, [A + 168] = fr + 2624, [A + 152] = S(fr) + 68, [A + 144] = fr + 2688,
   [A + 192] = fr + 2768, [A + 280] = fr + 3040, [A + 240] = fr + 3056, the frame cells at fr + 2688 / 2768 /
   3040 / 3056, s5 = fr + 2176, s2 = mrow and our[]'s 6 bytes addressable, none of which this segment writes; the
   exit adds OUTA (out[] 1492 addressable) and the id record's 38 bytes addressable from the entry.
   This segment's write set is the 72 fragment bytes (inside the frame body) plus the callee's stack window,
   with no shadow write (r4_addr_keep_app), so FRA moves with the canonical Tac_slot.sl_fr_cl; ENT with
   ent_store + ent_mat. *)

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes no app byte outside the frame
   body below the real stack's low end, and nothing in the low image: the tp word is in the low image, and the
   class-6 flag byte and the slot's last word are inside the FakeStack, which a_laws_fs_place puts entirely
   below stklo.  (Tac_slot.fsrec_munch asks for EVERY app byte outside the frame body to be unwritten, which a
   segment that writes a callee stack window cannot give; the stklo bound is what this lane needs.) *)
Lemma r4_fsrec : forall hb mem mem' md W fr,
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

Lemma seg_R4 : Hcut B APIf ra (Inv_A81588 B APIf ra) -> Hcut B APIf ra (Inv_A81578 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HCUR & HOUR & HID & H48 & Hout & Hidad &
                    Hfgad & H128 & HPRO & H21 & H152 & H144 & H208 & Hidr & Hjnk & H280 & H240 & Hjy & Hscr &
                    H56 & H88 & H80 & H72 & H192 & H216 & H18).
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
  pose proof (Hplace 2208 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
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
  (* the three spills, read at the spill base A *)
  pose proof (r4_spillA regs mem 48 (fr + 2256) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H48) as Hq48.
  pose proof (r4_spillA regs mem 128 (fr + 544) A Hr9 ltac:(lia) ltac:(lia) ltac:(lia) H128) as Hq128.
  clear H128.
  (* the frame is readable and writable; the 72 fragment bytes as one cell *)
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists b, mrd rsegs mem (wa a) = Some b).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(lia))).
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_state _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hw HFSr) as (Hok & _).
      destruct Hok as (Hok1 & _). destruct (Hok1 a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  destruct (stk_split rsegs mem fr (fr + 2256) (fr + FRAME_BYTES) Hfstk ltac:(lia)) as (_ & Hfs2).
  destruct (stk_split rsegs mem (fr + 2256) (fr + 2328) (fr + FRAME_BYTES) Hfs2 ltac:(lia)) as (Hfgs & _).
  destruct (stk_bytes rsegs mem (fr + 2256) (fr + 2328) Hfgs ltac:(lia)) as (fgb & Hfgl & Hfgb).
  assert (RWfg : rw_cells rsegs mem (fr + 2256) [CB 72 fgb]).
  { replace 72%nat with (length fgb) by lia. apply r4_rw_CB; [exact Hfgb|].
    replace (Z.of_nat (length fgb)) with (fr + 2328 - (fr + 2256)) by lia. exact (r4_wr_stk _ _ _ Hfgs). }
  (* the spill [A + 48] = fr + 2256 as a read/write cell (the save area [A, A + 416) is in the slot window) *)
  assert (RW48 : rw_cells rsegs mem (A + 48) [C8 (Z_to_bv 64 (fr + 2256))]).
  { unfold q64 in Hq48. split; [split|].
    - cbn [cells_wf cell_wf]. split; exact I.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq48.
    - cbn [cells_size csize Nat.add]. destruct Hwin as (Hw0 & Hw1 & Hw).
      split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (Hw (A + 48 + i) ltac:(lia))). }
  (* r4_evt's arithmetic premises *)
  assert (P1 : 0 <= fr + 2256 < 2 ^ 64) by lia.
  assert (P2 : 0 <= sp < 2 ^ 64) by lia.
  assert (P3 : end_in_app (fr + 2256) 72) by (unfold end_in_app; right; apply Happ'; lia).
  assert (P4 : app_mem (fr + 2256 + 7)) by (apply Happ'; lia).
  assert (P5 : fr + 2256 + 72 <= RT_LO \/ RT_HI <= fr + 2256) by (right; unfold RT_HI; lia).
  assert (P6 : fr + 2256 + 72 <= sp - 2208 \/ sp <= fr + 2256) by lia.
  assert (P7 : sp - FN_STACK + 2208 <= sp) by lia.
  assert (P8 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P9 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P10 : 6283264 <= fr + 2256) by lia.
  assert (P11 : 6283264 <= sp - FN_STACK) by lia.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof Hr9 as Hr9'. unfold rg in Hr9'.
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81578) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81588 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 22 = getr regs 22 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 18 = getr regs 18 /\ getr R 21 = getr regs 21 /\
       LF.munch [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' /\
       LF.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
       asan_cells mem' /\ shadow_rw mem' /\
       rw_cells rsegs mem' (fr + 2256) [CB 72 (repeat (Z_to_bv 8 0) 72)])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply (r4_evt MSET) with (spv := sp) (A := A) (D := fr + 2256) (lo := sp - FN_STACK) (junk := fgb).
      all: try assumption.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P22' & P25' & P26' & P18' & P21' &
                  MUq & WMq & ROq & STq & ACq & SWq & RWq).
      exists R, (Z_to_bv 64 0x81588), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P22'|].
      split; [exact P25'|]. split; [exact P26'|]. split; [exact P18'|]. split; [exact P21'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq|]. split; [exact STq|].
      split; [exact ACq|]. split; [exact SWq | exact RWq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K22 & K25 & K26 & K18 & K21 & MU & WM & RO' & ST' & AC' & SW' & RWfg')
      Hreg Hmat.
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
    (* the write set is application memory: the fragment record and the callee window *)
    assert (HWapp1 : forall a, fr + 2256 <= a < fr + 2256 + 72 -> app_mem a) by (intros a Ha; apply Happ'; lia).
    assert (HWapp2 : forall a, sp - 2208 <= a < sp -> app_mem a) by (intros a Ha; unfold app_mem; right; lia).
    (* every written byte is readable after the run *)
    assert (RDW : forall x, ~ LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. apply r4_not_out in Hx. destruct Hx as [Hx|Hx].
      - apply (r4_rd_rw mem' (fr + 2256) 72 _ x RWfg'). lia.
      - destruct ST' as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
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
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
          - exfalso. apply Hnok. apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + right; left. apply Hreal. lia.
            + right; left. lia. }
        exact (ACw.a_laws_store _ _ _ _ _ ALAWS ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: the frame is the FakeStack's *)
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
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q) as [Ho|Hno].
          - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exact (RDW q Hno). }
        assert (Hmeta : forall q, fs_meta FS q ->
                  LF.outside [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q).
        { intros q Hq. pose proof (r4_fs_meta_range FS q Hq) as Hqr.
          cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                  ~ ACw.a_store_ok ([] ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FS <= q < FS + ACw.FS_SIZE) ->
                  ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hnok Hnfs Hnsh.
          destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] q) as [Ho|Hno].
          - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - exfalso. apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
            + apply Hnfs. lia.
            + apply Hnok. right; left. lia. }
        exact (a_fs_ok_store_AH _ _ _ _ _ [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]
                 ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit Hpres Hmeta Hagree). }
    destruct HAHS as (HAH' & HOWN' & HSTK' & HSHI').
    (* FRA at mem' *)
    assert (HDJ : rt_disjoint [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
        replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r4_fsh; [exact Happ' | lia]. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
    assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r4_ag_range a Ha) as Har.
      apply (r4_addr_keep [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia.
      assert (Hsa : 2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the slot window outside the frame stays addressable: W is app memory, so no shadow byte changes *)
    assert (HWA' : forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
                     addressable mem' a 1).
    { intros a H1 H2.
      apply (r4_addr_keep [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' a 1 (HWA a H1 H2) MU).
      intros i Hi. replace (a + i) with a by lia.
      assert (Happa : app_mem a) by (unfold app_mem; right; lia).
      assert (Hsh' : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
      assert (Hn1 : ~ (fr + 2256 <= shadow_addr a < fr + 2256 + 72)).
      { intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh']. apply Happ'. lia. }
      assert (Hn2 : ~ (sp - 2208 <= shadow_addr a < sp)).
      { intros Hin. apply (app_not_shadow (shadow_addr a)); [|exact Hsh']. unfold app_mem. right. lia. }
      cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the side-arm FakeStack record: its cells are below stklo, so below the callee window, and the fragment
       bytes it could meet are inside the frame body *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec0.
      apply (r4_fsrec ([] ++ g_H g) mem mem' md [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] fr Hrec0 HAH MU).
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hap Hnfr Hlo2. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* the window stays backed after the run *)
    assert (HWIN' : stk rsegs mem' (g_S g - AFw.SLOT_STACK) (g_S g)).
    { apply (r4_stk_tr [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] mem mem' _ _ Hwin MU WM).
      intros x Hx.
      destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno];
        [left; exact Ho | right; exact (RDW x Hno)]. }
    assert (HFRAm : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs'' mem mem' md
               [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] HFRA MU WM RO').
      - cbn [all_app]. split; [|split; [|exact I]].
        + intros a Ha. apply Happ'. lia.
        + intros a Ha. unfold app_mem. right. lia.
      - exact HDJ.
      - exact HAH'.
      - exact HSTK'.
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros A' HA' HA'r x Hx. cbn [LF.outside].
        assert (EA : A' = A) by (rewrite <- HbvA, HA'; symmetry; apply MState.unsigned_lit; exact HA'r).
        subst A'. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros A' HA' HA'r x Hx. cbn [LF.outside].
        assert (EA : A' = A) by (rewrite <- HbvA, HA'; symmetry; apply MState.unsigned_lit; exact HA'r).
        subst A'. split; [lia | split; [lia | exact I]].
      - exact HWIN'.
      - exact HREC'.
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
               [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] HENT HFRA MU).
      - intros x Hx.
        destruct (r4_out_dec [(fr + 2256, fr + 2256 + 72); (sp - 2208, sp)] x) as [Ho|Hno];
          [left; exact Ho|].
        apply r4_not_out in Hno. destruct Hno as [Hx1|Hx1].
        + right; right; left. lia.
        + right; left. lia.
      - exact HSTK'.
      - exact HSHI'.
      - intros a _ Hown. exact (proj2 (HOWN' a) Hown). }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split; [exact (r4_addr_keep_app mem mem' _ _ _ _ _ _ Hout MU HWapp1 HWapp2)|].
    split.
    { unfold IDBr in *. eapply fl_bytes; [exact HID | exact MU |].
      change (RID (g_in g) 0) with (repeat (Z_to_bv 8 0) 38). rewrite repeat_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    split.
    { unfold FGBr. change (RFG (g_in g) 0) with (repeat (Z_to_bv 8 0) 72).
      destruct RWfg' as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    split.
    { exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq128 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]]. }
    (* PRO (push 13B): the eight spills are above the frame, our[]'s shadow byte is no app byte, and the two
       write ranges (fragment record, callee window) are RcPro.rc_away *)
    split.
    { apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md _ A HFRA HPRO MU Hr9 ltac:(lia) ltac:(lia) E9).
      - intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | exact I]].
      - intros i Hi. pose proof (shadow_of_app (fr + 2624 + i) (Happ' (fr + 2624 + i) ltac:(lia))) as Hs.
        cbn [LF.outside].
        split; [intros Hin; exact (app_not_shadow _ (HWapp1 _ Hin) Hs)|].
        split; [intros Hin; exact (app_not_shadow _ (HWapp2 _ Hin) Hs) | exact I].
      - intros x Hx. apply r4_not_out in Hx. destruct Hx as [Hx|Hx].
        + apply (rc_away_frame B APIf ra g fr [] regs mem md x HFRA). lia.
        + apply (rc_away_hi B APIf ra g fr [] regs mem md x HFRA). lia. }
    (* s5, the spills [A + 152], [A + 144], [A + 192], [A + 280], [A + 240], the four frame cells at fr + 2688,
       fr + 2768, fr + 3040, fr + 3056, the id record's and our[]'s bytes addressable and s2 = mrow: none is in the
       write set (memset keeps s2 and s5; it writes no shadow byte) *)
    split; [unfold rg; rewrite E21; exact H21|].
    split; [r4_keep_spill H152|]. split; [r4_keep_spill H144|]. split; [r4_keep_spill H208|].
    split; [r4_keep_cells Hidr|]. split; [r4_keep_cells Hjnk|].
    split; [r4_keep_spill H280|]. split; [r4_keep_spill H240|].
    split; [r4_keep_cells Hjy|]. split; [r4_keep_cells Hscr|].
    (* push 10: [A + 48] (read by the memset call, not written), R1's [A + 56 / 88 / 80 / 72], A4's
       [A + 200 / 216], and the 72 fragment bytes addressable (memset writes the bytes, not their shadow) *)
    split; [r4_keep_spill H48|]. split; [r4_keep_spill H56|]. split; [r4_keep_spill H88|].
    split; [r4_keep_spill H80|]. split; [r4_keep_spill H72|]. split; [r4_keep_spill H192|].
    split; [r4_keep_spill H216|].
    split; [exact (r4_addr_keep_app mem mem' _ _ _ _ _ _ Hfgad MU HWapp1 HWapp2)|].
    split; [exact (r4_addr_keep_app mem mem' _ _ _ _ _ _ Hidad MU HWapp1 HWapp2)|].
    unfold rg; rewrite E18; exact H18.
Qed.

End R4.
