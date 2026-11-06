(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module names, addresses and numbers changed; 628 of its 880 lines of code are new or changed and 1457 lines of the source are left out. *)
(* Segment F23 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, patched image B): slot-plan-asan-ubsan section 2
   row F23 = 0x82844-0x82874, 13 instructions: the call of checked_memcpy (0x52164) at 0x82870 and `li s7,1` after
   it; FAIL branch 0x82844, no trap row, no instrumented-check row.  The segment runs from the cut 0x82844 (the
   return of reac_ctrl_headamp_record_verify at 0x82840) to the return cut 0x82878 (the entry of F24).

     0x82844  bne   a0,s7,82fa4    a0 = s7 = the record-verify result, so the branch is not taken
     0x82848  sd    s8,272(s1)     [A+272] = k
     0x8284c  mv    s8,s9          s8 = the sum flag
     0x82850  sb    zero,16(s3)    shadow byte S(fr) + 16 = 0
     0x82854  li    a0,4
     0x82858  sb    a0,17(s3)      shadow byte S(fr) + 17 = 4
     0x8285c  auipc a0,0xfff9f
     0x82860  addi  a1,a0,-1756    a1 = 0x21180, the 12 read-only bytes __const.check_ports.ports
     0x82864  li    a2,12
     0x82868  ld    s5,104(s1)     s5 = fr + 128, the ports words
     0x8286c  mv    a0,s5
     0x82870  jal   checked_memcpy copy the 12 bytes to fr + 128
     0x82874  li    s7,1           s7 = 1, the ports shadow value F25 stores (0x8288c sb s7,20(s3))

   The two shadow stores mark [fr + 128, fr + 140) usable: the byte at S(fr) + 16 = 0 covers the whole granule
   [fr + 128, fr + 136), the byte at S(fr) + 17 = 4 covers the first four bytes of [fr + 136, fr + 144).  That is
   what makes the copy's destination addressable, so the error path of the copy is not reached; the source
   [0x21180, 0x2118c) is a registered global, whose bytes FRA keeps addressable.  The 12 bytes are three int32
   -7, so the three ports words start at -7, -7, -7 -- the value F24's reac_ports_parse call leaves when the
   block is not a declaration.

   The write set of the whole segment is the two shadow bytes [S(fr) + 16, S(fr) + 18), the spill
   [A + 272, A + 280), the copy's destination [fr + 128, fr + 140) and the copy's own stack window
   [sp - 2224, sp).  FRA and ENT cross it with Tac_f23's tf_fra_ent.  The copy's contract
   (lib/B/Prog/asan_memcpy_c.v) is a Section Hypothesis; it asks for mem_inv, which no cut carries (push 5c), so
   the run is made on MemNorm.normalize and carried back by MemNorm.evt_normalize from FRA's ro_agree, as
   lib/B/Prog/Seg/F12.v does for the same callee.

   Entry cut: the official Inv_B82844_at of lib/B/Prog/SlotInv.v; its FTURN gives the frame bytes at Phi and, at
   50 <= flen (SlotInv.fturn_g), their 50-byte prefix.  Exit cut: the official Inv_B82878_at (FCUTP with LK, FTL,
   s6 = 1, IFS (S j), F27K, s7 = 1, [A + 184] = the fill flag, s5 = fr + 128 and the window facts above).
   Statement: S_F23 of the assembly forms. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv asan_memcpy_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_f23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
(* lib.Prog's chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this file's
   registers and mkst must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* The byte a `sb` writes, in whichever of its two forms the step tactic leaves. *)
Ltac f23_zb := first [ reflexivity | cbn; reflexivity | vm_compute; reflexivity ].

(* Fold the engine-form stack pointer `bv_unsigned (reg_get regs 2)` back to AC.aspZ regs. *)
Ltac fold_sp regs :=
  match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) end.

(* The `bne` of 0x82844 compares two copies of the same value, so it is not taken. *)
Ltac f23_bne :=
  first [ match goal with
          | |- context [negb (bv_eqb ?x ?x)] =>
              replace (negb (bv_eqb x x)) with false by (rewrite bv_eqb_refl; reflexivity)
          end
        | match goal with
          | |- context [bv_eqb ?x ?x] => replace (bv_eqb x x) with true by (symmetry; apply bv_eqb_refl)
          end ]; cbv iota.

(* ---- the 12 read-only bytes the copy reads: three int32 -7 at 0x21180 (__const.check_ports.ports), a
   registered global of frame_AG. ---- *)

Definition f23_src : list byte :=
  le4 (Z_to_bv 64 (-7)) ++ le4 (Z_to_bv 64 (-7)) ++ le4 (Z_to_bv 64 (-7)).

Lemma f23_src_len : length f23_src = 12%nat.
Proof. unfold f23_src. rewrite !length_app, !length_le4. reflexivity. Qed.

(* The turn's record bytes: t_g is 50 bytes, so its slices below 50 have their full length
   (lib/B/Prog/Seg/F26.v f26_bsl_len / f26_blk_len). *)
Lemma f23_bsl_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.
Lemma f23_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk. rewrite f23_bsl_len by lia. reflexivity. Qed.

Lemma f23_src_ro : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x21180 f23_src.
Proof. intros m Hm. apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]. Qed.

(* The three words of a copy of those bytes. *)
Lemma f23_src_u32 : forall m D, bytes_at rsegs m D f23_src ->
  u32 m D (-7) /\ u32 m (D + 4) (-7) /\ u32 m (D + 8) (-7).
Proof.
  intros m D H. unfold f23_src in H. unfold u32.
  apply (proj1 (bytes_at_app rsegs m D _ _)) in H. destruct H as (H1 & H2).
  rewrite length_le4 in H2. change (Z.of_nat 4) with 4 in H2.
  apply (proj1 (bytes_at_app rsegs m (D + 4) _ _)) in H2. destruct H2 as (H2 & H3).
  rewrite length_le4 in H3. change (Z.of_nat 4) with 4 in H3.
  replace (D + 4 + 4) with (D + 8) in H3 by lia.
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* The cell of a writable byte range (lib/B/Prog/Seg/F12.v f12_cb_rw). *)
Lemma f23_cb_rw : forall m a n bs, bytes_at rsegs m a bs -> length bs = n ->
  wr_at rsegs m a (Z.of_nat n) -> rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* ---- push 5c: the cuts carry ro_agree, not mem_inv, and the copy's contract asks for mem_inv.  These are
   lib/B/Prog/Seg/F12.v's moves to MemNorm.normalize and back, copied here (F12 is a segment file, not a helper
   file).  Every address they speak of is at or above GT, where no segment lies, so normalizing changes nothing
   there. ---- *)

Lemma f23_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f23_ro_ge_GT : forall x, AC.GT <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. assert (HGT : AC.GT = 0x5fe000) by reflexivity. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. assert (Ex : bv_unsigned (wa x) = x) by (rewrite wa_unsigned by lia; reflexivity).
  rewrite Ex in E.
  destruct (sl_find_below rsegs AC.GT x 1 s ltac:(vm_compute; reflexivity) E ltac:(lia)) as [L|L]; lia.
Qed.

Lemma f23_addr_norm : forall m p n, ro_agree rsegs m -> addressable m p n -> addressable (normalize rsegs m) p n.
Proof.
  intros m p n HRO (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m HRO)). exact Hb.
Qed.

Lemma f23_stk_norm : forall m lo hi, ro_agree rsegs m -> AC.GT <= lo -> stk rsegs m lo hi ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO Hlo (H1 & H2 & H). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false) by (apply f23_ro_ge_GT; lia).
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f23_shadow_rw_norm : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m HRO H a Ha. pose proof (mem_rel_normalize rsegs m HRO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f23_ro_ge_GT. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f23_cells_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply bytes_at_normalize; assumption.
Qed.

Lemma f23_rw_norm : forall m a cs, ro_agree rsegs m -> AC.GT <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HRO Ha ((Hw & Hb) & Hwr). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [split; [exact Hw | exact (bytes_at_normalize rsegs m a _ HRO Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) a _ REL Hwr).
  intros i Hi. apply f23_ro_ge_GT. destruct Hwr as (H0 & H1 & _). lia.
Qed.

Lemma f23_wr_norm : forall m a n, ro_agree rsegs m -> AC.GT <= a -> wr_at rsegs m a n ->
  wr_at rsegs (normalize rsegs m) a n.
Proof.
  intros m a n HRO Ha Hwr. pose proof (mem_rel_normalize rsegs m HRO) as REL.
  apply (wr_at_norm rsegs m (normalize rsegs m) a n REL Hwr).
  intros i Hi. apply f23_ro_ge_GT. destruct Hwr as (H0 & H1 & _). lia.
Qed.

Lemma f23_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f23_shadow_rw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL H a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f23_cells_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

(* A state related to an MS state by evt_normalize's ms_rel is that state with its own memory. *)
Lemma f23_ms_rel_MS : forall s R F pc fc rv m0 ro,
  ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* ---- the segment's write set: the two shadow bytes, the spill [A + 272], the copy's destination and the
   copy's own stack window. ---- *)

Definition f23_W (K A D sp : Z) : list Frame.ivl :=
  [(K + 16, K + 18); (A + 272, A + 280); (D, D + 12); (sp - ASAN_MEMCPY_K, sp)].

Lemma f23_out4 : forall K A D sp x,
  (x < K + 16 \/ K + 18 <= x) -> (x < A + 272 \/ A + 280 <= x) -> (x < D \/ D + 12 <= x) ->
  (x < sp - ASAN_MEMCPY_K \/ sp <= x) -> Frame.outside (f23_W K A D sp) x.
Proof.
  intros K A D sp x H1 H2 H3 H4. cbn [Frame.outside f23_W].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma f23_in4 : forall K A D sp x, ~ Frame.outside (f23_W K A D sp) x ->
  (K + 16 <= x < K + 18) \/ (A + 272 <= x < A + 280) \/ (D <= x < D + 12) \/
  (sp - ASAN_MEMCPY_K <= x < sp).
Proof.
  intros K A D sp x H.
  destruct (Z_lt_le_dec x (K + 16)) as [D1|D1];
    [|destruct (Z_lt_le_dec x (K + 18)) as [D2|D2]; [left; lia|]];
  (destruct (Z_lt_le_dec x (A + 272)) as [E1|E1];
    [|destruct (Z_lt_le_dec x (A + 280)) as [E2|E2]; [right; left; lia|]]);
  (destruct (Z_lt_le_dec x D) as [F1|F1];
    [|destruct (Z_lt_le_dec x (D + 12)) as [F2|F2]; [right; right; left; lia|]]);
  (destruct (Z_lt_le_dec x (sp - ASAN_MEMCPY_K)) as [G1|G1];
    [|destruct (Z_lt_le_dec x sp) as [G2|G2]; [right; right; right; lia|]]);
  exfalso; apply H; apply f23_out4; lia.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (lib/B/Prog/asan_memcpy_c.v), taken as a Section Hypothesis. *)
Hypothesis HMCPY : asan_memcpy_contract.

(* ---- The Lib-level run lemma: the ONE place of this file that uses the lazy-model lemma
   AsanLift.evt_SR_canon_lazy.  It is used once, by seg_F23, for the run 0x82844 -> 0x82870 (the call) ->
   0x82874 -> 0x82878 (f23_evt).  That run reads the spill [s1+104, s1+112) of the save area and the 12 read-only
   bytes [0x21180, 0x2118c); it writes the two shadow bytes [S(fr) + 16, S(fr) + 18), the spill [s1+272, s1+280),
   the copy's destination [fr + 128, fr + 140) and the copy's own stack window [sp - 2224, sp). *)
Lemma f23_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ---- The run 0x82844 -> 0x82870 (the call) -> 0x82874 -> 0x82878: the FAIL branch that is not taken, the spill
   store, the register move s8 = s9 (the sum flag), the two shadow stores that mark [D, D + 12) usable, the source
   address, the count, the spill load and the call.  The copy's post lands at the return pc 0x82874 with a0 = D,
   s5 = D and every callee-saved register unchanged; the last step sets s7 = 1. ---- *)
Lemma f23_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A K3 D v kk lo : Z) (junk : list byte),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 v -> s7v = Z_to_bv 64 v -> s3v = Z_to_bv 64 K3 ->
    s8v = Z_to_bv 64 kk ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    0 <= K3 -> K3 + FRAME_SHADOW <= 2 ^ 64 -> ASAN_K + 0x4240 <= K3 ->
    0 <= D -> D + 12 <= APPMEM_END -> D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 16 ->
    (forall t, 0 <= t <= 12 -> app_mem (D + t)) ->
    AC.GT <= D -> D + 12 <= A -> K3 + 18 <= A -> K3 + 18 <= lo ->
    (K3 + 18 <= D \/ D + 12 <= K3 + 16) ->
    0 <= kk < 2 ^ 64 ->
    wr_at rsegs m (K3 + 16) 2 ->
    wr_at rsegs m (A + 272) 8 ->
    shadow_rw m ->
    (forall mm, munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm -> wmono rsegs m mm ->
       (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
       asan_cells mm /\ shadow_rw mm) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 D)) ->
    rw_cells rsegs m D [CB 12 junk] ->
    addressable m 0x21180 12 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 12 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    bv_unsigned sp <= A ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3v s4 (Z_to_bv 64 D) s6v (Z_to_bv 64 1) s9 s9 s10 s11
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82878) fc None m' (seg_rom rsegs)
         /\ munch (f23_W K3 A D (bv_unsigned sp)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' D f23_src
         /\ q64 m' (A + 272) kk
         /\ b8 m' (K3 + 16) 0 /\ b8 m' (K3 + 17) 4)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
              t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82844) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
    t3 t4 t5 t6 Fr fc m A K3 D v kk lo junk -> -> -> -> ->
    HA0 HA1 HK0 HK1 HKlow HD0 HDE HD8 HDK HappD HGTD HDA HKA HKlo HdjKD Hkk
    HWRsh HWRsp HSWm HRTnew H104 HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HspA.
  pose proof FRAME_SHADOW_val as HFSv.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold ASAN_MEMCPY_K in Hlo1; lia).
  (* the FAIL branch at 0x82844 is not taken: a0 and s7 both hold the record-verify result *)
  step. f23_bne.
  (* 0x82848 sd s8,272(s1) *)
  assert (HS272 : store_ok rsegs m (wa (A + 272)) 8 = true).
  { replace (A + 272) with (A + 272 + 0) by lia.
    apply (wr_at_store_ok rsegs m (A + 272) 8 0 8%nat HWRsp); [lia | cbn; lia]. }
  step.
  (* 0x8284c mv s8,s9 *)
  step.
  (* 0x82850 sb zero,16(s3) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS16 : store_ok rsegs mm (wa (K3 + 16)) 1 = true) by
      (replace (K3 + 16) with (K3 + 16 + 0) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 16) 2 0 1%nat);
       [repeat apply wr_at_write; exact HWRsh | lia | cbn; lia])
  end.
  step.
  (* 0x82854 li a0,4 *)
  step.
  (* 0x82858 sb a0,17(s3) *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS17 : store_ok rsegs mm (wa (K3 + 17)) 1 = true) by
      (replace (K3 + 17) with (K3 + 16 + 1) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 16) 2 1 1%nat);
       [repeat apply wr_at_write; exact HWRsh | lia | cbn; lia])
  end.
  step.
  (* the memory after the three stores: the write set, the readable cells, the two new shadow bytes and the
     12 bytes at D marked usable *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU3 : munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm) by
      (repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; slia ]);
       apply munch_refl);
    assert (WM3 : wmono rsegs m mm) by (repeat apply wmono_write; apply wmono_refl);
    assert (ST3 : stk rsegs mm lo (bv_unsigned sp)) by
      (repeat (apply stk_write; [ | lia | simpl_sizes; lia ]); exact HST);
    assert (MI3 : mem_inv rsegs mm) by
      (apply mem_inv_store; [|simpl_sizes; exact HS17];
       apply mem_inv_store; [|simpl_sizes; exact HS16];
       apply mem_inv_store; [|simpl_sizes; exact HS272]; exact HMI);
    assert (B16 : b8 mm (K3 + 16) 0) by
      (apply tf_wother; [f23_zb | | lia | lia | lia];
       apply tf_wsame; [f23_zb | lia | lia]);
    assert (B17 : b8 mm (K3 + 17) 4) by
      (apply tf_wsame; [f23_zb | lia | lia]);
    assert (Q272 : q64 mm (A + 272) kk) by
      (unfold q64;
       repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
       apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
    assert (RD104 : ov_read_bytes rsegs mm (wa (A + 104)) 8 = Some (le8 (Z_to_bv 64 D))) by
      (apply tf_rd8;
       [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact H104
       | apply length_le8 ]);
    assert (RW3 : rw_cells rsegs mm D [CB 12 junk]) by
      (repeat (apply rw_cells_frame; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact HRWD);
    assert (AS3 : addressable mm 0x21180 12) by
      (apply (tf_addr_munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm 0x21180 12 HADS MU3);
       intros i Hi;
       assert (Hsh : ASAN_K + 0x4230 <= shadow_addr (0x21180 + i) <= ASAN_K + 0x4231)
         by (unfold shadow_addr; Z.div_mod_to_equations; lia);
       cbn [Frame.outside];
       split; [lia|]; split; [unfold HIGHMEM_BEG, ASAN_K in *; lia | exact I]);
    assert (AD3 : addressable mm D 12) by
      (apply (tf_addr_sh mm D 12); [lia | lia | lia | exact HD8 | intros t Ht; apply HappD; lia |];
       intros t Ht;
       assert (Esh : shadow_addr D = K3 + 16) by (unfold shadow_addr; lia);
       rewrite Esh;
       destruct (Z_lt_le_dec t 8) as [Hlt|Hge];
       [ exists 0; replace (K3 + 16 + t / 8) with (K3 + 16) by (Z.div_mod_to_equations; lia);
         split; [exact B16|]; split; [lia | left; reflexivity]
       | exists 4; replace (K3 + 16 + t / 8) with (K3 + 17) by (Z.div_mod_to_equations; lia);
         split; [exact B17|]; split; [lia | right; Z.div_mod_to_equations; lia] ]);
    assert (RT3 : asan_cells mm /\ shadow_rw mm) by
      (apply (HRTnew mm MU3 WM3); intros a Hin;
       assert (Hab : 0 <= a < 2 ^ 64) by
         (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia);
       destruct (Z.eq_dec a (K3 + 16)) as [->|Hne16];
       [ exact (tf_ba_rd mm (K3 + 16) [Z_to_bv 8 0] (K3 + 16) B16 ltac:(cbn [length]; lia)) |];
       destruct (Z.eq_dec a (K3 + 17)) as [->|Hne17];
       [ exact (tf_ba_rd mm (K3 + 17) [Z_to_bv 8 4] (K3 + 17) B17 ltac:(cbn [length]; lia)) |];
       destruct (HSWm a Hin) as (_ & b & Hb); exists b; unfold mrd in *;
       rewrite (MU3 (wa a)); [exact Hb|];
       rewrite wa_unsigned by lia; cbn [Frame.outside]; split; [lia|]; split;
         [ unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin;
           unfold HIGHMEM_BEG in HAhi; lia
         | exact I ])
  end.
  destruct RT3 as (AC3 & SW3).
  (* 0x8285c auipc a0,0xfff9f ; 0x82860 addi a1,a0,-1756 (a1 = 0x21180) ; 0x82864 li a2,12 ;
     0x82868 ld s5,104(s1) ; 0x8286c mv a0,s5 ; 0x82870 jal checked_memcpy *)
  do 6 step.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 0x21180) = 0x21180) by reflexivity.
  assert (E12 : bv_unsigned (Z_to_bv 64 12) = 12) by reflexivity.
  pose proof HMCPY as HM. unfold asan_memcpy_contract, ASAN_MEMCPY_K in HM. cbv zeta in HM.
  eapply evt_cut.
  { eapply HM with (src := f23_src) (junk := junk) (lo := lo) (a1 := Z_to_bv 64 0x21180).
    all: rewrite ?ED, ?ES, ?E12.
    - exact (f23_src_ro _ MI3).
    - rewrite f23_src_len. reflexivity.
    - change (Z.to_nat 12) with 12%nat. exact RW3.
    - right; left. unfold AC.GT in HGTD. lia.
    - clear; lia.
    - exact AS3.
    - exact AD3.
    - right. unfold app_mem, LOWMEM_END. left. lia.
    - right. apply HappD. lia.
    - right. split; [unfold app_mem, LOWMEM_END; left; lia | apply HappD; lia].
    - right. exact HRTD.
    - exact HdjDW.
    - left. unfold ASAN_MEMCPY_K, HIGHMEM_BEG in *. lia.
    - exact ST3.
    - unfold ASAN_MEMCPY_K in Hlo1. lia.
    - exact Hlo2.
    - exact Hspa.
    - exact AC3.
    - exact SW3.
    - exact MI3. }
  intros ms2 Hp. unfold asan_memcpy_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MUc & WMc & MIc & STc & RWc & BSc & ACc & SWc).
  subst ms2.
  replace (ret_pc (Z_to_bv 64 534644)) with (Z_to_bv 64 534644)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  (* 0x82874 li s7,1 *)
  step.
  apply evt_done.
  exists (Z_to_bv 64 534644), (Z_to_bv 64 D), a1', a2', a3', a4', a5', a6', a7',
         t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { eapply munch_trans.
    - apply (munch_weaken [(K3 + 16, K3 + 18); (A + 272, A + 280)]); [|exact MU3].
      unfold sub_fp, f23_W, ASAN_MEMCPY_K. cbn [Frame.outside].
      intros x (Hx1 & Hx2 & _). split; [lia|]. split; [lia | exact I].
    - apply (munch_weaken [(bv_unsigned (Z_to_bv 64 D),
                            bv_unsigned (Z_to_bv 64 D) + bv_unsigned (Z_to_bv 64 12));
                           (bv_unsigned sp - ASAN_MEMCPY_K, bv_unsigned sp)]); [|exact MUc].
      unfold sub_fp, f23_W. cbn [Frame.outside].
      intros x (_ & _ & Hx3 & Hx4 & _). rewrite ED, E12. split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WM3 WMc)|].
  split; [exact MIc|].
  split; [exact STc|].
  split; [exact ACc|].
  split; [exact SWc|].
  split.
  { rewrite <- ED. exact (tf_cb_bytes m' _ _ _ RWc). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Q272 | exact MUc |].
    rewrite length_le8. intros x Hx. cbn [Frame.outside].
    rewrite ED, E12. split; [lia|]. split; [unfold ASAN_MEMCPY_K; lia | exact I]. }
  split.
  { unfold b8 in *. eapply fl_bytes; [exact B16 | exact MUc |].
    cbn [length]. intros x Hx. cbn [Frame.outside].
    rewrite ED, E12. split; [lia|].
    split; [unfold ASAN_MEMCPY_K, HIGHMEM_BEG in *; lia | exact I]. }
  { unfold b8 in *. eapply fl_bytes; [exact B17 | exact MUc |].
    cbn [length]. intros x Hx. cbn [Frame.outside].
    rewrite ED, E12. split; [lia|].
    split; [unfold ASAN_MEMCPY_K, HIGHMEM_BEG in *; lia | exact I]. }
Qed.

(* ---- The segment: S_F23, from the official Inv_B82844_at to the official Inv_B82878_at (F24's entry). ---- *)
Lemma seg_F23 : forall j : nat, Hat B APIf ra (Inv_B82878_at B APIf ra) j -> Hat B APIf ra (Inv_B82844_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & H20 & HFM &
    H10 & H18 & H23 & H24 & Hphi0 & Hphi50 & Hflen & Hkb & Hblk & Hbsl & H25 & Happ & Hdj & HFTURN & HIFS).
  (* the 50-byte prefix of the frame bytes at Phi, from FTURN at 50 <= flen *)
  pose proof (fturn_g g j phi regs mem HFTURN Hflen) as Hphig.
  subst c. rewrite SEGS.
  (* at 50 <= flen the cut's live block is (phi, flen) *)
  rewrite (tf_asize (flen g j) Hflen) in HFRA, HENT.
  pose proof HLK as HLK0. destruct HLK0 as (Hj255 & Hs240 & HOURb & HFLI).
  pose proof HFLI as HFLI0.
  destruct HFLI0 as (H27 & P168 & P96 & P112 & P120 & P128 & P136 & P144 & P152 & P280 & P160 & P176 & P192 &
    P200 & P216 & P208 & P104 & P256 & P264 & P288 & P296 & P304 & HadOur & HstkF & (HRid & HRfg & HRfst) &
    HKNT & P168b & P88).
  pose proof HFM as HFM0. destruct HFM0 as (M184 & M24 & M22 & M25 & M312).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwlo & Hwstk).
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  destruct (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGT & Happfr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr40q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof HRT as HRT0. destruct HRT0 as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH).
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happfr fr ltac:(lia)) as H1. pose proof (Happfr (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the frame's FRAME_SHADOW shadow bytes are shadow addresses, below the high application memory *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happfr _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HK3b : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as H2.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1, H2.
    unfold LOWMEM_END, HIGHMEM_BEG. lia. }
  assert (HDK : (fr + 128) / 8 + ASAN_K = Sfr fr + 16).
  { unfold Sfr, shadow_addr. replace (fr + 128) with (128 + (fr / 8) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (HD8 : (fr + 128) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HdjKD : Sfr fr + 18 <= fr + 128 \/ fr + 128 + 12 <= Sfr fr + 16).
  { pose proof (HshIS (Sfr fr + 16) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 17) ltac:(lia)) as H2.
    pose proof (Happfr (fr + 128) ltac:(lia)) as H3. pose proof (Happfr (fr + 139) ltac:(lia)) as H4.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HKA : Sfr fr + 18 <= A) by (unfold HIGHMEM_BEG in *; lia).
  assert (HKlo : Sfr fr + 18 <= AC.aspZ regs - FN_STACK) by (unfold HIGHMEM_BEG in *; lia).
  assert (HKlow : ASAN_K + 0x4240 <= Sfr fr).
  { unfold Sfr, shadow_addr, ASAN_K in *. unfold AC.GT in HGT. Z.div_mod_to_equations. lia. }
  assert (HDA : fr + 128 + 12 <= A) by lia.
  assert (HGTD : AC.GT <= fr + 128) by (unfold AC.GT in *; lia).
  assert (HDE : fr + 128 + 12 <= APPMEM_END).
  { pose proof (Happfr (fr + 139) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1. unfold APPMEM_END. lia. }
  assert (HspA : AC.aspZ regs <= A) by lia.
  pose proof (Hplace ASAN_MEMCPY_K ltac:(unfold ASAN_MEMCPY_K, FN_STACK; lia)) as Hfrsep.
  (* the spills the run reads, at the cut's own spill base *)
  assert (HAE : 0 <= A < APPMEM_END) by (unfold APPMEM_END in *; lia).
  pose proof (tf_spill_q regs mem A 104 (fr + 128) Hr9 HAE ltac:(lia) P104) as H104.
  (* the writable ranges the run stores into *)
  assert (HWRsh : wr_at rsegs mem (Sfr fr + 16) 2).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|].
    intros i Hi. destruct (HSW0 (Sfr fr + 16 + i) (HshIS (Sfr fr + 16 + i) ltac:(lia))) as (Hw & _).
    exact Hw. }
  assert (HWRsp : wr_at rsegs mem (A + 272) 8)
    by (apply (tf_wr_of_stk mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  (* the copy's destination: present (the frame body is byte-backed) and writable *)
  destruct (tf_stk_bytes mem fr (fr + FRAME_BYTES) (fr + 128) 12 HstkF ltac:(lia) ltac:(lia) ltac:(lia))
    as (junk & Hjb & Hjl).
  assert (HRWD : rw_cells rsegs mem (fr + 128) [CB 12 junk])
    by (apply f23_cb_rw; [exact Hjb | exact Hjl |
        change (Z.of_nat 12) with 12; apply (tf_wr_of_stk mem fr (fr + FRAME_BYTES)); [exact HstkF | lia | lia | lia]]).
  (* the copy's source: the registered global at 0x21180 *)
  assert (HADS : addressable mem 0x21180 12).
  { split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
    intros i Hi.
    assert (Hin : in_globals AF.frame_AG (0x21180 + i)).
    { exists 0x21180, 12. split; [unfold AF.frame_AG; apply in_cons; apply in_cons; apply in_eq | lia]. }
    destruct (HAG (0x21180 + i) Hin) as (_ & _ & _ & Hb).
    pose proof (Hb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0. }
  (* the facts the run reads, on the normalized memory it starts from, and the runtime cells after the
     shadow stores *)
  pose proof (mem_rel_normalize rsegs mem Hro) as REL0.
  assert (HSW0n : shadow_rw (normalize rsegs mem)) by exact (f23_shadow_rw_norm mem Hro HSW0).
  assert (HWRshN : wr_at rsegs (normalize rsegs mem) (Sfr fr + 16) 2).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|].
    intros i Hi. destruct (HSW0n (Sfr fr + 16 + i) (HshIS (Sfr fr + 16 + i) ltac:(lia))) as (Hw & _).
    exact Hw. }
  assert (HRTnewN : forall mm, munch [(Sfr fr + 16, Sfr fr + 18); (A + 272, A + 280)]
            (normalize rsegs mem) mm -> wmono rsegs (normalize rsegs mem) mm ->
            (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
            asan_cells mm /\ shadow_rw mm).
  { intros mm MU WM HSH. split.
    - apply (asan_cells_kept [(Sfr fr + 16, Sfr fr + 18); (A + 272, A + 280)]
               (normalize rsegs mem) mm (f23_cells_norm mem Hro HAC0) MU).
      pose proof (HshIS (Sfr fr + 16) ltac:(lia)) as H1.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1.
      unfold RT_LO, RT_HI. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - intros a Ha. split; [apply WM; exact (proj1 (HSW0n a Ha)) | exact (HSH a Ha)]. }
  (* run the segment *)
  apply (f23_run_lib regs (Z_to_bv 64 0x82844) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82878 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\
       getr R0 26 = getr regs 26 /\ getr R0 27 = getr regs 27 /\
       getr R0 21 = Z_to_bv 64 (fr + 128) /\ getr R0 23 = Z_to_bv 64 1 /\
       getr R0 24 = getr regs 25 /\
       munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
       bytes_at rsegs mem' (fr + 128) f23_src /\
       q64 mem' (A + 272) (t_k (g_in g) j) /\
       b8 mem' (Sfr fr + 16) 0 /\ b8 mem' (Sfr fr + 17) 4)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the copy's contract asks for mem_inv, which the cut does not carry (push 5c): run f23_evt on the
       normalized memory and carry the run back to mem by MemNorm.evt_normalize from FRA's ro_agree *)
    eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (evt_normalize rsegs); [exact f23_wx | exact Hro |].
      eapply f23_evt with (A := A) (K3 := Sfr fr) (D := fr + 128) (v := t_want_v (g_in g) j)
        (kk := t_k (g_in g) j)
        (lo := AC.aspZ regs - FN_STACK) (junk := junk).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in H10; exact H10.
      - unfold rg in H23; exact H23.
      - unfold rg in Hr19; exact Hr19.
      - unfold rg in H24; exact H24.
      - lia.
      - unfold APPMEM_END in *; lia.
      - unfold LOWMEM_END in *; lia.
      - unfold HIGHMEM_BEG in *; lia.
      - exact HKlow.
      - lia.
      - exact HDE.
      - exact HD8.
      - exact HDK.
      - intros t Ht. apply Happfr. lia.
      - exact HGTD.
      - exact HDA.
      - exact HKA.
      - exact HKlo.
      - exact HdjKD.
      - lia.
      - exact HWRshN.
      - apply (f23_wr_norm mem (A + 272) 8 Hro ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia) HWRsp).
      - exact HSW0n.
      - exact HRTnewN.
      - exact (bytes_at_normalize rsegs mem _ _ Hro H104).
      - apply (f23_rw_norm mem _ _ Hro); [unfold AC.GT in *; lia | exact HRWD].
      - exact (f23_addr_norm mem _ _ Hro HADS).
      - exact (mem_inv_normalize rsegs mem).
      - fold_sp regs. apply (f23_stk_norm mem _ _ Hro);
          [unfold AC.GT, HIGHMEM_BEG in *; lia | exact Hwstk].
      - fold_sp regs. unfold ASAN_MEMCPY_K, FN_STACK in *. lia.
      - unfold HIGHMEM_BEG, FN_STACK in *. lia.
      - fold_sp regs. lia.
      - unfold RT_HI, AC.GT in *. lia.
      - fold_sp regs. unfold ASAN_MEMCPY_K in *. lia.
      - fold_sp regs. exact HspA. }
    { intros ms' (s0' & (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4'
                  & t5' & t6' & m' & E & MU & WM & MI' & ST' & AC' & SW' & HbD & HQ & HB16 & HB17)
                & REL & SAME).
      subst s0'.
      destruct (f23_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
      eexists _, (Z_to_bv 64 0x82878), (ms_mem ms'). split; [exact Ems|].
      split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
      split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m' REL0 HREL SAME MU)|].
      split; [exact (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m' REL0 HREL SAME WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs (ms_mem ms') m' HREL)|].
      split; [exact (f23_stk_back (ms_mem ms') m' _ _ HREL ST')|].
      split; [exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HbD)|].
      split; [unfold q64 in *; exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HQ)|].
      split; [unfold b8 in *; exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HB16)
             |unfold b8 in *; exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HB17)]. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er22 & Er26 &
      Er27 & Er21 & Er23 & Er24 & MU & WM & HroM & ST' & HbD & HQ & HB16 & HB17) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr21 : getr regs' 21 = Z_to_bv 64 (fr + 128)) by (rewrite Hreg; exact Er21).
    assert (Fr23 : getr regs' 23 = Z_to_bv 64 1) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 25) by (rewrite Hreg; exact Er24).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the write set: clear of the runtime's cells, and the addresses it misses *)
    assert (HGTW : forall lo hi, In (lo, hi) (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) -> AC.GT <= lo).
    { intros lo hi Hin. cbn [f23_W In] in Hin.
      destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
        unfold AC.GT, LOWMEM_END, HIGHMEM_BEG, ASAN_MEMCPY_K in *; lia. }
    assert (Hrtdj : rt_disjoint (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs))).
    { apply tf_rt_dj4; unfold AC.GT, LOWMEM_END, HIGHMEM_BEG, ASAN_MEMCPY_K in *; lia. }
    (* FRA and ENT cross the segment's write set *)
    assert (HCL : forall q, ~ Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) q ->
              (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
              (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
              (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)).
    { intros q Hq. destruct (f23_in4 (Sfr fr) A (fr + 128) (AC.aspZ regs) q Hq) as [H1|[H1|[H1|H1]]].
      - right; left. lia.
      - right; right; right. rewrite HbvA. lia.
      - left. lia.
      - right; right; left. unfold ASAN_MEMCPY_K, FN_STACK in *. lia. }
    assert (HRD : forall q, ~ Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) q ->
              exists b, mrd rsegs mem' (wa q) = Some b).
    { intros q Hq. destruct (f23_in4 (Sfr fr) A (fr + 128) (AC.aspZ regs) q Hq) as [H1|[H1|[H1|H1]]].
      - destruct (Z.eq_dec q (Sfr fr + 16)) as [->|Hne].
        + exact (tf_ba_rd mem' (Sfr fr + 16) [Z_to_bv 8 0] (Sfr fr + 16) HB16 ltac:(cbn [length]; lia)).
        + assert (Eq : q = Sfr fr + 17) by lia. subst q.
          exact (tf_ba_rd mem' (Sfr fr + 17) [Z_to_bv 8 4] (Sfr fr + 17) HB17 ltac:(cbn [length]; lia)).
      - unfold q64 in HQ.
        apply (tf_ba_rd mem' (A + 272) _ q HQ). rewrite length_le8. lia.
      - apply (tf_ba_rd mem' (fr + 128) f23_src q HbD). rewrite f23_src_len. lia.
      - destruct ST' as (_ & _ & HS).
        destruct (HS q ltac:(unfold ASAN_MEMCPY_K, FN_STACK in *; lia)) as (_ & b & Hb).
        exists b. exact Hb. }
    destruct (tf_fra_ent B APIf ra empty FF g fr (hb1 phi (flen g j)) regs mem mem' md
                (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) HFRA HENT MU WM Hrtdj HroM HCL HRD)
      as (HFRA' & HENT').
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs' mem' md md' HFRA');
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* what the exit cut names, moved to the post memory *)
    assert (Hout : forall x, (x < Sfr fr + 16 \/ Sfr fr + 18 <= x) -> (x < A + 272 \/ A + 280 <= x) ->
              (x < fr + 128 \/ fr + 140 <= x) ->
              (x < AC.aspZ regs - ASAN_MEMCPY_K \/ AC.aspZ regs <= x) ->
              Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) x).
    { intros x H1 H2 H3 H4. apply f23_out4; lia. }
    assert (HoutA : forall x, A <= x -> x < A + 272 -> Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) x).
    { intros x Hx1 Hx2. apply Hout; [right; unfold HIGHMEM_BEG in *; lia | lia | right; lia |
        right; unfold ASAN_MEMCPY_K in *; lia]. }
    assert (HoutA2 : forall x, A + 280 <= x -> x < A + 448 ->
              Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) x).
    { intros x Hx1 Hx2. apply Hout; [right; unfold HIGHMEM_BEG in *; lia | right; lia | right; lia |
        right; unfold ASAN_MEMCPY_K in *; lia]. }
    assert (Hspkeep : forall off v, 0 <= off <= 264 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs.
      eapply tf_spill_keep; [exact Hr9 | exact Fr9 | exact HAE | lia | exact Hs | exact MU |].
      intros x Hx. apply HoutA; lia. }
    assert (Hspkeep2 : forall off v, 280 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs.
      eapply tf_spill_keep; [exact Hr9 | exact Fr9 | exact HAE | lia | exact Hs | exact MU |].
      intros x Hx. apply HoutA2; lia. }
    (* the frame bytes outside the copy's destination, and the live block, are untouched *)
    assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 128 <= x < fr + 140) ->
              Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) x).
    { intros x Hx Hnd. apply Hout.
      - pose proof (Happfr x Hx) as Hap. pose proof (HshIS (Sfr fr + 16) ltac:(lia)) as H1.
        pose proof (HshIS (Sfr fr + 17) ltac:(lia)) as H2.
        unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
        lia.
      - left. lia.
      - lia.
      - unfold ASAN_MEMCPY_K in *. lia. }
    assert (Hblkout : forall x, phi <= x < phi + flen g j ->
              Frame.outside (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) x).
    { intros x Hx.
      destruct (tf_blk_out B APIf ra g fr phi (flen g j) regs mem md HFRA x Hx)
        as (Hap & Hlo & Hnfr).
      pose proof (HshIS (Sfr fr + 16) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 17) ltac:(lia)) as H2.
      unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END,
        ASAN_MEMCPY_K, FN_STACK in *.
      apply Hout; lia. }
    (* KNT: the kind-name table (image bytes below GT) and its shadow bytes [0x8000beb0, 0x8000bebe), below the
       frame's shadow S(fr) >= GT / 8 + K and below every other range the segment writes *)
    assert (HKNT' : KNT mem').
    { apply (tf_knt_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' HKNT MU).
      - intros x Hx. apply (tf_out_GT _ x HGTW). unfold KNC.KIND_NAME in Hx. unfold AC.GT. lia.
      - intros x Hx.
        assert (HSfr : 0x800b7c00 <= Sfr fr)
          by (clear - HGT; unfold Sfr, shadow_addr, ASAN_K; unfold AC.GT in HGT; Z.div_mod_to_equations; lia).
        pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1. pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K, FN_STACK in *.
        apply Hout; lia. }
    (* `first` [fr + 2880, fr + 2920) stays addressable: its shadow bytes S(fr) + 360 .. 364 are not written *)
    assert (HAfst : addressable mem' (fr + 2880) 40).
    { apply (tf_addr_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' (fr + 2880) 40 HRfst MU).
      intros i Hi.
      pose proof (tf_sh_ge fr (fr + 2880 + i) 360 Hfr8 ltac:(lia) ltac:(lia)) as H1.
      pose proof (Happfr (fr + 2880 + i) ltac:(lia)) as Hap.
      pose proof (shadow_of_app (fr + 2880 + i) Hap) as His2.
      pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1. pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
      unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
        APPMEM_END, ASAN_MEMCPY_K, FN_STACK in *.
      apply Hout; lia. }
    (* LK: the turn index, our[], the 23 FLI spills (21 at the kept positions plus [A + 168] / [A + 88]
       appended; none of them is [A + 272]), the frame's stack facts, RAD and KNT *)
    assert (HLK' : LK g fr j regs' mem').
    { split; [exact Hj255|].
      split; [apply Hspkeep; [lia | exact Hs240]|].
      split.
      { unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
        rewrite OUR_length. intros x Hx. apply Hfrout; lia. }
      unfold FLI. split; [unfold rg in H27 |- *; rewrite Fr27; exact H27|].
      split; [apply Hspkeep; [lia | exact P168]|].
      split; [apply Hspkeep; [lia | exact P96]|].
      split; [apply Hspkeep; [lia | exact P112]|].
      split; [apply Hspkeep; [lia | exact P120]|].
      split; [apply Hspkeep; [lia | exact P128]|].
      split; [apply Hspkeep; [lia | exact P136]|].
      split; [apply Hspkeep; [lia | exact P144]|].
      split; [apply Hspkeep; [lia | exact P152]|].
      split; [apply Hspkeep2; [lia | exact P280]|].
      split; [apply Hspkeep; [lia | exact P160]|].
      split; [apply Hspkeep; [lia | exact P176]|].
      split; [apply Hspkeep; [lia | exact P192]|].
      split; [apply Hspkeep; [lia | exact P200]|].
      split; [apply Hspkeep; [lia | exact P216]|].
      split; [apply Hspkeep; [lia | exact P208]|].
      split; [apply Hspkeep; [lia | exact P104]|].
      split; [apply Hspkeep; [lia | exact P256]|].
      split; [apply Hspkeep; [lia | exact P264]|].
      split; [apply Hspkeep2; [lia | exact P288]|].
      split; [apply Hspkeep2; [lia | exact P296]|].
      split; [apply Hspkeep2; [lia | exact P304]|].
      split.
      { apply (tf_addr_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' (fr + 2624) 6
                 HadOur MU).
        intros i Hi.
        pose proof (tf_sh_ge fr (fr + 2624 + i) 328 Hfr8 ltac:(lia) ltac:(lia)) as H1.
        pose proof (Happfr (fr + 2624 + i) ltac:(lia)) as Hap.
        pose proof (shadow_of_app (fr + 2624 + i) Hap) as His2.
        pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1.
        pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
        unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
          APPMEM_END, ASAN_MEMCPY_K, FN_STACK in *.
        apply Hout; lia. }
      split.
      { apply (tf_stk_keep (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' fr (fr + FRAME_BYTES));
          [exact HstkF | exact MU | exact WM |].
        intros x Hx Ho.
        destruct (Z_lt_ge_dec x (fr + 128)) as [Dq1|Dq1];
          [|destruct (Z_lt_ge_dec x (fr + 140)) as [Dq2|Dq2]].
        - exfalso. apply Ho. apply Hfrout; lia.
        - apply (tf_ba_rd mem' (fr + 128) f23_src x HbD). rewrite f23_src_len. lia.
        - exfalso. apply Ho. apply Hfrout; lia. }
      split; [|split; [exact HKNT' | split; [apply Hspkeep; [lia | exact P168b] | apply Hspkeep; [lia | exact P88]]]].
      (* RAD: the three ranges' bytes stay addressable (their shadow bytes are S(fr) + 336 .. 355 and
         S(fr) + 360 .. 364 (the local first), which the segment's stores at S(fr) + 16 / 17 miss) *)
      unfold RAD. split; [|split; [|exact HAfst]].
      { apply (tf_addr_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' (fr + 2688) 38 HRid MU).
        intros i Hi.
        pose proof (tf_sh_ge fr (fr + 2688 + i) 336 Hfr8 ltac:(lia) ltac:(lia)) as H1.
        pose proof (Happfr (fr + 2688 + i) ltac:(lia)) as Hap.
        pose proof (shadow_of_app (fr + 2688 + i) Hap) as His2.
        pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1.
        pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
        unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
          APPMEM_END, ASAN_MEMCPY_K, FN_STACK in *.
        apply Hout; lia. }
      { apply (tf_addr_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' (fragb fr) 72 HRfg MU).
        intros i Hi.
        pose proof (tf_sh_ge fr (fragb fr + i) 346 Hfr8 ltac:(unfold fragb in *; lia)
                      ltac:(unfold fragb in *; lia)) as H1.
        pose proof (Happfr (fragb fr + i) ltac:(unfold fragb in *; lia)) as Hap.
        pose proof (shadow_of_app (fragb fr + i) Hap) as His2.
        pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1.
        pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
        unfold fragb, app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
          APPMEM_END, ASAN_MEMCPY_K, FN_STACK in *.
        apply Hout; lia. } }
    (* F27K: the frame-loop state of the check_ports window *)
    assert (HK' : F27K g j phi fr regs' mem').
    { unfold F27K. split; [exact HLK'|].
      split; [unfold rg in H18 |- *; rewrite Fr18; exact H18|].
      split; [unfold rg in H27 |- *; rewrite Fr27; exact H27|].
      split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hflen|].
      split.
      { eapply fl_bytes; [exact Hblk | exact MU |].
        intros x Hx. apply Hblkout.
        pose proof (f23_blk_len (g_in g) j) as Hbl. rewrite Hbl in Hx. lia. }
      split.
      { (* [A + 312] = Phi + 18: the length arm is the long one, so t_big is true *)
        assert (Hbig : t_big (g_in g) j = true)
          by (unfold t_big; apply Z.leb_le; unfold flen in Hflen; lia).
        rewrite Hbig in M312. apply Hspkeep2; [lia | exact M312]. }
      split.
      { (* [A + 272] = k: the store of 0x82848 *)
        exists A. split; [unfold rg in *; rewrite Fr9; exact Hr9 | exact HQ]. }
      split; [unfold rg in H25 |- *; rewrite Fr24; exact H25|].
      split; [apply Hspkeep; [lia | exact P104]|].
      apply Hspkeep; [lia | exact P136]. }
    (* rebuild the exit cut *)
    rewrite <- SEGS. apply Hexit.
    unfold Inv_B82878_at, FCUTP.
    exists phi, regs', mem', md', fr.
    rewrite SEGS. split; [reflexivity|].
    rewrite (tf_asize (flen g j) Hflen).
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      rewrite (tf_asize (flen g j) Hflen) in Hphiad |- *.
      pose proof Hphiad as Hphiad2.
      apply (tf_addr_munch (f23_W (Sfr fr) A (fr + 128) (AC.aspZ regs)) mem mem' phi (flen g j)
               Hphiad MU).
      intros i Hi. destruct Hphiad2 as (_ & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      pose proof (HshIS (Sfr fr + 16) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 17) ltac:(lia)) as H2.
      pose proof (shadow_of_app (phi + i) Hap) as His.
      destruct (tf_blk_out B APIf ra g fr phi (flen g j) regs mem md HFRA (phi + i) ltac:(lia))
        as (_ & Hlo & Hnfr).
      assert (Hback : ~ (Sfr fr <= shadow_addr (phi + i) < Sfr fr + FRAME_SHADOW)).
      { intros Hin. apply Hnfr.
        exact (tf_sh_back fr (phi + i) Hfr8 ltac:(lia)
          ltac:(unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia) Hin). }
      pose proof (Happfr (fr + 128) ltac:(lia)) as Hd1. pose proof (Happfr (fr + 139) ltac:(lia)) as Hd2.
      unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END,
        ASAN_MEMCPY_K, FN_STACK in *.
      apply Hout; lia. }
    split; [unfold rg in H18 |- *; rewrite Fr18; exact H18|].
    split; [unfold rg in H20 |- *; rewrite Fr20; exact H20|].
    split.
    { (* FTURN: the cursor spills [A + 224] / [A + 232] (below [A + 272]) and the frame bytes at Phi *)
      destruct HFTURN as (T224 & T232 & Tphi & Tlen).
      split; [apply Hspkeep; [lia | exact T224]|].
      split; [apply Hspkeep; [lia | exact T232]|].
      split; [|exact Tlen].
      eapply fl_bytes; [exact Tphi | exact MU |]. intros x Hx. apply Hblkout. unfold flen. lia. }
    split; [exact HLK'|].
    split.
    { (* FTL: s5 = fr + 128 (0x82868), [A + 184] = the fill flag (kept), [A + 272] = k (0x82848),
         s8 = sum_ok (0x8284c mv s8,s9) and [A + 312] = blk (kept) *)
      split; [unfold rg; exact Fr21|].
      split; [apply Hspkeep; [lia | exact M184]|].
      split; [exists A; split; [unfold rg in *; rewrite Fr9; exact Hr9 | exact HQ]|].
      split; [unfold rg in H25 |- *; rewrite Fr24; exact H25 | apply Hspkeep2; [lia | exact M312]]. }
    split; [unfold rg in M22 |- *; rewrite Fr22; exact M22|].
    split.
    { (* IFS (S j): the local first [fr + 2880, fr + 2920) and the two frame records at fr + 2688 / fr + 2768,
         which the copy's destination [fr + 128, fr + 140) misses *)
      apply (Tac_ro.ifs_keep g fr (S j) regs regs' mem mem' HIFS).
      - intros Hb. eapply fl_bytes; [exact Hb | exact MU |].
        rewrite Tac_ro.tr_ID_length. intros x Hx. apply Hfrout; lia.
      - intros Hb. eapply fl_bytes; [exact Hb | exact MU |].
        rewrite Tac_ro.tr_FG_length. intros x Hx. apply Hfrout; lia.
      - intros a bs Ha Hl Hb. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply Hfrout; lia.
      - exact HAfst. }
    split; [exact HK'|].
    (* the registers and the ports words the copy wrote *)
    split; [unfold rg in H20 |- *; rewrite Fr20; exact H20|].
    split; [unfold rg; exact Fr23|].
    split; [apply Hspkeep; [lia | exact M184]|].
    split; [unfold rg; exact Fr21|].
    destruct (f23_src_u32 mem' (fr + 128) HbD) as (U0 & U4 & U8).
    split; [exact U0|].
    split; [replace (fr + 132) with (fr + 128 + 4) by lia; exact U4|].
    split; [replace (fr + 136) with (fr + 128 + 8) by lia; exact U8|].
    split.
    { (* the 12 bytes are marked usable by the two shadow bytes the segment wrote *)
      apply (tf_addr_sh mem' (fr + 128) 12); [lia | lia | exact HDE | exact HD8 |
        intros t Ht; apply Happfr; lia |].
      intros t Ht.
      assert (Esh : shadow_addr (fr + 128) = Sfr fr + 16) by (unfold shadow_addr; lia).
      rewrite Esh.
      destruct (Z_lt_le_dec t 8) as [Hlt|Hge].
      - exists 0. replace (Sfr fr + 16 + t / 8) with (Sfr fr + 16) by (Z.div_mod_to_equations; lia).
        split; [exact HB16|]. split; [lia | left; reflexivity].
      - exists 4. replace (Sfr fr + 16 + t / 8) with (Sfr fr + 17) by (Z.div_mod_to_equations; lia).
        split; [exact HB17|]. split; [lia | right; Z.div_mod_to_equations; lia]. }
    (* the frame bytes at Phi and their 50-byte prefix *)
    split.
    { unfold F23GAP. split.
      - eapply fl_bytes; [exact (proj1 (proj2 (proj2 HFTURN))) | exact MU |].
        intros x Hx. apply Hblkout.
        pose proof (proj2 (proj2 (proj2 HFTURN))) as Hlen. unfold flen in *. lia.
      - intros _. eapply fl_bytes; [exact Hphig | exact MU |].
        intros x Hx. apply Hblkout. rewrite (tf_g_len (g_in g) j) in Hx. lia. }
    rewrite HaspEq. exact Hdj.
Qed.

End S.
