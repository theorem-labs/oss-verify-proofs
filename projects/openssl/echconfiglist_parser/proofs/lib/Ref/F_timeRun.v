(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: time_sr_vc, time() at the run's heap instance HRv: the walk of time and clock_gettime over the run's segment list (straight to the resolved vDSO entry, or through cgt_init, __vdsosym and the vdso_func CAS), the vDSO call node of Spec/VdNode.v, and the walk back to time's caller; after the vDSO step the configuration is projected out of the step's answer without reduction, so vd_npost stays folded. *)

(* WHAT IS PROVED.  [time_sr_stmt] (Ref/F_time.v) at [HRv tail vlo vmid vhi] (Ref/HeapSRVC.v),
   whose reach is [sr_run tail] (Ref/HeapSRRun.v): an [sreach] over [rsegs ++ tail] from the
   state with that list's read-only backing.  The walk has three parts.

   1. time() and clock_gettime() up to the indirect call of [vdso_func], over [rvsegs tail]
      ([time_front_v]).  When the cell holds [P_cgt_init], cgt_init runs first
      ([cgt_init_v]): it calls __vdsosym ([RVdsoWalk.vdsosym_walk]), which returns the
      vDSO's clock_gettime entry [vb + 1460 = hvdso], stores it into [vdso_func] by its
      lr/sc loop, pops its frame and jumps there.  Either way the machine stands at [hvdso]
      with clock_gettime's return address in ra.
   2. The call itself: one step of the model's vDSO node (Spec/VdNode.v, [vd_step_sound],
      [vd_step_complete], [vd_rob]).  [Run.vdso_post] (Run.v:623-635) leaves the
      caller-saved registers and the first F = 240 bytes below sp to the launch's draw
      ([ts_npost_MS], [vwf_cases_g]); the timespec is the effect's 16 bytes.
   3. clock_gettime's return of 0 and time()'s epilogue ([time_back_v]).

   The overlay facts move between the binary's list and the run's list by the window
   hypotheses: no tail byte lies outside [vlo, vhi) ([Htw]), and the overlay holds no byte
   inside it ([vclean], part of [HRv]'s heap relation); [tr_vclean_of_inv] gives the window
   back after the call from [mem_inv] over the run's list and [Hcov]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import MmVdso VdNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import AuxvTable VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RVdsoAddr RVdsoSegs RVdsoSym RVdsoXfer RVdsoWalk.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import HeapSRRun HeapSRVC.
(* Ref/F_time.v's own import list, in its order, so that every name its proofs used resolves
   here as it did there. *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame ITree Nodes Decode.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Time Require Import PosixTimers.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog STree Malloc MmNodes KLink CgNode.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMalloc_iface RMalloc_ifaceP HeapSR_iface MallocSR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import SReach SReachTree.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac RSegs RMallocRep RMallocTree RF_am_E F_syscalls.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import F_time.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* ------------------------------------------------------------------ *)
(* Facts that name no binary.                                          *)
(* ------------------------------------------------------------------ *)

Lemma ts_sub_lit : forall a b : Z, (Z_to_bv 64 a - Z_to_bv 64 b)%bv = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* the vDSO text base is page-aligned, so its clock_gettime entry is even *)
Lemma ts_even_entry : forall vb h : Z, vb mod 4096 = 0 -> vb + 1460 = h -> h mod 2 = 0.
Proof.
  intros vb h H E. subst h.
  rewrite (Z.div_mod vb 4096) by lia. rewrite H.
  replace (4096 * (vb / 4096) + 0 + 1460) with ((2048 * (vb / 4096) + 730) * 2) by lia.
  first [apply Z_mod_mult | apply Z.mod_mul; lia].
Qed.

Lemma ts_image_in : forall ims bs im, vdso_image_of_bytes ims bs = Some im -> In im ims.
Proof.
  induction ims as [|i ims IH]; intros bs im H; cbn [vdso_image_of_bytes] in H; [discriminate H|].
  destruct (pstrings_eqb (vi_bytes i) bs).
  - injection H as E. left. exact E.
  - right. exact (IH bs im H).
Qed.

(* An exported entry means the text segment holds the one measured image (Vdso.v:287-315),
   whose largest frame is 240 bytes. *)
Lemma ts_vframe_of_entry : forall segs a f, vdso_entry_fn segs a = Some f -> vdso_frame segs = 240%N.
Proof.
  intros segs a f H. unfold vdso_entry_fn in H. unfold vdso_frame.
  revert H. unfold vdso_image.
  destruct (vdso_text_seg segs) as [seg0|]; [| intros H; discriminate H].
  destruct (vdso_image_of_bytes vdso_images (seg_bytes seg0)) as [im0|] eqn:E2; [| intros H; discriminate H].
  intros _. apply ts_image_in in E2.
  destruct E2 as [<- | []]. reflexivity.
Qed.

(* [VdNode.vd_npost] of a clock_gettime call that returns 0 and writes the 16 bytes [bs] at
   [tp]: the caller-saved registers are the draw's (or kept, where its list is short), a0 is
   0, pc is the old ra, and memory is the frame write of at most 240 bytes from [sp - 240]
   followed by the effect's write. *)
Lemma ts_npost_MS : forall (segs : list Segment) (tp : Z) (d : VdsoDraw) (calls : N)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) (m ro : word -> option byte) (bs : list byte),
  vdso_frame segs = 240%N ->
  exists (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (fr : list byte),
    vd_npost segs (VDRealtime tp d calls)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F pc fc rv m ro)
      (mkEffectU (Z_to_bv 64 0) [(Z_to_bv 64 tp, bs)] [] [] [] [])
    = MS (mkR y1 x2 x3 x4 y5 y6 y7 x8 x9 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
         F x1 fc rv
         (write_to_mem (vdso_write_frame segs m (x2 - Z_to_bv 64 240)%bv (firstn 240%nat fr)) (Z_to_bv 64 tp) bs) ro.
Proof.
  intros segs tp d calls x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
         x24 x25 x26 x27 x28 x29 x30 x31 F pc fc rv m ro bs HF.
  unfold vd_npost. cbv beta iota zeta. rewrite HF.
  lazymatch goal with |- context [d calls ?u ?v ?w] => destruct (d calls u v w) as [vs fr] end.
  exists (nth_default x1 vs 0%nat), (nth_default x5 vs 1%nat), (nth_default x6 vs 2%nat), (nth_default x7 vs 3%nat),
         (nth_default x11 vs 5%nat), (nth_default x12 vs 6%nat), (nth_default x13 vs 7%nat), (nth_default x14 vs 8%nat),
         (nth_default x15 vs 9%nat), (nth_default x16 vs 10%nat), (nth_default x17 vs 11%nat), (nth_default x28 vs 12%nat),
         (nth_default x29 vs 13%nat), (nth_default x30 vs 14%nat), (nth_default x31 vs 15%nat), fr.
  cbn [vl_regs vl_frame].
  do 16 (destruct vs as [|? vs]; [reflexivity|]).
  reflexivity.
Qed.

(* auxv pair 0 is (AT_SYSINFO_EHDR, its value), Lib/AuxvTable.v:59-68. *)
Lemma ts_auxv_pair : forall segs m av v rnd execfn r,
  bytes_at segs m av (u64s (map (Z_to_bv 64) (auxv_words_Z v rnd execfn r))) ->
  cells_at segs m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 (ax_sysinfo v))].
Proof.
  intros segs m av v rnd execfn r H. split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r.
  unfold auxv_words_Z in H. cbn [map app u64s] in H. rewrite app_assoc in H.
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma ts_cells_split : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (H0 & H1 & Hw)].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite (cells_bytes_length cs1 W1) in B2.
  rewrite cells_size_app in H1, Hw.
  split.
  - split; [split; [exact W1 | exact B1]|]. split; [exact H0|]. split; [lia|].
    intros i Hi. apply Hw. lia.
  - split; [split; [exact W2 | exact B2]|]. split; [lia|]. split; [lia|].
    intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* [Run.vdso_write_frame] (Run.v:563-573) writes a byte only where the writable view has one,
   and only at the addresses it walks. *)
Lemma vwf_cases_g : forall segs bs m (a x : word),
  vdso_write_frame segs m a bs x = m x
  \/ (wview segs m x <> None /\ exists b, vdso_write_frame segs m a bs x = Some b).
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a x; [left; reflexivity|].
  cbn [vdso_write_frame].
  destruct (wview segs m a) as [b0|] eqn:E; cbv beta iota.
  - lazymatch goal with |- context [vdso_write_frame segs ?mm ?aa bs x] =>
      destruct (IH mm aa x) as [H1 | (H1 & b1 & H2)] end.
    + rewrite H1. cbv beta. destruct (bv_eqb x a) eqn:Exa.
      * right. split; [| exists b; reflexivity].
        apply bv_eqb_eq in Exa. rewrite Exa, E. discriminate.
      * left. reflexivity.
    + right. split; [| exists b1; exact H2].
      destruct (bv_eqb x a) eqn:Exa.
      * apply bv_eqb_eq in Exa. rewrite Exa, E. discriminate.
      * revert H1. unfold wview. cbv beta. rewrite Exa. exact (fun H => H).
  - apply IH.
Qed.

Lemma vwf_wmono : forall segs bs m (a x : word),
  wview segs m x <> None -> wview segs (vdso_write_frame segs m a bs) x <> None.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m a x H; [exact H|].
  cbn [vdso_write_frame]. apply IH.
  destruct (wview segs m a) as [b0|] eqn:E; cbv beta iota; [|exact H].
  revert H. unfold wview. cbv beta.
  destruct (bv_eqb x a); [intros _; cbv iota; discriminate | exact (fun H => H)].
Qed.

Lemma vwf_out : forall segs bs m (z : Z) (x : word),
  (forall i, (i < length bs)%nat -> x <> wa (z + Z.of_nat i)) ->
  vdso_write_frame segs m (wa z) bs x = m x.
Proof.
  intros segs bs. induction bs as [|b bs IH]; intros m z x Hx; [reflexivity|].
  cbn [vdso_write_frame]. rewrite wa_succ. rewrite IH.
  - destruct (wview segs m (wa z)); cbv beta iota; [|reflexivity].
    destruct (bv_eqb x (wa z)) eqn:E; [|reflexivity].
    exfalso. apply bv_eqb_eq in E. apply (Hx 0%nat); [cbn [length]; lia|].
    replace (z + Z.of_nat 0) with z by lia. exact E.
  - intros i Hi. replace (z + 1 + Z.of_nat i) with (z + Z.of_nat (S i)) by lia.
    apply Hx. cbn [length]. lia.
Qed.

Lemma vwf_munch : forall segs bs m (z : Z), 0 <= z -> z + Z.of_nat (length bs) <= 2^64 ->
  munch [(z, z + Z.of_nat (length bs))] m (vdso_write_frame segs m (wa z) bs).
Proof.
  intros segs bs m z Hz Hl x Hx. apply vwf_out. intros i Hi E. subst x.
  cbn [outside] in Hx. destruct Hx as [Hx _]. apply Hx.
  rewrite wa_unsigned by lia. lia.
Qed.

Lemma vwf_mem_inv : forall segs bs m (a : word), mem_inv segs m -> mem_inv segs (vdso_write_frame segs m a bs).
Proof.
  intros segs bs m a MI x b Hx.
  destruct (vwf_cases_g segs bs m a x) as [E | (Hw & _)].
  - rewrite E in Hx. exact (MI x b Hx).
  - destruct (m x) as [b0|] eqn:Em; [exact (MI x b0 Em) | exact (wview_not_ro segs m x Hw Em)].
Qed.

Lemma vwf_stk : forall segs bs m (a : word) lo hi,
  stk segs m lo hi -> stk segs (vdso_write_frame segs m a bs) lo hi.
Proof.
  intros segs bs m a lo hi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros y Hy. destruct (H y Hy) as [Hw (b & Hb)].
  split; [exact (vwf_wmono segs bs m a _ Hw)|].
  destruct (vwf_cases_g segs bs m a (wa y)) as [E | (_ & b' & E)].
  - exists b. unfold mrd in *. rewrite E. exact Hb.
  - exists b'. unfold mrd. rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* time() at the run's instance.                                       *)
(* ------------------------------------------------------------------ *)

Section TimeRun.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image rsegs = None.
  Variables vlo vmid vhi : Z.
  Hypothesis HW : 0x311000 <= vlo /\ vlo <= vmid /\ vmid <= vhi /\ vhi <= hceil.
  Hypothesis Htw  : forall (x : Z) s, find_segment tail x 1 = Some s -> vlo <= x < vhi.
  Hypothesis Hcov : forall (x : Z), vlo <= x < vhi -> find_segment tail x 1 <> None.
  Hypothesis ROM  : rvdso_rom (rvsegs tail) vmid.
  Hypothesis HVB  : hvdso = vmid + 1460.
  Hypothesis HENT : vdso_entry_fn (rsegs ++ tail) (Z_to_bv 64 hvdso) = Some VdsoClockGettime.
  Hypothesis HUNM : forall ms, ms_pc ms = Z_to_bv 64 hvdso -> RiscvSemantics.step (rsegs ++ tail) ms = MachineUnmodeled.

  Local Notation VS := (rvsegs tail).

  (* a branch on a register holding [hvdso] against x0 *)
  Local Ltac if_false_nz :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; unfold bv_eqb; rewrite ?w0_lit; rewrite ?unsigned_lit by lia; apply Z.eqb_neq; lia ]
    end.

  (* the target of a [jalr] through a register holding [hvdso], which is even *)
  Local Ltac fix_pc_hv HEV :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ ?pcx _ _ _ _) =>
        replace pcx with (Z_to_bv 64 hvdso)
          by first [ reflexivity
                   | symmetry; rewrite ?Z.add_0_r, ?ret_pc_fold; apply ret_pc_even; [lia | exact HEV] ]
    end.

  Local Ltac trw H MU WM :=
    lazymatch type of MU with
    | munch ?W ?m0 ?m1 =>
        apply (rw_cells_transport _ W m0 m1) in H;
        [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]
    end.

  Local Ltac trwr H a bs :=
    apply (rw_cells_frame _ _ _ _ a bs) in H;
    [| lia | lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia].

  (* -------- the binary's list and the run's list -------- *)

  Lemma tr_wview : forall m x, wview VS m x = wview rsegs m x.
  Proof. intros m x. unfold rvsegs. apply wview_app_nw; first [exact Hnw | exact Hnx]. Qed.

  Lemma tr_wr_at_keep : forall m A n, wr_at rsegs m A n -> wr_at VS m A n.
  Proof.
    intros m A n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite tr_wview. exact (H i Hi).
  Qed.

  Lemma tr_rw_cells_keep : forall m A cs, rw_cells rsegs m A cs -> rw_cells VS m A cs.
  Proof.
    intros m A cs [[Hwf Hb] Hw].
    split; [split; [exact Hwf | exact (rv_bytes_at_keep tail m A _ Hb)] | exact (tr_wr_at_keep m A _ Hw)].
  Qed.

  Lemma tr_stk_keep : forall m lo hi, stk rsegs m lo hi -> stk VS m lo hi.
  Proof.
    intros m lo hi (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros a Ha. destruct (H a Ha) as [Hw (b & Hb)].
    split; [rewrite tr_wview; exact Hw | exists b; exact (rv_mrd_keep tail m _ _ Hb)].
  Qed.

  (* an overlay byte is never at a tail address: those are inside the window, which is clean *)
  Lemma tr_mem_inv_keep : forall m, mem_inv rsegs m -> vclean vlo vhi m -> mem_inv VS m.
  Proof.
    intros m MI VC a b Ha. pose proof (MI a b Ha) as R. revert R.
    unfold ro_addr, rvsegs. rewrite find_segment_app.
    destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|]; intros R; [exact R|].
    destruct (find_segment tail (bv_unsigned a) 1) as [sg|] eqn:E2; [|reflexivity].
    exfalso. rewrite (VC a (Htw _ _ E2)) in Ha. discriminate Ha.
  Qed.

  (* every window byte is a tail address, read-only, so [mem_inv] keeps the overlay off it *)
  Lemma tr_vclean_of_inv : forall m, mem_inv VS m -> vclean vlo vhi m.
  Proof.
    pose proof HW as (HW1 & _).
    intros m MI x Hx. destruct (m x) as [b|] eqn:E; [exfalso | reflexivity].
    pose proof (MI x b E) as R. revert R.
    unfold ro_addr, rvsegs. rewrite find_segment_app.
    rewrite (ref_find_segment_none (bv_unsigned x) 1) by lia.
    destruct (find_segment tail (bv_unsigned x) 1) as [sg|] eqn:E2; [| exfalso; exact (Hcov _ Hx E2)].
    cbv beta iota. rewrite (Hnw sg (find_segment_in _ _ _ _ E2)). cbn [negb].
    intros R. discriminate R.
  Qed.

  Lemma tr_mrd_off : forall m x, ~ (vlo <= bv_unsigned x < vhi) -> mrd VS m x = mrd rsegs m x.
  Proof.
    intros m x Hx. unfold mrd. destruct (m x) as [b|]; [reflexivity|].
    unfold OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.seg_rom, memory_read, rvsegs.
    rewrite find_segment_app.
    destruct (find_segment rsegs _ _) as [sg|]; [reflexivity|].
    destruct (find_segment tail _ _) as [sg|] eqn:E; [|reflexivity].
    exfalso. apply Hx. exact (Htw _ sg E).
  Qed.

  Lemma tr_bytes_at_back : forall m A bs, (A + Z.of_nat (length bs) <= vlo \/ vhi <= A) ->
    bytes_at VS m A bs -> bytes_at rsegs m A bs.
  Proof.
    intros m A bs Hoff (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- tr_mrd_off; [exact (H i Hi)|].
    rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma tr_rw_cells_back : forall m A cs, (A + Z.of_nat (cells_size cs) <= vlo \/ vhi <= A) ->
    rw_cells VS m A cs -> rw_cells rsegs m A cs.
  Proof.
    intros m A cs Hoff [[Hwf Hb] (H0 & H1 & Hw)]. split; [split; [exact Hwf|]|].
    - apply tr_bytes_at_back; [rewrite (cells_bytes_length cs Hwf); exact Hoff | exact Hb].
    - split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- tr_wview. exact (Hw i Hi).
  Qed.

  Lemma tr_stk_back : forall m lo hi, vhi <= lo -> stk VS m lo hi -> stk rsegs m lo hi.
  Proof.
    intros m lo hi Hlo (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
    intros a Ha. destruct (H a Ha) as [Hw Hb]. split; [rewrite <- tr_wview; exact Hw|].
    rewrite <- tr_mrd_off; [exact Hb|]. rewrite wa_unsigned by lia. lia.
  Qed.

  Lemma tr_wmono_back : forall m m', wmono VS m m' -> wmono rsegs m m'.
  Proof.
    intros m m' W x Hx. rewrite <- tr_wview in Hx. rewrite <- tr_wview. exact (W x Hx).
  Qed.

  (* -------- cgt_init: __vdsosym, the CAS, the tail call -------- *)

  Definition cgt_init_post_v (ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 hvdso) fc None m' (seg_rom VS)
      /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m m'
      /\ wmono VS m m' /\ mem_inv VS m'
      /\ stk VS m' lo (bv_unsigned sp) /\ rw_cells VS m' 3000480 [C8 (Z_to_bv 64 hvdso)].

  (* cgt_init at 0x27d9f8 (probe P1): the [vdso_func] cell at 0x2dc8a0 holds cgt_init itself;
     the auxv cell at 0x30f710 holds [av], whose pair 0 is (33, vb). *)
  Lemma cgt_init_v : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo av vb : Z),
    ro_cells VS m 3208976 [C8 (Z_to_bv 64 av)] ->
    ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
    rvdso_rom VS vb -> 0 < vb -> vb + 1460 = hvdso -> bv_unsigned sp <= av ->
    rw_cells VS m 3000480 [C8 (Z_to_bv 64 2611704)] ->
    stk VS m lo (bv_unsigned sp) -> 3208984 <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv VS m ->
    evt VS (cgt_init_post_v ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2611704) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo av vb CELL AUXP ROMv VBP HVBv SPA VF ST CLO LO MI.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROMv as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    pose proof (ts_even_entry vb hvdso VBA HVBv) as HEV.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m) as MU.
    pose proof (wmono_refl VS m) as WM.
    (* addi sp,sp,-32; sd ra,s0,s1; mv s0,a1; mv s1,a0; the two strings *)
    step. carve_frame 32%nat ST. do 9 step.
    (* jal __vdsosym *)
    step.
    eapply evt_cut.
    { eapply (vdsosym_walk tail) with (lo := lo) (av := av) (vb := vb);
        rewrite ?unsigned_lit by lia; first [eassumption | lia | (unfold VW_AUXV_CELL; lia)]. }
    intros ms1 PV. unfold vdsosym_post_v in PV.
    destruct PV as (u0 & u1 & u2 & r0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & u3 & u4 & u5 & u6 & m1
                    & -> & E0 & MU1 & WM1 & MI1 & ST1).
    rewrite unsigned_lit in MU1, ST1 by lia.
    unfold RVDSO_CGT_OFF in E0. rewrite HVBv in E0. subst r0.
    replace (ret_pc (Z_to_bv 64 2611748)) with (Z_to_bv 64 2611748) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch type of MU1 with munch _ ?m0 _ => transport_after_call (rvsegs tail) m0 m1 MU1 WM1 end.
    clear MU1 WM1.
    (* mv t1,a0; a0 = &vdso_func; a1 = cgt_init *)
    step. step. step. step. step.
    (* lr.d; bne; sc.d; bnez: the CAS stores hvdso *)
    astep. step. if_false. astep. step. if_false.
    (* beqz t1: the entry is not null *)
    step. if_false_nz.
    (* mv a0,s1; mv a1,s0; restore ra,s0,s1; addi sp,sp,32; jalr x0,0(t1) *)
    step. step. step. step. step. step. step.
    fix_pc_hv HEV.
    lazymatch goal with
    | H : rw_cells VS ?mX (bv_unsigned sp + -32) _, S : stk VS ?mX lo _ |- _ => release_frame H S (bv_unsigned sp)
    end.
    unfold cgt_init_post_v. finish.
  Qed.

  (* -------- time() and clock_gettime() up to the vDSO call -------- *)

  Definition time_front_post_v (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word)
      (F : bvmap 5 word) (fc : bv 32) (lo can : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : mem) (junk16 junk8 : list byte),
      ms' = MS (mkR (Z_to_bv 64 2611568) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7
                    (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -48))
                    x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 hvdso) fc None m1 (seg_rom VS)
      /\ rw_cells VS m1 (bv_unsigned sp + -48) [CB 16 junk16; C8 (Z_to_bv 64 can); C8 s1v; C8 s0v; C8 rav]
      /\ rw_cells VS m1 (bv_unsigned sp + -80)
           [CB 8 junk8; C8 (Z_to_bv 64 3208376); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2612912)]
      /\ rw_cells VS m1 3000480 [C8 (Z_to_bv 64 hvdso)]
      /\ rw_cells VS m1 3208376 [C8 (Z_to_bv 64 can)]
      /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m m1
      /\ wmono VS m m1 /\ mem_inv VS m1
      /\ stk VS m1 lo (bv_unsigned sp + -80).

  (* time at 0x27de80 and clock_gettime at 0x27d940 (probe P1); GOT slot 0x2db120 holds
     &__stack_chk_guard = 0x30f4b8, the guard holds [can]. *)
  Lemma time_front_v : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo av vb vf can : Z),
    ro_cells VS m 3208976 [C8 (Z_to_bv 64 av)] ->
    ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 vb)] ->
    rvdso_rom VS vb -> 0 < vb -> vb + 1460 = hvdso -> bv_unsigned sp <= av ->
    rw_cells VS m 2994464 [C8 (Z_to_bv 64 3208376)] ->
    rw_cells VS m 3208376 [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
    rw_cells VS m 3000480 [C8 (Z_to_bv 64 vf)] -> (vf = hvdso \/ vf = 2611704) ->
    stk VS m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 224 -> mem_inv VS m ->
    a0 = Z_to_bv 64 0 ->
    evt VS (time_front_post_v sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 F fc lo can m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2612864) fc None m (seg_rom VS)).
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo av vb vf can CELL AUXP ROMv VBP HVBv SPA GOT CAN CANR VF HVF ST CLO LO MI A0.
    subst a0. hcb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof ROMv as (VB0 & VBA & VBH & _). rewrite RVDSO_SPAN_val in VBH.
    pose proof (ts_even_entry vb hvdso VBA HVBv) as HEV.
    pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m) as MU.
    pose proof (wmono_refl VS m) as WM.
    (* time: frame, canary, a1 = sp, a0 = CLOCK_REALTIME, jal clock_gettime *)
    step. carve_frame 48%nat ST. do 10 step.
    (* clock_gettime: frame, s0 = ts, a2 = vdso_func, s1 = clk *)
    step. lstep. carve_frame 32%nat ST. do 7 lstep.
    destruct HVF as [-> | ->].
    - (* the entry is resolved: a2 != 0, then jalr ra,0(a2) *)
      step. if_false_nz. step. step. step. fix_pc_hv HEV.
      apply evt_done. unfold time_front_post_v. do 16 eexists. split; [reflexivity|].
      do 7 (split; [eassumption|]). eassumption.
    - (* the first call: a2 = cgt_init *)
      step. if_false. step. step. step.
      eapply evt_cut.
      { eapply cgt_init_v with (lo := lo) (av := av) (vb := vb);
          rewrite ?unsigned_lit by lia; first [eassumption | lia]. }
      intros ms1 PG. unfold cgt_init_post_v in PG.
      destruct PG as (u0 & u1 & u2 & q2 & q3 & q4 & q5 & q6 & q7 & u3 & u4 & u5 & u6 & m1
                      & -> & MU1 & WM1 & MI1 & ST1 & VF1).
      rewrite unsigned_lit in MU1, ST1 by lia.
      lazymatch type of MU1 with munch _ ?m0 _ => transport_after_call (rvsegs tail) m0 m1 MU1 WM1 end.
      clear MU1 WM1.
      apply evt_done. unfold time_front_post_v. do 16 eexists. split; [reflexivity|].
      do 7 (split; [eassumption|]). eassumption.
  Qed.

  (* -------- after the call: clock_gettime returns 0, time() returns -------- *)

  Definition time_back_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 tv a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom VS)
      /\ stk VS m lo (bv_unsigned sp).

  Lemma time_back_v : forall (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
      (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (lo can : Z) (bs jk0 junk8 : list byte),
    rw_cells VS m (bv_unsigned sp + -48) [CB 16 bs; CB 0 jk0] ->
    rw_cells VS m (bv_unsigned sp + -32) [C8 (Z_to_bv 64 can); C8 s1v; C8 s0v; C8 rav] ->
    rw_cells VS m (bv_unsigned sp + -80)
      [CB 8 junk8; C8 (Z_to_bv 64 3208376); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2612912)] ->
    rw_cells VS m 3208376 [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
    stk VS m lo (bv_unsigned sp + -80) -> hceil <= lo -> lo <= bv_unsigned sp - 320 ->
    evt VS (time_back_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc lo m)
        (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y5 y6 y7
                 (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
            F (Z_to_bv 64 2611568) fc None m (seg_rom VS)).
  Proof.
    intros y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           rav s0v s1v F fc m lo can bs jk0 junk8 F16 FRr FRb CAN CANR ST CLO LO.
    hcb.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    (* clock_gettime: r == 0; sext.w; restore ra,s0,s1; addi sp,sp,32; ret *)
    step. if_true. step. step. step. step. step. step.
    (* time: a0 = ts.tv_sec; t == NULL; canary check; restore; ret *)
    step. step. if_true. step. step. step.
    if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
    step. step. step. step. step.
    release_frame FRb ST (bv_unsigned sp + -48).
    release_frame F16 ST (bv_unsigned sp + -32).
    release_frame FRr ST (bv_unsigned sp).
    apply evt_done. unfold time_back_post. do 15 eexists. split; [reflexivity | exact ST].
  Qed.

  (* -------- the theorem -------- *)

  Theorem time_sr_vc : time_sr_stmt (HRv tail vlo vmid vhi).
  Proof using Hnx Hnw Hvi HW Htw Hcov ROM HVB HENT HUNM.
    hcb. hsb.
    pose proof HW as (HW1 & HW2 & HW3 & HW4).
    pose proof ROM as (VM0 & VMA & VMH & _). rewrite RVDSO_SPAN_val in VMH.
    unfold time_sr_stmt, time_sr_stmt_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m s LB lo B vf errv mo HR KR AUX HB ST CLO LO ERR MI TP A0 VF HVF.
    unfold HRv, hsr_vc, hsr_run, HS in *.
    cbn [hs_SR hs_KREL hs_RHEAP hs_rauxv_ok] in HR, KR, AUX |- *.
    destruct HR as (HR0 & VC & BO). destruct KR as (KMs & PI). destruct AUX as (AUX0 & BTS).
    unfold sr_run.
    (* the run's backing is the run's list's [seg_rom]; [rvsegs tail] is [rsegs ++ tail] *)
    lazymatch goal with
    | |- sreach _ ?Q (cwrom (mkCfg (MS ?R ?F0 ?pc ?fc0 ?rv ?mm _) ?mo0) _) =>
        change (sreach (rvsegs tail) Q (mkCfg (MS R F0 pc fc0 rv mm (seg_rom (rvsegs tail))) mo0))
    end.
    pose proof (KM_halted_lazy s mo KMs) as [HH HL].
    subst a0.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    unfold TIME_STACK in LO.
    pose proof AUX0 as (av & v & rnd & execfn & r & AVC & AVL & ARND & HCB & HBA & HAV & HBR & HR2
                        & HVv & HRN & HEX & HVD).
    pose proof HR0 as (st & LB0 & _ & _ & MR & _).
    destruct MR as (_ & _ & (G1 & G2 & G3 & G4 & G5 & G6) & _).
    assert (ETP : bv_unsigned tp + -164 = 3077076) by (rewrite TP; vm_compute; reflexivity).
    assert (VBE : ax_sysinfo v = vmid) by lia.
    (* the facts over the run's list *)
    assert (MIv : mem_inv VS m) by exact (tr_mem_inv_keep m MI VC).
    assert (STv : stk VS m lo (bv_unsigned sp)) by exact (tr_stk_keep m lo _ ST).
    assert (VFv : rw_cells VS m 3000480 [C8 (Z_to_bv 64 vf)]) by exact (tr_rw_cells_keep m _ _ VF).
    assert (GOTv : rw_cells VS m 2994464 [C8 (Z_to_bv 64 3208376)]) by exact (tr_rw_cells_keep m _ _ G4).
    assert (CANv : rw_cells VS m 3208376 [C8 (Z_to_bv 64 hcanary)]) by exact (tr_rw_cells_keep m _ _ G5).
    assert (CELLv : ro_cells VS m 3208976 [C8 (Z_to_bv 64 av)]).
    { pose proof AVC as [[Wf Bt] _]. split; [exact Wf | exact (rv_bytes_at_keep tail m _ _ Bt)]. }
    assert (AUXv : ro_cells VS m av [C8 (Z_to_bv 64 33); C8 (Z_to_bv 64 (ax_sysinfo v))]).
    { pose proof (ts_auxv_pair rsegs m av v rnd execfn r AVL) as [Wf Bt].
      split; [exact Wf | exact (rv_bytes_at_keep tail m _ _ Bt)]. }

    (* 1. time and clock_gettime, to the vDSO entry *)
    eapply (cj_evt_sreach_k VS); [exact HH | exact HL | |].
    { eapply time_front_v with (lo := lo) (av := av) (vb := ax_sysinfo v) (vf := vf) (can := hcanary);
        first [reflexivity | eassumption | (rewrite VBE; exact ROM) | lia]. }
    intros ms1 PF.
    destruct PF as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & junk16 & junk8
                    & -> & FRa & FRb & VF1 & CAN1 & MU1 & WM1 & MI1 & ST1).

    (* 2. the vDSO call *)
    assert (WR16 : wr_at VS m1 (bv_unsigned sp + -48) 16)
      by (apply (rw_cells_wr_at VS m1 _ _ 16 FRa); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    assert (VFR : vdso_frame VS = 240%N) by exact (ts_vframe_of_entry _ _ _ HENT).
    lazymatch goal with
    | |- sreach _ _ (mkCfg ?msc _) =>
        assert (AT : vd_at_node VS (VDRealtime (bv_unsigned sp + -48) (vdr_draw (m_vdso mo)) (vdr_calls (m_vdso mo))) msc)
    end.
    { split; [reflexivity|]. split; [exact HENT|]. split; [apply HUNM; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact WR16 | lia]. }
    assert (SF : vd_safe (VDRealtime (bv_unsigned sp + -48) (vdr_draw (m_vdso mo)) (vdr_calls (m_vdso mo))) mo)
      by (split; reflexivity).
    apply sr_step.
    { exact (vd_rob VS _ _ mo AT). }
    { eexists. exact (vd_step_sound VS _ _ _ _ mo _ AT SF HH HL realtime_ok_zeros). }
    { intros evs X Hss.
      destruct (vd_step_complete VS _ _ _ _ mo evs X AT SF HH HL Hss) as (bs & _ & E1 & E2).
      subst evs X. split; [reflexivity | eexists; reflexivity]. }
    intros evs c' Hss.
    destruct (vd_step_complete VS _ _ _ _ mo evs (SNext c') AT SF HH HL Hss) as (bs & HBS & _ & E2).
    (* [injection] reduces the configuration it extracts (vd_npost unfolds); project it out
       with beta and iota only, so the node's post stays folded for [ts_npost_MS] below *)
    pose proof (f_equal (fun st => match st with SNext x => x | _ => c' end) E2) as E3.
    cbv beta iota in E3. subst c'.
    lazymatch goal with
    | |- sreach _ _ (mkCfg (vd_npost ?sg (VDRealtime ?tpz ?dd ?cc)
          (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20
                   ?r21 ?r22 ?r23 ?r24 ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?F0 ?pc0 ?fc0 ?rv0 ?mm ?ro0)
          (mkEffectU _ [(_, ?bb)] _ _ _ _)) _) =>
        destruct (ts_npost_MS sg tpz dd cc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
                    r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 F0 pc0 fc0 rv0 mm ro0 bb VFR)
          as (z1 & z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & fr & EQ);
        rewrite EQ; clear EQ
    end.
    rewrite (ts_sub_lit (bv_unsigned sp + -80) 240).
    replace (bv_unsigned sp + -80 - 240) with (bv_unsigned sp + -320) by lia.
    change (Z_to_bv 64 (bv_unsigned sp + -320)) with (wa (bv_unsigned sp + -320)).
    pose proof (firstn_le_length 240 fr) as FL.
    pose proof (realtime_ok_length bs HBS) as L16.
    assert (SP320 : 0 <= bv_unsigned sp + -320) by lia.
    (* the frame write: only [sp - 320, sp - 80), only where the writable view has a byte *)
    pose proof (vwf_munch VS (firstn 240%nat fr) m1 (bv_unsigned sp + -320) SP320 ltac:(lia)) as MUf.
    pose proof (vwf_mem_inv VS (firstn 240%nat fr) m1 (wa (bv_unsigned sp + -320)) MI1) as MIf.
    pose proof (vwf_stk VS (firstn 240%nat fr) m1 (wa (bv_unsigned sp + -320)) lo _ ST1) as STf.
    assert (WMf : wmono VS m1 (vdso_write_frame VS m1 (wa (bv_unsigned sp + -320)) (firstn 240%nat fr)))
      by (intros x Hx; exact (vwf_wmono VS _ m1 _ x Hx)).
    remember (vdso_write_frame VS m1 (wa (bv_unsigned sp + -320)) (firstn 240%nat fr)) as m1f eqn:Em1f.
    clear Em1f.
    trw FRa MUf WMf. trw FRb MUf WMf. trw VF1 MUf WMf. trw CAN1 MUf WMf.
    destruct (ts_cells_split VS m1f (bv_unsigned sp + -48) [CB 16 junk16]
                [C8 (Z_to_bv 64 hcanary); C8 s1; C8 s0; C8 ra] FRa) as [FR16 FRr].
    cbn [cells_size csize Nat.add] in FRr.
    replace (bv_unsigned sp + -48 + Z.of_nat 16) with (bv_unsigned sp + -32) in FRr by lia.
    (* the effect: 16 bytes of the timespec *)
    pose proof (rw_cells_CB_prefix_write VS m1f (bv_unsigned sp + -48) 16 junk16 bs FR16 ltac:(lia)) as W16.
    rewrite L16 in W16. change (16 - 16)%nat with 0%nat in W16.
    pose proof (mem_inv_syswrite VS m1f (bv_unsigned sp + -48) 16 junk16 bs MIf FR16 ltac:(lia)) as MI2.
    trwr FRr (bv_unsigned sp + -48) bs. trwr FRb (bv_unsigned sp + -48) bs.
    trwr VF1 (bv_unsigned sp + -48) bs. trwr CAN1 (bv_unsigned sp + -48) bs.
    pose proof (stk_write VS m1f lo (bv_unsigned sp + -80) (bv_unsigned sp + -48) bs STf ltac:(lia) ltac:(lia)) as ST2.
    assert (MUd : munch [(bv_unsigned sp - 320, bv_unsigned sp); (3000480, 3000480 + 8)]%Z m
                        (write_to_mem m1f (wa (bv_unsigned sp + -48)) bs)).
    { apply munch_write; [| lia | lia | cbn [inside]; lia].
      apply (munch_trans _ m m1 m1f).
      - eapply munch_weaken; [| exact MU1]. intros x Hx. cbn [outside] in Hx |- *. lia.
      - eapply munch_weaken; [| exact MUf]. intros x Hx. cbn [outside] in Hx |- *. lia. }
    assert (WMd : wmono VS m (write_to_mem m1f (wa (bv_unsigned sp + -48)) bs)).
    { apply wmono_write. exact (wmono_trans VS m m1 m1f WM1 WMf). }
    pose proof (tr_wmono_back _ _ WMd) as WMr.

    (* 3. clock_gettime's return and time()'s *)
    eapply (cj_evt_sreach_k VS); [exact HH | exact HL | |].
    { exact (time_back_v z1 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31
               sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 F fc _ lo hcanary bs _ junk8
               W16 FRr FRb CAN1 HCANB ST2 CLO ltac:(lia)). }
    intros ms3 PB.
    destruct PB as (u0 & u1 & u2 & tv & q1 & q2 & q3 & q4 & q5 & q6 & q7 & u3 & u4 & u5 & u6 & -> & ST3).
    apply sr_done.
    exists (mkCfg (MS (mkR ra sp gp tp u0 u1 u2 s0 s1 tv q1 q2 q3 q4 q5 q6 q7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                      F (ret_pc ra) fc None (write_to_mem m1f (wa (bv_unsigned sp + -48)) bs) (seg_rom rsegs))
                  (with_vdso_bump mo)).
    split; [reflexivity|].
    unfold time_sr_post.
    exists u0, u1, u2, tv, q1, q2, q3, q4, q5, q6, q7, u3, u4, u5, u6, (write_to_mem m1f (wa (bv_unsigned sp + -48)) bs).
    cbn [cfg_ms cfg_model hs_KREL hs_MPRES hs_RHEAP hs_rauxv_ok].
    split; [reflexivity|].
    split.
    { (* the kernel relation and the pair after [with_vdso_bump] *)
      split.
      - apply (KM_vm s mo (with_vdso_bump mo) KMs).
        + pose proof KMs as (L & _ & Kk & _). pose proof (kb_minv _ _ _ Kk) as (Q1 & Q2 & Q3).
          split; [exact Q1 | split; [exact Q2 | exact Q3]].
        + exact HH.
        + reflexivity.
        + reflexivity.
      - destruct PI as [PI1 PI2]. split.
        + apply (mm_vinv_frame vlo vmid mo); first [reflexivity | exact PI1].
        + apply (mm_vinv_frame vmid vhi mo); first [reflexivity | exact PI2]. }
    split.
    { repeat split; reflexivity. }
    split.
    { eapply rv_mem_inv; first [exact MI2 | exact Hnx | exact Hnw]. }
    split.
    { apply tr_stk_back; [lia | exact ST3]. }
    split.
    { eapply rw_cells_transport; [exact ERR | exact MUd | exact WMr |].
      rewrite ETP. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    split.
    { split; [| exact BTS].
      eapply rauxv_ok_frame; [exact AUX0 | exact MUd | exact WMr |].
      unfold RAUXV_CELL. constructor; [cbn; lia|]. constructor; [cbn; lia | constructor]. }
    split.
    { split; [| split; [exact (tr_vclean_of_inv _ MI2) | exact BO]].
      eapply RHEAP_frame_proof; [exact HR0 | exact MUd | exact WMr |].
      unfold rclient_write_ok, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP.
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia | constructor]. }
    split.
    { eapply munch_weaken; [| exact MUd]. intros x Hx. unfold TIME_STACK, A_vdso_func in Hx.
      cbn [outside] in Hx |- *. lia. }
    split.
    { exact WMr. }
    apply tr_rw_cells_back; [unfold A_vdso_func; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact VF1].
  Qed.

End TimeRun.
