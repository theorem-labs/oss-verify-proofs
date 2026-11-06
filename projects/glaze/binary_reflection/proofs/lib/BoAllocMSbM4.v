(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM4s.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma rz_sec : forall n, (64512 < n)%Z -> rz n = 2048%Z.
Proof.
  intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold rz, rz_log in G in change_no_check G' end).
  repeat (match goal with |- context [Z.leb n ?k] => destruct (Z.leb_spec n k) as [?|?]; [exfalso; lia|] end). reflexivity.
Qed.
Lemma sec_needed_eq : forall n, (64512 < n)%Z -> sec_needed n = (rounded n + 4096)%Z.
Proof. intros n Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_needed in G in change_no_check G' end). rewrite (rz_sec n Hn). lia. Qed.

Lemma sec_needed_bnd : forall n, (64512 < n)%Z -> (n + 4096 <= sec_needed n <= n + 4103)%Z.
Proof.
  intros n Hn. rewrite (sec_needed_eq n Hn). (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end).
  pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Section FPGen1.
Context {fx : FPState}.

Section AMCS.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL2 : code_ato segs rb 0x4c834 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K67770 := BoAllocM4.K67770 segs rb HAL2.
  Let K67774 := BoAllocM4.K67774 segs rb HAL2.
  Let K67778 := BoAllocM4.K67778 segs rb HAL2.
  Let K6777c := BoAllocM4.K6777c segs rb HAL2.
  Let K67780 := BoAllocM4.K67780 segs rb HAL2.
  Let K67784 := BoAllocM4.K67784 segs rb HAL2.
  Let K67790 := BoAllocM4.K67790 segs rb HAL2.
  Let K67794 := BoAllocM4.K67794 segs rb HAL2.
  Let K67798 := BoAllocM4.K67798 segs rb HAL2.
  Let K6779c := BoAllocM4.K6779c segs rb HAL2.
  Let K677a0 := BoAllocM4.K677a0 segs rb HAL2.
  Let K677a4 := BoAllocM4.K677a4 segs rb HAL2.
  Let K677a8 := BoAllocM4.K677a8 segs rb HAL2.
  Let K677ac := BoAllocM4.K677ac segs rb HAL2.
  Let K677b0 := BoAllocM4.K677b0 segs rb HAL2.
  Let K677b4 := BoAllocM4.K677b4 segs rb HAL2.
  Let K677b8 := BoAllocM4.K677b8 segs rb HAL2.
  Let K677bc := BoAllocM4.K677bc segs rb HAL2.
  Let K677c0 := BoAllocM4.K677c0 segs rb HAL2.
  Let K677c4 := BoAllocM4.K677c4 segs rb HAL2.
  Let K677c8 := BoAllocM4.K677c8 segs rb HAL2.
  Let K677cc := BoAllocM4.K677cc segs rb HAL2.
  Let K677d0 := BoAllocM4.K677d0 segs rb HAL2.
  Let K677d4 := BoAllocM4.K677d4 segs rb HAL2.
  Let K677d8 := BoAllocM4.K677d8 segs rb HAL2.
  Let K677dc := BoAllocM4.K677dc segs rb HAL2.
  Let K677e0 := BoAllocM4.K677e0 segs rb HAL2.
  Let K677e4 := BoAllocM4.K677e4 segs rb HAL2.
  Let K67870 := BoAllocM4.K67870 segs rb HAL2.
  Let K67874 := BoAllocM4.K67874 segs rb HAL2.
  Let K67878 := BoAllocM4.K67878 segs rb HAL2.

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp m stk thr ctx tr szw : word) (bsz : list byte) (b1 : byte) (n tid : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr regs 10 = m.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (sec_needed n).
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (rz n).
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 n.
  Hypothesis H23 : getr regs 23 = stk.
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 7.
  Hypothesis H26 : getr regs 26 = thr.
  Hypothesis H27 : getr regs 27 = Z_to_bv 64 1.
  Hypothesis Hn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis Htid : (0 <= tid < 2 ^ 31)%Z.
  Hypothesis Gm : (U m mod 16 = 0)%Z /\ (4096 <= U m)%Z /\ (U m + sec_needed n + 4096 <= 2 ^ 63)%Z.   (* [comment removed for export] *)
  Hypothesis Gsp : (2 ^ 32 <= U sp)%Z /\ (U sp + 144 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis Gthr : (4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= 2 ^ 64)%Z.   (* [comment removed for export] *)
  Hypothesis Gctx : (U ctx + 16 <= 2 ^ 64)%Z.
  Hypothesis Gstk : (U stk + 16 <= 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis Rb1 : rdn segs mem (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok segs mem (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn segs mem (at_ sp 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis Rctx : rdn segs mem thr 8 = Some (LE8 ctx).
  Hypothesis Rtid : rdn segs mem (at_ ctx 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn segs mem stk 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn segs mem (at_ stk 8) 8 = Some bsz.
  Hypothesis Hbsz : bytes_le_to_Z bsz = U szw /\ length bsz = 8%nat.
  Hypothesis Dsp : (U m + rz n <= U sp + 16 \/ U sp + 24 <= U m + rz n - 16)%Z.
  Hypothesis Dthr : (U m + rz n <= U thr \/ U thr + 8 <= U m + rz n - 16)%Z.
  Hypothesis Dctx : (U m + rz n <= U ctx + 8 \/ U ctx + 12 <= U m + rz n - 16)%Z.
  Hypothesis Dstk : (U m + rz n <= U stk \/ U stk + 16 <= U m + rz n - 16)%Z.

  #[local] Abbreviation CLC := (fun r => In r (18 :: 20 :: 21 :: 24 :: 25 :: 1 :: 5 :: 6 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: nil)).

  Definition amCs_mem : word -> option byte :=
    let w1 := hb0w (Z_to_bv 64 (U b1)) in
    wbytes (wbytes (wbytes (wbytes mem (at_ m (rz n - 15)) [Z_to_bv 8 (U w1)]) (at_ m (rz n - 14)) (LE2 (n / 2 ^ 32))) (at_ m (rz n - 12)) (LE4 n))
           (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1))))].
  Lemma amCs_mem_outside : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> amCs_mem x = mem x.
  Proof using Hbsz Gsp Gm Hn bsz szw sp rb.
    intros x Hx. pose proof (u64_range m). destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n).
    assert (Erz : rz n = 2048%Z) by (apply rz_sec; lia).
    assert (Hrz2 : (16 <= rz n <= 2048)%Z) by lia.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    (lazymatch goal with |- ?G => let G' := eval unfold amCs_mem in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity.
  Qed.

  Theorem amCs_run :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4c834) mem rom) (mkst r (at_ rb 0x8f4f0) amCs_mem rom)
      /\ getr r 1 = at_ rb 0x4c940 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 18 = m /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ regs_agree CLC regs r.
  Proof using Dstk Dctx Dthr Dsp Hbsz Rsz Rtr Rtid Rctx R16 SOKh Rb1 Gstk Gctx Gthr Gsp Gm Htid Hn H27 H26 H25 H23 H21 H20 H19 H10 H9 H2 bsz ctx thr stk sp K67878 K67874 K67870 K677e4 K677e0 K677dc K677d8 K677d4 K677d0 K677cc K677c8 K677c4 K677c0 K677bc K677b8 K677b4 K677b0 K677ac K677a8 K677a4 K677a0 K6779c K67798 K67794 K67790 K67784 K67780 K6777c K67778 K67774 K67770 HAL2.
    pose proof (u64_range m) as Hmr. pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctx) as Hctx.
    pose proof (u64_range stk) as Hstk. pose proof (u8_range b1) as Hb1.
    destruct Gm as (Gm1 & Gm2 & Gm3). destruct Gsp as [Gs1 Gs2]. destruct Gthr as [Gt1 Gt2]. pose proof (rz_log_range n) as HRL.
    assert (Erz : rz n = 2048%Z) by (apply rz_sec; lia).
    assert (Hrz2 : (16 <= rz n <= 2048)%Z) by lia.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (Hrz16 : (rz n mod 16 = 0)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end); rewrite Z.mul_comm; apply Z_mod_mult).
    assert (Hnd : (sec_needed n = rounded n + 4096)%Z) by (apply sec_needed_eq; lia).
    assert (Hrd2 : (Z.max n 8 <= rounded n <= Z.max n 8 + 7)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    set (M1 := wbytes mem (at_ m (rz n - 15)) [Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1))))]).
    set (M2 := wbytes M1 (at_ m (rz n - 14)) (LE2 (n / 2 ^ 32))).
    set (M3 := wbytes M2 (at_ m (rz n - 12)) (LE4 n)).
    assert (M3_out : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> M3 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3, M2, M1 in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity. }
    assert (AM_out : forall x : word, (U x < U m + rz n - 16 \/ U m + rz n <= U x)%Z -> amCs_mem x = mem x) by exact amCs_mem_outside.
    Ltac cellC R OUT := rewrite <- R; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply OUT; rewrite ?at_u in Hx by lia; cbn in Hx; lia].
    assert (R16' : rdn segs M3 (at_ sp 16) 8 = Some (LE8 (Z_to_bv 64 16))) by cellC R16 M3_out.
    assert (Rctx' : rdn segs amCs_mem thr 8 = Some (LE8 ctx)) by cellC Rctx AM_out.
    assert (Rtid' : rdn segs amCs_mem (at_ ctx 8) 4 = Some (LE4 tid)) by cellC Rtid AM_out.
    assert (Rtr' : rdn segs amCs_mem stk 8 = Some (LE8 tr)) by cellC Rtr AM_out.
    assert (Rsz' : rdn segs amCs_mem (at_ stk 8) 8 = Some bsz) by cellC Rsz AM_out.
    Ltac sok SOKh k N := repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs mem (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOKh | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    assert (Hp8 : ((U m + rz n) mod 8 = 0)%Z) by (apply mod16_sum8; [exact Gm1 | exact Hrz16]).
    assert (SOK1 : store_ok segs M1 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOKh]).
    assert (SOK2 : store_ok segs M2 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOK1]).
    assert (SOK3 : store_ok segs M3 (at_ m (rz n - 16)) 16 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); eapply store_ok_mono; [apply wbytes_grows | exact SOK2]).
    Ltac sok16 SOK := eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
               first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
    wd_eexists. split.
    - an K67770 D_4c834.                                   (* [comment removed for export] *)
      ab_ft K67774 D_4c838 ltac:(condz).                  (* [comment removed for export] *)
      av K67778 D_4c83c (at_ m (rz n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      an K6777c D_4c840.                                   (* [comment removed for export] *)
      replace (v_and (at_ m (rz n)) (Z_to_bv 64 7)) with (Z_to_bv 64 0)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite at_u by lia; f_equal; change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact Hp8).
      av K67780 D_4c844 (Z_to_bv 64 (sec_needed n + U m)) ltac:(vz).   (* [comment removed for export] *)
      ab_tk K67784 D_4c848 ltac:(condz).                  (* [comment removed for export] *)
      av K67790 D_4c854 (at_ m (rz n + n)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
      ab_ft K67794 D_4c858 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := b1); [exact K67798 | reflexivity | exact D_4c85c
          | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rb1; f_equal; f_equal; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K6779c D_4c860.                                   (* [comment removed for export] *)
      an K677a0 D_4c864.                                   (* [comment removed for export] *)
      an K677a4 D_4c868.                                   (* [comment removed for export] *)
      change (v_or (v_andi (Z_to_bv 64 (U b1)) (-4)) (Z_to_bv 64 1)) with (hb0w (Z_to_bv 64 (U b1))).
      av K677a8 D_4c86c (Z_to_bv 64 (n / 2 ^ 32)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
      av K677ac D_4c870 (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1)))));
          [exact K677b0 | reflexivity | exact D_4c874 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes mem _ _) with M1.
      chain_step; [reflexivity
        | eapply step_sh_at with (a := at_ m (rz n - 14)) (v := Z_to_bv 64 (n / 2 ^ 32));
          [exact K677b4 | reflexivity | exact D_4c878 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK1]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M2.
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ m (rz n - 12)) (v := Z_to_bv 64 n);
          [exact K677b8 | reflexivity | exact D_4c87c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK2]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M2 _ _) with M3.
      ab_ft K677bc D_4c880 ltac:(condz).                  (* [comment removed for export] *)
      av K677c0 D_4c884 (at_ m (rz n - 16)) ltac:(rewrite at_addi; f_equal; lia).   (* [comment removed for export] *)
      an K677c4 D_4c888.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 16)) (v := Z_to_bv 64 16);
          [exact K677c8 | reflexivity | exact D_4c88c | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; fold_at_vars; exact R16' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K677cc D_4c890.                                   (* [comment removed for export] *)
      change (v_or (v_andi (hb0w (Z_to_bv 64 (U b1))) 143) (Z_to_bv 64 16)) with (hb1w (Z_to_bv 64 (U b1))).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))));
          [exact K677d0 | reflexivity | exact D_4c894 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOK3]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M3 _ _) with amCs_mem.
      ab_ft K677d4 D_4c898 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ctx) (v := ctx);
          [exact K677d8 | reflexivity | exact D_4c89c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rctx' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 tid)) (v := Z_to_bv 64 tid);
          [exact K677dc | reflexivity | exact D_4c8a0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rtid' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small tid) by lia; vn.    (* [comment removed for export] *)
      av K677e0 D_4c8a4 (Z_to_bv 64 (tid * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an K677e4 D_4c8a8.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tr) (v := tr);
          [exact K67870 | reflexivity | exact D_4c934 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rtr' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := bsz) (v := szw);
          [exact K67874 | reflexivity | exact D_4c938 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rsz' | exact (proj1 Hbsz)]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K67878 D_4c93c.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AMCS.
End FPGen1.
End BoAllocM4s.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 BoAllocM4s.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma land_neg_pow2 : forall x k, (0 <= x)%Z -> (0 <= k)%Z -> Z.land x (- 2 ^ k) = (x - x mod 2 ^ k)%Z.
Proof.
  intros x k Hx Hk. assert (E : (- 2 ^ k)%Z = (Z.lnot (Z.ones k))).
  { rewrite Z.ones_equiv. (lazymatch goal with |- ?G => let G' := eval unfold Z.lnot in G in change_no_check G' end). set (q := (2 ^ k)%Z). lia. }
  rewrite E.
  rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2 ^ k) ltac:(apply Z.pow_nonzero; lia)) as D. set (q := (2 ^ k)%Z) in *. set (d := (x / q)%Z) in *. set (r := (x mod q)%Z) in *.
  rewrite (Z.mul_comm d q). lia.
Qed.

Lemma land_wrapw_neg_pow2 : forall w x k, (0 <= w)%Z -> (0 <= x < 2 ^ w)%Z -> (0 <= k)%Z -> Z.land x ((- 2 ^ k) mod 2 ^ w) = (x - x mod 2 ^ k)%Z.
Proof.
  intros w x k Hw Hx Hk. rewrite <- Z.land_ones by lia. rewrite Z.land_assoc. rewrite Z.land_ones by lia.
  rewrite land_neg_pow2 by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound x (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)).
  pose proof (Z.mod_le x (2 ^ k) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)). lia.
Qed.
Lemma land_wrap_neg_pow2 : forall x k, (0 <= x < 2 ^ 64)%Z -> (0 <= k)%Z -> Z.land x ((- 2 ^ k) mod 2 ^ 64) = (x - x mod 2 ^ k)%Z.
Proof. intros x k. apply land_wrapw_neg_pow2. lia. Qed.
Lemma land_48m8s : forall x, (0 <= x < 2 ^ 48)%Z -> Z.land x (2 ^ 48 - 8) = (x - x mod 8)%Z.
Proof. intros x Hx. change (2 ^ 48 - 8)%Z with ((- 2 ^ 3) mod 2 ^ 48)%Z. rewrite land_wrapw_neg_pow2 by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition sbre (um n : Z) : Z := (um + rz n + n + 7 - (um + rz n + n + 7) mod 8)%Z.
(* [comment removed for export] *)
Definition sbasz (n : Z) : Z := (sec_needed n + 4095 - (sec_needed n + 4095) mod 4096)%Z.

Lemma sbre_bnd : forall um n, (um + rz n + n <= sbre um n <= um + rz n + n + 7)%Z /\ (sbre um n mod 8 = 0)%Z.
Proof. intros um n. (lazymatch goal with |- ?G => let G' := eval unfold sbre in G in change_no_check G' end). set (x := (um + rz n + n + 7)%Z). replace (um + rz n + n)%Z with (x - 7)%Z by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); lia). clearbody x. Z.div_mod_to_equations. lia. Qed.
Lemma sbasz_bnd : forall n, (sec_needed n <= sbasz n <= sec_needed n + 4095)%Z /\ (sbasz n mod 4096 = 0)%Z.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold sbasz in G in change_no_check G' end). set (x := (sec_needed n + 4095)%Z). replace (sec_needed n) with (x - 4095)%Z by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); lia). clearbody x. Z.div_mod_to_equations. lia. Qed.

Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
           first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

Section FPGen1.
Context {fx : FPState}.

Section AMDS.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL2 : code_ato segs rb 0x4c834 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K6787c := BoAllocM4.K6787c segs rb HAL2.
  Let K67880 := BoAllocM4.K67880 segs rb HAL2.
  Let K67884 := BoAllocM4.K67884 segs rb HAL2.
  Let K67888 := BoAllocM4.K67888 segs rb HAL2.
  Let K6788c := BoAllocM4.K6788c segs rb HAL2.
  Let K678ac := BoAllocM4.K678ac segs rb HAL2.
  Let K678b0 := BoAllocM4.K678b0 segs rb HAL2.
  Let K678b4 := BoAllocM4.K678b4 segs rb HAL2.
  Let K678b8 := BoAllocM4.K678b8 segs rb HAL2.
  Let K678bc := BoAllocM4.K678bc segs rb HAL2.
  Let K678c0 := BoAllocM4.K678c0 segs rb HAL2.
  Let K678e8 := BoAllocM4.K678e8 segs rb HAL2.
  Let K678ec := BoAllocM4.K678ec segs rb HAL2.
  Let K678f0 := BoAllocM4.K678f0 segs rb HAL2.
  Let K678f4 := BoAllocM4.K678f4 segs rb HAL2.
  Let K678f8 := BoAllocM4.K678f8 segs rb HAL2.
  Let K678fc := BoAllocM4.K678fc segs rb HAL2.
  Let K67900 := BoAllocM4.K67900 segs rb HAL2.
  Let K67904 := BoAllocM4.K67904 segs rb HAL2.
  Let K67908 := BoAllocM4.K67908 segs rb HAL2.
  Let K6790c := BoAllocM4.K6790c segs rb HAL2.
  Let K67910 := BoAllocM4.K67910 segs rb HAL2.
  Let K67914 := BoAllocM4.K67914 segs rb HAL2.
  Let K6793c := BoAllocM4.K6793c segs rb HAL2.
  Let K67940 := BoAllocM4.K67940 segs rb HAL2.
  Let K67944 := BoAllocM4.K67944 segs rb HAL2.
  Let K67948 := BoAllocM4.K67948 segs rb HAL2.
  Let K6794c := BoAllocM4.K6794c segs rb HAL2.
  Let K67950 := BoAllocM4.K67950 segs rb HAL2.
  Let K67954 := BoAllocM4.K67954 segs rb HAL2.
  Let K67958 := BoAllocM4.K67958 segs rb HAL2.
  Let K6795c := BoAllocM4.K6795c segs rb HAL2.
  Let K67960 := BoAllocM4.K67960 segs rb HAL2.
  Let K67964 := BoAllocM4.K67964 segs rb HAL2.
  Let K67968 := BoAllocM4.K67968 segs rb HAL2.
  Let K6796c := BoAllocM4.K6796c segs rb HAL2.
  Let K67970 := BoAllocM4.K67970 segs rb HAL2.
  Let K67974 := BoAllocM4.K67974 segs rb HAL2.
  Let K67978 := BoAllocM4.K67978 segs rb HAL2.
  Let K6797c := BoAllocM4.K6797c segs rb HAL2.
  Let K67980 := BoAllocM4.K67980 segs rb HAL2.
  Let K67984 := BoAllocM4.K67984 segs rb HAL2.
  Let K67988 := BoAllocM4.K67988 segs rb HAL2.
  Let K6798c := BoAllocM4.K6798c segs rb HAL2.
  Let K67990 := BoAllocM4.K67990 segs rb HAL2.
  Let K6799c := BoAllocM4.K6799c segs rb HAL2.
  Let K679a0 := BoAllocM4.K679a0 segs rb HAL2.
  Let K679a4 := BoAllocM4.K679a4 segs rb HAL2.
  Let K679a8 := BoAllocM4.K679a8 segs rb HAL2.
  Let K679ac := BoAllocM4.K679ac segs rb HAL2.
  Let K679b0 := BoAllocM4.K679b0 segs rb HAL2.
  Let K679b4 := BoAllocM4.K679b4 segs rb HAL2.
  Let K679c8 := BoAllocM4.K679c8 segs rb HAL2.
  Let K679cc := BoAllocM4.K679cc segs rb HAL2.
  Let K679d0 := BoAllocM4.K679d0 segs rb HAL2.
  Let K679d4 := BoAllocM4.K679d4 segs rb HAL2.
  Let K679e4 := BoAllocM4.K679e4 segs rb HAL2.
  Let K679e8 := BoAllocM4.K679e8 segs rb HAL2.
  Let K679ec := BoAllocM4.K679ec segs rb HAL2.
  Let K679f0 := BoAllocM4.K679f0 segs rb HAL2.
  Let K679f4 := BoAllocM4.K679f4 segs rb HAL2.
  Let K67a00 := BoAllocM4.K67a00 segs rb HAL2.
  Let K67a04 := BoAllocM4.K67a04 segs rb HAL2.
  Let K67a08 := BoAllocM4.K67a08 segs rb HAL2.
  Let K67a0c := BoAllocM4.K67a0c segs rb HAL2.
  Let K67a10 := BoAllocM4.K67a10 segs rb HAL2.
  Let K67a14 := BoAllocM4.K67a14 segs rb HAL2.
  Let K67a18 := BoAllocM4.K67a18 segs rb HAL2.
  Let K67a20 := BoAllocM4.K67a20 segs rb HAL2.
  Let K67a24 := BoAllocM4.K67a24 segs rb HAL2.
  Let K67a28 := BoAllocM4.K67a28 segs rb HAL2.
  Let K67a2c := BoAllocM4.K67a2c segs rb HAL2.
  Let K67a30 := BoAllocM4.K67a30 segs rb HAL2.
  Let K67a34 := BoAllocM4.K67a34 segs rb HAL2.
  Let K67a38 := BoAllocM4.K67a38 segs rb HAL2.
  Let K67a3c := BoAllocM4.K67a3c segs rb HAL2.
  Let K67a40 := BoAllocM4.K67a40 segs rb HAL2.
  Let K67a44 := BoAllocM4.K67a44 segs rb HAL2.
  Let K67a48 := BoAllocM4.K67a48 segs rb HAL2.
  Let K67a4c := BoAllocM4.K67a4c segs rb HAL2.
  Let K67a50 := BoAllocM4.K67a50 segs rb HAL2.
  Let K67a54 := BoAllocM4.K67a54 segs rb HAL2.
  Let K67a58 := BoAllocM4.K67a58 segs rb HAL2.
  Let K67a5c := BoAllocM4.K67a5c segs rb HAL2.
  Let K67a60 := BoAllocM4.K67a60 segs rb HAL2.
  Let K67a64 := BoAllocM4.K67a64 segs rb HAL2.
  Let K67b84 := BoAllocM4.K67b84 segs rb HAL2.
  Let K67b88 := BoAllocM4.K67b88 segs rb HAL2.
  Let K67b8c := BoAllocM4.K67b8c segs rb HAL2.
  Let K67b90 := BoAllocM4.K67b90 segs rb HAL2.
  Let K67b94 := BoAllocM4.K67b94 segs rb HAL2.
  Let K67ba0 := BoAllocM4.K67ba0 segs rb HAL2.
  Let K67ba4 := BoAllocM4.K67ba4 segs rb HAL2.
  Let K67ba8 := BoAllocM4.K67ba8 segs rb HAL2.
  Let K67bac := BoAllocM4.K67bac segs rb HAL2.

  Variables (rom : word -> option byte) (m : word) (n tid : Z).
  Hypothesis Hn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis Htid : (0 <= tid < 2 ^ 31)%Z.
  (* [comment removed for export] *)
  Hypothesis Gm : (U m mod 4096 = 0)%Z /\ (8192 <= U m)%Z /\ (U m + sec_needed n + 4096 <= 2 ^ 47)%Z.

  Lemma sec_arith : rz n = 2048%Z /\ (n + 4096 <= sec_needed n <= n + 4103)%Z /\ (0 <= n mod 8 < 8)%Z /\ (n mod 8 <= n)%Z.
  Proof using Hn m rb.
    split; [apply rz_sec; lia|]. split; [apply sec_needed_bnd; lia|].
    split; [apply Z.mod_pos_bound; lia | apply Z.mod_le; lia].
  Qed.

  #[local] Abbreviation sb_re := (sbre (U m) n).
  #[local] Abbreviation sb_asz := (sbasz n).

  Lemma amD1s : forall (M : word -> option byte) r0 (id sbeg : Z),
    (0 <= id < 2 ^ 32)%Z ->
    getr r0 10 = Z_to_bv 64 id -> getr r0 8 = Z_to_bv 64 0 -> getr r0 9 = Z_to_bv 64 n -> getr r0 18 = m -> getr r0 20 = at_ m (rz n) ->
    getr r0 21 = at_ m (rz n - 16) -> getr r0 22 = Z_to_bv 64 0x10ab58 -> getr r0 24 = Z_to_bv 64 (tid * 2 ^ 32) -> getr r0 25 = at_ m (rz n + n) ->
    store_ok segs M (at_ m (rz n - 16)) 16 = true ->
    (0 <= sbeg /\ sbeg + 2 ^ 37 < 2 ^ 64)%Z -> (U m < sbeg \/ sbeg + 2 ^ 37 <= U m)%Z ->
    (U m + sec_needed n <= AIMGLO \/ AIMGHI <= U m)%Z ->
    rdn segs M (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 sbeg)) ->
    rdn segs M (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn segs M (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c940) M rom) (mkst r (at_ rb 0x70080) (amD_mem m n tid M id) rom)
      /\ getr r 1 = at_ rb 0x4ca18 /\ getr r 10 = m /\ getr r 11 = Z_to_bv 64 2048 /\ getr r 12 = Z_to_bv 64 250
      /\ getr r 8 = Z_to_bv 64 sb_asz /\ getr r 22 = Z_to_bv 64 sb_re
      /\ regs_agree (fun x => In x [1; 8; 10; 11; 12; 22; 25]) r0 r.
  Proof using Gm Htid Hn K67950 K6794c K67948 K67944 K67940 K6793c K67914 K67910 K6790c K67908 K67904 K67900 K678fc K678f8 K678f4 K678f0 K678ec K678e8 K678c0 K678bc K678b8 K678b4 K678b0 K678ac K6788c K67888 K67884 K67880 K6787c RB HAL2.
    intros M r0 id sbeg Hid R10 R8 R9 R18 R20 R21 R22 R24 R25 SOK Hsb Dsb Dimg Rsb Rpg Rsz.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9).
    set (M' := amD_mem m n tid M id).
    assert (M'_out : forall x : word, (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z -> M' x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M', amD_mem in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rsb' : rdn segs M' (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 sbeg))).
    { rewrite <- Rsb. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rpg' : rdn segs M' (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096))).
    { rewrite <- Rpg. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rsz' : rdn segs M' (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n)))).
    { rewrite <- Rsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M'_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ rb 0x4c940) M rom) (mkst r1 (at_ rb 0x4c974) M' rom)
               /\ getr r1 10 = Z_to_bv 64 sbeg /\ regs_agree (fun x => In x [10]) r0 r1).
    { wd_eexists. split.
      - av K6787c D_4c940 (Z_to_bv 64 (id * 2 ^ 32)) ltac:(vz).            (* [comment removed for export] *)
        av K67880 D_4c944 (Z_to_bv 64 id) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_mul; lia).  (* [comment removed for export] *)
        an K67884 D_4c948.                                                   (* [comment removed for export] *)
        rewrite (v_or_shl (Z_to_bv 64 id) tid 32) by (wd_ulia).
        replace (tid * 2 ^ 32 + U (Z_to_bv 64 id))%Z with (tid * 2 ^ 32 + id)%Z by (unorm; reflexivity).
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ m (rz n - 8));
            [exact K67888 | reflexivity | exact D_4c94c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity
            | eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        change (wbytes M _ _) with M'.
        ab_tk K6788c D_4c950 ltac:(condz).                                  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 sbeg)) (v := Z_to_bv 64 sbeg);
            [exact K678ac | reflexivity | exact D_4c970 | gres; rwH; imm_norm; exact Rsb' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve. }
    destruct W1 as (r1 & RUN1 & A10 & AG1).
    assert (B18 : getr r1 18 = m) by (rewrite (AG1 18) by notin_list; exact R18).
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4c974) M' rom) (mkst r2 (at_ rb 0x4c9ac) M' rom)
               /\ regs_agree (fun x => In x [11]) r1 r2).
    { destruct Dsb as [Dlo|Dhi].
      - wd_eexists. split; [ab_tk K678b0 D_4c974 ltac:(condz); wd_refl | intros i Hi; reflexivity].   (* [comment removed for export] *)
      - wd_eexists. split.
        + ab_ft K678b0 D_4c974 ltac:(condz).                                (* [comment removed for export] *)
          an K678b4 D_4c978.                                                 (* [comment removed for export] *)
          an K678b8 D_4c97c.                                                 (* [comment removed for export] *)
          av K678bc D_4c980 (Z_to_bv 64 (sbeg + 2 ^ 37)) ltac:(vz).         (* [comment removed for export] *)
          ab_tk K678c0 D_4c984 ltac:(condz).                                (* [comment removed for export] *)
          wd_refl.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & AG2).
    assert (K2 : forall i : reg, i <> 10 -> i <> 11 -> getr r2 i = getr r0 i).
    { intros i N10 N11. rewrite (AG2 i) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [X|[]]; apply N11; symmetry; exact X).
      apply AG1. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros [X|[]]. apply N10. symmetry. exact X. }
    assert (C18 : getr r2 18 = m) by (rewrite K2 by (intros E; discriminate E); exact R18).
    assert (C20 : getr r2 20 = at_ m (rz n)) by (rewrite K2 by (intros E; discriminate E); exact R20).
    assert (C22 : getr r2 22 = Z_to_bv 64 0x10ab58) by (rewrite K2 by (intros E; discriminate E); exact R22).
    assert (C25 : getr r2 25 = at_ m (rz n + n)) by (rewrite K2 by (intros E; discriminate E); exact R25).
    assert (W3 : exists r3, msteps segs (mkst r2 (at_ rb 0x4c9ac) M' rom) (mkst r3 (at_ rb 0x70080) M' rom)
               /\ getr r3 1 = at_ rb 0x4ca18 /\ getr r3 10 = m /\ getr r3 11 = Z_to_bv 64 2048 /\ getr r3 12 = Z_to_bv 64 250
               /\ getr r3 8 = Z_to_bv 64 sb_asz /\ getr r3 22 = Z_to_bv 64 sb_re
               /\ regs_agree (fun x => In x [1; 8; 10; 11; 12; 22; 25]) r2 r3).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
            [exact K678e8 | reflexivity | exact D_4c9ac | gres; rwH; imm_norm; exact Rpg' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        an K678ec D_4c9b0.                                                   (* [comment removed for export] *)
        an K678f0 D_4c9b4.                                                   (* [comment removed for export] *)
        match goal with |- context [v_and ?a ?b] =>
          replace (v_and a b) with (Z_to_bv 64 0)
            by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 4095%Z with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; exact Gm1) end.
        ab_ft K678f4 D_4c9b8 ltac:(condz).                                  (* [comment removed for export] *)
        an K678f8 D_4c9bc.                                                   (* [comment removed for export] *)
        ab_ft K678fc D_4c9c0 ltac:(condz).                                  (* [comment removed for export] *)
        av K67900 D_4c9c4 (at_ m (-4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 (sec_needed n))) (v := Z_to_bv 64 (sec_needed n));
            [exact K67904 | reflexivity | exact D_4c9c8 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Rsz' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        av K67908 D_4c9cc (Z_to_bv 64 (sec_needed n + 4095)) ltac:(vz).     (* [comment removed for export] *)
        an K6790c D_4c9d0.                                                   (* [comment removed for export] *)
        an K67910 D_4c9d4.                                                   (* [comment removed for export] *)
        match goal with |- context [v_and ?a ?b] =>
          replace (v_and a b) with (Z_to_bv 64 sb_asz)
            by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and, v_sub, sbasz in G in change_no_check G' end); unorm; f_equal; change 18446744073709547520%Z with ((- 2 ^ 12) mod 2 ^ 64)%Z; rewrite land_wrap_neg_pow2 by lia; reflexivity) end.
        an K67914 D_4c9d8.                                                   (* [comment removed for export] *)
        av K6793c D_4ca00 (at_ m (rz n + n + 7)) ltac:(rewrite ?at_addi; reflexivity).   (* [comment removed for export] *)
        av K67940 D_4ca04 (Z_to_bv 64 sb_re) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi, sbre in G in change_no_check G' end); rewrite at_u by lia; unorm; f_equal; change (bv_wrap 64 (-8)) with ((- 2 ^ 3) mod 2 ^ 64)%Z; rewrite land_wrap_neg_pow2 by lia; change (2 ^ 3)%Z with 8%Z; f_equal; [lia | f_equal; lia]).                  (* [comment removed for export] *)
        av K67944 D_4ca08 (Z_to_bv 64 2048) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); rewrite at_u by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
        an K67948 D_4ca0c.                                                   (* [comment removed for export] *)
        an K6794c D_4ca10.                                                   (* [comment removed for export] *)
        an K67950 D_4ca14.                                                   (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve. }
    destruct W3 as (r3 & RUN3 & D1 & D10 & D11 & D12 & D8 & D22 & AG3).
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split; [exact D1|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D8|]. split; [exact D22|].
    intros i Hi. rewrite (AG3 i Hi). apply K2; intros E; apply Hi; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto.
  Qed.


  (* [comment removed for export] *)
  Lemma amD1b : forall (M : word -> option byte) r0,
    getr r0 18 = m -> getr r0 22 = Z_to_bv 64 sb_re -> getr r0 8 = Z_to_bv 64 sb_asz ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca18) M rom) (mkst r (at_ rb 0x70080) M rom)
      /\ getr r 1 = at_ rb 0x4ca2c /\ getr r 10 = Z_to_bv 64 sb_re /\ getr r 11 = Z_to_bv 64 (U m + sb_asz - sb_re) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Gm Hn K67964 K67960 K6795c K67958 K67954 HAL2.
    intros M r0 R18 R22 R8.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9).
    pose proof (sbre_bnd (U m) n) as [Hre _]. pose proof (sbasz_bnd n) as [Hasz _].
    wd_eexists. split.
    - an K67954 D_4ca18.                                                   (* [comment removed for export] *)
      av K67958 D_4ca1c (Z_to_bv 64 (U m + sb_asz - sb_re)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, v_sub in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end); change (bv_modulus 64) with (2 ^ 64)%Z;
          rewrite (Z.mod_small sb_re), (Z.mod_small sb_asz) by lia; rewrite Zplus_mod_idemp_l; f_equal; lia).   (* [comment removed for export] *)
      an K6795c D_4ca20.                                                   (* [comment removed for export] *)
      an K67960 D_4ca24.                                                   (* [comment removed for export] *)
      an K67964 D_4ca28.                                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma amD1c : forall (M : word -> option byte) r0,
    getr r0 9 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca2c) M rom) (mkst r (at_ rb 0x4ca38) M rom)
      /\ getr r 22 = Z_to_bv 64 (n - n mod 8)
      /\ regs_agree (fun x => In x [10; 22]) r0 r.
  Proof using Hn m K67970 K6796c K67968 HAL2.
    intros M r0 R9.
    wd_eexists. split.
    - an K67968 D_4ca2c.                                                   (* [comment removed for export] *)
      an K6796c D_4ca30.                                                   (* [comment removed for export] *)
      an K67970 D_4ca34.                                                   (* [comment removed for export] *)
      match goal with |- context [v_and (Z_to_bv 64 n) ?msk] =>
        replace (v_and (Z_to_bv 64 n) msk) with (Z_to_bv 64 (n - n mod 8))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; imm_norm; apply land_48m8s; lia) end.
      wd_refl.
    - post. ra_solve.
  Qed.

  Lemma amD2s : forall (M : word -> option byte) r0,
    (8 <= n)%Z -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca38) M rom) (mkst r (at_ rb 0x70080) M rom)
      /\ getr r 1 = at_ rb 0x4ca4c /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 (n - n mod 8) /\ getr r 12 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Gm Hn K67984 K67980 K6797c K67978 K67974 HAL2.
    intros M r0 Hn8 R22 R20. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    wd_eexists. split.
    - ab_ft K67974 D_4ca38 ltac:(condz).                  (* [comment removed for export] *)
      an K67978 D_4ca3c. an K6797c D_4ca40. an K67980 D_4ca44.   (* [comment removed for export] *)
      an K67984 D_4ca48.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Variable gSB : Z.                     (* [comment removed for export] *)
  Variables (psb : word) (SB : Z).
  Hypothesis GgSB : (AIMGLO <= gSB /\ gSB + 8 <= AIMGHI)%Z.
  Hypothesis Gpsb : (AIMGLO <= U psb /\ U psb + 8 <= AIMGHI)%Z.
  Hypothesis GSB : (0 < SB <= 0x7fff8000)%Z /\ (SB + U m / 8 + 1 <= 2 ^ 62)%Z.
  Variables (g_cpm gMB gME gHE gFL : Z) (pmb pme phe pfl : word) (midend : word) (pp : byte).
  Hypothesis CPM : code_ato segs rb 0x7006c cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x7006c 10 g_cpm.
  Hypothesis GLSB2 : gload segs rb 0x4ca58 10 gSB.
  Hypothesis GLMB : gload segs rb 0x4ca7c 12 gMB.
  Hypothesis GLME : gload segs rb 0x4ca84 13 gME.
  Hypothesis GLHE : gload segs rb 0x4caa0 13 gHE.
  Hypothesis GLFL : gload segs rb 0x4cabc 11 gFL.
  (* [comment removed for export] *)
  Hypothesis Gcells : Forall (fun c => AIMGLO <= c /\ c + 8 <= AIMGHI)%Z [g_cpm; gMB; gME; gHE; gFL] /\ (AIMGLO <= U pmb /\ U pmb + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pme /\ U pme + 8 <= AIMGHI)%Z
                      /\ (AIMGLO <= U phe /\ U phe + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pfl /\ U pfl + 128 <= AIMGHI)%Z.

  Lemma amE1zs : forall (M : word -> option byte) r0,
    (n mod 8 = 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) ->
    msteps segs (mkst r0 (at_ rb 0x4ca4c) M rom) (mkst r0 (at_ rb 0x4cae0) M rom).
  Proof using Hn m K67988 HAL2.
    intros M r0 Hm R9 R22. ab_tk K67988 D_4ca4c ltac:(rewrite Hm, Z.sub_0_r; condz). wd_refl.
  Qed.

  Lemma amE1s : forall (M : word -> option byte) r0,
    (U m + sec_needed n <= SB - 1 \/ 0x10007fff8000 <= U m)%Z ->
    (n mod 8 <> 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    rdn segs M (Z_to_bv 64 g_cpm) 1 = Some [Z_to_bv 8 1] ->
    rdn segs M (Z_to_bv 64 gSB) 8 = Some (LE8 psb) -> rdn segs M psb 8 = Some (LE8 (Z_to_bv 64 SB)) ->
    rdn segs M (Z_to_bv 64 gMB) 8 = Some (LE8 pmb) -> rdn segs M pmb 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn segs M (Z_to_bv 64 gME) 8 = Some (LE8 pme) -> rdn segs M pme 8 = Some (LE8 midend) ->
    rdn segs M (Z_to_bv 64 gHE) 8 = Some (LE8 phe) -> rdn segs M phe 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)) ->
    rdn segs M (Z_to_bv 64 gFL) 8 = Some (LE8 pfl) -> rdn segs M (at_ pfl 85) 1 = Some [Z_to_bv 8 1] ->
    store_ok segs M (Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8)) 1 = true ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4ca4c) M rom) (mkst r (at_ rb 0x4cae0) (amE1_mem m n SB M) rom)
      /\ regs_agree (fun x => In x [22; 1; 10; 11; 12; 13; 14; 15; 16; 17]) r0 r.
  Proof using Gcells GLFL GLHE GLME GLMB GLSB2 GCPM CPM GSB Gm Hn K67a18 K67a14 K67a10 K67a0c K67a08 K67a04 K67a00 K679f4 K679f0 K679ec K679e8 K679e4 K679d4 K679d0 K679cc K679c8 K679b4 K679b0 K679ac K679a8 K679a4 K679a0 K6799c K67990 K6798c K67988 RB HAL2.
    intros M r0 Grng Hm R9 R22 R20 Rcpm RgSB RSB RgMB RMB RgME RME RgHE RHE RgFL Rpp SOK.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n) as HRL. destruct GSB as [GS1 GS2].
    destruct Gcells as (GC & Gpmb & Gpme & Gphe & Gpfl).
    pose proof (u64_range pmb). pose proof (u64_range pme). pose proof (u64_range phe). pose proof (u64_range pfl). pose proof (u64_range psb).
    assert (Erz : rz n = 2048%Z) by (apply rz_sec; lia).
    assert (Hrz2 : (16 <= rz n <= 2048)%Z) by lia.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm8. pose proof (Z.mod_le n 8 ltac:(lia) ltac:(lia)) as Hm9.
    set (e := (U m + rz n + (n - n mod 8))%Z).
    destruct (cpm_run segs rb g_cpm CPM GCPM M rom (regupd r0 1 (at_ rb 0x4ca54)) (at_ rb 0x4ca54) Rcpm) as (r1 & RUN1 & A10 & AG1).
    { apply ret_ok_at; [exact (proj1 RB) | reflexivity | pose proof (u64_range rb); pose proof (proj2 RB); lia]. }
    { gres. reflexivity. }
    assert (B20 : getr r1 20 = at_ m (rz n)) by (rewrite (AG1 20) by notin_list; gres; exact R20).
    assert (B22 : getr r1 22 = Z_to_bv 64 (n - n mod 8)) by (rewrite (AG1 22) by notin_list; gres; exact R22).
    assert (B9 : getr r1 9 = Z_to_bv 64 n) by (rewrite (AG1 9) by notin_list; gres; exact R9).
    destruct Grng as [Glo|Ghi].
    - (* [comment removed for export] *)
      assert (Hd : (0 <= e / 8)%Z /\ (SB + e / 8 < 2 ^ 47)%Z /\ (e <= SB - 1)%Z).
      { split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)). unfold e in *. lia. }
      wd_eexists. split.
      + idtac.
        ab_ft K67988 D_4ca4c ltac:(condz).                  (* [comment removed for export] *)
        an K6798c D_4ca50.                                   (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        ab_ft K67990 D_4ca54 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
            [exact K6799c | reflexivity | exact D_4ca60 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K679a0 D_4ca64 (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av K679a4 D_4ca68 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
        an K679a8 D_4ca6c.                                   (* [comment removed for export] *)
        replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
          by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        an K679ac D_4ca70.                                   (* [comment removed for export] *)
        an K679b0 D_4ca74.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
        ab_tk K679b4 D_4ca78 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 1); [exact K67a00 | reflexivity | exact D_4cac4
            | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K67a04 D_4cac8 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av K67a08 D_4cacc (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
        an K67a0c D_4cad0.                                   (* [comment removed for export] *)
        an K67a10 D_4cad4.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        av K67a14 D_4cad8 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
            [exact K67a18 | reflexivity | exact D_4cadc | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        change (wbytes M _ _) with (amE1_mem m n SB M).
        wd_refl.
      + ra_chain.
    - (* [comment removed for export] *)
      assert (He : (0x10007fff8000 <= e)%Z /\ (e + 8 <= 2 ^ 47)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); lia).
      assert (Hd : (0 <= e / 8)%Z /\ (SB + e / 8 < 2 ^ 47)%Z /\ (0x10007fff7fff < e)%Z).
      { split; [apply Z.div_pos; lia|]. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)). lia. }
      wd_eexists. split.
      + idtac.
        ab_ft K67988 D_4ca4c ltac:(condz).                  (* [comment removed for export] *)
        an K6798c D_4ca50.                                   (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        ab_ft K67990 D_4ca54 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
            [exact K6799c | reflexivity | exact D_4ca60 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K679a0 D_4ca64 (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av K679a4 D_4ca68 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
        an K679a8 D_4ca6c.                                   (* [comment removed for export] *)
        replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
          by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        an K679ac D_4ca70.                                   (* [comment removed for export] *)
        an K679b0 D_4ca74.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
        ab_ft K679b4 D_4ca78 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLMB _ M rom pmb RgMB)|]. zlit_at.   (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLME _ M rom pme RgME)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
            [exact K679c8 | reflexivity | exact D_4ca8c | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RMB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 midend) (v := midend);
            [exact K679cc | reflexivity | exact D_4ca90 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RME | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        an K679d0 D_4ca94.                                   (* [comment removed for export] *)
        ab_tk K679d4 D_4ca98 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLHE _ M rom phe RgHE)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 0x7fffffffffff)) (v := Z_to_bv 64 0x7fffffffffff);
            [exact K679e4 | reflexivity | exact D_4caa8 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RHE | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        an K679e8 D_4caac.                                   (* [comment removed for export] *)
        av K679ec D_4cab0 (Z_to_bv 64 (0xfffffffffff + SB)) ltac:(vz).   (* [comment removed for export] *)
        ab_ft K679f0 D_4cab4 ltac:(condz).                  (* [comment removed for export] *)
        ab_ft K679f4 D_4cab8 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 1); [exact K67a00 | reflexivity | exact D_4cac4
            | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K67a04 D_4cac8 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av K67a08 D_4cacc (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
        an K67a0c D_4cad0.                                   (* [comment removed for export] *)
        an K67a10 D_4cad4.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        av K67a14 D_4cad8 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
            [exact K67a18 | reflexivity | exact D_4cadc | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        change (wbytes M _ _) with (amE1_mem m n SB M).
        wd_refl.
      + ra_chain.
  Qed.

  (* [comment removed for export] *)
  Variables (sp thr : word).
  Hypothesis Gsp : (2 ^ 32 <= U sp)%Z /\ (U sp + 144 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr)%Z /\ (U thr + 4096 <= 2 ^ 64)%Z.

  Definition amE2s_mem (M : word -> option byte) (w0 w8 w16 w104 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes M (at_ thr 2800) (LE8 w0)) (at_ thr 2808) (LE8 w8)) (at_ thr 2816) (LE8 w16)) (at_ thr 2904) (LE8 w104).

  Lemma amE2sa : forall (M : word -> option byte) r0 (v0 v8 v16 v104 : word),
    getr r0 10 = at_ thr 2800 -> getr r0 9 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (sec_needed n) ->
    rdn segs M (at_ thr 2800) 8 = Some (LE8 v0) -> rdn segs M (at_ thr 2808) 8 = Some (LE8 v8) -> rdn segs M (at_ thr 2816) 8 = Some (LE8 v16) ->
    rdn segs M (at_ thr 2904) 8 = Some (LE8 v104) ->
    store_ok segs M (at_ thr 2800) 112 = true ->
    exists r w0 w8 w16 w104, msteps segs (mkst r0 (at_ rb 0x4cae4) M rom) (mkst r (at_ rb 0x4cb24) (amE2s_mem M w0 w8 w16 w104) rom)
      /\ regs_agree (fun x => In x [11; 12; 13; 14]) r0 r.
  Proof using Gthr Gm Hn m K67a5c K67a58 K67a54 K67a50 K67a4c K67a48 K67a44 K67a40 K67a3c K67a38 K67a34 K67a30 K67a2c K67a28 K67a24 K67a20 HAL2.
    intros M r0 v0 v8 v16 v104 R10 R9 R19 Rv0 Rv8 Rv16 Rv104 SOK.
    pose proof (u64_range thr) as Hthr. destruct Gthr as [Gt1 Gt2]. pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9). destruct Gm as (Gm1 & Gm2 & Gm3).
    Ltac sok112 SOK := repeat (eapply store_ok_mono; [apply wbytes_grows|]);
      eapply (store_ok_sub segs _ (at_ thr 2800) _ 112); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
    Ltac setlast :=
      lazymatch goal with
      | |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => first [is_var v | let t := fresh "w" in set (t := v)]
      | |- _ => idtac
      end.
    eexists _, _, _, _, _. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v16) (v := v16);
          [exact K67a20 | reflexivity | exact D_4cae4 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv16 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v0) (v := v0);
          [exact K67a24 | reflexivity | exact D_4cae8 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; zlit_at; exact Rv0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v8) (v := v8);
          [exact K67a28 | reflexivity | exact D_4caec | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv8 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K67a2c D_4caf0 (Z_to_bv 64 (sec_needed n - n)) ltac:(vz).   (* [comment removed for export] *)
      an K67a30 D_4caf4. setlast.                          (* [comment removed for export] *)
      an K67a34 D_4caf8. an K67a38 D_4cafc.               (* [comment removed for export] *)
      an K67a3c D_4cb00. setlast.                          (* [comment removed for export] *)
      an K67a40 D_4cb04. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2800);
          [exact K67a44 | reflexivity | exact D_4cb08 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2808);
          [exact K67a48 | reflexivity | exact D_4cb0c | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2816);
          [exact K67a4c | reflexivity | exact D_4cb10 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      ab_ft K67a50 D_4cb14 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v104) (v := v104);
          [exact K67a54 | reflexivity | exact D_4cb18
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; rewrite <- Rv104; apply rdn_ext;
            [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
            | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx;
              rewrite !wbytes_outside; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K67a58 D_4cb1c. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2904);
          [exact K67a5c | reflexivity | exact D_4cb20 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ (wbytes (wbytes (wbytes (wbytes M _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ (word_to_le_bytes 8 ?c)) _ (word_to_le_bytes 8 ?d)) _) _ =>
        change (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) with (amE2s_mem M a b c d) end.
      wd_refl.
    - ra_chain.
  Qed.

  Variables (gFL3 gRMS : Z) (prms msetw : word) (fillw : Z).
  Hypothesis GLFL3 : gload segs rb 0x4cc40 10 gFL3.
  Hypothesis GLRMS : gload segs rb 0x4cc5c 11 gRMS.
  Hypothesis Gfillw : (0 <= fillw < 2 ^ 31)%Z.
  Hypothesis MSOK : ret_ok msetw.

  Lemma amE2sc : forall (M : word -> option byte) r0,
    getr r0 9 = Z_to_bv 64 n -> getr r0 20 = at_ m (rz n) -> getr r0 2 = sp ->
    rdn segs M (at_ sp 8) 8 = Some (LE8 (Z_to_bv 64 1)) ->
    rdn segs M (Z_to_bv 64 gFL3) 8 = Some (LE8 pfl) -> rdn segs M (at_ pfl 44) 4 = Some (LE4 4096) -> rdn segs M (at_ pfl 52) 4 = Some (LE4 fillw) ->
    rdn segs M (Z_to_bv 64 gRMS) 8 = Some (LE8 prms) -> rdn segs M prms 8 = Some (LE8 msetw) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4cb24) M rom) (mkst r msetw M rom)
      /\ getr r 1 = at_ rb 0x4cc74 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 fillw /\ getr r 12 = Z_to_bv 64 4096
      /\ regs_agree (fun x => In x [1; 10; 11; 12; 13]) r0 r.
  Proof using MSOK Gfillw GLRMS GLFL3 Gsp Gcells phe pme pmb gFL gHE gME gMB g_cpm Gm Hn K67bac K67ba8 K67ba4 K67ba0 K67b94 K67b90 K67b8c K67b88 K67b84 K67a64 K67a60 HAL2.
    intros M r0 R9 R20 R2 Rfill RgFL Rmmf Rfb RgRMS Rrms.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range pfl). destruct Gsp as [Gs1 Gs2]. destruct Gcells as (_ & _ & _ & _ & Gpfl).
    pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9). destruct Gm as (Gm1 & Gm2 & Gm3).
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
          [exact K67a60 | reflexivity | exact D_4cb24 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rfill | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                (* [comment removed for export] *)
      ab_tk K67a64 D_4cb28 ltac:(condz).                                 (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLFL3 _ _ rom pfl); exact RgFL|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
          [exact K67b84 | reflexivity | exact D_4cc48 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rmmf | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small 4096) by lia; vn.              (* [comment removed for export] *)
      ab_ft K67b88 D_4cc4c ltac:(condz).                                 (* [comment removed for export] *)
      an K67b8c D_4cc50.                                                  (* [comment removed for export] *)
      ab_ft K67b90 D_4cc54 ltac:(condz).                                 (* [comment removed for export] *)
      an K67b94 D_4cc58.                                                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLRMS _ _ rom prms); exact RgRMS|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 msetw) (v := msetw);
          [exact K67ba0 | reflexivity | exact D_4cc64 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rrms | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fillw)) (v := Z_to_bv 64 fillw);
          [exact K67ba4 | reflexivity | exact D_4cc68 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rfb | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small fillw) by lia; vn.                (* [comment removed for export] *)
      an K67ba8 D_4cc6c.                                                    (* [comment removed for export] *)
      aret K67bac D_4cc70 msetw.                                            (* [comment removed for export] *)
      rewrite ?at_addi; zlit_at. wd_refl.
    - post. all: try (rewrite ?at_add_0_r; reflexivity). ra_solve.
  Qed.

End AMDS.
End FPGen1.
