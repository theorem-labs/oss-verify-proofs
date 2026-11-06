(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM4s.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4.
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
  Hypothesis HAL2 : code_ato segs rb 0x4bdc4 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K66cf8 := AsAllocM4.K66cf8 segs rb HAL2.
  Let K66cfc := AsAllocM4.K66cfc segs rb HAL2.
  Let K66d00 := AsAllocM4.K66d00 segs rb HAL2.
  Let K66d04 := AsAllocM4.K66d04 segs rb HAL2.
  Let K66d08 := AsAllocM4.K66d08 segs rb HAL2.
  Let K66d0c := AsAllocM4.K66d0c segs rb HAL2.
  Let K66d18 := AsAllocM4.K66d18 segs rb HAL2.
  Let K66d1c := AsAllocM4.K66d1c segs rb HAL2.
  Let K66d20 := AsAllocM4.K66d20 segs rb HAL2.
  Let K66d24 := AsAllocM4.K66d24 segs rb HAL2.
  Let K66d28 := AsAllocM4.K66d28 segs rb HAL2.
  Let K66d2c := AsAllocM4.K66d2c segs rb HAL2.
  Let K66d30 := AsAllocM4.K66d30 segs rb HAL2.
  Let K66d34 := AsAllocM4.K66d34 segs rb HAL2.
  Let K66d38 := AsAllocM4.K66d38 segs rb HAL2.
  Let K66d3c := AsAllocM4.K66d3c segs rb HAL2.
  Let K66d40 := AsAllocM4.K66d40 segs rb HAL2.
  Let K66d44 := AsAllocM4.K66d44 segs rb HAL2.
  Let K66d48 := AsAllocM4.K66d48 segs rb HAL2.
  Let K66d4c := AsAllocM4.K66d4c segs rb HAL2.
  Let K66d50 := AsAllocM4.K66d50 segs rb HAL2.
  Let K66d54 := AsAllocM4.K66d54 segs rb HAL2.
  Let K66d58 := AsAllocM4.K66d58 segs rb HAL2.
  Let K66d5c := AsAllocM4.K66d5c segs rb HAL2.
  Let K66d60 := AsAllocM4.K66d60 segs rb HAL2.
  Let K66d64 := AsAllocM4.K66d64 segs rb HAL2.
  Let K66d68 := AsAllocM4.K66d68 segs rb HAL2.
  Let K66d6c := AsAllocM4.K66d6c segs rb HAL2.
  Let K66df8 := AsAllocM4.K66df8 segs rb HAL2.
  Let K66dfc := AsAllocM4.K66dfc segs rb HAL2.
  Let K66e00 := AsAllocM4.K66e00 segs rb HAL2.

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
      msteps segs (mkst regs (at_ rb 0x4bdc4) mem rom) (mkst r (at_ rb 0x8ea80) amCs_mem rom)
      /\ getr r 1 = at_ rb 0x4bed0 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 18 = m /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ regs_agree CLC regs r.
  Proof using Dstk Dctx Dthr Dsp Hbsz Rsz Rtr Rtid Rctx R16 SOKh Rb1 Gstk Gctx Gthr Gsp Gm Htid Hn H27 H26 H25 H23 H21 H20 H19 H10 H9 H2 bsz ctx thr stk sp K66e00 K66dfc K66df8 K66d6c K66d68 K66d64 K66d60 K66d5c K66d58 K66d54 K66d50 K66d4c K66d48 K66d44 K66d40 K66d3c K66d38 K66d34 K66d30 K66d2c K66d28 K66d24 K66d20 K66d1c K66d18 K66d0c K66d08 K66d04 K66d00 K66cfc K66cf8 HAL2.
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
    - an K66cf8 D_4bdbc.                                   (* [comment removed for export] *)
      ab_ft K66cfc D_4bdc0 ltac:(condz).                  (* [comment removed for export] *)
      av K66d00 D_4bdc4 (at_ m (rz n)) ltac:(rewrite v_add_at by lia; reflexivity).   (* [comment removed for export] *)
      an K66d04 D_4bdc8.                                   (* [comment removed for export] *)
      replace (v_and (at_ m (rz n)) (Z_to_bv 64 7)) with (Z_to_bv 64 0)
        by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; rewrite at_u by lia; f_equal; change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact Hp8).
      av K66d08 D_4bdcc (Z_to_bv 64 (sec_needed n + U m)) ltac:(vz).   (* [comment removed for export] *)
      ab_tk K66d0c D_4bdd0 ltac:(condz).                  (* [comment removed for export] *)
      av K66d18 D_4bddc (at_ m (rz n + n)) ltac:(rewrite v_add_at by lia; rewrite at_at; reflexivity).   (* [comment removed for export] *)
      ab_ft K66d1c D_4bde0 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu with (b := b1); [exact K66d20 | reflexivity | exact D_4bde4
          | gres; rwH; imm_norm; rewrite ?at_addi; rewrite <- Rb1; f_equal; f_equal; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66d24 D_4bde8.                                   (* [comment removed for export] *)
      an K66d28 D_4bdec.                                   (* [comment removed for export] *)
      an K66d2c D_4bdf0.                                   (* [comment removed for export] *)
      change (v_or (v_andi (Z_to_bv 64 (U b1)) (-4)) (Z_to_bv 64 1)) with (hb0w (Z_to_bv 64 (U b1))).
      av K66d30 D_4bdf4 (Z_to_bv 64 (n / 2 ^ 32)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
      av K66d34 D_4bdf8 (Z_to_bv 64 0) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_small; lia).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb0w (Z_to_bv 64 (U b1)))));
          [exact K66d38 | reflexivity | exact D_4bdfc | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOKh]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes mem _ _) with M1.
      chain_step; [reflexivity
        | eapply step_sh_at with (a := at_ m (rz n - 14)) (v := Z_to_bv 64 (n / 2 ^ 32));
          [exact K66d3c | reflexivity | exact D_4be00 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK1]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M2.
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ m (rz n - 12)) (v := Z_to_bv 64 n);
          [exact K66d40 | reflexivity | exact D_4be04 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | sok16 SOK2]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M2 _ _) with M3.
      ab_ft K66d44 D_4be08 ltac:(condz).                  (* [comment removed for export] *)
      av K66d48 D_4be0c (at_ m (rz n - 16)) ltac:(rewrite at_addi; f_equal; lia).   (* [comment removed for export] *)
      an K66d4c D_4be10.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 16)) (v := Z_to_bv 64 16);
          [exact K66d50 | reflexivity | exact D_4be14 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; fold_at_vars; exact R16' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66d54 D_4be18.                                   (* [comment removed for export] *)
      change (v_or (v_andi (hb0w (Z_to_bv 64 (U b1))) 143) (Z_to_bv 64 16)) with (hb1w (Z_to_bv 64 (U b1))).
      chain_step; [reflexivity
        | eapply step_sb_at with (a := at_ m (rz n - 15)) (b := Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))));
          [exact K66d58 | reflexivity | exact D_4be1c | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity | reflexivity | sok16 SOK3]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M3 _ _) with amCs_mem.
      ab_ft K66d5c D_4be20 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 ctx) (v := ctx);
          [exact K66d60 | reflexivity | exact D_4be24 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rctx' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 tid)) (v := Z_to_bv 64 tid);
          [exact K66d64 | reflexivity | exact D_4be28 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rtid' | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small tid) by lia; vn.    (* [comment removed for export] *)
      av K66d68 D_4be2c (Z_to_bv 64 (tid * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      an K66d6c D_4be30.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 tr) (v := tr);
          [exact K66df8 | reflexivity | exact D_4bebc | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rtr' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := bsz) (v := szw);
          [exact K66dfc | reflexivity | exact D_4bec0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rsz' | exact (proj1 Hbsz)]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66e00 D_4bec4.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AMCS.
End FPGen1.
End AsAllocM4s.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 AsAllocM4s.
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
  Hypothesis HAL2 : code_ato segs rb 0x4bdc4 al2_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K66e04 := AsAllocM4.K66e04 segs rb HAL2.
  Let K66e08 := AsAllocM4.K66e08 segs rb HAL2.
  Let K66e0c := AsAllocM4.K66e0c segs rb HAL2.
  Let K66e10 := AsAllocM4.K66e10 segs rb HAL2.
  Let K66e14 := AsAllocM4.K66e14 segs rb HAL2.
  Let K66e34 := AsAllocM4.K66e34 segs rb HAL2.
  Let K66e38 := AsAllocM4.K66e38 segs rb HAL2.
  Let K66e3c := AsAllocM4.K66e3c segs rb HAL2.
  Let K66e40 := AsAllocM4.K66e40 segs rb HAL2.
  Let K66e44 := AsAllocM4.K66e44 segs rb HAL2.
  Let K66e48 := AsAllocM4.K66e48 segs rb HAL2.
  Let K66e70 := AsAllocM4.K66e70 segs rb HAL2.
  Let K66e74 := AsAllocM4.K66e74 segs rb HAL2.
  Let K66e78 := AsAllocM4.K66e78 segs rb HAL2.
  Let K66e7c := AsAllocM4.K66e7c segs rb HAL2.
  Let K66e80 := AsAllocM4.K66e80 segs rb HAL2.
  Let K66e84 := AsAllocM4.K66e84 segs rb HAL2.
  Let K66e88 := AsAllocM4.K66e88 segs rb HAL2.
  Let K66e8c := AsAllocM4.K66e8c segs rb HAL2.
  Let K66e90 := AsAllocM4.K66e90 segs rb HAL2.
  Let K66e94 := AsAllocM4.K66e94 segs rb HAL2.
  Let K66e98 := AsAllocM4.K66e98 segs rb HAL2.
  Let K66e9c := AsAllocM4.K66e9c segs rb HAL2.
  Let K66ec4 := AsAllocM4.K66ec4 segs rb HAL2.
  Let K66ec8 := AsAllocM4.K66ec8 segs rb HAL2.
  Let K66ecc := AsAllocM4.K66ecc segs rb HAL2.
  Let K66ed0 := AsAllocM4.K66ed0 segs rb HAL2.
  Let K66ed4 := AsAllocM4.K66ed4 segs rb HAL2.
  Let K66ed8 := AsAllocM4.K66ed8 segs rb HAL2.
  Let K66edc := AsAllocM4.K66edc segs rb HAL2.
  Let K66ee0 := AsAllocM4.K66ee0 segs rb HAL2.
  Let K66ee4 := AsAllocM4.K66ee4 segs rb HAL2.
  Let K66ee8 := AsAllocM4.K66ee8 segs rb HAL2.
  Let K66eec := AsAllocM4.K66eec segs rb HAL2.
  Let K66ef0 := AsAllocM4.K66ef0 segs rb HAL2.
  Let K66ef4 := AsAllocM4.K66ef4 segs rb HAL2.
  Let K66ef8 := AsAllocM4.K66ef8 segs rb HAL2.
  Let K66efc := AsAllocM4.K66efc segs rb HAL2.
  Let K66f00 := AsAllocM4.K66f00 segs rb HAL2.
  Let K66f04 := AsAllocM4.K66f04 segs rb HAL2.
  Let K66f08 := AsAllocM4.K66f08 segs rb HAL2.
  Let K66f0c := AsAllocM4.K66f0c segs rb HAL2.
  Let K66f10 := AsAllocM4.K66f10 segs rb HAL2.
  Let K66f14 := AsAllocM4.K66f14 segs rb HAL2.
  Let K66f18 := AsAllocM4.K66f18 segs rb HAL2.
  Let K66f24 := AsAllocM4.K66f24 segs rb HAL2.
  Let K66f28 := AsAllocM4.K66f28 segs rb HAL2.
  Let K66f2c := AsAllocM4.K66f2c segs rb HAL2.
  Let K66f30 := AsAllocM4.K66f30 segs rb HAL2.
  Let K66f34 := AsAllocM4.K66f34 segs rb HAL2.
  Let K66f38 := AsAllocM4.K66f38 segs rb HAL2.
  Let K66f3c := AsAllocM4.K66f3c segs rb HAL2.
  Let K66f50 := AsAllocM4.K66f50 segs rb HAL2.
  Let K66f54 := AsAllocM4.K66f54 segs rb HAL2.
  Let K66f58 := AsAllocM4.K66f58 segs rb HAL2.
  Let K66f5c := AsAllocM4.K66f5c segs rb HAL2.
  Let K66f6c := AsAllocM4.K66f6c segs rb HAL2.
  Let K66f70 := AsAllocM4.K66f70 segs rb HAL2.
  Let K66f74 := AsAllocM4.K66f74 segs rb HAL2.
  Let K66f78 := AsAllocM4.K66f78 segs rb HAL2.
  Let K66f7c := AsAllocM4.K66f7c segs rb HAL2.
  Let K66f88 := AsAllocM4.K66f88 segs rb HAL2.
  Let K66f8c := AsAllocM4.K66f8c segs rb HAL2.
  Let K66f90 := AsAllocM4.K66f90 segs rb HAL2.
  Let K66f94 := AsAllocM4.K66f94 segs rb HAL2.
  Let K66f98 := AsAllocM4.K66f98 segs rb HAL2.
  Let K66f9c := AsAllocM4.K66f9c segs rb HAL2.
  Let K66fa0 := AsAllocM4.K66fa0 segs rb HAL2.
  Let K66fa8 := AsAllocM4.K66fa8 segs rb HAL2.
  Let K66fac := AsAllocM4.K66fac segs rb HAL2.
  Let K66fb0 := AsAllocM4.K66fb0 segs rb HAL2.
  Let K66fb4 := AsAllocM4.K66fb4 segs rb HAL2.
  Let K66fb8 := AsAllocM4.K66fb8 segs rb HAL2.
  Let K66fbc := AsAllocM4.K66fbc segs rb HAL2.
  Let K66fc0 := AsAllocM4.K66fc0 segs rb HAL2.
  Let K66fc4 := AsAllocM4.K66fc4 segs rb HAL2.
  Let K66fc8 := AsAllocM4.K66fc8 segs rb HAL2.
  Let K66fcc := AsAllocM4.K66fcc segs rb HAL2.
  Let K66fd0 := AsAllocM4.K66fd0 segs rb HAL2.
  Let K66fd4 := AsAllocM4.K66fd4 segs rb HAL2.
  Let K66fd8 := AsAllocM4.K66fd8 segs rb HAL2.
  Let K66fdc := AsAllocM4.K66fdc segs rb HAL2.
  Let K66fe0 := AsAllocM4.K66fe0 segs rb HAL2.
  Let K66fe4 := AsAllocM4.K66fe4 segs rb HAL2.
  Let K66fe8 := AsAllocM4.K66fe8 segs rb HAL2.
  Let K66fec := AsAllocM4.K66fec segs rb HAL2.
  Let K6710c := AsAllocM4.K6710c segs rb HAL2.
  Let K67110 := AsAllocM4.K67110 segs rb HAL2.
  Let K67114 := AsAllocM4.K67114 segs rb HAL2.
  Let K67118 := AsAllocM4.K67118 segs rb HAL2.
  Let K6711c := AsAllocM4.K6711c segs rb HAL2.
  Let K67128 := AsAllocM4.K67128 segs rb HAL2.
  Let K6712c := AsAllocM4.K6712c segs rb HAL2.
  Let K67130 := AsAllocM4.K67130 segs rb HAL2.
  Let K67134 := AsAllocM4.K67134 segs rb HAL2.

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
    getr r0 21 = at_ m (rz n - 16) -> getr r0 22 = Z_to_bv 64 0x103f18 -> getr r0 24 = Z_to_bv 64 (tid * 2 ^ 32) -> getr r0 25 = at_ m (rz n + n) ->
    store_ok segs M (at_ m (rz n - 16)) 16 = true ->
    (0 <= sbeg /\ sbeg + 2 ^ 37 < 2 ^ 64)%Z -> (U m < sbeg \/ sbeg + 2 ^ 37 <= U m)%Z ->
    (U m + sec_needed n <= AIMGLO \/ AIMGHI <= U m)%Z ->
    rdn segs M (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 sbeg)) ->
    rdn segs M (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
    rdn segs M (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bed0) M rom) (mkst r (at_ rb 0x6f610) (amD_mem m n tid M id) rom)
      /\ getr r 1 = at_ rb 0x4bfa8 /\ getr r 10 = m /\ getr r 11 = Z_to_bv 64 2048 /\ getr r 12 = Z_to_bv 64 250
      /\ getr r 8 = Z_to_bv 64 sb_asz /\ getr r 22 = Z_to_bv 64 sb_re
      /\ regs_agree (fun x => In x [1; 8; 10; 11; 12; 22; 25]) r0 r.
  Proof using Gm Htid Hn K66ed8 K66ed4 K66ed0 K66ecc K66ec8 K66ec4 K66e9c K66e98 K66e94 K66e90 K66e8c K66e88 K66e84 K66e80 K66e7c K66e78 K66e74 K66e70 K66e48 K66e44 K66e40 K66e3c K66e38 K66e34 K66e14 K66e10 K66e0c K66e08 K66e04 RB HAL2.
    intros M r0 id sbeg Hid R10 R8 R9 R18 R20 R21 R22 R24 R25 SOK Hsb Dsb Dimg Rsb Rpg Rsz.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9).
    set (M' := amD_mem m n tid M id).
    assert (M'_out : forall x : word, (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z -> M' x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M', amD_mem in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rsb' : rdn segs M' (Z_to_bv 64 0x103f38) 8 = Some (LE8 (Z_to_bv 64 sbeg))).
    { rewrite <- Rsb. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rpg' : rdn segs M' (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096))).
    { rewrite <- Rpg. apply rdn_ext; [wd_ulia_c | intros x Hx; apply M'_out; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rsz' : rdn segs M' (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n)))).
    { rewrite <- Rsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M'_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps segs (mkst r0 (at_ rb 0x4bed0) M rom) (mkst r1 (at_ rb 0x4bf04) M' rom)
               /\ getr r1 10 = Z_to_bv 64 sbeg /\ regs_agree (fun x => In x [10]) r0 r1).
    { wd_eexists. split.
      - av K66e04 D_4bec8 (Z_to_bv 64 (id * 2 ^ 32)) ltac:(vz).            (* [comment removed for export] *)
        av K66e08 D_4becc (Z_to_bv 64 id) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal; apply Z.div_mul; lia).  (* [comment removed for export] *)
        an K66e0c D_4bed0.                                                   (* [comment removed for export] *)
        rewrite (v_or_shl (Z_to_bv 64 id) tid 32) by (wd_ulia).
        replace (tid * 2 ^ 32 + U (Z_to_bv 64 id))%Z with (tid * 2 ^ 32 + id)%Z by (unorm; reflexivity).
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ m (rz n - 8));
            [exact K66e10 | reflexivity | exact D_4bed4 | gres; rwH; imm_norm; rewrite ?at_addi; f_equal; lia | gres; rwH; reflexivity
            | eapply (store_ok_sub segs _ (at_ m (rz n - 16)) _ 16); [rewrite at_u; lia | exact SOK | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        change (wbytes M _ _) with M'.
        ab_tk K66e14 D_4bed8 ltac:(condz).                                  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 sbeg)) (v := Z_to_bv 64 sbeg);
            [exact K66e34 | reflexivity | exact D_4bef8 | gres; rwH; imm_norm; exact Rsb' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        wd_refl.
      - post. ra_solve. }
    destruct W1 as (r1 & RUN1 & A10 & AG1).
    assert (B18 : getr r1 18 = m) by (rewrite (AG1 18) by notin_list; exact R18).
    (* [comment removed for export] *)
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4bf04) M' rom) (mkst r2 (at_ rb 0x4bf3c) M' rom)
               /\ regs_agree (fun x => In x [11]) r1 r2).
    { destruct Dsb as [Dlo|Dhi].
      - wd_eexists. split; [ab_tk K66e38 D_4befc ltac:(condz); wd_refl | intros i Hi; reflexivity].   (* [comment removed for export] *)
      - wd_eexists. split.
        + ab_ft K66e38 D_4befc ltac:(condz).                                (* [comment removed for export] *)
          an K66e3c D_4bf00.                                                 (* [comment removed for export] *)
          an K66e40 D_4bf04.                                                 (* [comment removed for export] *)
          av K66e44 D_4bf08 (Z_to_bv 64 (sbeg + 2 ^ 37)) ltac:(vz).         (* [comment removed for export] *)
          ab_tk K66e48 D_4bf0c ltac:(condz).                                (* [comment removed for export] *)
          wd_refl.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & AG2).
    assert (K2 : forall i : reg, i <> 10 -> i <> 11 -> getr r2 i = getr r0 i).
    { intros i N10 N11. rewrite (AG2 i) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros [X|[]]; apply N11; symmetry; exact X).
      apply AG1. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros [X|[]]. apply N10. symmetry. exact X. }
    assert (C18 : getr r2 18 = m) by (rewrite K2 by (intros E; discriminate E); exact R18).
    assert (C20 : getr r2 20 = at_ m (rz n)) by (rewrite K2 by (intros E; discriminate E); exact R20).
    assert (C22 : getr r2 22 = Z_to_bv 64 0x103f18) by (rewrite K2 by (intros E; discriminate E); exact R22).
    assert (C25 : getr r2 25 = at_ m (rz n + n)) by (rewrite K2 by (intros E; discriminate E); exact R25).
    assert (W3 : exists r3, msteps segs (mkst r2 (at_ rb 0x4bf3c) M' rom) (mkst r3 (at_ rb 0x6f610) M' rom)
               /\ getr r3 1 = at_ rb 0x4bfa8 /\ getr r3 10 = m /\ getr r3 11 = Z_to_bv 64 2048 /\ getr r3 12 = Z_to_bv 64 250
               /\ getr r3 8 = Z_to_bv 64 sb_asz /\ getr r3 22 = Z_to_bv 64 sb_re
               /\ regs_agree (fun x => In x [1; 8; 10; 11; 12; 22; 25]) r2 r3).
    { wd_eexists. split.
      - chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
            [exact K66e70 | reflexivity | exact D_4bf34 | gres; rwH; imm_norm; exact Rpg' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        an K66e74 D_4bf38.                                                   (* [comment removed for export] *)
        an K66e78 D_4bf3c.                                                   (* [comment removed for export] *)
        match goal with |- context [v_and ?a ?b] =>
          replace (v_and a b) with (Z_to_bv 64 0)
            by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 4095%Z with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; exact Gm1) end.
        ab_ft K66e7c D_4bf40 ltac:(condz).                                  (* [comment removed for export] *)
        an K66e80 D_4bf44.                                                   (* [comment removed for export] *)
        ab_ft K66e84 D_4bf48 ltac:(condz).                                  (* [comment removed for export] *)
        av K66e88 D_4bf4c (at_ m (-4096)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 (sec_needed n))) (v := Z_to_bv 64 (sec_needed n));
            [exact K66e8c | reflexivity | exact D_4bf50 | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Rsz' | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                                 (* [comment removed for export] *)
        av K66e90 D_4bf54 (Z_to_bv 64 (sec_needed n + 4095)) ltac:(vz).     (* [comment removed for export] *)
        an K66e94 D_4bf58.                                                   (* [comment removed for export] *)
        an K66e98 D_4bf5c.                                                   (* [comment removed for export] *)
        match goal with |- context [v_and ?a ?b] =>
          replace (v_and a b) with (Z_to_bv 64 sb_asz)
            by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and, v_sub, sbasz in G in change_no_check G' end); unorm; f_equal; change 18446744073709547520%Z with ((- 2 ^ 12) mod 2 ^ 64)%Z; rewrite land_wrap_neg_pow2 by lia; reflexivity) end.
        an K66e9c D_4bf60.                                                   (* [comment removed for export] *)
        av K66ec4 D_4bf88 (at_ m (rz n + n + 7)) ltac:(rewrite ?at_addi; reflexivity).   (* [comment removed for export] *)
        av K66ec8 D_4bf8c (Z_to_bv 64 sb_re) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi, sbre in G in change_no_check G' end); rewrite at_u by lia; unorm; f_equal; change (bv_wrap 64 (-8)) with ((- 2 ^ 3) mod 2 ^ 64)%Z; rewrite land_wrap_neg_pow2 by lia; change (2 ^ 3)%Z with 8%Z; f_equal; [lia | f_equal; lia]).                  (* [comment removed for export] *)
        av K66ecc D_4bf90 (Z_to_bv 64 2048) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); rewrite at_u by lia; unorm; f_equal; lia).   (* [comment removed for export] *)
        an K66ed0 D_4bf94.                                                   (* [comment removed for export] *)
        an K66ed4 D_4bf98.                                                   (* [comment removed for export] *)
        an K66ed8 D_4bf9c.                                                   (* [comment removed for export] *)
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
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfa8) M rom) (mkst r (at_ rb 0x6f610) M rom)
      /\ getr r 1 = at_ rb 0x4bfbc /\ getr r 10 = Z_to_bv 64 sb_re /\ getr r 11 = Z_to_bv 64 (U m + sb_asz - sb_re) /\ getr r 12 = Z_to_bv 64 250
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Gm Hn K66eec K66ee8 K66ee4 K66ee0 K66edc HAL2.
    intros M r0 R18 R22 R8.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9).
    pose proof (sbre_bnd (U m) n) as [Hre _]. pose proof (sbasz_bnd n) as [Hasz _].
    wd_eexists. split.
    - an K66edc D_4bfa0.                                                   (* [comment removed for export] *)
      av K66ee0 D_4bfa4 (Z_to_bv 64 (U m + sb_asz - sb_re)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, v_sub in G in change_no_check G' end); apply bv_eq; rewrite !Z_to_bv_unsigned; (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end); change (bv_modulus 64) with (2 ^ 64)%Z;
          rewrite (Z.mod_small sb_re), (Z.mod_small sb_asz) by lia; rewrite Zplus_mod_idemp_l; f_equal; lia).   (* [comment removed for export] *)
      an K66ee4 D_4bfa8.                                                   (* [comment removed for export] *)
      an K66ee8 D_4bfac.                                                   (* [comment removed for export] *)
      an K66eec D_4bfb0.                                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma amD1c : forall (M : word -> option byte) r0,
    getr r0 9 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfbc) M rom) (mkst r (at_ rb 0x4bfc8) M rom)
      /\ getr r 22 = Z_to_bv 64 (n - n mod 8)
      /\ regs_agree (fun x => In x [10; 22]) r0 r.
  Proof using Hn m K66ef8 K66ef4 K66ef0 HAL2.
    intros M r0 R9.
    wd_eexists. split.
    - an K66ef0 D_4bfb4.                                                   (* [comment removed for export] *)
      an K66ef4 D_4bfb8.                                                   (* [comment removed for export] *)
      an K66ef8 D_4bfbc.                                                   (* [comment removed for export] *)
      match goal with |- context [v_and (Z_to_bv 64 n) ?msk] =>
        replace (v_and (Z_to_bv 64 n) msk) with (Z_to_bv 64 (n - n mod 8))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; imm_norm; apply land_48m8s; lia) end.
      wd_refl.
    - post. ra_solve.
  Qed.

  Lemma amD2s : forall (M : word -> option byte) r0,
    (8 <= n)%Z -> getr r0 22 = Z_to_bv 64 (n - n mod 8) -> getr r0 20 = at_ m (rz n) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfc8) M rom) (mkst r (at_ rb 0x6f610) M rom)
      /\ getr r 1 = at_ rb 0x4bfdc /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 (n - n mod 8) /\ getr r 12 = Z_to_bv 64 0
      /\ regs_agree (fun x => In x [1; 10; 11; 12]) r0 r.
  Proof using Gm Hn K66f0c K66f08 K66f04 K66f00 K66efc HAL2.
    intros M r0 Hn8 R22 R20. pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    wd_eexists. split.
    - ab_ft K66efc D_4bfc0 ltac:(condz).                  (* [comment removed for export] *)
      an K66f00 D_4bfc4. an K66f04 D_4bfc8. an K66f08 D_4bfcc.   (* [comment removed for export] *)
      an K66f0c D_4bfd0.                                   (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Variable gSB : Z.                     (* [comment removed for export] *)
  Variables (psb : word) (SB : Z).
  Hypothesis GgSB : (AIMGLO <= gSB /\ gSB + 8 <= AIMGHI)%Z.
  Hypothesis Gpsb : (AIMGLO <= U psb /\ U psb + 8 <= AIMGHI)%Z.
  Hypothesis GSB : (0 < SB <= 0x7fff8000)%Z /\ (SB + U m / 8 + 1 <= 2 ^ 62)%Z.
  Variables (g_cpm gMB gME gHE gFL : Z) (pmb pme phe pfl : word) (midend : word) (pp : byte).
  Hypothesis CPM : code_ato segs rb 0x6f5fc cpm_words.
  Hypothesis GCPM : gloadb segs rb 0x6f5fc 10 g_cpm.
  Hypothesis GLSB2 : gload segs rb 0x4bfe8 10 gSB.
  Hypothesis GLMB : gload segs rb 0x4c00c 12 gMB.
  Hypothesis GLME : gload segs rb 0x4c014 13 gME.
  Hypothesis GLHE : gload segs rb 0x4c030 13 gHE.
  Hypothesis GLFL : gload segs rb 0x4c04c 11 gFL.
  (* [comment removed for export] *)
  Hypothesis Gcells : Forall (fun c => AIMGLO <= c /\ c + 8 <= AIMGHI)%Z [g_cpm; gMB; gME; gHE; gFL] /\ (AIMGLO <= U pmb /\ U pmb + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pme /\ U pme + 8 <= AIMGHI)%Z
                      /\ (AIMGLO <= U phe /\ U phe + 8 <= AIMGHI)%Z /\ (AIMGLO <= U pfl /\ U pfl + 128 <= AIMGHI)%Z.

  Lemma amE1zs : forall (M : word -> option byte) r0,
    (n mod 8 = 0)%Z -> getr r0 9 = Z_to_bv 64 n -> getr r0 22 = Z_to_bv 64 (n - n mod 8) ->
    msteps segs (mkst r0 (at_ rb 0x4bfdc) M rom) (mkst r0 (at_ rb 0x4c070) M rom).
  Proof using Hn m K66f10 HAL2.
    intros M r0 Hm R9 R22. ab_tk K66f10 D_4bfd4 ltac:(rewrite Hm, Z.sub_0_r; condz). wd_refl.
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
    exists r, msteps segs (mkst r0 (at_ rb 0x4bfdc) M rom) (mkst r (at_ rb 0x4c070) (amE1_mem m n SB M) rom)
      /\ regs_agree (fun x => In x [22; 1; 10; 11; 12; 13; 14; 15; 16; 17]) r0 r.
  Proof using Gcells GLFL GLHE GLME GLMB GLSB2 GCPM CPM GSB Gm Hn K66fa0 K66f9c K66f98 K66f94 K66f90 K66f8c K66f88 K66f7c K66f78 K66f74 K66f70 K66f6c K66f5c K66f58 K66f54 K66f50 K66f3c K66f38 K66f34 K66f30 K66f2c K66f28 K66f24 K66f18 K66f14 K66f10 RB HAL2.
    intros M r0 Grng Hm R9 R22 R20 Rcpm RgSB RSB RgMB RMB RgME RME RgHE RHE RgFL Rpp SOK.
    pose proof (u64_range m) as Hmr. destruct Gm as (Gm1 & Gm2 & Gm3). pose proof (rz_log_range n) as HRL. destruct GSB as [GS1 GS2].
    destruct Gcells as (GC & Gpmb & Gpme & Gphe & Gpfl).
    pose proof (u64_range pmb). pose proof (u64_range pme). pose proof (u64_range phe). pose proof (u64_range pfl). pose proof (u64_range psb).
    assert (Erz : rz n = 2048%Z) by (apply rz_sec; lia).
    assert (Hrz2 : (16 <= rz n <= 2048)%Z) by lia.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm8. pose proof (Z.mod_le n 8 ltac:(lia) ltac:(lia)) as Hm9.
    set (e := (U m + rz n + (n - n mod 8))%Z).
    destruct (cpm_run segs rb g_cpm CPM GCPM M rom (regupd r0 1 (at_ rb 0x4bfe4)) (at_ rb 0x4bfe4) Rcpm) as (r1 & RUN1 & A10 & AG1).
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
        ab_ft K66f10 D_4bfd4 ltac:(condz).                  (* [comment removed for export] *)
        an K66f14 D_4bfd8.                                   (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        ab_ft K66f18 D_4bfdc ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
            [exact K66f24 | reflexivity | exact D_4bfe8 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K66f28 D_4bfec (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av K66f2c D_4bff0 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
        an K66f30 D_4bff4.                                   (* [comment removed for export] *)
        replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
          by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        an K66f34 D_4bff8.                                   (* [comment removed for export] *)
        an K66f38 D_4bffc.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
        ab_tk K66f3c D_4c000 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 1); [exact K66f88 | reflexivity | exact D_4c04c
            | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K66f8c D_4c050 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av K66f90 D_4c054 (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
        an K66f94 D_4c058.                                   (* [comment removed for export] *)
        an K66f98 D_4c05c.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        av K66f9c D_4c060 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
            [exact K66fa0 | reflexivity | exact D_4c064 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
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
        ab_ft K66f10 D_4bfd4 ltac:(condz).                  (* [comment removed for export] *)
        an K66f14 D_4bfd8.                                   (* [comment removed for export] *)
        eapply msteps_trans; [exact RUN1|].
        ab_ft K66f18 D_4bfdc ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLSB2 _ M rom psb RgSB)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 SB)) (v := Z_to_bv 64 SB);
            [exact K66f24 | reflexivity | exact D_4bfe8 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RSB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K66f28 D_4bfec (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); cbv delta [v_add] beta; rewrite at_u by lia; unorm; f_equal; lia).  (* [comment removed for export] *)
        av K66f2c D_4bff0 (Z_to_bv 64 (SB - 1)) ltac:(vz).  (* [comment removed for export] *)
        an K66f30 D_4bff4.                                   (* [comment removed for export] *)
        replace (v_sltu (Z_to_bv 64 SB) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 0)
          by ((lazymatch goal with |- ?G => let G' := eval unfold v_sltu, c_ltu, bv_ltu in G in change_no_check G' end); unorm; replace (SB <? SB - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        an K66f34 D_4bff8.                                   (* [comment removed for export] *)
        an K66f38 D_4bffc.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (SB - 1))) with (Z_to_bv 64 (SB - 1))
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; apply Z.mod_small; lia).
        ab_ft K66f3c D_4c000 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLMB _ M rom pmb RgMB)|]. zlit_at.   (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLME _ M rom pme RgME)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
            [exact K66f50 | reflexivity | exact D_4c014 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RMB | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 midend) (v := midend);
            [exact K66f54 | reflexivity | exact D_4c018 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RME | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        an K66f58 D_4c01c.                                   (* [comment removed for export] *)
        ab_tk K66f5c D_4c020 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLHE _ M rom phe RgHE)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_ld with (bs := LE8 (Z_to_bv 64 0x7fffffffffff)) (v := Z_to_bv 64 0x7fffffffffff);
            [exact K66f6c | reflexivity | exact D_4c030 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact RHE | apply bytes_le_to_Z_8]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        an K66f70 D_4c034.                                   (* [comment removed for export] *)
        av K66f74 D_4c038 (Z_to_bv 64 (0xfffffffffff + SB)) ltac:(vz).   (* [comment removed for export] *)
        ab_ft K66f78 D_4c03c ltac:(condz).                  (* [comment removed for export] *)
        ab_ft K66f7c D_4c040 ltac:(condz).                  (* [comment removed for export] *)
        eapply msteps_trans; [apply (GLFL _ M rom pfl RgFL)|]. zlit_at.   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lbu with (b := Z_to_bv 8 1); [exact K66f88 | reflexivity | exact D_4c04c
            | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rpp]
          | step_simpl]; vn.                                 (* [comment removed for export] *)
        av K66f8c D_4c050 (Z_to_bv 64 (e / 8)) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).  (* [comment removed for export] *)
        av K66f90 D_4c054 (Z_to_bv 64 (SB + e / 8)) ltac:(vz).   (* [comment removed for export] *)
        an K66f94 D_4c058.                                   (* [comment removed for export] *)
        an K66f98 D_4c05c.                                   (* [comment removed for export] *)
        replace (v_and (Z_to_bv 64 n) (Z_to_bv 64 18446744073709551615)) with (Z_to_bv 64 n)
          by (symmetry; (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
        av K66f9c D_4c060 (Z_to_bv 64 (n mod 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); unorm; f_equal; change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).  (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sb_at with (a := Z_to_bv 64 (SB + e / 8)) (b := Z_to_bv 8 (n mod 8));
            [exact K66fa0 | reflexivity | exact D_4c064 | gres; rwH; imm_norm; rewrite ?v_addi_0; reflexivity | gres; rwH; reflexivity | unorm; reflexivity | exact SOK]
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
    exists r w0 w8 w16 w104, msteps segs (mkst r0 (at_ rb 0x4c074) M rom) (mkst r (at_ rb 0x4c0b4) (amE2s_mem M w0 w8 w16 w104) rom)
      /\ regs_agree (fun x => In x [11; 12; 13; 14]) r0 r.
  Proof using Gthr Gm Hn m K66fe4 K66fe0 K66fdc K66fd8 K66fd4 K66fd0 K66fcc K66fc8 K66fc4 K66fc0 K66fbc K66fb8 K66fb4 K66fb0 K66fac K66fa8 HAL2.
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
          [exact K66fa8 | reflexivity | exact D_4c06c | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv16 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v0) (v := v0);
          [exact K66fac | reflexivity | exact D_4c070 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; zlit_at; exact Rv0 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v8) (v := v8);
          [exact K66fb0 | reflexivity | exact D_4c074 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rv8 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K66fb4 D_4c078 (Z_to_bv 64 (sec_needed n - n)) ltac:(vz).   (* [comment removed for export] *)
      an K66fb8 D_4c07c. setlast.                          (* [comment removed for export] *)
      an K66fbc D_4c080. an K66fc0 D_4c084.               (* [comment removed for export] *)
      an K66fc4 D_4c088. setlast.                          (* [comment removed for export] *)
      an K66fc8 D_4c08c. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2800);
          [exact K66fcc | reflexivity | exact D_4c090 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2808);
          [exact K66fd0 | reflexivity | exact D_4c094 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2816);
          [exact K66fd4 | reflexivity | exact D_4c098 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      ab_ft K66fd8 D_4c09c ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 v104) (v := v104);
          [exact K66fdc | reflexivity | exact D_4c0a0
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; rewrite <- Rv104; apply rdn_ext;
            [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
            | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx;
              rewrite !wbytes_outside; [reflexivity | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      an K66fe0 D_4c0a4. setlast.                          (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sd_at with (a := at_ thr 2904);
          [exact K66fe4 | reflexivity | exact D_4c0a8 | gres; rwH; imm_norm; rewrite ?at_addi; reflexivity | gres; rwH; reflexivity | sok112 SOK]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst _ _ (wbytes (wbytes (wbytes (wbytes M _ (word_to_le_bytes 8 ?a)) _ (word_to_le_bytes 8 ?b)) _ (word_to_le_bytes 8 ?c)) _ (word_to_le_bytes 8 ?d)) _) _ =>
        change (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) with (amE2s_mem M a b c d) end.
      wd_refl.
    - ra_chain.
  Qed.

  Variables (gFL3 gRMS : Z) (prms msetw : word) (fillw : Z).
  Hypothesis GLFL3 : gload segs rb 0x4c1d0 10 gFL3.
  Hypothesis GLRMS : gload segs rb 0x4c1ec 11 gRMS.
  Hypothesis Gfillw : (0 <= fillw < 2 ^ 31)%Z.
  Hypothesis MSOK : ret_ok msetw.

  Lemma amE2sc : forall (M : word -> option byte) r0,
    getr r0 9 = Z_to_bv 64 n -> getr r0 20 = at_ m (rz n) -> getr r0 2 = sp ->
    rdn segs M (at_ sp 8) 8 = Some (LE8 (Z_to_bv 64 1)) ->
    rdn segs M (Z_to_bv 64 gFL3) 8 = Some (LE8 pfl) -> rdn segs M (at_ pfl 44) 4 = Some (LE4 4096) -> rdn segs M (at_ pfl 52) 4 = Some (LE4 fillw) ->
    rdn segs M (Z_to_bv 64 gRMS) 8 = Some (LE8 prms) -> rdn segs M prms 8 = Some (LE8 msetw) ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4c0b4) M rom) (mkst r msetw M rom)
      /\ getr r 1 = at_ rb 0x4c204 /\ getr r 10 = at_ m (rz n) /\ getr r 11 = Z_to_bv 64 fillw /\ getr r 12 = Z_to_bv 64 4096
      /\ regs_agree (fun x => In x [1; 10; 11; 12; 13]) r0 r.
  Proof using MSOK Gfillw GLRMS GLFL3 Gsp Gcells phe pme pmb gFL gHE gME gMB g_cpm Gm Hn K67134 K67130 K6712c K67128 K6711c K67118 K67114 K67110 K6710c K66fec K66fe8 HAL2.
    intros M r0 R9 R20 R2 Rfill RgFL Rmmf Rfb RgRMS Rrms.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range pfl). destruct Gsp as [Gs1 Gs2]. destruct Gcells as (_ & _ & _ & _ & Gpfl).
    pose proof sec_arith as (Erz & Hsnb & Hm8 & Hm9). destruct Gm as (Gm1 & Gm2 & Gm3).
    wd_eexists. split.
    - chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 (Z_to_bv 64 1)) (v := Z_to_bv 64 1);
          [exact K66fe8 | reflexivity | exact D_4c0ac | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rfill | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                (* [comment removed for export] *)
      ab_tk K66fec D_4c0b0 ltac:(condz).                                 (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLFL3 _ _ rom pfl); exact RgFL|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 4096)) (v := Z_to_bv 64 4096);
          [exact K6710c | reflexivity | exact D_4c1d0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rmmf | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small 4096) by lia; vn.              (* [comment removed for export] *)
      ab_ft K67110 D_4c1d4 ltac:(condz).                                 (* [comment removed for export] *)
      an K67114 D_4c1d8.                                                  (* [comment removed for export] *)
      ab_ft K67118 D_4c1dc ltac:(condz).                                 (* [comment removed for export] *)
      an K6711c D_4c1e0.                                                  (* [comment removed for export] *)
      eapply msteps_trans; [apply (GLRMS _ _ rom prms); exact RgRMS|]. zlit_at.   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 msetw) (v := msetw);
          [exact K67128 | reflexivity | exact D_4c1ec | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rrms | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 fillw)) (v := Z_to_bv 64 fillw);
          [exact K6712c | reflexivity | exact D_4c1f0 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; exact Rfb | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small fillw) by lia; vn.                (* [comment removed for export] *)
      an K67130 D_4c1f4.                                                    (* [comment removed for export] *)
      aret K67134 D_4c1f8 msetw.                                            (* [comment removed for export] *)
      rewrite ?at_addi; zlit_at. wd_refl.
    - post. all: try (rewrite ?at_add_0_r; reflexivity). ra_solve.
  Qed.

End AMDS.
End FPGen1.
