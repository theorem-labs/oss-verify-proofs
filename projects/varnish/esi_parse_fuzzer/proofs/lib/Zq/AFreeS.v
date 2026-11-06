(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.

Module ARt4_gbb.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma nearest_range : forall hs m, 0 <= m -> 0 <= nearest hs m <= Z.max 0 m /\ (nearest hs m = 0 \/ nearest hs m <= m).
Proof.
  intros hs m Hm. unfold nearest.
  enough (G : forall z, 0 <= z -> (z = 0 \/ z <= m) -> let r := fold_left (fun acc h => nearest_step m acc (bv_unsigned h)) hs z in
                       0 <= r <= Z.max 0 m /\ (r = 0 \/ r <= m)) by (apply G; lia).
  induction hs as [|h hs IH]; intros z Hz Hzm; cbn.
  - lia.
  - apply IH; unfold nearest_step; pose proof (bv_unsigned_in_range _ h);
      destruct (Z.ltb_spec m (bv_unsigned h)); try lia; destruct (Z.ltb_spec (m - bv_unsigned h) (m - z)); lia.
Qed.


(* [comment removed for export] *)
Definition nfold (mh : Z) (acc : Z) (l : list word) : Z := fold_left (fun a h => nearest_step mh a (bv_unsigned h)) l acc.

Lemma nfold_range : forall mh l acc, 0 <= mh -> 0 <= acc -> (acc = 0 \/ acc <= mh) ->
  0 <= nfold mh acc l /\ (nfold mh acc l = 0 \/ nfold mh acc l <= mh).
Proof.
  intros mh l. induction l as [|h l IH]; intros acc Hm Ha Ham; cbn; [lia|].
  apply IH; [exact Hm| |]; unfold nearest_step; pose proof (bv_unsigned_in_range _ h);
    destruct (Z.ltb_spec mh (bv_unsigned h)); try lia; destruct (Z.ltb_spec (mh - bv_unsigned h) (mh - acc)); lia.
Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma gbb_loop : forall (k : nat) (i : Z) (acc : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mh pa : Z) (hs : list word) (Q : machine_state -> Prop),
  let n := Z.of_nat (length hs) in
  (k = length hs - Z.to_nat i)%nat -> 0 <= i < n ->
  mem_inv rsegs m -> u64arr rsegs m pa hs -> aobj pa (8 * n) -> pa + 8 * n <= alloc_ceiling -> pa mod 8 = 0 -> n < 2^20 ->
  0 <= mh < 2^64 -> 0 <= acc -> (acc = 0 \/ acc <= mh) ->
  (forall (a5' a6' a7' t0' : word),
      evt rsegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 mh) (Z_to_bv 64 (pa + 8 * n))
                          (Z_to_bv 64 (nfold mh acc (skipn (Z.to_nat i) hs))) (Z_to_bv 64 (pa + 8 * n)) a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x396d0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 mh) (Z_to_bv 64 (pa + 8 * i)) (Z_to_bv 64 acc) (Z_to_bv 64 (pa + 8 * n))
                      a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x396a4) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i acc ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mh pa hs Q;
    cbv zeta; intros HK HI MI ARR PLO PHI PAL NH MHR ACC0 ACCM K; [lia|].
  pose proof alloc_ceiling_val as CV. unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  destruct (nth_error hs (Z.to_nat i)) as [h|] eqn:NTH; [| apply nth_error_None in NTH; lia].
  pose proof (u64arr_read rsegs m pa hs i h (Z_to_bv 64 (pa + 8 * i)) ARR NTH ltac:(lia) ltac:(unfold wa; reflexivity)) as RD.
  pose proof (bv_unsigned_in_range _ h) as HR.
  amz. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (STEP : forall (a5' a6' a7' t0' : word),
    evt rsegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 mh) (Z_to_bv 64 (pa + 8 * i))
                        (Z_to_bv 64 (nearest_step mh acc (bv_unsigned h))) (Z_to_bv 64 (pa + 8 * Z.of_nat (length hs)))
                        a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3969c) fc None m (seg_rom rsegs))).
  { intros a5' a6' a7' t0'.
    amz. (* [comment removed for export] *)
    amz. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by lia.
    - (* [comment removed for export] *)
      replace (pa + 8 * i + 8) with (pa + 8 * Z.of_nat (length hs)) by lia.
      replace (nearest_step mh acc (bv_unsigned h)) with (nfold mh acc (skipn (Z.to_nat i) hs)).
      2:{ replace (skipn (Z.to_nat i) hs) with [h]; [reflexivity|].
          rewrite <- (firstn_skipn (Z.to_nat i) hs) in NTH. rewrite nth_error_app2 in NTH by (rewrite firstn_length; lia).
          rewrite firstn_length, Nat.min_l, Nat.sub_diag in NTH by lia.
          destruct (skipn (Z.to_nat i) hs) as [|x l] eqn:E; [discriminate|]. injection NTH; intros ->.
          assert (L : length (skipn (Z.to_nat i) hs) = 1%nat) by (rewrite skipn_length; lia).
          rewrite E in L. destruct l; [reflexivity | cbn in L; lia]. }
      apply K.
    - replace (pa + 8 * i + 8) with (pa + 8 * (i + 1)) by lia.
      pose proof (nfold_range mh [h] acc ltac:(lia) ACC0 ACCM) as NR. cbn [nfold fold_left] in NR.
      eapply (IH (i + 1)); try eassumption; try lia.
      intros. replace (skipn (Z.to_nat i) hs) with (h :: skipn (Z.to_nat (i + 1)) hs) in K; [apply K|].
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      clear -NTH; try pose proof alloc_ceiling_val. revert hs NTH. generalize (Z.to_nat i) as j. intros j. induction j as [|j IHj]; intros hs NTH.
      + destruct hs; [discriminate|]. injection NTH; intros ->. reflexivity.
      + destruct hs; [discriminate|]. cbn in NTH. cbn [skipn]. apply IHj. exact NTH. }
  amz. if_cases K1; zify_cond K1; amz; first [if_cases K2 | amz; if_cases K2]; zify_cond K2; unfold nearest_step in STEP.
  all: first
    [ (* [comment removed for export] *)
      rewrite (proj2 (Z.ltb_lt mh (bv_unsigned h))) in STEP by lia; first [apply STEP | amz; amz; apply STEP]
    | rewrite (proj2 (Z.ltb_ge mh (bv_unsigned h))) in STEP by lia; rewrite ?Z.mod_small in K1 by lia;
      first [ rewrite (proj2 (Z.ltb_lt _ _)) in STEP by lia; amz; amz; rewrite ?Z_to_bv_bv_unsigned in STEP; apply STEP
            | rewrite (proj2 (Z.ltb_ge _ _)) in STEP by lia; first [apply STEP | amz; amz; apply STEP | amz; amz; amz; apply STEP] ] ].
Qed.

Theorem gbb_ok : gbb_stmt.
Proof.
  unfold gbb_stmt. intros until hs. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 MR PLO PHI PAL NR U1R U2R NLO NAL MB1 MB2 MH MSH MB0 DJP RL RN LCK ARR HC RA.
  pose proof alloc_ceiling_val as CV. unfold gbb_entry, LMA_L, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  lit_addrs.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0xb1800, 0xb1804)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  remember (Z.of_nat (length hs)) as n eqn:Hn.
  remember (nearest hs mh) as nr eqn:Hnr.
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 32%nat ST.
  do 5 amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  apply (hdr4_join _ _ 0 u1 u2) in LCK; [| lia | lia | lia | cbn; tauto].
  replace (0 + 256 * u1 + 65536 * u2) with (256 * (u1 + 256 * u2)) in LCK by lia.
  amz. rewrite sx32_small by lia. (* [comment removed for export] *)
  amz. amz. amz. amz. rewrite (cas_set_low0 1 (u1 + 256 * u2)) by lia.
  scstep; zsimp.
  amz. if_false. (* [comment removed for export] *)
  amz. rewrite (land255_low0 (u1 + 256 * u2)) by lia. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  replace (1 + 256 * (u1 + 256 * u2)) with (1 + 256 * u1 + 65536 * u2) in LCK by lia.
  apply (hdr4_split _ _ 1 u1 u2) in LCK; [| lia | lia | lia | cbn; tauto].
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 n 3) by lia. replace (pa + n * 2 ^ 3) with (pa + 8 * n) by lia.
  replace (Z_to_bv 64 pa) with (Z_to_bv 64 (pa + 8 * 0)) by (f_equal; lia).
  subst n. eapply (gbb_loop (length hs) 0 0); try eassumption; try lia.
  intros a5' a6' a7' t0'. rewrite skipn_O. change (nfold mh 0 hs) with (nearest hs mh). rewrite <- Hnr.
  pose proof (nearest_range hs mh ltac:(lia)) as NRR. rewrite <- Hnr in NRR.
  (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  replace (Z.land 4095 nr) with 0 in * by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096; rewrite NAL; reflexivity).
  amz. if_false. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 5 amz. release_frame FR ST (bv_unsigned sp).
  amz. (* [comment removed for export] *)
  replace (4096 + nr) with (nr + 4096) by lia.
  (subst hotQ; finish).
Qed.

End CEIL.

Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- u64arr _ _ _ _ => eassumption
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem cbrec_sec_ok : cbrec_sec_stmt.
Proof.
  unfold cbrec_sec_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 SB0 SBH MHR PLO PHI PAL NR U1R U2R NLO NAL MB1 MB2 MH MSH MB0 DJP PR RSB RL RN LCK ARR HC K.
  pose proof alloc_ceiling_val as CV. unfold cbrec_entry, cbrec_tail, LMA_L, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1.
  lit_addrs.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xb1800, 0xb1804)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  remember (nearest hs mh) as nr eqn:Hnr.
  carve_frame 48%nat ST.
  do 7 amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (TOGBB : forall (a1' : word),
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 cb) (Z_to_bv 64 mh)
                        (Z_to_bv 64 sb) a1' a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0xb1558) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x39420) fc None mm (seg_rom rsegs))) end.
  { intros a1'.
    amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    rewrite Hnr in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply gbb_ok with (mh := mh) (pa := pa) (mb := mb) (ms := ms) (u1 := u1) (u2 := u2) (lo := lo) (hs := hs)
                      | post_call_z rsegs mc ] end.
    all: rewrite ?unsigned_lit by lia.
    all: try first [exact MI | eassumption | lia | reflexivity | unfold LMA_L; reflexivity].
    idtac.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    assert (FIN : forall (a1x : word),
      evt rsegs Q (MS (mkR (Z_to_bv 64 0x3942c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x x0 x1 (Z_to_bv 64 cb) (Z_to_bv 64 mh)
                          (Z_to_bv 64 sb) a1x x3 x4 x5 x6 x7 x8 (Z_to_bv 64 (nearest hs mh + 4096)) (Z_to_bv 64 0xb1558) (Z_to_bv 64 137438953472)
                          s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12) F (Z_to_bv 64 0x39520) fc None x13 (seg_rom rsegs))).
    { intros a1x. subst nr. eapply K; try eassumption. }
    amz. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      amz. if_cases KB2; zify_cond KB2; [apply FIN | exfalso; rewrite ?Z.mod_small in KB, KB2 by lia; lia].
    - amz. (* [comment removed for export] *) apply FIN. }
  amz. if_cases KB; zify_cond KB.
  - apply TOGBB.
  - amz. amz. if_cases KB2; zify_cond KB2; [apply TOGBB | exfalso; rewrite ?Z.mod_small in KB2 by lia; lia].
Qed.

End CEIL2.
End ARt4_gbb.


Module ARt4tam.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_m2s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Lemma class_bits : forall sb c off, 0 <= sb -> 0 <= c <= 31 -> 0 <= off < 2^32 ->
  Z.shiftr (Z.shiftl (sb + c * 2^32 + off - sb) 27 mod 2^64) 59 = c.
Proof.
  intros sb c off Hs Hc Ho. replace (sb + c * 2^32 + off - sb) with (c * 2^32 + off) by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((c * 2^32 + off) * 2^27) with (off * 2^27 + c * 2^59) by lia.
  rewrite <- (Z.mod_unique_pos _ (2^64) 0 (off * 2^27 + c * 2^59)); [|lia|lia].
  symmetry. apply Z.div_unique_pos with (r := off * 2^27); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tails.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Theorem cbrec_tailp_ok : cbrec_tailp_stmt.
  Proof.
    unfold cbrec_tailp_stmt. intros until Q.
    intros MI ST LOLE CEIL USP UAL TPE HP CR OFR SB0 SBH MLO MHI NR STR B1R CLO CHI CAL CDJ RFR RFDR RSB RCB HDR TC RST DJT FR RA K.
    pose proof alloc_ceiling_val as CV. unfold cbrec_tail, lcdealloc_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    pose proof TC as TC'. (first [ dand13 TC' as T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 | destruct TC' as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13) ]). aobj_lin_all.
    unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(usp - 80, usp); (thr + 2840, thr + 2856)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold cbrec_frame in FR.
    amz. (* [comment removed for export] *)
    callz thread_stats_ok.
    1:{ exact MI. }
    1:{ rewrite unsigned_lit by lia. exact ST. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ lia. }
    1:{ exact TC. }
    1:{ reflexivity. }
    rename POST into ST. unfold off_th_stats.
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (size_hi n) with 0 by (unfold size_hi; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    replace (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity.
    rewrite (zx32_small n), (unsigned_lit 0), (unsigned_lit n), Z.shiftl_0_l, Z.lor_0_l by lia.
    idtac "join".
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. amz. amz. rewrite HP, class_bits by lia. rewrite <- HP. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    do 7 amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    release_frame FR ST usp.
    replace (n + rfd) with (rfd + n) in * by lia.
    eapply K; try eassumption.
  Qed.

  Theorem cbrec_tails_ok : cbrec_tails_stmt.
  Proof.
    unfold cbrec_tails_stmt. intros until Q.
    intros MI ST LOLE CEIL USP UAL TPE PNZ PR SB0 SBH MLO MHI NR STR B1R RFR RFDR RSB HDR TC RST DJT FR RA K.
    pose proof alloc_ceiling_val as CV. unfold cbrec_tail, ldealloc_entry, LMA_L, LMA_STAT, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    pose proof TC as TC'. (first [ dand13 TC' as T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 | destruct TC' as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13) ]). aobj_lin_all.
    unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(usp - 80, usp); (thr + 2840, thr + 2856)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold cbrec_frame in FR.
    amz.
    callz thread_stats_ok.
    1:{ exact MI. }
    1:{ rewrite unsigned_lit by lia. exact ST. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ lia. }
    1:{ exact TC. }
    1:{ reflexivity. }
    rename POST into ST. unfold off_th_stats.
    amz. amz.
    amz. amz.
    amz. amz.
    replace (size_hi n) with 0 by (unfold size_hi; rewrite Z.shiftr_div_pow2, Z.div_small by lia; reflexivity).
    replace (zx16 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity.
    rewrite (zx32_small n), (unsigned_lit 0), (unsigned_lit n), Z.shiftl_0_l, Z.lor_0_l by lia.
    amz. amz.
    amz. amz.
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    destruct PR as [PRlo | PRhi].
    - amz. br_taken. (* [comment removed for export] *)
      amz. amz. amz. (* [comment removed for export] *)
      do 7 amz. amz. (* [comment removed for export] *)
      release_frame FR ST usp.
      replace (n + rfd) with (rfd + n) in * by lia.
      eapply K; try eassumption.
    - amz. br_not_taken.
      amz. (* [comment removed for export] *)
      amz. br_taken. (* [comment removed for export] *)
      amz. amz. amz.
      do 7 amz. amz.
      release_frame FR ST usp.
      replace (n + rfd) with (rfd + n) in * by lia.
      eapply K; try eassumption.
  Qed.
End Tails.

(* [comment removed for export] *)
End ARt4tam.


Module ARt4eab.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_fpo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_pkh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4tam.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)

Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- u64arr _ _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => eassumption
  | |- poison_consts _ => eassumption
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Ltac sidec := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- thread_cells _ _ _ _ _ => first [eassumption | unfold thread_cells; rebundle]
  | |- poison_consts _ => first [eassumption | unfold poison_consts; rebundle]
  | |- stk _ _ _ ?hi => lazymatch goal with H : stk _ _ _ ?hi' |- _ => replace hi with hi' by lia; exact H end
  | |- _ => first [ eassumption | reflexivity | lia
                  | (rewrite unsigned_lit by lia; first [reflexivity | lia | assumption])
                  | plia | (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia) | (intros; lia) ]
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ld_prefix h u1 u2 pa hs idx n hl hla HAL LCK ARR NTH NTL Hhla :=
  do 5 amz;
  amz;
  amz; amz;
  replace (Z.land 4095 (h + 4096)) with 0 in * by
    (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096;
     rewrite <- Zplus_mod_idemp_r, Z_mod_same_full, Z.add_0_r, HAL; reflexivity);
  amz; if_false;
  amz; amz; amz; amz;
  apply (hdr4_join _ _ 0 u1 u2) in LCK; [| lia | lia | lia | cbn; tauto];
  replace (0 + 256 * u1 + 65536 * u2) with (256 * (u1 + 256 * u2)) in LCK by lia;
  amz; rewrite sx32_small by lia;
  amz; amz; amz; amz; rewrite (cas_set_low0 1 (u1 + 256 * u2)) by lia;
  scstep; zsimp;
  amz; if_false;
  amz; rewrite (land255_low0 (u1 + 256 * u2)) by lia;
  amz; replace (h + 4096 - 4096) with h by lia;
  amz; if_false;
  replace (1 + 256 * (u1 + 256 * u2)) with (1 + 256 * u1 + 65536 * u2) in LCK by lia;
  apply (hdr4_split _ _ 1 u1 u2) in LCK; [| lia | lia | lia | cbn; tauto];
  amz;
  amz;
  amz; amz;
  rewrite (Z.shiftl_mul_pow2 idx 3) by lia; replace (pa + idx * 2 ^ 3) with (pa + 8 * idx) by lia;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_read rsegs mm pa hs idx (Z_to_bv 64 h) (Z_to_bv 64 (pa + 8 * idx)) ARR NTH ltac:(lia) ltac:(unfold wa; reflexivity)) as RD1 end;
  amz;
  amz; if_false;
  amz;
  amz; br_not_taken;
  amz; rewrite (Z.shiftl_mul_pow2 n 3) by lia;
  amz;
  amz; replace (n * 2 ^ 3 + pa) with (pa + 8 * (n - 1) + 8) by lia;
  amz; amz;
  amz;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_read rsegs mm pa hs (n - 1) hl (Z_to_bv 64 (pa + 8 * (n - 1) + 8 + -8)) ARR NTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2 end;
  amz;
  amz; amz;
  amz; amz; amz; amz;
  amz; amz;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u64arr_store_ok rsegs mm pa hs idx (Z_to_bv 64 (pa + 8 * idx)) ARR ltac:(lia) ltac:(unfold wa; reflexivity)) as SOK end;
  amz;
  (change (Z_to_bv 64 (pa + 8 * idx)) with (wa (pa + 8 * idx)) || idtac);
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u64arr_write rsegs mm pa hs idx hl ARR ltac:(lia)) as ARR2 end;
  clear ARR; store_done; rename ARR2 into ARR;
  rewrite <- ?Hhla in *;
  rewrite <- (Z_to_bv_bv_unsigned hl); rewrite <- Hhla.

Ltac ld_suffix gA gM msz n GS RN :=
  amz; (* [comment removed for export] *)
  amz; (* [comment removed for export] *)
  amz; amz; amz; (* [comment removed for export] *)
  amz; (* [comment removed for export] *)
  amz; amz; (* [comment removed for export] *)
  amz; amz; (* [comment removed for export] *)
  amz; amz; amz; (* [comment removed for export] *)
  rewrite !amo_add_wz in GS; replace (gA + (0 - msz)) with (gA - msz) in GS by lia; replace (gM + (0 - msz)) with (gM - msz) in GS by lia;
  replace (n + -1) with (n - 1) in RN by lia.

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem ldealloc_pre_ok : ldealloc_pre_stmt.
Proof.
  unfold ldealloc_pre_stmt. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL A0 A1 A2 HLO HHI HAL MSZ PLO PHI PAL NR IDX NTH NTL HLLO HLHI HLAL DJH DJL U1R U2R SRT NFR CAR GAR GMR CSR
         RL RN RS LCK GS ARR HC HLC K.
  pose proof alloc_ceiling_val as CV. unfold ldealloc_entry, ldealloc_poison, LMA_L, LMA_STAT, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1 a2.
  lit_addrs.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  remember (Z.of_nat (length hs)) as n eqn:Hn.
  remember (bv_unsigned hl) as hla eqn:Hhla.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8); (0xb1800, 0xb1804);
                         (0xb1818, 0xb1828); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HLC as [EQ | [DJHL HLC2]].
  - (* [comment removed for export] *)
    rewrite EQ in *. carve_frame 32%nat ST. ld_prefix h u1 u2 pa hs idx n hl h HAL LCK ARR NTH NTL Hhla. ld_suffix gA gM msz n GS RN.
    eapply K; try eassumption.
    all: try (left; reflexivity).
    all: sidec.
  - carve_frame 32%nat ST. ld_prefix h u1 u2 pa hs idx n hl hla HAL LCK ARR NTH NTL Hhla. ld_suffix gA gM msz n GS RN.
    eapply K; try eassumption.
    all: try (right; eassumption).
    all: sidec.
Qed.

End CEIL2.
End ARt4eab.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_soh ARt_png ANodijx ANod9v0 APgGeo.

Module ARtSxaw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ANodijx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition madvise_ecall_pc : Z := 0x6a9b8.
Definition madvise_after_pc : Z := 0x6a9bc.
Definition ldealloc_resume : Z := 0x39a80.      (* [comment removed for export] *)
Definition SEALED_WORD : Z := 0xa8bb0.          (* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
Definition flush_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a size sealed lo : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz a -> a1 = wz size -> fl_in a size -> 0 <= size -> a + size < 2^47 -> a mod 8 = 0 -> size mod 8 = 0 ->
    sealed <> 0 -> 0 <= sealed < 2^64 ->
    poison_consts m -> ro_cells rsegs m SEALED_WORD [C8 (wz sealed)] ->
    a8_pbeg a < a8_pend a size ->
    (forall (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp) ->
        Q (MSsvc (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (a8_pbeg a)) (wz (a8_len a size)) (wz 4) (wz 4) a4' a5' a6' (wz 233)
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz flush_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition ldealloc_mid_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo h mb msz sealed : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 32) -> lo <= usp - 32 - 64 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    fl_in mb msz -> 0 <= msz -> mb + msz < 2^47 -> mb mod 8 = 0 -> msz mod 8 = 0 -> sealed <> 0 -> 0 <= sealed < 2^64 ->
    poison_consts m -> ro_cells rsegs m SEALED_WORD [C8 (wz sealed)] ->
    a8_pbeg mb < a8_pend mb msz ->
    (forall (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : word -> option byte),
        munch [(usp - 96, usp - 32)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp - 32) ->
        Q (MSsvc (mkR (wz ldealloc_resume) (wz (usp + -32)) gp tp t0' t1' t2' (wz h) (wz mb)
                      (wz (a8_pbeg mb)) (wz (a8_len mb msz)) (wz 4) (wz 4) a4' a5' a6' (wz 233)
                      (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -32)) gp tp t0 t1 t2 (wz h) (wz mb) a0 a1 a2 a3 a4 a5 a6 a7
                        (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ldealloc_after) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition ldealloc_post2_stack : Z := 32.   (* [comment removed for export] *)
Definition ldealloc_post2_stmt : Prop :=
  forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo h mb msz tsd ctx thr mu md : Z) (s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 32) -> lo <= usp - 32 - 32 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    tp = wz TP ->
    aobj h 32 -> h + 32 <= alloc_ceiling -> 0 <= msz < 2^64 -> 0 <= mb < 2^64 ->
    0 <= mu < 2^64 -> 0 <= md < 2^64 ->
    ro_cells rsegs m h [C8 (wz mb); C8 (wz msz)] ->
    thread_cells m tp tsd ctx thr ->
    rw_cells rsegs m (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
    (h + 32 <= thr \/ thr + 4096 <= h) ->
    rw_cells rsegs m (usp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    bv_unsigned ra0 mod 2 = 0 ->
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (thr + 2888) [C8 (wz (mu + 1)); C8 (wz (md + msz))] ->
        munch [(usp - 64, usp); (thr + 2888, thr + 2904)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0' t1' t2' s0v s1v (wz mb) (wz msz) (wz 0) a3' a4' a5' a6' a7'
                            s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz unmapordie_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz ldealloc_resume) (wz (usp + -32)) gp tp t0 t1 t2 (wz h) (wz mb) (wz 0) a1 a2 a3 a4 a5 a6 a7
                        (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz madvise_after_pc) fc None m (seg_rom rsegs)).

End CEIL.
End ARtSxaw.


Module ARt4fuu.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep ZBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSoqz ARtSnjd ARtSrgm ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_fpo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ANodijx APgGeo.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_pkh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARtSxaw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- u64arr _ _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => eassumption
  | |- poison_consts _ => eassumption
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

(* [comment removed for export] *)
Ltac rebundleU := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Ltac sidec := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- thread_cells _ _ _ _ _ => first [eassumption | unfold thread_cells; rebundle]
  | |- poison_consts _ => first [eassumption | unfold poison_consts; rebundle]
  | |- stk _ _ _ ?hi => lazymatch goal with H : stk _ _ _ ?hi' |- _ => replace hi with hi' by lia; exact H end
  | |- _ => first [ eassumption | reflexivity | lia
                  | (rewrite unsigned_lit by lia; first [reflexivity | lia | assumption])
                  | plia | (unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *; plia) | (intros; lia) ]
  end.

(* [comment removed for export] *)
Lemma m2s_sh : forall p, 0 <= p -> 2147450880 + Z.shiftr p 3 = sh p.
Proof. intros p Hp. unfold sh, kShadowOffset. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma sh_add8 : forall a s, a mod 8 = 0 -> s mod 8 = 0 -> sh (a + s) = sh a + s / 8.
Proof.
  intros a s Ha Hs. unfold sh.
  pose proof (Z_div_mod_eq_full a 8) as Qa. pose proof (Z_div_mod_eq_full s 8) as Qs. rewrite Ha in Qa. rewrite Hs in Qs.
  set (qa := a / 8) in *. set (qs := s / 8) in *. clearbody qa qs.
  replace (a + s) with ((qa + qs) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Section CEIL.
Context {Clg : Ceiling}.

Theorem flush_pre_ok : flush_pre_stmt.
Proof.
  unfold flush_pre_stmt. intros until Q. intros MI ST LOLE CEIL A0 A1 ALO S0' AS A8 S8 SNZ SR PC SEAL NE K.
  pose proof alloc_ceiling_val as CV. unfold flush_entry, madvise_ecall_pc, SEALED_WORD, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a0 a1.
  pose proof PC as PC'. (first [ dand13 PC' as P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 | destruct PC' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13) ]). aobj_lin_all.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  assert (A0' : 0 <= a) by plia.
  pose proof (pg_up_bounds (sh a)) as [PB1 PB2]. pose proof (pg_dn_bounds (sh a + size / 8)) as [PE1 PE2].
  unfold a8_len, a8_pbeg, a8_pend in *.
  assert (SHA : sh a = 2147450880 + Z.shiftr a 3) by (symmetry; apply m2s_sh; exact A0').
  assert (SHE : sh a + size / 8 = 2147450880 + Z.shiftr (a + size) 3) by (rewrite <- (sh_add8 a size A8 S8); symmetry; apply m2s_sh; lia).
  assert (SHR : 0 <= sh a /\ sh a + size / 8 < 2^45).
  { unfold sh, kShadowOffset. pose proof (Z.div_pos a 8 A0' ltac:(lia)). pose proof (Z.div_pos size 8 S0' ltac:(lia)).
    pose proof (Z.div_le_mono (a + size) (2^47) 8 ltac:(lia) ltac:(lia)) as DL. change (2^47 / 8) with (2^44) in DL.
    pose proof (sh_add8 a size A8 S8) as E. unfold sh, kShadowOffset in E. lia. }
  unfold kHighMemEnd, kShadowOffset in *.
  carve_frame 32%nat ST.
  do 5 amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callz m2s_al_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundleU. }
  1:{ reflexivity. }
  1:{ unfold fl_in, kLowShadowMapBeg in *. plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callz m2s_al_ok.
  1:{ eassumption. }
  1:{ apply poison_consts_m2s. rebundleU. }
  1:{ reflexivity. }
  1:{ unfold fl_in, kLowShadowMapBeg in *. plia. }
  1:{ rewrite unsigned_lit by lia. reflexivity. }
  amz. amz. (* [comment removed for export] *)
  do 5 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  amz. (* [comment removed for export] *)
  carve_frame 32%nat ST.
  do 5 amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. if_cases KB.
  - (* [comment removed for export] *)
    exfalso. rewrite bv_ltu_Z in KB. apply negb_true_iff in KB. apply Z.ltb_ge in KB.
    rewrite <- SHA in KB. replace (size + a) with (a + size) in KB by lia. rewrite <- SHE in KB.
    rewrite (Z.mod_small (sh a + size / 8)) in KB by lia.
    rewrite (pg_up_land (sh a)), (pg_dn_land (sh a + size / 8)) in KB by lia.
    rewrite !unsigned_lit in KB by lia. lia.
  - amz. amz. (* [comment removed for export] *)
    do 5 amz. release_frame FR ST (bv_unsigned sp).
    amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. br_not_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. br_taken. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    step_ecall.
    rewrite <- SHA. replace (size + a) with (a + size) by lia. rewrite <- SHE.
    rewrite (Z.mod_small (sh a + size / 8)) by lia.
    rewrite (pg_up_land (sh a)), (pg_dn_land (sh a + size / 8)) by lia.
    eapply K; eassumption.
Qed.

Theorem ldealloc_mid_ok : ldealloc_mid_stmt.
Proof.
  unfold ldealloc_mid_stmt. intros until Q.
  intros MI ST LOLE CEIL USP UAL MBLO MS0 MBH MB8 MS8 SNZ SR PC SEAL NE K.
  pose proof alloc_ceiling_val as CV. unfold ldealloc_after, ldealloc_resume in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply flush_pre_ok with (a := mb) (size := msz) (sealed := sealed) (lo := lo).
  all: rewrite ?unsigned_lit by lia.
  all: try sidec.
  intros t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' m' MU' WM' MI' ST'.
  replace (usp + -32 - 64) with (usp - 96) in MU' by lia. replace (usp + -32) with (usp - 32) in MU', ST' by lia.
  eapply K; eassumption.
Qed.

Theorem ldealloc_post2_ok : ldealloc_post2_stmt.
Proof.
  unfold ldealloc_post2_stmt. intros until Q.
  intros MI ST LOLE CEIL USP UAL TPE HLO HHI MSR MBR MUR MDR HC TC TST DJT FR RA K.
  pose proof alloc_ceiling_val as CV. unfold madvise_after_pc, ldealloc_resume, unmapordie_entry, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  pose proof TC as TC'. (first [ dand13 TC' as T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 | destruct TC' as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13) ]). aobj_lin_all.
  unfold pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(usp - 64, usp); (thr + 2888, thr + 2904)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [ eapply thread_stats_ok with (tsd := tsd) (ctx := ctx) (thr := thr) (lo := lo) | post_call_z rsegs mc ] end.
  all: rewrite ?unsigned_lit by lia. all: sidec.
  unfold off_th_stats.
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 5 amz. (* [comment removed for export] *)
  lazymatch goal with H : stk _ ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => release_frame FR H usp end.
  amz. (* [comment removed for export] *)
  replace (msz + md) with (md + msz) in * by lia.
  eapply K; try eassumption.
  all: sidec.
Qed.

End CEIL.
End ARt4fuu.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 AFreeC.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4_gbb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4tam OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4eab OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_soh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARt4fuu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@MSZ; @LHLO; @CV; @LHLLO; @LPALO; @CBLO; @SPR; @LOLE; @CEIL; @LBthr; @IDX; @SEALR; @HQ; @MH2; @MQ; @MH1; @TSDL; @SNZ; @SBHI; @MHR; @LBctx2; @SPH; @SBLO; @CBST; @SEP_lt; @HSB0; @H; @SEP_hp; @SEP_ht; @SEP_pt; @X; @HSB; @H0; @HSB1; @HSB2; @SEP_lp; @SEP_tc; @SEP_pc; @SEP_lc; @SZ8])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Lemma rw_ro_prefix1 : forall (m : word -> option byte) A c1 rest,
  rw_cells rsegs m A (c1 :: rest) -> ro_cells rsegs m A [c1].
Proof. intros m A c1 rest H. apply (rw_cells_app_split m A [c1] rest) in H as [[H _] _]. exact H. Qed.
Lemma rw_ro_prefix2 : forall (m : word -> option byte) A c1 c2 rest,
  rw_cells rsegs m A (c1 :: c2 :: rest) -> ro_cells rsegs m A [c1; c2].
Proof. intros m A c1 c2 rest H. apply (rw_cells_app_split m A [c1; c2] rest) in H as [[H _] _]. exact H. Qed.

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac tf_threshold ::= constr:(4%nat).   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; tf_transport segs m m' MU WM.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac fside_asm := first
  [ lazymatch goal with
    | |- rw_cells ?s ?m ?a _ => match goal with H : rw_cells s m a _ |- _ => exact H end
    | |- ro_cells ?s ?m ?a _ => match goal with H : ro_cells s m a _ |- _ => exact H end
    end
  | eassumption ].
Local Ltac fside_tail E := lazymatch goal with |- ?g => tryif has_evar g then first [ fside_asm | eqrefl ]
             else first [ fside_asm | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; fside_asm
                        | match goal with S : sh _ = _ |- _ => rewrite S; fside_asm end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [fside_asm | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
 end.
Local Ltac fside E ::=
  lazymatch goal with
  | |- apart _ _ _ _ => fail
  | |- forall _ : word, _ => fail
  | |- forall _ : machine_state, _ => fail
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; fside_asm
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- _ mod _ = _ => first [ zmod | fside_tail E ]
  | |- _ \/ _ => first [ solve [kung; slia] | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@LOLE; @CEIL; @LBthr; @Bthr'; @Bctx'; @LBctx2; @LHLO; @HQ; @MQ; @CBLO; @LPALO; @LHLLO])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= first [ solve [ hot_tf_cut; hot_tf_lia0 ] | hot_tf_lia0 ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.simpl_arr_sizes ::= rewrite ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u32s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.u64s_length, ?OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.upd_length.
(* [comment removed for export] *)
Section SecDealloc.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo cb mh sb pa u1 u2 srt h msz csz idx nf ca gA gM nsz st b1 tsd ctx thr rf rfd mu md sealed : Z)
            (hs : list word) (hl hlb hlm hls : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation n := (Z.of_nat (length hs)).
  #[warnings="-notation-for-abbreviation"] Local Notation hla := (bv_unsigned hl).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis TPE : tp = wz TP.
  (* [comment removed for export] *)
  Hypothesis CBLO : alloc_ceiling <= cb.
  Hypothesis CBHI : cb + 16 <= 2^47.
  Hypothesis CBAL : cb mod 8 = 0.
  Hypothesis CBST : cb + 16 <= usp - 80 \/ usp <= cb.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis PALO : aobj pa (8 * n).   (* [comment removed for export] *)
  Hypothesis PAHI : pa + 8 * n <= alloc_ceiling.
  Hypothesis PAAL : pa mod 8 = 0.
  Hypothesis NR : 1 <= n < 2^20.
  Hypothesis U1R : 0 <= u1 < 256.
  Hypothesis U2R : 0 <= u2 < 2^15.
  Hypothesis SRTR : 0 <= srt < 256.
  Hypothesis IDX : 0 <= idx < n.
  Hypothesis NTH : nth_error hs (Z.to_nat idx) = Some (wz h).
  Hypothesis NTL : nth_error hs (Z.to_nat (n - 1)) = Some hl.
  Hypothesis HLLO : aobj hla 32.   (* [comment removed for export] *)
  Hypothesis HLHI : hla + 32 <= alloc_ceiling.
  Hypothesis HLAL : hla mod 8 = 0.
  Hypothesis NFR : 0 <= nf < 2^64.
  Hypothesis CAR : 0 <= ca < 2^64.
  Hypothesis GAR : 0 <= gA < 2^64.
  Hypothesis GMR : 0 <= gM < 2^64.
  Hypothesis CSR : 0 <= csz < 2^64.
  (* [comment removed for export] *)
  Hypothesis HLO : aobj h msz.   (* [comment removed for export] *)
  Hypothesis HAL : h mod 4096 = 0.
  Hypothesis MSZ : 4096 + 32 <= msz.
  Hypothesis MSZAL : msz mod 4096 = 0.
  Hypothesis HHI : h + msz <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis HSB : apart h msz sb (2^37).   (* [comment removed for export] *)
  Hypothesis MHR : h + 32 <= mh /\ mh + 16 <= h + msz.
  Hypothesis NRST : nearest hs mh = h.
  (* [comment removed for export] *)
  Let HSB0 : boxed (h + msz <= sb \/ sb + 2^37 <= h).
  Proof. unfold apart in HSB. exact HSB. Qed.
  Let HSB1 : boxed (0 <= mh < sb \/ sb + 2^37 <= mh < 2^64).
  Proof. pose proof (aobj_facts _ _ HLO). pose proof alloc_ceiling_val. unfold apart in HSB. unfold boxed, kHighMemBeg in *. lia. Qed.
  Let HSB2 : boxed (h + 4096 < sb \/ sb + 2^37 <= h + 4096).
  Proof. pose proof (aobj_facts _ _ HLO). unfold apart in HSB. unfold boxed in *. lia. Qed.
  Hypothesis NSZ : 0 <= nsz < 2^32.
  Hypothesis STR : 0 <= st < 256.
  Hypothesis B1R : 0 <= b1 < 256.
  (* [comment removed for export] *)
  Hypothesis RFR : 0 <= rf < 2^64.
  Hypothesis RFDR : 0 <= rfd < 2^64.
  Hypothesis MUR : 0 <= mu < 2^64.
  Hypothesis MDR : 0 <= md < 2^64.
  Hypothesis SEALR : sealed <> 0 /\ 0 <= sealed < 2^64.
  (* [comment removed for export] *)
  Hypothesis SEP_hp : apart h msz pa (8 * n).
  Hypothesis SEP_lp : apart hla 32 pa (8 * n).
  Hypothesis SEP_ht : apart h msz thr 4096.
  Hypothesis SEP_hc : apart h msz ctx 0x10000.
  Hypothesis SEP_pt : apart pa (8 * n) thr 4096.
  Hypothesis SEP_pc : apart pa (8 * n) ctx 0x10000.
  Hypothesis SEP_lt : apart hla 32 thr 4096.
  Hypothesis SEP_lc : apart hla 32 ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  Hypothesis CLMA : ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)].
  Hypothesis CSEAL : ro_cells rsegs m 0xa8bb0 [C8 (wz sealed)].
  Hypothesis PCo : poison_consts m.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  (* [comment removed for export] *)
  Hypothesis CBC : ro_cells rsegs m cb [C8 (wz (thr + 208))].
  Hypothesis NSRT : rw_cells rsegs m 0xb15d0 [C8 (wz n); C1 (Z_to_bv 8 srt)].
  Hypothesis NFCA : rw_cells rsegs m 0xb15e8 [C8 (wz nf); C8 (wz ca)].
  Hypothesis LCK : rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)].
  Hypothesis GAM : rw_cells rsegs m 0xb1818 [C8 (wz gA); C8 (wz gM)].
  Hypothesis ARR : u64arr rsegs m pa hs.
  Hypothesis HDRL : rw_cells rsegs m h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)].
  Hypothesis HLC : hla = h \/ ((h + 32 <= hla \/ hla + 32 <= h) /\ rw_cells rsegs m hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (n - 1))]).
  Hypothesis HDRU : ro_cells rsegs m mh [C1 (Z_to_bv 8 st); C1 (Z_to_bv 8 b1); C2 (wz (size_hi nsz)); C4 (wz nsz)].
  Hypothesis TRF : rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)].
  Hypothesis TMU : rw_cells rsegs m (thr + 2888) [C8 (wz mu); C8 (wz md)].

  (* [comment removed for export] *)
  Definition sdeal_prefix_W : list (Z * Z) :=
    [(usp - 112, usp); (0xb1800, 0xb1804); (thr + 2840, thr + 2856); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8);
     (0xb1818, 0xb1828); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32)].

  (* [comment removed for export] *)
  #[using="TMU TRF HDRU HLC HDRL ARR GAM LCK NFCA NSRT CBC TSDL TC CSEAL CLMA CSB SEP_tc SEP_lc SEP_lt SEP_pc SEP_pt SEP_ht SEP_lp SEP_hp SEALR RFDR RFR B1R STR NSZ HSB2 HSB1 HSB0 NRST MHR HSB HHI MSZ HAL HLO CSR GMR GAR CAR NFR HLAL HLHI HLLO NTL NTH IDX SRTR U2R U1R NR PAAL PAHI PALO SBHI SBLO CBST CBLO TPE RA2 SPA SPH CEIL ST MI sealed ctx tsd b1 st srt sb Clg"] Lemma sdeal_prefix : forall (Q : machine_state -> Prop),
    lo <= usp - 112 ->
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
        rw_cells rsegs m' (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
        munch sdeal_prefix_W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -32) ->
        evt rsegs Q (MS (mkR (wz ldealloc_after) (wz (usp + -32)) gp tp t0' t1' t2' (wz h) (wz h)
                            (wz h) (wz msz) (wz 0) a3' a4' a5' a6' a7'
                            (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (wz poison_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz mh) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros Q LOLE K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word hl) as HLR; unfold inr64 in HLR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    destruct SEALR as [SNZ SR]. destruct MHR as [MH1 MH2].
    unfold kHighMemBeg, LMA_L in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    pose proof (rw_ro_prefix2 m h _ _ _ HDRL) as HRO. pose proof (rw_ro_prefix1 m 0xb15d0 _ _ NSRT) as NRO.
    pose proof (munch_refl sdeal_prefix_W m) as MU. unfold sdeal_prefix_W in MU. pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl [(usp - 80, usp); (0xb1800, 0xb1804); (thr + 2840, thr + 2856)] m) as MUS.
    (* [comment removed for export] *)
    eapply (cbrec_sec_ok _ _ gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              cb mh sb pa h msz u1 u2 lo hs); rewrite ?NRST; [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros rab t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 CF1 LCK1 ARR1 MU1 WM1 MI1 ST1.
    unfold cbrec_frame in CF1. rewrite ?unsigned_lit in CF1, MU1, ST1 by lia.
    clear LCK ARR NRO. kpost MU1 WM1.
    unfold cbrec_tail. rewrite ?NRST, ?unsigned_lit by lia.
    (* [comment removed for export] *)
    assert (TC1 : thread_cells m1 tp tsd ctx thr) by tcells TPL.
    eapply (cbrec_tails_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1
              usp lo cb mh (h + 4096) sb nsz st b1 tsd ctx thr rf rfd s4 s3 s2 s1 s0 ra); [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try (unfold apart in SEP_ht; lia).
    intros t0c t1c t2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m2 TRF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    clear TRF CF1. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_HDRU); kpost MU2 WM2.
    unfold ldealloc_entry. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    assert (HLC2 : hla = h \/ ((h + 32 <= hla \/ hla + 32 <= h) /\ rw_cells rsegs m2 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (n - 1))])).
    { destruct HLC as [EE|[DD CC]]; [left; exact EE| right; split; [exact DD|]]. xfer CC MUS WM. exact CC. }
    clear HLC MUS.
    rewrite (Z_to_bv_bv_unsigned sp).
    eapply (ldealloc_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2
              h pa idx msz csz nf ca gA gM u1 u2 srt lo hs hl hlb hlm hls); [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try exact HLC2.
    intros t0d t1d t2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m3 DF NSRT3 NFCA3 LCK3 GAM3 ARR3 HDRL3 HLC3 MU3 WM3 MI3 ST3.
    rewrite ?unsigned_lit in DF, MU3, ST3 by lia.
    clear NSRT NFCA GAM HDRL HRO HLC2. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ARR1); kpost MU3 WM3.
    unfold ldealloc_poison. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    amz.
    eapply K.
    all: first [kcell | eassumption].
  Qed.

  (* [comment removed for export] *)
  Definition sdeal_Wd (d : Z) : list (Z * Z) :=
    [(usp - d, usp); (0xb1800, 0xb1804); (thr + 2840, thr + 2856); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8);
     (0xb1818, 0xb1828); (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32); (sh h, sh h + msz / 8); (thr + 2888, thr + 2904)].
  Definition sdeal_W : list (Z * Z) := sdeal_prefix_W ++ [(sh h, sh h + msz / 8); (thr + 2888, thr + 2904)].

  (* [comment removed for export] *)
  #[using="TMU TRF HDRU HLC HDRL ARR GAM LCK NFCA NSRT CBC TSDL TC PCo CSEAL CLMA CSB SEP_tc SEP_lc SEP_lt SEP_pc SEP_pt SEP_ht SEP_lp SEP_hp SEALR RFDR RFR B1R STR NSZ HSB2 HSB1 HSB0 NRST MHR HSB HHI MSZAL MSZ HAL HLO CSR GMR GAR CAR NFR HLAL HLHI HLLO NTL NTH IDX SRTR U2R U1R NR PAAL PAHI PALO SBHI SBLO CBST CBLO TPE RA2 SPA SPH CEIL ST MI sealed ctx tsd b1 st srt sb Clg"] Lemma sdeal_pre : forall (Q : machine_state -> Prop) (old : list byte),
    lo <= usp - 112 -> a8_pbeg h < a8_pend h msz ->
    rw_cells rsegs m (sh h) [CB (Z.to_nat (msz / 8)) old] ->
    (forall (t0' t1' t2' a4' a5' a6' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
        rw_cells rsegs m' (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
        bytes_at rsegs m' (sh h) (repeat (Z_to_bv 8 0) (Z.to_nat (msz / 8))) ->
        munch sdeal_W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -32) ->
        Q (MSsvc (mkR (wz ldealloc_resume) (wz (usp + -32)) gp tp t0' t1' t2' (wz h) (wz h)
                      (wz (a8_pbeg h)) (wz (a8_len h msz)) (wz 4) (wz 4) a4' a5' a6' (wz 233)
                      (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (wz madvise_ecall_pc) (wz 233) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz mh) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz cbrec_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros Q old LOLE NEI SHC K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word hl) as HLR; unfold inr64 in HLR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct SEALR as [SNZ SR]. destruct MHR as [MH1 MH2].
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    (* [comment removed for export] *)
    assert (HQ : h = 4096 * (h / 4096)) by (pose proof (Z_div_mod_eq_full h 4096) as X; rewrite HAL in X; lia).
    assert (MQ : msz = 4096 * (msz / 4096)) by (pose proof (Z_div_mod_eq_full msz 4096) as X; rewrite MSZAL in X; lia).
    set (hq := h / 4096) in *. set (mq := msz / 4096) in *. clearbody hq mq.
    assert (SHE : sh h = 512 * hq + 2147450880).
    { unfold sh, kShadowOffset. rewrite HQ. replace (4096 * hq) with ((512 * hq) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    assert (SZ8 : msz / 8 = 512 * mq) by (rewrite MQ; replace (4096 * mq) with ((512 * mq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold kHighMemBeg in *. rewrite SHE, SZ8 in SHC, K.
    apply sdeal_prefix; [exact LOLE|].
    intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m3 DF NSRT3 NFCA3 LCK3 GAM3 ARR3 HDRL3 HLC3 TRF3 TMU3 MU3 WM3 MI3 ST3.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    pose proof MU3 as MUX. unfold sdeal_prefix_W in MUX.
    xfer Ccan MUX WM3. xfer Cgotcf MUX WM3. xfer Cthr MUX WM3. xfer Cgotsh MUX WM3. xfer Cshoff MUX WM3. xfer Cgotmid MUX WM3.
    xfer Cgotmide MUX WM3. xfer Cgothi MUX WM3. xfer Chivars MUX WM3. xfer Cgotms MUX WM3. xfer Creal MUX WM3. xfer Cgotps MUX WM3. xfer Cps MUX WM3.
    xfer Cini MUX WM3. xfer Ckey MUX WM3. xfer Ctsd MUX WM3. xfer Cctx MUX WM3. xfer Cthr2 MUX WM3.
    xfer CSEAL MUX WM3. xfer SHC MUX WM3. clear MUX.
    clear MI ST CSB CLMA CBC NSRT NFCA LCK GAM ARR HDRL HLC HDRU TRF TMU.
    (* [comment removed for export] *)
    assert (MU : munch sdeal_W m m3).
    { unfold sdeal_W. intros y Hy. apply outside_app in Hy. destruct Hy as [Hy _]. exact (MU3 y Hy). }
    unfold sdeal_W, sdeal_prefix_W in MU. cbn [app] in MU. rewrite SHE, SZ8 in MU. pose proof WM3 as WM. clear MU3 WM3.
    (* [comment removed for export] *)
    kp HLC3. pose proof (munch_refl [(usp - 112, usp); (512 * hq + 2147450880, 512 * hq + 2147450880 + 512 * mq); (thr + 2888, thr + 2904)] m3) as MUB.
    pose proof (wmono_refl rsegs m3) as WMB.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (poison_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 h msz 0 lo old)|];
      [> try (fside CV) .. | idtac].
    all: try (first [zmod | rewrite ?SHE, ?SZ8; kcell | unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption]).
    intros ms' PO. unfold poison_post in PO. destruct_exs PO. (first [ dand6 PO as E4 MUc WMc MI4 ST4 SHZ | destruct PO as (E4 & MUc & WMc & MI4 & ST4 & SHZ) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST4 by lia. rewrite ?SHE, ?SZ8 in MUc, SHZ.
    kp SHZ. clear SHC. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 ldealloc_after)) with (Z_to_bv 64 ldealloc_after) by (symmetry; apply ret_pc_even; [unfold ldealloc_after; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    pose proof (munch_refl [(usp - 112, usp); (thr + 2888, thr + 2904)] m4) as MUB4. pose proof (wmono_refl rsegs m4) as WMB4.
    (* [comment removed for export] *)
    assert (PC4 : poison_consts m4) by (unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption).
    eapply ldealloc_mid_ok with (usp := usp) (lo := lo) (h := h) (mb := h) (msz := msz) (sealed := sealed); [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try (first [zmod | exact NEI | kcell]).
    intros t0e t1e t2e a4e a5e a6e t3e t4e t5e t6e m5 MU5 WM5 MI5 ST5.
    rewrite ?unsigned_lit in MU5, ST5 by lia.
    kpost MU5 WM5.
    (* [comment removed for export] *)
    unfold keep in SHZ, HLC3.
    eapply bytes_at_transport in SHZ; [| exact MUB4 | rewrite repeat_length; cbn [disjoint_from]; lia].
    assert (HLC5 : hla = h \/ rw_cells rsegs m5 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]).
    { destruct HLC3 as [EE|CC]; [left; exact EE| right]. xfer CC MUB WMB. exact CC. }
    assert (MUF : munch sdeal_W m m5).
    { unfold sdeal_W, sdeal_prefix_W. cbn [app]. rewrite SHE, SZ8. exact MU. }
    unfold madvise_ecall_pc, ldealloc_resume in *.
    eapply K.
    all: first [kcell | exact HLC5 | exact MUF | exact WM | rewrite ?SHE, ?SZ8; first [kcell | eassumption] | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="TSDL SEP_tc SEP_lt SEP_pt SEP_ht SEALR MDR MUR MHR MSZ HLO HLLO PALO CBLO TPE RA2 SPA SPH CEIL sealed mh cb"] Lemma sdeal_mid : forall (Q : machine_state -> Prop) (m7 : word -> option byte)
      (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    lo <= usp - 112 ->
    mem_inv rsegs m7 -> stk rsegs m7 lo (usp + -32) ->
    thread_cells m7 tp tsd ctx thr ->
    rw_cells rsegs m7 (usp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs m7 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m7 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
    rw_cells rsegs m7 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
    rw_cells rsegs m7 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
    u64arr rsegs m7 pa (upd hs (Z.to_nat idx) hl) ->
    rw_cells rsegs m7 h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
    (hla = h \/ rw_cells rsegs m7 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
    rw_cells rsegs m7 (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
    rw_cells rsegs m7 (thr + 2888) [C8 (wz mu); C8 (wz md)] ->
    (forall (t0'' t1'' t2'' a3'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -48) (unmap_frame scr s2 s1 s0 ra) ->
        rw_cells rsegs m' 0xb15d0 [C8 (wz (n - 1)); C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))] ->
        rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)] ->
        rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))] ->
        u64arr rsegs m' pa (upd hs (Z.to_nat idx) hl) ->
        rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)] ->
        (hla = h \/ rw_cells rsegs m' hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + nsz))] ->
        rw_cells rsegs m' (thr + 2888) [C8 (wz (mu + 1)); C8 (wz (md + msz))] ->
        munch [(usp - 112, usp); (thr + 2888, thr + 2904)] m7 m' -> wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (usp + -48) ->
        Q (MSsvc (mkR (wz unmap_resume) (wz (usp + -48)) gp tp t0'' t1'' t2'' (wz msz) (wz 0)
                      (wz h) (wz msz) (wz 0) a3'' a4'' a5'' a6'' (wz 215)
                      (wz h) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                 F (wz munmap_ecall_pc) (wz 215) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz ldealloc_resume) (wz (usp + -32)) gp tp t0' t1' t2' (wz h) (wz h)
                        (wz 0) a1' a2' a3' a4' a5' a6' a7'
                        (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F (wz madvise_after_pc) fc None m7 (seg_rom rsegs)).
  Proof.
    intros until t6'. intros LOLE MI7 ST7 TC7 DF NSRT7 NFCA7 LCK7 GAM7 ARR7 HDRL7 HLC7 TRF7 TMU7 K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word hl) as HLR; unfold inr64 in HLR.
    assert (LO0 : 0 <= lo) by (destruct ST7 as [? _]; assumption).
    destruct SEALR as [SNZ SR]. destruct MHR as [MH1 MH2].
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    clear MI ST CSB CLMA CSEAL PCo TC CBC NSRT NFCA LCK GAM ARR HDRL HLC HDRU TRF TMU.
    pose proof TC7 as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold kHighMemBeg in *. rewrite TPL in *.
    pose proof (munch_refl [(usp - 112, usp); (thr + 2888, thr + 2904)] m7) as MU. pose proof (wmono_refl rsegs m7) as WM.
    kp HLC7.
    (* [comment removed for export] *)
    pose proof (rw_ro_prefix2 m7 h _ _ _ HDRL7) as HRO7.
    eapply ldealloc_post2_ok with (usp := usp) (lo := lo) (h := h) (mb := h) (msz := msz) (tsd := tsd) (ctx := ctx) (thr := thr) (mu := mu) (md := md)
              (s2v := s2) (s1v := s1) (s0v := s0) (ra0 := ra); [> try (fside CV) .. | idtac].
    all: try (fside CV). all: try (unfold apart in SEP_ht; lia).
    intros t0e t1e t2e a3e a4e a5e a6e a7e t3e t4e t5e t6e m5 TMU5 MU5 WM5 MI5 ST5.
    rewrite ?unsigned_lit in MU5, ST5 by lia.
    clear TMU7 HRO7 TC7. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_DF); kpost MU5 WM5.
    unfold unmapordie_entry.
    (* [comment removed for export] *)
    rewrite (Z_to_bv_bv_unsigned sp).
    eapply (unmap_pre_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 h msz 0 lo);
      [> try (fside CV) .. | idtac].
    all: try (fside CV).
    intros scr m6 UF MU6 WM6 MI6 ST6. rewrite ?unsigned_lit in UF, MU6, ST6 by lia.
    kpost MU6 WM6.
    unfold keep in HLC7.
    assert (HLC6 : hla = h \/ rw_cells rsegs m6 hla [C8 hlb; C8 hlm; C8 hls; C8 (wz idx)]).
    { destruct HLC7 as [EE|CC]; [left; exact EE| right]. xfer CC MU WM. exact CC. }
    unfold munmap_ecall_pc, unmap_resume in *.
    eapply K.
    all: first [kcell | exact HLC6 | exact MU | exact WM | eassumption].
  Qed.
End SecDealloc.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
