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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARtSoqz ARtSb8o ARtSf1m ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx.

Module ARt3_lma.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtS4t2 ARtSoqz ARtSb8o ARtSf1m ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt34mx.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx.ARt3_pop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx.
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
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
Lemma roundup_page : forall x, 0 <= x < 2^62 -> Z.land (x + 4095) 18446744073709547520 = round_up x 4096.
Proof.
  intros x Hx. change 18446744073709547520 with (2^64 - 2^12). rewrite land_align_down by lia.
  unfold round_up. change (2^12) with 4096. replace (x + 4096 - 1) with (x + 4095) by lia.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096). lia.
Qed.
Lemma roundup_page_range : forall x, 0 <= x -> x <= round_up x 4096 < x + 4096 /\ round_up x 4096 mod 4096 = 0.
Proof. intros x Hx. split; [split; [apply round_up_ge | apply round_up_lt] | apply round_up_mod]; lia. Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 200.





Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem lma_pre_ok : lma_pre_stmt.
Proof.
  unfold lma_pre_stmt. intros until Q. cbv zeta. intros MI ST LOLE CEIL A1 A2 A3 SZ SZ8 PGS GOTN PN PNLO PNHI K.
  pose proof alloc_ceiling_val as CV. unfold lma_entry, lma_mapret, mmapordie_entry, LMA, LSTAT, lma_name, lma_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. subst a1 a2 a3.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 96%nat ST.
  do 12 amz.
  amz. amz. amz. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. amz. if_false. (* [comment removed for export] *)
  pose proof (roundup_page_range size ltac:(lia)) as [RU1 RU2].
  do 9 amz. rewrite roundup_page by lia. amz. (* [comment removed for export] *)
  amz. br_taken. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K; [exact FR | exact MU | exact WM | assumption | exact ST].
Qed.

(* [comment removed for export] *)

#[using="Clg"] Theorem lma_esp_ok : lma_esp_stmt.
Proof.
  unfold lma_esp_stmt. intros until Q. intros MI NR PA0 PAH RR PAC K.
  pose proof alloc_ceiling_val as CV. unfold lma_estest, lma_espost, mapordie_entry, LMA, LSTAT in *. lit_addrs.
  amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  replace (n ≪ 3 + pa) with (pa + 8 * n) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  exact K.
Qed.

#[using="Clg"] Theorem lma_espost_ok : lma_espost_stmt.
Proof.
  unfold lma_espost_stmt. intros until Q. intros MI NR RR NC K.
  pose proof alloc_ceiling_val as CV. unfold lma_espost, lma_tail, LMA, LSTAT in *. lit_addrs.
  pose proof (munch_refl [(726472, 726480)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  eapply K; [exact NC | exact MU | exact WM | assumption].
Qed.


Lemma lxor63_range : forall z, 0 <= z < 64 -> 0 <= Z.lxor z 63 < 64.
Proof. intros z Hz. pose proof (zall_spec 0 63 (fun z => (0 <=? Z.lxor z 63) && (Z.lxor z 63 <? 64)) eq_refl z ltac:(lia)) as H. cbn beta in H. lia. Qed.

Theorem lma_tail_ok : lma_tail_stmt.
Proof.
  unfold lma_tail_stmt. intros until ra0. cbv zeta.
  intros MI ST LOLE CEIL USP UAL LZ NR NRES PALO PAHI PAAL MBLO MBHI MBAL MSR LBSL DJ FR PAC NC STS LKC HC PNC STC RA.
  pose proof alloc_ceiling_val as CV. unfold lma_tail, LMA, LSTAT, lma_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all. lit_addrs.
  pose proof (lxor63_range lz LZ) as IXR. remember (Z.lxor lz 63) as idx eqn:HIDX.
  remember (pa + 8 * n) as pn8 eqn:HPN.
  replace (usp - 96) with (usp + -96) in ST by lia.
  pose proof (munch_refl [(usp - 96, usp); (726472, 726489); (726496, 727040); (727040, 727041);
               (mb + 24, mb + 32); (pn8, pn8 + 8); (727064, 727080)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  apply rw_cells_app_split with (cs1 := [C8 na; C8 nf; C8 ca; C8 mx]) in STS as [STH BSL].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BSL. change (Z.of_nat 32) with 32 in BSL. lit_addrs.
  pose proof BSL as BSL0. apply u8arr_of_rw_cells in BSL.
  assert (BA : u64arr rsegs m 726528 bsl).
  { destruct BSL as [B W]. split; [exact B|]. rewrite u64s_length in W. replace (8 * Z.of_nat (length bsl)) with (Z.of_nat (8 * length bsl)) by lia. exact W. }
  clear BSL.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?P _ => set (Q0 := P) end.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *) replace (pa + n ≪ 3) with pn8 by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  rewrite <- HIDX.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mm _) =>
  assert (J : forall (mxv : word),
    evt rsegs P (MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 727048) (Z_to_bv 64 726424)
                        (Z_to_bv 64 (mb + 4096)) (Z_to_bv 64 idx) mxv (Z_to_bv 64 (bv_unsigned ca + ms)) (Z_to_bv 64 (bv_unsigned na + 1)) ca (Z_to_bv 64 (n + 1)) a7
                        (Z_to_bv 64 ms) (Z_to_bv 64 lz) s4 (Z_to_bv 64 mb) s6 s7 (Z_to_bv 64 7) (Z_to_bv 64 (mb + 4096)) s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x3bd80) fc None mm (seg_rom rsegs))) end.
  { intros mxv.
    destruct (nth_error bsl (Z.to_nat idx)) as [w|] eqn:NW; [| apply nth_error_None in NW; lia].
    amz. amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_read rsegs mm 726528 bsl idx w (Z_to_bv 64 (726424 + idx ≪ 3 + 104)) BA NW ltac:(lia)
                    ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD end.
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    pose proof (u64arr_store_ok rsegs _ 726528 bsl idx (Z_to_bv 64 (726424 + idx ≪ 3 + 104)) BA ltac:(lia) ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as SOK.
    amz. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      replace (write_to_mem mm a bs) with (write_to_mem mm (wa (726528 + 8 * idx)) bs) by (unfold wa; f_equal; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia);
      pose proof (u64arr_write rsegs mm 726528 bsl idx (Z_to_bv 64 (bv_unsigned w + 1)) BA ltac:(lia)) as BA2 end.
    replace (Z_to_bv 64 (726424 + idx ≪ 3 + 104)) with (wa (726528 + 8 * idx)) in SOK by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    clear BA. store_done.
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    do 12 amz. release_frame FR ST usp. amz. (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct BA2 as [B2 W2].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BSL' : rw_cells rsegs mm 726528 [CB 512 (u64s (upd bsl (Z.to_nat idx) (Z_to_bv 64 (bv_unsigned w + 1))))]) end.
    { split; [split; [cbn; rewrite u64s_length, upd_length, LBSL; split; reflexivity | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B2] |].
      cbn [cells_size csize Nat.add]. rewrite upd_length, LBSL in W2. exact W2. }
    lazymatch goal with H : rw_cells rsegs ?mm 726496 [C8 _; C8 _; C8 _; C8 _] |- _ =>
      pose proof (rw_cells_app_join _ _ _ _ H BSL') as STS'; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in STS' end.
    subst Q0. replace (nth (Z.to_nat idx) bsl (Z_to_bv 64 0)) with w by (symmetry; apply nth_error_nth; exact NW).
    finish. all: try eassumption. }
  amz. if_cases KM.
  - eapply J.
  - amz. eapply J.
Qed.

End CEIL.
End ARt3_lma.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_soh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSb8o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_51v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt25ye OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73.ARt3_gfa OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx.ARt3_pop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt34mx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt3mp4.ARt3_lma OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_soh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Lemma land_mul_low : forall j q, 0 <= j -> 0 <= q -> Z.land (2^j * q) (Z.ones j) = 0.
Proof. intros j q Hj Hq. rewrite Z.land_ones by nia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma land4095_l : forall q, 0 <= q -> Z.land 4095 (4096 * q) = 0.
Proof. intros q Hq. rewrite Z.land_comm. change 4095 with (Z.ones 12). change 4096 with (2^12). apply land_mul_low; lia. Qed.
Lemma land_m8_round : forall q r, 0 <= q -> 0 <= r < 8 -> 8 * q + r < 2^64 -> Z.land (8 * q + r) 18446744073709551608 = 8 * q.
Proof.
  intros q r Hq Hr Hb. change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia. change (2^3) with 8.
  rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.
Lemma shr_small : forall a n, 0 <= n -> 0 <= a < 2^n -> Z.shiftr a n = 0.
Proof. intros a n Hn Ha. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma land7_r8 : forall q, 0 <= q -> Z.land (8 * q) 7 = 0.
Proof. intros q Hq. change 7 with (Z.ones 3). change 8 with (2^3). apply land_mul_low; lia. Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 200.






Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
Definition keep (P : Prop) : Prop := P.
Lemma lor_range64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof.
  intros a b Ha Hb. assert (L : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact L|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NZ]; [rewrite E; lia|].
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma shiftr_range64 : forall a d, 0 <= a < 2^64 -> 0 <= d -> 0 <= Z.shiftr a d < 2^64.
Proof.
  intros a d Ha Hd. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. assert (1 <= 2^d) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia). nia.
Qed.
Lemma lor_shiftr_range : forall a d, 0 <= a < 2^64 -> 0 <= d -> 0 <= Z.lor a (Z.shiftr a d) < 2^64.
Proof. intros. apply lor_range64; [lia| apply shiftr_range64; lia]. Qed.
(* [comment removed for export] *)
Ltac hot_name_lor :=
  match goal with
  | |- context [Z.lor ?a (Z.shiftr ?a ?d)] =>
      is_var a;
      let s := fresh "smr" in let H := fresh "HSMR" in let R := fresh "RSMR" in
      remember (Z.lor a (Z.shiftr a d)) as s eqn:H;
      assert (R : 0 <= s < 2^64) by (rewrite H; apply lor_shiftr_range; [ first [ assumption | lia ] | lia ])
  end.

(* [comment removed for export] *)
Lemma lma2_smear_unfold : forall x, smear x = ltac:(let u := eval cbv delta [smear] beta zeta in (smear x) in exact u).
Proof. intros x. reflexivity. Qed.
Lemma lma2_lzG_unfold : forall s, lz_G s = ltac:(let u := eval cbv delta [lz_G] beta zeta in (lz_G s) in exact u).
Proof. intros s. reflexivity. Qed.
Lemma lma2_lma_lz_unfold : forall x, lma_lz x = lz_G (smear x).
Proof. intros x. reflexivity. Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem lma_mid_ok : lma_mid_stmt.
Proof.
  unfold lma_mid_stmt. intros PS P0 TS. intros until Q. cbv zeta.
  intros MI ST LOLE CEIL USP UAL SZ SZ8 TL KR MBLO MBHI MBAL NCH NRES LK1 LK2 PC TC TPLO TSDLO DJ1 FR PGS HC SH1 SH2 THS LKC NC K.
  pose proof alloc_ceiling_val as CV. unfold lma_mapret, lma_estest, LMA, LSTAT, lma_frame, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg, off_th_stats in *. aobj_lin_all. unfold kShadowOffset in TPLO, TSDLO. lit_addrs.
  remember (4096 * k) as ms eqn:HMS.
  remember (mb + 4096 + size) as ue eqn:HUE.
  remember (ms - 4096 - size) as tl eqn:HTL.
  (* [comment removed for export] *)
  set (mq := mb / 4096) in *. assert (MQ : mb = 4096 * mq) by (subst mq; rewrite (Z_div_mod_eq_full mb 4096) at 1; rewrite MBAL; lia). clearbody mq.
  set (s8q := size / 8) in *. assert (S8 : size = 8 * s8q) by (subst s8q; rewrite (Z_div_mod_eq_full size 8) at 1; rewrite SZ8; lia). clearbody s8q.
  assert (TL8 : tl = 8 * (512 * k - 512 - s8q)) by lia.
  assert (MB8 : mb mod 8 = 0) by (rewrite MQ; replace (4096 * mq) with ((512 * mq) * 8) by lia; apply Z_mod_mult).
  assert (UE8 : ue mod 8 = 0) by (rewrite HUE, MQ, S8; replace (4096 * mq + 4096 + 8 * s8q) with ((512 * mq + 512 + s8q) * 8) by lia; apply Z_mod_mult).
  assert (TLM8 : tl mod 8 = 0) by (rewrite TL8, Z.mul_comm; apply Z_mod_mult).
  assert (SHM : sh mb = 512 * mq + 2147450880) by (unfold sh, kShadowOffset; rewrite MQ; replace (4096 * mq) with ((512 * mq) * 8) by lia; rewrite Z.div_mul by lia; lia).
  assert (SHU : sh ue = 512 * mq + 512 + s8q + 2147450880).
  { unfold sh, kShadowOffset. rewrite HUE, MQ, S8. replace (4096 * mq + 4096 + 8 * s8q) with ((512 * mq + 512 + s8q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (TLQ : tl / 8 = 512 * k - 512 - s8q) by (rewrite TL8, Z.mul_comm, Z.div_mul by lia; reflexivity).
  rewrite SHM, SHU, TLQ in *.
  replace (usp - 96) with (usp + -96) in ST by lia.
  replace (thr + 2800 + 72) with (thr + 2872) in * by lia. replace (thr + 2800 + 88) with (thr + 2888) in * by lia.
  pose proof (munch_refl [(usp - 96 - 64, usp - 96); (512 * mq + 2147450880, 512 * mq + 2147450880 + 512);
               (512 * mq + 512 + s8q + 2147450880, 512 * mq + 512 + s8q + 2147450880 + (512 * k - 512 - s8q)); (mb, mb + 24);
               (thr + 2872, thr + 2888); (727040, 727044)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof PC as PC0. unfold poison_consts in PC. (first [ dand13 PC as P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 | destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13) ]). aobj_lin_all.
  pose proof TC as TC0. unfold thread_cells in TC. (first [ dand6 TC as T1 T2 T3 T4 T5 TR | destruct TC as (T1 & T2 & T3 & T4 & T5 & TR) ]). unfold kHighMemBeg in TR. aobj_lin_all.
  (first [ dand8 TR as TR1 TR2 TR3 TR4 TR5 TR6 TR7 TR8 | destruct TR as (TR1 & TR2 & TR3 & TR4 & TR5 & TR6 & TR7 & TR8) ]). aobj_lin_all.
  amz. br_not_taken. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *) replace (Z.land 4095 mb) with 0 by (rewrite MQ, land4095_l by lia; reflexivity).
  amz. if_false. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) replace (Z.land (4096 + mb) 7) with 0 by (rewrite MQ; replace (4096 + 4096 * mq) with (8 * (512 + 512 * mq)) by lia; rewrite land7_r8 by lia; reflexivity).
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. replace (0 + (4096 + mb)) with (mb + 4096) by lia. amz. (* [comment removed for export] *) rewrite <- HUE.
  amz. amz. amz. (* [comment removed for export] *)
  replace (Z.land (mb + 4103) 18446744073709551608) with (mb + 4096)
    by (rewrite MQ; replace (4096 * mq + 4103) with (8 * (512 * mq + 512) + 7) by lia; rewrite land_m8_round by lia; lia).
  replace (Z.land ue 18446744073709551608) with ue
    by (rewrite HUE, MQ, S8; replace (4096 * mq + 4096 + 8 * s8q) with (8 * (512 * mq + 512 + s8q) + 0) by lia; rewrite land_m8_round by lia; lia).
  amz. amz. amz. (* [comment removed for export] *) replace (mb + 4096 - mb) with 4096 by lia.
  amz. (* [comment removed for export] *)
  callzx (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mb 4096 250 lo old1) (fun H => rewrite ?SHM in H; change (4096 / 8) with 512 in H).
  all: try (rewrite SHM). all: try sidec.
  (* [comment removed for export] *)
  lazymatch goal with H : bytes_at rsegs ?mm (512 * mq + 2147450880) _ |- _ =>
    rename H into SHP1; change (keep (bytes_at rsegs mm (512 * mq + 2147450880) (repeat (Z_to_bv 8 250) (Z.to_nat 512)))) in SHP1;
    pose proof (munch_refl [(usp - 96 - 64, usp - 96); (512 * mq + 512 + s8q + 2147450880, 512 * mq + 512 + s8q + 2147450880 + (512 * k - 512 - s8q));
                            (mb, mb + 24); (thr + 2872, thr + 2888); (727040, 727044)] mm) as MU1;
    pose proof (wmono_refl rsegs mm) as WM1 end.
  amz. replace (ms + mb - ue) with tl by lia. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  callzx (P0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ue tl 250 lo old2) (fun H => rewrite ?SHU, ?TLQ in H).
  all: try (rewrite SHU). all: try (rewrite TLQ). all: try sidec.
  all: lazymatch goal with |- evt _ _ _ => idtac | _ => rebundle end.
  lazymatch goal with H : bytes_at rsegs ?mm (512 * mq + 512 + s8q + 2147450880) _ |- _ =>
    rename H into SHP2; change (keep (bytes_at rsegs mm (512 * mq + 512 + s8q + 2147450880) (repeat (Z_to_bv 8 250) (Z.to_nat (512 * k - 512 - s8q))))) in SHP2;
    pose proof (munch_refl [(usp - 96 - 64, usp - 96); (mb, mb + 24); (thr + 2872, thr + 2888); (727040, 727044)] mm) as MU2;
    pose proof (wmono_refl rsegs mm) as WM2 end.
  amz. (* [comment removed for export] *)
  callz (TS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tsd ctx thr lo).
  all: try sidec.
  all: lazymatch goal with |- evt _ _ _ => idtac | _ => rebundle end.
  unfold off_th_stats.
  amz. amz. amz. (* [comment removed for export] *)
  replace (Z.land (mb + 4096) 7) with 0 by (rewrite MQ; replace (4096 * mq + 4096) with (8 * (512 * mq + 512)) by lia; rewrite land7_r8 by lia; reflexivity).
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. amz. (* [comment removed for export] *)
  replace (Z.land 4095 (mb + 4096)) with 0 by (rewrite MQ; replace (4096 * mq + 4096) with (4096 * (mq + 1)) by lia; rewrite land4095_l by lia; reflexivity).
  amz. if_false. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  amz. replace (mb + 4096 - 4096) with mb by lia. (* [comment removed for export] *)
  amz. amz. amz. (* [comment removed for export] *)
  amz. br_not_taken. (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply (hdr4_join _ _ 0 lk1 lk2) in LKC; [| lia | lia | lia | cbn; tauto]. replace (0 + 256 * lk1 + 65536 * lk2) with (256 * lk1 + 65536 * lk2) in LKC by lia.
  amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. amz. amz. amz. (* [comment removed for export] *)
  replace (256 * lk1 + 65536 * lk2) with (256 * (lk1 + 256 * lk2)) by lia. rewrite (cas_set_low0 1 (lk1 + 256 * lk2)) by lia.
  replace (256 * (lk1 + 256 * lk2)) with (256 * lk1 + 65536 * lk2) by lia. replace (1 + 256 * (lk1 + 256 * lk2)) with (1 + 256 * lk1 + 65536 * lk2) by lia.
  scstep; zsimp.
  amz. if_false. (* [comment removed for export] *)
  amz. replace (Z.land (256 * lk1 + 65536 * lk2) 255) with 0 by (replace (256 * lk1 + 65536 * lk2) with (256 * (lk1 + 256 * lk2)) by lia; rewrite land255_low0 by lia; reflexivity).
  amz. if_false. (* [comment removed for export] *)
  replace (1 + (256 * lk1 + 65536 * lk2)) with (1 + 256 * lk1 + 65536 * lk2) in LKC by lia.
  apply (hdr4_split _ _ 1 lk1 lk2) in LKC; [| lia | lia | lia | cbn; tauto].
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *) rewrite (shr_small nch 20) by lia.
  amz. if_false. (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 24 (amz; try hot_name_lor).
  lazymatch goal with R6 : 0 <= ?s6 < 2^64, H6 : ?s6 = Z.lor ?s5 (Z.shiftr ?s5 32) |- _ =>
    rename s6 into sm; rename R6 into SMR;
    assert (HSM : sm = smear ms) by (symmetry; subst; reflexivity);
    repeat match goal with H : ?v = Z.lor _ (Z.shiftr _ _) |- _ => clear H end
  end.
  do 18 amz.
  (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (Z.shiftr ((Z.land ?P 1085102592571150095 * 72340172838076673) mod 18446744073709551616) 56)] =>
    rewrite <- (Z.mod_small (Z.land P 1085102592571150095) 18446744073709551616)
      by abstract (rewrite (Z.land_comm P); pose proof (land_lt_pow2 1085102592571150095 P 60 ltac:(lia) ltac:(apply Z.mod_pos_bound; lia)); lia)   (* [comment removed for export] *)
  end.
  rewrite <- (lma2_lzG_unfold sm).
  pose proof (lma_lz_range ms ltac:(lia)) as LZR.
  rewrite HSM. rewrite <- (lma2_lma_lz_unfold ms).
  replace (ms + mb) with (mb + ms) by lia.
  eapply K; try eassumption.
  - unfold keep in SHP1. eapply bytes_at_transport; [exact SHP1 | exact MU1 | cbn [disjoint_from]; rewrite repeat_length; lia].
  - unfold keep in SHP2. eapply bytes_at_transport; [exact SHP2 | exact MU2 | cbn [disjoint_from]; rewrite repeat_length; lia].
Qed.

End CEIL.
