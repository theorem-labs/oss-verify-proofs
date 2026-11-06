(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AIcpm9j ARtStmts ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@SZ; @HI; @HE; @HI0; @K; @Hs; @VAL; @Hq; @LOLE; @SR2; @VTH; @H; @VZ])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstep1 := first [ zstep; fold_xlits | if_false | if_true | br_auto ].
Ltac run_to_a pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep1 end).
Ltac run_to_with pc tac := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep1; tac end).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem poison0_ok : poison0_stmt.
Proof.
  unfold poison0_stmt. intros until old. intros MI ST LOLE CEIL A0 A1 A2 AL SZ8 SZ HI HE VAL VTH PC SH RA.
  pose proof alloc_ceiling_val as CV.
  unfold poison_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (sh addr, sh addr + size / 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (first [ dand13 PC as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
  replace (0x146ee8 + 120) with 0x146f60 in Cthr by reflexivity.
  unfold sh in *. unfold kShadowOffset, kHighMemEnd, pz_in, pz0_in, fl_in, kLowShadowMapBeg, kHighMemBeg in *. aobj_lin_all.
  (* [comment removed for export] *)
  pose proof (proj2 (Z.div_exact addr 8 ltac:(lia)) AL) as Hq. set (q := addr / 8) in *.
  pose proof (proj2 (Z.div_exact size 8 ltac:(lia)) SZ8) as Hs. set (s := size / 8) in *.
  assert (Hq8 : addr / 8 = q) by (rewrite Hq, Z.mul_comm, Z.div_mul; lia).
  assert (Hs8 : size / 8 = s) by (rewrite Hs, Z.mul_comm, Z.div_mul; lia).
  clearbody q s.
  assert (LA : Z.land addr 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; subst addr; rewrite Z.mul_comm; apply Z_mod_mult).
  assert (LSZ : Z.land size 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; subst size; rewrite Z.mul_comm; apply Z_mod_mult).
  assert (SR1 : Z.shiftr addr 3 = q) by (rewrite Z.shiftr_div_pow2, Hq by lia; change (2^3) with 8; rewrite Z.mul_comm, Z.div_mul; lia).
  assert (SR2 : Z.shiftr (addr + size + -8) 3 = q + s - 1).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. replace (addr + size + -8) with ((q + s - 1) * 8) by lia. rewrite Z.div_mul; lia. }
  subst a0 a1 a2.
  pose proof (rw_cells_bound _ _ _ _ SH) as SHB. cbn [cells_size csize Nat.add] in SHB. rewrite Nat.add_0_r, Z2Nat.id in SHB by lia.
  carve_frame 64%nat ST.
  (* [comment removed for export] *)
  destruct HI as [[HI0 HI]|HI].
  all: run_to_a 0x59db4. all: zstep. all: (if_cases VZ; zify_cond VZ).
  all: run_to_with 0x5a03c ltac:(try rewrite LA; try rewrite LSZ).
  all: rewrite ?SR1, ?SR2; rewrite ?(Z.add_comm 2147450880 q).
  1,3: subst value.
  all: run_to_a 0x5a130.
  all: release_frame FR ST (bv_unsigned sp).
  all: zstep.
  all: try replace ((q + s - 1 + 1) mod 18446744073709551616 - q) with s by (rewrite Z.mod_small by lia; lia).
  all: try replace (q + s - 1 + 1 - q) with s by lia.
  all: callz memset_spec_z.
  all: try exact SH. all: try exact MI. all: try lia.
  all: rename POST into RW.
  all: pose proof (rw_cells_bytes_at _ _ _ _ RW) as BA; cbn [cells_bytes cbytes app] in BA; rewrite app_nil_r in BA.
  1,3: change (0 mod 256) with 0 in BA.
  2,4: rewrite Z.mod_small in BA by lia.
  all: finish.
  all: unfold sh, kShadowOffset; rewrite ?Hq8, ?Hs8.
  all: try exact BA.
  all: replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact MU.
Qed.

End CEIL.
