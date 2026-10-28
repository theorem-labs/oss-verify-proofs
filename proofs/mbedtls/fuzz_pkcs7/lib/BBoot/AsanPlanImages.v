(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Export AsanCertDefs.   (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.

(* [comment removed for export] *)
From Ltac2 Require Constr Std Control.
Ltac2 vm_cast_true () :=
  let g := Control.goal () in
  let r := constr:(@eq_refl bool true) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Ltac2 gd_tbl_AsanPlanImages () : Init.string Init.list := ["Stdlib.Lists.List.forallb"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "segs_in_hull_b"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.in_hull"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.BOTH"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.img_lo"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.img_hi"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.Tgt_fuzz_pkcs7_both_segment_000"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.Tgt_fuzz_pkcs7_both_segment_001"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.Tgt_fuzz_pkcs7_both_segment_002"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.Tgt_fuzz_pkcs7_both_segment_003"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
Definition AITAB : itab := mk_itab ASEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof. exact Both_wx_nowrap. Qed.

(* [comment removed for export] *)
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanPlanImages ()) "(0.$1.Lseg,$1.(2.(3.O2.(4.(5.R1.)))(3.(6.(4.(5.R1.))(4.(7.R1.)))O1.))O3.)")
(* [comment removed for export] *).

Lemma find_segment1_none_outside : ltac2:(CDefT.buildp (gd_tbl_AsanPlanImages ()) "Psegs,(8.$1.)Plo,$9.Phi,$9.Px,$9.P,(:.$;.(<.R4.R3.R2.)$=.)P,(>.(?.R2.R4.)(10.R3.R2.))(:.(11.$1.)(12.R6.R3.+1.)(13.$1.))")
(* [comment removed for export] *).
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo BOTH) (img_hi BOTH) = true.
Proof. first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. Qed. (* [comment removed for export] *)

Lemma asan_in_hull : ltac2:(CDefT.buildp (gd_tbl_AsanPlanImages ()) "Pa,(14.&40.)P,(:.$;.(15.$16.(17.&40.R1.))$18.)(:.(11.$1.)(12.$19.(17.&40.R2.)+1.)(13.$1.))")
(* [comment removed for export] *).
Proof.
  intros a H. apply (find_segment1_none_outside ASEGS (img_lo BOTH) (img_hi BOTH)); [exact asan_segs_in_hull|].
  unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS BOTH.
Proof. first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. Qed. (* [comment removed for export] *)

Lemma asan_res_hull : ltac2:(CDefT.buildp (gd_tbl_AsanPlanImages ()) "(1:.(1;.(14.&40.)(14.&40.))Liv,(1;.(14.&40.)(14.&40.))(1<.(10.(1=.$16.)(17.&40.(1>.(14.&40.)(14.&40.)R1.)))(10.(6.(17.&40.(1>.(14.&40.)(14.&40.)R1.))(17.&40.(1?.(14.&40.)(14.&40.)R1.)))(20.$16.)))(21.$19.))")
(* [comment removed for export] *).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x36000); (Z_to_bv 64 0x46000, Z_to_bv 64 0xab000);
                                         (Z_to_bv 64 0x0f1000, Z_to_bv 64 0x6000); (Z_to_bv 64 0x0f7000, Z_to_bv 64 0x568000)])   (* [comment removed for export] *)
    by (first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]) (* [comment removed for export] *).
  rewrite E. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok BOTH.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi BOTH]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok BOTH.
Proof. unfold APS.shadow_ok. cbn [shadow_off BOTH]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x64f000.
Proof. first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. Qed. (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma asan_hull_cov : APS.hull_cov ASEGS BOTH.
Proof.
  unfold APS.hull_cov. cbn [img_lo img_hi BOTH]. split; [lia|].
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x36000); (Z_to_bv 64 0x46000, Z_to_bv 64 0xab000);
                                         (Z_to_bv 64 0x0f1000, Z_to_bv 64 0x6000); (Z_to_bv 64 0x0f7000, Z_to_bv 64 0x568000)])
    by (first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]) (* [comment removed for export] *).
  rewrite E. intros z Hz. unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x46000); [|destruct (Z.lt_ge_cases z 0xf1000); [|destruct (Z.lt_ge_cases z 0xf7000)]].
  - rewrite (proj2 (Z.leb_le 0x10000 z)), (proj2 (Z.ltb_lt z (0x10000 + 0x36000))) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le 0x46000 z)), (proj2 (Z.ltb_lt z (0x46000 + 0xab000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xf1000 z)), (proj2 (Z.ltb_lt z (0xf1000 + 0x6000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
  - rewrite (proj2 (Z.leb_le 0xf7000 z)), (proj2 (Z.ltb_lt z (0xf7000 + 0x568000))) by lia. cbn [andb orb]. rewrite ?orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma asan_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 24576 = true.
Proof. ltac2:(vm_cast_true ()). Qed.
Lemma asan_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5668864 = true.
Proof. ltac2:(vm_cast_true ()). Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 24576%N.
Proof. first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. Qed. (* [comment removed for export] *)
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5668864%N.
Proof. first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. Qed. (* [comment removed for export] *)

Lemma asan_segs_eq : ltac2:(CDefT.buildp (gd_tbl_AsanPlanImages ()) "(:.(8.$1.)$19.(22.$1.$23.(22.$1.$24.(22.$1.$25.(22.$1.$26.(27.$1.))))))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0x0f1000 <= bv_unsigned x < 0x65f000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 24576); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5668864); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x0f7000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS BOTH APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH]. lia.
  - first [lazymatch goal with |- ?g0 => tryif has_evar g0 then fail else (let g := eval hnf in g0 in lazymatch g with _ = ?r => vm_cast_no_check (@eq_refl _ r) end) end | vm_compute; reflexivity]. (* [comment removed for export] *)
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.
