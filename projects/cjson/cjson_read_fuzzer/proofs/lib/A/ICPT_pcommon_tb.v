(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcdefs2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require JunkAbs.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.JunkAbs.split_for_access_raw H segs m A cs kn n.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma fmt_tb_bytes : forall m, mem_inv asegs m ->
  ro_cells asegs m 0x19748 [CB 33 (zbs [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0])].
Proof.
  intros m MI. apply (ro_cells_image asegs m 0x19748 (zbs [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32; 37; 117; 32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10; 0]) MI);
    [vm_compute; reflexivity| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
Ltac pc_walk2 :=
  do 16 gs;
  gsto 0x46124%Z;
  lazymatch goal with SHW1 : rw_cells asegs _ 0x7fffb6b8 _, SHW2 : rw_cells asegs _ 0x7fffb6c0 _ |- _ => shw_read SHW1; shw_read SHW2 end;
  gs; gs;
  repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end;
  gsto3 0x461a0%Z 0x46978%Z 0x46978%Z;
  repeat (at_pc 0x461a0%Z; pc_iter);
  repeat gs;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with STa : stk asegs mm _ (bv_unsigned ?u + -2240) |- _ =>
  lazymatch goal with STb : stk asegs mm (bv_unsigned u + -2176) _ |- _ =>
  lazymatch goal with FBa : rw_cells asegs mm (bv_unsigned u + -2240) _ |- _ =>
  lazymatch goal with FBd : rw_cells asegs mm (bv_unsigned u + -2216) _ |- _ =>
  lazymatch goal with FR : rw_cells asegs mm (bv_unsigned u + -104) _ |- _ =>
    release_frame FBa STa (bv_unsigned u + -2216);
    release_frame FBd STa (bv_unsigned u + -2176);
    let ST := fresh "ST" in
    pose proof (stk_merge asegs mm _ _ _ STa STb ltac:(lia)) as ST; clear STa STb;
    release_frame FR ST (bv_unsigned u) end end end end end end;
  finish.

Section Pcommon_tb.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APC_STACK <= bv_unsigned sp.

  Lemma pcommon_tb_body :
    evt asegs (pcommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x19748) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APC_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_tb_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffb2e8 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof SB as SB'. shbase_split SB'.
    unfold APRINTF_COMMON.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    pc_walk.
  Qed.
End Pcommon_tb.

Lemma pcommon_tb_ok : pcommon_stmt 0x19748.
Proof. unfold pcommon_stmt. intros until lo. intros MI SB LOW ST CEIL SPB ->. eapply pcommon_tb_body; eassumption. Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac pc_walk2 :=
  do 16 gs;
  gsto 0x46124%Z;
  lazymatch goal with SHW1 : rw_cells asegs _ 0x7fffb6b8 _, SHW2 : rw_cells asegs _ 0x7fffb6c0 _ |- _ => shw_read SHW1; shw_read SHW2 end;
  gs; gs;
  repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end;
  gsto3 0x461a0%Z 0x46978%Z 0x46978%Z;
  repeat (at_pc 0x461a0%Z; pc_iter);
  repeat gs;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with STa : stk asegs mm _ (bv_unsigned ?u + -2240) |- _ =>
  lazymatch goal with STb : stk asegs mm (bv_unsigned u + -2176) _ |- _ =>
  lazymatch goal with FBa : rw_cells asegs mm (bv_unsigned u + -2240) _ |- _ =>
  lazymatch goal with FBd : rw_cells asegs mm (bv_unsigned u + -2216) _ |- _ =>
  lazymatch goal with FR : rw_cells asegs mm (bv_unsigned u + -104) _ |- _ =>
    release_frame FBa STa (bv_unsigned u + -2216);
    release_frame FBd STa (bv_unsigned u + -2176);
    let ST := fresh "ST" in
    pose proof (stk_merge asegs mm _ _ _ STa STb ltac:(lia)) as ST; clear STa STb;
    release_frame FR ST (bv_unsigned u) end end end end end end;
  finish.
