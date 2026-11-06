(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcleaf ICPT_pcdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AVFPRINTF_T : Z := 0x4250c.
Definition AVFPRINTF_ICPT : Z := 0x46b54.
Definition AVFPRINTF_RET : Z := 0x46bc4.      (* [comment removed for export] *)
Definition A_REAL_VFPRINTF : Z := 0x94664.   (* [comment removed for export] *)
Definition AVFI_STACK : Z := 2320.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vfi_cells (m : word -> option byte) : Prop :=
  icpt_cells m /\ ro_cells asegs m 0x13bdfc [C1 (zb 1)] /\ ro_cells asegs m 0xa3cf8 [C8 (Z_to_bv 64 0x94664)].

Lemma vfi_cells_munch : forall W m m', vfi_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  disjoint_from W 0x13bdfc 1 -> disjoint_from W 0xa3cf8 8 -> vfi_cells m'.
Proof.
  intros W m m' (IC & CF & RL) MU D1 D2 D3. split; [eapply icpt_cells_munch; eauto|].
  split; (eapply ro_cells_transport; [| exact MU|]; [eassumption| assumption]).
Qed.

Section VfprintfIcpt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo fa : Z) (strm apw : word).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis VC : vfi_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AVFI_STACK <= bv_unsigned sp.
  Hypothesis PC : pcommon_stmt fa.
  Hypothesis HF : 0 <= fa < 2^64.

  (* [comment removed for export] *)
  Lemma vfprintf_icpt_prefix : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
        munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m1 (* [comment removed for export] *) -> wmono asegs m m1 -> mem_inv asegs m1 ->
        vfi_cells m1 ->
        stk asegs m1 lo (bv_unsigned sp + -48) ->
        rw_cells asegs m1 (bv_unsigned sp + -48) [C8 apw; C8 apw; C8 s2; C8 s1; C8 s0; C8 ra] ->
        evt asegs Q
          (MS (mkR (Z_to_bv 64 AVFPRINTF_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2'
                   (Z_to_bv 64 fa) strm
                   strm (Z_to_bv 64 fa) apw a3' a4' a5' a6' a7'
                   apw s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 A_REAL_VFPRINTF) fc None m1 (seg_rom asegs))) ->
    evt asegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 strm (Z_to_bv 64 fa) apw a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVFPRINTF_ICPT) fc None m (seg_rom asegs)).
  Proof.
    intros until Q. intros K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVFI_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - AVFI_STACK, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold AVFI_STACK in MU.
    pose proof VC as (IC & CF & RL). pose proof IC as IC'. icpt_split IC'.
    pose proof ST0 as ST. clear ST0.
    unfold AVFPRINTF_ICPT.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 10 gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 48 - 16, bv_unsigned sp - 48)] mm) as MU1 end.
    callsp try_init_ok.
    1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
    1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
    clear MU1.
    gsto 0x46ba8%Z. gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SB1 : shbase_cells mm) by (eapply shbase_cells_munch; [exact (proj1 IC)| exact MU| cbn; lia| cbn; lia]);
      assert (LOW1 : lowsh_at mm) by (eapply lowsh_at_munch_stack; [exact LOW| exact MU| exact WM| lia]);
      pose proof (munch_refl [(bv_unsigned sp - 48 - 2272, bv_unsigned sp - 48)] mm) as MU2;
      lazymatch goal with STc : stk asegs mm lo _ |- _ =>
        callsp PC; [ assumption | exact SB1 | exact LOW1 | exact STc | exact CEIL | unfold APC_STACK; lia | reflexivity | ] end end.
    clear MU2 SB1 LOW1.
    (* [comment removed for export] *)
    gsto 0x94664%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with STc : stk asegs mm lo _, FRc : rw_cells asegs mm (bv_unsigned sp + -48) _ |- _ =>
        apply K; [exact MU| exact WM| assumption| | exact STc| exact FRc] end end.
    eapply vfi_cells_munch; [exact VC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma vfprintf_icpt_epilogue : forall (xra x8 x9 x18 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c0 c1 : word)
      (F' : bvmap 5 word) (fc' : bv 32) (m2 : word -> option byte) (Q : machine_state -> Prop),
    mem_inv asegs m2 ->
    stk asegs m2 lo (bv_unsigned sp + -48) ->
    rw_cells asegs m2 (bv_unsigned sp + -48) [C8 c0; C8 c1; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (stk asegs m2 lo (bv_unsigned sp) ->
     evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F' (ret_pc ra) fc' None m2 (seg_rom asegs))) ->
    evt asegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F' (Z_to_bv 64 AVFPRINTF_RET) fc' None m2 (seg_rom asegs)).
  Proof.
    intros until Q. intros MI2 ST2 FR2 K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVFI_STACK in SPB.
    unfold AVFPRINTF_RET.
    do 6 gs.
    release_frame FR2 ST2 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)).
    apply K. exact ST2.
  Qed.
End VfprintfIcpt.


End CeilWrap.
