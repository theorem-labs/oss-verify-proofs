(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcdefs.
Module ICPT_vfscanf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AVFSCANF_T : Z := 0x4252c.
Definition AVFSCANF_ICPT : Z := 0x45e74.
Definition AVFSCANF_RET : Z := 0x45ebc.       (* [comment removed for export] *)
Definition A_REAL_VFSCANF : Z := 0x9681c.    (* [comment removed for export] *)
Definition ASCOMMON : Z := 0x45314.           (* [comment removed for export] *)
Definition ASC_STACK : Z := 2320.             (* [comment removed for export] *)
Definition AVFSI_STACK : Z := 2368.           (* [comment removed for export] *)
Definition A_FMT_LG : Z := 0x21280.           (* [comment removed for export] *)

(* [comment removed for export] *)
Definition vfsi_cells (m : word -> option byte) : Prop :=
  icpt_cells m /\ ro_cells bsegs m 0xa3468 [C8 (Z_to_bv 64 0x9681c)].

Lemma vfsi_cells_munch : forall W m m', vfsi_cells m -> munch W m m' ->
  Forall (fun iv => disjoint_from W (fst iv) (snd iv - fst iv)) icpt_cell_ivs ->
  disjoint_from W 0xa3468 8 -> vfsi_cells m'.
Proof.
  intros W m m' (IC & RL) MU D1 D2. split; [eapply icpt_cells_munch; eauto|].
  eapply ro_cells_transport; [exact RL| exact MU| exact D2].
Qed.

(* [comment removed for export] *)
Definition scommon_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (AQ PD lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'   (* [comment removed for export] *)
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' AQ [C8 (Z_to_bv 64 PD)].
Definition scommon_lg_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo AQ PD : Z),
    mem_inv bsegs m -> icpt_cells m -> lowsh_at m ->
    stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ASC_STACK <= bv_unsigned sp ->
    a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 A_FMT_LG -> a3 = Z_to_bv 64 AQ ->
    rw_cells bsegs m AQ [C8 (Z_to_bv 64 PD)] -> (AQ + 8 <= lo \/ bv_unsigned sp <= AQ) -> (AQ + 8 <= 2^63) ->
    app_range PD 8 -> shadow_ok m PD 8 ->
    evt bsegs (scommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc AQ PD lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASCOMMON) fc None m (seg_rom bsegs)).

Section VfscanfIcpt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo : Z) (strm : word) (AQ PD : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis VC : vfsi_cells m.
  Hypothesis ST0 : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AVFSI_STACK <= bv_unsigned sp.
  Hypothesis HAQ : bv_unsigned sp <= AQ /\ AQ + 8 <= 2^63.

  (* [comment removed for export] *)
  Lemma vfscanf_icpt_prefix : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte),
        munch [(bv_unsigned sp - 2368, bv_unsigned sp)] m m1 (* [comment removed for export] *) -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
        vfsi_cells m1 ->
        stk bsegs m1 lo (bv_unsigned sp + -48) ->
        rw_cells bsegs m1 (bv_unsigned sp + -48) [C8 (Z_to_bv 64 AQ); C8 (Z_to_bv 64 AQ); C8 s2; C8 s1; C8 s0; C8 ra] ->
        evt bsegs Q
          (MS (mkR (Z_to_bv 64 AVFSCANF_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2'
                   (Z_to_bv 64 A_FMT_LG) strm
                   strm (Z_to_bv 64 A_FMT_LG) (Z_to_bv 64 AQ) a3' a4' a5' a6' a7'
                   (Z_to_bv 64 AQ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 A_REAL_VFSCANF) fc None m1 (seg_rom bsegs))) ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 strm (Z_to_bv 64 A_FMT_LG) (Z_to_bv 64 AQ) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AVFSCANF_ICPT) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVFSI_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - AVFSI_STACK, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold AVFSI_STACK in MU.
    pose proof VC as (IC & RL). pose proof IC as IC'. icpt_split IC'.
    pose proof ST0 as ST. clear ST0.
    unfold AVFSCANF_ICPT, A_FMT_LG.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 9 gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 48 - 16, bv_unsigned sp - 48)] mm) as MU1 end.
    gs. callsp try_init_ok.
    1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
    1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
    clear MU1.
    gsto 0x45eb8%Z. gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with STc : stk bsegs mm lo _, FRc : rw_cells bsegs mm (bv_unsigned sp + -48) _ |- _ =>
        apply K; [exact MU| exact WM| assumption| | exact STc| exact FRc] end end.
    eapply vfsi_cells_munch; [exact VC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma vfscanf_icpt_epilogue : forall (xra x9 x18 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (F' : bvmap 5 word) (fc' : bv 32) (m2 : word -> option byte) (r : Z) (Q : machine_state -> Prop),
    scommon_lg_stmt ->
    (r = 1 \/ r = 0 \/ r = -1) ->
    mem_inv bsegs m2 -> vfsi_cells m2 -> lowsh_at m2 ->
    stk bsegs m2 lo (bv_unsigned sp + -48) ->
    rw_cells bsegs m2 (bv_unsigned sp + -48) [C8 (Z_to_bv 64 AQ); C8 (Z_to_bv 64 AQ); C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs m2 AQ [C8 (Z_to_bv 64 PD)] ->
    (r = 1 -> app_range PD 8 /\ shadow_ok m2 PD 8) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m3,
     munch [(bv_unsigned sp - 2368, bv_unsigned sp + -48)] m2 m3 -> wmono bsegs m2 m3 -> mem_inv bsegs m3 ->
     stk bsegs m3 lo (bv_unsigned sp) -> rw_cells bsegs m3 AQ [C8 (Z_to_bv 64 PD)] ->
     evt bsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F' (ret_pc ra) fc' None m3 (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A_FMT_LG) x9 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F' (Z_to_bv 64 AVFSCANF_RET) fc' None m2 (seg_rom bsegs)).
  Proof.
    intros until Q. intros SC Hr MI2 VC2 LOW2 ST2 FR2 AQC CHK K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AVFSI_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2368, bv_unsigned sp + -48)] m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    pose proof VC2 as (IC & RL). pose proof IC as IC'. icpt_split IC'.
    unfold AVFSCANF_RET, A_FMT_LG.
    assert (NOSC : forall r0, (r0 = 0 \/ r0 = -1) ->
      evt bsegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A_FMT_LG) (Z_to_bv 64 r0) (Z_to_bv 64 r0) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F' (Z_to_bv 64 0x45edc) fc' None m2 (seg_rom bsegs)) ->
      evt bsegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 A_FMT_LG) x9 (Z_to_bv 64 r0) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F' (Z_to_bv 64 0x45ebc) fc' None m2 (seg_rom bsegs))).
    { intros r0 Hr0 KK. destruct Hr0 as [-> | ->]; (gs; gs; exact KK). }
    destruct Hr as [-> | Hr0].
    - (* [comment removed for export] *)
      destruct (CHK eq_refl) as [ARP SOP].
      gs. gs.
      do 5 gs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 48 - 2320, bv_unsigned sp - 48)] mm) as MU1 end.
      gs. callsp SC; [ exact MI2 | exact IC | exact LOW2 | exact ST2 | exact CEIL | unfold ASC_STACK; lia | reflexivity | reflexivity | reflexivity
                     | exact AQC | lia | lia | exact ARP | exact SOP | ].
      clear MU1.
      do 7 gs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with STc : stk bsegs mm lo _, FRc : rw_cells bsegs mm (bv_unsigned sp + -48) _, AQc : rw_cells bsegs mm AQ _ |- _ =>
          release_frame FRc STc (bv_unsigned sp);
          try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp));
          apply K; [exact MU| exact WM| assumption| exact STc| exact AQc] end end.
    - (* [comment removed for export] *)
      apply (NOSC r Hr0).
      do 7 gs.
      release_frame FR2 ST2 (bv_unsigned sp).
      try (replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)).
      apply K; [exact MU| exact WM| exact MI2| exact ST2| exact AQC].
  Qed.
End VfscanfIcpt.


End CeilWrap.
End ICPT_vfscanf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.ICPT_pcdefs2.
Import ICPT_vfscanf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
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

Lemma fmt_lg_bytes : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x21280 [CB 4 (zbs [37; 108; 103; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x21280 (zbs [37; 108; 103; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma tbl_scs : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x17986 [CB 6 (zbs [99; 67; 115; 83; 91; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x17986 (zbs [99; 67; 115; 83; 91; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

(* [comment removed for export] *)
Lemma imemset32_call : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (P : Z) (junk : list byte),
  rw_cells bsegs m P [CB 32 junk] -> mem_inv bsegs m -> 0 <= P -> P + 32 < 2^64 ->
  evt bsegs (imemset_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc P 0 32 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 32) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AIMEMSET) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros DST MI H1 H2.
  destruct (Z.eq_dec (Z.land (Z.lor 32 P) 15) 0) as [AL|NAL]; [| eapply imemset_call; eauto; lia].
  assert (P16 : P mod 16 = 0).
  { rewrite Z.land_lor_distr_l in AL. apply Z.lor_eq_0_iff in AL. destruct AL as [_ AL].
    change 15 with (Z.ones 4) in AL. rewrite Z.land_ones in AL by lia. exact AL. }
  unfold AIMEMSET.
  pose proof (munch_refl [(P, P + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in DST; [| reflexivity]. cbn [mk_CB_cells app] in DST.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; try (exfalso; apply K0; first [exact AL | rewrite Z.lor_comm; exact AL]).
  zstep. if_cases K1; zify_cond K1; try (exfalso; revert K1; rewrite ?unsigned_lit by lia; lia).
  do 8 zstep.
  gs. gs. gs. zstep. if_cases K2; zify_cond K2; try (exfalso; revert K2; rewrite ?unsigned_lit by lia; lia).
  all: pc_is.
  gs. gs. gs. zstep. if_cases K3; zify_cond K3; try (exfalso; revert K3; rewrite ?unsigned_lit by lia; lia).
  all: pc_is.
  zstep.
  apply (rw_cells_recast bsegs _ P _ [CB (Z.to_nat 32) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 32))]) in DST;
    [| cbn; repeat split; exact I | apply bytes_eqb_sound; vm_compute; reflexivity].
  apply evt_done. unfold imemset_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact DST].
Qed.

Section Scommon_lg.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo AQ PD : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis IC : icpt_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + ASC_STACK <= bv_unsigned sp.
  Hypothesis AQC : rw_cells bsegs m AQ [C8 (Z_to_bv 64 PD)].
  Hypothesis SEPQ : AQ + 8 <= lo \/ bv_unsigned sp <= AQ.
  Hypothesis AQB : AQ + 8 <= 2^63.
  Hypothesis ARP : app_range PD 8.
  Hypothesis SOP : shadow_ok m PD 8.

  Lemma RBP : 0 <= PD /\ PD + 8 < 2^47. Proof. exact (app_range_lt47 _ _ ARP). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : ASC_STACK = 2320. Proof. reflexivity. Qed.
  Hypothesis AQlo : 0 <= AQ.   (* [comment removed for export] *)

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (scommon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc AQ PD lo m).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation DIRC := ([C4 (Z_to_bv 64 (-1)); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0];
                     C8 (Z_to_bv 64 135808); C8 (Z_to_bv 64 135811);
                     CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; C1 (Z_to_bv 8 108); CB 1 [Z_to_bv 8 0]; C1 (Z_to_bv 8 103);
                     CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]; CB 1 [Z_to_bv 8 0]] : list cell).
  Definition sc_frame (j0 j1 : list byte) (w2 w3 : word) (mm : word -> option byte) : Prop :=
    mem_inv bsegs mm /\ icpt_cells mm /\ stk bsegs mm lo (bv_unsigned sp + -2240) /\ stk bsegs mm (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ rw_cells bsegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs mm (bv_unsigned sp + -2240) [CB 8 j0; CB 8 j1; C8 w2; C8 w3]
    /\ rw_cells bsegs mm (bv_unsigned sp + -2208) DIRC
    /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)] m mm /\ wmono bsegs m mm
    /\ shadow_ok mm PD 8 /\ rw_cells bsegs mm AQ [C8 (Z_to_bv 64 PD)]
    /\ ro_cells bsegs mm 0x21280 [CB 4 (zbs [37; 108; 103; 0])].
  Ltac sc_intro AF := (nelim AF 12%nat; intros MI' IC' STa STb FR FBa FBd MU' WM' SO AQC' FMT').
  Ltac sc_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))); eassumption.

  #[warnings="-notation-for-abbreviation"]
  Notation SC_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 135811) x21 x22 (Z_to_bv 64 8) x24 x25 (Z_to_bv 64 (bv_unsigned sp + -2208)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma sc_ret : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x45cb8 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. sc_intro AF.
    pose proof RBP as RB. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof AQlo as AQ0.
    do 16 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk bsegs mm2 lo _, ST3 : stk bsegs mm2 (bv_unsigned sp + -2176) _,
                          FR3 : rw_cells bsegs mm2 (bv_unsigned sp + -104) _, FA3 : rw_cells bsegs mm2 (bv_unsigned sp + -2240) _,
                          FD3 : rw_cells bsegs mm2 (bv_unsigned sp + -2208) _ |- _ =>
        release_frame FA3 ST1 (bv_unsigned sp + -2208);
        release_frame FD3 ST1 (bv_unsigned sp + -2176);
        pose proof (stk_merge bsegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end.
    try (replace (bv_unsigned sp + -2240 + 208 + 2032) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
    apply evt_done. unfold scommon_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [assumption|]. split; [assumption| exact AQC'].
  Qed.

  (* [comment removed for export] *)
  Lemma sc_560 : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x45994 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof AF as AF'. sc_intro AF'. pose proof RBP as RB.
    gs. gs. gs. gs. eapply sc_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_424 : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm -> 0 <= bv_unsigned x24 + 8 < 2^64 ->
    evt bsegs POST (SC_ 0x45858 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF H24. pose proof AF as AF'. sc_intro AF'. pose proof RBP as RB.
    gs. gs. gs. eapply sc_560. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_region : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x459f0 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 PD) (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. sc_intro AF.
    pose proof RBP as RB. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof AQlo as AQ0.
    pose proof IC' as IC2. pose proof SO as SO2. pose proof CEIL as CEn. try rewrite CE in CEn.
    pose proof (munch_refl [(bv_unsigned sp - 2240 - 80, bv_unsigned sp - 2240)] mm) as MU1.
    pose proof (wmono_refl bsegs mm) as WM1.
    zstep. zstep. zstep.
    callsp region_is_poisoned_ok;
      [ exact IC' | exact MI' | exact STa | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact ARP | exact SO | ].
    zstep. fold_lits. sh_if_true.
    eapply sc_424; [| rewrite unsigned_lit by lia; lia].
    lazymatch goal with |- sc_frame _ _ _ _ ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2, WMc : wmono bsegs mm mm2 |- _ =>
        assert (IC3 : icpt_cells mm2) by (eapply icpt_cells_munch; [exact IC2| exact MUc|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
        assert (SO3 : shadow_ok mm2 PD 8) by (eapply shadow_ok_munch_app; [exact SO2| exact MUc| lia| exact ARP|]; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil])
      end end.
    sc_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_5b4 : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x459e8 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 PD) (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBP as RB. pose proof AQlo as AQ0.
    zstep. zstep. if_cases Kc.
    - eapply sc_424; [exact AF| rewrite unsigned_lit by lia; lia].
    - eapply sc_region; exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_loop : forall j0 j1 w2 w3 mm (k : nat) (i : Z) x1 x5 x6 x7 x9 (acc : word) x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    Z.to_nat (SH (PD + 7) - SH PD - i) = k -> 0 <= i -> SH PD + i < SH (PD + 7) ->
    evt bsegs POST (SC_ 0x459d8 mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + PD / 8 + i)) (Z_to_bv 64 (2147450880 + (PD + 7) / 8)) acc
                        x13 x14 x15 x16 x17 x21 (Z_to_bv 64 PD) (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros j0 j1 w2 w3 mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 x9 acc x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31 AF Hk Hi Hlt;
      pose proof RBP as RB; pose proof (SH_bounds PD ltac:(lia)) as B1; pose proof (SH_bounds (PD + 7) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. sc_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + PD / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + PD / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 SO (2147450880 + PD / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + PD / 8 + i + 1) with (2147450880 + PD / 8 + (i + 1)) by lia.
      eapply (IH (i + 1)); try eassumption; lia.
    - replace (2147450880 + PD / 8 + i + 1) with (2147450880 + (PD + 7) / 8) by lia.
      eapply sc_5b4; exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_slow : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x459bc mm x1 x5 x6 x7 x9 (Z_to_bv 64 (2147450880 + PD / 8)) (Z_to_bv 64 (2147450880 + (PD + 7) / 8)) (Z_to_bv 64 (PD + 7))
                        x13 x14 x15 x16 x17 x21 (Z_to_bv 64 PD) (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBP as RB.
    pose proof (SH_bounds PD ltac:(lia)) as B1. pose proof (SH_bounds (PD + 7) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. sc_intro AF'.
    (nelim (shadow_ok_shb mm PD 8 (8 - 1) SO ltac:(lia)) 3%nat; intros ve SHE Ce).
    replace (PD + (8 - 1)) with (PD + 7) in SHE, Ce by lia.
    pose proof (shb_load_div' mm (PD + 7) ve (PD + 7) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - eapply sc_5b4; exact AF.
    - replace (2147450880 + PD / 8) with (2147450880 + PD / 8 + 0) by lia.
      eapply (sc_loop j0 j1 w2 w3 mm (Z.to_nat (SH (PD + 7) - SH PD - 0)) 0); try exact AF; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sc_quick : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x4581c mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 (Z_to_bv 64 PD) (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBP as RB.
    pose proof (SH_bounds PD ltac:(lia)) as B1. pose proof (SH_bounds (PD + 7) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. sc_intro AF'.
    pose proof IC' as IC2. icpt_split IC2.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + PD / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (PD + 7) / 8) / 8 * 8)) as (w2' & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 SO). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - eapply sc_slow; exact AF.
    - eapply sc_424; [exact AF| pose proof AQlo; rewrite unsigned_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sc_3bc : forall j0 j1 w2 w3 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x27 x28 x29 x30 x31,
    sc_frame j0 j1 w2 w3 mm ->
    evt bsegs POST (SC_ 0x457f0 mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 (Z_to_bv 64 AQ) x25 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RBP as RB. pose proof AQlo as AQ0. pose proof AF as AF'. sc_intro AF'.
    zstep.
    gs. (* [comment removed for export] *)
    gs. gs. gs. gs. (* [comment removed for export] *)
    zstep. fold_lits. rewrite (zb_lxor_ones PD) by lia.
    zstep. if_cases K1; zify_cond K1; try (exfalso; revert K1; rewrite ?unsigned_lit by lia; lia).
    all: try (gs; gs; gs; eapply sc_quick; exact AF).
  Qed.

  Lemma scommon_lg_body :
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 1) (Z_to_bv 64 A_FMT_LG) (Z_to_bv 64 AQ) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASCOMMON) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold ASC_STACK in SPB.
    pose proof RBP as RB. pose proof AQlo as AQ0.
    pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_scs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6.
    pose proof (fmt_lg_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffc250 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW. lowsh_eval SHW.
    pose proof IC as IC'. icpt_split IC'.
    unfold ASCOMMON, A_FMT_LG.
    (* [comment removed for export] *)
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split bsegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 32]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app bsegs _ _ [_; _; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 32) with (bv_unsigned sp + -2208) in FBd by lia.
    do 16 gs.
    gsto 0x453b0%Z.
    shw_read SHW. gs. gs.
    repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end.
    gsto 0x45434%Z.
    (* [comment removed for export] *)
    lazymatch goal with FBd : rw_cells bsegs _ (bv_unsigned ?u + -2208) _ |- _ =>
      apply (rw_cells_merge bsegs _ _ [] [_; _; _; _; _] []) in FBd; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FBd end.
    gs. call imemset32_call; [exact FBd | assumption | lia | lia | ].
    lazymatch goal with FBd : rw_cells bsegs _ (bv_unsigned ?u + -2208) [CB _ (repeat _ _)] |- _ =>
      change (0 mod 256) with 0 in FBd; change (Z.to_nat 32) with 32%nat in FBd; cbn [repeat] in FBd;
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FBd; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FBd
    end.
    lazymatch goal with H : rw_cells bsegs _ (bv_unsigned sp + -2208) _ |- _ => rename H into FBd end.
    gsto 0x495ec%Z.
    (* [comment removed for export] *)
    carve_frame 32%nat STa.
    lazymatch goal with FV : rw_cells bsegs _ (bv_unsigned sp + -2272) _ |- _ =>
      apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8]%nat) in FV; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FV end.
    gsto 0x45710%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : rw_cells bsegs mm (bv_unsigned sp + -2272) _ |- _ =>
        lazymatch goal with STa' : stk bsegs mm _ (bv_unsigned sp + -2272) |- _ =>
          release_frame H STa' (bv_unsigned sp + -2240); rename STa' into STa end end end.
    gsto 0x457f0%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ICm : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MU|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
      assert (SOm : shadow_ok mm PD 8) by (eapply shadow_ok_munch_app; [exact SOP| exact MU| lia| exact ARP|]; apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil])
    end.
    eapply sc_3bc.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))); eassumption.
  Qed.
End Scommon_lg.

Lemma scommon_lg_ok : scommon_lg_stmt.
Proof.
  unfold scommon_lg_stmt. intros until PD. intros MI IC LOW ST CEIL SPB -> -> -> AQC SEPQ AQB ARP SOP.
  pose proof (rw_cells_bound _ _ _ _ AQC) as B.
  eapply scommon_lg_body; try eassumption. lia.
Qed.


End CeilWrap.
