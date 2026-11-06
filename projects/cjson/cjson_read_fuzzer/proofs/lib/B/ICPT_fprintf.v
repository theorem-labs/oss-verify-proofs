(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_pcsdefs ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rwc_eq : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Definition AFPRINTF_ICPT : Z := 0x4722c.
Definition AFPRINTF_RET : Z := 0x472ec.       (* [comment removed for export] *)
Definition AFPI_STACK : Z := 2432.             (* [comment removed for export] *)

Section FprintfIcpt.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo fa : Z) (strm : word).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis VC : vfi_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis ST0 : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + AFPI_STACK <= bv_unsigned sp.
  Hypothesis HF : 0 <= fa < 2^64.

  (* [comment removed for export] *)
  Definition fprintf_icpt_K (a2 a3 a4 a5 a6 a7 : word) (Q : machine_state -> Prop) : Prop :=
    forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : word -> option byte) (u : list byte),
        munch [(bv_unsigned sp - 2432, bv_unsigned sp)] m m1 (* [comment removed for export] *) -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
        vfi_cells m1 ->
        stk bsegs m1 lo (bv_unsigned sp + -112) ->
        rw_cells bsegs m1 (bv_unsigned sp + -112)
           [CB 8 u; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
            C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
        evt bsegs Q
          (MS (mkR (Z_to_bv 64 AFPRINTF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2'
                   (Z_to_bv 64 fa) strm
                   strm (Z_to_bv 64 fa) (Z_to_bv 64 (bv_unsigned sp + -48)) (Z_to_bv 64 A_REAL_VFPRINTF) a4' a5' a6' a7'
                   (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 A_REAL_VFPRINTF) fc None m1 (seg_rom bsegs)).

  (* [comment removed for export] *)
  Local Ltac to_real K MU WM :=
    gsto 0x93de4%Z;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with STc : stk bsegs mm lo _, FRc : rw_cells bsegs mm (bv_unsigned sp + -112) _ |- _ =>
        eapply K; [exact MU| exact WM| assumption| | exact STc| exact FRc] end end;
    eapply vfi_cells_munch; [exact VC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia| cbn; lia].

  (* [comment removed for export] *)
  Lemma fprintf_icpt_prefix : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : machine_state -> Prop),
    pcommon_stmt fa ->
    fprintf_icpt_K a2 a3 a4 a5 a6 a7 Q ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 strm (Z_to_bv 64 fa) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFPRINTF_ICPT) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros PC K. unfold fprintf_icpt_K in K.
    (nelimp VC 3%nat; intros IC CF RL).
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP;
    pose proof CEIL as CE; unfold alloc_ceiling, sp_window_lo, stack_max_size in CE; unfold AFPI_STACK in SPB;
    pose proof (munch_refl [(bv_unsigned sp - AFPI_STACK, bv_unsigned sp)] m) as MU; pose proof (wmono_refl bsegs m) as WM;
    unfold AFPI_STACK in MU;
    pose proof IC as IC'; icpt_split IC';
    pose proof ST0 as ST; clear ST0;
    unfold AFPRINTF_ICPT;
    carve_frame 112%nat ST;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    do 16 gs;
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end;
    callsp try_init_ok;
    [ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end
    | assumption | eassumption | exact CEIL | lia | ];
    clear MU1;
    gsto 0x47278%Z; gs;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end;
    callsp try_init_ok;
    [ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end
    | assumption | eassumption | exact CEIL | lia | ];
    clear MU1;
    gsto 0x472a8%Z; gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SB1 : shbase_cells mm) by (eapply shbase_cells_munch; [exact (proj1 IC)| exact MU| cbn; lia| cbn; lia]);
      assert (LOW1 : lowsh_at mm) by (eapply lowsh_at_munch_stack; [exact LOW| exact MU| exact WM| lia]);
      pose proof (munch_refl [(bv_unsigned sp - 112 - 2272, bv_unsigned sp - 112)] mm) as MU2;
      lazymatch goal with STc : stk bsegs mm lo _ |- _ =>
        callsp PC; [ assumption | exact SB1 | exact LOW1 | exact STc | exact CEIL | unfold APC_STACK; lia | reflexivity | ] end end.
    clear MU2 SB1 LOW1.
    to_real K MU WM.
  Qed.

  (* [comment removed for export] *)
  Lemma fprintf_icpt_prefix_s : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (str slack : list byte) (Q : machine_state -> Prop),
    pcommon_s_stmt fa ->
    sh_zero m alloc_ceiling (2^47) ->
    bytes_at bsegs m (bv_unsigned a2) (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
    bv_unsigned sp <= bv_unsigned a2 -> bv_unsigned a2 + Z.of_nat (length str) + 1 + 16 <= 2^47 -> Z.of_nat (length str) <= 2^20 ->
    fprintf_icpt_K a2 a3 a4 a5 a6 a7 Q ->
    evt bsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 strm (Z_to_bv 64 fa) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFPRINTF_ICPT) fc None m (seg_rom bsegs)).
  Proof.
    intros until Q. intros PCS SZ BY NZ SA1 SA2 SA3 K. unfold fprintf_icpt_K in K.
    (nelimp VC 3%nat; intros IC CF RL).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP;
    pose proof CEIL as CE; unfold alloc_ceiling, sp_window_lo, stack_max_size in CE; unfold AFPI_STACK in SPB;
    pose proof (munch_refl [(bv_unsigned sp - AFPI_STACK, bv_unsigned sp)] m) as MU; pose proof (wmono_refl bsegs m) as WM;
    unfold AFPI_STACK in MU;
    pose proof IC as IC'; icpt_split IC';
    pose proof ST0 as ST; clear ST0;
    unfold AFPRINTF_ICPT;
    carve_frame 112%nat ST;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    do 16 gs;
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end;
    callsp try_init_ok;
    [ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end
    | assumption | eassumption | exact CEIL | lia | ];
    clear MU1;
    gsto 0x47278%Z; gs;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 112 - 16, bv_unsigned sp - 112)] mm) as MU1 end;
    callsp try_init_ok;
    [ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| eassumption| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end
    | assumption | eassumption | exact CEIL | lia | ];
    clear MU1;
    gsto 0x472a8%Z; gs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SB1 : shbase_cells mm) by (eapply shbase_cells_munch; [exact (proj1 IC)| exact MU| cbn; lia| cbn; lia]);
      assert (LOW1 : lowsh_at mm) by (eapply lowsh_at_munch_stack; [exact LOW| exact MU| exact WM| lia]);
      assert (IC1 : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]);
      assert (SZ1 : sh_zero mm alloc_ceiling (2^47)) by (eapply sh_zero_munch_stack; [exact SZ| exact MU| try rewrite alloc_ceiling_lit; lia| lia| apply Forall_cons; [cbn [fst]; try rewrite alloc_ceiling_lit; lia| apply Forall_nil]]);
      pose proof (munch_refl [(bv_unsigned sp - 112 - 2320, bv_unsigned sp - 112)] mm) as MU2;
      lazymatch goal with STc : stk bsegs mm lo _, FRc : rw_cells bsegs mm (bv_unsigned sp + -112) _ |- _ =>
        (* [comment removed for export] *)
        apply (proj1 (rw_cells_app bsegs _ _ [_; _; _; _; _; _; _; _] _)) in FRc;
        let FRv := fresh "FRv" in let FRw := fresh "FRw" in
        destruct FRc as [FRc FRv]; cbn [cells_size csize Nat.add app] in FRv;
        apply (proj1 (rw_cells_app bsegs _ _ [_] _)) in FRv; destruct FRv as [FRv FRw]; cbn [cells_size csize Nat.add app] in FRw;
        replace (bv_unsigned sp + -112 + Z.of_nat 64 + Z.of_nat 8) with (bv_unsigned sp + -40) in FRw by lia;
        replace (bv_unsigned sp + -112 + Z.of_nat 64) with (bv_unsigned sp + -48) in FRv by lia;
        callsp PCS; [ assumption | exact SB1 | exact LOW1 | exact IC1 | exact SZ1 | exact STc | exact CEIL | unfold APCS_STACK; lia | reflexivity | reflexivity
                    | rewrite Z_to_bv_bv_unsigned; exact FRv | lia | lia | exact BY | exact NZ | lia | exact SA2 | exact SA3 | ] end end.
    clear MU2 SB1 LOW1 IC1 SZ1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with FRc : rw_cells bsegs mm (bv_unsigned sp + -112) ?cs1, FRv : rw_cells bsegs mm (bv_unsigned sp + -48) ?cs2, FRw : rw_cells bsegs mm (bv_unsigned sp + -40) ?cs3 |- _ =>
        assert (FRall : rw_cells bsegs mm (bv_unsigned sp + -112) (cs1 ++ cs2 ++ cs3));
        [ apply (proj2 (rw_cells_app bsegs _ _ _ _)); split; [exact FRc|]; cbn [cells_size csize Nat.add app];
          apply (proj2 (rw_cells_app bsegs _ _ [_] _)); split;
          [ eapply rwc_eq; [exact FRv| cbn; lia] | cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FRw| cbn; lia] ]
        | cbn [app] in FRall; clear FRc FRv FRw; rename FRall into FRc ] end end.
    to_real K MU WM.
  Qed.

  (* [comment removed for export] *)
  Lemma fprintf_icpt_epilogue : forall (xra x8 x9 x18 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c1 c2 c3 v2 v3 v4 v5 v6 v7 : word) (u : list byte)
      (F' : bvmap 5 word) (fc' : bv 32) (m2 : word -> option byte) (Q : machine_state -> Prop),
    mem_inv bsegs m2 ->
    stk bsegs m2 lo (bv_unsigned sp + -112) ->
    rw_cells bsegs m2 (bv_unsigned sp + -112) [CB 8 u; C8 c1; C8 c2; C8 c3; C8 s2; C8 s1; C8 s0; C8 ra; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7] ->
    (stk bsegs m2 lo (bv_unsigned sp) ->
     evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F' (ret_pc ra) fc' None m2 (seg_rom bsegs))) ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F' (Z_to_bv 64 AFPRINTF_RET) fc' None m2 (seg_rom bsegs)).
  Proof.
    intros until Q. intros MI2 ST2 FR2 K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold AFPI_STACK in SPB.
    unfold AFPRINTF_RET.
    do 6 gs.
    release_frame FR2 ST2 (bv_unsigned sp).
    try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia; rewrite (Z_to_bv_bv_unsigned sp)).
    apply K. exact ST2.
  Qed.
End FprintfIcpt.


End CeilWrap.
