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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloatProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_sn_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_vsprintf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module ICPT_sprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_printf_core.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_sn_write OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.Printf_sn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsnprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsnprintf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_d OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_g15 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_g17 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ASPRINTF_ICPT : Z := 0x472d8.
Definition ASPI_STACK : Z := 10304.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition asprintf_gen_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in let D := bv_unsigned a0 in
    a1 = Z_to_bv 64 A ->
    rw_cells asegs m D [CB dn junkd] ->
    bytes_at asegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    Forall no_s args -> args_ok 0 0 0 m lo q 0 [a2; a3; a4; a5; a6; a7] args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat ->
    stk asegs m lo q -> (lo <= q - ASPI_STACK) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    MRT m -> vspi_cells m -> lowsh_at m -> pcommon_stmt A ->
    (alloc_ceiling <= lo) -> (q + 64 <= 2^47 - 1) ->
    (0 < zlength fmt) -> shadow_ok m A (zlength fmt) -> app_range A (zlength fmt) ->
    app_range D (Z.of_nat dn) -> mrt_iv_ok (D, D + Z.of_nat dn) -> shadow_ok m D (Z.of_nat dn) ->
    (0 <= r) -> (r + 1 <= Z.of_nat dn) -> (Z.of_nat dn < 2^31) ->
    evt asegs (vsnprintf_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ASPRINTF_T) fc None m (seg_rom asegs)).

Theorem asprintf_gen_ok : asprintf_gen_stmt.
Proof.
  unfold asprintf_gen_stmt. intros until o. cbv zeta.
  intros -> DST BY HF P1 NOS AOK MODEL FPF ROOM ST LO GLO QHI SSP MI FRM HA0 HA DD1 GD.
  intros MR VSC LOW PC CEIL Q47 FNZ FSO FAR ARD MID SOD R0 R1 DN31.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold ASPI_STACK in LO.
  unfold GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  set (D := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 D) by (unfold D; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (app_range_lt47 _ _ ARD) as RB.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (WAPP : Forall app_iv [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_of_range; exact ARD| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [exact MID| apply Forall_nil]. }
  pose proof VSC as [[[IC [CF RLV]] RLN] RL]. pose proof IC as IC'. icpt_split IC'.
  unfold ASPRINTF_T.
  zstep.                                  (* [comment removed for export] *)
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 14 gs.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(bv_unsigned sp - 80 - 16, bv_unsigned sp - 80)] mm) as MU1 end.
  gs. callsp try_init_ok.
  1:{ lazymatch goal with |- icpt_cells ?mm => eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil] end. }
  1:{ assumption. } 1:{ eassumption. } 1:{ exact CEIL. } 1:{ lia. }
  clear MU1.
  gsto 0x47324%Z.
  (* [comment removed for export] *)
  gs.
  name_spq (bv_unsigned sp + -80)%Z.
  lazymatch goal with FRc : rw_cells asegs ?mm (bv_unsigned sp + -80) [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] |- _ =>
    apply (proj1 (rw_cells_app asegs _ _ [c0; c1; c2; c3] _)) in FRc; destruct FRc as [FR4 VAC]; cbn [cells_size csize Nat.add app] in VAC;
    replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in VAC by lia
  end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA; cbn [cells_bytes cbytes] in VAA;
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA;
    assert (MR2 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (VSC2 : vspi_cells mm) by (eapply vspi_cells_munch; [exact VSC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil| cbn; lia| cbn; lia]);
    assert (LOW2 : lowsh_at mm) by (eapply lowsh_at_munch; [exact LOW| exact MU| exact WM|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_HI; lia|];
       apply Forall_cons; [cbn [fst snd]; unfold SH, SHADOW_OFFSET, AIMG_LO, AIMG_HI; destruct ARD as [ARD'|ARD']; unfold lowmem_range, highmem_range, KHIGHMEM_BEG, KLOWSHADOW_BEG in ARD'; lia| apply Forall_nil]);
    assert (FSO2 : shadow_ok mm A (Z.of_nat (length fmt))) by (eapply shadow_ok_munch_app; [exact FSO| exact MU| lia| exact FAR| exact WAPP]);
    assert (SOD2 : shadow_ok mm D (Z.of_nat dn)) by (eapply shadow_ok_munch_app; [exact SOD| exact MU| lia| exact ARD| exact WAPP]);
    assert (SSP2 : ssp_cells mm canary) by (destruct SSP as [SS1 SS2]; split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia]))
  end.
  lazymatch goal with STc : stk asegs _ lo (bv_unsigned sp + -80) |- _ => rename STc into ST1 end.
  pose proof vsprintf_icpt_ok as VS. unfold vsprintf_icpt_stmt, AVSPRINTF_ICPT in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (A := A) (VA := bv_unsigned sp + -48) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args)
                   (lo := lo) (canary := canary) (r := r) (o := o);
      clear VS; rewrite ?unsigned_lit by lia; unfold AVSPI_STACK, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity.
    all: try lia.
    all: first [ exact BY | exact HF | exact P1 | exact VAA | exact NOS | eapply args_ok_nos; [exact NOS | exact AOK]
               | exact MODEL | exact FPF | rewrite Hsp; exact ST1 | exact SSP2 | assumption | exact FRM | exact MR2 | exact VSC2 | exact LOW2 | exact PC | exact CEIL | exact FSO2 | exact FAR | exact ARD | exact MID | exact SOD2
               | match goal with |- ?G => idtac "VS-REMAINING" G end ]. }
  cbv beta. intros ms' P. clear VS.
  unfold vsnprintf_icpt_post in P. rewrite ?Hsp in P.
  (nelim P 26%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call asegs mm m3 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 291624)) with (Z_to_bv 64 291624 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  subst sp0. clear Hsp MR2 VSC2 LOW2 FSO2 SOD2 SSP2.
  (* [comment removed for export] *)
  do 5 gs.
  lazymatch goal with FRa : rw_cells asegs m3 (bv_unsigned sp + -80) _, FRb : rw_cells asegs m3 (bv_unsigned sp + -48) _ |- _ =>
    assert (FALL : rw_cells asegs m3 (bv_unsigned sp + -80) ([C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 s1; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]));
    [ apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRa|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FRb | lia]
    | clear FRa FRb ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  try (replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia); try rewrite (Z_to_bv_bv_unsigned sp).
  apply evt_done. unfold vsnprintf_icpt_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|]. split; [exact SSP3|]. exact DST3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at asegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma fmt_d_ret : forall i o r, -2^31 <= i < 2^31 -> fmt_d i = Some (o, r) -> r = zlength o.
Proof.
  intros i o r Hi E.
  destruct (Z.eq_dec i 0) as [->|NZ]. { vm_compute in E. inversion E; subst. reflexivity. }
  destruct (Z_lt_le_dec i 0).
  - rewrite fmt_d_neg in E by lia. inversion E; subst. unfold zlength. cbn [length]. lia.
  - rewrite fmt_d_pos in E by lia. inversion E; subst. reflexivity.
Qed.

Lemma fmt_g_ret : forall d prec o r, FMT_G_RET -> (prec = 15 \/ prec = 17) -> fmt_g d prec = Some (o, r) -> r = zlength o.
Proof.
  intros d prec o r RET Hp E. unfold fmt_g in E.
  destruct (fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g) as [[o1 l]|] eqn:F; [|discriminate].
  pose proof (RET _ _ _ _ Hp F) as Hl. pose proof (zlength_nonneg o1).
  inversion E; subst. replace (zlength o <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac pre_split PRE := (nelim PRE 13%nat; intros FC MR LOW MI FRM SSP ST CEIL LO Q47 DD1 HR SOD);
  (nelimp FC 6%nat; intros IC CF RVS RLN RLV _).

Theorem asprintf_d_ok : asprintf_d_stmt.
Proof.
  unfold asprintf_d_stmt. intros until r. intros DST Ha0 Ha1 Hi Hir FD ROOM DN PRE FSO. pre_split PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in HR'.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (fmt_d_ret i o r Hir FD) as Hr. pose proof (zlength_nonneg o) as Ho. unfold zlength in Hr, Ho.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) o) with (zb o).
  eapply SG with (fmt := FMT_d) (args := [PA_i i]) (A := A_FMT_d); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | exact pcommon_d_ok
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_d; lia | vm_compute; discriminate]
          | unfold FMT_d; forall_range
          | apply pass1_ok_d
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [exact Hir | exact Hi] | exact I]
          | apply printf_sn_d; [exact Hir | exact FD]
          | rewrite fp_calls_d; apply Forall_nil
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | right; exact HR
          | apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia
          | left; unfold lowmem_range, A_FMT_d, FMT_d, zlength, KLOWSHADOW_BEG; cbn; lia
          | unfold A_FMT_d, GLOBALS_TOP, STATIC_SPLIT, FMT_d, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.

Theorem asprintf_g_ok : forall prec, asprintf_g_stmt prec.
Proof.
  intros prec. unfold asprintf_g_stmt. intros until r. intros RET LEN DST Ha0 Ha1 Hp FG FACTS ROOM DN PRE FSO. pre_split PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in HR'.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (fmt_g_ret _ prec o r RET Hp FG) as Hr. pose proof (zlength_nonneg o) as Ho. unfold zlength in Hr, Ho.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) o) with (zb o).
  eapply SG with (fmt := if prec =? 15 then FMT_g15 else FMT_g17) (args := [PA_g (bv_unsigned a2)]) (A := if prec =? 15 then A_FMT_g15 else A_FMT_g17); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; [exact pcommon_g15_ok | exact pcommon_g17_ok]
          | destruct Hp as [-> | ->]; exact FSO
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; (apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_g15, A_FMT_g17; lia | vm_compute; discriminate])
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold FMT_g15, FMT_g17; forall_range
          | apply pass1_ok_g
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [reflexivity | exact I]
          | apply printf_sn_g; assumption
          | rewrite fp_calls_g by exact Hp; apply Forall_cons; [exact FACTS | apply Forall_nil]
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | right; exact HR
          | apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; left; unfold lowmem_range, A_FMT_g15, A_FMT_g17, FMT_g15, FMT_g17, zlength, KLOWSHADOW_BEG; cbn; lia
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold A_FMT_g15, A_FMT_g17, GLOBALS_TOP, STATIC_SPLIT, FMT_g15, FMT_g17, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.

Theorem asprintf_u04x_ok : asprintf_u04x_stmt.
Proof.
  unfold asprintf_u04x_stmt. intros until c. intros DST Ha0 Ha1 Hc Hcr Hn6 DN PRE FSO. pre_split PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END in HR'.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) (117 :: hex4_lower c)) with (zb (117 :: hex4_lower c)).
  eapply SG with (fmt := FMT_u04x) (args := [PA_u c]) (A := A_FMT_u04x); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | exact pcommon_u04x_ok
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_u04x; lia | vm_compute; discriminate]
          | unfold FMT_u04x; forall_range
          | apply pass1_ok_u04x
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [lia | exact Hc] | exact I]
          | apply printf_sn_u04x; exact Hcr
          | rewrite fp_calls_u04x; apply Forall_nil
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | right; exact HR
          | apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia
          | left; unfold lowmem_range, A_FMT_u04x, FMT_u04x, zlength, KLOWSHADOW_BEG; cbn; lia
          | unfold A_FMT_u04x, GLOBALS_TOP, STATIC_SPLIT, FMT_u04x, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | unfold hex4_lower; cbn [length]; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Ltac pre_split PRE := (nelim PRE 13%nat; intros FC MR LOW MI FRM SSP ST CEIL LO Q47 DD1 HR SOD);
  (nelimp FC 6%nat; intros IC CF RVS RLN RLV _).
End ICPT_sprintf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs RT_data CJ_iface AShadow ICPT_iface RT_poison RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat SoftFloatProps FmtFp Stdio StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas Printf_model Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_pop_arg Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_printf_core.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcleaf ICPT_pcdefs ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_sn_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_vsnprintf.Printf_sn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_vsprintf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_vsprintf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsnprintf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_vsprintf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_vsprintf2.ICPT_vsprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_vsprintf2.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_d.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_g15.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcommon_g17.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcommon_x ICPT_fmt_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope. Open Scope Z_scope. Open Scope mspec_scope.
Import ICPT_sprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fmt_glue.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fmt_glue.ICPT_fmt_iface2.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

(* [comment removed for export] *)
Ltac pre_split_b PRE := destruct PRE as (FC & MR & LOW & MI & FRM & SSP & ST & CEIL & LO & Q47 & DD1 & (HLO & HR) & SOD);
  pose proof FC as (IC & CF & RVS & RLN & RLV & _).

Theorem asprintf_d_ok_b : asprintf_d_stmt_b.
Proof.
  unfold asprintf_d_stmt_b. intros until r. intros DST Ha0 Ha1 Hi Hir FD ROOM DN PRE FSO. pre_split_b PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold app_range, lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in HR'. unfold AIMG_HI in HLO.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (fmt_d_ret i o r Hir FD) as Hr. pose proof (zlength_nonneg o) as Ho. unfold zlength in Hr, Ho.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) o) with (zb o).
  eapply SG with (fmt := FMT_d) (args := [PA_i i]) (A := A_FMT_d); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | exact pcommon_d_ok
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_d; lia | vm_compute; discriminate]
          | unfold FMT_d; forall_range
          | apply pass1_ok_d
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [exact Hir | exact Hi] | exact I]
          | apply printf_sn_d; [exact Hir | exact FD]
          | rewrite fp_calls_d; apply Forall_nil
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | exact HR
          | destruct HR' as [HRl|HRh]; [apply mrt_iv_ok_mid; lia| apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia]
          | left; unfold lowmem_range, A_FMT_d, FMT_d, zlength, KLOWSHADOW_BEG; cbn; lia
          | unfold A_FMT_d, GLOBALS_TOP, STATIC_SPLIT, FMT_d, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.

Theorem asprintf_g_ok_b : forall prec, asprintf_g_stmt_b prec.
Proof.
  intros prec. unfold asprintf_g_stmt_b. intros until r. intros RET LEN DST Ha0 Ha1 Hp FG FACTS ROOM DN PRE FSO. pre_split_b PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold app_range, lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in HR'. unfold AIMG_HI in HLO.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof (fmt_g_ret _ prec o r RET Hp FG) as Hr. pose proof (zlength_nonneg o) as Ho. unfold zlength in Hr, Ho.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) o) with (zb o).
  eapply SG with (fmt := if prec =? 15 then FMT_g15 else FMT_g17) (args := [PA_g (bv_unsigned a2)]) (A := if prec =? 15 then A_FMT_g15 else A_FMT_g17); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; [exact pcommon_g15_ok | exact pcommon_g17_ok]
          | destruct Hp as [-> | ->]; exact FSO
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; (apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_g15, A_FMT_g17; lia | vm_compute; discriminate])
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold FMT_g15, FMT_g17; forall_range
          | apply pass1_ok_g
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [reflexivity | exact I]
          | apply printf_sn_g; assumption
          | rewrite fp_calls_g by exact Hp; apply Forall_cons; [exact FACTS | apply Forall_nil]
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | exact HR
          | destruct HR' as [HRl|HRh]; [apply mrt_iv_ok_mid; lia| apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia]
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; left; unfold lowmem_range, A_FMT_g15, A_FMT_g17, FMT_g15, FMT_g17, zlength, KLOWSHADOW_BEG; cbn; lia
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold A_FMT_g15, A_FMT_g17, GLOBALS_TOP, STATIC_SPLIT, FMT_g15, FMT_g17, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.

Theorem asprintf_u04x_ok_b : asprintf_u04x_stmt_b.
Proof.
  unfold asprintf_u04x_stmt_b. intros until c. intros DST Ha0 Ha1 Hc Hcr Hn6 DN PRE FSO. pre_split_b PRE.
  unfold AFMT_STACK in LO. pose proof HR as HR'. unfold app_range, lowmem_range, highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, KLOWSHADOW_BEG in HR'. unfold AIMG_HI in HLO.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  assert (HD : bv_unsigned a0 = D) by (subst a0; apply unsigned_lit; lia). subst D.
  pose proof asprintf_gen_ok as SG. unfold asprintf_gen_stmt in SG. cbv zeta in SG.
  unfold asprintf_post. change (map (Z_to_bv 8) (117 :: hex4_lower c)) with (zb (117 :: hex4_lower c)).
  eapply SG with (fmt := FMT_u04x) (args := [PA_u c]) (A := A_FMT_u04x); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM | exact MR | exact LOW | exact SOD | exact FSO
          | exact pcommon_u04x_ok
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_u04x; lia | vm_compute; discriminate]
          | unfold FMT_u04x; forall_range
          | apply pass1_ok_u04x
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [lia | exact Hc] | exact I]
          | apply printf_sn_u04x; exact Hcr
          | rewrite fp_calls_u04x; apply Forall_nil
          | exact (conj (conj (conj IC (conj CF RLV)) RLN) RVS)
          | exact HR
          | destruct HR' as [HRl|HRh]; [apply mrt_iv_ok_mid; lia| apply mrt_iv_ok_high; unfold KHIGHMEM_BEG; lia]
          | left; unfold lowmem_range, A_FMT_u04x, FMT_u04x, zlength, KLOWSHADOW_BEG; cbn; lia
          | unfold A_FMT_u04x, GLOBALS_TOP, STATIC_SPLIT, FMT_u04x, zlength; cbn; lia
          | unfold ASPI_STACK, GLOBALS_TOP; lia
          | unfold hex4_lower; cbn [length]; lia
          | lia
          | match goal with |- ?G => idtac "SG-REMAINING" G end ].
Qed.

End CeilWrap.
