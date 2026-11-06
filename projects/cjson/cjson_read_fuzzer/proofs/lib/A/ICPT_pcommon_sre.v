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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes Image ZBridge.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_pcleaf ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcommon_x.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcommon_x.ICPT_pcdefs2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_istrlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_pcsdefs.
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
Lemma fmt_sre_bytes : forall m, mem_inv asegs m ->
  ro_cells asegs m 0x1d7ac [CB 23 (zbs [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0])].
Proof.
  intros m MI. apply (ro_cells_image asegs m 0x1d7ac (zbs [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 37; 115; 10; 0]) MI);
    [vm_compute; reflexivity| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
Ltac pcs_iter1 :=
  pc_dir5;
  gsto 0x461c4%Z; gs;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) _ |- _ =>
    apply (rw_cells_merge asegs _ _ [] [_; _; _; _; _] []) in FBd; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FBd;
    call imemset_call;
    [ exact FBd | assumption | lia | lia | lia | lia
    | intros E; rewrite Z.land_lor_distr_l in E; apply Z.lor_eq_0_iff in E; destruct E as [E _]; vm_compute in E; lia | ]
  end;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) [CB _ (repeat _ _)] |- _ =>
    change (0 mod 256) with 0 in FBd; change (Z.to_nat 40) with 40%nat in FBd; cbn [repeat] in FBd;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FBd; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FBd
  end;
  gs;
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) [?c0; ?c1; C8 ?v; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] |- _ =>
    apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) _ [c0; c1; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) in FBd;
    [| cbn; repeat split; exact I | apply bytes_eqb_sound; vm_compute; reflexivity] end;
  gsto3 0x4652c%Z 0x495c0%Z 0x46978%Z.

(* [comment removed for export] *)
Ltac pcs_rest :=
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

Section Pcommon_sre.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (lo VA S : Z) (str slack : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis SB : shbase_cells m.
  Hypothesis LOW : lowsh_at m.
  Hypothesis IC : icpt_cells m.
  Hypothesis SZ : sh_zero m alloc_ceiling (2^47).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + APCS_STACK <= bv_unsigned sp.
  Hypothesis VAC : rw_cells asegs m VA [C8 (Z_to_bv 64 S)].
  Hypothesis VA1 : bv_unsigned sp <= VA.
  Hypothesis VA2 : VA + 8 <= 2^47.
  Hypothesis BY : bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NZ : ~ In (Z_to_bv 8 0) str.
  Hypothesis S1 : bv_unsigned sp <= S.
  Hypothesis S2 : S + Z.of_nat (length str) + 1 + 16 <= 2^47.
  Hypothesis S3 : Z.of_nat (length str) <= 2^20.

  Lemma pcommon_sre_body :
    evt asegs (pcommons_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0x1d7ac) (Z_to_bv 64 VA) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APRINTF_COMMON) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
    pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. unfold APCS_STACK in SPB.
    pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (tbl_flags m MI) as T1. pose proof (tbl_lenmod m MI) as T2. pose proof (tbl_cs m MI) as T3.
    pose proof (tbl_iconv m MI) as T4. pose proof (tbl_fconv m MI) as T5. pose proof (tbl_aa m MI) as T6. pose proof (tbl_atoll m MI) as T7.
    pose proof (fmt_sre_bytes m MI) as FMT.
    pose proof (lowsh_word8 m 0x7fffbaf0 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW1. lowsh_eval SHW1.
    pose proof (lowsh_word8 m 0x7fffbaf8 LOW ltac:(unfold SH, SHADOW_OFFSET, AIMG_LO; lia) ltac:(unfold SH, SHADOW_OFFSET, AIMG_HI; lia)) as SHW2. lowsh_eval SHW2.
    pose proof SB as SB'. shbase_split SB'.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    unfold APRINTF_COMMON.
    pose proof ST0 as ST. clear ST0. carve_frame 104%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2176) (bv_unsigned sp + -104) ST ltac:(lia)) as [STa STb]. clear ST.
    carve_frame 64%nat STa. rename FR0 into FB.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] _)) in FB. destruct FB as [FBa FBd]. cbn [cells_size csize Nat.add app] in FBd.
    replace (bv_unsigned sp + -2240 + Z.of_nat 24) with (bv_unsigned sp + -2216) in FBd by lia.
    (* [comment removed for export] *)
    do 16 gs.
    gsto 0x46124%Z.
    shw_read SHW1. shw_read SHW2.
    gs. gs.
    repeat match goal with RD : ov_read_bytes _ _ _ _ = Some _ |- _ => clear RD end.
    gsto3 0x461a0%Z 0x46978%Z 0x46978%Z.
    (* [comment removed for export] *)
    pcs_iter1.
    (* [comment removed for export] *)
    gs. gs. zstep. if_cases Knull; zify_cond Knull. { exfalso. revert Knull. rewrite ?unsigned_lit by lia. lia. }
    clear Knull.
    gsto 0x465b4%Z.
    zstep.
    eapply evt_cut. { eapply istrlen_spec; [exact BY| exact NZ| lia]. }
    cbv beta. intros ms' ->.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kov; zify_cond Kov.
    { exfalso. revert Kov. rewrite ?unsigned_lit by lia. rewrite zb_lxor_ones by lia. clear -S1 S2 RSP. intros Kov. lia. }
    clear Kov.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kbig; zify_cond Kbig.
    - (* [comment removed for export] *)
      assert (HL : 64 <= Z.of_nat (length str)) by (revert Kbig S3; clear; intros Kbig S3; Z.div_mod_to_equations; lia). clear Kbig.
      zstep. if_cases Kz; zify_cond Kz. 2:{ exfalso. revert Kz. rewrite ?unsigned_lit by lia. lia. }
      clear Kz. gs. gs. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (ICc : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]);
        assert (SZc : sh_zero mm alloc_ceiling (2^47)) by (eapply sh_zero_munch_stack; [exact SZ| exact MU| try rewrite alloc_ceiling_lit; lia| lia| apply Forall_cons; [cbn [fst]; try rewrite alloc_ceiling_lit; lia| apply Forall_nil]]);
        pose proof (munch_refl [(bv_unsigned sp - 2240 - 80, bv_unsigned sp - 2240)] mm) as MU1
      end.
      lazymatch goal with STa : stk asegs _ lo (bv_unsigned sp + -2240) |- _ =>
      callsp region_is_poisoned_ok;
        [ exact ICc | assumption | exact STa | exact CEIL | lia | reflexivity | reflexivity | lia
        | right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END; lia
        | eapply sh_zero_shadow_ok64; [exact SZc| (try rewrite alloc_ceiling_lit; lia)| reflexivity| try rewrite alloc_ceiling_lit; lia| lia| lia| lia]
        | ] end.
      clear MU1 ICc SZc.
      pc_is.
      gs. pc_is.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with MIc : mem_inv asegs mm |- _ =>
          first [ lazymatch type of FMT with ro_cells _ mm _ _ => idtac "FMT-transported" end
                | idtac "FMT-repose"; clear T1 T2 T3 T4 T5 T6 T7 FMT;
                  pose proof (tbl_flags mm MIc) as T1; pose proof (tbl_lenmod mm MIc) as T2; pose proof (tbl_cs mm MIc) as T3;
                  pose proof (tbl_iconv mm MIc) as T4; pose proof (tbl_fconv mm MIc) as T5; pose proof (tbl_aa mm MIc) as T6; pose proof (tbl_atoll mm MIc) as T7;
                  pose proof (fmt_sre_bytes mm MIc) as FMT ] end end.
      pcs_rest.
    - (* [comment removed for export] *)
      assert (HL : Z.of_nat (length str) <= 63) by (revert Kbig S3; clear; intros Kbig S3; Z.div_mod_to_equations; lia). clear Kbig.
      do 9 gs.
      rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
      zstep. zstep. rewrite !land_m8 by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SZc : sh_zero mm alloc_ceiling (2^47)) by (eapply sh_zero_munch_stack; [exact SZ| exact MU| try rewrite alloc_ceiling_lit; lia| lia| apply Forall_cons; [cbn [fst]; try rewrite alloc_ceiling_lit; lia| apply Forall_nil]]);
        pose proof (sh_zero_read8 mm alloc_ceiling (2^47) ((2147450880 + S / 8) / 8 * 8) SZc alloc_ceiling_mod8 ltac:(try rewrite alloc_ceiling_lit; lia) ltac:(lia)
                      ltac:(try rewrite alloc_ceiling_lit; unfold SH, SHADOW_OFFSET; clear -S1 CE SPB; Z.div_mod_to_equations; lia)
                      ltac:(unfold SH, SHADOW_OFFSET; clear -S2 S1 RSP; Z.div_mod_to_equations; lia)) as RD1;
        pose proof (sh_zero_read8 mm alloc_ceiling (2^47) ((2147450880 + (S + (Z.of_nat (length str) + 1) + -1) / 8) / 8 * 8) SZc alloc_ceiling_mod8 ltac:(try rewrite alloc_ceiling_lit; lia) ltac:(lia)
                      ltac:(try rewrite alloc_ceiling_lit; unfold SH, SHADOW_OFFSET; clear -S1 CE SPB; Z.div_mod_to_equations; lia)
                      ltac:(unfold SH, SHADOW_OFFSET; clear -S2 S1 RSP; Z.div_mod_to_equations; lia)) as RD2;
        unfold wa in RD1, RD2
      end.
      step. step. clear RD1 RD2 SZc.
      pc_is.
      gs. gs. pc_is.
      pcs_rest.
  Qed.

End Pcommon_sre.

Lemma pcommon_sre_ok : pcommon_s_stmt 0x1d7ac.
Proof.
  unfold pcommon_s_stmt. intros until slack. intros MI SB LOW IC SZ ST CEIL SPB -> -> VAC VA1 VA2 BY NZ S1 S2 S3.
  eapply pcommon_sre_body; eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac pcs_iter1 :=
  pc_dir5;
  gsto 0x461c4%Z; gs;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) _ |- _ =>
    apply (rw_cells_merge asegs _ _ [] [_; _; _; _; _] []) in FBd; cbn [cells_size csize cells_bytes cbytes app Nat.add] in FBd;
    call imemset_call;
    [ exact FBd | assumption | lia | lia | lia | lia
    | intros E; rewrite Z.land_lor_distr_l in E; apply Z.lor_eq_0_iff in E; destruct E as [E _]; vm_compute in E; lia | ]
  end;
  lazymatch goal with FBd : rw_cells asegs _ (bv_unsigned ?u + -2216) [CB _ (repeat _ _)] |- _ =>
    change (0 mod 256) with 0 in FBd; change (Z.to_nat 40) with 40%nat in FBd; cbn [repeat] in FBd;
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [4; 4; 8; 8; 8; 1; 1; 1; 1; 1; 1; 1; 1]%nat) in FBd; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FBd
  end;
  gs;
  lazymatch goal with FBd : rw_cells asegs ?mm (bv_unsigned ?u + -2216) [?c0; ?c1; C8 ?v; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] |- _ =>
    apply (rw_cells_recast asegs mm (bv_unsigned u + -2216) _ [c0; c1; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295); c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) in FBd;
    [| cbn; repeat split; exact I | apply bytes_eqb_sound; vm_compute; reflexivity] end;
  gsto3 0x4652c%Z 0x495c0%Z 0x46978%Z.
Ltac pcs_rest :=
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
