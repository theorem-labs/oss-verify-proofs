(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs Sj_stage1_tail Sj_stage1_top Sj_stage1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition s1z_post (E : s1env) (code : Z) (out : list Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m' : mem) (ws' : list word) (nxt' : word),
    ms' = MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E) (wz code) a1 a2 a3 a4 a5 a6 a7
                  (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
             (e_F E) (ret_pc (e_ra E)) (e_fc E) None m' (seg_rom usegs)
    /\ munch (u1_W E) (e_m0 E) m' /\ wmono usegs (e_m0 E) m' /\ mem_inv usegs m'
    /\ stk usegs m' (e_lo E) (bv_unsigned (e_sp E))
    /\ rw_cells usegs m' (e_THIS E) (parser_cells E (wz (Z.of_nat (length out))) nxt' (wz (e_BUF E)) (wz (e_len E)))
    /\ (code <> 13%Z -> nxt' = wz 0)
    /\ u32arr usegs m' (e_IDX E) ws' /\ length ws' = e_cap E
    /\ firstn (length out + 3) ws' = map wz (out ++ [e_len E; e_len E; 0%Z]).

Record env_okzu (E : s1env) : Prop := mkEnvOkzu {
  okz_nil : e_bs E = [];
  okz_glo : (U1_GTOP <= e_lo E)%Z;
  okz_room : (e_lo E + U1_STACK <= bv_unsigned (e_sp E))%Z;
  okz_this : (0 <= e_THIS E /\ e_THIS E + 96 <= e_lo E)%Z;
  okz_idx : (0 < e_IDX E /\ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_lo E)%Z;
  okz_cap : (3 <= Z.of_nat (e_cap E))%Z;
  okz_this_idx : (e_THIS E + 96 <= e_IDX E \/ e_IDX E + 4 * Z.of_nat (e_cap E) <= e_THIS E)%Z;
  okz_align : (e_IDX E mod 4 = 0)%Z
}.

Section S1Z.
  Variable E : s1env.
  Hypothesis OK : env_okzu E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Theorem s1z_spec : forall t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 (nsi nxt bufo leno : word) (ws0 : list word),
    mem_inv usegs (e_m0 E) ->
    stk usegs (e_m0 E) (e_lo E) (bv_unsigned (e_sp E)) ->
    rw_cells usegs (e_m0 E) (e_THIS E) (parser_cells E nsi nxt bufo leno) ->
    u32arr usegs (e_m0 E) (e_IDX E) ws0 -> length ws0 = e_cap E ->
    evt usegs (s1z_post E 13 [])
      (MS (mkR (e_ra E) (e_sp E) (e_gp E) (e_tp E) t0 t1 t2 (e_s0 E) (e_s1 E)
               (Z_to_bv 64 (e_THIS E)) (Z_to_bv 64 (e_BUF E)) (Z_to_bv 64 len) (Z_to_bv 64 0) a4 a5 a6 a7
               (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3 t4 t5 t6)
          (e_F E) (Z_to_bv 64 U1_ENTRY) (e_fc E) None (e_m0 E) (seg_rom usegs)).
  Proof using OK.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 nsi nxt bufo leno ws0 MI ST PARSER IDXA IDXL.
    pose proof OK as OK'.
    destruct OK' as [NIL GLO ROOM [TH0 TH1] [IX0 IX1] CAPOK S_TI ALIGN].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP, U1_ENTRY in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (LZ : len = 0%Z) by (rewrite NIL; reflexivity).
    assert (LO0 : (0 <= e_lo E)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl (u1_W E) (e_m0 E)) as MU. pose proof (wmono_refl usegs (e_m0 E)) as WM.
    unfold s1_W_g in MU. cbn [Z.opp] in MU. unfold parser_cells in PARSER.
    set (m := e_m0 E) in MI, ST, PARSER, IDXA, MU at 2, WM at 2 |- *.
    clearbody m.
    step.
    carve_frame 432%nat ST.
    apply (rw_cells_split_CB usegs m _ [] 432 junk [] [8;8;8;8;256;8;8;8;4;4;4;4;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 13 step. do 4 step. step. step. do 6 step.

    change [CB 8 j; CB 8 j0; CB 8 j1; CB 8 j2; CB 256 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 4 j7; CB 4 j8; CB 4 j9; CB 4 j10;
            C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
            C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]
      with ([CB 8 j; CB 8 j0; CB 8 j1; CB 8 j2] ++ [CB 256 j3] ++ [CB 8 j4; CB 8 j5; CB 8 j6; CB 4 j7; CB 4 j8; CB 4 j9; CB 4 j10;
            C8 (e_s11 E); C8 (e_s10 E); C8 (e_s9 E); C8 (e_s8 E); C8 (e_s7 E); C8 (e_s6 E); C8 (e_s5 E); C8 (e_s4 E);
            C8 (e_s3 E); C8 (e_s2 E); C8 (e_s1 E); C8 (e_s0 E); C8 (e_ra E)]) in FR.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FRtb FRhi].
    cbn [cells_size csize Nat.add] in FRtb, FRhi.
    replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in * by lia.
    pose proof (utable_at _ MI) as TB. unfold U1_TABLE in TB.
    pose proof umemcpy_stmt_holds as HM. unfold umemcpy_stmt, memcpy_stmt_g in HM.
    eapply evt_cut.
    { eapply HM with (src := TABLE_BYTES) (junk := j3); rewrite ?unsigned_lit by lia;
      [ exact TB | reflexivity | exact FRtb | lia | exact MI ]. }
    cbv beta. intros ms' P. unfold memcpy_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m3 & -> & MUc & WMc & MIc & DSTc & SRCc).
    rewrite !unsigned_lit in MUc, DSTc by lia. change (bv_unsigned (Z_to_bv 64 256)) with 256%Z in *. change (Z.to_nat 256) with 256%nat in DSTc.
    clear TB SRCc.
    transport_after_call usegs m0 m3 MUc WMc.
    clear MUc WMc MI HM. clear m0.
    replace (ret_pc (Z_to_bv 64 268948)) with (Z_to_bv 64 268948) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zstep. zstep. s1norm. do 7 zstep. zstep.
    rewrite LZ in *. if_true.

    zstep. zstep. zstep. unfold wz.

    pose proof (align4_ok (e_IDX E) 0 ALIGN ltac:(lia)) as AL. rewrite Z.mul_0_r, Z.add_0_r in AL.
    zstep. if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. rewrite AL. zstep. if_true. zstep.
    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) ws0 0 (wa (e_IDX E)) IDXA ltac:(lia) ltac:(f_equal; lia)) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write usegs mm (e_IDX E) ws0 0 (Z_to_bv 64 0) IDXA ltac:(lia)) as IDXA1;
      replace (e_IDX E + 4 * 0)%Z with (e_IDX E) in IDXA1 by lia end.
    store_done.
    zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
    zstep. if_cases G3; zify_cond G3; [|exfalso; lia].
    zstep. zstep.

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) _ 1 (wa (e_IDX E + 4)) IDXA1 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOK).
    step. unfold wz. rewrite (sx32_small 0) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write usegs mm (e_IDX E) _ 1 (Z_to_bv 64 0) IDXA1 ltac:(rewrite upd_length; lia)) as IDXA2;
      replace (e_IDX E + 4 * 1)%Z with (e_IDX E + 4)%Z in IDXA2 by lia end.
    store_done.
    zstep. if_cases G4; zify_cond G4; [|exfalso; lia].

    s1_cur_mem ltac:(fun m => pose proof (u32arr_store_ok usegs m (e_IDX E) _ 2 (wa (e_IDX E + 8)) IDXA2 ltac:(rewrite !upd_length; lia) ltac:(f_equal; lia)) as SOK).
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u32arr_write usegs mm (e_IDX E) _ 2 (Z_to_bv 64 0) IDXA2 ltac:(rewrite !upd_length; lia)) as IDXA3;
      replace (e_IDX E + 4 * 2)%Z with (e_IDX E + 8)%Z in IDXA3 by lia end.
    store_done.
    assert (IDXF3 : firstn (length (@nil Z) + 3) (upd (upd (upd ws0 (length (@nil Z)) (wz 0)) (length (@nil Z) + 1) (wz 0)) (length (@nil Z) + 2) (wz 0)) = map wz ([] ++ [0; 0; 0]%Z)).
    { apply arr_push3; [reflexivity| cbn; lia]. }
    cbn [length Nat.add app] in IDXF3. change (Z.to_nat 0) with 0%nat in IDXA3. change (Z.to_nat 1) with 1%nat in IDXA3. change (Z.to_nat 2) with 2%nat in IDXA3.
    unfold wz in IDXF3 at 1 2 3.
    assert (IDXL3 : length (upd (upd (upd ws0 0 (Z_to_bv 64 0)) 1 (Z_to_bv 64 0)) 2 (Z_to_bv 64 0)) = e_cap E)
      by (rewrite !upd_length; exact IDXL).

    zstep. zstep.
    replace (e_IDX E - e_IDX E)%Z with 0%Z by lia. change (Z.shiftr 0 2) with 0%Z.
    zstep. s1norm. zstep. zstep. zstep. if_false. zstep.

    do 13 zstep. zstep. zstep.
    s1_cur_mem ltac:(fun m =>
      pose proof (stk_release usegs m _ _ _ ST FRlo ltac:(lia)) as ST1;
      cbn [cells_size csize Nat.add] in ST1;
      replace (bv_unsigned (e_sp E) + -432 + Z.of_nat 32)%Z with (bv_unsigned (e_sp E) + -400)%Z in ST1 by lia;
      pose proof (stk_release usegs m _ _ _ ST1 DSTc ltac:(lia)) as ST2;
      cbn [cells_size csize Nat.add] in ST2;
      replace (bv_unsigned (e_sp E) + -400 + Z.of_nat 256)%Z with (bv_unsigned (e_sp E) + -144)%Z in ST2 by lia;
      pose proof (stk_release usegs m _ _ _ ST2 FRhi ltac:(lia)) as ST3;
      cbn [cells_size csize Nat.add] in ST3;
      replace (bv_unsigned (e_sp E) + -144 + Z.of_nat 144)%Z with (bv_unsigned (e_sp E))%Z in ST3 by lia;
      apply evt_done; unfold s1z_post;
      do 14 eexists; exists m; eexists _, _).
    split; [cbv delta [mkR]; reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ST3|].
    split; [unfold parser_cells; cbn [length Z.of_nat]; rewrite LZ; unfold wz; eassumption|].
    split; [intros X; exfalso; apply X; reflexivity|].
    split; [exact IDXA3|]. split; [exact IDXL3|]. cbn [length Nat.add app] in IDXF3 |- *. rewrite LZ. exact IDXF3.
  Qed.
End S1Z.
