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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require MState.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Cells.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Exec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib Require SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc Require RStep.
Module RTac.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.PropExec OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.MState OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Mem OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Cells OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Exec OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Step OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Tac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.Image OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.Lib.SysStep.
Export OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.CJ.RL.Reloc.RStep.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac rel_unf := unfold RelCode, RelSym, RelNear, rel_code, rel_sym, rel_near in *.
(* [comment removed for export] *)
Ltac arel_side :=
  first [ solve [ match goal with
                  | R1 : RelCode ?B _ |- context [?B] =>
                      first [ match goal with R2 : RelSym ?K |- context [?K] => clear - R1 R2; rel_unf; lia end
                            | match goal with R2 : RelNear ?B ?C |- context [?C] => clear - R1 R2; rel_unf; lia end
                            | clear - R1; rel_unf; lia ]
                  | R2 : RelSym ?K |- context [?K] => clear - R2; rel_unf; lia
                  end ]
        | rel_unf; lia ].

(* [comment removed for export] *)
Ltac is_sym x :=
  first [ lazymatch x with @sym _ _ => idtac end
        | is_var x;
          first [ lazymatch goal with _ : rel_sym x |- _ => idtac end
                | lazymatch goal with _ : rel_code x _ |- _ => idtac end
                | lazymatch goal with _ : rel_near _ x |- _ => idtac end
                | lazymatch goal with _ : RelSym x |- _ => idtac end
                | lazymatch goal with _ : RelCode x _ |- _ => idtac end
                | lazymatch goal with _ : RelNear _ x |- _ => idtac end ] ].
Ltac has_sym e := first [ lazymatch e with context [@sym _ _] => idtac end | match e with context [?x] => is_sym x end ].

(* [comment removed for export] *)
Ltac arel :=
  repeat match goal with
  | |- context [(Z.shiftl (bv_signed (hi20 ?d)) 12 + ?P + bv_signed (lo12 ?d))%Z] =>
      rewrite (pcrel_pair d P) by arel_side
  | |- context [bv_signed (jimm21 ?d)] => rewrite (jimm21_signed d) by arel_side
  | |- context [bv_signed (bimm13 ?d)] => rewrite (bimm13_signed d) by arel_side
  | |- context [(?x + (?y - ?x))%Z] => has_sym y; rewrite (add_sub_cancel x y)
  | |- context [(?x - ?y + ?y)%Z] => is_sym y; rewrite (sub_add_cancel x y)
  | |- context [sx32 (Z_to_bv 64 ?e)] => has_sym e; rewrite (sx32_small e) by arel_side
  | |- context [Z_to_bv 64 (Z.add 0 ?x)] => is_sym x; rewrite (Z.add_0_l x)
  | |- context [Z_to_bv 64 (Z.add ?c ?x)] => is_Zlit c; is_sym x; rewrite (Z.add_comm c x)
  end.

(* [comment removed for export] *)
Ltac aret_pc :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] =>
      tryif is_Zlit n then fail else
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_sym; arel_side)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac apc_base E := lazymatch E with Z.add ?B ?k => lazymatch k with Z0 => B | Zpos _ => B | Zneg _ => B | _ => E end | _ => E end.
Ltac apc_off E := lazymatch E with Z.add ?B ?k => lazymatch k with Z0 => k | Zpos _ => k | Zneg _ => k | _ => constr:(0%Z) end | _ => constr:(0%Z) end.

Ltac find_off_eval k p :=
  let p' := eval hnf in p in
  eval cbv beta iota zeta delta [find_off Z.eqb Pos.eqb] in (find_off k p').
(* [comment removed for export] *)
Ltac desc_head t := lazymatch t with ?f _ => desc_head f | _ => t end.
Ltac find_t_eval k t :=
  (* [comment removed for export] *)
  let h := desc_head t in
  eval lazy beta iota zeta delta [find_t find_off Z.eqb Z.ltb Z.compare Pos.eqb Pos.compare Pos.compare_cont h] in (find_t k t).

(* [comment removed for export] *)
Ltac afetch segs E :=
  let B := apc_base E in
  let k := apc_off E in
  match goal with
  | CODE : CodeAtT segs B ?t |- _ =>
      let x := find_t_eval k t in
      lazymatch x with
      | Some ?ix =>
          lazymatch E with
          | Z.add _ _ => constr:(code_at_t_fetch segs B t k ix (@code_at_t_pf segs B t CODE) (@eq_refl (option (instr * Z)) (Some ix)))
          | _ => constr:(code_at_t_fetch0 segs B t ix (@code_at_t_pf segs B t CODE) (@eq_refl (option (instr * Z)) (Some ix)))
          end
      | None => fail 100 "astep: no instruction at offset" k "of routine" B
      end
  | CODE : CodeAt segs B ?p |- _ =>
      let x := find_off_eval k p in
      lazymatch x with
      | Some ?ix =>
          lazymatch E with
          | Z.add _ _ => constr:(code_at_fetch segs B p k ix (@code_at_pf segs B p CODE) (@eq_refl (option (instr * Z)) (Some ix)))
          | _ => constr:(code_at_fetch0 segs B p ix (@code_at_pf segs B p CODE) (@eq_refl (option (instr * Z)) (Some ix)))
          end
      | None => fail 100 "astep: no instruction at offset" k "of routine" B
      end
  | CODE : code_at segs B ?p |- _ =>
      let x := find_off_eval k p in
      lazymatch x with
      | Some ?ix =>
          lazymatch E with
          | Z.add _ _ => constr:(code_at_fetch segs B p k ix CODE (@eq_refl (option (instr * Z)) (Some ix)))
          | _ => constr:(code_at_fetch0 segs B p ix CODE (@eq_refl (option (instr * Z)) (Some ix)))
          end
      | None => fail 100 "astep: no instruction at offset" k "of routine" B
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac astepL_pc S := rewrite ?b_addsext; vnorm_tail_ctx S; arel; aret_pc; reflexivity.
Ltac astepL_val i S vh := simp_is_x0; simp_regs; stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; arel; vh; reflexivity.
Ltac astepL_addr i S := simp_is_x0; simp_regs; stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; arel; reflexivity.

Ltac astepL_load_val vh :=
  cbv beta iota delta [width_bytes]; simp_is_x0; simp_regs; stepL_frm;
  solve_load;
  cbv beta iota; load_post; arel; vh; reflexivity.

Ltac astepL_apply app FD i S rp vh :=
  eapply app;
  [ exact FD
  | reflexivity                  (* [comment removed for export] *)
  | astepL_val i S vh            (* [comment removed for export] *)
  | astepL_pc S                  (* [comment removed for export] *)
  | stepL_post; rp ].

Ltac astepL_apply_load app FD i S rp vh :=
  eapply app;
  [ exact FD
  | reflexivity
  | astepL_addr i S
  | astepL_load_val vh
  | astepL_pc S
  | stepL_post; rp ].

Ltac astepL_apply_store app FD i S rp vh :=
  eapply app;
  [ exact FD
  | astepL_addr i S
  | cbv beta iota delta [width_bytes]; simp_is_x0; simp_regs; stepL_frm; vnorm_tail_ctx S;
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1'; vh; reflexivity
  | cbv beta iota delta [width_bytes]; stepL_store_ok
  | cbv beta iota; reflexivity
  | astepL_pc S
  | stepL_frm; rp; mem_after_store_opt ].

Ltac astepL_apply_branch app FD i S rp vh :=
  eapply app;
  [ exact FD
  | cbv beta iota delta [branch_taken]; simp_is_x0; simp_regs; stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; vh; reflexivity
  | astepL_pc S
  | astepL_pc S
  | stepL_frm; rp ].

Ltac astepL_apply_jal app FD S rp vh :=
  eapply app; [ exact FD | reflexivity | astepL_pc S | astepL_pc S | stepL_post; rp ].
Ltac astepL_apply_jal0 app FD S rp vh :=
  eapply app; [ exact FD | reflexivity | astepL_pc S | rp ].
Ltac astepL_apply_jalr app FD i S rp vh :=
  eapply app;
  [ exact FD | reflexivity | astepL_pc S
  | simp_is_x0; simp_regs; stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; arel; aret_pc; vh; reflexivity
  | stepL_post; rp ].
Ltac astepL_apply_jalr0 app FD i S rp vh :=
  eapply app;
  [ exact FD | reflexivity
  | simp_is_x0; simp_regs; stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; arel; aret_pc; vh; reflexivity
  | rp ].

Ltac astep2_lemma segs Q R F pcw fc rv m ro FD i sz rp rpm vh :=
  let S := constr:(MS R F pcw fc rv m ro) in
  lazymatch i with
  | Store ?msz ?rs1 ?rs2 ?imm => astepL_apply_store (aevt_Store segs Q R F pcw fc rv m ro msz rs1 rs2 imm) FD i S rpm vh
  | Branch ?bc ?rs1 ?rs2 ?imm => astepL_apply_branch (aevt_Branch segs Q R F pcw fc rv m ro bc rs1 rs2 imm) FD i S rpm vh
  | Jal ?rd ?imm =>
      let x0 := eval vm_compute in (is_x0 rd) in
      lazymatch x0 with
      | true => astepL_apply_jal0 (aevt_Jal_x0 segs Q R F pcw fc rv m ro rd imm sz) FD S rpm vh
      | false => astepL_apply_jal (aevt_Jal segs Q R F pcw fc rv m ro rd imm sz) FD S rpm vh
      end
  | Jalr ?rd ?rs ?imm =>
      let x0 := eval vm_compute in (is_x0 rd) in
      lazymatch x0 with
      | true => astepL_apply_jalr0 (aevt_Jalr_x0 segs Q R F pcw fc rv m ro rd rs imm sz) FD i S rpm vh
      | false => astepL_apply_jalr (aevt_Jalr segs Q R F pcw fc rv m ro rd rs imm sz) FD i S rpm vh
      end
  | _ =>
    let rd := stepL_rd i in
    let x0 := eval vm_compute in (is_x0 rd) in
    lazymatch x0 with false =>
    lazymatch i with
    | OpImm ?op ?rd ?rs ?imm => astepL_apply (aevt_OpImm segs Q R F pcw fc rv m ro op rd rs imm) FD i S rp vh
    | ShiftImm ?op ?rd ?rs ?sh => astepL_apply (aevt_ShiftImm segs Q R F pcw fc rv m ro op rd rs sh) FD i S rp vh
    | Op ?op ?rd ?rs1 ?rs2 => astepL_apply (aevt_Op segs Q R F pcw fc rv m ro op rd rs1 rs2) FD i S rp vh
    | OpImm32 ?rd ?rs ?imm => astepL_apply (aevt_OpImm32 segs Q R F pcw fc rv m ro rd rs imm) FD i S rp vh
    | ShiftImm32 ?op ?rd ?rs ?sh => astepL_apply (aevt_ShiftImm32 segs Q R F pcw fc rv m ro op rd rs sh) FD i S rp vh
    | Op32 ?op ?rd ?rs1 ?rs2 => astepL_apply (aevt_Op32 segs Q R F pcw fc rv m ro op rd rs1 rs2) FD i S rp vh
    | Mul ?op ?rd ?rs1 ?rs2 => astepL_apply (aevt_Mul segs Q R F pcw fc rv m ro op rd rs1 rs2) FD i S rp vh
    | Mul32 ?op ?rd ?rs1 ?rs2 => astepL_apply (aevt_Mul32 segs Q R F pcw fc rv m ro op rd rs1 rs2) FD i S rp vh
    | Lui ?rd ?imm => astepL_apply (aevt_Lui segs Q R F pcw fc rv m ro rd imm) FD i S rp vh
    | Auipc ?rd ?imm => astepL_apply (aevt_Auipc segs Q R F pcw fc rv m ro rd imm) FD i S rp vh
    | Load ?msz ?sgn ?rd ?rs ?imm => astepL_apply_load (aevt_Load segs Q R F pcw fc rv m ro msz sgn rd rs imm) FD i S rpm vh
    end end
  end.

(* [comment removed for export] *)
Ltac astep_core segs R F pcw fc rv m ro FD i sz :=
  eapply evt_step;
  [ split; [reflexivity|];
    rewrite (step_gen_dec segs R F pcw fc rv m ro i sz FD ltac:(discriminate));
    exec_pre i;
    exec_cbv; simp_is_x0; simp_regs; vnorm_for i; arel;
    try solve_load; try solve_store;
    reflexivity
  | simp_regs; vnorm_for i; arel; aret_pc; mem_after_store_opt; post_step i ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac concrete_segs segs := first [ is_const segs | fail 100 "astep: the pc is in no routine description of this abstract image (wrong LEN / missing --split or --range / un-normalised jump target)" ].

Ltac step2_with_orig rp rpm vh :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => concrete_segs segs; step2_core segs Q R F pc fc rv m ro rp rpm vh
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Ltac astep2_with rp rpm vh :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?E) ?fc ?rv ?m ?ro) =>
      tryif (let B := apc_base E in first [ lazymatch goal with CODE : code_at segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAt segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAtT segs B _ |- _ => idtac end ])
      then
        (let FD0 := afetch segs E in
         let FD := fresh "FD" in
         pose proof FD0 as FD;
         lazymatch type of FD with
         | fetch_dec _ _ = Some (?i, ?sz) =>
             first [ astep2_lemma segs Q R F (Z_to_bv 64 E) fc rv m ro FD i sz rp rpm vh
                   | astep_core segs R F (Z_to_bv 64 E) fc rv m ro FD i sz ];
             try clear FD
         end)
      else step2_with_orig rp rpm vh
  | |- _ => step2_with_orig rp rpm vh
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac step_ecall_orig :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      concrete_segs segs;
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w =>
          apply (evt_ecall segs Q R F pc fc rv m ro w);
          [ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
      | None => fail "no instruction at" pc
      end
  end.
Ltac astep_ecall :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?E) ?fc ?rv ?m ?ro) =>
      tryif (let B := apc_base E in first [ lazymatch goal with CODE : code_at segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAt segs B _ |- _ => idtac end
                                             | lazymatch goal with CODE : CodeAtT segs B _ |- _ => idtac end ])
      then (let FD0 := afetch segs E in apply (aevt_ecall segs Q R F (Z_to_bv 64 E) fc rv m ro FD0); simp_regs)
      else step_ecall_orig
  end.

Ltac astep2 := astep2_with ltac:(vnorm_tail) ltac:(vnorm_tail) ltac:(idtac).
Ltac astep2_fast := astep2_with ltac:(idtac) ltac:(vnorm_tail) ltac:(idtac).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac asolve_load_image :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          match goal with
          | RO : RoB segs ?G (cells_bytes ?cs) |- _ =>
              let k := addr_diff E G in
              let RC := fresh "ROimg" in
              assert (RC : ro_cells segs m G cs)
                by (apply (ro_cells_image_cells segs m G cs HI (@ro_b_pf segs G _ RO));
                    [ cbv [cells_wf cell_wf]; repeat split | arel_side | cbv [cells_bytes cbytes]; rewrite ?length_app, ?length_le4, ?length_le8; cbn [length]; arel_side ]);
              solve_load_base; clear RC
          | RO : RoB segs ?G ?bs |- _ =>
              let k := addr_diff E G in
              let RC := fresh "ROimg" in
              assert (RC : ro_cells segs m G [CB (length bs) bs])
                by (apply (ro_cells_image segs m G bs HI (@ro_b_pf segs G bs RO)); cbn [length]; arel_side);
              cbn [length] in RC;
              solve_load_base; clear RC
          | RO : ro_bytes_b segs ?G (cells_bytes ?cs) = true |- _ =>
              let k := addr_diff E G in
              let RC := fresh "ROimg" in
              assert (RC : ro_cells segs m G cs)
                by (apply (ro_cells_image_cells segs m G cs HI RO);
                    [ cbv [cells_wf cell_wf]; repeat split | arel_side | cbv [cells_bytes cbytes]; rewrite ?length_app, ?length_le4, ?length_le8; cbn [length]; arel_side ]);
              solve_load_base; clear RC
          | RO : ro_bytes_b segs ?G ?bs = true |- _ =>
              let k := addr_diff E G in
              let RC := fresh "ROimg" in
              assert (RC : ro_cells segs m G [CB (length bs) bs])
                by (apply (ro_cells_image segs m G bs HI RO); cbn [length]; arel_side);
              cbn [length] in RC;
              solve_load_base; clear RC
          end
      end
  end.

Ltac asolve_load := first [ solve_load_base | solve_load_image | asolve_load_image ].

(* [comment removed for export] *)
Ltac sym_unsigned :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => has_sym z; rewrite (unsigned_lit z) by arel_side
  | |- context [bv_signed (Z_to_bv 64 ?z)] => has_sym z; rewrite (Z_to_bv_signed 64 z), (bv_swrap_small 64 z) by (change (bv_half_modulus 64) with (2^63)%Z; arel_side)
  end.
Ltac asolve_cond := unfold_cond; fold_lit_ux; sym_unsigned; solve_cond_rec.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac step2_fast_abs := astep2_fast.

(* [comment removed for export] *)
Ltac asys_nret :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       tryif is_Zlit p then
         (let p' := eval vm_compute in (p + 4)%Z in
          replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity))
       else (rewrite lit_add_lit; fold_closed_in_goal)
   | _ => idtac
   end);
  first [ rewrite apply_mem_none
        | rewrite apply_mem_delivered; sys_mem_write
        | rewrite apply_mem_write; sys_mem_write
        | rewrite apply_mem_zeros; sys_mem_zeros
        | rewrite apply_mem_unmaps; sys_mem_unmaps
        | idtac ].

(* [comment removed for export] *)
Ltac rimg_evars :=
  repeat match goal with
  | |- context [?x] => is_evar x; let T := type of x in unify T RImg; let I := constr:(_ : RImg) in unify x I
  end.

(* [comment removed for export] *)
Ltac asys_nret_raw :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       tryif is_Zlit p then
         (let p' := eval vm_compute in (p + 4)%Z in
          replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity))
       else (rewrite lit_add_lit; fold_closed_in_goal)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].

(* [comment removed for export] *)
Ltac apost_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      tryif is_Zlit n then
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
      else aret_pc
  end).

(* [comment removed for export] *)
(* [comment removed for export] *)
End RTac.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Import RTac.
Unset Lia Cache.

Ltac find_t_eval_at k t :=
  let h := desc_head t in
  let r := eval lazy beta iota zeta delta [find_t find_off Z.eqb Z.ltb Z.compare Pos.eqb Pos.compare Pos.compare_cont h] in (find_t k t) in
  lazymatch r with
  | Some _ => r
  | None => r
  | _ => let t1 := eval cbv beta delta [h] in t in
         let h1 := desc_head t1 in
         eval lazy beta iota zeta delta [find_t find_off Z.eqb Z.ltb Z.compare Pos.eqb Pos.compare Pos.compare_cont h1] in (find_t k t1)
  end.
