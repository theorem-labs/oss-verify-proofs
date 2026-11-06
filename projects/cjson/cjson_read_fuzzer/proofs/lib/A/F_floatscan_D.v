(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan_nn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan_nn.FloatScan_split.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FloatScan_split2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memcpy F_memchr F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_multf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_multf3.F_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_multf3 F_divtf3 F_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_subtf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_subtf3.F_addtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_subtf3 F_letf2 F_getf2 F_floatsitf F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pop_arg.F_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_scalbn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_proofs.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_scalbnl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_floatscan_common.F_fmodl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_floatscan_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

(* [comment removed for export] *)
Local Ltac nat_diet ::= repeat nat_diet_step;
  lazymatch goal with _ : Z.of_nat (natZ _) = _ |- _ => idtac | _ =>
    repeat match goal with H : context [natZ (Zpos ?p)] |- _ =>
      lazymatch goal with _ : Z.of_nat (natZ (Zpos p)) = _ |- _ => fail | _ => pose proof (natZ_pos p) end end end.
Section Floatscan.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
            (fR : shfile) (yR : Z).
  Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
  Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
  Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
  Hypothesis HP64 : (p <= 64)%Z.
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
  Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
  Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
  Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
  Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
  Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
  Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
  Hypothesis Q1 : (q < 2^63)%Z.
  Hypothesis FRM : frm0 fc.
  Hypothesis AXF : sh_stdio f0 = true -> scan_ax m0 q FS_DEPTH Fp T txt p.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac lia ::= first [ zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
                           | zify_prune_fast; Zify.zify; xlia zchecker
                           | Zify.zify; xlia zchecker ].
  (* [comment removed for export] *)
  Local Ltac solve_load_base ::=
    match goal with
    | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      match goal with
      | H : rw_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
          end
      | H : ro_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
          end
      | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
          cbv delta [wa] in HR;
          first [ rewrite HR
                | replace (ov_read_bytes segs m a n) with (Some bs)
                    by (rewrite <- HR; f_equal; word_eq_tac) ]
      end
    end;
    load_post.
  Local Ltac solve_store ::=
    match goal with
    | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let E := addr_expr a in
      match goal with
      | H : rw_cells segs m ?A ?cs0 |- _ =>
          let k := addr_diff E A in
          lazymatch k with Zneg _ => fail | _ => idtac end;
          let kn := eval vm_compute in (Z.to_nat k) in
          split_for_access H segs m A cs0 kn n;
          let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
          let c := eval_cell_at cs kn in
          lazymatch c with Some ?c0 =>
            rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
            cbv beta iota;
            match goal with
            | |- context [write_to_mem m a ?bs] =>
                replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
            end
          end
      | HS : store_ok segs m ?a' n = true |- _ =>
          cbv delta [wa] in HS;
          first [ rewrite HS
                | replace (store_ok segs m a n) with true
                    by (rewrite <- HS; f_equal; word_eq_tac);
                  try replace (write_to_mem m a) with (write_to_mem m a')
                    by (f_equal; word_eq_tac) ];
          cbv beta iota
      end
    end.
  Notation TPv := (Z_to_bv 64 RATP).
  Notation SPv := (Z_to_bv 64 (q + -8416)).
  Notation XA := (q + -8312)%Z.
  Notation RFJ' := (RFJ T txt p true J).
  (* [comment removed for export] *)
  Local Notation ctx_all := (@F_floatscan_common.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation Wfs := (@F_floatscan_common.Wfs q Fp).
  Local Notation FokR := (@F_floatscan_common.FokR F).
  Local Notation Fok := (@F_floatscan_common.Fok F).
  Local Notation Fok_refl := (@F_floatscan_common.Fok_refl F).
  Local Notation Fok_set := (@F_floatscan_common.Fok_set F).
  Local Notation Fok_trans10 := (@F_floatscan_common.Fok_trans10 F).
  Local Notation fs_post := (@F_floatscan_common.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
  Local Notation hi_cells := (@F_floatscan_common.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F canary).
  Local Notation finv := (@F_floatscan_common.finv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T txt canary).
  Local Notation zbytes_len := (@F_floatscan_common.zbytes_len txt).
  Local Notation framL := (@F_floatscan_common.framL q).
  Local Notation txt_char := (@F_floatscan_common.txt_char txt BYT).
  Local Notation numch_nz := (@F_floatscan_common.numch_nz p txt Hnum).
  Local Notation frame_release := (@F_floatscan_common.frame_release ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T txt pre canary).
  Local Notation post_tail := (@F_floatscan_common.post_tail ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt pre canary fR yR Hp SE_T SPF SPT SG1 SG3).
  Local Notation L_RET34 := (@F_floatscan_common.L_RET34 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
  Local Notation L_RET1 := (@F_floatscan_common.L_RET1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
  Local Notation L_RET30 := (@F_floatscan_common.L_RET30 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPF SPT SG1 SG3).
  Local Notation L_SCL := (@F_floatscan_common.L_SCL ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR Hp SE_T SPLO SPF SPT SG1 SG3 Q1).
  Local Notation dfinv := (@F_floatscan_common.dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
  Local Notation dfinvG := (@F_floatscan_common.dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
  Local Notation dfinvG_dfinv := (@F_floatscan_common.dfinvG_dfinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
  Local Notation S_F3 := (@F_floatscan_common.S_F3 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_F2 := (@F_floatscan_common.S_F2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_F1 := (@F_floatscan_common.S_F1 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A69C := (@F_floatscan_common.S_A69C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A62C := (@F_floatscan_common.S_A62C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A5C4 := (@F_floatscan_common.S_A5C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A568 := (@F_floatscan_common.S_A568 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A534 := (@F_floatscan_common.S_A534 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation SN324 := (@F_floatscan_common.SN324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_N324 := (@F_floatscan_common.S_N324 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_N2D4 := (@F_floatscan_common.S_N2D4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_U1A8 := (@F_floatscan_common.S_U1A8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_NK := (@F_floatscan_common.S_NK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok fR yR).
  Local Notation S_N484 := (@F_floatscan_common.S_N484 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_N3E8 := (@F_floatscan_common.S_N3E8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_UK := (@F_floatscan_common.S_UK ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation SU1C4 := (@F_floatscan_common.SU1C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_U1C4 := (@F_floatscan_common.S_U1C4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_T := (@F_floatscan_common.S_T ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_DD0 := (@F_floatscan_common.S_DD0 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_DD24 := (@F_floatscan_common.S_DD24 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_M := (@F_floatscan_common.S_M ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_P := (@F_floatscan_common.S_P ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_R := (@F_floatscan_common.S_R ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_C38 := (@F_floatscan_common.S_C38 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_C2C := (@F_floatscan_common.S_C2C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_E := (@F_floatscan_common.S_E ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation SDn := (@F_floatscan_common.SDn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_D := (@F_floatscan_common.S_D ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation winv := (@F_floatscan_common.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
  Local Notation winv_dfinvG := (@F_floatscan_common.winv_dfinvG ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary pok).
  Local Notation S_B0C := (@F_floatscan_common.S_B0C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A9C := (@F_floatscan_common.S_A9C ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A44 := (@F_floatscan_common.S_A44 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation SRZn := (@F_floatscan_common.SRZn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_RZ := (@F_floatscan_common.S_RZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_9EC := (@F_floatscan_common.S_9EC ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_A64 := (@F_floatscan_common.S_A64 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_7F4 := (@F_floatscan_common.S_7F4 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_9C8 := (@F_floatscan_common.S_9C8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation SLZn := (@F_floatscan_common.SLZn ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_LZ := (@F_floatscan_common.S_LZ ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_990 := (@F_floatscan_common.S_990 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_848 := (@F_floatscan_common.S_848 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation S_6F8 := (@F_floatscan_common.S_6F8 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  Local Notation FS_tail := (@F_floatscan_common.FS_tail pok fuelc).
  Local Notation S_618 := (@F_floatscan_common.S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
  (* [comment removed for export] *)
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    (nelim H 8%nat; intros MI MU WM FRhi ST TXT SSP1 SSP2); unfold F_floatscan_common.Wfs, FS_DEPTH, RERRNO in MU; unfold F_floatscan_common.hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
    unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
    try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    unfold zlength in *.
  Ltac mk_finv := unfold F_floatscan_common.finv, F_floatscan_common.Wfs, F_floatscan_common.hi_cells, FS_DEPTH, RERRNO, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.
  Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.
  Ltac mk_framL := unfold F_floatscan_common.framL, RERRNO; split; hyp.
  Ltac lo96w H := apply (cb8_c8_in _ _ [_; _; _; _; _; _; _; _; _; _; _; _] []) in H; cbn [app] in H.
  Ltac lo96b H := apply (proj1 (rw_cells_C8_CB8 _ _ [_; _; _; _; _; _; _; _; _; _; _; _] _ [])) in H; cbn [app] in H.
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.
  Ltac fok := repeat (apply Fok_set; [|vm_compute; lia]); first [assumption | apply Fok_refl].
  Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac unstash := unfold hide in *.
  Ltac store_done' := stash_mods; stash_disj; unfold hide in SPT; store_done; unstash.
  (* [comment removed for export] *)
  Ltac lia_goal P := lazymatch P with
    | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
    | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
    | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
    | ?A /\ ?B => lia_goal A; lia_goal B | ?A \/ ?B => lia_goal A; lia_goal B | ?A -> ?B => lia_goal B | ~ _ => idtac
    | ?A <-> ?B => lia_goal A; lia_goal B | False => idtac | True => idtac | hide ?A => lia_goal A | hide2 ?A => lia_goal A
    end.
  Ltac flia := lazymatch goal with |- ?G => lia_goal G end; first [ solve [stash_mods; stash_disj; lia] | lia ].
  Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
  Ltac hush := try stash SEP; try stash SG2; try stash SG3; try stash SE_T; try stash Hpok; stash_mods.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.
  Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
  (* [comment removed for export] *)
  Ltac predi := repeat match goal with H : @eq nat ?a ?l |- _ => natlit_z l ltac:(fun z p => change (@eq nat a (natZ z)) in H; note_natZ z p) end.
  Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok; predi.
  Ltac unbury := unfold hide2 in *.
  Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
  (* [comment removed for export] *)
  Ltac glia := lazymatch goal with |- ?G => lia_goal G end; lia.
  (* [comment removed for export] *)
  Ltac br10 K := brf K; [ exfalso; lia | ].
  Ltac br01 K := brf K; [ | exfalso; lia ].
  (* [comment removed for export] *)
  Ltac zsimp_in_w H :=
    try (match type of H with
         | context [v_sltu _ _] => idtac | context [v_slt _ _] => idtac
         | context [v_sltiu _ _] => idtac | context [v_slti _ _] => idtac end;
         rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H);
    try (match type of H with context [zxb] => cbv delta [zxb] in H end);
    zb_fold_lits_in H;
    repeat match type of H with
    | context [bv_unsigned (Z_to_bv 64 ?e)] => zs_wrap_in e H
    | _ => progress (zs_idioms_in H)
    end; zb_fold_lits_in H.
  Ltac brfw K := if_cases K; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K;
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in_w K; zify_bool K;
    try (rewrite ?signed_of_Z in K by lia).
  Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_dfinv := unfold F_floatscan_common.dfinv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Ltac mk_dfinvG := unfold F_floatscan_common.dfinvG; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Ltac fixk := rewrite ?land2047, ?landW_mod2048 in *.
  Ltac hlia H := let E := fresh in intros E; specialize (H E); lia.
  Tactic Notation "call_split" constr(K) tactic3(tac) :=
    lazymatch goal with ST : stk _ ?m (q - 10960)%Z (q + -8416)%Z |- _ =>
      let ST1 := fresh "ST1" in
      destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
      callw tac;
      lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
        lazymatch goal with ST1' : stk _ m' (q - 10960)%Z (q + -8416 - K)%Z |- _ =>
        pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
    end.
  Ltac eval_lands := repeat match goal with |- context [Z.land ?a ?b] =>
    lazymatch isZcst a with true => lazymatch isZcst b with true =>
      let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v end end end.
  Ltac simpF := repeat first [rewrite freg_get_same by (vm_compute; reflexivity) | rewrite freg_get_other by (vm_compute; reflexivity)].
  Ltac dest_winv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    (nelim H 5%nat; intros FI FL XW LW FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_winv := unfold F_floatscan_common.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Notation POST := (fs_post m0).

  (* [comment removed for export] *)

  Hypothesis HS_E : S_E.
  Hypothesis HS_C2C : S_C2C.
  Hypothesis HS_C38 : S_C38.

  (* [comment removed for export] *)
  Ltac ufc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac ufc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac site_facts FC RJ k c f :=
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.
  Ltac eplia := unfold zlength, got_ssp, ssp_guard in *; unfold hide2 in *; lia.
  (* [comment removed for export] *)
  Ltac fsx :=
    lazymatch goal with |- scan_ax ?mm _ _ _ _ _ _ =>
      match goal with S : sh_stdio f0 = true, MUx : munch _ m0 mm |- _ =>
        let X := fresh "AXc" in pose proof (AXF S) as X;
        let C := fresh "AXce" in pose proof (proj1 (proj2 X)) as C; unfold alloc_ceiling, sp_window_lo, stack_max_size, FS_DEPTH in C;
        eapply (scan_ax_xfer m0 mm _ _ _ _ Fp T txt p _ X MUx);
        [ unfold scan_iv_ok; repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size; lia|]); apply Forall_nil
        | unfold FS_DEPTH, SCANEXP_DEPTH; lia | lia | lia | unfold zlength in *; unfold hide2 in *; lia ]
      end end.
  Ltac fsxE := let S := fresh "STDx" in intros S; try match goal with H : sh_stdio _ = sh_stdio f0 |- _ => rewrite H in S end; fsx.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
  Ltac mk_facts := unfold digI, dig_facts; splits; try assumption; try glia.
  Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
  Proof using . clear. intros f. exact (proj1 (sh_getc_stdio f)). Qed.
  Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
  Proof using . clear. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
  Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
  Proof using . clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
  Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
  Proof using .
    clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
    destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
  Qed.
  Lemma b2z_land1 : forall b, Z.land (Z.b2z b) 1 = Z.b2z b.
  Proof using . clear. destruct b; reflexivity. Qed.
  Lemma Eng : forall g, (0 <= g <= 1)%Z -> Z.b2z (g <? 1)%Z = Z.b2z (g =? 0)%Z.
  Proof using . clear. intros g Hg. destruct (Z.ltb_spec g 1); destruct (Z.eqb_spec g 0); cbn; lia. Qed.
  (* [comment removed for export] *)
  Lemma sh_getc_rpos : forall f, sh_buf f = txt ->
    (sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
  Proof using .
    clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
    destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma L_LATCH : forall n, SDn n ->
    forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
      j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> c <> 0%Z -> c <> (-1)%Z ->
    xrel ws x (digz k j) -> X31 x -> (0 <= j <= 8)%Z -> (0 <= k)%Z -> (9 * k + j <= dc)%Z -> (0 <= dc <= sh_rpos f)%Z ->
    (0 <= lnz <= dc)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z -> (j <> 0%Z -> znth x k < 10 ^ j)%Z -> (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) ->
    (-2^20 <= lrp <= 2^20)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
    df_dig_loop n (mkDL (snd (sh_getc f)) (fst (sh_getc f)) j k lrp dc lnz gotdig gotrad x) = Some s' ->
    dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
    evt asegs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x98468) fct None m (seg_rom asegs)).
  Proof using AXF BYT HP64 HS_E Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros n IH. intros until s'. intros DI RJ Hk FOK FRM' Hsg Hst Hc0 Hcn1 XR X31H Rj Rk Hkj9 Rdc Rlnz Hlnz Hxk Hkj Rlrp Rg Rgr HL HK.
    pose proof DI as DI0. dest_dfinv DI. bury_disj.
    site_facts FC RJ kmin c f.
    pose proof (RFI_getc T txt p J BYT Hp Hnul kmin c f RJ Hc0) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    pose proof (sh_getc_rpos f Hbuf) as [Rrp1 Rrp2].
    (* [comment removed for export] *)
    assert (NEXT : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
      dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
      (evt asegs POST
         (MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
                  (Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
             Ft (Z_to_bv 64 (if (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z then 0x983e4 else 0x9832c)) fct None m2 (seg_rom asegs)))).
    { intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2.
      destruct (isdigitc (fst (sh_getc f)) || (fst (sh_getc f) =? 46))%Z eqn:Hcond.
      - eapply (IH m2); try eassumption; try glia. mk_facts.
      - destruct n as [|n']; [discriminate HL|]. rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
        injection HL as <-.
        stmt HS_E. eapply NX with (gotdig := gotdig) (gotrad := gotrad); try eassumption; try glia.
        all: try (rewrite <- dfinvG_dfinv in DI2; exact DI2). all: try (intros _; reflexivity). all: mk_facts. }
    (* [comment removed for export] *)
    assert (N68 : forall m2 (x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' : word),
      dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign (snd (sh_getc f)) ->
      fst (sh_getc f) <> 46%Z ->
      evt asegs POST
         (MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) + -48)) (Z_to_bv 64 (Z.b2z (fst (sh_getc f) =? 46)%Z)) x13' x14' x15' x16' x17'
                  (Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28' x29' x30' x31')
             Ft (Z_to_bv 64 0x983e0) fct None m2 (seg_rom asegs))).
    { intros m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2 Hne.
      clear HL. pose proof DI2 as DI3. dest_dfinv DI3.
      set (c' := fst (sh_getc f)) in *.
      zs. brfw K; rewrite ?land_W64 in K.
      - (* [comment removed for export] *)
        pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
        replace (isdigitc c' || (c' =? 46))%Z with false in NX; [exact NX|].
        replace (c' =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne).
        replace (isdigitc c') with false; [reflexivity|]. symmetry. apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c' ltac:(lia))) in D.
        clear -K D Rc'. Z.div_mod_to_equations. lia.
      - pose proof (NEXT m2 x1' x5' x6' x7' x13' x14' x15' x16' x17' x28' x29' x30' x31' DI2) as NX.
        replace (isdigitc c' || (c' =? 46))%Z with true in NX; [exact NX|].
        replace (isdigitc c') with true; [reflexivity|]. symmetry. apply (proj2 (isdigitc_iff c' ltac:(lia))).
        clear -K Rc'. Z.div_mod_to_equations. lia. }
    destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. ufc2 FC.
      zs. zs. zs. br K1.
      (nelim (rf_getc_slow T txt p J Hp T1 kmin c f RJ SLOW) 5%nat; intros STD EJ Hn Hrpe Hc00).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. call_split 2464%Z (eapply shgetc_callJ with (pre := pre) (post := post);
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | eplia | eplia | exact SEP | replace (q + -8416 - 2464)%Z with (q + -8416 - 2464)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption | fsx ]).
      match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
      match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
      set (c' := fst (sh_getc f)) in *.
      zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brfw K2; rewrite ?land_W64 in K2.
      + (* [comment removed for export] *)
        assert (E46 : c' = 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
        pose proof NEXT as NX.
        replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
        eapply NX. mk_dfinv.
      + assert (N46 : c' <> 46%Z) by (clear -K2 Rc'; Z.div_mod_to_equations; lia).
        eapply N68; [mk_dfinv | exact N46].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp kmin c f RJ Hc0 FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp kmin c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      ufc2 FC.
      zs. zs. zs. br10 K1.
      zs. zs0.
      pose proof (u8ro_read asegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. try rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      set (c' := znth txt (sh_rpos f)) in *.
      zs. fixw3. fixw. zs. zs. rewrite (seqz46 c') by lia. zs. brf K2; rewrite ?land_W64 in K2.
      + (* [comment removed for export] *)
        assert (N46 : c' <> 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
        eapply N68; [| exact N46]. unfold F_floatscan_common.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
      + assert (E46 : c' = 46%Z) by (clear -K2 Rch; Z.div_mod_to_equations; lia).
        zs.
        pose proof NEXT as NX.
        replace (c' =? 46)%Z with true in NX |- * by (symmetry; apply Z.eqb_eq; exact E46). rewrite Bool.orb_true_r in NX.
        eapply NX. unfold F_floatscan_common.dfinv. split; [mk_finv|]. split; [mk_framL|]. split; [eassumption|]. split; [assumption|].
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
  Qed.

  Lemma seqz_land : forall e, (-2^63 < e < 2^63)%Z -> (Z.land e 18446744073709551615 <? 1)%Z = (e =? 0)%Z.
  Proof using .
    clear. intros e He. rewrite land_W64. destruct (Z.eqb_spec e 0) as [->|Hne]; [reflexivity|].
    destruct (Z.ltb_spec (e mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_D : S_D.
  Proof using AXF BYT HP64 HS_C2C HS_C38 HS_E Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    unfold F_floatscan_common.S_D. induction n as [|n IH].
    { intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK. discriminate HL. }
    pose proof (L_LATCH n IH) as LATCH.
    intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Hst DG Hcond HL HK.
    pose proof DI as DI0. dest_dfinv DI. bury_disj.
    (nelim DG 14%nat; intros XR X31H Rj Rk Hkj9 Rdc Hdc1 Rlnz Hlnz Hxk Hkj Rlrp Rg Rgr).
    (nelim XR 3%nat; intros LW' LX REL).
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    rewrite df_dig_loop_step in HL. unfold df_dig_cond in HL. cbn [dl_c] in HL. rewrite Hcond in HL.
    unfold df_dig_body in HL. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in HL.
    zs. rewrite b2z_land1. zs. brf K1.
    - (* [comment removed for export] *)
      replace (c =? 46)%Z with false in Hcond by (symmetry; apply Z.eqb_neq; exact K1). rewrite Bool.orb_false_r in Hcond.
      replace (c =? 46)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K1).
      assert (Hd : (48 <= c <= 57)%Z) by (apply (proj1 (isdigitc_iff c ltac:(lia))); exact Hcond).
      assert (Hk7 : (k <= 7)%Z) by lia.
      replace (k <? KMAX - 3)%Z with true in HL by (symmetry; apply Z.ltb_lt; unfold KMAX; lia).
      rewrite (s32_id (dc + 1)) in HL by lia.
      zs. zs. brs K2.
      (* [comment removed for export] *)
      assert (G94 : forall m2 (x12' : word) lnz2, lnz2 = (if (c =? 48)%Z then lnz else (dc + 1)%Z) ->
        dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz2)) ev ws sign f ->
        evt asegs POST
          (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 (dc + 1)) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12' x13 x14 x15 x16 x17
                   (Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
              Ft (Z_to_bv 64 0x9840c) fct None m2 (seg_rom asegs))).
      { intros m2 x12' lnz2 Elnz2 DI2.
        clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW FC FI FL.
        pose proof DI2 as DI3. dest_dfinv DI3.
        zs. zs. zs. fix_idx. zs. brf K4.
        + (* [comment removed for export] *)
          assert (Ej : j = 0%Z) by exact K4. rewrite Ej in HL |- *. unfold nz in HL. rewrite Z.eqb_refl in HL. cbn [negb] in HL.
          replace (0 + 1 =? 9)%Z with false in HL by reflexivity. cbv beta iota in HL. replace (0 + 1)%Z with 1%Z in HL by reflexivity.
          pose proof (u32arr_store_ok asegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ k (Z_to_bv 64 (c + -48)) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
          zs. fixw3. zs. zs. change (Z.b2z (18446744073709551608 <? 1)) with 0%Z. zs. fixw3. try rewrite (Z.add_0_r k). zs. zs. zs. zs.
          try rewrite !swrap32_small by lia. try rewrite (Z.add_0_r k).
          rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
          replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
          eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 (c + -48))) sign kmin c (zupd x k (c - 48)) f 1%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
          all: try assumption; try glia.
          { mk_dfinv. }
          { split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
            intros i0 Hq Hr. destruct (Z.eq_dec i0 k) as [->|Hne].
            - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia.
            - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz in Hr |- *. lia. }
          { intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
          { rewrite Elnz2. destruct (c =? 48)%Z; lia. }
          { intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
            destruct (Z.eq_dec k 0) as [Ek|Hk0].
            - exfalso. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). lia.
            - rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
          { intros _. rewrite znth_zupd_eq by (unfold zlength; lia). change (10 ^ 1)%Z with 10%Z. lia. }
        + (* [comment removed for export] *)
          assert (Hj : j <> 0%Z) by exact K4.
          unfold nz in HL. replace (j =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact Hj). cbn [negb] in HL.
          pose proof (X31H k) as Rt. pose proof (REL k ltac:(lia) ltac:(unfold digz; right; right; split; [reflexivity | exact Hj])) as Et.
          specialize (Hxk Hj).
          pose proof (Z.pow_le_mono_r 10 j 8 ltac:(lia) ltac:(lia)) as P10. change (10 ^ 8)%Z with 100000000%Z in P10.
          pose proof (u32arr_read asegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD.
          zs. rewrite (sx32_wval ws k (znth x k) (eq_sym Et) Rt). set (t := znth x k) in *. clear RD.
          zs. zs. zs.
          rewrite (u32_id (t * 10 + c - 48)) in HL by lia.
          replace (t * 10 + c - 48)%Z with (c + t * 10 + -48)%Z in HL by lia.
          set (v := (c + t * 10 + -48)%Z) in *.
          assert (P10j : (10 ^ j * 10 = 10 ^ (j + 1))%Z) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
          assert (Rv : (0 <= v < 10 ^ (j + 1))%Z) by (subst v; nia).
          assert (Rv2 : (10 ^ (j + 1) <= 1000000000)%Z) by (change 1000000000%Z with (10 ^ 9)%Z; apply Z.pow_le_mono_r; lia).
          pose proof (u32arr_store_ok asegs _ _ _ k _ XW ltac:(lia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ k (Z_to_bv 64 v) XW ltac:(lia)) as XW'. clear XW. store_done'. rename XW' into XW.
          assert (XR' : forall Q : Z -> Prop, (forall i, (0 <= i < 2048)%Z -> Q i -> (i <= k)%Z) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 v)) (zupd x k v) Q).
          { intros Q HQ. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
            intros i0 Hq Hr. specialize (HQ i0 Hq Hr). destruct (Z.eq_dec i0 k) as [->|Hne].
            - rewrite znth_zupd_eq by (unfold zlength; lia). rewrite wval_upd_same by lia. rewrite unsigned_lit by lia. symmetry. apply Z.mod_small. lia.
            - rewrite znth_zupd_neq by lia. rewrite wval_upd_other by lia. apply REL; [lia|]. unfold digz. lia. }
          assert (X31' : X31 (zupd x k v)).
          { intros i0. destruct (Z.eq_dec i0 k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; lia); lia | rewrite znth_zupd_neq by lia; apply X31H]. }
          assert (Hx0' : znth (zupd x k v) 0 <> 0%Z -> (1 <= lnz2)%Z).
          { intros Hx0. rewrite Elnz2. destruct (Z.eqb_spec c 48) as [Ec|Hc48]; [|lia].
            destruct (Z.eq_dec k 0) as [Ek|Hk0].
            - apply Hlnz. intros E0. apply Hx0. rewrite Ek. rewrite znth_zupd_eq by (unfold zlength; lia). subst v t. rewrite Ek, E0, Ec. reflexivity.
            - rewrite znth_zupd_neq in Hx0 by lia. exact (Hlnz Hx0). }
          zs. fixw3. zs. zs.
          rewrite (seqz_land (j + -8)%Z) by lia.
          destruct (Z.eq_dec j 8) as [Ej8|Hj8].
          * (* [comment removed for export] *)
            replace (j + -8 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia).
            replace (j + 1 =? 9)%Z with true in HL by (symmetry; apply Z.eqb_eq; lia). cbv beta iota in HL.
            change (Z.b2z true) with 1%Z.
            zs. fixw3. zs. zs. zs. zs.
            rewrite (Z.land_0_l (j + 1)).
            rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
            replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
            eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f 0%Z (k + 1)%Z lrp (dc + 1)%Z lnz2 1%Z gotrad s').
            all: try assumption; try glia.
            { mk_dfinv. }
            { apply XR'. unfold digz. intros; lia. }
            { rewrite Elnz2; destruct (c =? 48)%Z; lia. }
          * replace (j + -8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
            replace (j + 1 =? 9)%Z with false in HL by (symmetry; apply Z.eqb_neq; lia). cbv beta iota in HL.
            change (Z.b2z false) with 0%Z.
            zs. fixw3. zs. zs. zs. zs.
            replace (Z.land 18446744073709551615 (j + 1)) with (j + 1)%Z by (rewrite Z.land_comm, land_W64; symmetry; apply Z.mod_small; lia).
            try rewrite (Z.add_0_r k).
            rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
            replace (if negb (c =? 48) then (dc + 1)%Z else lnz) with lnz2 in HL by (rewrite Elnz2; destruct (c =? 48)%Z; reflexivity).
            eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev (upd ws (Z.to_nat k) (Z_to_bv 64 v)) sign kmin c (zupd x k v) f (j + 1)%Z k lrp (dc + 1)%Z lnz2 1%Z gotrad s').
            all: try assumption; try glia.
            { mk_dfinv. }
            { apply XR'. unfold digz. intros; lia. }
            { rewrite Elnz2; destruct (c =? 48)%Z; lia. }
            { intros _. rewrite znth_zupd_eq by (unfold zlength; lia). exact (proj2 Rv). } }
      (* [comment removed for export] *)
      zs. brf K3.
      + eapply (G94 m _ lnz); [rewrite K3, Z.eqb_refl; reflexivity | exact DI0].
      + zs. lo96b LOW.
        eapply (G94 _ _ (dc + 1)%Z); [replace (c =? 48)%Z with false by (symmetry; apply Z.eqb_neq; exact K3); reflexivity | mk_dfinv].
    - (* [comment removed for export] *)
      rewrite K1 in HL. change (46 =? 46)%Z with true in HL. unfold nz in HL. cbv beta iota in HL.
      zs. brf K2.
      + (* [comment removed for export] *)
        replace (gotrad =? 0)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb] in HL. injection HL as <-.
        pose proof FC as FC0. ufc2 FC.
        zs. zs. zs.
        rewrite (Eng gotdig Rg).
        unfold dfK_exp in HK.
        change (0 <=? 46)%Z with true in HK. replace (nz gotrad) with true in HK by (unfold nz; symmetry; rewrite Bool.negb_true_iff; apply Z.eqb_neq; exact K2).
        cbn [negb Z.lor Pos.lor Z.eqb Pos.eqb andb] in HK. rewrite Bool.andb_false_r in HK. cbv beta iota in HK.
        assert (DF : dig_facts ws x j k dc lnz) by (unfold dig_facts; splits; try assumption; try glia; exact (conj LW' (conj LX REL))).
        destruct (sh_shlim_neg f) eqn:SN; unfold M64.
        * rewrite (rf_unget_nop f SN) in HK.
          zs. br10 K3. zs.
          stmt HS_C38. eapply NX with (gotdig := gotdig); try eassumption; try glia; try reflexivity.
        * zs. br01 K3.
          stmt HS_C2C. eapply NX with (gotdig := gotdig); try eassumption; try glia; try reflexivity.
      + (* [comment removed for export] *)
        replace (gotrad =? 0)%Z with true in HL by (symmetry; apply Z.eqb_eq; exact K2). cbn [negb] in HL.
        rewrite (surjective_pairing (sh_getc f)) in HL. cbv beta iota in HL.
        zs. zs. zs.
        eapply (LATCH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 ev ws sign kmin c x f j k dc dc lnz gotdig 1%Z s').
        all: try assumption; try glia.
        exact (conj LW' (conj LX REL)).
  Qed.

End Floatscan.


End CeilWrap.
