(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_memcpy F_memchr F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_multf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_multf3.F_multf3_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_multf3 F_divtf3 F_divtf3_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_subtf3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_subtf3.F_addtf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_subtf3 F_letf2 F_getf2 F_floatsitf F_floatunsitf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg.F_extenddftf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_scalbn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_shgetc_proofs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_shgetc_proofs.F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_scanexp.F_rscan_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_scanexp.F_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_scalbnl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_floatscan_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_floatscan_common.F_fmodl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_scanexp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_floatscan_common.
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
    destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold F_floatscan_common.Wfs, FS_DEPTH, RERRNO in MU; unfold F_floatscan_common.hi_cells in FRhi;
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
  Ltac bury_disj := try bury SEP; try bury SG2; try bury SG3; try bury SE_T; try bury Hpok.
  Ltac unbury := unfold hide2 in *.
  Ltac zs0 := unstash; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zs1 := hush; unfold hide in SEP, SE_T; unfold hide2 in SEP, SE_T; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
  (* [comment removed for export] *)
  Ltac dest_dfinv H := let FI := fresh "FI" in let FL := fresh "FL" in let XW := fresh "XW" in let LW := fresh "LW" in let FC := fresh "FC" in
    destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
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
    destruct H as (FI & FL & XW & LW & FC); pose proof FI as FI'; dest_finv FI'; pose proof FL as FL'; dest_framL FL'.
  Ltac mk_winv := unfold F_floatscan_common.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|]; split; [first [assumption | rewrite ?upd_length; assumption] | hyp].
  Notation POST := (fs_post m0).

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
  Lemma lor_b2z_zero : forall p q, Z.lor (Z.b2z p) (Z.b2z q) = 0%Z <-> (p = false /\ q = false).
  Proof using . clear. destruct p, q; cbn; split; intros H; try discriminate H; try (destruct H; congruence); auto. Qed.
  Lemma lxor_pos_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((0 <? Z.lxor a b) = negb (a =? b))%Z.
  Proof using .
    clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne]; cbn.
    - rewrite Z.lxor_nilpotent. reflexivity.
    - apply Z.ltb_lt. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
  Qed.
  Lemma lxor_lt1_iff : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> ((Z.lxor a b <? 1) = (a =? b))%Z.
  Proof using .
    clear. intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|Hne].
    - rewrite Z.lxor_nilpotent. reflexivity.
    - apply Z.ltb_ge. assert (Z.lxor a b <> 0)%Z by (intros E; apply (proj1 (Z.lxor_eq_0_iff a b)) in E; flia). assert (0 <= Z.lxor a b)%Z by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; flia). flia.
  Qed.

  Lemma L_UK : S_UK.
  Proof using Hp SE_T SG1 SG3 SPF SPF2 SPT T1.
    unfold F_floatscan_common.S_UK. induction n as [|n IH]; intros m; intros until s1; intros DI FOK FRM' XR X31H Ra Rz Rk Kin Rc HL CONT; [discriminate HL|].
    pose proof DI as DI'. dest_dfinv DI'.
    destruct XR as (LW' & LX & REL).
    rewrite df_upk_loop_step in HL. unfold df_upk_body in HL. cbn [uk_k uk_x uk_z uk_carry] in HL. change MASK with 2047%Z in HL.
    pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs. unfold inring in Kin. pose proof (Z.mod_pos_bound (k - a) 2048 ltac:(flia)) as Rks.
    pose proof (X31H k) as Rt. pose proof (REL k ltac:(flia) (or_introl Kin)) as Et.
    pose proof (u32arr_read bsegs _ _ _ k _ _ XW (nth_error_wnth ws k ltac:(clear -Rk; flia) ltac:(clear -Rk LW'; flia)) ltac:(clear -Rk; flia) eq_refl) as RD.
    zs. zs. fix_idx. zs. rewrite zx32_wval, <- Et. set (t := znth x k) in *. clear RD.
    zs. zs.
    set (tmp := (Z.shiftl t 29 + carry)%Z) in *.
    assert (Rtmp : (0 <= tmp < 2^60 + 2^31)%Z) by (subst tmp; rewrite Z.shiftl_mul_pow2 by flia; flia).
    assert (Etmp : u64 tmp = tmp) by (unfold u64; apply Z.mod_small; flia). rewrite !Etmp in HL.
    pose proof (Z.mod_pos_bound (z - 1) 2048 ltac:(flia)) as Rkm. set (km := ((z - 1) mod 2048)%Z) in *.
    rewrite !land2047 in HL. fold km in HL.
    (* [comment removed for export] *)
    assert (G240 : forall (v carry' cand : Z) m' ws',
      (0 <= v < 2^31)%Z -> (0 <= carry' < 2^31)%Z -> cand = (if v =? 0 then k else z)%Z ->
      dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
      (forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' a z' ii -> ii = k \/ zone h a z ii) -> xrel ws' (zupd x k v) (zone h' a z')) ->
      (let x' := zupd x k v in
       let z' := (if (k =? km) && negb (k =? a) && (znth x' k =? 0) then k else z)%Z in
       let s' := mkUK k carry' z' x' in
       match (if (k =? a)%Z then inr s' else inl (mkUK ((k - 1) mod 2048) carry' z' x')) with
       | inl s'' => df_upk_loop n a s''
       | inr s'' => Some s''
       end = Some s1) ->
      evt bsegs POST
        (MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
                 (Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (XA + 4 * k)) (Z_to_bv 64 v) (Z_to_bv 64 cand) x31)
            Ft (Z_to_bv 64 0x98238) fct None m' (seg_rom bsegs))).
    { intros v carry' cand m' ws' Rv Rc' Hcand DI2 XRz HB. cbv zeta in HB.
      clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC.
      pose proof DI2 as DI2'. dest_dfinv DI2'.
      set (x' := zupd x k v) in *.
      assert (X31' : X31 x').
      { intros ii. subst x'. destruct (Z.eq_dec ii k) as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X31H]. }
      assert (Exk : znth x' k = v) by (subst x'; rewrite znth_zupd_eq by (unfold zlength; flia); reflexivity). rewrite Exk in HB.
      assert (Hkm1 : k <> a -> inring a z ((k - 1) mod 2048) /\ inring a k ((k - 1) mod 2048)).
      { intros Hka. unfold inring. rewrite !Zminus_mod_idemp_l. clear -Kin Hka Ra Rz Rk Rrs Rks. Z.div_mod_to_equations. nia. }
      (* [comment removed for export] *)
      zs. zs. zs. fixkg. replace (z + -1)%Z with (z - 1)%Z by flia. fold km. zs. zs. zs. zs. zs.
      rewrite (lxor_pos_iff k km), (lxor_lt1_iff k a) by flia.
      (* [comment removed for export] *)
      assert (LATCH : forall z' (x29' x30' : word),
        z' = (if (k =? km) && negb (k =? a) && (v =? 0) then k else z)%Z ->
        evt bsegs POST
          (MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 z) (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry') x17
                   (Z_to_bv 64 z') (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 km) x29' x30' (Z_to_bv 64 (Z.b2z (negb (k =? km)))))
              Ft (Z_to_bv 64 0x981d8) fct None m' (seg_rom bsegs))).
      { intros z' x29' x30' Hz'. rewrite <- Hz' in HB.
        assert (Rz' : (0 <= z' < 2048)%Z) by (rewrite Hz'; destruct (_ && _ && _); flia).
        zs. zs. brf K4.
        - (* [comment removed for export] *)
          replace (k =? a)%Z with true in HB by (symmetry; apply Z.eqb_eq; flia). injection HB as <-.
          assert (Ez' : z' = z) by (rewrite Hz'; replace (k =? a)%Z with true by (symmetry; apply Z.eqb_eq; flia); cbn [negb andb]; destruct (k =? km)%Z; reflexivity).
          clear Hz'. subst z'.
          replace (Z_to_bv 64 k) with (Z_to_bv 64 a) by (f_equal; flia).
          eapply (CONT _ _ _ _ _ _ _ h); [mk_dfinv | cbn [uk_x uk_z]; apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | cbn; flia | cbn; flia | cbn; flia | cbn; intros E; split; [exact E | flia] | cbn; flia].
        - replace (k =? a)%Z with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
          zs. rewrite land2047, ?landW_mod2048. replace (k + -1)%Z with (k - 1)%Z by flia.
          destruct (Hkm1 ltac:(flia)) as [Hin1 Hin2].
          assert (Hz2 : z' = (if (k =? km) && (v =? 0) then k else z)%Z).
          { rewrite Hz'. replace (k =? a)%Z with false by (symmetry; apply Z.eqb_neq; flia). cbn [negb]. destruct (k =? km)%Z; reflexivity. }
          clear Hz'.
          replace ((k =? km) && negb false && (v =? 0))%Z with ((k =? km) && (v =? 0))%Z in HB by (destruct (k =? km)%Z; reflexivity).
          destruct ((k =? km) && (v =? 0))%Z eqn:Ec; subst z'.
          + (* [comment removed for export] *)
            assert (Ekm : k = km) by (apply andb_prop in Ec; destruct Ec as [Ec _]; apply Z.eqb_eq in Ec; exact Ec).
            destruct (Z.eq_dec z 0) as [Ez0|Hz0].
            * (* [comment removed for export] *)
              assert (Ek : k = 2047%Z) by (rewrite Ekm; subst km; rewrite Ez0; reflexivity).
              eapply IH with (h := true) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
              -- destruct Hq as [Hq | [_ Hq]]; [| left; flia]. right. left.
                 unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ez0 Ek. Z.div_mod_to_equations. nia.
              -- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
                 intros E. destruct (Hlow3 E) as [E2 _]. discriminate E2.
            * assert (Ek : k = (z - 1)%Z) by (rewrite Ekm; subst km; apply Z.mod_small; flia).
              eapply IH with (h := h) (z := k) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii Rii Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin2 | flia | exact HB | ].
              -- destruct Hq as [Hq | [Hh Hq]].
                 { right. left. unfold inring in Hq |- *. clear -Hq Kin Ra Rz Rk Rrs Rks K4 Rii Ek. Z.div_mod_to_equations. nia. }
                 destruct (Z.eq_dec ii k) as [->|Hne]; [left; reflexivity | right; right; split; [exact Hh | flia]].
              -- intros mm ws2 y7 y18 y29 y30 y31 h'' DI3 XR3 X313 Hk3 Rc3 Rz3 Hlow3 Haz3. eapply (CONT _ _ _ _ _ _ _ h''); try eassumption.
                 intros E. destruct (Hlow3 E) as [E2 R2]. split; [exact E2 | flia].
          + (* [comment removed for export] *)
            eapply IH with (h := h) (z := z) (x := x'); [mk_dfinv | assumption | assumption | apply XRz; intros ii _ Hq; right; exact Hq | exact X31' | flia | flia | apply Z.mod_pos_bound; flia | exact Hin1 | flia | exact HB | exact CONT]. }
      zs. brf K3.
      - (* [comment removed for export] *)
        eapply LATCH. symmetry.
        destruct (Z.eqb_spec k km); destruct (Z.eqb_spec k a); cbn [negb andb Z.b2z Z.lor] in K3 |- *; try reflexivity. exfalso. apply K3. reflexivity.
      - (* [comment removed for export] *)
        apply (proj1 (lor_b2z_zero _ _)) in K3. destruct K3 as [K3a K3b].
        apply (proj1 (Bool.negb_false_iff _)) in K3a.
        zs. zs.
        eapply LATCH. rewrite K3a, K3b. cbn [negb andb]. exact Hcand. }
    zs. zs. brf K2.
    - (* [comment removed for export] *)
      replace (1000000000 <? tmp)%Z with false in HL by (symmetry; apply Z.ltb_ge; flia).
      rewrite (u32_id tmp) in HL by flia.
      zs.
      pose proof (u32arr_store_ok bsegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
      zs.
      pose proof (u32arr_write bsegs _ _ _ k (Z_to_bv 64 tmp) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
      assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' a z' ii -> ii = k \/ zone h a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 tmp)) (zupd x k tmp) (zone h' a z')).
      { intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
        intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
        - rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
        - rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
      zs. zs. brf K5.
      + (* [comment removed for export] *) eapply (G240 tmp 0%Z k); [flia | flia | replace (tmp =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
      + zs. eapply (G240 tmp 0%Z z); [flia | flia | replace (tmp =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
    - (* [comment removed for export] *)
      replace (1000000000 <? tmp)%Z with true in HL by (symmetry; apply Z.ltb_lt; flia).
      assert (Rq : (0 <= tmp / 1000000000 < 2^31)%Z) by (split; [apply Z.div_pos; flia | apply Z.div_lt_upper_bound; flia]).
      pose proof (Z.mod_pos_bound tmp 1000000000 ltac:(flia)) as Rr.
      rewrite (u32_id (tmp / 1000000000)) in HL by flia. rewrite (u32_id (tmp mod 1000000000)) in HL by flia.
      zs. zs. zs. showall.
      rewrite (magic_div_1e9_reg tmp) by flia.
      zs. zs.
      replace (tmp - tmp / 1000000000 * 1000000000)%Z with (tmp mod 1000000000)%Z by (rewrite Zmod_eq_full by flia; flia).
      pose proof (u32arr_store_ok bsegs _ _ _ k _ XW ltac:(flia) eq_refl) as SOK.
      zs.
      pose proof (u32arr_write bsegs _ _ _ k (Z_to_bv 64 (tmp mod 1000000000)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
      assert (XRz : forall (h' : bool) z', (forall ii, (0 <= ii < 2048)%Z -> zone h' a z' ii -> ii = k \/ zone h a z ii) -> xrel (upd ws (Z.to_nat k) (Z_to_bv 64 (tmp mod 1000000000))) (zupd x k (tmp mod 1000000000)) (zone h' a z')).
      { intros h' z' Hsub. split; [rewrite upd_length; exact LW'|]. split; [rewrite zupd_length; exact LX|].
        intros ii Hq Hr. destruct (Z.eq_dec ii k) as [->|Hne].
        - rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
        - rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL; [flia |]. destruct (Hsub ii Hq Hr) as [E|Hz0]; [exfalso; flia | exact Hz0]. }
      zs. zs. brf K5.
      + (* [comment removed for export] *) zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z z); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
      + zs. eapply (G240 (tmp mod 1000000000)%Z (tmp / 1000000000)%Z k); [flia | flia | replace (tmp mod 1000000000 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; flia); reflexivity | mk_dfinv | exact XRz | cbv beta iota in HL; exact HL].
  Qed.

End Floatscan.


End CeilWrap.
