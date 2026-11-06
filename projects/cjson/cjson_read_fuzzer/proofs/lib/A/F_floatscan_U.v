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
  Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
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

  Hypothesis HS_N2D4 : S_N2D4.
  Hypothesis HS_UK : S_UK.

  (* [comment removed for export] *)
  Ltac fixkg := rewrite ?land2047, ?landW_mod2048.
  Lemma th0_valU : znth th_list 0 = 10384593%Z. Proof using . reflexivity. Qed.
  Lemma mod_add2046 : forall u, ((u + 2046) mod 2048 = ((u - 1) mod 2048 - 1) mod 2048)%Z.
  Proof using . clear. intros u. rewrite Zminus_mod_idemp_l. rewrite <- (Z.mod_add (u - 1 - 1) 1 2048) by flia. f_equal. flia. Qed.

  (* [comment removed for export] *)
  Lemma L_UPX : forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (x : list Z) (h : bool) (rp a z e2 : Z),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    (sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
    xrel ws x (zone h a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 42)%Z -> (-2^20 <= rp <= 2^20)%Z -> (-2^20 <= e2 <= 0)%Z ->
    up_K sign rp a z e2 x = Some yR ->
    evt asegs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x98b4c) fct None m (seg_rom asegs)).
  Proof using HS_N2D4.
    intros until e2. intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Rrp Re2 HK. unfold up_K in HK.
    destruct (df_dn_loop FUEL_SCALE _) as [s'|] eqn:HL; [|discriminate HK].
    stmt HS_N2D4. eapply (NX 2000%nat); try eassumption; try (cbn; flia).
    intros E; specialize (Rzh E); cbn; flia.
  Qed.

  (* [comment removed for export] *)
  Lemma L_U1C4 : S_U1C4.
  Proof using HS_N2D4 HS_UK SG1 SPF SPF2 SPT T1.
    unfold F_floatscan_common.S_U1C4, F_floatscan_common.SU1C4. induction fo as [|fo IH]; intros m; intros until s'; intros DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Haz Rrp Re2 HL HK; [discriminate HL|].
    pose proof DI as DI'. dest_dfinv DI'.
    destruct XR as (LW' & LX & REL).
    rewrite df_up_loop_step in HL. unfold df_up_cond in HL. cbn [us_rp us_x us_a] in HL.
    change (9 * LD_B1B_DIG)%Z with 36%Z in HL. rewrite th0_valU in HL.
    pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(flia)) as Rrs.
    assert (Hrs1 : (0 < (z - a) mod 2048)%Z) by (clear -Haz Ra Rz Rrs; Z.div_mod_to_equations; flia).
    (* [comment removed for export] *)
    assert (GHEAD : forall m' ws' x' (h' : bool) (a' z' rp' : Z) (x6' x7' x16' x28' x29' x30' x31' : word),
      dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
      xrel ws' x' (zone h' a' z') -> X31 x' -> (0 <= a' < 2048)%Z -> (0 <= z' < 2048)%Z -> (h' = false -> z' <= 42)%Z -> a' <> z' ->
      (-2^20 <= rp' <= 45)%Z ->
      df_up_loop fo (mkUS rp' a' z' (e2 - 29) x') = Some s' ->
      evt asegs POST
        (MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp') x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a'))
                 (Z_to_bv 64 z') (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp') x24 x25 x26 x27 x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x98a3c) fct None m' (seg_rom asegs))).
    { intros m' ws' x' h' a' z' rp' x6' x7' x16' x28' x29' x30' x31' DI2 XR2 X312 Ra' Rz' Rzh' Haz' Rrp' HL'.
      eapply (IH m' x1 x6' x7' x8 x9 x16' x20 x22 x24 x25 x26 x27 x28' x29' x30' x31' Ft fct j0 b96 ev ws' sign k c x' h' rp' a' z' (e2 - 29)%Z s');
        [exact DI2 | exact RJ | exact Hk | exact FOK | exact FRM' | exact Hsg | flia | exact XR2 | exact X312 | flia | exact Rzh' | exact Haz' | flia | flia | exact HL' | exact HK]. }
    clear IH.
    (* [comment removed for export] *)
    assert (GBODY : forall (x16' : word), (rp <= 36)%Z ->
      match df_up_body (mkUS rp a z e2 x) with Some s'' => df_up_loop fo s'' | None => None end = Some s' ->
      evt asegs POST
        (MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16' (Z_to_bv 64 (XA + 4 * a))
                 (Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x98a4c) fct None m (seg_rom asegs))).
    { intros x16' Rrp36 HB. clear HL HK. unfold df_up_body in HB. cbn [us_a us_z us_x us_rp us_e2] in HB. change MASK with 2047%Z in HB.
      destruct (df_upk_loop FUEL_RING a _) as [[k1 carry1 z1 x1']|] eqn:HUK; [|discriminate HB].
      unfold FUEL_RING in HUK. rewrite land2047 in HUK.
      (* [comment removed for export] *)
      zs. zs. zs. zs. fixkg. rewrite mod_add2047.
      stmt HS_UK.
      eapply (NX 2050%nat) with (h := h) (x := x) (s1 := mkUK k1 carry1 z1 x1');
        [exact DI | exact FOK | exact FRM' | exact (conj LW' (conj LX REL)) | exact X31H | flia | flia | apply Z.mod_pos_bound; flia | | flia | exact HUK | ].
      { unfold inring. rewrite Zminus_mod_idemp_l. clear -Hrs1 Rrs Ra Rz. Z.div_mod_to_equations. flia. }
      clear NX.
      intros m' ws' x7' x18' x29' x30' x31' h' DI2 XR2 X312 Hk1 Rc1 Rz1 Hlow1 Haz1.
      cbn [uk_x uk_z uk_k uk_carry] in DI2, XR2, X312, Hk1, Rc1, Rz1, Hlow1, Haz1 |- *. subst k1.
      clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC HUK Rrs Hrs1 LW' LX REL X31H.
      pose proof DI2 as DI'. dest_dfinv DI'. destruct XR2 as (LW2 & LX2 & REL2).
      assert (Rzh1 : (h' = false -> z1 <= 42)%Z) by (intros E; destruct (Hlow1 E) as [E0 R0]; specialize (Rzh E0); flia).
      pose proof (Z.mod_pos_bound (z1 - a) 2048 ltac:(flia)) as Rrs2.
      unfold nz in HB.
      (* [comment removed for export] *)
      zs. fixw3. fixw. replace (e2 + -29)%Z with (e2 - 29)%Z by flia. zs. zs. brf K1.
      - (* [comment removed for export] *)
        replace (negb (carry1 =? 0)) with true in HB by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; flia).
        rewrite !land2047 in HB.
        zs. zs. fixkg. replace (a + -1)%Z with (a - 1)%Z by flia.
        pose proof (Z.mod_pos_bound (a - 1) 2048 ltac:(flia)) as Ra'. set (a' := ((a - 1) mod 2048)%Z) in *.
        assert (FRONT : forall q0, (0 <= q0 < 2048)%Z -> inring a' z1 q0 -> q0 <> a' -> z1 <> a' -> inring a z1 q0).
        { intros q0 Hq H1 H2 H3. apply (inring_front a z1 q0); try flia; assumption. }
        assert (FULL : z1 = a' -> forall q0, (0 <= q0 < 2048)%Z -> q0 <> a' -> inring a z1 q0).
        { intros E q0 Hq Hne. unfold inring. clear -E Hq Hne Ra Rz1 Ra' Haz1 Rrs2. subst a'. Z.div_mod_to_equations. nia. }
        clearbody a'. clear Rrs2.
        (* [comment removed for export] *)
        assert (TAIL : forall m2 ws2 x2 (h2 : bool) (z2 : Z) (x5' x6' x17' : word),
          dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws2 sign fR ->
          xrel ws2 x2 (fun i => zone h2 a' z2 i /\ i <> a') -> X31 x2 -> (0 <= z2 < 2048)%Z -> (h2 = false -> z2 <= 42)%Z -> a' <> z2 ->
          df_up_loop fo (mkUS (rp + 9) a' z2 (e2 - 29) (zupd x2 a' carry1)) = Some s' ->
          evt asegs POST
            (MS (mkR x1 SPv gp TPv x5' x6' x7' x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) (Z_to_bv 64 carry1) x17'
                     (Z_to_bv 64 z1) (Z_to_bv 64 a') x20 (Z_to_bv 64 (e2 - 29)) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 z2) x29' x30' x31')
                Ft (Z_to_bv 64 0x98b20) fct None m2 (seg_rom asegs))).
        { intros m2 ws2 x2 h2 z2 x5' x6' x17' DI3 XR3 X313 Rz2 Rzh2 Haz2 HL3.
          clear MI MU WM FRhi ST BY SSP1 SSP2 LOW ERR XW LW FC DI2 LW2 LX2 REL2 X312 HB.
          pose proof DI3 as DI'. dest_dfinv DI'. destruct XR3 as (LW3 & LX3 & REL3).
          zs. zs. zs. fix_idx.
          pose proof (u32arr_store_ok asegs _ _ _ a' _ XW ltac:(flia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ a' (Z_to_bv 64 carry1) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
          zs. zs. zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 9 + 0)%Z with (rp + 9)%Z by flia. zs.
          eapply (GHEAD _ (upd ws2 (Z.to_nat a') (Z_to_bv 64 carry1)) (zupd x2 a' carry1) h2 a' z2 (rp + 9)%Z);
            [mk_dfinv | | | flia | flia | exact Rzh2 | flia | flia | exact HL3].
          * split; [rewrite upd_length; exact LW3|]. split; [rewrite zupd_length; exact LX3|].
            intros q0 Hq Hr. destruct (Z.eq_dec q0 a') as [->|Hne].
            -- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
            -- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL3; [flia|]. split; [exact Hr | exact Hne].
          * intros q0. destruct (Z.eq_dec q0 a') as [->|Hne]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X313]. }
        zs. brf K2.
        + (* [comment removed for export] *)
          replace (a' =? z1) with false in HB by (symmetry; apply Z.eqb_neq; flia). cbv beta iota in HB.
          zs.
          eapply (TAIL m' ws' x1' h' z1); [exact DI2 | | exact X312 | flia | exact Rzh1 | flia | exact HB].
          split; [exact LW2|]. split; [exact LX2|]. intros q0 Hq [Hr Hne]. apply REL2; [flia|].
          destruct Hr as [Hr | Hr]; [left | right; exact Hr]. apply (FRONT q0); try flia. exact Hr.
        + (* [comment removed for export] *)
          replace (a' =? z1) with true in HB by (symmetry; apply Z.eqb_eq; flia). cbv beta iota in HB.
          pose proof (Z.mod_pos_bound (z1 - 1) 2048 ltac:(flia)) as Rz2. set (z2 := ((z1 - 1) mod 2048)%Z) in *.
          zs. zs. zs. fix_idx. zs. fixkg. rewrite mod_add2046. fold z2.
          pose proof (Z.mod_pos_bound (z2 - 1) 2048 ltac:(flia)) as Rz3. set (z3 := ((z2 - 1) mod 2048)%Z) in *.
          assert (Hz2in : inring a z1 z2) by (apply (FULL ltac:(flia)); [flia | subst z2; clear -Rz1 Rz2 K2; Z.div_mod_to_equations; flia]).
          assert (Hz3in : inring a z1 z3) by (apply (FULL ltac:(flia)); [flia | subst z3 z2; clear -Rz1 Rz2 Rz3 K2; Z.div_mod_to_equations; flia]).
          assert (Hz23 : z3 <> z2) by (subst z3; clear -Rz2 Rz3; Z.div_mod_to_equations; flia).
          assert (LOWz2 : z1 <> 0%Z -> z2 = (z1 - 1)%Z) by (intros; subst z2; apply Z.mod_small; flia).
          assert (Hz21 : z2 <> z1) by (subst z2; clear -Rz1; Z.div_mod_to_equations; flia).
          clearbody z2 z3.
          pose proof (X312 z3) as Rt3. pose proof (REL2 z3 ltac:(flia) (or_introl Hz3in)) as Et3.
          pose proof (X312 z2) as Rt2. pose proof (REL2 z2 ltac:(flia) (or_introl Hz2in)) as Et2.
          zs. zs. fix_idx.
          pose proof (u32arr_read asegs _ _ _ z2 _ _ XW (nth_error_wnth ws' z2 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD2.
          zs. rewrite (sx32_wval ws' z2 (znth x1' z2) (eq_sym Et2) Rt2). clear RD2.
          pose proof (u32arr_read asegs _ _ _ z3 _ _ XW (nth_error_wnth ws' z3 ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RD3.
          zs. rewrite (sx32_wval ws' z3 (znth x1' z3) (eq_sym Et3) Rt3). clear RD3.
          set (t3 := znth x1' z3) in *. set (t2 := znth x1' z2) in *.
          zs.
          assert (Rt23 : (0 <= Z.lor t3 t2 < 2^31)%Z).
          { split; [apply Z.lor_nonneg; flia|]. apply (Bytes.lor_lt_pow2 t3 t2 31); flia. }
          pose proof (u32arr_store_ok asegs _ _ _ z3 _ XW ltac:(flia) eq_refl) as SOK.
          zs.
          pose proof (u32arr_write asegs _ _ _ z3 (Z_to_bv 64 (Z.lor t3 t2)) XW ltac:(flia)) as XW'. clear XW. store_done'. rename XW' into XW.
          zs.
          eapply (TAIL _ (upd ws' (Z.to_nat z3) (Z_to_bv 64 (Z.lor t3 t2))) (zupd x1' z3 (Z.lor t3 t2)) (if (z1 =? 0)%Z then true else h') z2);
            [mk_dfinv | | | flia | | flia | exact HB].
          * split; [rewrite !upd_length; exact LW2|]. split; [rewrite !zupd_length; exact LX2|].
            intros q0 Hq [Hr Hne].
            destruct (Z.eq_dec q0 z3) as [->|Hne3].
            -- rewrite znth_zupd_eq by (unfold zlength; flia). rewrite wval_upd_same by flia. rewrite unsigned_lit by flia. symmetry. apply Z.mod_small. flia.
            -- rewrite znth_zupd_neq by flia. rewrite wval_upd_other by flia. apply REL2; [flia|]. left.
               apply (FULL ltac:(flia) q0 Hq Hne).
          * intros q0. destruct (Z.eq_dec q0 z3) as [->|Hne3]; [rewrite znth_zupd_eq by (unfold zlength; flia); flia | rewrite znth_zupd_neq by flia; apply X312].
          * destruct (Z.eqb_spec z1 0) as [Ez1|Hz1]; [intros E; discriminate E|]. intros E. specialize (Rzh1 E). specialize (LOWz2 Hz1). flia.
      - (* [comment removed for export] *)
        replace (negb (carry1 =? 0)) with false in HB by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; flia).
        eapply (GHEAD m' ws' x1' h' a z1 rp); [exact DI2 | exact (conj LW2 (conj LX2 REL2)) | exact X312 | flia | flia | exact Rzh1 | flia | flia | exact HB]. }
    (* [comment removed for export] *)
    zs. brsf K0.
    - (* [comment removed for export] *)
      replace (rp <? 36) with true in HL by (symmetry; apply Z.ltb_lt; flia). cbn [orb] in HL.
      eapply (GBODY x16); [flia | exact HL].
    - replace (rp <? 36) with false in HL by (symmetry; apply Z.ltb_ge; flia). cbn [orb] in HL.
      zs. brf K1; rewrite ?land_W64 in K1.
      + (* [comment removed for export] *)
        replace (rp =? 36) with false in HL by (symmetry; apply Z.eqb_neq; mlia). cbn [andb] in HL. injection HL as <-.
        cbn [us_rp us_a us_z us_e2 us_x] in HK.
        eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | flia | flia | exact HK].
      + replace (rp =? 36) with true in HL by (symmetry; apply Z.eqb_eq; mlia). cbn [andb] in HL.
        (* [comment removed for export] *)
        assert (Hain : inring a z a) by (unfold inring; rewrite Z.sub_diag; change (0 mod 2048)%Z with 0%Z; exact Hrs1).
        pose proof (X31H a) as Rta. pose proof (REL a ltac:(flia) (or_introl Hain)) as Eta.
        pose proof (u32arr_read asegs _ _ _ a _ _ XW (nth_error_wnth ws a ltac:(flia) ltac:(flia)) ltac:(flia) eq_refl) as RDa.
        zs. rewrite (sx32_wval ws a (znth x a) (eq_sym Eta) Rta). set (ta := znth x a) in *.
        zs. brf K2.
        * (* [comment removed for export] *)
          replace (ta <? 10384593) with false in HL by (symmetry; apply Z.ltb_ge; flia). injection HL as <-.
          cbn [us_rp us_a us_z us_e2 us_x] in HK.
          eapply L_UPX; [exact DI | exact RJ | exact Hk | assumption | assumption | exact Hsg | flia | exact (conj LW' (conj LX REL)) | exact X31H | flia | exact Rzh | flia | flia | exact HK].
        * replace (ta <? 10384593) with true in HL by (symmetry; apply Z.ltb_lt; flia).
          eapply (GBODY _); [flia | exact HL].
  Qed.

  (* [comment removed for export] *)
  Lemma L_U1A8 : S_U1A8.
  Proof using HS_N2D4 HS_UK SG1 SPF SPF2 SPT T1.
    intros fo m; intros until s'. intros _ DI RJ Hk FOK FRM' Hsg Ra XR X31H Rz Rzh Haz Rrp Re2 HL HK. pose proof DI as DI0. dest_dfinv DI.
    zs. zs. fix_idx. zs. fixw3. fixw. try replace (rp + 0)%Z with rp by flia. zs.
    pose proof L_U1C4 as NX. unfold F_floatscan_common.S_U1C4, F_floatscan_common.SU1C4 in NX. eapply NX; try eassumption; try flia.
  Qed.

End Floatscan.


End CeilWrap.
