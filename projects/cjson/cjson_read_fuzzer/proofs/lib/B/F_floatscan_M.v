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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.


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
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                           clear - HI SPT SEP SE_T SG1 SG2 SG3 SPLO SPF SPF2 Q1 T0 T1 Hp HP64;
                           unfold F_floatscan_common.hide, F_floatscan_common.hide2, sf_hide in *; Zify.zify; xlia zchecker ].
  Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | sec_tier | tlia | split; [ tlia | exact I ] ].
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

  Hypothesis HS_T : S_T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma L_DD0 : S_DD0.
  Proof using Hp Q1 SE_T SG1 SG3 SPF SPLO SPT.
    intros m; intros until Y. intros _ DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
    zs. call_split 80%Z (eapply mul_callE with (X := X) (Y := Y); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
    eapply L_RET1; try eassumption; try glia; try mk_finv; try mk_framL.
  Qed.

  (* [comment removed for export] *)
  Ltac some_snd H := apply (f_equal (fun o : option (shfile * Z) => match o with Some pr => snd pr | None => 0%Z end)) in H; cbv beta iota delta [snd] in H.

  (* [comment removed for export] *)
  Lemma L_DD28 : forall m (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      j0 b96 ev ws sign k c (X Y : Z),
    dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
    yR = f128_mul X Y ->
    evt bsegs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x97d20) fct None m (seg_rom bsegs)).
  Proof using Hp Q1 SE_T SG1 SG3 SPF SPLO SPT c0 f0 fc fuelc kmin0 post pre.
    intros until Y. intros DI RJ Hk FOK FRM' Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h. pose proof (lo64_range Y) as R2l. pose proof (hi64_range Y) as R2h.
    zs. zs. zs. zs. zs.
    pose proof L_DD0 as NX. unfold F_floatscan_common.S_DD0 in NX. eapply NX; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_DD24 : S_DD24.
  Proof using Hp Q1 SE_T SG1 SG3 SPF SPLO SPT.
    intros m; intros until u. intros _ DI RJ Hk FOK FRM' Ru Hy. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof (lo64_range X) as R1l. pose proof (hi64_range X) as R1h.
    zs. callx (eapply floatunsitf_callv with (u := u); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
    eapply L_DD28; try eassumption; try mk_dfinv.
  Qed.

  (* [comment removed for export] *)
  Ltac pose_rd0 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with XW2 : u32arr bsegs mm _ ?wsx |- _ =>
      let R := fresh "RD" in
      pose proof (u32arr_read bsegs _ _ _ 0%Z _ _ XW2 (nth_error_wnth wsx 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as R;
      replace (XA + 4 * 0)%Z with XA in R by lia end end.
  Lemma p10s_lit : forall j, (0 <= j <= 7)%Z -> (0 <= znth p10s j < 2^31)%Z.
  Proof using . clear. intros j Hj. destruct (p10s_range j Hj) as [R _]. lia. Qed.

  Lemma L_M : S_M.
  Proof using HS_T Hp Q1 SE_T SG1 SG3 SPF SPF2 SPLO SPT T1.
    intros m; intros until kz. intros _ DI RJ Hk FOK FRM' Hsg XR X31H Rkz Hx0 Rlnz Rrp HK. pose proof DI as DI0. dest_dfinv DI. bury_disj.
    (nelim XR 3%nat; intros LW' LX REL).
    unfold dfK_mid in HK.
    assert (Kin0 : inring 0 kz 0) by (unfold inring; rewrite !Z.sub_0_r, !Z.mod_small by lia; lia).
    pose proof (X31H 0%Z) as Rt0. pose proof (REL 0%Z ltac:(lia) Kin0) as Et0.
    set (x0 := znth x 0) in *.
    (* [comment removed for export] *)
    zs. fixw3. fixw. try replace (lnz + 0)%Z with lnz by lia.
    zs. zs. brs K1.
    { (* [comment removed for export] *)
      replace (lnz <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in HK.
      stmt HS_T. eapply NX; try eassumption; try glia. exact (conj LW' (conj LX REL)). }
    replace (lnz <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
    zs. zs. brs K2.
    { (* [comment removed for export] *)
      replace (rp <? 18)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r in HK. cbv iota in HK.
      stmt HS_T. eapply NX; try eassumption; try glia. exact (conj LW' (conj LX REL)). }
    replace (rp <? 18)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia).
    zs. fixw3. fixw. try replace (rp + 0)%Z with rp by lia.
    zs. brs K3.
    { (* [comment removed for export] *)
      replace (lnz <=? rp)%Z with false in HK by (symmetry; apply Z.leb_gt; lia). cbn [andb] in HK.
      stmt HS_T. eapply NX; try eassumption; try glia. exact (conj LW' (conj LX REL)). }
    replace (lnz <=? rp)%Z with true in HK by (symmetry; apply Z.leb_le; lia). cbn [andb] in HK.
    (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ _ 0%Z _ _ XW (nth_error_wnth ws 0%Z ltac:(lia) ltac:(lia)) ltac:(lia) eq_refl) as RD0.
    replace (XA + 4 * 0)%Z with XA in RD0 by lia.
    zs. zs. brf K4.
    - (* [comment removed for export] *)
      replace (rp =? 9)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
      zs. zs. brs K5.
      + (* [comment removed for export] *)
        assert (Rrp2 : (10 <= rp <= 17)%Z) by lia.
        replace (rp <? 9)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
        zs. rewrite (Z.shiftl_mul_pow2 rp 1) by lia. change (2^1)%Z with 2%Z.
        zs. zs. fixw3. fixw.
        zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0).
        zs. fixw3. fixw. zs. fixw3. fixw.
        match goal with |- context [Z_to_bv 64 (?e + 27)%Z] => replace (e + 27)%Z with (53 - 3 * (rp - 9))%Z by lia end.
        set (bitlim := (53 - 3 * (rp - 9))%Z) in *.
        (* [comment removed for export] *)
        assert (G94 : forall (x10' : word), yR = f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10))) ->
          evt bsegs POST
            (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10' (Z_to_bv 64 30) x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
                     (Z_to_bv 64 8) x19 x20 (Z_to_bv 64 x0) x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
                Ft (Z_to_bv 64 0x98a8c) fct None m (seg_rom bsegs))).
        { intros x10' Hy. clear HK.
          zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
          set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
          zs. zs. zs. zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
          set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
          zs. zs. zs. zs.
          zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
          set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
          zs. zs. fixw3. fixw. zs. zs. rewrite (Z.shiftl_mul_pow2 (rp + -10)) by lia. change (2^2)%Z with 4%Z. zs. zs.
          (* [comment removed for export] *)
          assert (G_DC : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
            dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
            evt bsegs POST
              (MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (rp - 10))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
                       y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                  Ft (Z_to_bv 64 0x98ad4) fct None m2 (seg_rom bsegs))).
          { intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
            pose proof DI2 as DI'. dest_dfinv DI'.
            pose proof (p10s_lit (rp - 10)%Z ltac:(lia)) as Rp.
            zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
            zs. eapply L_DD28; try eassumption; try mk_dfinv. }
          assert (Hc : (rp = 10 \/ rp = 11 \/ rp = 12 \/ rp = 13 \/ rp = 14 \/ rp = 15 \/ rp = 16 \/ rp = 17)%Z) by lia.
          clear Hy. clearbody bitlim.
          destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_DC; mk_dfinv). }
        zs. zs. brs K6.
        * (* [comment removed for export] *)
          replace (30 <? bitlim)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK.
          eapply G94. symmetry. exact HK.
        * replace (30 <? bitlim)%Z with false in HK by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb] in HK.
          zs. rewrite srlw_small by lia.
          assert (Rs0 : (0 <= Z.shiftr x0 bitlim)%Z) by (apply Z.shiftr_nonneg; lia).
          assert (Rs1 : (Z.shiftr x0 bitlim <= x0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]; assert (X0nn : (0 <= x0)%Z) by lia; assert (P1b : (1 <= 2 ^ bitlim)%Z) by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia); first [ clear - X0nn P1b; nia | nia ]).   (* [comment removed for export] *)
          zs. brf K7.
          -- (* [comment removed for export] *)
             replace (Z.shiftr x0 bitlim =? 0)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
             eapply G94. symmetry. exact HK.
          -- replace (Z.shiftr x0 bitlim =? 0)%Z with false in HK by (symmetry; apply Z.eqb_neq; lia). cbn [andb orb] in HK.
             stmt HS_T. eapply NX; try eassumption; try glia. exact (conj LW' (conj LX REL)).
      + (* [comment removed for export] *)
        assert (Rrp1 : (1 <= rp <= 8)%Z) by lia.
        replace (rp <? 9)%Z with true in HK by (symmetry; apply Z.ltb_lt; lia). cbn [andb orb] in HK. some_snd HK. rename HK into HyR.
        zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
        set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
        zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs.
        zs. callx (eapply floatunsitf_callv with (u := x0); [eassumption | lia | rewrite sext32_small by lia; reflexivity]).
        set (XF := f128_of_u32 x0) in *. pose proof (lo64_range XF) as R2l. pose proof (hi64_range XF) as R2h.
        zs. zs. zs. zs.
        zs. call_split 80%Z (eapply mul_callE with (X := SF) (Y := XF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
        set (P := f128_mul SF XF) in *. pose proof (lo64_range P) as R3l. pose proof (hi64_range P) as R3h.
        zs. zs. fixw3. fixw. zs. zs. zs. try rewrite zext32_small by lia. try (rewrite (Z.shiftl_mul_pow2 (8 - rp)) by lia; change (2^2)%Z with 4%Z). zs. zs.
        (* [comment removed for export] *)
        assert (G_E4 : forall m2 (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
          dfinv m2 j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR ->
          evt bsegs POST
            (MS (mkR y1 SPv gp TPv y5 y6 y7 (Z_to_bv 64 (lo64 P)) y9 (Z_to_bv 64 (znth p10s (8 - rp))) (Z_to_bv 64 (hi64 P)) y12 y13 y14 y15 y16 y17
                     y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                Ft (Z_to_bv 64 0x97fdc) fct None m2 (seg_rom bsegs))).
        { intros m2 y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 DI2.
          pose proof DI2 as DI'. dest_dfinv DI'.
          pose proof (p10s_lit (8 - rp)%Z ltac:(lia)) as Rp.
          zs. zs. callx (eapply floatsitf_callp; [eassumption | exact Rp]).
          set (PF := f128_of_i32 (znth p10s (8 - rp))) in *. pose proof (lo64_range PF) as R4l. pose proof (hi64_range PF) as R4h.
          zs. zs. zs. zs.
          zs. call_split 112%Z (eapply div_callE with (X := P) (Y := PF); [eassumption | eassumption | lia | reflexivity | reflexivity | reflexivity | reflexivity]).
          zs. eapply L_RET1; try eassumption; try glia; try mk_finv; try mk_framL. }
        assert (Hc : (rp = 1 \/ rp = 2 \/ rp = 3 \/ rp = 4 \/ rp = 5 \/ rp = 6 \/ rp = 7 \/ rp = 8)%Z) by lia.
        clear HyR.
        destruct Hc as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst rp; (zs; eapply G_E4; mk_dfinv).
    - (* [comment removed for export] *)
      replace (rp =? 9)%Z with true in HK by (symmetry; apply Z.eqb_eq; lia). cbn [andb orb] in HK. some_snd HK.
      zs. zs. callx (eapply floatsitf_callsg; [eassumption | exact Hsg]).
      set (SF := f128_of_i32 sign) in *. pose proof (lo64_range SF) as R1l. pose proof (hi64_range SF) as R1h.
      zs. pose_rd0. zs. rewrite (sx32_wval ws 0%Z x0 (eq_sym Et0) Rt0). zs. zs.
      pose proof L_DD24 as NX. unfold F_floatscan_common.S_DD24 in NX. eapply NX; try eassumption; try glia; try mk_dfinv; try (symmetry; exact HK).
  Qed.

End Floatscan.


End CeilWrap.
