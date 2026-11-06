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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
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
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                           clear - HI SPT SEP SG1 SG2 SG3 SPLO SPF SPF2 Q1 T0 T1 Hp HP64;
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

  Hypothesis HS_D : S_D.
  Hypothesis HS_E : S_E.

  (* [comment removed for export] *)
  Ltac ufc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac splits := lazymatch goal with |- _ /\ _ => split; [|splits] | |- _ => idtac end.
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
  (* [comment removed for export] *)
  Ltac mk_winv2 := unfold F_floatscan_common.winv; split; [mk_finv|]; split; [mk_framL|]; split; [eassumption|];
    split; [first [assumption | rewrite ?upd_length; assumption]|];
    first [hyp | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Lemma znth_X0 : forall i, znth X0 i = 0%Z.
  Proof using .
    clear. intros i. unfold X0. destruct (Z.eq_dec i 0) as [->|Hne].
    - rewrite znth_zupd_eq; [reflexivity|]. rewrite zlength_zrepeat; unfold KMAX; lia.
    - rewrite znth_zupd_neq by lia. rewrite znth_zrepeat. destruct (_ && _); reflexivity.
  Qed.
  Lemma X0_len : length X0 = 2048%nat.
  Proof using . clear. unfold X0, KMAX. rewrite zupd_length. pose proof (zlength_zrepeat 0 2048 ltac:(lia)) as E. unfold zlength in E. lia. Qed.
  Lemma xrel_X0 : forall ws, length ws = 2048%nat -> wval ws 0 = 0%Z -> xrel ws X0 (digz 0 0).
  Proof using .
    clear. intros ws LW W0. split; [exact LW|]. split; [exact X0_len|].
    intros i Hi Hr. unfold digz in Hr. assert (Ei : i = 0%Z) by lia. rewrite Ei, znth_X0, W0. reflexivity.
  Qed.
  Ltac x0_facts := splits; try glia; try (apply xrel_X0; assumption); unfold X31; intros; rewrite ?znth_X0 in *; try glia.
  Lemma seqz46 : forall c, (-2^62 < c < 2^62)%Z -> Z.b2z (Z.land (c + -46) 18446744073709551615 <? 1)%Z = Z.b2z (c =? 46)%Z.
  Proof using .
    clear. intros c Hc. rewrite land_W64. destruct (Z.eqb_spec c 46) as [->|Hne]; [reflexivity|].
    destruct (Z.ltb_spec ((c + -46) mod 2 ^ 64) 1) as [Hl|Hg]; [|reflexivity]. exfalso. Z.div_mod_to_equations. lia.
  Qed.
  Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
  Proof using . clear. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
  Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
  Proof using . clear. intros f. unfold sh_getc. destruct (negb (sh_stdio f)); [reflexivity|]. destruct (negb _); reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma getc_rpos2 : forall f, sh_buf f = txt ->
    (sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1)%Z /\ (fst (sh_getc f) <> (-1)%Z -> sh_rpos (snd (sh_getc f)) = sh_rpos f + 1)%Z.
  Proof using .
    clear -BYT. intros f Hb. unfold sh_getc. destruct (negb (sh_stdio f)); [cbn; split; [lia | intros; reflexivity]|].
    destruct (negb (sh_rpos f =? sh_n f)%Z); cbn; [split; [lia | intros; reflexivity]|]. split; [lia|]. intros H. exfalso. apply H. reflexivity.
  Qed.
  Ltac site_facts FC RJ k c f :=
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

  (* [comment removed for export] *)
  Lemma L_B0C : S_B0C.
  Proof using HP64 HS_D Hp SG1 SPF SPT.   (* [comment removed for export] *)
    intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hcond HK.
    pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    unfold dfK_dig in HK. destruct (df_dig_loop fuelc _) as [s'|] eqn:HL; [|discriminate HK].
    pose proof LOW as LOWw. lo96w LOWw.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. rewrite (seqz46 c) by lia. zs. zs. zs. zs. zs.
    match goal with |- context [Z_to_bv 64 (q + -8416 + 104 + 8176)%Z] => replace (q + -8416 + 104 + 8176)%Z with (q + -136)%Z by lia | _ => idtac end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
    stmt HS_D. eapply (NX fuelc) with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try glia.
    { mk_dfinv. }
    { unfold digI. x0_facts. }
  Qed.

  (* [comment removed for export] *)
  Lemma L_A9C : S_A9C.
  Proof using HP64 HS_D HS_E Hp SG1 SPF SPT.   (* [comment removed for export] *)
    intros m; intros until gotrad. intros _ DI RJ Hk FOK FRM' Hsg Hst W0 Hr1 Rlrp Rg Rgr Hne HK.
    pose proof DI as DI0. dest_dfinv DI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    zs. zs. br K1; rewrite ?land_W64 in K1.
    - (* [comment removed for export] *)
      stmt L_B0C. eapply NX; try eassumption; try glia.
      replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). rewrite Bool.orb_false_r.
      apply (proj2 (isdigitc_iff c ltac:(lia))). clear -K1 Rc. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      assert (Hd : isdigitc c = false).
      { apply Bool.not_true_iff_false. intros D. apply (proj1 (isdigitc_iff c ltac:(lia))) in D. clear -K1 D Rc. Z.div_mod_to_equations. lia. }
      assert (HL : df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0)).
      { clear -HK Hd Hne. unfold dfK_dig in HK. destruct fuelc as [|fu]; [discriminate HK|].
        cbn [df_dig_loop]. unfold df_dig_cond. cbn [dl_c]. rewrite Hd. replace (c =? 46)%Z with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity. }
      unfold dfK_dig in HK. rewrite HL in HK.
      pose proof LOW as LOWw. lo96w LOWw.
      zs. zs. zs. zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => match goal with H : rw_cells _ m' (q + -8416) _ |- _ => lo96b H end end.
      stmt HS_E. eapply NX with (x := X0) (kmin := kmin) (f := f) (lnz := 0%Z); try eassumption; try glia.
      { mk_dfinvG. }
      { unfold dig_facts. x0_facts. }
      { rewrite znth_X0. intros X; exfalso; exact (X eq_refl). }
  Qed.

  (* [comment removed for export] *)
  Lemma L_A44 : S_A44.
  Proof using HP64 HS_D HS_E Hp Q1 SG1 SPF SPLO SPT.
    intros m; intros until gotdig. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rlrp Rg Hne HK.
    dest_winv WI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    zs. zs. zs.
    pose proof (u32arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs.
    pose proof (u32arr_write asegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
    replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
    assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
    zs. zs. fixw3. zs. brfw K1.
    - stmt L_A9C. eapply NX with (gotrad := 1%Z); try eassumption; try glia. { rewrite <- winv_dfinvG. mk_winv. }
      clear -K1 Rc. rewrite land_W64 in K1. Z.div_mod_to_equations; lia.
    - assert (E46 : c = 46%Z) by (clear -K1 Rc; rewrite land_W64 in K1; Z.div_mod_to_equations; lia).
      zs. stmt L_B0C. eapply NX with (gotrad := 1%Z); try eassumption; try glia. { rewrite <- winv_dfinvG. mk_winv. }
      all: rewrite E46; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma L_RZ : S_RZ.
  Proof using AXF BYT HP64 HS_D HS_E Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    unfold F_floatscan_common.S_RZ. induction n as [|n IH].
    { intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK. discriminate HL. }
    intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Rlrp HL HK.
    dest_winv WI. bury_disj.
    rewrite df_rz_loop_step in HL. rewrite Z.eqb_refl in HL.
    site_facts FC RJ kmin 48%Z f.
    pose proof (RFI_getc T txt p J BYT Hp Hnul kmin 48 f RJ ltac:(lia)) as RJ1.
    pose proof (getc_stdio f) as Hst1. rewrite Hst in Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    pose proof (getc_rpos2 f Hbuf) as [Rrp1 Rrp2].
    (* [comment removed for export] *)
    assert (HEAD : forall m2 (x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
      winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
      fst (sh_getc f) = 48%Z ->
      evt asegs POST
        (MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' x10' x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x98298) fct None m2 (seg_rom asegs))).
    { intros until x31'. intros WI2 E48. rewrite E48 in RJ1.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fct j0 w32 w48 w80 b96 ev ws sign (kmin + 1)%Z (snd (sh_getc f)) (lrp + -1)%Z 1%Z g' lrp' c' f');
        try eassumption; try glia.
      rewrite E48 in HL. replace (lrp + -1)%Z with (lrp - 1)%Z by lia. exact HL. }
    (* [comment removed for export] *)
    assert (EXIT : forall m2 (x1' x5' x6' x7' x9' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x22' x23' x27' x28' x29' x30' x31' : word),
      winv m2 j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws (snd (sh_getc f)) ->
      fst (sh_getc f) <> 48%Z ->
      evt asegs POST
        (MS (mkR x1' SPv gp TPv x5' x6' x7' (Z_to_bv 64 48) x9' (Z_to_bv 64 (fst (sh_getc f))) x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' x20' (Z_to_bv 64 Fp) x22' x23' (Z_to_bv 64 1) (Z_to_bv 64 (lrp + -1)) (Z_to_bv 64 1074) x27' x28' x29' x30' x31')
            Ft (Z_to_bv 64 0x982b8) fct None m2 (seg_rom asegs))).
    { intros until x31'. intros WI2 N48.
      assert (E : (g', lrp', c', f') = (1%Z, (lrp - 1)%Z, fst (sh_getc f), snd (sh_getc f))).
      { clear -HL N48. destruct n as [|n2]; [discriminate HL|]. rewrite df_rz_loop_step in HL.
        replace (fst (sh_getc f) =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
      injection E as -> -> -> ->. clear HL.
      pose proof WI2 as WI3. dest_winv WI3.
      zs.
      stmt L_A44. eapply NX with (gotdig := 1%Z) (lrp := (lrp + -1)%Z); try eassumption; try glia.
      all: try (intros Hn1; specialize (Rrp2 Hn1); lia).
      all: replace (lrp + -1)%Z with (lrp - 1)%Z by lia; exact HK. }
    clear HL HK IH.
    destruct (Z.eq_dec (T + sh_rpos f)%Z (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. ufc2 FC.
      zs. zs. zs. br K1.
      (nelim (rf_getc_slow T txt p J Hp T1 kmin 48 f RJ SLOW) 5%nat; intros STD EJ Hn Hrpe Hc00).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. call_split 2464%Z (eapply shgetc_callJ with (pre := pre) (post := post);
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | eplia | eplia | exact SEP | replace (q + -8416 - 2464)%Z with (q + -8416 - 2464)%Z by lia; eassumption | eplia | eplia | eplia | eplia | eplia | exact SG2 | exact SG3 | eplia | eplia | assumption | fsx ]).
      match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end. rewrite <- EJ in FC2.
      match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end.
      set (c'' := fst (sh_getc f)) in *.
      zs. zs. brfw K2; rewrite ?land_W64 in K2.
      + eapply EXIT; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
      + eapply HEAD; [mk_winv2 | clear -K2 Rc'; Z.div_mod_to_equations; lia].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp kmin 48 f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp kmin 48 f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (txt_char (sh_rpos f) ltac:(unfold zlength in *; lia)) as Rch.
      ufc2 FC.
      zs. zs. zs. br10 K1.
      zs. zs0.
      pose proof (u8ro_read asegs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. try rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      set (c'' := znth txt (sh_rpos f)) in *.
      zs. zs. brf K2; rewrite ?land_W64 in K2.
      + eapply HEAD; [mk_winv2 | exact K2].
      + eapply EXIT; [mk_winv2 | exact K2].
  Qed.
  Ltac norm_m1074 := try match goal with H : rw_cells _ _ _ ?cs |- _ =>
    lazymatch cs with context [Z_to_bv 64 18446744073709550542] =>
      replace (Z_to_bv 64 18446744073709550542) with (Z_to_bv 64 (-1074)) in H by (apply Z_to_bv_eqm; reflexivity) end end.
  (* [comment removed for export] *)
  Lemma L_9EC : S_9EC.
  Proof using AXF BYT HP64 HS_D HS_E Hnul Hp Q1 SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT ST0 T0 T1.
    intros m; intros until f'. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Rg HL HK.
    dest_winv WI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    zs. zs. zs. zs. zs. zs. zs. zs. brf K1; rewrite ?land_W64 in K1.
    - assert (E48 : c = 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia). rewrite E48 in RJ, HL.
      pose proof L_RZ as NX. unfold F_floatscan_common.S_RZ, F_floatscan_common.SRZn in NX. eapply (NX fuelc) with (lrp := 0%Z); try eassumption; try glia. norm_m1074. mk_winv2.
    - assert (N48 : c <> 48%Z) by (clear -K1 Rc; Z.div_mod_to_equations; lia).
      assert (E : (g', lrp', c', f') = (gotdig, 0%Z, c, f)).
      { clear -HL HK N48. unfold dfK_dig in HK. destruct fuelc as [|n2]; [|rewrite df_rz_loop_step in HL].
        - exfalso. cbn [df_dig_loop] in HK. discriminate HK.
        - replace (c =? 48)%Z with false in HL by (symmetry; apply Z.eqb_neq; exact N48). injection HL as <- <- <- <-. reflexivity. }
      injection E as -> -> -> ->. clear HL.
      zs. stmt L_A44. eapply NX with (lrp := 0%Z); try eassumption; try glia. norm_m1074. mk_winv2.
  Qed.
  (* [comment removed for export] *)
  Lemma L_A64 : S_A64.
  Proof using HP64 HS_D HS_E Hp Q1 SG1 SPF SPLO SPT.
    intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
    dest_winv WI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    pose proof (u32arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs.
    pose proof (u32arr_write asegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
    replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
    assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
    zs. zs. fixw3. zs. brfw K1; rewrite ?land_W64 in K1.
    - exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
    - norm_m1074. stmt L_A9C. eapply NX with (gotdig := 1%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try glia. rewrite <- winv_dfinvG. mk_winv.
  Qed.
  (* [comment removed for export] *)
  Lemma L_7F4 : S_7F4.
  Proof using HP64 HS_D HS_E Hp Q1 SG1 SPF SPLO SPT.
    intros m; intros until f. intros _ WI RJ Hk FOK FRM' Hsg Hst Hr1 Hne HK.
    dest_winv WI. bury_disj.
    pose proof (RFI_rpos T txt p J Hp kmin c f RJ) as Rrp.
    assert (Rc : (-1 <= c < 256)%Z) by ((nelim RJ 3%nat; intros _ R _); exact R).
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    pose proof (u32arr_store_ok asegs _ _ _ 0%Z (Z_to_bv 64 (q + -8416 + 104)) XW ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zs.
    pose proof (u32arr_write asegs _ _ _ 0%Z (Z_to_bv 64 0) XW ltac:(lia)) as XW'.
    replace (wa (XA + 4 * 0)) with (wa XA) in XW' by (unfold wa; f_equal; lia). clear XW. store_done'. rename XW' into XW.
    assert (W0 : wval (upd ws (Z.to_nat 0) (Z_to_bv 64 0)) 0 = 0%Z) by (rewrite wval_upd_same by lia; reflexivity).
    zs. zs. fixw3. zs. brfw K1; rewrite ?land_W64 in K1.
    - norm_m1074. stmt L_A9C. eapply NX with (gotdig := 0%Z) (gotrad := 0%Z) (lrp := 0%Z); try eassumption; try glia. rewrite <- winv_dfinvG. mk_winv.
    - exfalso. clear -K1 Rc Hne. Z.div_mod_to_equations; lia.
  Qed.

End Floatscan.


End CeilWrap.
