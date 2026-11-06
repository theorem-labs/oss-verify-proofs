(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl F_shgetc_proofs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_scanexp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_scanexp.F_shgetc_proofs3.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_scalbn F_trunctfdf2.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_rscan_shape.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_model.F_rscan_facts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_floatscan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

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
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].


(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
(* [comment removed for export] *)
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof using .
  intros a m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
  pose proof (Z.sub_land_same_l m a) as E. rewrite (Z.land_comm a m).
  assert (0 <= Z.land m (Z.lnot a))%Z by (apply Z.land_nonneg; left; exact Hm). lia.
Qed.

(* [comment removed for export] *)
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

(* [comment removed for export] *)
Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof using .
  intros ws i t Hw Ht. unfold sx32. f_equal. unfold wval in Hw. rewrite swrap32_eq.
  pose proof (bv_unsigned_in_range 64 (wnth ws i)) as R.
  rewrite <- Hw. rewrite <- Hw in Ht. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof using . intros. unfold zx32, wval. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof using .
  intros t sh Ht Hsh. rewrite (Z.mod_small sh 32) by lia.
  replace (bv_wrap 32 t) with t by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
  assert (0 <= Z.shiftr t sh <= t)%Z.
  { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ sh)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia). nia. }
  apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

(* [comment removed for export] *)
Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof using .
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof using .
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
  replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
  apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section DivW.
  Local Open Scope Z_scope.
Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof using .
  intros v i Hv Hi. unfold v_divw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
  rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
  rewrite (swrap32_small v), (swrap32_small i) by lia. rewrite Z.quot_div_nonneg by lia.
  assert (0 <= v / i <= v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|]; nia]).
  apply swrap32_small. lia.
Qed.
Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof using .
  intros j Hj.
  assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    match goal with |- context [znth p10s ?j] => let v := eval vm_compute in (znth p10s j) in change (znth p10s j) with v end; (split; [lia | reflexivity]).
Qed.
End DivW.


Definition VF_DEPTH : Z := 11440.   (* [comment removed for export] *)
Definition VFSCANF : Z := 0x9709c.
Definition RFMT : Z := 0x21260.      (* [comment removed for export] *)
Notation RATP := F_floatscan_common.RATP.
Notation RERRNO := F_floatscan_common.RERRNO.

Section Vfscanf.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (T : Z) (txt pre post : list Z) (canary : word) (PD : Z) (djunk : word) (r : Z) (res : option Z).
  Hypothesis HS : scan_sscanf_lg txt = Some (r, res).
  Hypothesis Htxt : txt = pre ++ 0%Z :: post.
  Hypothesis Hpre : Forall (fun c => is_numch c = true) pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis HP64 : (length pre <= 64)%nat.
  Hypothesis AL : ((T + zlength txt) mod 8 = 0)%Z.
  Hypothesis L256 : (zlength txt <= 256)%Z.
  Hypothesis T0 : (0 <= Z.max (q - 11440 - (T + zlength txt)) (T - (q + 408)))%Z.   (* [comment removed for export] *)
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SPLO : (0x5ff000 <= q - VF_DEPTH)%Z.
  Hypothesis Q1 : (q + 408 < 2^62)%Z.
  Hypothesis HPD : (0 <= Z.max (q - 11440 - (PD + 8)) (PD - (q + 408)))%Z.
  Hypothesis HPD2 : (PD + 8 <= 2^63)%Z.
  Hypothesis SEPD : (PD + 8 <= T \/ T + zlength txt <= PD)%Z.
  Hypothesis FRM : frm0 fc.
  (* [comment removed for export] *)
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                                 clear - HI T0 T1 SPLO Q1 HPD HPD2 SEPD AL L256;
                                 unfold zlength, VF_DEPTH, sf_hide in *; Zify.zify; xlia zchecker ].
  Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | sec_tier | tlia | split; [ tlia | exact I ] ].
  Hypothesis AXV : scan_ax m0 q VF_DEPTH (q + 56)%Z T txt (zlength pre).  (* [comment removed for export] *)
  Hypothesis HPDK : (0x10007fff8000 <= PD)%Z.                              (* [comment removed for export] *)
  Hypothesis TLO : (4096 <= T)%Z.                                           (* [comment removed for export] *)
  Hypothesis THI : (0x5ff000 <= T)%Z.                                       (* [comment removed for export] *)

  Definition ctx_all : unit :=
    let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
              T, txt, pre, post, canary, PD, djunk, r, res) in tt.

  Notation p := (zlength pre).
  Notation Fp := (q + 56)%Z.
  Notation AP := (q + 400)%Z.
  Notation TPv := (Z_to_bv 64 RATP).
  Notation SPv := (Z_to_bv 64 (q + -480)).
  Notation ssf0 := (F_rscan_model.ssf0 txt p).
  Definition resw : word := match res with Some b => Z_to_bv 64 b | None => djunk end.
  Definition Wvf : list (Z * Z) := [(q - VF_DEPTH, q); (q + 56, q + 288); (PD, PD + 8); (RERRNO, RERRNO + 4)]%Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma LTX : length (zbytes txt) = length txt. Proof using . unfold zbytes. apply length_map. Qed.
  Lemma Hp : (0 <= p < zlength txt)%Z. Proof using HP64 Htxt PD T q. rewrite Htxt. unfold zlength. rewrite length_app. cbn. lia. Qed.
  Lemma Hnul : znth txt p = 0%Z. Proof using Htxt. rewrite Htxt. apply znth_app_mid. Qed.
  Lemma Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
  Proof using Hpre Htxt. intros i Hi. rewrite Htxt. rewrite znth_app_pre by exact Hi. exact (proj1 (Forall_forall _ _) Hpre _ (znth_In' pre i Hi)). Qed.
  Lemma TXT : rtext T txt pre post.
  Proof using AL BYT HP64 Hpre Htxt L256 PD q.
    unfold rtext. split; [exact Htxt|]. split; [|split; [exact BYT | split; [exact AL | exact L256]]].
    apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hpre c Hc) as E.
    unfold is_numch in E. repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]); try (apply Z.eqb_eq in E; lia).
    apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  Qed.
  Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
  Proof using BYT. intros i Hi. exact (proj1 (Forall_forall _ _) BYT (znth txt i) (Shgetc_lemmas.znth_In' txt i Hi)). Qed.

  (* [comment removed for export] *)
  Definition FokR (F' : bvmap 5 word) : Prop :=
    forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.

  Definition vf_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' junk (ev' : word),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch Wvf m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ stk asegs m' (q - VF_DEPTH) q
      /\ rw_cells asegs m' Fp [CB 232 junk]
      /\ rw_cells asegs m' PD [C8 resw]
      /\ bytes_at asegs m' T (zbytes txt)
      /\ ssp_cells m' canary
      /\ rw_cells asegs m' RERRNO [C4 ev']
      /\ FokR F' /\ frm0 fc'.
  Notation POST := vf_post.

  (* [comment removed for export] *)
  Definition hi_cells : list cell :=
    [C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  (* [comment removed for export] *)
  Definition finv (m : word -> option byte) : Prop :=
    mem_inv asegs m /\ munch Wvf m0 m /\ wmono asegs m0 m
    /\ rw_cells asegs m (q + -112) hi_cells
    /\ stk asegs m (q - VF_DEPTH) (q + -480)
    /\ bytes_at asegs m T (zbytes txt)
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary]
    /\ rw_cells asegs m AP [C8 (Z_to_bv 64 PD)].
  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in let APC := fresh "APC" in
    (nelim H 9%nat; intros MI MU WM FRhi ST BY SSP1 SSP2 APC); unfold Wvf, VF_DEPTH, F_floatscan_common.RERRNO in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold VF_DEPTH in ST;
    unfold VF_DEPTH, got_ssp, ssp_guard, F_floatscan_common.RERRNO in SPLO, T0, HPD;
    try (let LT := fresh "LTX" in pose proof LTX as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    unfold zlength in *.
  Ltac mk_finv := unfold finv, Wvf, hi_cells, VF_DEPTH, F_floatscan_common.RERRNO, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

  (* [comment removed for export] *)
  Definition framV (w0 w8 w16 w24 w32 w40 w48 w56 w64 : word) (j72 : list byte) (scs : list byte) (m : word -> option byte) : Prop :=
    rw_cells asegs m (q + -480) [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; CB 40 j72]
    /\ rw_cells asegs m (q + -368) [CB 256 scs].
  Ltac dest_framV H := let LOW := fresh "LOW" in let SCS := fresh "SCS" in destruct H as (LOW & SCS).
  Ltac mk_framV := unfold framV; split; hyp.

  (* [comment removed for export] *)
  Ltac vsx_W := unfold scan_iv_ok; repeat (apply Forall_cons; [cbn [fst snd]; unfold KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size in *; lia|]); apply Forall_nil.
  Ltac vsx_pack d :=
    lazymatch goal with |- scan_ax ?mm _ _ _ _ _ _ =>
      match goal with MUx : munch _ m0 mm |- _ =>
        let C := fresh "AXce'" in pose proof (proj1 (proj2 AXV)) as C; unfold alloc_ceiling, sp_window_lo, stack_max_size, VF_DEPTH in C;
        eapply (scan_ax_xfer m0 mm _ _ _ _ _ T txt _ _ AXV MUx);
        [ vsx_W | unfold VF_DEPTH, F_floatscan_common.FS_DEPTH; lia | lia | unfold zlength in *; lia | pose proof Hp; unfold zlength in *; lia ]
      end end.
  Ltac vsx_now :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let X := fresh "AXn" in
      assert (X : scan_ax mm (q + -480) 2464 (q + 8) T txt (zlength pre)) by (vsx_pack 2464%Z);
      (nelim X 5%nat; intros AXmr AXce AXq AXar AXso); unfold alloc_ceiling, sp_window_lo, stack_max_size in AXce
    end.
  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

  Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof using . clear. destruct a, b; reflexivity. Qed.
  Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof using . clear. destruct c; reflexivity. Qed.
  Ltac b2z_01 := rewrite ?b2z_land; lazymatch goal with |- (0 <= Z.b2z ?b <= 1)%Z => destruct b; cbn; lia end.

  (* [comment removed for export] *)
  Definition hide (P : Prop) := P.
  Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac stash_disj := repeat match goal with H : _ \/ _ |- _ =>
    lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
  Ltac unstash := unfold hide in *.
  (* [comment removed for export] *)
  Ltac store_done' := stash_mods; stash_disj; store_done; unstash.
  (* [comment removed for export] *)
  Ltac flia := first [ solve [stash_mods; stash_disj; lia] | lia ].
  (* [comment removed for export] *)
  Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
  Ltac hush := try stash SEPD; stash_mods.
  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt); unstash.

  Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
  Proof using . clear. intros. rewrite (Z.add_comm c (Z.land a _)), swrap32_landW. f_equal. lia. Qed.
  Ltac fixw3 := rewrite ?swrap32_landW, ?swrap32_landW_r, ?swrap32_landW_sub; try rewrite !swrap32_small by lia.

  (* [comment removed for export] *)
  Definition hide2 (P : Prop) := P.
  Ltac bury H := lazymatch type of H with hide2 _ => idtac | ?T => change T with (hide2 T) in H end.
  Ltac bury_disj := try bury SEPD.
  Ltac unbury := unfold hide2 in *.
  (* [comment removed for export] *)
  Ltac zs0 := unstash; unfold hide2 in SEPD; zstep; try (fix_litstore; mem_after_store_opt).
  (* [comment removed for export] *)
  Ltac zs1 := hush; unfold hide in SEPD; unfold hide2 in SEPD; zstep; try (fix_litstore; mem_after_store_opt); unstash.
  (* [comment removed for export] *)
  Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
  (* [comment removed for export] *)
  Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
  Ltac br10 K := brf K; [ exfalso; lia | ].
  Ltac br01 K := brf K; [ | exfalso; lia ].
  Ltac brs10 K := brsf K; [ exfalso; lia | ].
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


  (* [comment removed for export] *)
  Tactic Notation "call_split" constr(K) tactic3(tac) :=
    lazymatch goal with ST : stk _ ?m (q - 11440)%Z (q + -480)%Z |- _ =>
      let ST1 := fresh "ST1" in
      destruct (stk_split _ _ _ (q + -480 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
      callw tac;
      lazymatch goal with STn : stk _ ?m' (q + -480 - K)%Z (q + -480)%Z |- _ =>
        lazymatch goal with ST1' : stk _ m' (q - 11440)%Z (q + -480 - K)%Z |- _ =>
        pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
    end.
  Ltac ufc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale ssJ] in FC.


  Lemma cb8_c8_in : forall m A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
  Proof using .
    clear. intros m A pre post bs [[Hwf Hb] Hw].
    apply cells_wf_app in Hwf. (nelim Hwf 3%nat; intros H1 H2 H3). cbn in H2.
    split; [split|].
    - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
    - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite F_rscan_shape.le8_of_bytes by exact H2. exact Hb.
    - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
  Qed.
  Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let rec go pre l := lazymatch l with
       | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
       | ?c :: ?l' => go constr:(pre ++ [c]) l' end in
    go constr:(@nil cell) cs end.
  (* [comment removed for export] *)
  Lemma ss_cells_raw : forall sh shl shc,
    rf_cells_raw T p false ssf0 ssJ (Z_to_bv 64 sh) shl shc = ss_cells T (T + 0) T (Z_to_bv 64 M64) T sh shl shc.
  Proof using . intros. unfold rf_cells_raw, rf_rend, F_rscan_model.ssf0, ss_cells. cbn. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition S_VRET : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 : word) (j72 scs fj : list byte) (ev : word),
    let _ := ctx_all in
    finv m -> framV w0 w8 w16 w24 w32 w40 w48 w56 w64 j72 scs m ->
    rw_cells asegs m Fp [CB 232 fj] -> rw_cells asegs m PD [C8 resw] -> rw_cells asegs m RERRNO [C4 ev] -> FokR Ft -> frm0 fct ->
    evt asegs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 ssp_guard) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 1) x19 (Z_to_bv 64 r) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Ft (Z_to_bv 64 0x97b4c) fct None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition S_VB : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word)
      (w16 w56 : word) (j72 scs : list byte) (ev : word) (f2 : shfile),
    let _ := ctx_all in
    finv m -> framV (Z_to_bv 64 1) (Z_to_bv 64 ssp_guard) w16 (Z_to_bv 64 (AP + 8)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) w56 (Z_to_bv 64 PD) j72 scs m ->
    rw_cells asegs m Fp (rf_cells T p true f2 ssJ) ->
    sh_rpos f2 = 0%Z -> sh_n f2 = p -> sh_stdio f2 = true -> sh_buf f2 = txt -> sh_lim0 f2 = ssf0 -> sh_ok T txt f2 ->
    rw_cells asegs m PD [C8 djunk] -> rw_cells asegs m RERRNO [C4 ev] ->
    evt asegs POST
      (MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 135778) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 0) (Z_to_bv 64 103) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 PD) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) (Z_to_bv 64 (q + -368)) x28 x29 x30 x31)
          F (Z_to_bv 64 0x974cc) fc None m (seg_rom asegs)).

  Lemma L_VRET : S_VRET.
  Proof using HP64.
    intros m; intros until ev. intros _ FI FV FJ PDC ERR FOK FRM'.
    pose proof FI as FI0. dest_finv FI. dest_framV FV. bury_disj. unfold ssp_guard.
    zs. br01 K0.
    zs. zs. zs. br10 K1.
    zs. do 13 zs. zs. zs.
    release_frame LOW ST (q + -368)%Z.
    release_frame SCS ST (q + -112)%Z.
    release_frame FRhi ST q.
    apply evt_done. unfold vf_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FJ|]. split; [exact PDC|]. split; [exact BY|]. split; [split; [exact SSP1 | exact SSP2]|]. split; [exact ERR|].
    split; [exact FOK | exact FRM'].
  Qed.
  Lemma L_VB : S_VB.
  Proof using AL AXV BYT FRM HP64 HPD HPD2 HPDK HS Hpre Htxt L256 Q1 SEPD SPLO T0 T1 THI TLO.
    intros m; intros until f2. intros _ FI FV FC R2 N2 S2 B2 L2 OK2 PDC ERR.
    pose proof FI as FI0. dest_finv FI. dest_framV FV. bury_disj. unfold RFMT. unfold F_floatscan_common.RERRNO in ERR.
    pose proof Hp as Hp'. pose proof Hnul as Hnul'. unfold zlength in Hp'.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof (rw_cells_bound _ _ _ _ PDC) as BPD. cbn [cells_size csize Nat.add] in BPD.
    (* [comment removed for export] *)
    pose proof (ss_model txt p BYT Hp Hnul Hnum r res HS) as HSM. cbv zeta in HSM.
    pose proof (ss_peek txt p BYT Hp Hnul Hnum) as PK. cbv zeta in PK. (nelim PK 10%nat; intros OK1 UPRE _ _ _ _ _ U2 NS1 LT1).
    (* [comment removed for export] *)
    pose proof FC as FC0. rewrite rf_cells_raw_eq in FC0.
    pose proof shlim_spec as SL. unfold shlim_stmt in SL.
    zs. zs. zs. callx (eapply SL with (Fp := Fp) (T := T) (p := p) (w := true) (txt := txt) (f := f2) (J := ssJ);
      [exact FC0 | exact OK2 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | assumption]).
    clear SL.
    match goal with H : rw_cells _ _ _ (rf_cells _ _ _ (sh_lim0 f2) _) |- _ => rename H into FC1; rewrite L2 in FC1 end.
    pose proof FC1 as FC2. unfold F_rscan_model.ssf0 in FC2. ufc FC2. unfold M64 in FC2.
    zs. zs.
    destruct (Z.eq_dec (zlength pre) 0) as [P0|P1].
    - (* [comment removed for export] *)
      zs. br K1.
      pose proof shgetc_spec as SG. unfold shgetc_stmtA, SHGETC_XD in SG. vsx_now.
      zs. zs. call_split 2464%Z (eapply SG with (w := true) (f := ssf0) (txt := txt) (pre := pre) (post := post) (canary := canary);
        [ exact FC1 | reflexivity | reflexivity | reflexivity | unfold F_rscan_model.ssf0; cbn; lia | intros X; discriminate X | unfold F_rscan_model.ssf0; cbn; lia
        | exact TXT | reflexivity | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp
        | lia | lia | unfold zlength in *; lia | replace (q + -480 - 2464)%Z with (q + -480 - 2464)%Z by lia; eassumption | lia | lia | lia | unfold zlength in *; lia | unfold ssp_guard; lia | unfold got_ssp, zlength in *; lia | unfold ssp_guard, zlength in *; lia | lia | lia | assumption
        | exact AXmr | unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | lia | exact AXar | exact AXso ]); clear AXmr AXce AXq AXar AXso.
      assert (E1 : fst (sh_getc ssf0) = (-1)%Z) by (unfold F_rscan_model.ssf0, sh_getc; cbn; rewrite P0; reflexivity).
      rewrite E1 in *.
      destruct HSM as [(_ & Er & Eres) | (NE & _)]; [|exfalso; exact (NE eq_refl)].
      match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ _ _ _) |- _ => rename H into FC3 end.
      match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
      zs. br01 K2.
      zs. zs. zs. zs. zs. zs. zs. zs.
      zs. zs. zs. zs. br01 K3.
      let v := getreg 20%Z in replace v with (Z_to_bv 64 r) by (rewrite Er; apply Z_to_bv_eqm; reflexivity).
      destruct (rw_cells_forget _ _ _ _ FC3) as [fj FJ]. cbn [cells_size csize Nat.add rf_cells length] in FJ.
      stmt L_VRET. eapply NX; try eassumption.
      { mk_finv. }
      { mk_framV. }
      { unfold resw. rewrite Eres. exact PDC. }
      { intros k _ _ _. reflexivity. }
    - (* [comment removed for export] *)
      zs. brf K1; rewrite ?land_W64 in K1.
      { exfalso. clear -K1 P1 T0 T1 Q1 Hp' L256. unfold zlength in *. Z.div_mod_to_equations. lia. }
      zs. zs. zs.
      zs. zs. br10 K2. zs. zs. zs.
      zs. zs. zs. br10 K3. zs. zs. zs. zs. zs. zs. zs. zs.
      (* [comment removed for export] *)
      destruct HSM as [(E1 & _ & _) | (NE1 & fR & yR & HM & JRR & CASES)].
      { exfalso. revert E1 P1. unfold F_rscan_model.ssf0, sh_getc. cbn [sh_stdio sh_rpos sh_n sh_buf negb].
        destruct (Z.eqb_spec 0 (zlength pre)); cbn [negb fst]; [lia|]. pose proof (txt_char 0 ltac:(unfold zlength in *; lia)). lia. }
      assert (RJ0 : RFJ T txt p true ssJ 0 1 ssf0).
      { unfold RFJ, F_rscan_model.ssf0, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
        unfold zlength in *. repeat split; try reflexivity; try lia; intros X; try discriminate X; try lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (FC4 : rw_cells asegs mm Fp (rf_cells T p true ssf0 ssJ)) by (unfold rf_cells, rf_rend, F_rscan_model.ssf0; cbn; unfold M64; hyp_cells) end.
      match goal with H : stk _ _ (q - 11440)%Z _ |- _ => rename H into ST end.
      (* [comment removed for export] *)
      zs. zs. zs. zs.
      destruct (stk_split _ _ _ (q + -480 - 10960)%Z _ ST ltac:(lia)) as [STlo SThi].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (F_floatscan.L_ENTRY (Z_to_bv 64 0x9754c) (q + -480)%Z gp (Z_to_bv 64 Fp) (Z_to_bv 64 135778) x18 (Z_to_bv 64 0) (Z_to_bv 64 103) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 PD) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) (Z_to_bv 64 (q + -368)) F fc mm
                Fp T p ssJ txt pre post canary 0%Z (fuel_of txt) ssf0 0%Z 1%Z fR yR) as LE end.
      specialize (LE HM ltac:(left; reflexivity) ltac:(intros _; split; [exact TXT | reflexivity]) BYT Hp Hnul Hnum ltac:(unfold zlength in *; lia) ltac:(lia) T1
                 ltac:(unfold zlength in *; lia) ltac:(unfold F_floatscan_common.RERRNO; unfold zlength in *; lia) ltac:(unfold F_floatscan_common.FS_DEPTH, zlength in *; lia) ltac:(lia) ltac:(lia)
                 ltac:(unfold F_floatscan_common.FS_DEPTH, zlength in *; lia) ltac:(unfold F_floatscan_common.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp; unfold zlength in *; lia) ltac:(unfold ssp_guard; unfold zlength in *; lia) ltac:(lia) FRM
                 ltac:(intros _; vsx_pack 10960%Z)).
      cbv zeta in LE. unfold F_floatscan_common.FS_DEPTH, F_floatscan_common.RERRNO, F_floatscan_common.FLOATSCAN, F_floatscan_common.RATP in LE.
      unfold F_floatscan_common.fs_post, F_floatscan_common.Wfs, F_floatscan_common.FS_DEPTH, F_floatscan_common.RERRNO, F_floatscan_common.FokR in LE.
      callx (eapply LE; [ exact SThi | exact MI0 | exact FC4 | exact RJ0 | lia | lia | reflexivity | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
      clear LE.
      match goal with H : rw_cells _ _ _ (rf_cells _ _ _ fR _) |- _ => rename H into FC5 end.
      match goal with H : RFJ _ _ _ _ _ _ _ fR |- _ => rename H into RJ5 end.
      match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
      match goal with H : stk _ ?m' (q + -480 - 10960)%Z _ |- _ => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as ST5; clear H STlo end.
      match goal with H : bytes_at _ _ T (zbytes txt) |- _ => rename H into BY5 end.
      match goal with H : frm0 ?x |- evt _ _ (MS _ _ _ ?x _ _ _) => rename H into FRM5 end.
      match goal with H : forall k : reg, _ -> _ -> _ -> reg_get _ k = reg_get F k |- _ => rename H into FOK5 end.
      match goal with H : rw_cells _ _ 6148524 _ |- _ => rename H into ERR5 end.
      match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
      pose proof RJ5 as RJ6. (nelim RJ6 6%nat; intros OK5 Rc5 CC5 KM5 NS5 SS5). (nelim OK5 6%nat; intros Hbuf5 Rl5 Rr5 Rc05 Rn5 Rst5).
      unfold JR in JRR.
      pose proof FC5 as FC6. unfold rf_cells in FC6.
      cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale ssJ] in FC6.
      assert (RR5 : (0 <= rf_rend T p true fR <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fR); unfold zlength in *; lia). unfold M64 in RR5.
      zs. zs. zs. zs. zs. brfw K4; rewrite ?land_W64 in K4.
      + (* [comment removed for export] *)
        destruct CASES as [(E0 & Er & Eres) | (N0 & _)]; [| exfalso; apply N0; unfold sh_cnt; clear -K4 JRR Hp' T0 T1 Q1 L256; unfold zlength in *; Z.div_mod_to_equations; lia].
        zs. zs. zs. zs. zs. zs. zs. br01 K5.
        let v := getreg 20%Z in replace v with (Z_to_bv 64 r) by (rewrite Er; reflexivity).
        destruct (rw_cells_forget _ _ _ _ FC6) as [fj FJ]. cbn [cells_size csize Nat.add length] in FJ.
        stmt L_VRET. eapply NX; try eassumption.
        { mk_finv. }
        { mk_framV. }
        { unfold resw. rewrite Eres. exact PDC. }
      + (* [comment removed for export] *)
        destruct CASES as [(E0 & _) | (N0 & Er & Eres)]; [exfalso; revert E0 K4; unfold sh_cnt; clear -JRR Hp' T0 T1 Q1 L256; unfold zlength in *; intros E0 K4; apply K4; Z.div_mod_to_equations; lia |].
        zs. br10 K5. zs. zs. br10 K6. zs. zs. br01 K7.
        zs. callx (eapply trunctfdf2_spec; [eassumption]).
        idtac. idtac .
        rewrite !ulit_lo64, !ulit_hi64.
        change (lo64 yR + 2 ^ 64 * hi64 yR)%Z with (canon yR). rewrite F_scan_calls.f128_to_d_canon.
        zs1. zs.
        do 14 zs.
        zs. zs. brs10 K8. zs. zs. br01 K9; rewrite ?land_W64 in K9. zs. br01 K10.
        zs. zs. zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => match goal with H : rw_cells _ mm Fp _ |- _ =>
          destruct (rw_cells_forget _ _ _ _ H) as [fj FJ]; cbn [cells_size csize Nat.add length] in FJ end end.
        stmt L_VRET. rewrite Er in NX. eapply NX; try eassumption.
        { mk_finv. }
        { mk_framV. }
        { unfold resw. rewrite Eres. exact PDC. }
        { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK5 k H10 H14 H15). }
  Qed.

End Vfscanf.


End CeilWrap.
(* [comment removed for export] *)
Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
  idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
Ltac fix_idx := repeat match goal with
  | |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
    replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
  | |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
    replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.
Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
  let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.
Notation RATP := F_floatscan_common.RATP.
Notation RERRNO := F_floatscan_common.RERRNO.
