(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UnKY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UnKY. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqYW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqYW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3qs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3qs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5d600%Z.
Definition w_97 := 0xfffb6517%Z.
Definition w_98 := 0xcac53a83%Z.
Definition hi_97 := (Z_to_bv 20 1048502).
Definition lo_98 := (Z_to_bv 12 3244).
Definition G_107a0 := 0x13430%Z.
Definition STRING_READ := STRING_READ.
Definition got_ssp := got_ssp.
Definition ssp_guard := ssp_guard.
Lemma CODE : CodeAt.code_at rsegs 0x5d600 (Q5m9.Mq1.scanexp_code 0xfffb6517%Z 0xcac53a83%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5d600 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5d600 /\ 0x5d600 + 624 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition RFI_rpos := @RFI_rpos.
Definition rf_getc_fast := @rf_getc_fast.
Definition rf_getc_fast_lt := @rf_getc_fast_lt.
Definition rf_getc_slow := @rf_getc_slow.
Definition RFI_getc := @RFI_getc.
Definition RFI_unget := @RFI_unget.
Definition rf_unget_eq := @rf_unget_eq.
Definition rf_unget_nop := @rf_unget_nop.
Definition shgetc_callJ := @shgetc_callJ.
Lemma RNG_got_ssp : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @RNG_got_ssp). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_got_ssp : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @LAY_lo_got_ssp). Proof. GwApply.gw_side. Qed.
Lemma RNG_ssp_guard : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @RNG_ssp_guard). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_ssp_guard : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @LAY_lo_ssp_guard). Proof. GwApply.gw_side. Qed.
Lemma LAY_got_ssp_ssp_guard : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @LAY_got_ssp_ssp_guard). Proof. GwApply.gw_side. Qed.
Lemma ROM_G_107a0 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq1.gw_all) @ROM_G_107a0). Proof. GwApply.gw_side. Qed.
End GwI.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Definition SCANEXP : Z := 0x5d600.
Lemma gw_eq_SCANEXP : @SCANEXP = ltac:(GwInst.gw_term (@Q5m9.Mq1.SCANEXP 0x5d600) (@SCANEXP)). Proof. unfold SCANEXP, Q5m9.Mq1.SCANEXP; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SCANEXP : gw_eqs.
Definition SCANEXP_DEPTH : Z := 240.
Lemma gw_eq_SCANEXP_DEPTH : @SCANEXP_DEPTH = ltac:(GwInst.gw_term (@Q5m9.Mq1.SCANEXP_DEPTH) (@SCANEXP_DEPTH)). Proof. unfold SCANEXP_DEPTH, Q5m9.Mq1.SCANEXP_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SCANEXP_DEPTH : gw_eqs.

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. first [GwInst.gw_exact (@Q5m9.Mq1.isdigitc_iff) | autorewrite with gw_eqs; GwInst.gw_exact (@Q5m9.Mq1.isdigitc_iff)]. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof. first [GwInst.gw_exact (@Q5m9.Mq1.isdigitc_t) | autorewrite with gw_eqs; GwInst.gw_exact (@Q5m9.Mq1.isdigitc_t)]. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof. first [GwInst.gw_exact (@Q5m9.Mq1.isdigitc_f) | autorewrite with gw_eqs; GwInst.gw_exact (@Q5m9.Mq1.isdigitc_f)]. Qed.

Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
match scanexp_l1_loop fuelc (0%Z, c, f) with
| None => None
| Some (x, c, f) =>
match scanexp_l2_loop fuelc (x, c, f) with
| None => None
| Some (y, c, f) =>
match scanexp_l3_loop fuelc (c, f) with
| None => None
| Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
end end end.
Lemma gw_eq_scanexp_tail : @scanexp_tail = ltac:(GwInst.gw_term (@Q5m9.Mq1.scanexp_tail) (@scanexp_tail)). Proof. unfold scanexp_tail, Q5m9.Mq1.scanexp_tail; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scanexp_tail : gw_eqs.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq3.ssp_cells) (@UxDK.ssp_cells) (Q6nq.gwt_def (@Q5m9.Mq1.ssp_cells) (@UxDK.ssp_cells) (Q6nq.gwt_def (@QQRC.Mq3.ssJ) (@UxDK.ssJ) (Q6nq.gwt_def (@Q5m9.Mq1.ssJ) (@UxDK.ssJ) (Q6nq.gwt_def (@QROt.Mq2.shgetc_post) (@UnKY.shgetc_post) (Q6nq.gwt_def (@Q5m9.Mq1.shgetc_post) (@UnKY.shgetc_post) (Q6nq.gwt_def (@Q8l1.Mq3.rtext) (@Uoo0.rtext) (Q6nq.gwt_def (@QQRC.Mq3.rf_rend) (@UxDK.rf_rend) (Q6nq.gwt_def (@QQRC.Mq3.rf_cells) (@UxDK.rf_cells) (Q6nq.gwt_def (@QQRC.Mq3.SHGETC) (@UxDK.SHGETC) (Q6nq.gwt_def (@Q5m9.Mq1.SHGETC) (@UxDK.SHGETC) (Q6nq.gwt_def (@Q5m9.Mq1.RFJ) (@U3qs.RFJ) (Q6nq.gwt_def (@QZxv.Mql.RFJ) (@U3qs.RFJ) (Q6nq.gwt_def (@QQRC.Mq3.M64) (@UxDK.M64) Q6nq.gwt_nil)))))))))))))).
Lemma scanexp_eq : ltac2:(Q6nq.tyx '(@Q5m9.Mq1.scanexp_eq) [[@gw_eq_scanexp_tail]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_scanexp_tail; first [GwInst.gw_exact (@Q5m9.Mq1.scanexp_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@Q5m9.Mq1.scanexp_eq)]. Qed.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - SCANEXP_DEPTH) q
/\ rw_cells rsegs m' Fp (rf_cells T p true fR J)
/\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary.
Lemma gw_eq_scanexp_rpost : @scanexp_rpost = ltac:(GwInst.gw_term (@Q5m9.Mq1.scanexp_rpost rsegs STRING_READ got_ssp ssp_guard) (@scanexp_rpost)). Proof. unfold scanexp_rpost, Q5m9.Mq1.scanexp_rpost; rewrite ?gw_eq_SCANEXP_DEPTH; ltac2:(GwEq.gw_rw [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scanexp_rpost : gw_eqs.

Definition scanexp_rstmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
scanexp fuelc f0 pok = Some (fR, e10) ->
rw_cells rsegs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
(sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
(ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SCANEXP) fc None m (seg_rom rsegs)).
Lemma gw_eq_scanexp_rstmt : @scanexp_rstmt = ltac:(GwInst.gw_term (@Q5m9.Mq1.scanexp_rstmt rsegs 0x5d600 STRING_READ got_ssp ssp_guard) (@scanexp_rstmt)). Proof. unfold scanexp_rstmt, Q5m9.Mq1.scanexp_rstmt; rewrite ?gw_eq_SCANEXP, ?gw_eq_SCANEXP_DEPTH, ?gw_eq_scanexp_rpost; ltac2:(GwEq.gw_rw [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_scanexp_rstmt : gw_eqs.

Section Scanexp.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Hpok : (0 <= pok <= 1)%Z.
Hypothesis Q0 : (0 <= q)%Z.
Hypothesis Q1 : (q < 2^63)%Z.

Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma gw_eq_frame : @frame = ltac:(GwInst.gw_term (@Q5m9.Mq1.frame) (@frame)). Proof. unfold frame, Q5m9.Mq1.frame; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_frame : gw_eqs.
Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
mem_inv rsegs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -80) (frame j8) /\ stk rsegs m (q - SCANEXP_DEPTH) (q + -80)
/\ bytes_at rsegs m T (zbytes txt) /\ ssp_cells m canary.
Lemma gw_eq_finv : @finv = ltac:(GwInst.gw_term (@Q5m9.Mq1.finv rsegs got_ssp ssp_guard) (@finv)). Proof. unfold finv, Q5m9.Mq1.finv; rewrite ?gw_eq_SCANEXP_DEPTH, ?gw_eq_frame; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_finv : gw_eqs.

#[using="Type"] Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.stdio_getc) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.stdio_getc)]. Qed.
#[using="Type"] Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.stdio_unget) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.stdio_unget)]. Qed.

#[using="pre"] Lemma L_ret : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_ret) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]] '([383040]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_ret) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_ret)]. Qed.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_end : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_end) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]] '([383012]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_end) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_end)]. Qed.

#[using="pre Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3"] Lemma L_ND : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_ND) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]] '([382696]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_ND) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_ND)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L3 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_L3) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]] '([382980]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L3) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L3)]. Qed.

Definition LM : Z := 92233720368547758.
Lemma gw_eq_LM : @LM = ltac:(GwInst.gw_term (@Q5m9.Mq1.LM) (@LM)). Proof. unfold LM, Q5m9.Mq1.LM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_LM : gw_eqs.
#[using="Type"] Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof. rewrite ?gw_eq_LM; first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.LM_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.LM_eq)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L2 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_L2) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_LM]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]] '([382864]%Z : list Z) '(Q6nq.gwt_zc LM gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_LM; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L2)]. Qed.

Definition IM : Z := 214748364.
Lemma gw_eq_IM : @IM = ltac:(GwInst.gw_term (@Q5m9.Mq1.IM) (@IM)). Proof. unfold IM, Q5m9.Mq1.IM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_IM : gw_eqs.
#[using="Type"] Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof. rewrite ?gw_eq_IM; first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.IM_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.IM_eq)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_L1 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_L1) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_finv]; [@gw_eq_IM]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]] '([382756]%Z : list Z) '(Q6nq.gwt_zc IM gwt_X)).
Proof. rewrite ?gw_eq_finv, ?gw_eq_IM; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_L1)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1"] Lemma L_E4 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_E4) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_scanexp_tail]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]; [@gw_eq_IM__3; @gw_eq_IM__2; @gw_eq_IM]] '([256; 382688]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_scanexp_tail, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_E4) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_E4)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_C4 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_C4) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_scanexp_tail]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]; [@gw_eq_IM__3; @gw_eq_IM__2; @gw_eq_IM]] '([256; 382656]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_scanexp_tail, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_C4) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_C4)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_SGN : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_SGN) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_scanexp_tail]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]; [@gw_eq_IM__3; @gw_eq_IM__2; @gw_eq_IM]] '([382576]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_scanexp_tail, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_SGN) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_SGN)]. Qed.

#[using="pre post ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_6c : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_6c) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_scanexp_tail]; [@gw_eq_finv]; [@gw_eq_SCANEXP__3; @gw_eq_SCANEXP__2; @gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH__3; @gw_eq_SCANEXP_DEPTH__2; @gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]; [@gw_eq_IM__3; @gw_eq_IM__2; @gw_eq_IM]] '([256; 382568]%Z : list Z) 'gwt_X).
Proof. rewrite ?gw_eq_scanexp_tail, ?gw_eq_finv; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_6c) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_6c)]. Qed.

#[using="pre post fuelc HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Hpok Q1"] Lemma L_main : ltac2:(Q6nq.ty1 'GwI.segs '(@Q5m9.Mq1.L_main) [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_SCANEXP]; [@gw_eq_SCANEXP_DEPTH]; [@gw_eq_scanexp_tail__3; @gw_eq_scanexp_tail__2; @gw_eq_scanexp_tail]; [@gw_eq_scanexp_rpost__3; @gw_eq_scanexp_rpost__2; @gw_eq_scanexp_rpost]; [@gw_eq_scanexp_rstmt__3; @gw_eq_scanexp_rstmt__2; @gw_eq_scanexp_rstmt]; [@gw_eq_frame__3; @gw_eq_frame__2; @gw_eq_frame]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_LM__3; @gw_eq_LM__2; @gw_eq_LM]; [@gw_eq_IM__3; @gw_eq_IM__2; @gw_eq_IM]] '(@nil Z) '(Q6nq.gwt_zc SCANEXP_DEPTH (Q6nq.gwt_zc SCANEXP gwt_X))).
Proof. rewrite ?gw_eq_SCANEXP, ?gw_eq_SCANEXP_DEPTH; ltac2:(GwEq.gw_rw [[@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_main) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.L_main)]. Qed.
End Scanexp.
Lemma gw_eq_frame__2 : @frame = ltac:(GwInst.gw_term (@Q5m9.Mq1.frame) (@frame)). Proof. unfold frame, Q5m9.Mq1.frame; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_frame__2 : gw_eqs.
Lemma gw_eq_finv__2 : @finv = ltac:(GwInst.gw_term (@Q5m9.Mq1.finv rsegs got_ssp ssp_guard) (@finv)). Proof. unfold finv, Q5m9.Mq1.finv; rewrite ?gw_eq_SCANEXP_DEPTH, ?gw_eq_frame__2; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_finv__2 : gw_eqs.
Lemma gw_eq_LM__2 : @LM = ltac:(GwInst.gw_term (@Q5m9.Mq1.LM) (@LM)). Proof. unfold LM, Q5m9.Mq1.LM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_LM__2 : gw_eqs.
Lemma gw_eq_IM__2 : @IM = ltac:(GwInst.gw_term (@Q5m9.Mq1.IM) (@IM)). Proof. unfold IM, Q5m9.Mq1.IM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_IM__2 : gw_eqs.

Lemma scanexp_rspec : scanexp_rstmt.
Proof. rewrite ?gw_eq_scanexp_rstmt; first [GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.scanexp_rspec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q5m9.Mq1.scanexp_rspec)]. Qed.
