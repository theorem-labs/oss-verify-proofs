(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G Require T_rfj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SHLIM : Z := 0x5b640.
Lemma gw_eq_SHLIM : @SHLIM = ltac:(GwInst.gw_term (@QQRC.Mq3.SHLIM 0x5b640) (@SHLIM)). Proof. unfold SHLIM, QQRC.Mq3.SHLIM; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SHLIM : gw_eqs.
Definition SHGETC : Z := 0x5b678.
Lemma gw_eq_SHGETC : @SHGETC = ltac:(GwInst.gw_term (@QQRC.Mq3.SHGETC 0x5b640) (@SHGETC)). Proof. unfold SHGETC, QQRC.Mq3.SHGETC; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_SHGETC : gw_eqs.
Definition UFLOW : Z := 0x5b740.
Lemma gw_eq_UFLOW : @UFLOW = ltac:(GwInst.gw_term (@QQRC.Mq3.UFLOW 0x5b640) (@UFLOW)). Proof. unfold UFLOW, QQRC.Mq3.UFLOW; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_UFLOW : gw_eqs.
Definition TOREAD : Z := 0x5b7cc.
Lemma gw_eq_TOREAD : @TOREAD = ltac:(GwInst.gw_term (@QQRC.Mq3.TOREAD 0x5b640) (@TOREAD)). Proof. unfold TOREAD, QQRC.Mq3.TOREAD; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_TOREAD : gw_eqs.
Definition STRING_READ : Z := 0x545d8.

Definition got_ssp := 0x659d0%Z.
Definition ssp_guard := 0x97e70%Z.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5b640%Z.
Definition w_71 := 0x0000a517%Z.
Definition w_72 := 0x27453903%Z.
Definition w_98 := 0x85df50ef%Z.
Definition hi_71 := (Z_to_bv 20 10).
Definition lo_72 := (Z_to_bv 12 628).
Definition joff_98 := (Z_to_bv 21 2054236).
Definition got_ssp := got_ssp.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5b640 (QQRC.Mq3.shgetc_code 0x0000a517%Z 0x27453903%Z 0x85df50ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5b640 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5b640 /\ 0x5b640 + 544 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
End GwI.

Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].
Lemma gw_eq_ssp_cells : @ssp_cells = ltac:(GwInst.gw_term (@QQRC.Mq3.ssp_cells rsegs got_ssp ssp_guard) (@ssp_cells)). Proof. unfold ssp_cells, QQRC.Mq3.ssp_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ssp_cells : gw_eqs.

Notation rfj := G.T_rfj.rfj.
Notation mkJ := G.T_rfj.mkJ.
Notation j_flags := G.T_rfj.j_flags.
Notation j_pad0 := G.T_rfj.j_pad0.
Notation j_close := G.T_rfj.j_close.
Notation j_wend := G.T_rfj.j_wend.
Notation j_wpos := G.T_rfj.j_wpos.
Notation j_mbz1 := G.T_rfj.j_mbz1.
Notation j_wbase := G.T_rfj.j_wbase.
Notation j_read := G.T_rfj.j_read.
Notation j_write := G.T_rfj.j_write.
Notation j_seek := G.T_rfj.j_seek.
Notation j_bufsize := G.T_rfj.j_bufsize.
Notation j_prev := G.T_rfj.j_prev.
Notation j_next := G.T_rfj.j_next.
Notation j_fd := G.T_rfj.j_fd.
Notation j_ppid := G.T_rfj.j_ppid.
Notation j_lockcount := G.T_rfj.j_lockcount.
Notation j_mode := G.T_rfj.j_mode.
Notation j_lock := G.T_rfj.j_lock.
Notation j_lbf := G.T_rfj.j_lbf.
Notation j_pad1 := G.T_rfj.j_pad1.
Notation j_cookie := G.T_rfj.j_cookie.
Notation j_off := G.T_rfj.j_off.
Notation j_getln := G.T_rfj.j_getln.
Notation j_mbz2 := G.T_rfj.j_mbz2.
Notation j_pl := G.T_rfj.j_pl.
Notation j_nl := G.T_rfj.j_nl.
Notation j_locale := G.T_rfj.j_locale.

Definition M64 : Z := 18446744073709551615.
Lemma gw_eq_M64 : @M64 = ltac:(GwInst.gw_term (@QQRC.Mq3.M64) (@M64)). Proof. unfold M64, QQRC.Mq3.M64; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_M64 : gw_eqs.

Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
if sh_stdio f then (if w then T + p else T) else M64.
Lemma gw_eq_rf_rend : @rf_rend = ltac:(GwInst.gw_term (@QQRC.Mq3.rf_rend) (@rf_rend)). Proof. unfold rf_rend, QQRC.Mq3.rf_rend; rewrite ?gw_eq_M64; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rf_rend : gw_eqs.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].
Lemma gw_eq_rf_cells : @rf_cells = ltac:(GwInst.gw_term (@QQRC.Mq3.rf_cells) (@rf_cells)). Proof. unfold rf_cells, QQRC.Mq3.rf_cells; rewrite ?gw_eq_M64, ?gw_eq_rf_rend; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rf_cells : gw_eqs.

Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
let rend := rf_rend T p w f in
[C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
C8 she; C8 shl; C8 shc;
C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].
Lemma gw_eq_rf_cells_raw : @rf_cells_raw = ltac:(GwInst.gw_term (@QQRC.Mq3.rf_cells_raw) (@rf_cells_raw)). Proof. unfold rf_cells_raw, QQRC.Mq3.rf_cells_raw; rewrite ?gw_eq_rf_rend; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rf_cells_raw : gw_eqs.

Lemma rf_cells_raw_eq : ltac2:(Q6nq.tyx '(@QQRC.Mq3.rf_cells_raw_eq) [[@gw_eq_M64]; [@gw_eq_rf_rend]; [@gw_eq_rf_cells]; [@gw_eq_rf_cells_raw]; [@gw_eq_SHLIM__3; @gw_eq_SHLIM__2; @gw_eq_SHLIM]; [@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_UFLOW__3; @gw_eq_UFLOW__2; @gw_eq_UFLOW]; [@gw_eq_TOREAD__3; @gw_eq_TOREAD__2; @gw_eq_TOREAD]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]] '(@nil Z) '(Q6nq.gwt_zc M64 Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_M64, ?gw_eq_rf_rend, ?gw_eq_rf_cells, ?gw_eq_rf_cells_raw; first [GwInst.gw_exact (@QQRC.Mq3.rf_cells_raw_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq3.rf_cells_raw_eq)]. Qed.

Lemma rf_cells_size : ltac2:(Q6nq.tyx '(@QQRC.Mq3.rf_cells_size) [[@gw_eq_rf_cells]; [@gw_eq_SHLIM__3; @gw_eq_SHLIM__2; @gw_eq_SHLIM]; [@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_UFLOW__3; @gw_eq_UFLOW__2; @gw_eq_UFLOW]; [@gw_eq_TOREAD__3; @gw_eq_TOREAD__2; @gw_eq_TOREAD]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_M64__3; @gw_eq_M64__2; @gw_eq_M64]; [@gw_eq_rf_rend__3; @gw_eq_rf_rend__2; @gw_eq_rf_rend]; [@gw_eq_rf_cells_raw__3; @gw_eq_rf_cells_raw__2; @gw_eq_rf_cells_raw]] '([232]%Z : list Z) 'Q6nq.gwt_nil).
Proof. rewrite ?gw_eq_rf_cells; first [GwInst.gw_exact (@QQRC.Mq3.rf_cells_size) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq3.rf_cells_size)]. Qed.

Definition ssJ : rfj :=
mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).
Lemma gw_eq_ssJ : @ssJ = ltac:(GwInst.gw_term (@QQRC.Mq3.ssJ STRING_READ) (@ssJ)). Proof. unfold ssJ, QQRC.Mq3.ssJ; rewrite ?gw_eq_M64; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ssJ : gw_eqs.

Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\
(sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.
Lemma gw_eq_RFI : @RFI = ltac:(GwInst.gw_term (@QQRC.Mq3.RFI STRING_READ) (@RFI)). Proof. unfold RFI, QQRC.Mq3.RFI; rewrite ?gw_eq_ssJ; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_RFI : gw_eqs.

Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Fp (rf_cells T p w (sh_lim0 f) J).
Lemma gw_eq_shlim_post : @shlim_post = ltac:(GwInst.gw_term (@QQRC.Mq3.shlim_post rsegs) (@shlim_post)). Proof. unfold shlim_post, QQRC.Mq3.shlim_post; rewrite ?gw_eq_rf_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shlim_post : gw_eqs.

Definition shlim_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
rw_cells rsegs m Fp (rf_cells_raw T p w f J she shl shc) ->
sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
(0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
mem_inv rsegs m ->
evt rsegs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHLIM) fc None m (seg_rom rsegs)).
Lemma gw_eq_shlim_stmt : @shlim_stmt = ltac:(GwInst.gw_term (@QQRC.Mq3.shlim_stmt rsegs 0x5b640) (@shlim_stmt)). Proof. unfold shlim_stmt, QQRC.Mq3.shlim_stmt; rewrite ?gw_eq_SHLIM, ?gw_eq_rf_cells_raw, ?gw_eq_shlim_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_shlim_stmt : gw_eqs.

Ltac show_goal := match goal with |- ?g => idtac g end.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
end.
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. first [GwInst.gw_exact (@QQRC.Mq3.sx32_M64) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq3.sx32_M64)]. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. first [GwInst.gw_exact (@QQRC.Mq3.zx32_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@QQRC.Mq3.zx32_lit)]. Qed.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Lemma shlim_spec : shlim_stmt.
Proof. rewrite ?gw_eq_shlim_stmt; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq3.shlim_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq3.shlim_spec)]. Qed.

Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma gw_eq_zero4 : @zero4 = ltac:(GwInst.gw_term (@QQRC.Mq3.zero4) (@zero4)). Proof. unfold zero4, QQRC.Mq3.zero4; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_zero4 : gw_eqs.
Definition w0 : word := Z_to_bv 64 0.
Lemma gw_eq_w0 : @w0 = ltac:(GwInst.gw_term (@QQRC.Mq3.w0) (@w0)). Proof. unfold w0, QQRC.Mq3.w0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_w0 : gw_eqs.

Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
[C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
C8 w0; C8 w0; C8 w0].
Lemma gw_eq_ss_cells : @ss_cells = ltac:(GwInst.gw_term (@QQRC.Mq3.ss_cells STRING_READ) (@ss_cells)). Proof. unfold ss_cells, QQRC.Mq3.ss_cells; rewrite ?gw_eq_M64, ?gw_eq_zero4, ?gw_eq_w0; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_ss_cells : gw_eqs.

Lemma rf_cells_ss : ltac2:(Q6nq.ty1 'GwI.segs '(@QQRC.Mq3.rf_cells_ss) [[@gw_eq_M64]; [@gw_eq_rf_rend]; [@gw_eq_rf_cells]; [@gw_eq_ssJ]; [@gw_eq_ss_cells]; [@gw_eq_SHLIM__3; @gw_eq_SHLIM__2; @gw_eq_SHLIM]; [@gw_eq_SHGETC__3; @gw_eq_SHGETC__2; @gw_eq_SHGETC]; [@gw_eq_UFLOW__3; @gw_eq_UFLOW__2; @gw_eq_UFLOW]; [@gw_eq_TOREAD__3; @gw_eq_TOREAD__2; @gw_eq_TOREAD]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_rf_cells_raw__3; @gw_eq_rf_cells_raw__2; @gw_eq_rf_cells_raw]; [@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_shlim_post__3; @gw_eq_shlim_post__2; @gw_eq_shlim_post]; [@gw_eq_shlim_stmt__3; @gw_eq_shlim_stmt__2; @gw_eq_shlim_stmt]; [@gw_eq_zero4__3; @gw_eq_zero4__2; @gw_eq_zero4]; [@gw_eq_w0__3; @gw_eq_w0__2; @gw_eq_w0]] '(@nil Z) '(Q6nq.gwt_zc M64 Q6nq.gwt_nil)).
Proof. rewrite ?gw_eq_M64, ?gw_eq_rf_rend, ?gw_eq_rf_cells, ?gw_eq_ssJ, ?gw_eq_ss_cells; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq3.rf_cells_ss) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq3.rf_cells_ss)]. Qed.

Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 16) (q)
/\ rw_cells rsegs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).
Lemma gw_eq_toread_post : @toread_post = ltac:(GwInst.gw_term (@QQRC.Mq3.toread_post rsegs STRING_READ) (@toread_post)). Proof. unfold toread_post, QQRC.Mq3.toread_post; rewrite ?gw_eq_M64, ?gw_eq_ss_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_toread_post : gw_eqs.

Definition toread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
(0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
stk rsegs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 TOREAD) fc None m (seg_rom rsegs)).
Lemma gw_eq_toread_stmt : @toread_stmt = ltac:(GwInst.gw_term (@QQRC.Mq3.toread_stmt rsegs 0x5b640 STRING_READ) (@toread_stmt)). Proof. unfold toread_stmt, QQRC.Mq3.toread_stmt; rewrite ?gw_eq_TOREAD, ?gw_eq_M64, ?gw_eq_ss_cells, ?gw_eq_toread_post; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_toread_stmt : gw_eqs.

Lemma toread_spec : toread_stmt.
Proof. rewrite ?gw_eq_toread_stmt; first [GwApply.gw_by_name GwI.segs (@QQRC.Mq3.toread_spec) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQRC.Mq3.toread_spec)]. Qed.

