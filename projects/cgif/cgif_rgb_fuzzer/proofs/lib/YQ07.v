(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ00 YQ0h YQ09 YQ04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition s_f1 (op : fpop1) (a : sv) : sv :=
match a with
| SLit x => SLit (bv_unsigned (fpop1_denot op (Z_to_bv 64 x)))
| _ => SF1 op a
end.
Definition s_f2 (op : fpop2) (a b : sv) : sv :=
match a, b with
| SLit x, SLit y => SLit (bv_unsigned (fpop2_denot op (Z_to_bv 64 x) (Z_to_bv 64 y)))
| _, _ => SF2 op a b
end.
Definition s_f3 (op : fpop3) (a b c : sv) : sv :=
match a, b, c with
| SLit x, SLit y, SLit z => SLit (bv_unsigned (fpop3_denot op (Z_to_bv 64 x) (Z_to_bv 64 y) (Z_to_bv 64 z)))
| _, _, _ => SF3 op a b c
end.
Lemma lit_of_unsigned : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.
Lemma s_f1_sound : forall E op a, sv_denot E (s_f1 op a) = fpop1_denot op (sv_denot E a).
Proof. intros E op a. destruct a; cbn [s_f1 sv_denot]; try reflexivity. apply lit_of_unsigned. Qed.
Lemma s_f2_sound : forall E op a b, sv_denot E (s_f2 op a b) = fpop2_denot op (sv_denot E a) (sv_denot E b).
Proof. intros E op a b. destruct a; destruct b; cbn [s_f2 sv_denot]; try reflexivity. apply lit_of_unsigned. Qed.
Lemma s_f3_sound : forall E op a b c,
sv_denot E (s_f3 op a b c) = fpop3_denot op (sv_denot E a) (sv_denot E b) (sv_denot E c).
Proof. intros E op a b c. destruct a; destruct b; destruct c; cbn [s_f3 sv_denot]; try reflexivity. apply lit_of_unsigned. Qed.
Definition rm_resolve (rm : bv 3) : option rmode :=
let z := bv_unsigned rm in if z =? 7 then Some RNE else rmode_of_Z z.
Lemma rm_resolve_sound : forall rm md c,
rm_resolve rm = Some md -> frm_zero (c_fcsr c) -> resolve_rm rm c = Some md.
Proof.
intros rm md c H Hf. unfold resolve_rm, rmode_of_field, frm_of. unfold rm_resolve in H.
unfold frm_zero in Hf. rewrite Hf.
destruct (bv_unsigned rm =? 7); [|exact H]. injection H as <-. reflexivity.
Qed.
Inductive fp_out :=
| FO_freg (rd : reg) (v : sv)
| FO_xreg (rd : reg) (v : sv)
| FO_state (ss' : sstate)
| FO_stop (why : stop_reason).
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Definition fp_exec (ss : sstate) (i : instr) : option fp_out :=
let pc := ss_pc ss in
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
let F := sfr_get (ss_fregs ss) in
match i with
| FLoad fmt rd rs1 imm =>
Some (let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => FO_stop (SR_addr a)
| Some (b, off) =>
match fmt with
| FMT_D => match sload segs G (ss_mem ss) b off SZ8 false with
| Some v => FO_freg rd v
| None => FO_stop (SR_load b off)
end
| FMT_S => match sload segs G (ss_mem ss) b off SZ4 false with
| Some v => FO_freg rd (s_f1 FP1_nanbox v)
| None => FO_stop (SR_load b off)
end
end
end)
| FStore fmt rs1 rs2 imm =>
Some (match ss_resv ss with
| Some _ => FO_stop SR_resv
| None =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match addr_of a with
| None => FO_stop (SR_addr a)
| Some (b, off) =>
match sstore (ss_mem ss) b off (match fmt with FMT_S => SZ4 | FMT_D => SZ8 end) (F rs2) with
| Some m' => FO_state (mkSST (pc + 4) (ss_regs ss) (ss_fregs ss) m' None G)
| None => FO_stop (SR_store b off)
end
end
end)
| Fmv FMV_X_F FMT_D rd rs1 => Some (FO_xreg rd (F rs1))
| Fmv FMV_X_F FMT_S rd rs1 => Some (FO_xreg rd (s_ext true 32 (F rs1)))
| Fmv FMV_F_X FMT_D rd rs1 => Some (FO_freg rd (R rs1))
| Fmv FMV_F_X FMT_S rd rs1 => Some (FO_freg rd (s_f1 FP1_nanbox (R rs1)))
| Fsgnj op fmt rd rs1 rs2 => Some (FO_freg rd (s_f2 (FP2_sgnj op fmt) (F rs1) (F rs2)))
| Fari op fmt rd rs1 rs2 rm =>
Some (match rm_resolve rm with
| Some md => FO_freg rd (s_f2 (FP2_ari op fmt md) (F rs1) (F rs2))
| None => FO_stop SR_unsupported
end)
| Fsqrt fmt rd rs1 rm =>
Some (match rm_resolve rm with
| Some md => FO_freg rd (s_f1 (FP1_sqrt fmt md) (F rs1))
| None => FO_stop SR_unsupported
end)
| Fma op fmt rd rs1 rs2 rs3 rm =>
Some (match rm_resolve rm with
| Some md => FO_freg rd (s_f3 (FP3_fma op fmt md) (F rs1) (F rs2) (F rs3))
| None => FO_stop SR_unsupported
end)
| Fminmax op fmt rd rs1 rs2 => Some (FO_freg rd (s_f2 (FP2_minmax op fmt) (F rs1) (F rs2)))
| Fcmp op fmt rd rs1 rs2 => Some (FO_xreg rd (s_f2 (FP2_cmp op fmt) (F rs1) (F rs2)))
| Fclass fmt rd rs1 => Some (FO_xreg rd (s_f1 (FP1_class fmt) (F rs1)))
| Fcvt dst src rd rs1 rm =>
Some (match rm_resolve rm with
| None => FO_stop SR_unsupported
| Some md =>
match fcvt_fty dst, fcvt_fty src with
| Some _, Some _ => FO_freg rd (s_f1 (FP1_cvt dst src md) (F rs1))
| None, Some _ =>
match fcvt_ity dst with
| Some _ => FO_xreg rd (s_f1 (FP1_cvt dst src md) (F rs1))
| None => FO_stop SR_unsupported
end
| Some _, None =>
match fcvt_ity src with
| Some _ => FO_freg rd (s_f1 (FP1_cvt dst src md) (R rs1))
| None => FO_stop SR_unsupported
end
| None, None => FO_stop SR_unsupported
end
end)
| _ => None
end.
Definition fp_apply (ss : sstate) (o : fp_out) : sres :=
match o with
| FO_freg rd v => SRun (setfreg ss rd v (ss_pc ss + 4))
| FO_xreg rd v => SRun (setreg ss rd v (ss_pc ss + 4))
| FO_state ss' => SRun ss'
| FO_stop why => SStop why
end.
Definition sym_stepF (ss : sstate) : sres :=
match clookup tbl (ss_pc ss) with
| None => SStop SR_fetch
| Some wz =>
let w := Z_to_bv 32 wz in
if is_ecall w then SEcall ss else
match decode_any w with
| None => SStop SR_decode
| Some (i, isz) =>
if negb (isz =? 4) then SStop SR_unsupported else
match fp_exec ss i with
| Some o => fp_apply ss o
| None => sym_step segs tbl ss
end
end
end.
Fixpoint sym_runF (fuel : nat) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => match sym_stepF ss with
| SRun ss' => sym_runF f ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
Fixpoint sym_run_toF (fuel : nat) (stop_pc : Z) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => if ss_pc ss =? stop_pc then (ss, RS_running) else
match sym_stepF ss with
| SRun ss' => sym_run_toF f stop_pc ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
Section g.
Hypothesis Htbl : table_ok segs tbl.
Lemma fregs_ok_set' : forall E sfr fregs rd v e,
fregs_ok E sfr fregs -> sv_denot E e = v ->
fregs_ok E (sfr_set sfr rd e) (bvmap_set rd v fregs).
Proof. intros. apply fregs_ok_set; assumption. Qed.
Lemma fget_fregs : forall E sfr regs fregs pc fcsr rv r,
fregs_ok E sfr fregs -> fget (Core regs fregs pc fcsr rv) r = sv_denot E (sfr_get sfr r).
Proof. intros E sfr regs fregs pc fcsr rv r Hf. unfold fget. cbn [c_fregs]. apply Hf. Qed.
Lemma fread_fregs : forall E sfr regs fregs pc fcsr rv fmt r,
fregs_ok E sfr fregs ->
fread (Core regs fregs pc fcsr rv) fmt r = fp_arg fmt (sv_denot E (sfr_get sfr r)).
Proof. intros. unfold fread, fp_arg. rewrite (fget_fregs E sfr) by assumption. reflexivity. Qed.
Definition machF (regs fregs : bvmap 5 word) (pc : word) (fcsr : bv 32) (resv : option word)
(mem : word -> option byte) : machine_state :=
{| ms_regs := regs; ms_fregs := fregs; ms_pc_val := pc; ms_svc_pending := None;
ms_resv := resv; ms_fcsr := fcsr; ms_mem := mem; ms_rom := seg_rom segs |}.
Lemma st_okF_mach : forall E ss regs fregs pc fcsr resv mem,
fregs_ok E (ss_fregs ss) fregs ->
frm_zero fcsr ->
regs_ok E (ss_regs ss) regs ->
pc = Z_to_bv 64 (ss_pc ss) ->
resv = resv_denot E (ss_resv ss) ->
mem_ok segs E mem (ss_mem ss) ->
facts_ok E (ss_facts ss) ->
st_okF segs E ss (machF regs fregs pc fcsr resv mem).
Proof.
intros E ss regs fregs pc fcsr resv mem H1 H5 H7 H2 H4 H8 H9. unfold st_okF, machF; cbn.
split; [exact H1|]. split; [exact H2|]. split; [reflexivity|]. split; [exact H4|].
split; [exact H5|]. split; [reflexivity|]. split; [exact H7|]. exact (conj H8 H9).
Qed.
Lemma low32_zext32 : forall x : bv 32, low32 (zext 64 x) = x.
Proof.
intros x. unfold low32, zext. apply bv_eq. rewrite bv_extract_unsigned, bv_zero_extend_unsigned by lia.
rewrite Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma frm_zero_accrue : forall fcsr fl,
frm_zero fcsr -> frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned fcsr) (fflags_bits fl))).
Proof. intros fcsr fl H. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact H]. Qed.
Ltac fp_pair :=
match goal with
| |- context [let '(_, _) := ?X in _] =>
let v := fresh "v" in let fl := fresh "fl" in let H := fresh "Hop" in
destruct X as [v fl] eqn:H
end.
Ltac fp_fin Hfr Hfcsr Hregs Hresv Hmem HG :=
eexists; split; [reflexivity|]; split; [|cbn [ms_mem]; apply frame_of_refl];
apply st_okF_mach;
cbn [ss_fregs ss_regs ss_pc ss_resv ss_mem ss_facts setfreg setreg];
[ first [exact Hfr | apply fregs_ok_set'; [exact Hfr|] ]
| first [exact Hfcsr | apply frm_zero_accrue; exact Hfcsr]
| first [exact Hregs | apply regs_ok_set'; [exact Hregs|] ]
| apply pc_plus4
| exact Hresv
| exact Hmem
| exact HG ].
Theorem sym_stepF_sound : forall E ss ss' ms,
st_okF segs E ss ms -> sym_stepF ss = SRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okF segs E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros E ss ss' ms HS H.
unfold sym_stepF in H.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
cbv zeta in H.
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; [|discriminate].
destruct (fp_exec ss i) as [o|] eqn:Hx.
2:{
exact (sym_step_soundP segs tbl Htbl P1_trk P5_trk E ss ss' ms HS H). }
apply Z.eqb_eq in Hsz. subst isz.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). rewrite Hec, Hd.
assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
assert (HF : forall fmt r, fread (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) fmt r
= fp_arg fmt (sv_denot E (sfr_get (ss_fregs ss) r))).
{ intros fmt r. apply fread_fregs. exact Hfr. }
assert (HFg : forall r, fget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
= sv_denot E (sfr_get (ss_fregs ss) r)).
{ intros r. apply (fget_fregs E). exact Hfr. }
destruct i; try discriminate Hx; cbn [fp_exec] in Hx;
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv Sem.with_fregs Sem.with_fcsr Sem.fset Sem.fwrite Sem.accrue
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR, ?HFg, ?HF.
-
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (addr_of a) as [[b off]|] eqn:Hao; [|injection Hx as <-; discriminate H].
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct fmt.
+ destruct (sload segs (ss_facts ss) (ss_mem ss) b off SZ4 false) as [v|] eqn:Hsl;
injection Hx as <-; [|discriminate H]. injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
cbn [nbytes nbits] in Hrd, Hv.
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes].
rewrite ov_rdn, Hrd. cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_okF_mach; cbn; auto; [|apply pc_plus4].
apply fregs_ok_set'; [exact Hfr|]. rewrite s_f1_sound. cbn [fpop1_denot]. rewrite Hv.
cbn [load_result nbits]. rewrite low32_zext32. reflexivity.
+ destruct (sload segs (ss_facts ss) (ss_mem ss) b off SZ8 false) as [v|] eqn:Hsl;
injection Hx as <-; [|discriminate H]. injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
cbn [nbytes nbits] in Hrd, Hv.
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes].
rewrite ov_rdn, Hrd. cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
eexists. split; [reflexivity|]. split; [|cbn [ms_mem]; apply frame_of_refl].
apply st_okF_mach; cbn; auto; [|apply pc_plus4].
apply fregs_ok_set'; [exact Hfr|]. rewrite Hv, bv_extract_0_64. reflexivity.
-
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [injection Hx as <-; discriminate H|]. cbn in Hresv. subst resv.
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (addr_of a) as [[b off]|] eqn:Hao; [|injection Hx as <-; discriminate H].
remember (match fmt with FMT_S => SZ4 | FMT_D => SZ8 end) as sz eqn:Hszf.
destruct (sstore (ss_mem ss) b off sz (sfr_get (ss_fregs ss) rs2)) as [m'|] eqn:Hst;
injection Hx as <-; [|discriminate H]. injection H as <-.
pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (addr_of_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct fmt; subst sz; cbn [nbytes nbits] in Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite Hok; unfold inval_resv;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
eexists; (split; [reflexivity|]);
(split; [apply st_okF_mach; cbn; auto; apply pc_plus4
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ]).
all: unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
-
destruct (rm_resolve rm) as [md|] eqn:Hrm; injection Hx as <-; [|discriminate H]. injection H as <-.
rewrite (rm_resolve_sound rm md _ Hrm) by exact Hfcsr.
destruct op; cbv beta iota zeta; fp_pair; destruct fmt; cbv beta iota zeta;
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f3_sound; cbn [fpop3_denot fma_args fp_res]; rewrite Hop; reflexivity.
-
destruct (rm_resolve rm) as [md|] eqn:Hrm; injection Hx as <-; [|discriminate H]. injection H as <-.
rewrite (rm_resolve_sound rm md _ Hrm) by exact Hfcsr.
destruct op; cbv beta iota zeta; fp_pair; destruct fmt; cbv beta iota zeta;
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f2_sound; cbn [fpop2_denot fari_sem fp_res]; rewrite Hop; reflexivity.
-
destruct (rm_resolve rm) as [md|] eqn:Hrm; injection Hx as <-; [|discriminate H]. injection H as <-.
rewrite (rm_resolve_sound rm md _ Hrm) by exact Hfcsr.
fp_pair; destruct fmt; cbv beta iota zeta;
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f1_sound; cbn [fpop1_denot fp_res]; rewrite Hop; reflexivity.
-
injection Hx as <-. injection H as <-.
destruct fmt; cbv beta iota zeta; fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f2_sound; cbn [fpop2_denot]; reflexivity.
-
injection Hx as <-. injection H as <-.
fp_pair; destruct fmt; cbv beta iota zeta; fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f2_sound; cbn [fpop2_denot fp_res]; rewrite Hop; reflexivity.
-
injection Hx as <-. injection H as <-.
destruct op; cbv beta iota zeta; fp_pair; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f2_sound; cbn [fpop2_denot fcmp_sem]; rewrite Hop; cbn [fst]; destruct v; reflexivity.
-
destruct (rm_resolve rm) as [md|] eqn:Hrm; [|injection Hx as <-; discriminate H].
rewrite (rm_resolve_sound rm md _ Hrm) by exact Hfcsr.
destruct dst, src; cbn [fcvt_fty fcvt_ity] in Hx; injection Hx as <-; try discriminate H;
injection H as <-; cbv beta iota zeta; rewrite ?HF, ?HR; fp_pair;
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG;
rewrite s_f1_sound; cbn [fpop1_denot fcvt_denot fcvt_fty fcvt_ity fp_res int_res Z.eqb Pos.eqb];
rewrite Hop; reflexivity.
-
destruct dir, fmt; injection Hx as <-; injection H as <-; cbv beta iota zeta;
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG.
+ rewrite s_ext_sound. cbn [sv_denot]. reflexivity.
+ reflexivity.
+ rewrite s_f1_sound. cbn [fpop1_denot]. reflexivity.
+ reflexivity.
-
injection Hx as <-. injection H as <-. rewrite ?rset_core.
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
fp_fin Hfr Hfcsr Hregs Hresv Hmem HG.
rewrite s_f1_sound. cbn [fpop1_denot]. reflexivity.
Qed.
Theorem sym_stepF_ecall : forall E ss ss' ms,
st_okF segs E ss ms -> sym_stepF ss = SEcall ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okF_ecall segs E ss' ms'
/\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof.
intros E ss ss' ms HS H.
apply (sym_step_ecallP segs tbl Htbl P1_trk P5_trk E ss ss' ms HS).
unfold sym_stepF, sym_step in H. unfold sym_step.
destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in H |- *.
destruct (is_ecall (Z_to_bv 32 wz)); [exact H|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct (isz =? 4); cbn [negb] in H |- *; [|discriminate].
destruct (fp_exec ss i) as [o|] eqn:Hx; [|exact H].
exfalso. destruct o; cbn [fp_apply] in H; discriminate.
Qed.
Lemma sym_stepF_skeleton : forall ss ss',
sym_stepF ss = SRun ss' -> skeleton (ss_mem ss') = skeleton (ss_mem ss).
Proof.
intros ss ss' H. unfold sym_stepF in H.
destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in H.
destruct (is_ecall (Z_to_bv 32 wz)); [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; [|discriminate].
destruct (fp_exec ss i) as [o|] eqn:Hx; [| exact (sym_step_skeleton segs tbl ss ss' H)].
destruct i; try discriminate Hx; cbn [fp_exec] in Hx;
repeat match type of Hx with
| context [sstore ?rs ?b ?off ?sz ?v] =>
destruct (sstore rs b off sz v) eqn:?Hst; [|try (injection Hx as <-; discriminate H)]
| context [match ?x with _ => _ end] => destruct x; try (injection Hx as <-; discriminate H)
end;
injection Hx as <-; cbn [fp_apply] in H; try discriminate H; injection H as <-; cbn; try reflexivity.
all: try (eapply store_region_skeleton; eassumption).
Qed.
Theorem sym_runF_sound : forall fuel E ss ss' st ms,
st_okF segs E ss ms -> sym_runF fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okF_ecall segs E ss' ms'
| _ => st_okF segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros E ss ss' st ms HS H; cbn [sym_runF] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (sym_stepF ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_stepF_sound E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_stepF_skeleton ss ss1 Hs) as Hsk1.
destruct (IH E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_stepF_ecall E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
Theorem sym_run_toF_sound : forall fuel stop E ss ss' st ms,
st_okF segs E ss ms -> sym_run_toF fuel stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okF_ecall segs E ss' ms'
| _ => st_okF segs E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stop E ss ss' st ms HS H; cbn [sym_run_toF] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (ss_pc ss =? stop).
{ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl]. }
destruct (sym_stepF ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_stepF_sound E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_stepF_skeleton ss ss1 Hs) as Hsk1.
destruct (IH stop E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_stepF_ecall E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
End g.
Definition fp_of (ms : machine_state) : FPState := mkFP (ms_fregs ms) (ms_fcsr ms).
Lemma st_okF_to_legacy : forall E ss ms,
st_okF segs E ss ms -> @st_ok segs (fp_of ms) E ss ms.
Proof.
intros E ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_ok. repeat (split; [first [reflexivity | assumption]|]). exact H9.
Qed.

Lemma st_ok_to_F : forall (fx : FPState) E ss ms,
@st_ok segs fx E ss ms -> fregs_ok E (ss_fregs ss) fp_regs -> frm_zero fp_csr ->
st_okF segs E ss ms.
Proof.
intros fx E ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hf Hc.
unfold st_okF. rewrite H1, H5. repeat (split; [first [reflexivity | assumption]|]). exact H9.
Qed.
Lemma st_okF_frm : forall E ss ms, st_okF segs E ss ms -> frm_zero (ms_fcsr ms).
Proof. intros E ss ms (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma st_okF_fregs_ok : forall E ss ms, st_okF segs E ss ms -> fregs_ok E (ss_fregs ss) (ms_fregs ms).
Proof. intros E ss ms (H & _). exact H. Qed.
Lemma st_okF_freg : forall E ss ms r,
st_okF segs E ss ms -> reg_get (ms_fregs ms) r = sv_denot E (sfr_get (ss_fregs ss) r).
Proof. intros E ss ms r HS. apply (st_okF_fregs_ok E ss ms HS). Qed.
Lemma st_okF_regs_ok : forall E ss ms, st_okF segs E ss ms -> regs_ok E (ss_regs ss) (ms_regs ms).
Proof. intros E ss ms (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.



Lemma st_okF_mkst : forall E ss ms,
st_okF segs E ss ms -> ss_resv ss = None ->
ms = @mkst (fp_of ms) (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom segs).
Proof.
intros E ss ms HS Hrv. exact (@st_ok_mkst segs (fp_of ms) E ss ms (st_okF_to_legacy E ss ms HS) Hrv).
Qed.


Lemma st_okF_add_cond : forall E ss ms c a b,
st_okF segs E ss ms -> branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_okF segs E (add_cond ss (mkAC c a b)) ms.
Proof.
intros E ss ms c a b HS Hb. pose proof (st_okF_fregs_ok E ss ms HS) as Hf. pose proof (st_okF_frm E ss ms HS) as Hc.
apply (st_ok_to_F (fp_of ms)); [| exact Hf | exact Hc].
apply st_ok_add_cond; [apply st_okF_to_legacy; exact HS | exact Hb].
Qed.
Lemma st_okF_add_cond_neg : forall E ss ms c a b,
st_okF segs E ss ms -> branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_okF segs E (add_cond ss (mkAC (neg_bc c) a b)) ms.
Proof.
intros E ss ms c a b HS Hb. apply st_okF_add_cond; [exact HS|]. rewrite branch_taken_neg, Hb. reflexivity.
Qed.

Lemma st_okF_add_alias : forall E ss ms a b,
st_okF segs E ss ms -> sv_denot E a = sv_denot E b -> st_okF segs E (add_alias ss a b) ms.
Proof.
intros E ss ms a b HS Hab.
apply (st_ok_to_F (fp_of ms)); [| exact (st_okF_fregs_ok E ss ms HS) | exact (st_okF_frm E ss ms HS)].
apply st_ok_add_alias; [apply st_okF_to_legacy; exact HS | exact Hab].
Qed.


Lemma st_okF_branch : forall E ss ms (Q : Prop) c a b,
st_okF segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_okF segs E (add_cond ss (mkAC c a b)) ms -> Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> st_okF segs E (add_cond ss (mkAC (neg_bc c) a b)) ms -> Q) ->
Q.
Proof.
intros E ss ms Q c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_okF_add_cond; [exact HS | exact Hb].
- apply Hf; [reflexivity|]. apply st_okF_add_cond_neg; [exact HS | exact Hb].
Qed.



Definition sfr_atoms (k : nat) : list sv := map (fun i => SOff (k + i) 0) (seq 0 32).
Definition ew_fregs (E : env) (k : nat) (fregs : bvmap 5 word) : env :=
mkEnv (fun i => if (k <=? i)%nat && (i <? k + 32)%nat
then reg_get fregs (Z_to_bv 5 (Z.of_nat (i - k))) else ew E i)
(ed E).
Lemma env_agree_ew_fregs : forall E k fregs, env_agree k E (ew_fregs E k fregs).
Proof.
intros E k fregs. split; [|reflexivity]. intros n Hn. cbn [ew ew_fregs].
destruct (Nat.leb_spec k n); [lia|]. reflexivity.
Qed.
Lemma sfr_get_atoms : forall k r, sfr_get (sfr_atoms k) r = SOff (k + ridx r) 0.
Proof.
intros k r. unfold sfr_get, sfr_atoms. pose proof (u5_range r) as Hr.
assert (Hi : (ridx r < 32)%nat) by (unfold ridx; lia).
rewrite (nth_indep _ (SLit 0) (SOff (k + 0) 0)) by (rewrite length_map, length_seq; exact Hi).
change (SOff (k + 0)%nat 0) with ((fun i => SOff (k + i) 0) 0%nat).
rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Lemma fregs_ok_atoms : forall E k fregs, fregs_ok (ew_fregs E k fregs) (sfr_atoms k) fregs.
Proof.
intros E k fregs r. rewrite sfr_get_atoms. cbn [sv_denot ew ew_fregs].
pose proof (u5_range r) as Hr.
replace ((k <=? k + ridx r)%nat && (k + ridx r <? k + 32)%nat) with true
by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; unfold ridx; lia).
replace (k + ridx r - k)%nat with (ridx r) by lia.
unfold ridx. rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma st_ok_enterF : forall (fx : FPState) k E ss ms,
@st_ok segs fx E ss ms -> ss_atoms_lt k ss = true -> frm_zero (@fp_csr fx) ->
st_okF segs (ew_fregs E k (@fp_regs fx))
(mkSST (ss_pc ss) (ss_regs ss) (sfr_atoms k) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fx k E ss ms HS Hat Hc.
pose proof (@st_ok_agree segs fx k E (ew_fregs E k fp_regs) ss ms HS (env_agree_ew_fregs E k _) Hat)
as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold st_okF; cbn. rewrite H1, H5.
split; [apply fregs_ok_atoms|]. repeat (split; [assumption|]). exact H9.
Qed.



End d.
