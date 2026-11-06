(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgMain0.v at 6ebe35ba632 (the harness entry
   segment: the save area, sp1, the call of the side stack for frames, the frame facts, the frame and shadow regions,
   the header and shadow writes, the hand-off) made the first segment of reac_box_pin_parse on reac-pw/fuzz_pin's
   image A (fuzz_pin.asan). rule 24: no function proved (a segment of the walk). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgParse0.v of this library, for image B
   (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f): 0x80ba4 -> the
   cut P1 at 0x80cac (lib/AU/PPgParseCx.v ss_P1). What differs from the A file, each read from the neutral excerpt
   of 0x80ba4-0x80ca8:
   - 192-byte save area (`addi sp,sp,-0xc0` 0x80ba4, `sd zero,0(sp)` at sp-192, ra .. s11 at sp-8 .. sp-104, the
     same slots as in image A), `andi sp,sp,-0x20` at 0x80be4: sp1 = 32 * ((sp - 192) / 32) in [sp - 208, sp - 192];
     the stack region is trimmed to the saves [-104, 0) and region 70 = [sp1+8, sp1+88) holds the spill of F at
     sp1+0x50 (`sd s7,0x50(s1)` 0x80c4c);
   - the GOT loads at 0x80bf4-0x80c08 (0x991c8 -> 0xa1700, the option word 1; 0x99170 -> 0xa16f8, SB into s4),
     `beqz a2` at 0x80c10 decided by the option word, `li a0,0x40` and `jal 0x3c8e4` at 0x80c14 / 0x80c18 (RA
     0x80c1c), the call site lemma pin_fs0_site at RA 0x80c1c;
   - 0x80c1c-0x80ca8: s3 = s7 = F (`mv s3,a0`, `mv s7,s3`), `bnez s3` at 0x80c2c decided by HPTR 5 on F (the probe
     loop 0x80c30-0x80c48 is not reached), the header words F+0 = 0x41B58AB3, F+8 = 0x10add, F+16 = 0x80ba4 (stored
     through s7), s11 = SB + F/8, the 8 shadow bytes f1 f1 f1 f1 f8 f3 f3 f3, a3 = -1; the run stops at 0x80cac.
   No trap branch is in this segment. The proof text is the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgParseLib PPgParseCx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The windows a run may write (kept_of_frame's premise): every window of the regions before the run lies in Zs. *)
Ltac p0_win AG :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Ha;
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (b, wlo, whi) l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Ha; revert Ha; evalE AG; intros Ha; cbv beta;
first [lia | unfold pp_nf, SHADOW_OFF; lia] |]); destruct Hin.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* donor APgMain0.v:136-144 (A/ACer.v:156-164) *)
Lemma pp0_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* A materialization of the model keeps its I/O. *)
Lemma pp0_sio_wvb : forall m X, same_io m (with_vm_backing (m_vm_lazy m) X m).
Proof. intros m X. apply same_io_materialized. apply same_but_materialized_wvb_any. Qed.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Local Notation code := (as_code B).

(* The call site 0x80c18 (`jal 0x3c8e4`, the class-0 frame of the side stack for frames): with sp = sp1, gp, tp
   as at entry and ra = 0x80c1c, the state supplies every premise of aj_stack_malloc_atS at o = sp1 - sp0
   (stack offset, alignment, room below sp1 inside the caller's budget, gp, tp, the return address, the free
   class-0 frame of the contract) and the ecall_pre facts of astack_malloc_realizes. *)
Lemma pin_fs0_site : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
(regsT : bvmap 5 word) memT mdT sp1,
pin_pre_kit tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch T_parse_STK EV_parse ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k ->
sp1 = 32 * ((spZ regs + -192) / 32) -> getr regsT 2 = Z_to_bv 64 sp1 ->
getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 -> getr regsT 1 = Z_to_bv 64 0x80c1c ->
count_cid 0 (frames Sc) < fs_frames 0 ->
spZ regsT = sp0 + (sp1 - sp0) /\ (sp1 - sp0) mod 16 = 0 /\ sp1 - sp0 <= 0 /\ ESTACK - (sp1 - sp0) <= STK /\
getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ YK0s.ret_ok (getr regsT 1) /\
count_cid 0 (frames Sc) < fs_frames 0 /\
ecall_pre tfibsegs B lyc Sc W regsT memT mdT.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch regsT memT mdT sp1 HPK HJT Esp1 R2 R3 R4 R1 Hcnt.
destruct HPK as (HJ & Hraok & Hra4 & Hgp & Htp & Hch & Hal16 & Hwin & Hsp0 & Hev).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (asan_consts) as (C1 & _).
assert (WS : T_parse_STK = 8400) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (sp1_facts (spZ regs + -192) ltac:(clear - Hceil Hslo Hstk0 Hwin WS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & _ & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al16.
assert (Hsp : spZ regsT = sp0 + (sp1 - sp0)).
{ unfold spZ at 1. rewrite R2, unsigned_lit_small by (clear - Hsp1r Hceil Hslo Hstk0 Hwin WS C1 Hsp0 Hshi H47; lia). lia. }
assert (Hal : (sp1 - sp0) mod 16 = 0) by (rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity).
assert (Hneg : sp1 - sp0 <= 0) by (clear - Hsp1r Hsp0; lia).
assert (Hbud : ESTACK - (sp1 - sp0) <= STK) by (rewrite Hes; clear - Hsp1r Hwin WS; lia).
assert (Hgp' : getr regsT 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp).
assert (Htp' : getr regsT 4 = w64 (as_tp B)) by (rewrite R4; exact Htp).
assert (Hra' : YK0s.ret_ok (getr regsT 1)) by (rewrite R1; vm_compute; reflexivity).
split; [exact Hsp|]. split; [exact Hal|]. split; [exact Hneg|]. split; [exact Hbud|].
split; [exact Hgp'|]. split; [exact Htp'|]. split; [exact Hra'|]. split; [exact Hcnt|].
exact (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT (sp1 - sp0) HJT Hsp Hal Hneg Hbud Hra' Hgp' Htp').
Qed.

(* reac_box_pin_parse 0x80ba4 -> 0x80cac *)
Lemma pp_seg0 : PP_seg0 B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg0. intros PF cx HPRE. unfold pp_from in PF.
pose proof HPRE as HPRE0.
pose proof (pp_entry B MT RLO RHI cat TP DP cx TL LAWS HPRE) as HS.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos0 sp10 E00].
unfold pp_pre in HPRE.
cbn [c_STK c_sp0 c_FP c_ly c_S c_W0 c_mem0 c_md0 c_own c_lyc c_Sc c_W c_memc c_mdc c_k c_regs c_ch c_sa c_mo c_lb c_s
c_cidm c_posm c_cidl c_posl c_fpos c_sp1 c_E0] in HPRE, HS |- *.
destruct HPRE as (HPK & H10 & H11 & H12 & Hsa & Hmo & Hlb & Hstr & Hlive & HPREr).
(* the free class-0 frame of the contract (CP1.7), wherever it sits in the rest of the premise list *)
assert (Hcnt : count_cid 0 (frames Sc) < fs_frames 0)
by (clear - HPREr; repeat (lazymatch type of HPREr with
| count_cid _ _ < _ => exact HPREr
| _ /\ _ => first [exact (proj1 HPREr) | apply proj2 in HPREr] end)).
clear HPREr.
pose proof HPK as HPK0.
destruct HPK as (HJ & Hraok & Hra4 & Hgp & Htp & Hch & Hal16 & Hwin & Hsp0 & Hev).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : T_parse_STK = 8400) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the caller's cells the walk may change (none in this segment), below the allocation ceiling and off the image *)
set (OC := fun a => pin_parse_live sa mo lb = true /\ pin_out_cell mo lb a).
assert (HOCF : pp_oc_frames lyc Sc (pin_parse_live sa mo lb) mo lb cidm posm cidl posl).
{ intros Hl. destruct (Hlive Hl) as (_ & _ & _ & Hm & _ & _ & Hm1 & Hm2 & Hb & _ & _ & Hb1 & Hb2 & _).
rewrite Hfrs. split; [apply in_or_app; left; exact Hm|]. split; [exact Hm1|]. split; [exact Hm2|].
split; [apply in_or_app; left; exact Hb|]. split; [exact Hb1 | exact Hb2]. }
destruct (pp_oc_sep tfibsegs B LAWS lyc Sc W memc mdc _ mo lb cidm posm cidl posl HAR HOCF) as (HOCc & _).
pose proof (pp_oc_img B lyc Sc W memc mdc _ mo lb cidm posm cidl posl HAR HOCF) as HOCi.
assert (Hce : alloc_ceiling <= spZ regs - T_parse_STK) by (clear - Hceil Hslo Hwin; lia).
assert (Hs64 : spZ regs <= 2 ^ 64) by (clear - Hsp0 Hshi H47; lia).
(* the kept-memory fact at entry (grant's CtrlParse.v:102) *)
pose proof (pz_kept_refl tfibsegs B lyc Sc W memc (spZ regs - T_parse_STK) (spZ regs) OC
ltac:(intros a Ha; apply Hpres; clear - Ha Hwin Hsp0; lia)) as KP.
remember (Ereg regs pp_extra) as E eqn:HE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros nn r Hnn; rewrite HE; apply ew_Ereg_nat; exact Hnn).
clear HE.
unfold cfg_at. change (w64 A_PARSE) with (Z_to_bv 64 A_PARSE).
shok_auto SHOK PPBx E (mrestrict (w_H W) memc).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
(* 0x80ba4-0x80be4: the save area and andi sp,sp,-0x20; stop at 0x80be8 (donor :199-200) *)
aj_run_to_tok tfibtbl_lib_ok HS HJ SHOK PPBspan 0x80be8.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | evalE AG; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* what the run kept of the caller's memory: its windows lie in [sp - T_parse_STK, sp) (grant's CtrlParse.v:111-120) *)
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => spZ regs - T_parse_STK <= a < spZ regs) a) by (p0_win AG);
pose proof (pz_kept_run tfibsegs B LAWS Hsegs lyc Sc W memc mdc W mA W mB (spZ regs - T_parse_STK) (spZ regs) OC (fun _ => False)
(fun a => spZ regs - T_parse_STK <= a < spZ regs) HAR Hce Hs64 HOCc HOCi
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; left; exact Ha) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1) (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
(* sp1 := 32 * ((sp0 - 192) / 32) into env slot 70 (donor :202-226) *)
set (sp1 := 32 * ((spZ regs + -192) / 32)).
destruct (sp1_facts (spZ regs + -192) ltac:(clear - Hceil Hslo Hstk0 Hwin WS C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by (clear - Hsp1r; lia). clear Hsp1r.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(pp0_and_m32 Ev 2 (spZ regs) (-192) ltac:(evalE AG; rewrite E2; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(clear - Hceil Hslo Hstk0 Hwin WS C1; lia) ltac:(clear - Hsp0 Hshi H47; lia) ltac:(clear - Hceil Hslo Hstk0 Hwin WS C1 Hsp0 Hshi H47; lia)) R2 end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 70 Ev (havoc Ev 70 [Z_to_bv 64 sp1]) ssv msv HS
(env_agree_havoc_ge 70 70 Ev Ev _ ltac:(lia) (env_agree_refl 70 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 Hwin WS C1 Hsp0 Hshi H47; lia); reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear R2.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 Hwin WS C1 Hsp0 Hshi H47; lia); change (2 ^ 5) with 32;
clear - Hsp1 Hsp1al Hslo Hstk0 Hshi H47 Hceil Hwin WS Hsp0 C1 C3; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* the stack region keeps the saves [sp0-104, sp0); the sd zero at sp0-192 is dropped (donor :228-234) *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* region 70 = [s1+8, s1+88): the spills 8..88(s1) (donor :235-246, [16, 88)) *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 8 88 8 88 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E70, unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hstk0 Hwin WS C1 Hsp0 Hshi H47; lia); split; [clear - Hsp1 Hceil Hslo Hstk0 Hwin WS C1; lia|]; split; [clear - Hsp1 Hsp0 Hshi H47; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply HJpres; clear - Ho Hsp1 Hwin WS Hsp0; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 Hwin WS Hsp0 C1; repeat split; zone_lia)) as HS3; clear HJpres;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
(* 0x80be8-0x80c18: the GOT loads, the option word (1) decides beqz a2, a0 = 0x40, jal 0x3c8e4; stop by SR_fetch
   (donor :248-249) *)
aj_run_tok tfibtbl_lib_ok HS HJ SHOK PPBspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | evalE AG; lia | cbn; lia | cbn; lia |]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1 - sp0)); [reflexivity | evalE AG; try (rewrite unsigned_lit_small by lia); lia | cbn; lia | cbn; lia |] ]. }
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => spZ regs - T_parse_STK <= a < spZ regs) a) by (p0_win AG);
pose proof (pz_kept_run tfibsegs B LAWS Hsegs lyc Sc W memc mdc W mA W mB (spZ regs - T_parse_STK) (spZ regs) OC (fun _ => False)
(fun a => spZ regs - T_parse_STK <= a < spZ regs) HAR Hce Hs64 HOCc HOCi
ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction) ltac:(intros; contradiction)
ltac:(intros a Ha; left; exact Ha) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1) (fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
(* the class-0 call through aj_stack_malloc_atS, its premises from pin_fs0_site (donor :252-263, class 1 -> 0) *)
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (1%bv : bv 5) R1.
rewrite E70 in R2. rewrite (AG 3%nat) in R3 by lia. rewrite (AG 4%nat) in R4 by lia.
rewrite (EE 3%nat 3%bv eq_refl) in R3. rewrite (EE 4%nat 4%bv eq_refl) in R4.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
destruct (pin_fs0_site STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch _ (ms_mem msX) _ sp1 HPK0 HJ eq_refl R2 R3 R4 R1 Hcnt)
as (Hsp' & Hal' & Hneg' & Hbud' & Hgp' & Htp' & Hra' & Hcnt' & _) end.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 248036 with (pc_stack_malloc code 0) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
exact (aj_stack_malloc_atS tfibsegs B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
(sp1 - sp0) (Z_to_bv 64 0x80c1c) HJ Hsp' Hal' Hneg' Hbud' Hgp' Htp' R1 ltac:(rewrite <- R1; exact Hra') Hcnt') end. }
cbv beta. clear R2 R3 R4 R1 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJin & (fS2 & ES2)).
rewrite Hes in HK. replace (sp0 + (sp1 - sp0) - 4096) with (sp1 - 4096) in HK by (clear; lia).
replace (sp0 + (sp1 - sp0)) with sp1 in HK by (clear; lia).
(* the model's I/O so far, and the kept fact across the call (grant's CtrlParse.v:185) *)
assert (SIO2 : same_io mdc md2).
{ pose proof HJin as (_ & _ & _ & _ & Hio_in & _).
eapply same_io_trans; [| exact (aos_step_closed_same_io [] _ _ sink_closed_nil Hio_in)].
repeat (eapply same_io_trans; [| apply pp0_sio_wvb]). apply same_io_refl. }
clear HJin.
pose proof (pz_kept_trans tfibsegs B lyc Sc W memc W _ W mem2 (spZ regs - T_parse_STK) (spZ regs) (sp1 - 4096) sp1 OC (fun _ => False)
Hce Hs64 KP HK ltac:(clear - Hsp1 WS; lia) ltac:(clear - Hsp1; lia) ltac:(intros; contradiction)) as KP'.
clear KP; rename KP' into KP.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof (proj1 HJ2) as HAR2.
(* the class-0 frame (donor :273-280 at class 1) *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
(* the registers the call clobbers are fresh atoms from 71; the regions are kept (donor :281-282) *)
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac;
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ2 | evalE AG; try exact Usp | lia | lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj tfibsegs _); [exact HK | exact HJ2 | evalE AG; try (rewrite unsigned_lit_small by lia); try reflexivity | lia | lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot0 | exact Kgot2 | lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell0 | exact Kcell2 | lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar0 | exact Kguar2 | lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar0 | exact Kuar2 | lia] ]
end).
(* atom 75 = F (a0), 87 = FL, 88 = SB + F/8 (donor :283-292) *)
rreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_agree tfibsegs 87 Ev (havoc Ev 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) ssv msv HS
(env_agree_havoc_ge 87 87 Ev Ev _ ltac:(lia) (env_agree_refl 87 Ev)) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E87 : ew Ev 87 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E88 : ew Ev 88 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 87 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ => assert (E32' : ew Ev 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32) end.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
(* the facts of 75 / 87 / 88, the shadow alias, region 75 = the 64-byte frame with the flag pointer at F + 56
   (donor :298-322, 128 bytes / chunk 120) *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ 75 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 87 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E87, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_fact tfibsegs Ev _ _ 88 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E88, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias tfibsegs Ev _ _ _ _ HS (shadow_decl_ok Ev 75 32 88 F SB RF ltac:(lia) E32' E88)) as HS3;
clear HS; rename HS3 into HS;
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 87 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val tfibsegs Ev _ F 56 8 _ FL);
[cbn [sv_denot]; rewrite E87, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword tfibsegs _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 Hwin WS Hsp0 C1 C3 HF4096 HFceil HFhigh HFhigh_img; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
(* region 88 = the frame's 8 shadow bytes, zero after the call (donor :323-342, 16 bytes) *)
assert (ZS : val_mem tfibsegs (mrestrict (w_H W) mem2) (SB + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
apply Hz. change (64 / 8) with 8. lia. }
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _
(fshadow_region 88 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite E88, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; exact ZS]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite E88, RF; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 Hwin WS Hsp0 C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x80c1c-0x80ca8: bnez s3 decided by HPTR 5 on F (the probe loop 0x80c30-0x80c48 is not reached), sd s7,0x50(s1),
   the frame header, s11 = SB + F/8, the 8 shadow bytes, a3 = -1; stop at 0x80cac (donor :344-346) *)
aj_run_to_sh tfibtbl_lib_ok HS HJ2 0x80cac.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own' => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own') end.
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | evalE AG; lia | cbn; lia | cbn; lia |]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1 - sp0)); [reflexivity | evalE AG; try (rewrite unsigned_lit_small by lia); lia | cbn; lia | cbn; lia |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 75%nat F); [reflexivity | evalE AG; try (rewrite unsigned_lit_small by lia); try reflexivity
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0, fpos; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 88%nat (SB + F / 8)); [reflexivity | evalE AG; try (rewrite unsigned_lit_small by (unfold SB; lia)); try reflexivity
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 0, fpos; split; [left; reflexivity|]; right;
    unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; fold F; lia | ] ]. }
(* the run kept the caller's memory: its windows are in the stack window or the own frame (grant's CtrlParseEpi.v:96-99) *)
lazymatch type of HFr with frame_of ?Ef ?rsf (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (Hw1 : forall b wlo whi a, In (b, wlo, whi) (windows rsf) -> base_val Ef b + wlo <= a < base_val Ef b + whi ->
(fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a) a) by (p0_win AG);
pose proof (pz_kept_own B LAWS lyc lyc Sc S2 W memc mdc W mem2 md2 W mA W mB (spZ regs - T_parse_STK) (spZ regs) fpos F FL OC
(fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a) HAR HAR2 Hfrs2 ltac:(rewrite Eab; apply Permutation_refl)
eq_refl eq_refl eq_refl FFL Hce Hs64 HOCc HOCi
ltac:(intros a [Ha | Ha]; [left; exact Ha | right; right; exact Ha]) KP (kept_of_frame _ _ _ _ _ _ HFr Hw1)
(fun a _ Ha => apresent_grows _ _ _ a HG Ha)) as KP' end.
clear KP Hw1 HF HFr HG; rename KP' into KP.
rebaseE HS AG HEv. clear HEv.
(* the frame's shadow region read-only (APgRt.v:343-351 fs_roF) and the four cell regions dropped *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (ast_ok_set_region tfibsegs Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow tfibsegs Ex _ r 0 0 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (firstn 4 (ss_mem ssx)) in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
(* the facts in ss_P1's order *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ss_P1)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] pp_alias HS ltac:(incl_lit_tac) ltac:(intros x Hx; destruct Hx) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ _ ?ssx _ => change ssx with ss_P1 in HS end.
(* hand-off to the continuation at P1 (donor :367-381) *)
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdF) _ =>
assert (SIO : same_io mdc mdF) by (eapply same_io_trans; [exact SIO2 | apply pp0_sio_wvb]) end.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
change (pp_post B MT RLO RHI cat TP DP (mkPPCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos0 sp10 E00))
with (pp_post B MT RLO RHI cat TP DP (mkPPCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos sp1 E));
apply (PF (mkPPCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl fpos sp1 E) Ev lyc S2 Wg msF mdF) end end.
- split; [exact HPRE0|]. split; [reflexivity|]. split; [exact EE | exact E32].
- unfold pp_E, pp_F, pp_FL. cbn [c_E0 c_sp1 c_lyc c_fpos]. fold F FL.
split; [exact AG|]. split; [exact E70|]. split; [exact RF|]. split; [exact E87 | exact E88].
- exact HJ2.
- exact Hfrs2.
- cbn [c_lyc c_Sc]. rewrite Eab. apply Permutation_refl.
- exact (pp_mo_le_set_fs MT Sc S2 MTL MTF (ex_intro _ fS2 ES2)).
- exact SIO.
- apply wle_refl.
- exact KP.
- exact I.
- exact HS.
Qed.
End d.
End b.
