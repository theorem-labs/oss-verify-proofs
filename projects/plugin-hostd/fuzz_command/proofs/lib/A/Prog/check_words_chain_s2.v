(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_grant_build_sweep's contract, adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v (the entry state and its region_ok facts), lib/A/AChf.v (the side-stack frame: aj_stack_malloc_atS, the realigned sp, reseat, the frame and shadow regions, the shadow_decl_ok alias), lib/A/ACb8.v (the chain pushed at a call, the flag store and the return) and lib/A/ACh1.v (a callee in afn_pre form through cl_callS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proof speed only, no statement change: lia's case splits are hidden at the hot steps (rs_hide_all) and the exit paths drop the facts they do not need. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantBuildSweepWalk.v, with its module paths, module names and numbers changed; 710 of its 769 lines of code are new or changed and 594 lines of the source are left out. *)
(* The walk of check_words_chain on the ASan build of plugin-hostd/fuzz_command, stage 2: from the take of the
   side-stack frame at 0x88d14 to the loop head 0x88e74 or, when read < 3, to the tail 0x88ed4.

   The stage runs the verified symbolic executor from the state check_words_chain_s1.v left at the call of the
   class-4 side-stack entry, takes that call with cgif's stack-malloc rule, gives the frame and the frame's
   metadata bytes regions of their own, walks the frame header and the 30 inline metadata stores, takes the two
   shadow-fill calls with lib/A/Prog/PaRt.v's step, and ends at the guard `read < 3`, where it hands the walk to
   the loop stage or to the tail stage (lib/A/Prog/check_words_chain_iv.v's CWC_LOOP_stmt, CWC_TAIL_stmt), with
   the facts of cwc_mid that those stages read.

   The executor here is the PLAIN one (SRr_run_pi_AJ and friends), not the token one: this stage holds writable
   regions inside the metadata band, and the token executor's `cells_safe_b` (lib/Reusable/YCbn.v:116) asks that
   such a region be covered by an `sh_ok` entry, whose `app_apart` says the covered bytes are OUTSIDE the band.
   No instrumented check stands between 0x88d18 and 0x88e40, so the plain executor is enough. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaStep PaShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaJournal CmdPaLib PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaWalk PaArt PaRt CwcText HarnessPropsA sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_chain_c check_words_chain_s0 check_words_chain_s1 check_words_chain_iv check_words_chain_s2h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HR : CwcRec B RLO RHI.
Let TL : PALib B := cr_tl B RLO RHI HR.
Let TLF : PALibF B := cr_tlf B RLO RHI HR.
Hypothesis ML : model_laws (as_universe B).
Hypothesis BOK : asyms_ok B.
Let GREC_RA := cr_grec_ra B RLO RHI HR.
Let GREC_NOT_RT := cr_grec_not_rt B RLO RHI HR.
(* the loop and the tail stages (check_words_chain_s3.v, check_words_chain_s4.v), which this stage hands on to *)
Hypothesis LOOP : CWC_LOOP_stmt B RLO RHI.
Hypothesis TAIL : CWC_TAIL_stmt B RLO RHI.

Let RUNTO := paj_run_to B LAWS.
Let RUN := paj_run B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
Hypothesis ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (pa_sigma CS___asan_set_shadow_f8) 0xf8.
Hypothesis ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (pa_sigma CS___asan_set_shadow_00) 0.
Lemma cwc_rk : forall E (Wx : world SEGS) memc mem2 (r : YP09.region),
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
   aview SEGS (w_H Wx) mem2 a = aview SEGS (w_H Wx) memc a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
   apresent (w_H Wx) mem2 a) ->
region_kept SEGS E (mrestrict (w_H Wx) memc) (mrestrict (w_H Wx) mem2) r.
Proof.
intros E Wx memc mem2 r H1 H2. split.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (H1 a Ha).
- intros a Ha _. apply (apresent_writable SEGS). exact (H2 a Ha).
Qed.
Hypothesis ASMALLOC4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.


Ltac keptCW HK HJx Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 E2 E1024 E33 E10u sp0v sp1v :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _) with (sp := sp0v); [exact HK | exact HJx | exact E2 | lia | lia | lia | lia | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 1024%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj _ _) with (sp := sp1v);
[exact HK | exact HJx | rewrite E1024; apply unsigned_lit_small; lia | lia | lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 33%nat) _ _ _ _ _) =>
let Bv := rnB in apply (region_kept_val_at Ex _ _ 33%nat (as_uar_cell Bv) 4 1);
[rewrite E33; apply unsigned_lit_small; lia | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E10u; intros a Ha;
[ apply (mbyte_of_aview SEGS); eapply (cwc_grec_call_kept _ GREC_NOT_RT); [exact HK | unfold CALL_SIZE, CALL_OFF_NARGS, A_G_REC, OFF_CALLS, REC_SIZE in *; lia]
| lia ]
| |- ?g => idtac "KEPTCW-FAIL" g; fail
end.

Ltac awrCW E1101x RFx E1024x E2x sp1x spx fposx Fx :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' a1 a2 a3 a4 a5 a6 a7 a8) end;
repeat first
[ lazymatch goal with |- awr_ok _ _ _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ _ =>
  lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply (YCbq.awr_ok_cons_ro SEGS B); [cbn; lia|] end end
| lazymatch goal with |- awr_ok _ _ _ (YP09.mkRegion (Some 1101%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
  eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 1101%nat) (b := SB + Fx / 8);
  [reflexivity | rewrite E1101x; apply unsigned_lit_small; unfold SB; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 4, fposx;
    split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
    change (fs_frame_bytes 4 / 8) with 128; fold Fx; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia
  |] end
| lazymatch goal with |- awr_ok _ _ _ (YP09.mkRegion (Some 1029%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
  eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 1029%nat) (b := Fx);
  [reflexivity | rewrite RFx; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 4, fposx;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    change (fs_frame_bytes 4) with 1024; fold Fx; lia
  |] end
| lazymatch goal with |- awr_ok _ _ _ (YP09.mkRegion (Some 1024%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
  eapply (YCbq.awr_ok_cons_stack_off SEGS B _) with (n := 1024%nat) (d := sp1x - spx);
  [reflexivity | rewrite E1024x, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |] end
| lazymatch goal with |- awr_ok _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ _ =>
  eapply (YCbq.awr_ok_cons_stack SEGS B _) with (n := 2%nat);
  [reflexivity | exact E2x | cbn; lia | cbn; lia |] end ];
apply (YCbq.awr_ok_nil SEGS B).

(* region_kept for the regions this stage holds, across a call that writes only [q, q + n) and the stack
   window: the bytes come from the call's "kept" clause, the writability from the frame's own presence
   (the allocator record's frames law) and the journal's stack presence. *)
Ltac cwc_unf := repeat first [ progress unfold A_G_REC in * | progress unfold OFF_CALLS in *
| progress unfold REC_SIZE in * | progress unfold CALL_SIZE in * | progress unfold CALL_OFF_NARGS in *
| progress unfold SB in * | progress unfold CHECK_WORDS_CHAIN_STK in * | progress unfold ESTACK in * ].

Ltac keptFILL Hkeepx HFpresx HFSpresx HJpresx E1101x RFx E1024x E2x Fx E33x E10x E241x E242x E253x :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 1101%nat) _ _ _ _ _) =>
  first [ apply cwc_rk;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
    rewrite E1101x, unsigned_lit_small in Ha by (unfold SB; lia);
    apply Hkeepx; unfold SB in *; lia
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite E1101x, unsigned_lit_small in Ha by (unfold SB; lia);
    replace a with (shadow_addr Fx + (a - (SB + Fx / 8)))
      by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpresx (a - (SB + Fx / 8)) ltac:(try change (fs_frame_bytes 4 / 8) with 128; lia))) ]
  | idtac "KF-1101"; fail ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 1029%nat) _ _ _ _ _) =>
  first [ apply cwc_rk;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
    rewrite RFx, unsigned_lit_small in Ha by lia; apply Hkeepx; unfold SB in *; lia
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite RFx, unsigned_lit_small in Ha by lia;
    apply (proj1 (HFpresx a ltac:(try change (fs_frame_bytes 4) with 1024; lia))) ]
  | idtac "KF-1029"; fail ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 1024%nat) _ _ _ _ _) =>
  first [ apply cwc_rk;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
    rewrite E1024x, unsigned_lit_small in Ha by lia; apply Hkeepx; unfold SB in *; lia
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite E1024x, unsigned_lit_small in Ha by lia; apply HJpresx; lia ]
  | idtac "KF-1024"; fail ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  first [ apply cwc_rk;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite E2x in Ha;
    apply Hkeepx; unfold SB in *; lia
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite E2x in Ha;
    apply HJpresx; lia ]
  | idtac "KF-2"; fail ]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some ?n) _ _ ?wlo ?whi _) =>
  first [ apply cwc_rk;
  [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
    rewrite ?E241x, ?E242x, ?E253x, ?E33x, ?E10x in Ha;
    apply Hkeepx; [ first [cwc_unf; lia | pose proof (pa_val_range n); cwc_unf; lia] | cwc_unf; lia ]
  | intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia ]
  | lazymatch goal with |- ?g => idtac "KF-OTHER" n g end; fail ]
| |- ?g => idtac "KEPTFILL-FAIL" g; fail
end.

(* one spill slot, one frame word, one metadata byte, read back from a region of the final state *)
Ltac fld8 RG EB :=
change 8%nat with (N.to_nat 8);
eapply field_of_region; [exact RG | exact EB | cbn [In]; repeat (first [left; reflexivity | right]) | | | cbn; lia].
Ltac fld1 RG EB :=
change 1%nat with (N.to_nat 1);
eapply field_of_region; [exact RG | exact EB | cbn [In]; repeat (first [left; reflexivity | right]) | | | cbn; lia].

Lemma cwc_s2_ok : forall ly S W regs mem md ch (cp wp r nargs p1 p2 : Z) pw ws x1 x2
(E0 : env) (ms0 : machine_state) (mdq : Model) (sp1 : Z),
cwc_pre B RLO RHI ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 ->
img_env VAL A_LIM E0 ->
st_ok_pi SEGS VAL E0 ss_cwc_sm (restrict (w_H W) ms0) ->
sh_ok SEGS CWC_Bx cwc_SH E0 (mrestrict (w_H W) (ms_mem ms0)) ->
ajournal SEGS B CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms0) mdq 0 ->
(forall n, (n < 33)%nat -> ew E0 n = ew (Eimg (Ereg regs (cwc_extra B p1 p2))) n) ->
ew E0 1024 = Z_to_bv 64 sp1 -> ew E0 33 = Z_to_bv 64 (as_uar_cell B) ->
sp1 = 32 * ((spZ regs + -192) / 32) -> sp1 mod 32 = 0 -> spZ regs - 208 <= sp1 <= spZ regs - 192 ->
(* rounding mode 0 at the entry (the statement's pre), which the loop and the tail take *)
frm0 fx ->
SRr SEGS W (mkCfg ms0 mdq) (cwc_post B ly S W regs mem md).
Proof.
intros ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 E0 ms0 mdq sp1
HPRE HEI HS SHOK HJ AGo E1024 E33 Hsp1e Hsp1al Hsp1 HRM0.
pose proof HPRE as (HFN & PRrod & H10 & PR11 & PR12 & PRr64 & PRro & PRobj & PRguard & PRflag & PRerrno
 & Hlo & Hhi & PRna & PRna6 & PRa1 & PRa2 & PRws & PRn3 & PRx1 & PRx2 & Hroom & PRev).
pose proof HFN as (HAR0 & PRra & PRra4 & Hgp & Htp & Hstk & PRpres & PRch & PRqt).
set (Q := cwc_post B ly S W regs mem md) in *.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : CHECK_WORDS_CHAIN_STK = 12496) by reflexivity.
assert (EI2 : bv_unsigned (ew (Eimg (Ereg regs (cwc_extra B p1 p2))) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E2 : bv_unsigned (ew E0 2) = spZ regs) by (rewrite (AGo 2%nat) by lia; exact EI2).
assert (EI10 : bv_unsigned (ew (Eimg (Ereg regs (cwc_extra B p1 p2))) 10) = cp)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10;
apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia).
unfold ss_cwc_sm in HS.
paj_run_tok RUN HS HJ SHOK CWC_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex _ _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off SEGS B Ex) with (d := sp1 - spZ regs);
[reflexivity | rewrite E1024, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |];
eapply (awr_ok_cons_stack SEGS B Ex); [reflexivity | exact E2 | cbn; lia | cbn; lia |] end;
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
set (mdv1 := mdx) in *; clearbody mdv1 end.
pmkst HS.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
change (pa_sigma CS___asan_stack_malloc_4) with (pa_sigma (cs_stack_malloc 4)).
rewrite (palf_sm B TLF 4 ltac:(cbn; tauto)).
assert (E3 : ew E0 3 = getr regs 3)
by (rewrite (AGo 3%nat) by lia; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E0 4 = getr regs 4)
by (rewrite (AGo 4%nat) by lia; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 4 (ASMALLOC4 fx) ltac:(lia)
W (ms_regs msX) (ms_mem msX) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
- unfold spZ at 1. rewrite R2, E1024, unsigned_lit_small by lia. lia.
- rewrite <- Zminus_mod_idemp_l.
replace (sp1 mod 16) with 0 by (rewrite Hsp1e; replace (32 * ((spZ regs + -192) / 32)) with (((spZ regs + -192) / 32) * 2 * 16) by lia;
rewrite Z_mod_mult; reflexivity).
rewrite Zminus_mod, Hsp0al. reflexivity.
- lia.
- assert (ESTACK = 4096) by reflexivity. lia.
- rewrite R3, E3. exact Hgp.
- rewrite R4, E4. exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- exact Hroom. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
(* the take is a set_fs of the entry state; the rest of the walk keeps S2 (cwc_frm) *)
assert (FRMp : cwc_frm S S2) by (exists fS2; exact ES2).
assert (E10u : bv_unsigned (ew E0 10) = cp).
{ rewrite (AGo 10%nat) by lia. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
apply unsigned_lit_small. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia. }
pose proof (palf_uar_img B TLF) as Huar.
pose proof (pa_obj_img 0 ltac:(lia)) as Img0. pose proof (pa_obj_img 1 ltac:(lia)) as Img1.
pose proof (pa_obj_img 12 ltac:(lia)) as Img12.
assert (HES : ESTACK = 4096) by reflexivity.
aconstsF HJ Kgot0 Kcell0 Kguar0 Kuar0.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
reseat_pi HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AGo
ltac:(idtac; keptCW HK HJ2 Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 E2 E1024 E33 E10u (spZ regs) sp1).
assert (E2n : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AGo 2%nat) by lia; exact EI2).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
set (F := frame_addr ly 4 fpos) in *. set (FL := flag_addr ly 4 fpos) in *.
assert (Hfin2 : In (4, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 4) with 1024 in *.
fold F in HFal, HFhi, HFpres, HFSpres, HF4096, HFceil, HFhigh, HFhigh_img.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32))
by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
(* the frame is 32-aligned, so F and F / 8 are both linear in q = F / 32, which is what the disjointness of
   the frame from its own shadow needs *)
remember (F / 32) as q eqn:Hq32. clear Hq32.
destruct (FFL ly S2 W mem2 md2 4 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1100 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS
ltac:(vm_compute; reflexivity)) as HS3; hei_pose Ev 1100%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. rebaseE HS AGo HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E1100 : ew Ev 1100 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 1100 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E1101 : ew Ev 1101 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 1100 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E2n2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AGo 2%nat) by lia; exact EI2);
assert (E10n : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat) by lia; exact EI10);
assert (E33n : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E32v : ew Ev 32 = Z_to_bv 64 SB)
by (rewrite (AGo 32%nat) by lia; rewrite Eimg_low by (unfold A_TEXT; lia);
exact (ew_Ereg_extra regs (cwc_extra B p1 p2) 0)) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 1029 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1100 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E1100, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1101 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1101, unsigned_lit_small by (unfold SB; lia);
change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * q) with ((536862720 + q) * 4) by lia;
apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1029 32 1101 F SB RF ltac:(lia) E32v E1101)) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS end.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1029%nat) 0 1024 0 1024 [YP09.mkChunk 1016 (CVal 8 (SOff 1100 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[| apply Forall_cons; [|apply Forall_nil];
   apply (chunk_ok_val SEGS Ev _ F 1016 8 (SOff 1100 0) FL);
   [ cbn [sv_denot]; rewrite E1100, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
   | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
   | replace (F + 1016) with (F + 1024 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF, E1024, E2n2, E33n, E10n, unsigned_lit_small by lia;
lazymatch goal with HEIx : img_env VAL A_LIM Ev |- _ =>
rewrite (HEIx 241%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 242%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end;
cbn [A_OBJ Nat.add] in Img0, Img1, Img12;
rewrite unsigned_lit_small by lia;
unfold off_img in HFhigh_img; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *;
destruct HFhigh_img as [Himg|Himg]; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1101%nat) 0 4 0 4 []) HS eq_refl
ltac:(unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E1101, unsigned_lit_small by (unfold SB; lia);
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
apply (proj1 (HFSpres o ltac:(change (1024 / 8) with 128; lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E1101, RF, E1024, E2n2, E33n, E10n, !unsigned_lit_small by (unfold SB; lia);
rewrite HF8;
lazymatch goal with HEIx : img_env VAL A_LIM Ev |- _ =>
rewrite (HEIx 241%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 242%nat ltac:(unfold A_TEXT, A_LIM; lia)),
(HEIx 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end;
cbn [A_OBJ Nat.add] in Img0, Img1, Img12;
unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, SB in *;
unfold off_img in HFhigh_img; destruct HFhigh_img as [Himg|Himg];
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS end.
paj_run_to_sh RUNTOP HS HJ2 CWC_FILL_F8.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' a1 a2 a3 a4 a5 a6 a7 a8) end;
eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 1101%nat) (b := SB + F / 8);
[reflexivity | rewrite E1101; apply unsigned_lit_small; unfold SB; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 4, fpos;
  split; [left; reflexivity|]; right; unfold in_zr, shadow_addr; cbn [fst snd];
  change (fs_frame_bytes 4 / 8) with 128; fold F; rewrite <- SB_SHADOW_OFF; unfold SB in *; lia
|];
eapply (YCbq.awr_ok_cons_gen SEGS B _) with (k := 1029%nat) (b := F);
[reflexivity | rewrite RF; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 4, fpos;
  split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
  change (fs_frame_bytes 4) with 1024; fold F; lia
|];
eapply (YCbq.awr_ok_cons_stack_off SEGS B _) with (n := 1024%nat) (d := sp1 - spZ regs);
[reflexivity | rewrite E1024, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |];
eapply (YCbq.awr_ok_cons_stack SEGS B _) with (n := 2%nat);
[reflexivity | exact E2n2 | cbn; lia | cbn; lia |];
repeat (apply (YCbq.awr_ok_cons_ro SEGS B); [cbn; lia|]); apply (YCbq.awr_ok_nil SEGS B). }
clear HF HFr HG.
(* --- the first shadow fill: the 97 bytes from the frame's metadata byte 4 := 0xf8 --- *)
paj_run_shc RUNP RUNC HS HJ2.
{ awrCW E1101 RF E1024 E2n2 sp1 (spZ regs) fpos F. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qgp : getr (ms_regs ms2) 3 = w64 (as_gp B)).
{ rewrite Q3. rewrite (AGo 3%nat ltac:(lia)). rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact Hgp. }
assert (Qtp : getr (ms_regs ms2) 4 = w64 (as_tp B)).
{ rewrite Q4. rewrite (AGo 4%nat ltac:(lia)). rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact Htp. }
assert (Qsp : spZ (ms_regs ms2) = spZ regs + (sp1 - spZ regs))
by (unfold spZ; rewrite Q2, E1024, unsigned_lit_small by lia; lia).
assert (Qal : (sp1 - spZ regs) mod 16 = 0).
{ rewrite <- Zminus_mod_idemp_l.
replace (sp1 mod 16) with 0 by (rewrite Hsp1e; replace (32 * ((spZ regs + -192) / 32)) with (((spZ regs + -192) / 32) * 2 * 16) by lia;
rewrite Z_mod_mult; reflexivity).
rewrite Zminus_mod, Hsp0al. reflexivity. }
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ eapply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (pa_sigma CS___asan_set_shadow_f8) 0xf8 (ASETF8 fx)
W (ms_regs ms2) (ms_mem ms2) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(4%Z, fpos)] ly S2 mdv2 0
4 fpos (SB + F / 8 + 4) 97 (sp1 - spZ regs) _ HJ2).
- left; reflexivity.
- rewrite Q10, E1101; cbn [sv_denot]; rewrite unsigned_lit_small by (unfold SB; lia); unfold w64; f_equal; lia.
- rewrite Q11. reflexivity.
- lia.
- unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; unfold SB in *; lia.
- unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 4 / 8) with 128; fold F; unfold SB in *; lia.
- exact Qsp.
- exact Qal.
- lia.
- lia.
- exact Qgp.
- exact Qtp.
- reflexivity.
- rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfill1 & Hkeep1 & Hwin1 & Hsame1).
rewrite Q1.
pose proof (proj1 HJ3) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR3 Hfin2) as (_ & _ & HFpres3 & HFSpres3).
fold F in HFpres3, HFSpres3. change (fs_frame_bytes 4) with 1024 in HFpres3.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
cbn [A_OBJ Nat.add] in Img0, Img1, Img12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E241v : bv_unsigned (ew Ev 241) = VAL 241%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E242v : bv_unsigned (ew Ev 242) = VAL 242%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 242%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E253v : bv_unsigned (ew Ev 253) = VAL 253%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E33v : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia);
assert (E10v : bv_unsigned (ew Ev 10) = cp)
by (rewrite (AGo 10%nat ltac:(lia)); exact EI10) | st_ok _ ?Ev _ _ =>
assert (E241v : bv_unsigned (ew Ev 241) = VAL 241%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E242v : bv_unsigned (ew Ev 242) = VAL 242%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 242%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E253v : bv_unsigned (ew Ev 253) = VAL 253%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E33v : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia);
assert (E10v : bv_unsigned (ew Ev 10) = cp)
by (rewrite (AGo 10%nat ltac:(lia)); exact EI10) end.
assert (HdFS : F + 1024 <= SB + F / 8 \/ SB + F / 8 + 128 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh. unfold SB. rewrite HF8.
clear - HFhigh HFq HF4096 HFceil C1. lia. }
reseat_pi HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AGo
ltac:(idtac; keptFILL Hkeep1 HFpres3 HFSpres3 HJ3pres E1101 RF E1024 E2n2 F E33v E10v E241v E242v E253v).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E2b : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AGo 2%nat ltac:(lia)); exact EI2);
assert (E10b : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat ltac:(lia)); exact EI10);
assert (E33b : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia);
assert (E241b : bv_unsigned (ew Ev 241) = VAL 241%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E242b : bv_unsigned (ew Ev 242) = VAL 242%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 242%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E253b : bv_unsigned (ew Ev 253) = VAL 253%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]) end.
(* the metadata bytes [100, 128) of the frame: the inline stores of the guard bytes write [101, 124), the
   byte 100 and the two bytes 118, 119 come after the second fill *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 1101%nat) 100 128 100 124 []) HS eq_refl
ltac:(unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E1101, unsigned_lit_small by (unfold SB; lia);
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres3 o ltac:(change (fs_frame_bytes 4 / 8) with 128; lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E1101, RF, E1024, E2b, E33b, E10b, E241b, E242b, E253b, !unsigned_lit_small by (unfold SB; lia);
rewrite HF8;
cwc_unf; unfold off_img in HFhigh_img; destruct HFhigh_img as [Himg|Himg];
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss_pi HS end.
(* --- the guard bytes and the second shadow fill --- *)
paj_run_to_sh RUNTOP HS HJ3 CWC_FILL_00.
{ awrCW E1101 RF E1024 E2b sp1 (spZ regs) fpos F. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
paj_run_shc RUNP RUNC HS HJ3.
{ awrCW E1101 RF E1024 E2b sp1 (spZ regs) fpos F. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv4 := mdx) in *; clearbody mdv4 end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1b. prreg HS (2%bv : bv 5) Q2b. prreg HS (3%bv : bv 5) Q3b. prreg HS (4%bv : bv 5) Q4b.
prreg HS (10%bv : bv 5) Q10b. prreg HS (11%bv : bv 5) Q11b.
assert (Qgpb : getr (ms_regs ms4) 3 = w64 (as_gp B)).
{ rewrite Q3b. rewrite (AGo 3%nat ltac:(lia)). rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact Hgp. }
assert (Qtpb : getr (ms_regs ms4) 4 = w64 (as_tp B)).
{ rewrite Q4b. rewrite (AGo 4%nat ltac:(lia)). rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact Htp. }
assert (Qspb : spZ (ms_regs ms4) = spZ regs + (sp1 - spZ regs))
by (unfold spZ; rewrite Q2b, E1024, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (pa_sigma CS___asan_set_shadow_00) 0 (ASET00 fx)
W (ms_regs ms4) (ms_mem ms4) CHECK_WORDS_CHAIN_STK (spZ regs) [] ly S W mem md [(4%Z, fpos)] ly S2 mdv4 0
4 fpos (SB + F / 8 + 4) 96 (sp1 - spZ regs) _ HJ3).
- left; reflexivity.
- rewrite Q10b, E1101; cbn [sv_denot]; rewrite unsigned_lit_small by (unfold SB; lia); unfold w64; f_equal; lia.
- rewrite Q11b. reflexivity.
- lia.
- unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; unfold SB in *; lia.
- unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 4 / 8) with 128; fold F; unfold SB in *; lia.
- exact Qspb.
- exact Qal.
- lia.
- lia.
- exact Qgpb.
- exact Qtpb.
- reflexivity.
- rewrite Q1b; apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfill2 & Hkeep2 & Hwin2 & Hsame2).
rewrite Q1b.
pose proof (proj1 HJ4) as HAR4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR4 Hfin2) as (_ & _ & HFpres4 & HFSpres4).
fold F in HFpres4, HFSpres4. change (fs_frame_bytes 4) with 1024 in HFpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E10c : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat ltac:(lia)); exact EI10);
assert (E33c : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia);
assert (E241c : bv_unsigned (ew Ev 241) = VAL 241%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E242c : bv_unsigned (ew Ev 242) = VAL 242%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 242%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E253c : bv_unsigned (ew Ev 253) = VAL 253%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range])
| st_ok _ ?Ev _ _ =>
assert (E10c : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat ltac:(lia)); exact EI10);
assert (E33c : bv_unsigned (ew Ev 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia);
assert (E241c : bv_unsigned (ew Ev 241) = VAL 241%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 241%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E242c : bv_unsigned (ew Ev 242) = VAL 242%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 242%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]);
assert (E253c : bv_unsigned (ew Ev 253) = VAL 253%nat)
by (lazymatch goal with Himg : img_env _ _ Ev |- _ =>
rewrite (Himg 253%nat ltac:(unfold A_TEXT, A_LIM; lia)) end; first [reflexivity | apply unsigned_lit_small; apply pa_val_range]) end.
reseat_pi HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AGo
ltac:(idtac; keptFILL Hkeep2 HFpres4 HFSpres4 HJ4pres E1101 RF E1024 E2b F E33c E10c E241c E242c E253c).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E2d : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AGo 2%nat ltac:(lia)); exact EI2) end.
(* --- the byte 100, the bytes 118 and 119, the spill of the frame and list[0] := 0, to the guard read < 3 --- *)
paj_run_to_sh RUNTOP HS HJ4 CWC_GUARD.
{ awrCW E1101 RF E1024 E2d sp1 (spZ regs) fpos F. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv5 := mdx) in *; clearbody mdv5 end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => SB + F / 8 <= a < SB + F / 8 + 4 \/ SB + F / 8 + 100 <= a < SB + F / 8 + 124
  \/ F <= a < F + 1024 \/ spZ regs - CHECK_WORDS_CHAIN_STK <= a < spZ regs) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?E1101, ?RF, ?E1024, ?unsigned_lit_small in Hrr by (unfold SB; lia); rewrite ?E2d in Hrr;
      cwc_unf; lia |]); destruct Hin)) as KG.
cbn [ms_mem mkst] in KG.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* read < 3: the loop is skipped *)
  paj_run_to_sh RUNTOP HS HJ4 CWC_TAIL.
  { awrCW E1101 RF E1024 E2d sp1 (spZ regs) fpos F. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv6 := mdx) in *; clearbody mdv6 end.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => SB + F / 8 <= a < SB + F / 8 + 4 \/ SB + F / 8 + 100 <= a < SB + F / 8 + 124
    \/ F <= a < F + 1024 \/ spZ regs - CHECK_WORDS_CHAIN_STK <= a < spZ regs) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
        rewrite ?E1101, ?RF, ?E1024, ?unsigned_lit_small in Hrr by (unfold SB; lia); rewrite ?E2d in Hrr;
        cwc_unf; lia |]); destruct Hin)) as KA.
  clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  assert (Eu2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AGo 2%nat ltac:(lia)); exact EI2);
  assert (Eu10 : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat ltac:(lia)); exact EI10);
  assert (Eu12 : bv_unsigned (ew Ev 12) = r)
  by (rewrite (AGo 12%nat ltac:(lia)), Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), PR12;
      apply unsigned_lit_small; lia);
  assert (Eu32 : bv_unsigned (ew Ev 32) = SB)
  by (rewrite (AGo 32%nat ltac:(lia)), Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_extra regs (cwc_extra B p1 p2) 0 : ew _ 32 = _); cbn [nth cwc_extra map]; apply unsigned_lit_small; unfold SB; lia);
  assert (Eu1024 : bv_unsigned (ew Ev 1024) = sp1) by (rewrite E1024; apply unsigned_lit_small; lia);
  assert (Eu1029 : bv_unsigned (ew Ev 1029) = F) by (rewrite RF; apply unsigned_lit_small; lia);
  assert (Eu1101 : bv_unsigned (ew Ev 1101) = SB + F / 8) by (rewrite E1101; apply unsigned_lit_small; unfold SB; lia);
  assert (EEn : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew Ev n = getr regs rr)
  by (intros n rr Hn Hrr; rewrite (AGo n ltac:(lia)), Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr);
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 0 _ HS eq_refl) as RSc;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 2 _ HS eq_refl) as RFr;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 3 _ HS eq_refl) as RSp;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 4 _ HS eq_refl) as RR2;
  cbn [ms_mem restrict mkst] in RSc, RFr, RSp, RR2;
  prreg HS (2%bv : bv 5) T2; prreg HS (3%bv : bv 5) T3; prreg HS (4%bv : bv 5) T4;
  prreg HS (8%bv : bv 5) T8; prreg HS (9%bv : bv 5) T9; prreg HS (20%bv : bv 5) T20 end.
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ev (SOff 12 0)) _ = true =>
    cbn [sv_denot] in Hc; rewrite Eu12, Z.add_0_r, (cwc_blt_small r 3 ltac:(lia) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc.
  pose proof (proj1 HJ4) as HARF.
  destruct (PRa1 PRn3) as [_ HA1]. destruct (PRa2 PRn3) as [_ HA2].
  assert (HdFSa : F + 1024 <= SB + F / 8 \/ SB + F / 8 + 128 <= F) by exact HdFS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem ?msF) _; cfg_model := ?mdF |} _ =>
  eapply (TAIL ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 (ms_mem msF) mdF fpos sp1 (ms_regs msF));
  [ exact HPRE | | exact FRMp | exact HRM0 | | | | | | | | | ] end.
  + (* cwc_mid *)
    split; [exact HJ4|]. split; [exact Eab|]. split; [rewrite Hsp1e; f_equal; f_equal; lia|].
    split; [eapply cwc_frame_of_region2; [exact RR2 | unfold cwc_ch2; apply incl_refl | exact Eu2 | exact EEn]|].
    unfold CWC_CID. fold F FL. unfold cwc_spill.
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split].
    * replace sp1 with (sp1 + 0) at 1 by lia. fld8 RSp Eu1024;
      [cbn [sv_denot]; rewrite Eu1101; rewrite <- SB_SHADOW_OFF; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite <- SB_SHADOW_OFF; unfold SB in *; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu10; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); cwc_unf; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu32; rewrite <- SB_SHADOW_OFF; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite <- SB_SHADOW_OFF; unfold SB; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; unfold OFF_LIST; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFF_LIST; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu12; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * apply rdword_of_val_mem; [| destruct HFLrng as (_ & H1 & _ & H2); lia].
      fld8 RFr Eu1029; [cbn [sv_denot]; rewrite E1100, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct HFLrng as (_ & H1 & _ & H2); lia].
    * unfold cwc_fshadow. rewrite <- SB_SHADOW_OFF.
      split; [|split; [|split]].
      -- intros i Hi.
         rewrite (KA (SB + F / 8 + i)) by (cwc_unf; lia). rewrite (KG (SB + F / 8 + i)) by (cwc_unf; lia).
         replace (SB + F / 8 + i) with (SB + F / 8 + 4 + (i - 4)) by lia. apply Hfill2. lia.
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
  + rewrite T2, E1024. reflexivity.
  + rewrite T3, (EEn 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  + rewrite T4, (EEn 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  + rewrite T8, (EEn 2%nat 2%bv ltac:(lia) eq_refl). unfold w64, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite T9, E1024. reflexivity.
  + rewrite T20, E1101. unfold w64, CWC_CID. rewrite <- SB_SHADOW_OFF. fold F. reflexivity.
  + assert (Hcl : pf_bytes (chain_list_at atoi_a r ws ++ [0]) = [Z_to_bv 8 0])
    by (unfold chain_list_at; replace (Z.to_nat (r - 2)) with 0%nat by lia; reflexivity).
    rewrite Hcl. intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [nth]. unfold CWC_CID. fold F. unfold OFF_LIST. rewrite Z.add_0_r.
    replace (bv_unsigned (Z_to_bv 8 0)) with 0 by (vm_compute; reflexivity).
    apply aview_of_val_mem1; [| lia].
    fld1 RFr Eu1029; [cbn [sv_denot]; reflexivity | cbn; lia].
  + eapply (cwc_strk_of_sblk B RLO RHI HR LAWS); [exact HARF|].
    eapply (cwc_sblk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HA1].
  + eapply (cwc_strk_of_sblk B RLO RHI HR LAWS); [exact HARF|].
    eapply (cwc_sblk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HA2].
- (* read >= 3: the loop's set-up, to the loop head *)
  paj_run_to_sh RUNTOP HS HJ4 CWC_LOOP.
  { awrCW E1101 RF E1024 E2d sp1 (spZ regs) fpos F. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv6 := mdx) in *; clearbody mdv6 end.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => SB + F / 8 <= a < SB + F / 8 + 4 \/ SB + F / 8 + 100 <= a < SB + F / 8 + 124
    \/ F <= a < F + 1024 \/ spZ regs - CHECK_WORDS_CHAIN_STK <= a < spZ regs) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
        rewrite ?E1101, ?RF, ?E1024, ?unsigned_lit_small in Hrr by (unfold SB; lia); rewrite ?E2d in Hrr;
        cwc_unf; lia |]); destruct Hin)) as KA.
  clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  assert (Eu2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AGo 2%nat ltac:(lia)); exact EI2);
  assert (Eu10 : bv_unsigned (ew Ev 10) = cp) by (rewrite (AGo 10%nat ltac:(lia)); exact EI10);
  assert (Eu12 : bv_unsigned (ew Ev 12) = r)
  by (rewrite (AGo 12%nat ltac:(lia)), Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), PR12;
      apply unsigned_lit_small; lia);
  assert (Eu32 : bv_unsigned (ew Ev 32) = SB)
  by (rewrite (AGo 32%nat ltac:(lia)), Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_extra regs (cwc_extra B p1 p2) 0 : ew _ 32 = _); cbn [nth cwc_extra map]; apply unsigned_lit_small; unfold SB; lia);
  assert (Eu1024 : bv_unsigned (ew Ev 1024) = sp1) by (rewrite E1024; apply unsigned_lit_small; lia);
  assert (Eu1029 : bv_unsigned (ew Ev 1029) = F) by (rewrite RF; apply unsigned_lit_small; lia);
  assert (Eu1101 : bv_unsigned (ew Ev 1101) = SB + F / 8) by (rewrite E1101; apply unsigned_lit_small; unfold SB; lia);
  assert (EEn : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew Ev n = getr regs rr)
  by (intros n rr Hn Hrr; rewrite (AGo n ltac:(lia)), Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr);
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 0 _ HS eq_refl) as RSc;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 2 _ HS eq_refl) as RFr;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 3 _ HS eq_refl) as RSp;
  pose proof (st_ok_pi_region_nth Ev ssx (restrict _ msx) 4 _ HS eq_refl) as RR2;
  cbn [ms_mem restrict mkst] in RSc, RFr, RSp, RR2;
  prreg HS (2%bv : bv 5) T2; prreg HS (3%bv : bv 5) T3; prreg HS (4%bv : bv 5) T4;
  prreg HS (8%bv : bv 5) T8; prreg HS (9%bv : bv 5) T9; prreg HS (20%bv : bv 5) T20;
  prreg HS (18%bv : bv 5) T18; prreg HS (22%bv : bv 5) T22; prreg HS (23%bv : bv 5) T23;
  prreg HS (24%bv : bv 5) T24; prreg HS (26%bv : bv 5) T26 end.
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ev (SOff 12 0)) _ = false =>
    cbn [sv_denot] in Hc; rewrite Eu12, Z.add_0_r, (cwc_blt_small r 3 ltac:(lia) ltac:(lia)) in Hc end.
  apply Z.ltb_ge in Hc.
  assert (Hwp : 0 <= wp /\ wp + 24 <= alloc_ceiling).
  { destruct (PRws 2 ltac:(lia)) as ((qb & kb & Hinb & Hqb1 & Hqb2) & _ & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR0 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & Hbnd & Hbk).
    pose proof (req_size_pos kb ltac:(lia)) as [Hbr1 Hbr2]. lia. }
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (Eu11 : bv_unsigned (ew Ev 11) = wp)
    by (rewrite (EEn 11%nat 11%bv ltac:(lia) eq_refl), PR11; apply unsigned_lit_small; lia) end.
  pose proof (proj1 HJ4) as HARF.
  destruct (PRa1 PRn3) as [_ HA1]. destruct (PRa2 PRn3) as [_ HA2].
  assert (HdFSa : F + 1024 <= SB + F / 8 \/ SB + F / 8 + 128 <= F) by exact HdFS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst (ms_regs ?msF) _ (ms_mem ?msF) _; cfg_model := ?mdF |} _ =>
  eapply (LOOP (Z.to_nat (r - 2)) ly S W regs mem md ch cp wp r nargs p1 p2 pw ws x1 x2 S2 (ms_mem msF) mdF fpos sp1 (ms_regs msF) 2);
  [ exact HPRE | | exact FRMp | exact HRM0 | lia | lia | | | | | | | | | | | | | | | | ] end.
  + (* cwc_mid *)
    split; [exact HJ4|]. split; [exact Eab|]. split; [rewrite Hsp1e; f_equal; f_equal; lia|].
    split; [eapply cwc_frame_of_region2; [exact RR2 | unfold cwc_ch2; apply incl_refl | exact Eu2 | exact EEn]|].
    unfold CWC_CID. fold F FL. unfold cwc_spill.
    split; [split; [|split; [|split; [|split; [|split; [|split]]]]] | split].
    * replace sp1 with (sp1 + 0) at 1 by lia. fld8 RSp Eu1024;
      [cbn [sv_denot]; rewrite Eu1101; rewrite <- SB_SHADOW_OFF; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite <- SB_SHADOW_OFF; unfold SB in *; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu10; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); cwc_unf; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu32; rewrite <- SB_SHADOW_OFF; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite <- SB_SHADOW_OFF; unfold SB; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu1029; unfold OFF_LIST; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold OFF_LIST; lia].
    * fld8 RSp Eu1024; [cbn [sv_denot]; rewrite Eu12; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia].
    * apply rdword_of_val_mem; [| destruct HFLrng as (_ & H1 & _ & H2); lia].
      fld8 RFr Eu1029; [cbn [sv_denot]; rewrite E1100, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); destruct HFLrng as (_ & H1 & _ & H2); lia].
    * unfold cwc_fshadow. rewrite <- SB_SHADOW_OFF.
      split; [|split; [|split]].
      -- intros i Hi.
         rewrite (KA (SB + F / 8 + i)) by (cwc_unf; lia). rewrite (KG (SB + F / 8 + i)) by (cwc_unf; lia).
         replace (SB + F / 8 + i) with (SB + F / 8 + 4 + (i - 4)) by lia. apply Hfill2. lia.
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
      -- apply aview_of_val_mem1; [| lia].
         fld1 RSc Eu1101; [reflexivity | cbn; lia].
  + rewrite T2, E1024. reflexivity.
  + rewrite T3, (EEn 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  + rewrite T4, (EEn 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  + rewrite T8, (EEn 2%nat 2%bv ltac:(lia) eq_refl). unfold w64, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite T9, E1024. reflexivity.
  + rewrite T18.
    lazymatch goal with |- ew ?E 276 = _ =>
      lazymatch goal with Hie : img_env _ _ E |- _ =>
        assert (Ha : bv_unsigned (ew E 276) = A_FMT_SPD)
        by (rewrite (Hie 276%nat ltac:(unfold A_TEXT, A_LIM; lia));
            change (VAL 276%nat) with (VAL (A_OBJ 35));
            rewrite (PRobj 35%nat ltac:(change (length cmd_objs) with 116%nat; lia)); reflexivity) end end.
    rewrite <- Ha. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + rewrite T20, E1101. unfold w64, CWC_CID. rewrite <- SB_SHADOW_OFF. fold F. reflexivity.
  + rewrite T22. reflexivity.
  + rewrite T23. apply cwc_shadow_w16; [rewrite Eu32; exact SB_SHADOW_OFF | exact Eu11 | lia | lia].
  + rewrite T24. apply cwc_word16. exact Eu11.
  + rewrite T26. reflexivity.
  + fld8 RSp Eu1024;
    [ cbn [sv_denot]; rewrite Z.add_0_r;
      lazymatch goal with |- Z_to_bv 64 (bv_unsigned (ew ?E 266)) = _ =>
        lazymatch goal with Hie : img_env _ _ E |- _ =>
          rewrite (Hie 266%nat ltac:(unfold A_TEXT, A_LIM; lia)) end end;
      change (VAL 266%nat) with (VAL (A_OBJ 25));
      rewrite (PRobj 25%nat ltac:(change (length cmd_objs) with 116%nat; lia)); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold A_FMT_D; lia].
  + assert (Hcl : pf_bytes (cwc_T ws 2 ++ [0]) = [Z_to_bv 8 0])
    by (unfold cwc_T; replace (Z.to_nat (2 - 2)) with 0%nat by reflexivity; reflexivity).
    rewrite Hcl. intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [nth]. unfold CWC_CID. fold F. unfold OFF_LIST. rewrite Z.add_0_r.
    replace (bv_unsigned (Z_to_bv 8 0)) with 0 by (vm_compute; reflexivity).
    apply aview_of_val_mem1; [| lia].
    fld1 RFr Eu1029; [cbn [sv_denot]; reflexivity | cbn; lia].
  + intros jj Hjj. destruct (PRws jj ltac:(lia)) as (HWB & HWV & HWA). split.
    * eapply (cwc_wordk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HWB | exact HWV].
    * eapply (cwc_strk_of_sblk B RLO RHI HR LAWS); [exact HARF|].
      eapply (cwc_sblk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HWA].
  + eapply (cwc_strk_of_sblk B RLO RHI HR LAWS); [exact HARF|].
    eapply (cwc_sblk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HA1].
  + eapply (cwc_strk_of_sblk B RLO RHI HR LAWS); [exact HARF|].
    eapply (cwc_sblk_now B LAWS); [exact HAR0 | exact HJ4 | exact Eab | exact HA2].
Qed.
End e.
End c.
End b.
