(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: send_message's first walk segment on plugin-hostd/fuzz_command's ASan image, from
   the entry 0x86b10 to the malloc wrapper's return 0x86c28, ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v,
   AChc.v and ACke.v (cgif_close) at c8557374ad2e, with the class-1 side-stack frame steps of A/ACk1.v
   (cgif_newgif) and the realigned stack pointer of A/AChf.v (flushFrame): fuzz_command's listing, send_message's
   symbolic states. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import send_message_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import send_message_l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* normalise the symbolic state of a st_ok_pi or st_ok hypothesis *)
Ltac norm_pi HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* the writable windows of send_message's regions: the stack below the entry sp (atom 2), the realigned sp's slot (atom 35),
   the frame F (atom 44) and its shadow (atom 61) *)
Ltac awr_sm AG E35 E44 E61 F fpos sp1 sp0 :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?spz ?fp ?b0 ?bc ?fr0 ?lyv ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk spz fp b0 bc fr0 lyv own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | evalE AG | cbn; lia | cbn; lia |]
| eapply awr_ok_cons_stack_off with (n := 35%nat) (d := sp1 - sp0); [reflexivity | rewrite E35, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |]
| eapply awr_ok_cons_gen with (n := 44%nat);
  [reflexivity | rewrite E44, unsigned_lit_small by lia; reflexivity
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; left;
    unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia |]
| eapply awr_ok_cons_gen with (n := 61%nat);
  [reflexivity | rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; right;
    unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; fold F; lia |] ].

Ltac reshok_pi HS bx :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
shok_auto SH (SOff bx 0) Ex (mrestrict (w_H Wx) (ms_mem msx)) end.

Lemma rdword_aview_range : forall segs H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros segs H mem a v Hw. unfold rdword in Hw.
destruct (aview segs H mem a) as [b0|] eqn:H0; [|discriminate].
destruct (aview segs H mem (a + 1)) as [b1|] eqn:H1; [|discriminate].
destruct (aview segs H mem (a + 2)) as [b2|] eqn:H2; [|discriminate].
destruct (aview segs H mem (a + 3)) as [b3|] eqn:H3; [|discriminate].
destruct (aview segs H mem (a + 4)) as [b4|] eqn:H4; [|discriminate].
destruct (aview segs H mem (a + 5)) as [b5|] eqn:H5; [|discriminate].
destruct (aview segs H mem (a + 6)) as [b6|] eqn:H6; [|discriminate].
destruct (aview segs H mem (a + 7)) as [b7|] eqn:H7; [|discriminate].
injection Hw as <-.
destruct (aview_byte segs H mem _ _ H0) as (_ & _ & _ & R0). destruct (aview_byte segs H mem _ _ H1) as (_ & _ & _ & R1).
destruct (aview_byte segs H mem _ _ H2) as (_ & _ & _ & R2). destruct (aview_byte segs H mem _ _ H3) as (_ & _ & _ & R3).
destruct (aview_byte segs H mem _ _ H4) as (_ & _ & _ & R4). destruct (aview_byte segs H mem _ _ H5) as (_ & _ & _ & R5).
destruct (aview_byte segs H mem _ _ H6) as (_ & _ & _ & R6). destruct (aview_byte segs H mem _ _ H7) as (_ & _ & _ & R7).
lia.
Qed.

Lemma denot_len1 : forall E n, ew E 11 = Z_to_bv 64 n -> 0 <= n <= 8192 ->
sv_denot E (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_SLTU (SOff 11 0) (SLit 1))) = Z_to_bv 64 (Z.max n 1).
Proof.
intros E n H Hn. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 11 n H) by lia.
change (zcanon 1) with 1.
destruct (Z.ltb_spec n 1) as [Hl | Hl].
- replace n with 0 by lia. reflexivity.
- change (zcanon 0) with 0. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ev_args_nonneg : forall R, 0 <= ev_args R.
Proof. intros R. unfold ev_args. induction (r_calls R) as [|c l IH]; cbn [fold_right]; lia. Qed.
(* a saved register's chunk of the stack region (atom 2) *)
Ltac sv_chunk HRk AG EE Usp regs :=
lazymatch goal with |- val_mem _ _ (spZ regs + ?o) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
let rn := eval vm_compute in (Z.to_nat r) in
lazymatch type of HRk with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi o 8%N (SOff rn 0) _ HRk);
[ rewrite (AG 2%nat) by lia; exact Usp
| cbn; tauto
| cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (AG rn) by lia; rewrite (EE rn (Z_to_bv 5 r) eq_refl);
  symmetry; apply Z_to_bv_bv_unsigned
| pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; cbn; lia
| cbn; lia ] end end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section k.
Variable segs : list Segment.
Variable B : asyms.
(* a value above the call's stack window is kept across the call *)
Lemma val_mem_kept_hi : forall lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) a (n : nat) v,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er ->
alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= slo \/ shi <= a) ->
val_mem segs (mrestrict (w_H W) memc) a n v -> val_mem segs (mrestrict (w_H W2) mem2) a n v.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er a n v (K1 & _) Ha1 Ha2 Hsep Hv.
apply (val_mem_moved segs (w_H W) (w_H W2) memc mem2 a a n v); [|exact Hv].
intros k Hk. apply K1; lia.
Qed.
(* a value in a live frame or its shadow, outside the call's footprint, is kept across the call *)
Lemma val_mem_kept_frame : forall lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) cid pos a (n : nat) v,
acall_kept segs B lyc Sc W memc W2 mem2 slo shi Er -> In (cid, pos) (frames Sc) ->
((frame_addr lyc cid pos <= a /\ a + Z.of_nat n <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
 (shadow_addr (frame_addr lyc cid pos) <= a /\ a + Z.of_nat n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)) ->
(forall x, a <= x < a + Z.of_nat n -> ~ Er x) ->
val_mem segs (mrestrict (w_H W) memc) a n v -> val_mem segs (mrestrict (w_H W2) mem2) a n v.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er cid pos a n v (_ & _ & _ & K4 & _) Hin Hr HnE Hv.
apply (val_mem_moved segs (w_H W) (w_H W2) memc mem2 a a n v); [|exact Hv].
intros k Hk. apply (K4 cid pos (a + k) Hin); [|apply HnE; lia].
unfold in_zr, frame_rng. cbn [fst snd]. destruct Hr as [Hr | Hr]; [left | right]; lia.
Qed.
End k.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNTP := SRr_run_to_pi_AJ B LAWS.

Theorem sm_s1 : SM_P1_stmt B MT -> SM_P0_stmt B MT.
Proof.
intros P1 ly S W regs mem md ch src n D R O rest CX.
pose proof CX as (HPRE & HFRM & Hfr3 & HROD & HRO & HVO & H10 & Hsrc & H11 & Hn & HlenD & HD & Hin & HPerm & HREP
& Hcalls & Hdecl & Hev & Hlive & MOK).
pose proof (sm_entry B TL LAWS TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SEND_MESSAGE_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (@pa_base_lo _ _ _ PI) as HBLO.
remember (Eimg (Ereg regs (sm_extra (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
by (intros nn r Hnn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (sm_extra (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth sm_extra map] in E32, E33, E34. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
clear HE.
assert (AG : forall nn, (nn < 32)%nat -> ew E nn = ew E nn) by (intros; reflexivity).
unfold cfg_at. change (w64 (BASE + AF_send_message)) with (Z_to_bv 64 (BASE + AF_send_message)).
shok_auto SHOK SMBx E (mrestrict (w_H W) mem).
assert (HSTK : 112 + 16384 <= SEND_MESSAGE_STK)
by (unfold SEND_MESSAGE_STK; change ASTACK with 16384; lia).
paj_run_to_tok RUNTO HS HJ SHOK SMBspan SM_ANDI_NEXT.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr0 ?lyv ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk sp0 fp b0 bc fr0 lyv own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG.
(* the realigned stack pointer sp1 = (sp0 - 96) & -32 becomes atom 35 *)
set (sp1 := sm_sp1 (spZ regs)).
assert (Hm96 : (spZ regs - 96) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
destruct (sp1_facts (spZ regs - 96) ltac:(lia) Hm96) as (Hsp1r & Hsp1al & Hsp1al16).
change (32 * ((spZ regs - 96) / 32)) with sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
(denot_and_m32 E 2 (spZ regs) (-96) ltac:(rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned)
ltac:(lia) ltac:(lia) ltac:(lia)) R2.
pose proof (st_ok_pi_havoc_hi 35 E _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E35 : ew Ev 35 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 35 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 35 0) HS ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E35, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_pi HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 35%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS; rename HS3 into HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (trim_stack rs (-88) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_pi HS.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => let HEv := rnHEI Ev in
assert (E241 : ew Ev 241 = Z_to_bv 64 (VAL (A_OBJ 0))) by exact (img_env_atomP Ev (A_OBJ 0) HEv ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
assert (E242 : ew Ev 242 = Z_to_bv 64 (VAL (A_OBJ 1))) by exact (img_env_atomP Ev (A_OBJ 1) HEv ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
assert (E253 : ew Ev 253 = Z_to_bv 64 (VAL (A_OBJ 12))) by exact (img_env_atomP Ev (A_OBJ 12) HEv ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 35%nat) 0 8 0 8 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E35, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJpres; lia)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS. norm_pi HS. clear HJpres.
reshok_pi HS 32%nat.
paj_run_tok RUN HS HJ SHOK SMBspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr0 ?lyv ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ev rs' stk sp0 fp b0 bc fr0 lyv own) end.
  eapply awr_ok_cons_stack_off with (n := 35%nat) (d := sp1 - spZ regs); [reflexivity | rewrite E35, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | evalE AG | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ.
(* __asan_stack_malloc_1(96): the class-1 frame F *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
rewrite E35 in R2. rewrite (AG 3%nat), (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite (AG 4%nat), (EE 4%nat 4%bv eq_refl) in R4 by lia.
pmkst HS.
pose proof (palf_sm B TLF 1 ltac:(cbn; right; left; reflexivity)) as HSM1. change (cs_stack_malloc 1) with CS___asan_stack_malloc_1 in HSM1.
rewrite HSM1.
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
lazymatch type of HJ with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memX ?mdX _ =>
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell0 & Kuar0 & Kgot0 & Kguar0) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rgX _ ?mmX _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 1 (ASM fx) ltac:(lia) W rgX mmX SEND_MESSAGE_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - change ESTACK with 4096. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 R1.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag2 & HK & HJe & (fS2 & ES2)).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & Kuar2 & Kgot2 & Kguar2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot0, Kgot2. rewrite (pal_cell B TL) in Kcell0, Kcell2.
rewrite <- SB_SHADOW_OFF in Kcell0, Kcell2. rewrite (palf_got_uar B TLF) in Kguar0, Kguar2.
jafter_call_keep_hi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil | specialize (HS2 HQ); clear HQ ] end.
{ eapply region_kept_stack_aj with (sp0 := spZ regs) (sp := sp1); [exact HK | exact HJ2 | rewrite E35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia]. }
{ eapply region_kept_stack_aj with (sp0 := spZ regs) (sp := spZ regs); [exact HK | exact HJ2 | evalE AG | cbn; lia | cbn; lia | cbn; lia | cbn; lia | cbn; lia]. }
{ apply region_kept_val_at with (n := 8%nat) (lo := VAL (A_OBJ 0)) (v := VAL (A_OBJ 12));
  [rewrite E241, unsigned_lit_small by lia; reflexivity | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia]. }
{ apply region_kept_val_at with (n := 8%nat) (lo := VAL (A_OBJ 12)) (v := SB);
  [rewrite E253, unsigned_lit_small by lia; reflexivity | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia]. }
{ apply region_kept_val_at with (n := 8%nat) (lo := VAL (A_OBJ 1)) (v := as_uar_cell B);
  [rewrite E242, unsigned_lit_small by lia; reflexivity | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar0) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar2) | lia]. }
{ apply region_kept_val_at with (n := 4%nat) (lo := as_uar_cell B) (v := 1);
  [rewrite E33, unsigned_lit_small by lia; reflexivity | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar0) | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rebaseE HS AG HEv.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E44 : ew Ev 44 = Z_to_bv 64 F) by (rewrite HEv; exact (eq_trans (ew_havoc_new _ 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lia)) Ha0)) end.
clear HEv.
(* the frame F (atom 44), its flag pointer FL (atom 60) and its shadow SB_F F (atom 61) *)
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
change (fs_frame_bytes 1) with 128 in HFapp, HFpres, HFSpres, HFceil, HFimg, Hz, Hflag2. change (128 / 8) with 16 in HFSpres.
change (frame_addr ly 1 fpos) with F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFimg.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres.
pose proof (rdword_aview_range _ _ _ _ _ Hflag2) as HFLr.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
pose proof (st_ok_pi_havoc_hi 60 E1 _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB_F F)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E60 : ew Ev 60 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (SB_F F)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E61 : ew Ev 61 = Z_to_bv 64 (SB_F F)) by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 FL; Z_to_bv 64 (SB_F F)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 44 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E44, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 61 (mkAF (SB + 512) (SB + 17592186044416 - 64) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 44 32 61 F SB E44 ltac:(lia) E32 E61)) as HS3;
clear HS; rename HS3 into HS; norm_pi HS;
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 60 1 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1) with 128; rewrite E44, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (128 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (128 - 8)) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag2)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1) with 128; evalE AG; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_pi HS end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 61 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); evalE AG; unfold SB in *;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_pi HS end.
clear SHOK.
paj_run_to_sh RUNTP HS HJ2 0x740.
{ awr_sm AG E35 E44 E61 F fpos sp1 (spZ regs). }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ2.
(* the frame's shadow is read-only for the token run of the call *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 61%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
reshok_pi HS 32%nat.
paj_run_tok RUN HS HJ2 SHOK SMBspan.
{ awr_sm AG E35 E44 E61 F fpos sp1 (spZ regs). }
clear HF HFr HG.
rewrite ?wvb_collapse in HJ2.
(* the malloc wrapper, with len + (len == 0) = max(len, 1) bytes *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
rewrite E35 in R2, R9. rewrite E44 in R18, R24. rewrite E61 in R23. rewrite E32 in R25.
rewrite (AG 3%nat), (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite (AG 4%nat), (EE 4%nat 4%bv eq_refl) in R4 by lia.
rewrite (AG 2%nat), (EE 2%nat 2%bv eq_refl) in R8 by lia. rewrite (AG 11%nat), (EE 11%nat 11%bv eq_refl), H11 in R19 by lia.
rewrite (AG 10%nat), (EE 10%nat 10%bv eq_refl), H10 in R20 by lia.
rewrite (AG 26%nat), (EE 26%nat 26%bv eq_refl) in R26 by lia. rewrite (AG 27%nat), (EE 27%nat 27%bv eq_refl) in R27 by lia.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs msx) 10 = w64 (Z.max n 1))
by (rewrite (st_ok_restrict_reg SEGS Hh Ex ssx msx 10 HS); change (sv_denot Ex e = Z_to_bv 64 (Z.max n 1)); apply denot_len1;
    [rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia]);
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRs;
pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRf;
pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRk end.
cbn [ms_mem restrict] in HRs, HRf, HRk.
pmkst HS. rewrite (pal_malloc B TL).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => set (regsM := ms_regs msx) in *; set (memM := ms_mem msx) in * end.
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => set (mdM := mdx) in * end.
(* the saved registers and the frame's bytes at the call *)
assert (SV0 : sm_saved regs (mrestrict (w_H W) memM)).
{ intros o r Hor. cbn [sm_saved_list In] in Hor.
  repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; sv_chunk HRk AG EE Usp regs |]); destruct Hor. }
assert (FR0 : sm_frame (mrestrict (w_H W) memM) F FL).
{ lazymatch type of HRf with region_ok _ ?Ex _ _ =>
  split; [| split; [| split; [| split]]];
  [ apply (field_of_region Ex _ 44 F _ _ _ _ _ 120 8%N (SOff 60 0) FL HRf);
    [rewrite E44, unsigned_lit_small by lia; reflexivity | cbn; tauto
    | cbn [sv_denot]; rewrite E60, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]
  | apply (field_of_region Ex _ 44 F _ _ _ _ _ 32 4%N (SLit 7) 7 HRf);
    [rewrite E44, unsigned_lit_small by lia; reflexivity | cbn; tauto | reflexivity | cbn; lia | cbn; lia]
  | apply (field_of_region Ex _ 61 (SB_F F) _ _ _ _ _ 4 1%N (SLit 0) 0 HRs);
    [rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity | cbn; tauto | reflexivity | cbn; lia | cbn; lia]
  | apply (field_of_region Ex _ 61 (SB_F F) _ _ _ _ _ 5 1%N (SLit 0) 0 HRs);
    [rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity | cbn; tauto | reflexivity | cbn; lia | cbn; lia]
  | apply (field_of_region Ex _ 61 (SB_F F) _ _ _ _ _ 6 1%N (SLit 0) 0 HRs);
    [rewrite E61; unfold SB_F; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity | cbn; tauto | reflexivity | cbn; lia | cbn; lia] ] end. }
destruct (sm_achain B [] ly S W regs mem md ch fpos ly S2 W memM mdM 0 HPRE (conj HJ2 Hfrs2) (fun a _ Ha => inFP_nil a Ha) SV0)
as (ch1 & Hch1). fold sp1 in Hch1.
assert (HCP : chain_pre ly (aview SEGS (w_H W) memM) regsM ch1).
{ eapply achain_chain_pre; [exact Hch1 | | |].
  - unfold spZ. rewrite R2, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia. }
pose proof (ev_args_nonneg R) as Hea. pose proof (ev_vr_nonneg (RecModel.rec_clear R) D) as Hevr.
assert (MLE2 : mo_le MT S S2 0) by (rewrite ES2; apply (mo_le_set_fs_r MT MTFL); exact (mle_start MT S MTL)).
assert (MOK2 : mo_ok MT S2 (mo_malloc MT (Z.max n 1))).
{ apply (mok_station MT S S2 (XM_SEND_MESSAGE MT R D) 0 (mo_malloc MT (Z.max n 1)) MTL MOK MLE2).
  - apply (mo_malloc_nonneg MT MTL). lia.
  - unfold XM_SEND_MESSAGE, XM_REC_CLEAR, XM_VERBS_RECEIVE.
    pose proof (mo_malloc_mono MT MTL (Z.max n 1) 8192 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hmreq.
    pose proof (mo_free_nonneg MT MTL) as Hfree.
    pose proof (Z.mul_nonneg_nonneg (ev_args R + 2) (mo_free MT) ltac:(lia) Hfree).
    pose proof (Z.mul_nonneg_nonneg (ev_vr (RecModel.rec_clear R) D) (mo_malloc MT VERBS_RECEIVE_REQ + mo_free MT)
      Hevr ltac:(lia)).
    lia. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W regsM memM SEND_MESSAGE_STK (spZ regs) [] ly S W mem md
    [(1, fpos)] ly S2 mdM 0 (Z.max n 1) (sp1 - spZ regs) (Z_to_bv 64 (BASE + SM_RET_MALLOC)) ch1 HJ2).
  - exact R10.
  - unfold MALLOC_MAX. lia.
  - rewrite Hbb2. unfold LIVE_SEND_MESSAGE, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in Hlive. lia.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
  - lia.
  - change ASTACK with 16384. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite R1. reflexivity.
  - apply ret_ok_codeptr_v; [unfold SM_RET_MALLOC, AF_send_message; lia | reflexivity].
  - rewrite Hnev2. unfold EV_SEND_MESSAGE, EV_REC_CLEAR in Hev. lia.
  - exact HCP.
  - exact MOK2. }
cbv beta.
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hres & Hfrs3 & Hr4 & Hbl3 & HK3 & MLE3 & _).
(* the post state's facts: the block is fresh and apart from the frame and its shadow *)
pose proof (proj1 HJ3) as HAR3.
assert (Hres3 : In (res, Z.max n 1) (ablocks B ly3 S3)) by (rewrite Hbl3; apply in_or_app; right; left; reflexivity).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
assert (EF3 : frame_addr ly3 1 fpos = F).
{ pose proof HJ3 as (_ & Hly3 & _). destruct Hly3 as (_ & _ & _ & _ & _ & HlyF & _). unfold F, frame_addr. rewrite HlyF. reflexivity. }
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hres3 Hfin3) as HdRF.
rewrite EF3 in HdRF. unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (fs_frame_bytes 1) with 128 in HdRF.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hres3) as (_ & Hres4096 & Hresceil & Hresapp & _).
pose proof (req_size_pos (Z.max n 1) ltac:(lia)) as Hrq.
assert (HnoF : forall x, F <= x < F + 128 -> ~ (res <= x < res + req_size (Z.max n 1))) by (intros x Hx Hr; lia).
assert (HnoS : forall x, SB + F / 8 <= x < SB + F / 8 + 16 -> ~ (res <= x < res + req_size (Z.max n 1))).
{ intros x Hx Hr. unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *. lia. }
apply (P1 ly S W regs mem md ch src n D R O rest ly3 S3 W3 regs3 mem3 md3 1 fpos res CX).
- split; [exact HJ3 | rewrite Hfrs3; exact Hfrs2].
- lia.
- unfold sm_regs_core. fold F.
  repeat split; first
  [ etransitivity; [exact (HP3 2 ltac:(unfold acallee_saved; lia)) | exact R2]
  | etransitivity; [exact (HP3 3 ltac:(unfold acallee_saved; lia)) | exact R3]
  | etransitivity; [exact (HP3 4 ltac:(unfold acallee_saved; lia)) | exact R4]
  | etransitivity; [exact (HP3 8 ltac:(unfold acallee_saved; lia)) | exact R8]
  | etransitivity; [exact (HP3 9 ltac:(unfold acallee_saved; lia)) | exact R9]
  | etransitivity; [exact (HP3 18 ltac:(unfold acallee_saved; lia)) | exact R18]
  | etransitivity; [exact (HP3 19 ltac:(unfold acallee_saved; lia)) | exact R19]
  | etransitivity; [exact (HP3 20 ltac:(unfold acallee_saved; lia)) | exact R20]
  | etransitivity; [exact (HP3 23 ltac:(unfold acallee_saved; lia)) | exact R23]
  | etransitivity; [exact (HP3 24 ltac:(unfold acallee_saved; lia)) | exact R24]
  | etransitivity; [exact (HP3 25 ltac:(unfold acallee_saved; lia)) | exact R25]
  | etransitivity; [exact (HP3 26 ltac:(unfold acallee_saved; lia)) | exact R26]
  | etransitivity; [exact (HP3 27 ltac:(unfold acallee_saved; lia)) | exact R27] ].
- exact Hres.
- intros o r Hor. pose proof (SV0 o r Hor) as Hv.
  assert (Ho : -88 <= o <= -8) by (cbn [sm_saved_list In] in Hor; repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; lia |]); destruct Hor).
  apply (val_mem_kept_hi SEGS B _ _ _ _ _ _ _ _ _ _ _ _ HK3); [lia | cbn; lia | right; lia | exact Hv].
- destruct FR0 as (V1 & V2 & V3 & V4 & V5). unfold sm_frame.
  split; [| split; [| split; [| split]]].
  + apply (val_mem_kept_frame SEGS B _ _ _ _ _ _ _ _ _ 1 fpos _ _ _ HK3 Hfin2); [left; fold F; change (fs_frame_bytes 1) with 128; cbn [Z.of_nat Pos.of_succ_nat]; lia | intros x Hx; apply HnoF; fold F in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact V1].
  + apply (val_mem_kept_frame SEGS B _ _ _ _ _ _ _ _ _ 1 fpos _ _ _ HK3 Hfin2); [left; fold F; change (fs_frame_bytes 1) with 128; cbn [Z.of_nat Pos.of_succ_nat]; lia | intros x Hx; apply HnoF; fold F in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact V2].
  + apply (val_mem_kept_frame SEGS B _ _ _ _ _ _ _ _ _ 1 fpos _ _ _ HK3 Hfin2);
    [right; unfold shadow_addr, SB_F; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; cbn [Z.of_nat Pos.of_succ_nat]; lia
    | intros x Hx; apply HnoS; unfold SB_F in Hx; fold F in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact V3].
  + apply (val_mem_kept_frame SEGS B _ _ _ _ _ _ _ _ _ 1 fpos _ _ _ HK3 Hfin2);
    [right; unfold shadow_addr, SB_F; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; cbn [Z.of_nat Pos.of_succ_nat]; lia
    | intros x Hx; apply HnoS; unfold SB_F in Hx; fold F in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact V4].
  + apply (val_mem_kept_frame SEGS B _ _ _ _ _ _ _ _ _ 1 fpos _ _ _ HK3 Hfin2);
    [right; unfold shadow_addr, SB_F; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; cbn [Z.of_nat Pos.of_succ_nat]; lia
    | intros x Hx; apply HnoS; unfold SB_F in Hx; fold F in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact V5].
- rewrite Hbl3, Eab. reflexivity.
- exact Hr4.
- intros Hin0. apply in_split in Hin0 as (l1 & l2 & El).
  assert (E3 : ablocks B ly3 S3 = l1 ++ (res, Z.max n 1) :: l2 ++ (res, Z.max n 1) :: []).
  { rewrite Hbl3, Eab, El, <- app_assoc. reflexivity. }
  pose proof (sep_blocks_pos SEGS B LAWS _ _ _ _ _ _ _ _ _ _ HAR3 E3) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
- pose proof (mle_station MT S S2 S3 0 (mo_malloc MT (Z.max n 1)) MTL MLE2 MLE3) as Hm. rewrite Z.add_0_l in Hm. exact Hm.
Qed.
End e.
End f.
End d.
