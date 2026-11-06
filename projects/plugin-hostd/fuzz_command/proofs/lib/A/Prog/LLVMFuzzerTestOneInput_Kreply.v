(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first step of segment K of LLVMFuzzerTestOneInput's ASan walk
   (plugin-hostd/fuzz_command, 0x8693c `sub s10,s5,s3`, 0x86940 `addi a0,sp,120`, 0x86944 `jal check_reply`, up to the
   return point 0x86948), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 and A/ACh1.v:114-226 (a
   program call through cl_callS over the callee's contract, the callee's premises discharged at the call state, the
   next point's statement applied at the call's post state) and of lib/A/Prog/check_refusal.v's call step. It proves
   `lt_seg_K0_stmt B MT` of lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v: LTA_K1 B MT m -> LT_K_stmt B MT m. Statement
   passes 4 and 5: check_reply returns at an FP state of its own (apost_baseF), so the call goes through PaFx.v's
   cl_callSF, the next cut is applied at the returned FP state fx1 (rounding mode 0 there by fxrel_frm0) and its post
   is lifted back by srr_apost_baseF_lift; check_reply no longer asks astack_pres. *)
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
PaJournal CmdPaLib PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallPg PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep CmdObj CmdRo
CmdRecBase CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_reply_code_c check_reply_answer_c check_reply_c check_arity_c check_words_c check_refusal_c
check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut HarnessPropsA HarnessPropsABridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small facts the kit does not carry (local to this step) ---- *)
Lemma lt_u8_loc : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 8) with 256 by (vm_compute; reflexivity). apply Z.mod_small. lia.
Qed.
Lemma lt_le_byte_range_loc : forall v n k, 0 <= le_byte v n k < 256.
Proof. intros v n k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
(* an n-wide field of the restricted memory is the same field through the ASan view *)
Lemma lt_aval_of_val_loc : forall segs H (mem : word -> option byte) a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
apply lt_u8_loc. apply lt_le_byte_range_loc.
Qed.
Lemma lt_nth_error0_loc : forall {A : Type} (l : list A) (d : A), (0 < length l)%nat -> nth_error l 0 = Some (nth 0 l d).
Proof. intros A [|a l] d H; [cbn in H; lia | reflexivity]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* an 8-byte word read through the view is that field of the view *)
Lemma lt_aval8_of_rdword_loc : forall (W : world SEGS) mem a v,
rdword (rdW W mem) a = Some v -> aval_mem (rdW W mem) a 8 v.
Proof.
intros W mem a v H. apply lt_aval_of_val_loc. exact (val_mem_of_rdword SEGS (w_H W) mem a v H).
Qed.

(* the machine step of a PCall slot: the jal links ra and enters the callee's entry (cgif A/ACh1.v's call step;
   this segment runs three instructions, so it needs no symbolic state) *)
Lemma lt_step_pcall_loc : forall k s (rd : Prelude.reg) regs mem rom,
plookup (@pl_tpi _ PL_cmd) k = Some (PCall s rd) -> bv_eqb rd 0 = false -> 0 <= k < 2 ^ 40 ->
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) mem rom) =
MachineOk (mkst (regupd regs rd (Z_to_bv 64 (BASE + (k + 4)))) (Z_to_bv 64 (SIGMA s)) mem rom).
Proof.
intros k s rd regs mem rom Hpl Hrd Hk.
pose proof pa_B_ok as (HB0 & HB1 & _).
rewrite <- (pl_tpi_eq (L := cmd_listing)) in Hpl.
pose proof (cert_slot csym (clookup pa_tbl) VAL SIGMA cmd_listing pa_cert _ _ Hpl) as (Hck & Hk0 & Hk4).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrdq _].
apply reg_eqb_eq in Hrdq. subst. apply Z.eqb_eq in Ht.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
lazymatch type of Hdec with
| decode_any _ = Some (Jal ?rr ?ii, _) =>
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) mem rom (Z_to_bv 32 wz) rr ii
  (pa_fetch_ok _ _ Hl) Hec Hdec)
end.
rewrite Hrd. f_equal. f_equal.
- unfold v_addi. rewrite unsigned_lit_small by lia. do 2 f_equal. lia.
- unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht, lit_canon.
  first [reflexivity | f_equal; lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, never restated (LLVMFuzzerTestOneInput_c.v's Section hypothesis, at every FP state) *)
Hypothesis HCHECK_REPLY : forall fx0 : YK11.FPState, @tcheck_reply_spec fx0 rc SK PI B MT.
(* the per-binary facts, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTFL : ameter_fs_laws MT.
(* every record fact this step needs is a lemma of lib/A/Prog/CmdRecBase.v / CmdRecRo.v / CmdRecImg.v, closed over
   LAWS, HB and IMG, so this walk carries no record hypothesis. *)

(* the program's statics, as a footprint: their addresses and the sink's *)
Lemma lt_PG_rec_loc : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
Qed.
Lemma lt_PG_spill_loc : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56).
split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
Qed.
Lemma lt_PG_quit_loc : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.
Ltac lt_getr_loc := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

Theorem lt_seg_K0 : lt_seg_K0_stmt B MT.
Proof.
unfold lt_seg_K0_stmt. intros m K1.
unfold LT_K_stmt. intros cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HMSG.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:EVR.
intros HWORDS HREC HBUD.
(* ---- unpack the premises ---- *)
pose proof HBASE as (HPRE & HROD0 & HRO0 & HVOBJ & E10 & E11 & Hpn & Hnlen & Hgarr & HFRS0 & HGI & HEVB & HLIVE & HMOKb & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HBODY as (HFRAME & HSLOTS & R8 & R9 & R18 & R22 & Hm32 & Hn26 & Hinp).
pose proof HFRAME as (HJ & Rsp & Rgp & Rtp & HSAVED).
pose proof HMSG as (Hr0 & R19 & R20 & R21 & R27 & HHOST & HSTATE).
pose proof HWORDS as (R24 & R23 & R25 & Wtext & Wcopy & Warr & Wcount & Hwplen & Warrslot & Wstr).
pose proof HREC as (HRREP & HRspill & HRcalls & HQval & HQrng & HPerm).
pose proof HBUD as (Hk0 & Hrem0 & Hkrem & HMLE & Hacc0 & Haccrem).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkj & G1 & G2 & G3 & G4 & Ggone & Hpresc & Hstkc & G5 & HQTc).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof pa_base_lo as HBLO.
(* ---- the frame's arithmetic ---- *)
assert (Esp1 : x_sp1 cx = spZ (x_regs cx) - 256) by reflexivity.
assert (Esp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
assert (ESTK : LTOI_STK = 32768) by (vm_compute; reflexivity).
assert (ECRSTK : CHECK_REPLY_STK = 12464) by (vm_compute; reflexivity).
rewrite ESTK in Hslo, Hbot, Hstkc.
assert (Hsp1lo : alloc_ceiling + 32512 <= x_sp1 cx) by lia.
assert (Hsp1hi : x_sp1 cx + 256 <= ly_stk_hi (x_ly cx)) by lia.
assert (Hsp1rng : 0 <= x_sp1 cx /\ x_sp1 cx + 256 <= 2 ^ 47) by lia.
(* ---- the word bounds and the harness facts of the message ---- *)
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as HWB. cbv zeta in HWB.
destruct HWB as (HL0 & HWS2 & HWS4096 & HWS8 & HJN).
pose proof (lt_msg_props_rd SEGS (w_H W) mem (x_sp1 cx + LT_HOSTB) (x_sp1 cx + LT_STATEB)
  (x_pl cx) (x_n cx) r Rh HHOST HSTATE) as HMP.
assert (EVR' : VerbsRun.run_receive atoi_a reply_code_a
  (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r) = (R1, xr, quit))
  by exact EVR.
unfold msg_props_at in HMP. cbv zeta in HMP. rewrite EVR' in HMP. cbv beta iota in HMP.
destruct HMP as (HNR & HRPL & HNO0 & HXLEN & HANSOK & HRPLOK & HARITY & HWORDSP & HRCNEG & HRTOK).
(* ---- the blocks of this message ---- *)
assert (HinW : forall b, In b (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) -> In b (ablocks B ly S)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm|].
  apply in_or_app. right. apply in_or_app. right. exact Hb. }
assert (HinO1 : forall pn, In pn O1 -> In pn (ablocks B ly S)).
{ intros pn Hp. eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. left. exact Hp. }
assert (HinArr : In (arr, SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
  (lt_D (x_pl cx) (x_n cx) r))) (ablocks B ly S)).
{ apply HinW. unfold lt_wblocks. cbv zeta. cbn [In]. right; right; left; reflexivity. }
assert (HinCopy : In (copy, StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
  (lt_D (x_pl cx) (x_n cx) r) + 1) (ablocks B ly S)).
{ apply HinW. unfold lt_wblocks. cbv zeta. cbn [In]. right; left; reflexivity. }
(* ---- the three instructions 0x8693c, 0x86940, 0x86944 ---- *)
assert (Hpl1 : plookup (@pl_tpi _ PL_cmd) LO_K = Some (PW 0x413a8d33)) by (vm_compute; reflexivity).
assert (Hdec1 : decode_any (Z_to_bv 32 0x413a8d33) = Some (Op ALU_SUB 26%bv 21%bv 19%bv, 4%Z)) by vm_refl_bv.
assert (Hpl2 : plookup (@pl_tpi _ PL_cmd) (LO_K + 4) = Some (PW 0x07810513)) by (vm_compute; reflexivity).
assert (Hdec2 : decode_any (Z_to_bv 32 0x07810513) = Some (OpImm ALU_ADD 10%bv 2%bv 120%bv, 4%Z)) by vm_refl_bv.
assert (Hpl3 : plookup (@pl_tpi _ PL_cmd) (LO_K + 8) = Some (PCall CS_check_reply (1%bv : Prelude.reg)))
  by (vm_compute; reflexivity).
assert (Hsp2 : getr regs 2%bv = Z_to_bv 64 (x_sp1 cx)).
{ unfold spZ in Rsp. rewrite <- Rsp. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hlenr : 0 <= lt_len (x_pl cx) (x_n cx) r <= r - SlotSpec.hdr_n r)
  by (apply lt_len_range; lia).
assert (Hhdr : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
assert (Hsub : v_sub (getr regs 21%bv) (getr regs 19%bv) = w64 (lt_r' (x_pl cx) (x_n cx) r)).
{ rewrite R21, R19. unfold v_sub, w64, lt_r'. rewrite !unsigned_lit_small by lia. reflexivity. }
(* step 1: sub s10,s5,s3 *)
eapply (SRr_step SEGS pa_wx W _ _ md); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_sub_at SEGS regs (Z_to_bv 64 (BASE + LO_K)) (mrestrict (w_H W) mem) (seg_rom SEGS)
  (Z_to_bv 32 0x413a8d33) 26%bv 21%bv 19%bv _ (pa_fetch_pw _ _ Hpl1)
  (not_ecall_of_decode _ _ _ Hdec1 ltac:(discriminate)) Hdec1 ltac:(vm_compute; reflexivity) Hsub). }
intros md1 Hsm1.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc1 : v_addi (Z_to_bv 64 (BASE + LO_K)) 4 = Z_to_bv 64 (BASE + (LO_K + 4))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold LO_K; lia). f_equal. lia. }
rewrite Epc1.
set (regsA := regupd regs 26%bv (w64 (lt_r' (x_pl cx) (x_n cx) r))).
assert (A2 : getr regsA 2%bv = Z_to_bv 64 (x_sp1 cx)) by (unfold regsA; lt_getr_loc; exact Hsp2).
assert (Haddi : v_addi (getr regsA 2%bv) (bv_signed (120%bv : bv 12)) = w64 (x_sp1 cx + LT_W)).
{ rewrite A2. unfold v_addi, w64. rewrite unsigned_lit_small by lia.
  replace (bv_signed (120%bv : bv 12)) with 120 by (vm_compute; reflexivity).
  unfold LT_W. reflexivity. }
(* step 2: addi a0,sp,120 *)
eapply (SRr_step SEGS pa_wx W _ _ md1); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_addi_at SEGS regsA (Z_to_bv 64 (BASE + (LO_K + 4))) (mrestrict (w_H W) mem) (seg_rom SEGS)
  (Z_to_bv 32 0x07810513) 10%bv 2%bv 120%bv _ (pa_fetch_pw _ _ Hpl2)
  (not_ecall_of_decode _ _ _ Hdec2 ltac:(discriminate)) Hdec2 ltac:(vm_compute; reflexivity) Haddi). }
intros md2 Hsm2.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc2 : v_addi (Z_to_bv 64 (BASE + (LO_K + 4))) 4 = Z_to_bv 64 (BASE + (LO_K + 8))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold LO_K; lia). f_equal. lia. }
rewrite Epc2.
set (regsB := regupd regsA 10%bv (w64 (x_sp1 cx + LT_W))).
(* step 3: jal check_reply *)
eapply (SRr_step SEGS pa_wx W _ _ md2); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (lt_step_pcall_loc (LO_K + 8) CS_check_reply (1%bv : Prelude.reg) regsB
  (mrestrict (w_H W) mem) (seg_rom SEGS) Hpl3 ltac:(vm_compute; reflexivity) ltac:(unfold LO_K; lia)). }
intros md3 Hsm3.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
replace (LO_K + 8 + 4) with LO_K1 by (vm_compute; reflexivity).
set (regsc := regupd regsB 1%bv (Z_to_bv 64 (BASE + LO_K1))).
rewrite (SIGP CS_check_reply ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_reply) with AF_check_reply by (vm_compute; reflexivity).
(* ---- the registers at the call ---- *)
assert (Q1 : getr regsc 1%bv = Z_to_bv 64 (BASE + LO_K1)) by (unfold regsc; lt_getr_loc; reflexivity).
assert (Q2 : getr regsc 2%bv = getr regs 2%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q3 : getr regsc 3%bv = getr regs 3%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q4 : getr regsc 4%bv = getr regs 4%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q8 : getr regsc 8%bv = getr regs 8%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q9 : getr regsc 9%bv = getr regs 9%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q10 : getr regsc 10%bv = w64 (x_sp1 cx + LT_W)) by (unfold regsc, regsB; lt_getr_loc; reflexivity).
assert (Q18 : getr regsc 18%bv = getr regs 18%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q19 : getr regsc 19%bv = getr regs 19%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q20 : getr regsc 20%bv = getr regs 20%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q22 : getr regsc 22%bv = getr regs 22%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q23 : getr regsc 23%bv = getr regs 23%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q24 : getr regsc 24%bv = getr regs 24%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q25 : getr regsc 25%bv = getr regs 25%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q26 : getr regsc 26%bv = w64 (lt_r' (x_pl cx) (x_n cx) r))
  by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q27 : getr regsc 27%bv = getr regs 27%bv) by (unfold regsc, regsB, regsA; lt_getr_loc; reflexivity).
assert (Qsp : spZ regsc = x_sp1 cx) by (unfold spZ; rewrite Q2; exact Rsp).
assert (Qs0 : s0Z regsc = 32).
{ unfold s0Z. rewrite Q8, R8. unfold w64. apply unsigned_lit_small. lia. }
(* ---- the journal at the call (the three steps write nothing) ---- *)
assert (HJ3 : ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) []
  ly S W mem md3 k).
{ rewrite (same_but_materialized_wvb md2 md3 Hsm3), (same_but_materialized_wvb md1 md2 Hsm2),
    (same_but_materialized_wvb md md1 Hsm1).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
(* ---- check_reply's premises at the call state ---- *)
assert (P3 : Z.of_nat (length (frames S)) <= 7).
{ rewrite Hfrs, HFRS0. cbn [app length]. lia. }
assert (ROI : ro_below_ofl SEGS RLO RHI) by exact (cif_ro_below_ofl _ _ IMG).
assert (P4 : arodata_okP SEGS RLO RHI B (rdW W mem)).
{ apply (arodata_ok_journalP SEGS RLO RHI (cif_relro_img _ _ IMG) B LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md3 k HJ3); [|exact HROD0].
  intros a Hro Hf. exact (cif_prog_not_ro _ _ IMG a Hf Hro). }
assert (P5 : cmd_ro_ok (rdW W mem))
  by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem md HAR P4).
assert (P8 : 0 <= x_sp1 cx + LT_W < 2 ^ 64) by (unfold LT_W; lia).
(* the reply: its block, its pointer and the bytes after its terminator *)
destruct HRREP as (Qrep & HREPAT & HO1Q).
pose proof HREPAT as (Hg8 & Hs8 & Hapart & HCALLS & HANSAT & HRPLAT & HSCAL & HOWN).
unfold areply_at in HRPLAT. rewrite HRPL in HRPLAT.
destruct (l_reply Qrep) as [pnr|] eqn:ELR; [|destruct HRPLAT].
destruct HRPLAT as (HRv & HRsz & HRnz & HRne & HRin & HRlen & HRby & HRlen2).
assert (HinR : In pnr (ablocks B ly S)) by exact HRin.
destruct (al_blocks SEGS B LAWS ly S W mem md (fst pnr) (snd pnr) HAR
  ltac:(destruct pnr; exact HinR)) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & Hrsep & Hrn).
pose proof (req_size_pos (snd pnr) ltac:(lia)) as [Hrq1 Hrq2].
rewrite length_app in HRlen. cbn [length] in HRlen.
assert (P13 : aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 (fst pnr)) by exact HRv.
assert (P14 : 0 <= fst pnr < 2 ^ 64) by lia.
assert (P15 : atail_vis SEGS W mem (fst pnr + Z.of_nat (length xr))).
{ apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md (fst pnr) (snd pnr) _ HAR
    ltac:(destruct pnr; exact HinR)). lia. }
(* the answer *)
assert (HANS : exists ans, aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 ans /\ 0 <= ans < 2 ^ 64 /\
  (forall xa, r_answer R1 = Some xa -> atail_vis SEGS W mem (ans + Z.of_nat (length xa)))).
{ unfold aanswer_at in HANSAT.
  destruct (r_answer R1) as [xa|] eqn:EAN; destruct (l_answer Qrep) as [pna|] eqn:ELA; try contradiction.
  - destruct HANSAT as (HAv & HAnz & HAin & HAlen & HAstr & HAle).
    assert (HinA : In pna (ablocks B ly S)) by exact HAin.
    destruct (al_blocks SEGS B LAWS ly S W mem md (fst pna) (snd pna) HAR
      ltac:(destruct pna; exact HinA)) as (Ha16 & Ha4096 & Haceil & Haapp & Hapres & Hasep & Han).
    pose proof (req_size_pos (snd pna) ltac:(lia)) as [Haq1 Haq2].
    exists (fst pna). split; [exact HAv|]. split; [lia|].
    intros xb Hxb. injection Hxb as <-.
    apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md (fst pna) (snd pna) _ HAR
      ltac:(destruct pna; exact HinA)). lia.
  - exists 0. split; [exact HANSAT|]. split; [lia|]. intros xa Hxa. discriminate Hxa. }
destruct HANS as (ans & P16 & P17 & P18).
(* the harness's struct words on the caller's stack *)
assert (P19 : (x_sp1 cx + LT_W) mod 8 = 0) by exact (lt_w_align B MT cx HBASE).
assert (P20 : spZ regsc <= x_sp1 cx + LT_W) by (rewrite Qsp; unfold LT_W; lia).
assert (P21 : x_sp1 cx + LT_W + WORDS_W + 12 <= ly_stk_hi ly)
  by (rewrite Eshi; unfold LT_W, WORDS_W; lia).
assert (P22 : aval_mem (rdW W mem) (x_sp1 cx + LT_W + WORDS_W) 8 arr).
{ replace (x_sp1 cx + LT_W + WORDS_W) with (x_sp1 cx + LT_W + 16) by (unfold WORDS_W; ring).
  apply lt_aval8_of_rdword_loc. exact Warr. }
assert (P23 : 0 <= arr < 2 ^ 64) by exact (lt_rdword_rng SEGS (w_H W) mem _ _ Warr).
assert (P24 : aval_mem (rdW W mem) (x_sp1 cx + LT_W + WORDS_N) 4
  (Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r)))).
{ replace (x_sp1 cx + LT_W + WORDS_N) with (x_sp1 cx + LT_W + 24) by (unfold WORDS_N; ring). exact Wcount. }
assert (P25 : 0 <= Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r)) < 2 ^ 31) by lia.
(* the first word, when there is one *)
assert (P26 : Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r)) <> 0 ->
  in_blockA (ablocks B ly S) arr 8 /\ arr mod 8 = 0 /\ aval_mem (rdW W mem) arr 8 (nth 0 wp 0) /\
  0 <= nth 0 wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B ly S) (nth 0 wp 0) (Z.of_nat (length (nth 0 (lt_ws (x_pl cx) (x_n cx) r) [])) + 1) /\
  astr_atR (rdW W mem) (nth 0 wp 0) (nth 0 (lt_ws (x_pl cx) (x_n cx) r) []) /\
  atail_vis SEGS W mem (nth 0 wp 0 + Z.of_nat (length (nth 0 (lt_ws (x_pl cx) (x_n cx) r) [])))).
{ intros Hne.
  assert (Hpos : (0 < length (lt_ws (x_pl cx) (x_n cx) r))%nat) by lia.
  assert (Hwpos : (0 < length wp)%nat) by (rewrite Hwplen; exact Hpos).
  pose proof (lt_nth_error0_loc wp 0 Hwpos) as Hwe.
  pose proof (lt_nth_error0_loc (lt_ws (x_pl cx) (x_n cx) r) [] Hpos) as Hse.
  pose proof (Warrslot 0%nat (nth 0 wp 0) Hwe) as Hslot.
  replace (arr + 8 * Z.of_nat 0) with arr in Hslot by (cbn [Z.of_nat]; ring).
  pose proof (Wstr 0%nat (nth 0 wp 0) (nth 0 (lt_ws (x_pl cx) (x_n cx) r) []) Hwe Hse) as (Hlo & Hhi & Hstr).
  destruct (al_blocks SEGS B LAWS ly S W mem md arr _ HAR HinArr) as (Hw16 & Hw4096 & Hwceil & Hwapp & Hwpres & Hwsep & Hwn).
  destruct (al_blocks SEGS B LAWS ly S W mem md copy _ HAR HinCopy) as (Hc16 & Hc4096 & Hcceil & Hcapp & Hcpres & Hcsep & Hcn).
  pose proof (req_size_pos (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
    (lt_D (x_pl cx) (x_n cx) r) + 1) ltac:(lia)) as [Hcq1 Hcq2].
  split.
  { exists arr, (SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
      (lt_D (x_pl cx) (x_n cx) r))). split; [exact HinArr|]. unfold SlotSpec.arr_size in *. lia. }
  split.
  { pose proof (Z.div_mod arr 16 ltac:(lia)) as Dv. rewrite Hw16, Z.add_0_r in Dv.
    rewrite Dv. replace (16 * (arr / 16)) with ((2 * (arr / 16)) * 8) by ring. apply Z_mod_mult. }
  split; [apply lt_aval8_of_rdword_loc; exact Hslot|].
  split; [exact (lt_rdword_rng SEGS (w_H W) mem _ _ Hslot)|].
  split.
  { exists copy, (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
      (lt_D (x_pl cx) (x_n cx) r) + 1). split; [exact HinCopy|]. lia. }
  split; [exact Hstr|].
  apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mem md copy _ _ HAR HinCopy). lia. }
assert (P27 : answer_ok_mA (r_answer R1) xr (Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r)))
  (nth 0 (lt_ws (x_pl cx) (x_n cx) r) [])) by exact (proj1 (answer_ok_a_bridge _ _ _ _) HANSOK).
assert (P28 : reply_okA (Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r)))
  (nth 0 (lt_ws (x_pl cx) (x_n cx) r) []) xr) by exact (proj1 (reply_ok_a_bridge _ _ _) HRPLOK).
assert (P29 : st_nev S + EV_CHECK_REPLY <= EV_MAX) by (unfold EV_CHECK_REPLY; lia).
(* ---- the call ---- *)
eapply SRr_bind;
[ eapply (cl_callSF B LAWS W regsc mem (Z_to_bv 64 (BASE + AF_check_reply))
  LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md3 k
  CHECK_REPLY_STK [] EV_CHECK_REPLY (-256) (Z_to_bv 64 (BASE + LO_K1)) []
  (fun ly2 S2 W2 regs2 mem2 md2 =>
     Permutation (ablocks B ly2 S2) (ablocks B ly S) /\ ly2 = ly /\ exists f, S2 = set_fs f S)
  HJ3) | ].
- rewrite Qsp. lia.
- reflexivity.
- lia.
- lia.
- lia.
- rewrite Q3, Rgp. exact Hgp.
- rewrite Q4, Rtp. exact Htp.
- exact Q1.
- apply ret_ok_codeptr_v; [unfold LO_K1; lia | reflexivity].
- rewrite unsigned_lit_small by (unfold LO_K1; lia). unfold LO_K1. lia.
- rewrite Qs0. apply achain_low. lia.
- (* check_reply's contract at the call state *)
  intros HPRE1. eapply SRr_mono;
  [ exact (HCHECK_REPLY fx ly S W regsc mem md3 [] (x_sp1 cx + LT_W) arr (nth 0 wp 0)
      (Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r))) (fst pnr) ans xr
      (nth 0 (lt_ws (x_pl cx) (x_n cx) r) []) R1 O1 HPRE1 HFRM P3 P4 P5 HVOBJ Q10 P8
      ltac:(exists Qrep; split; [exact HREPAT | exact HO1Q]) HNR HRPL HNO0 P13 P14 P15 P16 P17 P18
      P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29) | ].
  cbv beta. unfold apost_baseF.
  intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3' & -> & Hf31 & Hf32 & HJ3' & HP3 & HQ3).
  exists fx3, ly3, S3, regs3, mem3, md3'.
  split; [rewrite Q1; reflexivity|]. split; [exact Hf31|]. split; [exact Hf32|].
  split; [exact HJ3'|]. split; [exact HP3 | exact HQ3].
- (* the call's footprint is empty *)
  intros a Hf. exfalso. exact (inFP_nil a Hf).
- (* ---- LT_K1_stmt at the return point 0x86948, at the FP state fx1 check_reply returned; its post at fx1 is the
     post at fx (fxrel fx fx1) ---- *)
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md4 & Hfx & -> & HJ4 & HJc & HP2 & HK2).
  apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
  destruct HK2 as (HPerm2 & Ely2 & (fsf & ES2)). subst ly2. subst S2.
  (* what the call kept *)
  assert (KEEP : forall a, x_sp1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a).
  { intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1a & _).
    apply K1a; [lia | lia | apply inFP_nil]. }
  assert (KEEPB : forall p nb a, In (p, nb) (ablocks B ly S) -> p <= a < p + req_size nb ->
    rdW W2 mem2 a = rdW W mem a).
  { intros p nb a Hin Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2b & _).
    replace a with (p + (a - p)) by ring.
    apply (K2b p nb (a - p)); [exact Hin | | lia | apply inFP_nil].
    eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hin]. }
  assert (KEEPI : forall a, inFP cmd_PG a -> rdW W2 mem2 a = rdW W mem a).
  { intros a Hf. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K3c & _).
    destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Hf) as (Hi & Ho & He).
    apply K3c; [exact Hi | exact Ho | exact He
      | apply fp_spares_closed; [exact sink_closed_nil | apply inFP_nil]]. }
  assert (RDK : forall a v, x_sp1 cx <= a -> a + 8 <= 2 ^ 64 -> rdword (rdW W mem) a = Some v ->
    rdword (rdW W2 mem2) a = Some v).
  { intros a v Ha Ha8 Hv. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2) a); [exact Hv|].
    intros kk Hk. apply KEEP; lia. }
  assert (Hcs2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsc rr).
  { intros rr Hrr. pose proof (HP2 (bv_unsigned rr) Hrr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
  assert (G2sp : getr regs2 2%bv = getr regs 2%bv)
    by (rewrite (Hcs2 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q2).
  assert (G2gp : getr regs2 3%bv = getr regs 3%bv)
    by (rewrite (Hcs2 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q3).
  assert (G2tp : getr regs2 4%bv = getr regs 4%bv)
    by (rewrite (Hcs2 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q4).
  assert (G28 : getr regs2 8%bv = getr regs 8%bv)
    by (rewrite (Hcs2 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q8).
  assert (G29 : getr regs2 9%bv = getr regs 9%bv)
    by (rewrite (Hcs2 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q9).
  assert (G218 : getr regs2 18%bv = getr regs 18%bv)
    by (rewrite (Hcs2 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q18).
  assert (G219 : getr regs2 19%bv = getr regs 19%bv)
    by (rewrite (Hcs2 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q19).
  assert (G220 : getr regs2 20%bv = getr regs 20%bv)
    by (rewrite (Hcs2 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q20).
  assert (G222 : getr regs2 22%bv = getr regs 22%bv)
    by (rewrite (Hcs2 22%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q22).
  assert (G223 : getr regs2 23%bv = getr regs 23%bv)
    by (rewrite (Hcs2 23%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q23).
  assert (G224 : getr regs2 24%bv = getr regs 24%bv)
    by (rewrite (Hcs2 24%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q24).
  assert (G225 : getr regs2 25%bv = getr regs 25%bv)
    by (rewrite (Hcs2 25%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q25).
  assert (G226 : getr regs2 26%bv = w64 (lt_r' (x_pl cx) (x_n cx) r))
    by (rewrite (Hcs2 26%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q26).
  assert (G227 : getr regs2 27%bv = getr regs 27%bv)
    by (rewrite (Hcs2 27%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Q27).
  (* the next cut's statement *)
  specialize (K1 fx1 cx ly (set_fs fsf S) W2 regs2 mem2 md4 (k + EV_CHECK_REPLY) acc r Rh O1 text copy arr wp).
  cbv zeta in K1. rewrite EVR in K1. cbv beta iota in K1.
  apply K1; clear K1.
  + exact HBASE.
  + (* rounding mode 0 at fx1 *)
    exact (fxrel_frm0 fx fx1 HFRM Hfx).
  + (* lt_body *)
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    * (* lt_frame *)
      split; [exact HJ4|].
      split; [unfold spZ; rewrite G2sp; exact Rsp|].
      split; [rewrite G2gp; exact Rgp|]. split; [rewrite G2tp; exact Rtp|].
      intros i rr Hi. apply RDK; [| |exact (HSAVED i rr Hi)].
      -- pose proof (nth_error_Some LT_SAVED i) as Hlt.
         assert (Hi13 : (i < length LT_SAVED)%nat) by (apply Hlt; rewrite Hi; discriminate).
         unfold LT_SAVED in Hi13. cbn [length] in Hi13. rewrite Esp1, Esp0 in *. lia.
      -- pose proof (nth_error_Some LT_SAVED i) as Hlt.
         assert (Hi13 : (i < length LT_SAVED)%nat) by (apply Hlt; rewrite Hi; discriminate).
         unfold LT_SAVED in Hi13. cbn [length] in Hi13. unfold x_sp0. lia.
    * (* lt_slots *)
      intros o v Ho. apply RDK; [| | exact (HSLOTS o v Ho)].
      -- assert (Hor : 0 <= o <= 80) by (unfold LT_SLOTS in Ho; cbn [In] in Ho;
           repeat (destruct Ho as [Hq | Ho]; [injection Hq as <- <-; lia|]); destruct Ho).
         lia.
      -- assert (Hor : 0 <= o <= 80) by (unfold LT_SLOTS in Ho; cbn [In] in Ho;
           repeat (destruct Ho as [Hq | Ho]; [injection Hq as <- <-; lia|]); destruct Ho).
         lia.
    * rewrite G28. exact R8.
    * rewrite G29. exact R9.
    * rewrite G218. exact R18.
    * rewrite G222. exact R22.
    * exact Hm32.
    * exact Hn26.
    * exact Hinp.
  + (* lt_kregs *)
    split; [exact Hr0|].
    split; [rewrite G219; exact R19|].
    split; [rewrite G220; exact R20|].
    split; [exact G226|].
    split; [rewrite G227; exact R27|].
    split; [apply RDK; [unfold LT_HOSTB; lia | unfold LT_HOSTB; lia | exact HHOST]|].
    apply RDK; [unfold LT_STATEB; lia | unfold LT_STATEB; lia | exact HSTATE].
  + (* lt_words *)
    split; [rewrite G224; exact R24|].
    split; [rewrite G223; exact R23|].
    split; [rewrite G225; exact R25|].
    split; [apply RDK; [unfold LT_W; lia | unfold LT_W; lia | exact Wtext]|].
    split; [apply RDK; [unfold LT_W; lia | unfold LT_W; lia | exact Wcopy]|].
    split; [apply RDK; [unfold LT_W; lia | unfold LT_W; lia | exact Warr]|].
    split.
    { apply (aval_mem_kept_r (rdW W mem)); [|exact Wcount].
      intros y Hy. apply KEEP; cbn [Z.of_nat] in Hy; unfold LT_W in *; lia. }
    split; [exact Hwplen|].
    split.
    { intros i pt Hi. pose proof (Warrslot i pt Hi) as Hslot.
      assert (Hib : (i < length wp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      rewrite Hwplen in Hib.
      destruct (al_blocks SEGS B LAWS ly S W mem md arr _ HAR HinArr)
        as (Hw16 & Hw4096 & Hwceil & Hwapp & Hwpres & Hwsep & Hwn).
      rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact Hslot|].
      intros kk Hk. apply (KEEPB arr _ _ HinArr).
      pose proof (req_size_pos (SlotSpec.arr_size (StrFun.strnlen_res
        (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r))) ltac:(unfold SlotSpec.arr_size; lia)) as [Hq1 Hq2].
      assert (Hin8 : 8 * Z.of_nat i + 8 <= 8 * Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r))) by lia.
      lia. }
    { intros i pt w Hi Hw. pose proof (Wstr i pt w Hi Hw) as (Hlo & Hhi & Hstr).
      split; [exact Hlo|]. split; [exact Hhi|].
      apply (astr_atR_kept_r (rdW W mem)); [|exact Hstr].
      intros y Hy. apply (KEEPB copy _ _ HinCopy).
      pose proof (req_size_pos (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
        (lt_D (x_pl cx) (x_n cx) r) + 1) ltac:(lia)) as [Hq1 Hq2]. lia. }
  + (* lt_rec *)
    split.
    { apply (rec_repA_kept B ly S (rdW W mem) ly (set_fs fsf S) (rdW W2 mem2) R1 O1).
      - exists Qrep. split; [exact HREPAT | exact HO1Q].
      - intros pn Hp. eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact (HinO1 pn Hp)].
      - intros a [Ha | [Ha | Ha]].
        + apply KEEPI. exact (lt_PG_rec_loc a Ha).
        + apply KEEPI. exact (lt_PG_spill_loc a Ha).
        + destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & nb & Hb & Hr2).
          exact (KEEPB p nb a (HinO1 (p, nb) Hb) Hr2). }
    split; [exact HRspill|]. split; [exact HRcalls|].
    split.
    { apply (aval_mem_kept_r (rdW W mem)); [|exact HQval].
      intros y Hy. apply KEEPI. apply lt_PG_quit_loc. cbn [Z.of_nat] in Hy. lia. }
    split; [exact HQrng|].
    eapply Permutation_trans; [exact HPerm2 | exact HPerm].
  + (* lt_bud *)
    unfold lt_bud. unfold EV_CHECK_REPLY in *. rewrite Z.add_0_r.
    replace (3 + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
      EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
      ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r)))
    with (3 + 0 + EV_CHECK_ARITY + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
      EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
      ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) by ring.
    split; [exact Hk0|]. split; [exact Hrem0|]. split; [exact Hkrem|].
    split; [exact (mo_le_set_fs_r MT MTFL (x_S cx) S fsf acc HMLE)|].
    split; [exact Hacc0 | exact Haccrem].
Qed.

End e.
End f.
End d.
