(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first step of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a04 `add s7,s3,s4`, 0x86a08 `sub s8,s6,s4`, 0x86a0c `addi a0,sp,120`, 0x86a10 `jal check_reply`, up to the return point 0x86a14): check_reply returns at an FP state of its own (apost_baseF), so the call goes through PaFx.v's cl_callSF and srr_after_callF and the cut after it is applied at the returned FP state; the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Kreply.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 and A/ACh1.v:114-226 (a program call through cl_callS over the callee's contract, the callee's premises discharged at the call state, the next point's statement applied at the call's post state). Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaJournal CmdPaLib PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallPg PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj CmdRo CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_reply_code_c check_reply_answer_c check_reply_c check_arity_c check_words_c check_refusal_c
check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Karity_s1 HarnessPropsA HarnessPropsABridge.
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
   this segment runs four instructions, so it needs no symbolic state) *)
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
(* the callee's statement, exactly LLVMFuzzerTestOneInput_c.v's Section hypothesis (every FP state) *)
Hypothesis HCHECK_REPLY : forall fx0 : YK11.FPState, @tcheck_reply_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTFL : ameter_fs_laws MT.
(* every record fact this step needs is a lemma of lib/B/Prog/CmdRecFacts.v, closed over LAWS, HB and IMG
   (RULING-STMT.md section 2.1), so this walk carries no record hypothesis. *)

Ltac lt_getr_loc := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].

(* the budget at a state whose allocator state differs only by its side-stack frames (check_reply's class-1
   frame, taken and released: meter class (b)) *)
Lemma lt_bud_set_fs_loc : forall cx S k acc rem f, lt_bud MT cx S k acc rem -> lt_bud MT cx (set_fs f S) k acc rem.
Proof.
intros cx S k acc rem f (H1 & H2 & H3 & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [exact (mo_le_set_fs_r MT MTFL (x_S cx) S f acc H4)|]. split; [exact H5 | exact H6].
Qed.

Theorem lt_seg_K0 : lt_seg_K0_stmt B MT.
Proof.
unfold lt_seg_K0_stmt. intros m K1.
unfold LT_K_stmt. intros cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HMSG.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:EVR.
intros HWORDS HREC HBUD.
(* ---- unpack the premises ---- *)
pose proof HBASE as (HPRE & HROD0 & HRO0 & HVOBJ & E10 & E11 & Hpn & Hnlen & Hgarr & HFRS0 & HGI & HEVB & HLIVE & HMOKb).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HBODY as (HFRAME & HSLOTS & R8 & R9 & R18 & R25 & R26 & R27 & Hm32).
pose proof HFRAME as (HJ & Rsp & Rgp & Rtp & HSAVED).
pose proof HMSG as (Hr0 & R19 & R20 & R21 & R22 & Rst & Rho & HHOST).
pose proof HWORDS as (Wtext & Wcopy & Warr & Wcount & Hwplen & Warrslot & Wstr).
pose proof HREC as (HRREP & HRspill & HRcalls & HQval & HQrng & HPerm).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkj & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof pa_base_lo as HBLO.
pose proof alloc_ceiling_lt as HACL.
(* ---- the frame's arithmetic ---- *)
assert (Esp1 : x_sp1 cx = spZ (x_regs cx) - 256) by reflexivity.
assert (Esp0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
assert (ESTK : LTOI_STK = 32768) by (vm_compute; reflexivity).
assert (ECRSTK : CHECK_REPLY_STK = 12464) by (vm_compute; reflexivity).
rewrite ESTK in Hslo, Hbot.
assert (Hsp1lo : alloc_ceiling + 32512 <= x_sp1 cx) by lia.
assert (Hsp1hi : x_sp1 cx + 256 <= ly_stk_hi (x_ly cx)) by lia.
assert (Hsp1rng : 0 <= x_sp1 cx /\ x_sp1 cx + 256 <= 2 ^ 47) by lia.
(* ---- the payload block and the message inside it ---- *)
destruct (lt_payload_live B MT cx r HBASE Hr0) as (Hn26 & Hpin).
destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) (x_p cx) (x_n cx) HAR0 Hpin)
  as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreqn].
assert (Hlenr : 0 <= lt_len (x_pl cx) (x_n cx) r <= r - SlotSpec.hdr_n r) by (apply lt_len_range; lia).
assert (Hhdr : 0 < SlotSpec.hdr_n r <= r) by (unfold SlotSpec.hdr_n; lia).
(* ---- the word bounds and the harness facts of the message ---- *)
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as HWB. cbv zeta in HWB.
destruct HWB as (HL0 & HWS2 & HWS4096 & HWS8 & HJN).
pose proof (lt_msg_props (x_pl cx) (x_n cx) r Rh Rst Rho) as HMP.
assert (EVR' : VerbsRun.run_receive atoi_a reply_code_a
  (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r) = (R1, xr, quit))
  by exact EVR.
unfold msg_props_at in HMP. cbv zeta in HMP. rewrite EVR' in HMP. cbv beta iota in HMP.
destruct HMP as (HNR & HRPL & HNO0 & HXLEN & HANSOK & HRPLOK & HARITY & HWORDSP & HRCNEG & HRTOK).
(* ---- the blocks of this message ---- *)
assert (HinW : forall b, In b (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) -> In b (ablocks B ly S)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HPerm|].
  apply in_or_app. right. apply in_or_app. right. exact Hb. }
assert (HinArr : In (arr, SlotSpec.arr_size (StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
  (lt_D (x_pl cx) (x_n cx) r))) (ablocks B ly S)).
{ apply HinW. unfold lt_wblocks. cbv zeta. cbn [In]. right; right; left; reflexivity. }
assert (HinCopy : In (copy, StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r)))
  (lt_D (x_pl cx) (x_n cx) r) + 1) (ablocks B ly S)).
{ apply HinW. unfold lt_wblocks. cbv zeta. cbn [In]. right; left; reflexivity. }
(* ---- the four instructions 0x86a04, 0x86a08, 0x86a0c, 0x86a10 ---- *)
assert (Hpl1 : plookup (@pl_tpi _ PL_cmd) LO_K = Some (PW 0x01498bb3)) by (vm_compute; reflexivity).
assert (Hdec1 : decode_any (Z_to_bv 32 0x01498bb3) = Some (Op ALU_ADD 23%bv 19%bv 20%bv, 4%Z)) by vm_refl_bv.
assert (Hpl2 : plookup (@pl_tpi _ PL_cmd) (LO_K + 4) = Some (PW 0x414b0c33)) by (vm_compute; reflexivity).
assert (Hdec2 : decode_any (Z_to_bv 32 0x414b0c33) = Some (Op ALU_SUB 24%bv 22%bv 20%bv, 4%Z)) by vm_refl_bv.
assert (Hpl3 : plookup (@pl_tpi _ PL_cmd) (LO_K + 8) = Some (PW 0x07810513)) by (vm_compute; reflexivity).
assert (Hdec3 : decode_any (Z_to_bv 32 0x07810513) = Some (OpImm ALU_ADD 10%bv 2%bv 120%bv, 4%Z)) by vm_refl_bv.
assert (Hpl4 : plookup (@pl_tpi _ PL_cmd) (LO_K + 12) = Some (PCall CS_check_reply (1%bv : Prelude.reg)))
  by (vm_compute; reflexivity).
assert (Hsp2 : getr regs 2%bv = Z_to_bv 64 (x_sp1 cx)).
{ unfold spZ in Rsp. rewrite <- Rsp. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hadd : v_add (getr regs 19%bv) (getr regs 20%bv) = w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r))).
{ rewrite R19, R20. unfold v_add, w64. rewrite !unsigned_lit_small by lia. f_equal. unfold lt_r'. lia. }
(* step 1: add s7,s3,s4 *)
eapply (SRr_step SEGS pa_wx W _ _ md); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_add_at SEGS regs (Z_to_bv 64 (BASE + LO_K)) (mrestrict (w_H W) mem) (seg_rom SEGS)
  (Z_to_bv 32 0x01498bb3) 23%bv 19%bv 20%bv _ (pa_fetch_pw _ _ Hpl1)
  (not_ecall_of_decode _ _ _ Hdec1 ltac:(discriminate)) Hdec1 ltac:(vm_compute; reflexivity) Hadd). }
intros md1 Hsm1.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc1 : v_addi (Z_to_bv 64 (BASE + LO_K)) 4 = Z_to_bv 64 (BASE + (LO_K + 4))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold LO_K; lia). f_equal. lia. }
rewrite Epc1.
set (regsA := regupd regs 23%bv (w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r)))).
assert (Hsub : v_sub (getr regsA 22%bv) (getr regsA 20%bv) = w64 (lt_r' (x_pl cx) (x_n cx) r)).
{ unfold regsA. lt_getr_loc. rewrite R22, R20. unfold v_sub, w64, lt_r'. rewrite !unsigned_lit_small by lia.
  reflexivity. }
(* step 2: sub s8,s6,s4 *)
eapply (SRr_step SEGS pa_wx W _ _ md1); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_sub_at SEGS regsA (Z_to_bv 64 (BASE + (LO_K + 4))) (mrestrict (w_H W) mem) (seg_rom SEGS)
  (Z_to_bv 32 0x414b0c33) 24%bv 22%bv 20%bv _ (pa_fetch_pw _ _ Hpl2)
  (not_ecall_of_decode _ _ _ Hdec2 ltac:(discriminate)) Hdec2 ltac:(vm_compute; reflexivity) Hsub). }
intros md2 Hsm2.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc2 : v_addi (Z_to_bv 64 (BASE + (LO_K + 4))) 4 = Z_to_bv 64 (BASE + (LO_K + 8))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold LO_K; lia). f_equal. lia. }
rewrite Epc2.
set (regsB := regupd regsA 24%bv (w64 (lt_r' (x_pl cx) (x_n cx) r))).
assert (B2 : getr regsB 2%bv = Z_to_bv 64 (x_sp1 cx)) by (unfold regsB, regsA; lt_getr_loc; exact Hsp2).
assert (Haddi : v_addi (getr regsB 2%bv) (bv_signed (120%bv : bv 12)) = w64 (x_sp1 cx + LT_W)).
{ rewrite B2. unfold v_addi, w64. rewrite unsigned_lit_small by lia.
  replace (bv_signed (120%bv : bv 12)) with 120 by (vm_compute; reflexivity).
  unfold LT_W. reflexivity. }
(* step 3: addi a0,sp,120 *)
eapply (SRr_step SEGS pa_wx W _ _ md2); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_addi_at SEGS regsB (Z_to_bv 64 (BASE + (LO_K + 8))) (mrestrict (w_H W) mem) (seg_rom SEGS)
  (Z_to_bv 32 0x07810513) 10%bv 2%bv 120%bv _ (pa_fetch_pw _ _ Hpl3)
  (not_ecall_of_decode _ _ _ Hdec3 ltac:(discriminate)) Hdec3 ltac:(vm_compute; reflexivity) Haddi). }
intros md3 Hsm3.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc3 : v_addi (Z_to_bv 64 (BASE + (LO_K + 8))) 4 = Z_to_bv 64 (BASE + (LO_K + 12))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold LO_K; lia). f_equal. lia. }
rewrite Epc3.
set (regsC := regupd regsB 10%bv (w64 (x_sp1 cx + LT_W))).
(* step 4: jal check_reply *)
eapply (SRr_step SEGS pa_wx W _ _ md3); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (lt_step_pcall_loc (LO_K + 12) CS_check_reply (1%bv : Prelude.reg) regsC
  (mrestrict (w_H W) mem) (seg_rom SEGS) Hpl4 ltac:(vm_compute; reflexivity) ltac:(unfold LO_K; lia)). }
intros md4 Hsm4.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
replace (LO_K + 12 + 4) with LO_K1 by (vm_compute; reflexivity).
set (regsc := regupd regsC 1%bv (Z_to_bv 64 (BASE + LO_K1))).
rewrite (SIGP CS_check_reply ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_reply) with AF_check_reply by (vm_compute; reflexivity).
(* ---- the registers at the call ---- *)
assert (Q1 : getr regsc 1%bv = Z_to_bv 64 (BASE + LO_K1)) by (unfold regsc; lt_getr_loc; reflexivity).
assert (Q2 : getr regsc 2%bv = getr regs 2%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q3 : getr regsc 3%bv = getr regs 3%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q4 : getr regsc 4%bv = getr regs 4%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q8 : getr regsc 8%bv = getr regs 8%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q9 : getr regsc 9%bv = getr regs 9%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q10 : getr regsc 10%bv = w64 (x_sp1 cx + LT_W)) by (unfold regsc, regsC; lt_getr_loc; reflexivity).
assert (Q18 : getr regsc 18%bv = getr regs 18%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q21 : getr regsc 21%bv = getr regs 21%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q23 : getr regsc 23%bv = w64 (x_p cx + (x_n cx - lt_r' (x_pl cx) (x_n cx) r)))
  by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q24 : getr regsc 24%bv = w64 (lt_r' (x_pl cx) (x_n cx) r))
  by (unfold regsc, regsC, regsB; lt_getr_loc; reflexivity).
assert (Q25 : getr regsc 25%bv = getr regs 25%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q26 : getr regsc 26%bv = getr regs 26%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Q27 : getr regsc 27%bv = getr regs 27%bv) by (unfold regsc, regsC, regsB, regsA; lt_getr_loc; reflexivity).
assert (Qsp : spZ regsc = x_sp1 cx) by (unfold spZ; rewrite Q2; exact Rsp).
clearbody regsc regsC regsB regsA.
(* ---- the journal at the call (the four steps write nothing) ---- *)
assert (HJ4 : ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) []
  ly S W mem md4 k).
{ rewrite (same_but_materialized_wvb md3 md4 Hsm4), (same_but_materialized_wvb md2 md3 Hsm3),
    (same_but_materialized_wvb md1 md2 Hsm2), (same_but_materialized_wvb md md1 Hsm1).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
(* ---- the cut's facts at the call state (the K1 cut's registers: s7, s8 set, s5 and the frame kept) ---- *)
assert (HBODYc : lt_body B cx ly S W regsc mem md4 k m).
{ split; [|split; [exact HSLOTS|]].
  - split; [exact HJ4|]. split; [exact Qsp|]. split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|].
    exact HSAVED.
  - split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|]. split; [rewrite Q18; exact R18|].
    split; [rewrite Q25; exact R25|]. split; [rewrite Q26; exact R26|]. split; [rewrite Q27; exact R27|].
    exact Hm32. }
assert (HKRc : lt_kregs cx regsc (rdW W mem) r Rh).
{ split; [exact Hr0|]. split; [exact Q23|]. split; [exact Q24|]. split; [rewrite Q21; exact R21|].
  split; [exact Rst|]. split; [exact Rho | exact HHOST]. }
(* ---- check_reply's premises at the call state ---- *)
assert (P3 : Z.of_nat (length (frames S)) <= 7).
{ rewrite Hfrs, HFRS0. cbn [app length]. lia. }
assert (P4 : arodata_okP SEGS RLO RHI B (rdW W mem)).
{ apply (arodata_ok_journalP SEGS RLO RHI (cif_relro_img _ _ IMG) (RO := cif_ro_below_ofl _ _ IMG) B LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md4 k HJ4); [|exact HROD0].
  intros a Hro Hf. exact (cif_prog_not_ro _ _ IMG a Hf Hro). }
assert (P5 : cmd_ro_ok (rdW W mem))
  by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem md HAR P4).
assert (P8 : 0 <= x_sp1 cx + LT_W < 2 ^ 64) by (unfold LT_W; lia).
(* the reply: its block, its pointer and the bytes after its terminator *)
pose proof HRREP as HREPA.
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
assert (P29 : st_nev S + EV_CHECK_REPLY <= EV_MAX).
{ pose proof (lt_nev_now B MT cx ly S W mem md k acc _ HBASE HJ HBUD) as H1. unfold EV_CHECK_REPLY. lia. }
(* ---- the call's own premises (PaFx.v's cl_callSF): the frame chain at s0 = -1 is achain's empty case (the value
   is not 8-aligned) ---- *)
assert (Hsp' : spZ regsc = x_sp0 cx + -256) by (rewrite Qsp; unfold x_sp1, x_sp0, LT_FRAME; lia).
assert (Hgp' : getr regsc 3 = w64 (as_gp B)) by (rewrite Q3, Rgp; exact Hgp).
assert (Htp' : getr regsc 4 = w64 (as_tp B)) by (rewrite Q4, Rtp; exact Htp).
assert (Hraw : YK0s.ret_ok (getr regsc 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [unfold LO_K1; lia | reflexivity]).
assert (Hra4c : 4096 <= bv_unsigned (getr regsc 1)).
{ rewrite Q1, unsigned_lit_small by (unfold LO_K1; lia). unfold LO_K1. lia. }
assert (Hs0 : s0Z regsc mod 8 <> 0).
{ unfold s0Z. rewrite Q8, R8. vm_compute. intros Hx. discriminate Hx. }
assert (Hch : achain ly (rdW W mem) (x_sp0 cx + -256) (s0Z regsc) []).
{ left. split; [right; right; exact Hs0 | reflexivity]. }
pose proof (fun HPRE1 : afn_pre SEGS B CHECK_REPLY_STK ly S W regsc mem md4 [] =>
  HCHECK_REPLY fx ly S W regsc mem md4 [] (x_sp1 cx + LT_W) arr (nth 0 wp 0)
    (Z.of_nat (length (lt_ws (x_pl cx) (x_n cx) r))) (fst pnr) ans xr
    (nth 0 (lt_ws (x_pl cx) (x_n cx) r) []) R1 O1 HPRE1 HFRM P3 P4 P5 HVOBJ Q10 P8 HREPA HNR HRPL HNO0
    P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 P28 P29) as HCALL.
lazymatch type of HCALL with _ -> SRr _ _ _ (apost_baseF _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (K := Kq) in HCALL end.
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callSF B LAWS W regsc mem (Z_to_bv 64 (BASE + AF_check_reply)) LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md4 k CHECK_REPLY_STK [] EV_CHECK_REPLY
    (-256) (getr regsc 1) [] K HJ4 Hsp' eq_refl ltac:(lia) ltac:(rewrite ECRSTK; lia)
    ltac:(rewrite ECRSTK, ESTK; lia) Hgp' Htp' eq_refl Hraw Hra4c Hch).
  - intros HPRE1. eapply SRr_mono; [exact (HCALL HPRE1) | intros W3 c3 _ H3; exact H3].
  - intros a Hf. exfalso. exact (inFP_nil a Hf). }
(* ---- LT_K1_stmt at the return point 0x86a14, at check_reply's FP state fx1 ---- *)
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 mdr _ Hfx (HJ2 & HJc & HP2 & HK2).
unfold K in HK2. cbv beta in HK2. destruct HK2 as (HPerm2 & Ely2 & (fsf & ES2)). subst ly2 S2.
pose proof (lt_call_kept B HB LAWS IMG cx CHECK_REPLY_STK ly S W mem md4 ly (set_fs fsf S) W2 mem2 mdr EV_CHECK_REPLY
  HJc ltac:(lia) ltac:(unfold x_sp0; lia) HPerm2) as KEEP.
destruct (lt_kcut_keep B cx ly S W regsc mem md4 k ly (set_fs fsf S) W2 regs2 mem2 mdr (k + EV_CHECK_REPLY) m r Rh R1 O1
  (if quit then 1 else 0) text copy arr wp HBODYc HKRc HWORDS HREC HJ2 HP2 HPerm2 KEEP)
  as (HBODY2 & HKR2 & HW2 & HREC2).
pose proof (fxrel_frm0 fx fx1 HFRM Hfx) as HFRM1.
pose proof (K1 fx1 cx ly (set_fs fsf S) W2 regs2 mem2 mdr (k + EV_CHECK_REPLY) acc r Rh O1 text copy arr wp
  HBASE HFRM1 HBODY2 HKR2) as K1'.
cbv zeta in K1'. rewrite EVR in K1'. cbv beta iota in K1'.
rewrite Q1.
refine (K1' HW2 HREC2 _).
apply (lt_bud_eq MT cx (set_fs fsf S) k acc _ _ _ (lt_bud_set_fs_loc cx S k acc _ fsf HBUD));
  unfold EV_CHECK_REPLY; ring.
Qed.

End e.
End f.
End d.
