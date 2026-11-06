(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the check_arity step of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86948 addi a0,sp,120 and 0x8694c jal check_arity, to the return point 0x86950): from the cut after check_reply to the cut after check_arity (lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v), through check_arity's statement, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (cl_FC_okX: a symbolic run to a program call, the callee's contract, the next cut statement at the return point) and A/ACh2.v:122-290 (a program call through cl_callS and back), with lib/A/Prog/check_refusal.v's call step. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_Karity.v, with its module paths and module names changed; 388 of its 424 lines of code are new or changed and 217 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry
   BASE + AF_sup_remove = 0x8b258), segment G2: record's return 0x8b354 (SR_R) .. the snprintf wrapper's return
   0x8b378 (SR_S), at the FP state the wrapper returns at. The statement is sup_remove_s1.v's sr_g2_stmt; the rest of
   the walk is sr_g3_stmt (sup_remove_g3.v), taken here at that FP state (G3).

   - 0x8b354 .. 0x8b374: s5 := a0 (record's slot), b's shadow bytes (frame shadow 4 and 5) := 00, a2 := 0x21f40 ("%d",
     A_OBJ 51), a1 := 16, a0 := s4 = b = F + 32, a3 := s3 = id, `jal wrapper_snprintf`. A fresh symbolic state is
     seated at 0x8b354 from sr_cut: the registers are their own atoms, and the only region is the frame's shadow
     bytes 4 and 5 at s6 = SB + F / 8 (atom 22), a write window with no chunks (the token executor refuses a writable
     region in the shadow band, so the run uses the plain run lemmas).
   - 0x8b374: snprintf(b, 16, "%d", id) through the shared contract (RtPFCmd.asnprintf_sh at FR_cmd,
     the printf call step): the destination is in this call's own side-stack frame (aj_art_own_atF), the text is
     pf_dec id (the decimal of id, at most 12 bytes), so the wrapper writes it and its terminator into b. The
     contract's band premise `amem_range d (sn_len (n - 1) T + 8)` holds because b + 13 + 8 <= F + 64 lies in the
     64-byte class-0 frame (PaLibH.amem_range_sub_app).
   - 0x8b378: sr_cut at the wrapper's return (the journal, the flag word, the saves and the shadow bytes 4 and 5 are
     outside the destination and the wrapper's window), record's post (sr_recd) over the new memory (the recorder's
     bytes are outside the run's window, the destination and the wrapper's window), s5 = record's slot and b holding
     dec id (HarnessPropsProof.dec_pf). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaArt PaArtOwn PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require HarnessPropsProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns sup_remove_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the decimal text of id ---- *)
(* every byte of pf_dec is '-' (45) or a digit (48 .. 57) *)
Lemma sr_g2_digits_rng : forall f x acc, 0 <= x -> Forall (fun c => 45 <= c < 58) acc ->
  Forall (fun c => 45 <= c < 58) (PF.pf_digits f x acc).
Proof.
induction f as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (Z.ltb_spec x 10) as [Hl|Hl].
- constructor; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia|]. constructor; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Hacc].
Qed.
Lemma sr_g2_dec_rng : forall v, Forall (fun c => 45 <= c < 58) (PF.pf_dec v).
Proof.
intros v. unfold PF.pf_dec. destruct (Z.ltb_spec v 0) as [Hv|Hv].
- constructor; [lia|]. apply sr_g2_digits_rng; [lia | constructor].
- apply sr_g2_digits_rng; [lia | constructor].
Qed.
Lemma sr_g2_digits_len : forall f x acc, (length (PF.pf_digits f x acc) <= f + length acc)%nat.
Proof.
induction f as [|f IH]; intros x acc; cbn [PF.pf_digits]; [lia|].
destruct (x <? 10); cbn [length]; [lia|].
pose proof (IH (x / 10) ((48 + x mod 10) :: acc)) as H. cbn [length] in H. lia.
Qed.
Lemma sr_g2_dec_len : forall v, (length (PF.pf_dec v) <= 12)%nat.
Proof.
intros v. unfold PF.pf_dec. destruct (v <? 0); cbn [length].
- pose proof (sr_g2_digits_len 11 (- v) []) as H. cbn [length] in H. lia.
- pose proof (sr_g2_digits_len 11 v []) as H. cbn [length] in H. lia.
Qed.
(* no byte of the text is the terminator *)
Lemma sr_g2_no0 : forall T, Forall (fun c => 45 <= c < 58) T -> ~ In (Z_to_bv 8 0) (PF.pf_bytes T).
Proof.
intros T HT Hin. unfold PF.pf_bytes in Hin. apply in_map_iff in Hin as (c & Hc & Hct).
pose proof (proj1 (Forall_forall _ _) HT c Hct) as Hr. cbv beta in Hr.
apply (f_equal bv_unsigned) in Hc. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod in Hc. change (2 ^ 8) with 256 in Hc.
rewrite (Z.mod_small c 256) in Hc by lia. change (0 mod 256) with 0 in Hc. lia.
Qed.
Lemma sr_g2_lit_mod32 : forall z, bv_unsigned (Z_to_bv 64 z) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
Z.div_mod_to_equations. lia.
Qed.
(* the bytes the snprintf wrapper leaves at d (the shared post's sn_bytes, a list of Z) as the byte list of the
   string (B sup_resp's sr_buf_strZ) *)
Lemma sr_g2_buf_strZ : forall (rd : reader) d (T : list Z), Forall (fun c => 0 <= c < 256) T ->
  (forall i, 0 <= i < Z.of_nat (length T) + 1 -> rd (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
  abytes_atR rd d (PF.pf_bytes T ++ [Z_to_bv 8 0]).
Proof.
intros rd d T HT H i Hi. unfold PF.pf_bytes in *. rewrite length_app, length_map in Hi. cbn [length] in Hi.
rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. f_equal.
destruct (Nat.lt_ge_cases i (length T)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. rewrite app_nth1 by (rewrite length_map; exact Hl).
  rewrite map_nth. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
  pose proof (proj1 (Forall_forall _ T) HT (nth i T 0) (nth_In T 0 Hl)) as Hr. cbv beta in Hr.
  rewrite Z.mod_small by lia. reflexivity.
- assert (i = length T) as -> by lia.
  rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity.
Qed.
(* a literal of the image as the format's Z bytes *)
Lemma sr_g2_lit_bytes : forall (rd : reader) f (l : list Z), Forall (fun c => 0 <= c < 256) l ->
  abytes_atR rd f (map (Z_to_bv 8) l) -> forall i, 0 <= i < Z.of_nat (length l) -> rd (f + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros rd f l Hl H i Hi. pose proof (H (Z.to_nat i) ltac:(rewrite length_map; lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. rewrite Hb. f_equal. rewrite map_nth. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
assert (Hn : (Z.to_nat i < length l)%nat) by lia.
pose proof (proj1 (Forall_forall _ l) Hl (nth (Z.to_nat i) l 0) (nth_In l 0 Hn)) as Hr. cbv beta in Hr.
apply Z.mod_small. lia.
Qed.
(* the destination is in this call's side-stack frame, and the frame is off the image *)
Lemma sr_g2_img_eb : forall F a, off_img F 64 -> 0x10000 <= a < 0x606000 -> ~ (F + 32 <= a < F + 64).
Proof. intros F a HO Ha Hb. unfold off_img in HO. lia. Qed.

(* ---- the symbolic state at 0x8b354: the registers are their own atoms; one region, the frame's shadow bytes 4
   and 5 at s6 (atom 22), a write window with no chunks ---- *)
Definition sr_g2_region : YP09.region := YP09.mkRegion (Some 22%nat) 4 6 4 6 [].
Definition ss_sr_g2 : sstate := mkSS (AF_sup_remove + SR_R) sr_atoms [sr_g2_region] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the frame's bytes are not its shadow bytes 4 and 5 (the frame is app memory, its shadow is not) *)
Lemma sr_g2_frame_win : forall F a, in_app F 64 -> F = 8 * (F / 8) -> F <= a < F + 64 ->
  ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6).
Proof.
intros F a Happ HF Ha Hw. unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
destruct Happ as (H4096 & [H1 | (H2 & _)]); lia.
Qed.
(* nor is a byte of a live block *)
Lemma sr_g2_blk_win : forall p n F a, in_app p n -> 0 <= F / 8 <= 2 ^ 44 - 6 -> p <= a < p + n ->
  ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6).
Proof.
intros p n F a Happ HF Ha Hw. unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *.
destruct Happ as (H4096 & [H1 | (H2 & _)]); lia.
Qed.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a byte outside a run's write windows keeps its view (B sup_resp's sr_frame_kept) *)
Lemma sr_g2_frame_kept : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' a Hf Ha Hw. apply aview_eq_of. apply Hf. rewrite unsigned_lit_small by lia. exact Hw. Qed.
(* the seat at 0x8b354 *)
Lemma sr_g2_seat : forall (Wc : world SEGS) (regsc : bvmap 5 word) memc F,
  getr regsc 22 = w64 (SB + F / 8) -> 512 <= F / 8 <= 2 ^ 44 - 6 ->
  (forall i, 4 <= i < 6 -> apresent (w_H Wc) memc (SB + F / 8 + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) ss_sr_g2
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_R))) memc (seg_rom SEGS))).
Proof.
intros Wc regsc memc F H22 HF Hp.
rewrite restrict_mkst_fx. unfold ss_sr_g2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, sr_g2_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (ew_Eimg_Ereg_nat regsc [] 22 22%bv eq_refl), H22. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
  split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply Hp. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [exact I | split; exact I].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_remove_c.v:92-93), word for word *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
(* the rest of the walk, at the FP state the wrapper returns at *)
Hypothesis G3 : forall fx0 : YK11.FPState, @sr_g3_stmt fx0 rc SK PI B MT.
Let RUNP := SRr_run_pi_AJ (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.

Lemma sr_g2_rep_live : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.

Theorem sr_g2 : sr_g2_stmt B MT.
Proof.
unfold sr_g2_stmt.
intros ly S W regs mem md ch id R O lyc Sc Wc regsc memc mdc pos Fr O1 HPRE HFRM HCUT HRECD H10c.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HCK : CMD_SNP_K = 8192) by reflexivity.
assert (FFS : SUP_REMOVE_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_STK in exact v)) by reflexivity.
pose proof HPRE as (HAFN & Hfr7 & HROD & HRO & H10 & Hid & HREP & Hev & Hlive & MOK).
pose proof HAFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCUT as (HJ & Hflag & Hsp1 & R8 & R9 & R18 & R19 & R20 & R22 & R23 & R24 & R3 & R4 & R25 & R26 & R27 & HSV).
pose proof HRECD as (RP & RL & RF & RREP & RO1 & RBB & RMLE).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HARc Hfin) as (_ & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HARc Hfin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 pos HARc Hfin) as (HF64 & _ & _).
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 0 pos HARc Hfin) as HOI.
change (fs_frame_bytes 0 / 8) with 8 in HFSpres.
change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFceil, HOI.
set (F := frame_addr lyc 0 pos) in *.
assert (HF8m : F mod 8 = 0) by (clear - HF64; Z.div_mod_to_equations; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. rewrite HF8m, Z.add_0_r in HF8.
assert (HF8b : 512 <= F / 8 <= 2 ^ 44 - 6) by lia.
assert (HF8b' : 0 <= F / 8 <= 2 ^ 44 - 6) by lia.
(* the realigned stack pointer sp1 = 32 * ((sp0 - 96) / 32), 96 .. 112 below the entry sp *)
set (sp1 := sr_sp1 (spZ regs)) in *.
assert (Hsp1v : sp1 = 32 * ((spZ regs - 96) / 32)) by reflexivity.
pose proof (Z.div_mod (spZ regs - 96) 32 ltac:(lia)) as Hq1.
pose proof (Z.mod_pos_bound (spZ regs - 96) 32 ltac:(lia)) as Hq2.
pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Hk1. rewrite Hal16, Z.add_0_r in Hk1.
assert (Hsp1r : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia.
assert (Hal1 : (sp1 - spZ regs) mod 16 = 0).
{ replace (sp1 - spZ regs) with ((2 * ((spZ regs - 96) / 32) - spZ regs / 16) * 16) by lia. apply Z_mod_mult. }
clear Hsp1v Hq1 Hq2 Hk1.
(* where the wrapper's window [sp1 - 8192, sp1) lies: above alloc_ceiling, so above the frame, its shadow and the
   heap *)
assert (HW0 : alloc_ceiling <= sp1 - 8192) by lia.
assert (HW1 : F + 64 <= sp1 - 8192) by lia.
assert (HW2 : 0x606000 <= sp1 - 8192) by lia.
assert (HW3 : sp1 + 8 <= 2 ^ 47) by lia.
assert (HW4 : SB + F / 8 + 6 <= sp1 - 8192) by (unfold SB; lia).
(* ---- the seat at 0x8b354 ---- *)
assert (HSHp : forall i, 4 <= i < 6 -> apresent (w_H Wc) memc (SB + F / 8 + i)).
{ intros i Hi. pose proof (proj1 (HFSpres i ltac:(lia))) as Hp. unfold shadow_addr in Hp. rewrite <- SB_SHADOW_OFF in Hp. exact Hp. }
pose proof (sr_g2_seat Wc regsc memc F R22 HF8b HSHp) as HS.
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (U22 : bv_unsigned (ew E 22) = SB + F / 8)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; unfold SB; lia).
(* 0x8b354 .. 0x8b374: s5 := a0, b's shadow := 00 00, the snprintf arguments, `jal wrapper_snprintf` *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Hr). unfold ss_sr_g2, sr_g2_region in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U22 in Hr.
  right; right; right; left. exists 0, pos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- SB_SHADOW_OFF. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
pmkst HS. collapse_md.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ => rename msX into ms1 end.
rename HJ into HJ1.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
assert (HspT : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs)).
{ unfold spZ at 1. rewrite P2, (EE 2%nat 2%bv eq_refl). change (bv_unsigned (getr regsc 2)) with (spZ regsc). rewrite Hsp1. lia. }
assert (P3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (P10' : getr (ms_regs ms1) 10 = w64 (F + 32)) by (rewrite P10, (EE 20%nat 20%bv eq_refl); exact R20).
assert (P13' : getr (ms_regs ms1) 13 = w64 id) by (rewrite P13, (EE 19%nat 19%bv eq_refl), R19; exact H10).
assert (P21' : getr (ms_regs ms1) 21 = w64 (rec_slot R)) by (rewrite P21, (EE 10%nat 10%bv eq_refl); exact H10c).
assert (P12' : getr (ms_regs ms1) 12 = w64 0x21f40).
{ rewrite P12. lazymatch goal with |- ew _ ?n = _ =>
    pose proof (HEI n ltac:(unfold A_TEXT, A_LIM; lia)) as Hn;
    change (VAL n) with (VAL (A_OBJ 51)) in Hn end.
  rewrite (VOBJS 51%nat ltac:(vm_compute; lia)) in Hn.
  apply bv_eq. rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (P1' : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (AF_sup_remove + SR_S))) by (rewrite P1; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1))
  by (rewrite P1'; apply ret_ok_codeptr_v; [unfold AF_sup_remove, SR_S; lia | reflexivity]).
(* the run wrote only b's shadow bytes 4 and 5, both 00 *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hn. apply (sr_g2_frame_kept E (ss_mem ss_sr_g2) (w_H Wc) memc (ms_mem ms1) a HFr Ha).
  intros (r & Hin & Hr). unfold ss_sr_g2, sr_g2_region in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U22 in Hr. lia. }
assert (ZB : forall i, 4 <= i < 6 -> rdW Wc (ms_mem ms1) (SB + F / 8 + i) = Some 0).
{ lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx 0 _ HS eq_refl) as HR end.
  cbn [ms_mem restrict] in HR.
  intros i Hi. assert (Hc : i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | ->]; (apply aview_of_val_mem1; [|lia]);
  (eapply field_of_region with (w := 1%N) (e := SLit 0) (v := 0); [exact HR | exact U22 | cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]). }
(* the state at the call: the record's view, the read-only bytes (cmd_ro_ok again, from arodata_okP), the frame *)
pose proof (proj1 HJ1) as HAR1.
assert (HOlive : Forall (fun pn => In pn (ablocks B ly S)) O)
  by (apply Forall_forall; intros pn Hp; exact (sr_g2_rep_live ly S _ R O pn HREP Hp)).
pose proof (sr_aro_journal B HB LAWS IMG SUP_REMOVE_STK (spZ regs) O ly S W mem md [(0, pos)] lyc Sc Wc (ms_mem ms1) mdv
  (EV_RECORD R) HAR0 HOlive HJ1 HROD) as HROD1.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HAR1 HROD1) as HRO1.
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HAR1) as (_ & HGUARD & _).
destruct HGUARD as [HG1 [cval HG2]].
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR1 Hfin) as (_ & _ & HFpres1 & _).
change (fs_frame_bytes 0) with 64 in HFpres1. fold F in HFpres1.
assert (HLIT : abytes_atR (rdW Wc (ms_mem ms1)) 0x21f40 RO_lit_21f40).
{ clear - HRO1. destruct HRO1 as [HRO1 _]. unfold cmd_ro_bytes in HRO1.
  repeat match type of HRO1 with
  | abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 HRO1)
  | _ /\ _ => apply proj2 in HRO1
  end. }
change RO_lit_21f40 with (map (Z_to_bv 8) ([37; 100] ++ [0])) in HLIT.
pose proof (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [(0, pos)] lyc Sc Wc
  (ms_mem ms1) mdv (EV_RECORD R) (ms_regs ms1) (sp1 - spZ regs) HJ1 HspT Hal1 ltac:(lia) ltac:(rewrite HCK; lia)
  ltac:(rewrite HCK, FFS; lia) HraT P3' P4') as (HPS1 & HPS2 & HPS3).
(* the text the wrapper writes: T = pf_dec id (at most 12 bytes), then its terminator *)
set (T := PF.pf_dec id).
assert (HLT : (length T <= 12)%nat) by exact (sr_g2_dec_len id).
assert (HTD : Forall (fun c => 45 <= c < 58) T) by exact (sr_g2_dec_rng id).
assert (HTR : Forall (fun c => 0 <= c < 256) T) by (eapply Forall_impl; [|exact HTD]; intros c Hc; cbv beta in Hc |- *; lia).
assert (HSNW : sn_len (16 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. rewrite length_app. cbn [length]. lia. }
assert (HSNB : sn_bytes (16 - 1) T = T ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia. reflexivity. }
(* 0x8b374: snprintf(b, 16, "%d", id) (RtPFCmd.v's asnprintf_sh at FR_cmd), returning at some FP state fx1 *)
eapply (srr_after_artF (fx := fx) SEGS Wc _ (getr (ms_regs ms1) 1)).
{ eapply (aj_art_own_atF (fx := fx) SEGS B LAWS Hsegs CMD_SNP_K (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) T)
    (SIG CS___interceptor_trampoline_snprintf) Wc (ms_regs ms1) (ms_mem ms1) SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md
    [(0, pos)] lyc Sc mdv (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms1) 1) _ HJ1 HspT Hal1 ltac:(lia)
    ltac:(rewrite HCK; lia) ltac:(rewrite HCK, FFS; lia) eq_refl).
  { intros a Ha. right; right; right; left. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. cbv beta in Ha. rewrite HSNW in Ha. lia. }
  apply (srr_art_postF_of_pf (fx := fx) SEGS B CMD_SNP_K lyc Sc Wc (ms_regs ms1) (ms_mem ms1) _ _ (F + 32)
    (sn_len (16 - 1) T) (sn_bytes (16 - 1) T) (Z.of_nat (length T))).
  { intros a Ha. apply HPS3. unfold ascratch_stk. exact Ha. }
  apply (ASNPRINTF fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) _ (F + 32) 16 0x21f40 []
    (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) T cval).
  - exact HPS1.
  - exact HPS2.
  - intros a Ha. apply HPS3. unfold ascratch_stk. exact Ha.
  - exact P10'.
  - exact P11.
  - exact P12'.
  - exact (cmd_consts_view_snp SEGS B LAWS HB IMG RLO RHI Wc (ms_mem ms1) HROD1).
  - unfold CMD_SNP_CR. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
  - rewrite HSNW, HCK, HspT. unfold CMD_SNP_CR, snp_out. clear - HOI HW1 HW2 HLT. unfold off_img in HOI.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - exact HG1.
  - exact HG2.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. clear - HOI HW1 HW2 HLT. unfold off_img in HOI.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. clear - HOI HW1 HW2 HLT. unfold off_img in HOI.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - split; [reflexivity | intros i Hi; cbn in Hi; lia].
  - cbn [length]. rewrite HspT. lia.
  - rewrite HSNW, HCK, HspT. cbn [length]. unfold snp_out. clear - HW1 HLT.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - apply (FR_cmd_intro _ _ _ _ _ [37; 100] [PF.Pd] [PF.AInt id]).
    + split; [lia|]. split.
      { intros i Hi. apply (sr_g2_lit_bytes _ _ ([37; 100] ++ [0]));
          [repeat apply Forall_cons; try apply Forall_nil; lia | exact HLIT | cbn in Hi |- *; lia]. }
      change (Z.of_nat (length [37; 100]) + 1) with 3.
      split.
      { rewrite HSNW, HCK, HspT. unfold snp_out. clear - HOI HW1 HW2 HLT. unfold off_img in HOI.
        repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia. }
      split; [unfold amem_range; left; unfold kLowMemEnd; lia|].
      split; [exact (cmd_addressable_chk SEGS B LAWS HB _ _ Wc _ _ 0x21f40 3 HAR1 ltac:(vm_compute; reflexivity))
             | exact (cmd_hull_vis_chk SEGS B LAWS HB _ _ Wc _ _ 0x21f40 3 HAR1 ltac:(vm_compute; reflexivity))].
    + reflexivity.
    + cbn [map arg_of pf_args_asan app]. split; [|exact I]. cbn [pf_arg_asan]. split; [exact Hid|].
      unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite P13'. unfold w64. apply sr_g2_lit_mod32.
    + change (PF.pf_text [PF.Pd] [PF.AInt id]) with (Some (PF.pf_dec id ++ [])). rewrite app_nil_r. reflexivity.
    + exact I.
    + (* fr_lit_ok: "%d" at 0x21f40 is a nonempty image literal below the GOT word, and no string argument *)
      vm_compute. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite HSNW. lia.
  - rewrite HSNW, HCK, HspT. unfold snp_out. cbn [pairwise].
    split; [|split; [apply Forall_nil | exact I]].
    clear - HW1 HLT. repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - rewrite HSNW. intros a Ha. destruct (HFpres1 a ltac:(lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite HspT. lia.
  - (* the band premise of the `+ 8` contract: b and 8 bytes past the text's end lie in the 64-byte class-0 frame
       (32 + 13 + 8 <= 64), which is application memory below the allocation ceiling *)
    rewrite HSNW. apply (amem_range_sub_app F 64 (F + 32) (Z.of_nat (length T) + 1 + 8) HFapp); lia.
  - rewrite HSNW. intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
    assert (Hi : 4 <= x / 8 - F / 8 < 6) by (clear - Hx HF8 HLT; Z.div_mod_to_equations; lia).
    replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia. apply ZB. exact Hi.
  - rewrite HSNW. exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms1) _ 0 pos (F + 32) (Z.of_nat (length T) + 1)
      HAR1 Hfin ltac:(fold F; lia) ltac:(change (fs_frame_bytes 0) with 64; fold F; lia) ltac:(lia)).
  - rewrite HSNW. unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. clear - HOI HLT. unfold off_img in HOI. lia.
  - exact HFRM. }
cbv beta. intros fx1 regs3 mem3 md3 Hfx (HJ3 & HP3 & (HQa & HQb) & HK3).
rewrite HSNW in HQb, HK3. rewrite HSNB in HQb. rewrite HCK in HK3.
(* back at 0x8b378: the wrapper wrote only b [F + 32, F + 32 + |T| + 1) and its window below sp1 *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> ~ (sp1 - 8192 <= a < sp1) ->
  ~ (F + 32 <= a < F + 32 + (Z.of_nat (length T) + 1)) -> rdW Wc mem3 a = rdW Wc memc a).
{ intros a Ha H1 H2 H3. transitivity (rdW Wc (ms_mem ms1) a); [apply HK3; [exact Ha | clear - H2; lia | exact H3] | exact (KR a Ha H1)]. }
assert (KW : forall a v, spZ regs - 80 <= a -> a + 8 <= spZ regs -> rdword (rdW Wc memc) a = Some v -> rdword (rdW Wc mem3) a = Some v).
{ intros a v H1 H2 Hv. rewrite (YCbq.rdword_ext (rdW Wc memc) (rdW Wc mem3) a); [exact Hv|].
  intros k Hk. apply KEEP; lia. }
assert (KS : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> acallee_saved (Z.of_nat n) ->
  getr (ms_regs ms1) r = ew E n -> getr regs3 r = getr regsc r).
{ intros n r Hn Hc Hm. rewrite <- (EE n r Hn), <- Hm. rewrite Hn in Hc.
  pose proof (HP3 (bv_unsigned r) Hc) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
(* b's shadow bytes are still 00 *)
assert (HZ3 : forall i, 4 <= i < 6 -> rdW Wc mem3 (SB + F / 8 + i) = Some 0).
{ intros i Hi. transitivity (rdW Wc (ms_mem ms1) (SB + F / 8 + i)); [|exact (ZB i Hi)].
  apply HK3.
  - unfold SB; lia.
  - clear - Hi HW4. lia.
  - intros Hb. cbv beta in Hb. exact (sr_g2_frame_win F (SB + F / 8 + i) HFapp HF8 ltac:(lia) ltac:(lia)). }
(* b holds the decimal text of id *)
assert (HSTR : astr_atR (rdW Wc mem3) (F + 32) (dec id)).
{ rewrite <- (HarnessPropsProof.dec_pf id Hid). split.
  - apply sr_g2_buf_strZ; [exact HTR|]. intros i Hi. exact (HQb i Hi).
  - exact (sr_g2_no0 T HTD). }
assert (H21 : getr regs3 21 = w64 (rec_slot R))
  by (transitivity (getr (ms_regs ms1) 21); [exact (HP3 21 ltac:(unfold acallee_saved; lia)) | exact P21']).
(* the rest of the walk (sr_g3_stmt) at fx1, from the cut at 0x8b378 *)
rewrite P1'.
apply (G3 fx1 ly S W regs mem md ch id R O lyc Sc Wc regs3 mem3 md3 pos Fr O1 HPRE (fxrel_frm0 fx fx1 HFRM Hfx)).
(* sr_cut at 0x8b378 *)
{ unfold sr_cut. fold F. fold sp1.
  repeat match goal with |- _ /\ _ => split end.
  - exact HJ3.
  - transitivity (rdword (rdW Wc memc) (F + 56)); [|exact Hflag].
    apply YCbq.rdword_ext. intros k Hk. apply KEEP.
    + lia.
    + intros Hw. exact (sr_g2_frame_win F (F + 56 + k) HFapp HF8 ltac:(lia) Hw).
    + lia.
    + lia.
  - unfold spZ at 1. transitivity (bv_unsigned (getr (ms_regs ms1) 2)).
    + f_equal. exact (HP3 2 ltac:(unfold acallee_saved; lia)).
    + change (bv_unsigned (getr (ms_regs ms1) 2)) with (spZ (ms_regs ms1)). rewrite HspT. lia.
  - exact (eq_trans (KS 8%nat 8%bv eq_refl ltac:(unfold acallee_saved; lia) P8) R8).
  - exact (eq_trans (KS 9%nat 9%bv eq_refl ltac:(unfold acallee_saved; lia) P9) R9).
  - exact (eq_trans (KS 18%nat 18%bv eq_refl ltac:(unfold acallee_saved; lia) P18) R18).
  - exact (eq_trans (KS 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia) P19) R19).
  - exact (eq_trans (KS 20%nat 20%bv eq_refl ltac:(unfold acallee_saved; lia) P20) R20).
  - exact (eq_trans (KS 22%nat 22%bv eq_refl ltac:(unfold acallee_saved; lia) P22) R22).
  - exact (eq_trans (KS 23%nat 23%bv eq_refl ltac:(unfold acallee_saved; lia) P23) R23).
  - exact (eq_trans (KS 24%nat 24%bv eq_refl ltac:(unfold acallee_saved; lia) P24) R24).
  - exact (eq_trans (KS 3%nat 3%bv eq_refl ltac:(unfold acallee_saved; lia) P3) R3).
  - exact (eq_trans (KS 4%nat 4%bv eq_refl ltac:(unfold acallee_saved; lia) P4) R4).
  - exact (eq_trans (KS 25%nat 25%bv eq_refl ltac:(unfold acallee_saved; lia) P25) R25).
  - exact (eq_trans (KS 26%nat 26%bv eq_refl ltac:(unfold acallee_saved; lia) P26) R26).
  - exact (eq_trans (KS 27%nat 27%bv eq_refl ltac:(unfold acallee_saved; lia) P27) R27).
  - unfold sr_saves. destruct HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
    repeat match goal with |- _ /\ _ => split end; (apply KW; [lia | lia | assumption]). }
(* record's post over the new memory: g_rec, record.spill and the recorder's blocks are kept *)
{ refine (conj RP (conj RL (conj RF (conj _ (conj RO1 (conj RBB RMLE)))))).
  apply (PaCallPg.rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc mem3) _ O1 RREP).
  - intros pn Hpn. exact (sr_g2_rep_live lyc Sc _ _ O1 pn RREP Hpn).
  - intros a [Ha | [Ha | Ha]].
    + unfold A_G_REC, REC_SIZE in Ha. apply KEEP; [lia | unfold SB; lia | lia |].
      intros Hb. exact (sr_g2_img_eb F a HOI ltac:(lia) ltac:(lia)).
    + unfold A_REC_SPILL, SC_SIZE in Ha. apply KEEP; [lia | unfold SB; lia | lia |].
      intros Hb. exact (sr_g2_img_eb F a HOI ltac:(lia) ltac:(lia)).
    + destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & n & Hin & Hr).
      pose proof (sr_g2_rep_live lyc Sc _ _ O1 (p, n) RREP Hin) as Hlv.
      destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HARc Hlv) as (_ & H4096 & Hbc & Happ & _).
      pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 0 pos HARc Hlv Hfin) as Hd.
      change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
      apply KEEP.
      * lia.
      * exact (sr_g2_blk_win p (req_size n) F a Happ HF8b' Hr).
      * lia.
      * clear - Hd Hr HLT. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
{ exact H21. }
{ exact (HZ3 4 ltac:(lia)). }
{ exact (HZ3 5 ltac:(lia)). }
{ exact HSTR. }
Qed.
End e.
End f.
End d.
