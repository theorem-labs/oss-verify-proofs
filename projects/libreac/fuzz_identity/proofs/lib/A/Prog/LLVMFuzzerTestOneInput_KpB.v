(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths and addresses changed; 279 of its 354 lines of code are new or changed and 5990 lines of the source are left out. *)
(* k_pairB_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_Kcut.v: the second strlen / check_str pair of segment K's
   r = 0 path, fuzz_identity.asan 0x81e88 .. 0x81ea0 (listing offsets 0x177c .. 0x1794).

   The code, from kpre at BASE + 0x177c:
     0x177c addi a0,s5,0                 a0 = tk (x21)
     0x1780 jal __interceptor_trampoline_strlen
     0x1784 addiw a0,a0,0                the length, sign-extended from 32 bits
     0x1788 addi a1,s5,0                 a1 = tk
     0x178c addi a2,s4,0                 a2 = cap_tok (x20)
     0x1790 jal check_str                check_str (n_lt, tk, cap_tok)
     0x1794 kpre again, with the memory every callee journal keeps.
   Neither run touches memory: the two regions of the state between the calls have an empty write window, so the
   bytes of the state at 0x177c are the bytes at the call. strlen goes through Klib's aj_strlen_at and check_str
   through Klib's k_call_afn with the contract's HCHK; the string's premises are Klib's k_heap_str on tk's heap
   block, whose bytes come from inv_J_end at the start state through kpre's block clause. The model gives the
   length (k_n_tk_len), the capacity (k_fits) and the non-zero bytes (k_n_tk_nz). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig IdentBlkTail YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Klib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require check_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Import RcIdentModel.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Section d.
(* the Section of LLVMFuzzerTestOneInput_Kcut.v, in the same order *)
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* what this pair takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis HCHK : check_str.tcheck_str_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

Theorem k_pairB : k_pairB_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 regs2' mem2' md2' W c HJend Hr HK.
destruct HJend as (ly2 & S2 & regs2 & mem2 & md2 & Ecfg & HJ2 & Hfrs2 & Hk2 & MLE2 & MOK2 & HC & HP).
unfold cfg_at in Ecfg. injection Ecfg as -> -> ->.
destruct HP as (HBL2 & Hwok & R27J & R26J & R24J & R20J & R21J & R22J & Vnm & Vcn & Vcd & Vin & Vout & Vrow &
  Bxnm & Bxdp & Znm & Zdp & Hr0).
destruct HC as (RspJ & Rs1J & Rs0J & Hmfb & Hmf32 & RgpJ & RtpJ & Rs3J & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (HWW & ly & S & regs & mem & md & Ecfg1 & HJ & Hfrs & MLE & MOK & HBL & KP1 & KP2 & KP3 &
  Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & R18 & R20 & R21 & R22 & R24 & R26 & R27).
subst W. subst c.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (HCSS : check_str.CHECK_STR_STK = 8208) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W2 mem md 4 pos HAR Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly S W2 mem md 4 pos HAR Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the eight machine-frame words at the memory of this cut: above the ceiling and above sp = mf *)
assert (VKm : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 192 ->
  val_mem SEGS (rd W2 mem2) (mf + o) n v -> val_mem SEGS (rd W2 mem) (mf + o) n v).
{ intros o n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  apply KP1; [clear - H0 H1 Hkk Hmf0 Hmfb Hshi H47 C1; lia | clear - H0 Hkk; lia]. }
pose proof (k_ok_mf W2 regs mem 0x177c mf _ _ _ _ _ nm SF Rs1 ltac:(clear - Hmf0 C1; lia)
  ltac:(clear - Hmf0 Hmfb Hshi H47 C1; lia)
  (VKm 80 8%nat _ ltac:(lia) ltac:(lia) V80) (VKm 136 8%nat _ ltac:(lia) ltac:(lia) Vrow)
  (VKm 144 8%nat _ ltac:(lia) ltac:(lia) Vcd) (VKm 152 8%nat _ ltac:(lia) ltac:(lia) Vcn)
  (VKm 160 8%nat _ ltac:(lia) ltac:(lia) Vin) (VKm 168 8%nat _ ltac:(lia) ltac:(lia) Vout)
  (VKm 176 8%nat _ ltac:(lia) ltac:(lia) V176) (VKm 184 8%nat _ ltac:(lia) ltac:(lia) Vnm)) as HS.
remember (Eimg (Ereg regs (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
(* the model at r = 0, and the token's heap block *)
destruct (k_r0 (e_pl g) Hr) as [Hwok' Hfits].
destruct (k_fits (e_pl g) Hfits) as (Fnm & Ftk & Fdp).
destruct (Hr0 Hr) as (Bnm0 & Btk0 & Bdp0).
pose proof (SlotModel.n_ln_le (e_pl g) Hwok') as HL21.
assert (HCapT : 0 <= SlotModel.t_cap_tok (e_pl g) < 40).
{ unfold SlotModel.t_cap_tok, SlotModel.tb.
  pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 6)).
  apply Z.mod_pos_bound. lia. }
assert (Hblk : forall x, In x (k_blocks g nm tk dp) -> In x (ablocks B ly S)).
{ intros x Hx. destruct HBL as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. left. exact Hx. }
assert (Itk : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly S))
  by (apply Hblk; unfold k_blocks; right; left; reflexivity).
set (L := length (SlotModel.n_TK (e_pl g))) in *.
assert (HLn : Z.of_nat L = SlotModel.n_lt (e_pl g)) by (exact (k_n_tk_len (e_pl g))).
assert (HL40 : 0 <= Z.of_nat L <= 21).
{ rewrite HLn. unfold SlotModel.n_lt.
  destruct (SlotModel.has_dash (SlotModel.n_EXP_NM (e_pl g))); clear - HL21; lia. }
assert (Hcap1 : Z.of_nat L + 1 <= req_size (Z.max (SlotModel.t_cap_tok (e_pl g)) 1))
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) 0); lia).
(* 0x81e88 .. 0x81e8c: a0 := tk, the strlen call *)
unfold cfg_at. change (w64 (BASE + 0x177c)) with (Z_to_bv 64 (BASE + 0x177c)).
paj_run_shc RUNP RUNC HS HJ.
{ cbn [ss_mem k_ssm]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha.
  apply (kept_of_frame E _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr'. lia. }
clear HF HFr HG.
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) C8. prreg HS (9%bv : bv 5) C9. prreg HS (18%bv : bv 5) C18.
prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20. prreg HS (21%bv : bv 5) C21.
prreg HS (22%bv : bv 5) C22. prreg HS (24%bv : bv 5) C24. prreg HS (26%bv : bv 5) C26.
prreg HS (27%bv : bv 5) C27.
rewrite (EE 21%nat 21%bv eq_refl), R21 in R10.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4. rewrite (EE 8%nat 8%bv eq_refl), Rs0 in C8.
rewrite (EE 9%nat 9%bv eq_refl), Rs1 in C9. rewrite (EE 18%nat 18%bv eq_refl), R18 in C18.
rewrite (EE 19%nat 19%bv eq_refl), Rs3 in C19. rewrite (EE 20%nat 20%bv eq_refl), R20 in C20.
rewrite (EE 21%nat 21%bv eq_refl), R21 in C21. rewrite (EE 22%nat 22%bv eq_refl), R22 in C22.
rewrite (EE 24%nat 24%bv eq_refl), R24 in C24. rewrite (EE 26%nat 26%bv eq_refl), R26 in C26.
rewrite (EE 27%nat 27%bv eq_refl), R27 in C27.
pmkst HS.
pose proof HJ as (HARc & _).
(* the token's bytes at the call: kpre's block clause, then the run *)
assert (HBtk : bytes_at8 W2 (ms_mem ms) tk (SlotModel.n_TK (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms) _ _); [|exact Btk0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Itk) as (_ & Q4096 & Qceil & _).
  rewrite (KR1 (tk + kk) ltac:(clear - Hkk Q4096 Qceil C1 Hcap1; lia)).
  apply (KP2 tk _ kk Itk). clear - Hkk Hcap1. lia. }
destruct (k_heap_str B LAWS ly S W2 (ms_mem ms) _ tk _ (SlotModel.n_TK (e_pl g)) HARc Itk HBtk
  (k_n_tk_nz (e_pl g) Hwok') Hcap1) as (Hfb & Hmr & Hrx & Hhx & Htl & Hp0 & Hp1 & Happ).
fold L in Hfb, Hmr, Hrx, Hhx, Htl, Hp1.
assert (HROc : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ HAROS))). }
assert (Usp : spZ (ms_regs ms) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
eapply SRr_bind.
{ refine (aj_strlen_at B LAWS _ ASTRLEN W2 (ms_regs ms) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ _ _ _ tk (Z.of_nat L)
    (mf - sp0) _ HJ R10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hp1 C1; lia) Usp
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(clear - Hmfb HSTK' Has; unfold ESTACK; lia) R3 R4 eq_refl _ Hfb _ _
    Hmr Hrx Hhx Htl HROc).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + destruct Hfb as (_ & Hlt & Hat). destruct (Z.lt_ge_cases a (tk + Z.of_nat L)) as [Hl | Hg].
      * destruct (Hlt (a - tk) ltac:(lia)) as (b & Hb & _). replace a with (tk + (a - tk)) by lia. rewrite Hb. discriminate.
      * replace a with (tk + Z.of_nat L) by lia. rewrite (Hat ltac:(lia)). discriminate.
    + rewrite Usp. clear - Ha Hp1 Hmf0. unfold ESTACK. lia.
  - intros a Ha. clear - Ha Hp1 Hmf0. unfold ESTACK. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & R10' & KEEPs & GROWs).
(* back at 0x81e8c: the memory outside strlen's window is the memory of the cut *)
pose proof (k_pres _ _ 9%bv HP3 ltac:(kcs)) as P9. rewrite C9 in P9.
assert (KEEP3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - check_str.CHECK_STR_STK <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  rewrite (KEEPs a ltac:(clear - Ha C1; lia)
    ltac:(replace (sp0 + (mf - sp0)) with mf by lia; rewrite HCSS in Hw; clear - Hw; unfold ESTACK; lia)).
  rewrite (KR1 a ltac:(clear - Ha C1; lia)). apply KP1; [exact Ha | exact Hw]. }
assert (VM3 : forall o (n : nat) v, 0 <= o -> o + Z.of_nat n <= 192 ->
  val_mem SEGS (rd W2 mem2) (mf + o) n v -> val_mem SEGS (rd W2 mem3) (mf + o) n v).
{ intros o n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply KEEP3.
  - clear - H0 H1 Hkk Hmf0 Hmfb Hshi H47 C1. lia.
  - clear - H0 Hkk HCSS. rewrite HCSS. lia. }
pose proof (k_ok_mf W2 regs3 mem3 0x1784 mf _ _ _ _ _ nm SF P9 ltac:(clear - Hmf0 C1; lia)
  ltac:(clear - Hmf0 Hmfb Hshi H47 C1; lia)
  (VM3 80 8%nat _ ltac:(lia) ltac:(lia) V80) (VM3 136 8%nat _ ltac:(lia) ltac:(lia) Vrow)
  (VM3 144 8%nat _ ltac:(lia) ltac:(lia) Vcd) (VM3 152 8%nat _ ltac:(lia) ltac:(lia) Vcn)
  (VM3 160 8%nat _ ltac:(lia) ltac:(lia) Vin) (VM3 168 8%nat _ ltac:(lia) ltac:(lia) Vout)
  (VM3 176 8%nat _ ltac:(lia) ltac:(lia) V176) (VM3 184 8%nat _ ltac:(lia) ltac:(lia) Vnm)) as HS3.
rewrite R1.
remember (Eimg (Ereg regs3 (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE3.
clear HS HEI. rename HS3 into HS. rename HEI3 into HEI.
(* 0x81e8c .. 0x81e9c: a0 := sext.w len, a1 := tk, a2 := cap_tok, the check_str call *)
paj_run_shc RUNP RUNC HS HJ3.
{ cbn [ss_mem k_ssm]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]. }
prreg HS (10%bv : bv 5) X10. prreg HS (11%bv : bv 5) X11. prreg HS (12%bv : bv 5) X12. prreg HS (1%bv : bv 5) X1.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
rewrite (EE3 10%nat 10%bv eq_refl), R10' in X10. unfold w64 in X10. rewrite k_sextw in X10 by (clear - HL40; lia).
rewrite (EE3 21%nat 21%bv eq_refl), (k_pres _ _ 21%bv HP3 ltac:(kcs)), C21 in X11.
rewrite (EE3 20%nat 20%bv eq_refl), (k_pres _ _ 20%bv HP3 ltac:(kcs)), C20 in X12.
rewrite (EE3 2%nat 2%bv eq_refl), (k_pres _ _ 2%bv HP3 ltac:(kcs)), R2 in X2.
rewrite (EE3 3%nat 3%bv eq_refl), (k_pres _ _ 3%bv HP3 ltac:(kcs)), R3 in X3.
rewrite (EE3 4%nat 4%bv eq_refl), (k_pres _ _ 4%bv HP3 ltac:(kcs)), R4 in X4.
rewrite (EE3 8%nat 8%bv eq_refl), (k_pres _ _ 8%bv HP3 ltac:(kcs)), C8 in X8.
prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18. prreg HS (19%bv : bv 5) Y19. prreg HS (20%bv : bv 5) Y20.
prreg HS (21%bv : bv 5) Y21. prreg HS (22%bv : bv 5) Y22. prreg HS (24%bv : bv 5) Y24. prreg HS (26%bv : bv 5) Y26.
prreg HS (27%bv : bv 5) Y27.
rewrite (EE3 9%nat 9%bv eq_refl), (k_pres _ _ 9%bv HP3 ltac:(kcs)), C9 in Y9.
rewrite (EE3 18%nat 18%bv eq_refl), (k_pres _ _ 18%bv HP3 ltac:(kcs)), C18 in Y18.
rewrite (EE3 19%nat 19%bv eq_refl), (k_pres _ _ 19%bv HP3 ltac:(kcs)), C19 in Y19.
rewrite (EE3 20%nat 20%bv eq_refl), (k_pres _ _ 20%bv HP3 ltac:(kcs)), C20 in Y20.
rewrite (EE3 21%nat 21%bv eq_refl), (k_pres _ _ 21%bv HP3 ltac:(kcs)), C21 in Y21.
rewrite (EE3 22%nat 22%bv eq_refl), (k_pres _ _ 22%bv HP3 ltac:(kcs)), C22 in Y22.
rewrite (EE3 24%nat 24%bv eq_refl), (k_pres _ _ 24%bv HP3 ltac:(kcs)), C24 in Y24.
rewrite (EE3 26%nat 26%bv eq_refl), (k_pres _ _ 26%bv HP3 ltac:(kcs)), C26 in Y26.
rewrite (EE3 27%nat 27%bv eq_refl), (k_pres _ _ 27%bv HP3 ltac:(kcs)), C27 in Y27.
(* the run to the call writes nothing: its one region is read-only *)
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha.
  apply (kept_of_frame E3 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr'. lia. }
clear HF HFr HG.
(* the three clauses of the cut, at the call's memory *)
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - check_str.CHECK_STR_STK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite (KR2 a ltac:(clear - Ha C1; lia)). exact (KEEP3 a Ha Hw). }
assert (KB : forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) (ms_mem ms0) (b + i) = aview SEGS (w_H W2) mem2 (b + i)).
{ intros b n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Q4096 & Qceil & _).
  rewrite (KR2 (b + i) ltac:(clear - Hi Q4096 Qceil C1; lia)).
  rewrite (KEEPs (b + i) ltac:(clear - Hi Q4096 Qceil C1; lia)
    ltac:(clear - Hi Q4096 Qceil Hmf0; unfold ESTACK; lia)).
  rewrite (KR1 (b + i) ltac:(clear - Hi Q4096 Qceil C1; lia)). exact (KP2 b n i Hin Hi). }
assert (KF : forall a, (in_zr a (frame_rng ly (4, pos)) \/
    in_zr a (shadow_addr (frame_addr ly 4 pos), fs_frame_bytes 4 / 8)) ->
  ~ (sh + 86 <= a < sh + 87) -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hs.
  assert (Hrng : 0 <= a < alloc_ceiling).
  { unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite EFa, HFB in Ha. fold sh in Ha.
    clear - Ha HSF0 HSF1 Hsh1. lia. }
  rewrite (KR2 a ltac:(clear - Hrng C1; lia)).
  rewrite (KEEPs a ltac:(clear - Hrng C1; lia) ltac:(clear - Hrng Hmf0; unfold ESTACK; lia)).
  rewrite (KR1 a ltac:(clear - Hrng C1; lia)). exact (KP3 a Ha Hs). }
pmkst HS.
rewrite (PSIG IS_check_str AF_check_str eq_refl).
(* the string's facts again, at the call's memory *)
pose proof HJ3 as (HARc1 & _).
assert (HBtk1 : bytes_at8 W2 (ms_mem ms0) tk (SlotModel.n_TK (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms0) _ _); [|exact Btk0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  apply (KB tk _ kk Itk). clear - Hkk Hcap1. lia. }
destruct (k_heap_str B LAWS ly S W2 (ms_mem ms0) _ tk _ (SlotModel.n_TK (e_pl g)) HARc1 Itk HBtk1
  (k_n_tk_nz (e_pl g) Hwok') Hcap1) as (Gfb & Gmr & Grx & Ghx & Gtl & _ & _ & _).
fold L in Gfb, Gmr, Grx, Ghx, Gtl.
pose proof (blk_off_imgP B ly S W2 mem md tk _ HAR Itk) as Hoff.
assert (HROc1 : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms0))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 (HRO _ HAROS))). }
(* the call chain at the call: the entry's own frame record, as k_pairA *)
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0' & _ & Hch0 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (VK4 : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply KA.
  - clear - H0 H1 Hkk Hmf0 Hshi H47 C1. lia.
  - clear - H0 Hkk HCSS. rewrite HCSS. lia. }
assert (HCH : exists ch, achain ly (aview SEGS (w_H W2) (ms_mem ms0)) mf sp0 ch).
{ change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    apply (achain_push ly _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1c; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vra].
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vs0].
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hchain).
assert (Usp1 : spZ (ms_regs ms0) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite X2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us01 : s0Z (ms_regs ms0) = sp0).
{ unfold s0Z. rewrite X8. unfold w64. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
eapply SRr_bind.
{ apply (k_call_afn B LAWS W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly S _ _ check_str.CHECK_STR_STK [] 0 (mf - sp0) (getr (ms_regs ms0) 1) ch1 (BASE + AF_check_str)
    (fun ly' S' W' _ _ _ => ly' = ly /\ S' = S /\ W' = W2) HJ3 Usp1
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(rewrite HCSS; lia)
    ltac:(rewrite HCSS; clear - Hmfb HSTK' Has; lia) X3 X4 eq_refl).
  - rewrite X1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite X1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - rewrite Usp1, Us01. replace (sp0 + (mf - sp0)) with mf by lia. exact Hchain.
  - intros HAFN.
    refine (HCHK ly S W2 (ms_regs ms0) (ms_mem ms0) _ ch1 (Z.of_nat L) tk (SlotModel.t_cap_tok (e_pl g))
      HAFN HROc1 X10 X11 X12 ltac:(clear - HL40; lia) ltac:(clear - HCapT; lia) _).
    intros _. unfold check_str.tcheck_str_ok.
    split; [clear - Ftk HLn; lia|]. split; [clear - Hp0; lia|].
    split; [clear - Hoff Hcap1; destruct Hoff; [left | right]; lia|].
    split; [exact Gfb|].
    split; [intros a Ha; rewrite Usp1; rewrite HCSS; clear - Ha Hp1 Hmf0; lia|].
    split; [exact Gmr|]. split; [exact Grx|]. split; [exact Ghx | exact Gtl].
  - intros a (r & Hr' & _). destruct Hr'. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & (-> & -> & ->)).
(* 0x81ea0: kpre again *)
apply SRr_ret. unfold kpre. split; [reflexivity|].
exists ly, S, regs4, mem4, md4.
split; [unfold cfg_at; rewrite X1; reflexivity|].
split; [replace (4 * Z.of_nat (m_nrec g) + 7) with (4 * Z.of_nat (m_nrec g) + 7 + 0) by lia; exact HJ4|].
split; [exact Hfrs|]. split; [exact MLE|]. split; [exact MOK|]. split; [exact HBL|].
pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
split.
{ intros a Ha Hw. rewrite (G1 a Ha ltac:(rewrite HCSS in Hw |- *; clear - Hw; lia)).
  exact (KA a Ha Hw). }
split.
{ intros b n i Hin Hi. rewrite (G2 b n i Hin Hin Hi ltac:(intros (r & Hr' & _); destruct Hr')).
  exact (KB b n i Hin Hi). }
split.
{ intros a Ha Hs. rewrite (G4 4 pos a ltac:(rewrite Hfrs; left; reflexivity) Ha ltac:(intros (r & Hr' & _); destruct Hr')).
  exact (KF a Ha Hs). }
rewrite !(k_pres _ _ _ HP4) by kcs.
split; [exact X2|]. split; [exact Y9|]. split; [exact X8|]. split; [exact X3|]. split; [exact X4|].
split; [exact Y19|]. split; [exact Y18|]. split; [exact Y20|]. split; [exact Y21|]. split; [exact Y22|].
split; [exact Y24|]. split; [exact Y26 | exact Y27].
Qed.

End d.
End c.
End b.
End a.