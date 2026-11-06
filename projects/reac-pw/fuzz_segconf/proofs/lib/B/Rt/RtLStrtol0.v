(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrtol0.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Row 3 of proofs/reac-pw/fuzz_segconf/provenance/evidence/interceptors/INTERFACE-A-interceptors.md:
   RtSeg.astrtol0_realizes at the strtol trampoline 0x43b44 (PC_strtol), with the stack-protector pair
   0xa3e98 -> 0x5ff838 (A_SSP_GOT, A_SSP_GUARD) that musl's strtol 0x9a9e8 reads. Segconf's one call is
   strtol(x, NULL, 10) (reac_declared_vlan_split 0x8a304).
   The walk is A/Bz/A/I_strtol0w.v istrtol0_spec (pupnp/FuzzHttp's strtol0_i_spec path, endptr = NULL), whose
   StrtolFixAndCheck call is A/Bz/A/I_strtolfix0.v sfix0_spec (pupnp's sfix0_spec). The lift is RtLStrtol.v
   cmd_strtol (fuzz_command's, relocated) with the end-pointer cell taken out: no end-pointer premise, no
   end-pointer write, E = the errno cell alone. The walk's two Section hypotheses are discharged as cmd_strtol
   discharges them (R_isPoisoned.rip_proof, strtol_wrap_sb.sb_proof); the fixed cells, the errno cell, the stack
   window and the value are read with RtLStrtol.v's lemmas.
   - seg_strtol0: the contract, under AR_laws tfibsegs B and SegBSyms B.
   - seg_strtol0_closed: the same with AR_laws discharged by YG0q.AR_laws_ok (RtClosed.v's closing form).
   - seg_strtol0_digits_closed: on 1 to 18 decimal digits, the value is SegModel.strtol10 of the digits and the
     errno cell keeps its value (lib/Spec/SegBridge.v bridge_strtol10_str, bridge_strtol10_errno). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YK04 YK14 YK1b YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import
RtDefs RtNumber RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2y.
From OSSVerify.reac_pw.fuzz_segconf.images Require AsanUbsan.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.__intscan_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.__intscan_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strtolw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strtol0w.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.strtol_wrap_sb.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtLStrtol.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegBridge.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PIS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.__intscan_c.
Module APIS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.__intscan_c.
Module SW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strtolw.
Module SW0 := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strtol0w.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module SBP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.strtol_wrap_sb.
Module LS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtLStrtol.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.
Module SBr := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegBridge.
Module SS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.seg_spec.

(* the walk's answer (lib/A/Prog/__intscan_c.v) and the contract's (lib/Prog/__intscan_c.v): the same definitions
   over the same CType text *)
Lemma s10_val_seg : forall s, APIS.s10_val s = PIS.s10_val s.
Proof. intros s. reflexivity. Qed.

Lemma s10_errno_seg : forall s w, APIS.s10_errno s w = PIS.s10_errno s w.
Proof. intros s w. reflexivity. Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strtol0 : RtSeg.astrtol0_realizes tfibsegs B 0x43b44 0xa3e98 0x5ff838.
Proof.
  unfold RtSeg.astrtol0_realizes.
  intros ly S W regs mem md x str ev HG HPRE G10 G11 G12 Hx0 SX HXL RDX AMX _ SEPXERR RDE HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & _ & _ & _ & _ & _ & G4).
  assert (EX : astr_len str = Z.of_nat (length str)) by reflexivity.
  pose proof (LS.amem_top x _ AMX) as AMX'.
  pose proof (LS.end_le str) as HEND.
  pose proof RDX as (_ & _ & HXN & _).
  rewrite (ts_errno B TB) in SEPXERR, RDE.
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (LS.errno_cell_clean (w_H W) mem ev RE RDE) as ERRC.
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (3 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 3 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 3 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* 3. the string *)
  pose proof (RtBzAdapt.bz_str_bytes W mem x str SX ltac:(lia) ltac:(lia)) as BYXm.
  assert (BYX : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_clean _ x _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYXm]. }
  (* 4. the stack-protector pair musl's strtol reads *)
  destruct (RtBzAdapt.bz_guard_bytes W mem 0xa3e98 0x5ff838 HG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (GOTm & can & CANm).
  assert (GOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0xa3e98 (BM.le8 (Z_to_bv 64 0x5ff838))).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact GOTm]. }
  assert (CAN : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x5ff838 (BM.le8 can)).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact CANm]. }
  (* 5. the range checks: every prefix of the string with its NUL *)
  assert (CKX : forall nn, 1 <= nn <= Z.of_nat (length str) + 1 ->
                  BQ.chk_ok (clean (mrestrict (w_H W) mem)) x nn).
  { intros nn Hnn. apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (3 * ESTACK) W regs mem x (astr_len str + 1) nn (astr_len str)
             RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* 6. the string lies outside the callee's window *)
  pose proof (RtBzAdapt.sep_of_read (3 * ESTACK) W regs mem x (astr_len str + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as SEPX.
  (* 7. the fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (LS.inited_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as AI.
  pose proof (LS.icells_sx_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICX.
  destruct (LS.slots_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as (RSLOT & AFSLOT & AF29).
  (* 8. the registers the walk names *)
  assert (G4' : reg_get regs 4 = Z_to_bv 64 TFIB_TP) by (rewrite <- (ts_tp B TB); exact G4).
  assert (ETP : bv_unsigned (reg_get regs 4) = TFIB_TP)
    by (rewrite G4'; apply unsigned_lit_small; unfold TFIB_TP; lia).
  assert (ESP : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 x) by exact G10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 0) by exact G11.
  assert (R12 : reg_get regs 12 = Z_to_bv 64 10) by exact G12.
  set (lo := spZ regs - 3 * ESTACK) in *.
  assert (Elo : lo = spZ regs - 12288) by (unfold lo, ESTACK; lia).
  assert (KH : BR.kHighShadowEnd < lo) by (unfold BR.kHighShadowEnd; lia).
  (* 9. the run *)
  eapply (bz_run_clean B TB W 0x43b44 regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - eapply RtBzAdaptP.evt_grows. apply bz_canon. rewrite R10, R11, R12.
    apply SW0.istrtol0_spec with (A := x) (str := str)
      (fv := fun s => Z_to_bv 64 (APIS.s10_val s)) (fe := APIS.s10_end) (fr := fun s w => APIS.s10_errno s w)
      (ev := Z_to_bv 64 ev) (can := can) (lo := lo).
    + exact RIP.rip_proof.
    + exact SBP.sb_proof.
    + exact BYX.
    + lia.
    + lia.
    + rewrite ETP. exact ERRC.
    + exact GOT.
    + exact CAN.
    + rewrite ESP. exact ST.
    + rewrite ESP. unfold SW.ISTRTOL_DEPTH. lia.
    + exact KH.
    + rewrite ESP. exact Hsp47.
    + lia.
    + exact CKX.
    + rewrite ESP. destruct SEPX; lia.
    + rewrite ETP, ESP. left. unfold TFIB_TP. lia.
    + rewrite ESP. left. unfold SW.STRTOL_SSP_GOT. lia.
    + rewrite ESP. left. unfold SW.STRTOL_SSP_GUARD. lia.
    + rewrite ETP. right. unfold SW.STRTOL_SSP_GUARD, TFIB_TP. lia.
    + exact M2S.
    + exact ICX.
    + exact AI.
    + exact MI.
    + exact RSLOT.
    + exact AFSLOT.
    + exact AF29.
    + exact HEND.
    + rewrite ETP. left. unfold TFIB_TP. lia.
    + rewrite ETP. right. unfold TFIB_TP. lia.
    + rewrite ETP. unfold TFIB_TP, TFIB_ERRNO in *. lia.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SW0.istrtol0_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI'
                    & ST' & CR).
    cbv beta in CR.
    rewrite ETP in MU, CR. rewrite ESP in MU, ST'.
    unfold SW.ISTRTOL_DEPTH in MU.
    apply (RtBzAdaptP.art_post_clean B LAWS (3 * ESTACK) 2272 ly S W regs mem md
             (aerrno_cell B) _ msc ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm).
    all: subst msc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + (* outside the window and the errno cell the walk kept the cleaned store *)
      intros y Hy HEy. apply MU. cbn [BF.outside].
      split; [exact Hy|]. split; [|exact I]. intros Hc. apply HEy. unfold aerrno_cell. rewrite (ts_errno B TB).
      unfold TFIB_ERRNO, TFIB_TP in Hc |- *. lia.
    + exact (LS.win_in m' (spZ regs) 2272 lo ST' ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)).
    + exact GROW.
    + (* E: the errno cell *)
      intros a Ha. unfold aerrno_cell in Ha. rewrite (ts_errno B TB) in Ha.
      split; [exact (LS.errno_unowned B LAWS TB ly S W mem md a HAR Ha)|].
      split; [unfold TFIB_ERRNO in Ha; lia|].
      split; [exact (LS.errno_dc a Ha) | exact (LS.errno_wh W a Ha)].
    + (* the answer *)
      intros regs' mem' HR _ HE'. split.
      * rewrite (HR _). transitivity (Z_to_bv 64 (APIS.s10_val str)); [reflexivity|].
        unfold w64. rewrite s10_val_seg. reflexivity.
      * rewrite (ts_errno B TB), <- s10_errno_seg.
        apply (LS.rd32_of_E (w_H W) mem' m' TFIB_ERRNO (APIS.s10_errno str (Z_to_bv 64 ev))).
        -- destruct CR as ((_ & BYR) & _). cbn [BC.cells_bytes BC.cbytes] in BYR. rewrite app_nil_r in BYR.
           exact BYR.
        -- intros k Hk. apply HE'. unfold aerrno_cell. rewrite (ts_errno B TB). lia.
Qed.

End s.

(* ---- the closing form: only the per-binary record SegBSyms B remains ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strtol0_closed : RtSeg.astrtol0_realizes tfibsegs B PC_strtol A_SSP_GOT A_SSP_GUARD.
Proof. exact (seg_strtol0 B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* a 32-bit cell read through the view does not see the bits of its value above 2^64 *)
Lemma rd32_wrap64 : forall (rd : reader) a z, rd32 rd a (bv_unsigned (Z_to_bv 64 z)) -> rd32 rd a z.
Proof.
  intros rd a z H k Hk. rewrite (H k Hk). f_equal.
  rewrite <- (LS.le_byte_word (Z_to_bv 64 z) k Hk). exact (LS.le_byte_wrap64 z k Hk).
Qed.

(* the bridge to the spine's model (lib/Spec/SegBridge.v): on 1 to 18 decimal digits strtol returns
   SegModel.strtol10 of the digits and leaves the errno cell as it was *)
Theorem seg_strtol0_digits_closed : forall ly S W regs mem md x str ev,
  aguard_ok tfibsegs W mem A_SSP_GOT A_SSP_GUARD ->
  ecall_pre_stk tfibsegs B (3 * ESTACK) ly S W regs mem md ->
  getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 10 -> 0 < x ->
  astr_at tfibsegs W mem x str -> x + astr_len str + 1 < 2 ^ 64 ->
  aread_ok tfibsegs (3 * ESTACK) W regs mem x (astr_len str + 1) ->
  amem_range x (astr_len str + 8) ->
  atail_vis tfibsegs W mem (x + astr_len str) ->
  (as_errno B + 4 <= x \/ x + astr_len str + 1 <= as_errno B) ->
  rd32 (aview tfibsegs (w_H W) mem) (as_errno B) ev ->
  rt_rom_view tfibsegs B W mem ->
  str <> [] -> forallb SM.isdigit (SS.zs str) = true -> (length str <= 18)%nat ->
  SRr tfibsegs W (cfg_at tfibsegs PC_strtol regs mem md)
    (art_post tfibsegs B (3 * ESTACK) ly S W regs mem md (aerrno_cell B)
      (fun regs' mem' => getr regs' 10 = w64 (SM.strtol10 (SS.zs str)) /\
                         rd32 (aview tfibsegs (w_H W) mem') (as_errno B) ev)).
Proof.
  intros ly S W regs mem md x str ev HG HPRE G10 G11 G12 Hx0 SX HXL RDX AMX TV SEPXERR RDE HROM Hne Hd Hl.
  eapply SRr_mono.
  { exact (seg_strtol0_closed ly S W regs mem md x str ev HG HPRE G10 G11 G12 Hx0 SX HXL RDX AMX TV SEPXERR RDE HROM). }
  intros W' c' _ (EW & regs' & mem' & md' & Ec & HAR' & Hpres & Hsame & (Hv & He) & Hfr & Hp1 & Hp2).
  unfold art_post. split; [exact EW|]. exists regs', mem', md'.
  split; [exact Ec|]. split; [exact HAR'|]. split; [exact Hpres|]. split; [exact Hsame|].
  split; [cbv beta; split|].
  - rewrite Hv. rewrite (SBr.bridge_strtol10_str str Hne Hd Hl). reflexivity.
  - rewrite (SBr.bridge_strtol10_errno str (Z_to_bv 64 ev) Hne Hd Hl) in He. exact (rd32_wrap64 _ _ _ He).
  - split; [exact Hfr|]. split; [exact Hp1 | exact Hp2].
Qed.

End closed.
