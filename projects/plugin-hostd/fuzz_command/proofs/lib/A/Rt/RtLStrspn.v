(* Our runtime contract for the strspn interceptor: astrspn_realizes (RtString.v) at the trampoline 0x45148
   (`j 0x46810`, the image's objdump listing, line 18686), with the stack-protector pair 0xa7098 -> 0x6045d8 that musl's
   strspn reads. The walk is A/Bz/A/I_strspnw.v isspn_spec (from 0x45148 to the return); its two Section
   hypotheses are discharged by A/Bz/A/R_isPoisoned.v rip_proof (the range check) and A/Prog/strspn_wrap_sp.v
   sp_proof (musl's strspn at 0x9f70c).
   - pre side: RtBzAdapt.v turns our premises into the walk's (stack window, bytes, guard pair, range checks,
     separation from the callee's window) and RtBzClean.v moves them to the cleaned store; the interceptor's fixed
     cells (I_strspnw.v icells_sp and the asan-inited flag 0xb1d98) are read here from the record's constant table,
     as RtLStrncmp.v reads the strncmp interceptor's;
   - post side: the walk writes only its stack window, so RtBzAdaptP.art_post_ro_clean gives our art_post, with
     RtBzPre.bz_window on the walk's munch;
   - the answer: the walk returns I_strspnw.spn_len, the contract states lib/Prog/strspn_c.v spn_len; they are the
     same fixpoint over the same byte lists (spn_len_same). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import
RtDefs RtString RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strspnw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strspn_wrap_sp.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SPW := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.I_strspnw.
Module RIP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Bz.A.R_isPoisoned.
Module SPP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.strspn_wrap_sp.
Module PSc := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.strspn_c.

(* ---- the walk's answer and the contract's: one fixpoint ---- *)

Lemma spn_len_same : forall set s, SPW.spn_len set s = PSc.spn_len set s.
Proof.
  intros set s. induction s as [|b s IH]; [reflexivity|].
  cbn [SPW.spn_len PSc.spn_len]. unfold SPW.in_set, PSc.in_set. rewrite IH. reflexivity.
Qed.

Lemma spn_len_le : forall set s, (SPW.spn_len set s <= length s)%nat.
Proof.
  intros set s. induction s as [|b s IH]; cbn [SPW.spn_len length]; [lia|].
  destruct (SPW.in_set set b); lia.
Qed.

(* the contracts' band room keeps a range below 2^47 *)
Lemma amem_top : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

(* ---- the strspn interceptor's fixed cells (I_strspnw.v:38) and the asan-inited flag ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : CmdBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

Lemma icells_sp_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> SPW.icells_sp (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold SPW.icells_sp.
  split; [|split; [|split]].
  - c8 M.
  - c8 M.
  - c1 M.
  - c1 M.
Qed.

(* the same cells on the cleaned store: each lies below 2^47 and holds the bytes it held; the flag's address is
   writable in the image (decided) *)
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

Lemma icells_sp_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> SPW.icells_sp (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_sp_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4).
  split; [|split; [|split]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - roc RE C4.
Qed.

Lemma inited_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) ->
  BS.rw_cells BI.asegs (RtBzClean.clean (mrestrict H mem)) 0xb1d98 [BC.C1 (Z_to_bv 8 1)].
Proof.
  intros ly S H mem RE M.
  assert (C : BS.rw_cells BI.asegs (mrestrict H mem) 0xb1d98 [BC.C1 (Z_to_bv 8 1)])
    by (apply rw_of_ro; [c1 M | vm_compute; reflexivity]).
  rwc RE C.
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

Theorem cmd_strspn : astrspn_realizes tfibsegs B 0x45148 0xa7098 0x6045d8.
Proof.
  unfold astrspn_realizes.
  intros ly S W regs mem md x y str set HG HPRE G10 G11 Hx0 Hy0 SX SY RDX AMX RDY AMY _ _ HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _).
  assert (EX : astr_len str = Z.of_nat (length str)) by reflexivity.
  assert (EY : astr_len set = Z.of_nat (length set)) by reflexivity.
  pose proof (amem_top x _ AMX) as AMX'.
  pose proof (amem_top y _ AMY) as AMY'.
  assert (SPL : Z.of_nat (SPW.spn_len set str) <= Z.of_nat (length str))
    by (apply Nat2Z.inj_le; apply spn_len_le).
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  (* 3. the two strings *)
  pose proof SX as (_ & SNZ).
  pose proof SY as (_ & CNZ).
  pose proof (RtBzAdapt.bz_str_bytes W mem x str SX ltac:(lia) ltac:(lia)) as BYXm.
  pose proof (RtBzAdapt.bz_str_bytes W mem y set SY ltac:(lia) ltac:(lia)) as BYYm.
  assert (BYX : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (str ++ [Z_to_bv 8 0])).
  { apply (bytes_at_clean _ x _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYXm]. }
  assert (BYY : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) y (set ++ [Z_to_bv 8 0])).
  { apply (bytes_at_clean _ y _ RE); [rewrite length_app; cbn [length]; unfold BM.UTOP; lia | exact BYYm]. }
  (* 4. the stack-protector pair musl's strspn reads *)
  destruct (RtBzAdapt.bz_guard_bytes W mem 0xa7098 0x6045d8 HG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (GOTm & can & CANm).
  assert (GOT : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0xa7098 (BM.le8 (Z_to_bv 64 0x6045d8))).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact GOTm]. }
  assert (CAN : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) 0x6045d8 (BM.le8 can)).
  { apply (bytes_at_clean _ _ _ RE); [rewrite BM.length_le8; unfold BM.UTOP; lia | exact CANm]. }
  (* 5. the two range checks: the set with its NUL, the span with the byte that stops it *)
  assert (CKY : BQ.chk_ok (clean (mrestrict (w_H W) mem)) y (Z.of_nat (length set) + 1)).
  { apply (chk_ok_clean _ y _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (2 * ESTACK) W regs mem y (astr_len set + 1) (Z.of_nat (length set) + 1)
             (astr_len set) RDY AMY ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (CKX : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x (Z.of_nat (SPW.spn_len set str) + 1)).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (2 * ESTACK) W regs mem x (astr_len str + 1)
             (Z.of_nat (SPW.spn_len set str) + 1) (astr_len str) RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* 6. both strings lie outside the callee's window *)
  pose proof (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem x (astr_len str + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as SEPX.
  pose proof (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem y (astr_len set + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDY) as SEPY.
  (* 7. the fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (inited_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as AI.
  pose proof (icells_sp_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as ICP.
  (* 8. the run *)
  set (lo := spZ regs - 2 * ESTACK) in *.
  eapply (bz_run_clean B TB W 0x45148 regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - eapply RtBzAdaptP.evt_grows. apply bz_canon.
    apply (SPW.isspn_spec RIP.rip_proof SPP.sp_proof)
      with (s := x) (c := y) (str := str) (cset := set) (lo := lo) (can := can).
    + exact G10.
    + exact G11.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold lo, ESTACK. lia.
    + unfold BR.kHighShadowEnd. lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). exact Hsp47.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact BYX.
    + exact SNZ.
    + exact BYY.
    + exact CNZ.
    + exact GOT.
    + exact CAN.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs). lia.
    + exact CKY.
    + exact CKX.
    + exact M2S.
    + exact AI.
    + exact ICP.
    + exact MI.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SPW.isspn_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI' & ST').
    destruct (bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2240 lo MU ST') as (MO & MN).
    { unfold lo, ESTACK. lia. }
    { unfold TFIB_IMG_END. lia. }
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 2240 ly S W regs mem md _ msc ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm).
    all: subst msc.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + keep_regs.
    + exact MO.
    + exact MN.
    + exact GROW.
    + intros regs' mem' HR _. cbv beta. rewrite (HR _).
      transitivity (Z_to_bv 64 (Z.of_nat (SPW.spn_len set str))); [reflexivity|].
      unfold w64. rewrite spn_len_same. reflexivity.
Qed.

End s.
