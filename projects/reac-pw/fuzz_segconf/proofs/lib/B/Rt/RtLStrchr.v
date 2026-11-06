(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its module paths, module names, addresses and numbers changed; 520 of its 641 lines of code are new or changed and 714 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/reply.v, with its module paths and module names changed; 399 of its 440 lines of code are new or changed and 600 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMstrstr.v, with its module paths and module names changed; 266 of its 409 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Rt/RtLStrstr.v, with its module paths, module names and numbers changed; 142 of its 201 lines of code are new or changed and 350 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrchr.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Row 6 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md): strchr at
   SegRtPC.PC_strchr = 0x43ab4, the one-instruction trampoline in front of __interceptor_strchr 0x45b70, stated as
   RtSeg.astrchr_realizes.
   - the walk: A/Bz/A/I_strchrw.v tramp_strchr and istrchr_spec (relocated from omx-clap-core/fuzz_manifest), whose two
     Section hypotheses are A/Bz/A/R_isPoisoned.v rip_proof (the range check) and A/FMss_strchr_wrap.v chr_proof (musl
     strchr 0x9b180, called through the real-function cell);
   - pre side: RtBzAdapt.v gives the walk's premises from ours (the stack window, the string with its NUL and the rest
     of the NUL's 8-byte word, the range check, the separation from the callee's window) and RtBzClean.v moves them to
     the cleaned store; the interceptor's fixed cells (I_strchrw.v icells_chr) are read here from the record's
     constant table, as RtLStrncmp.v reads the strncmp interceptor's;
   - post side: the walk writes only its stack window, so RtBzAdaptP.art_post_ro_clean gives our art_post, with
     RtBzPre.bz_window on the walk's munch;
   - the answer: the walk returns I_strchrw.v chr_res, which chr_answer reads on the byte values as RtSeg's post.
   The pattern is fuzz_manifest's lib/A/FMstrchr.v astrchr_holds, restated on RtSeg's premises the way
   fuzz_command's RtLStrspn.v restates a Bz walk on RtString's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import
RtDefs RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg SegRtPC.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Spec.StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.FMss_strchr_wrap.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BSF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Spec.StrFun.
Module BCH := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strchrw.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module SCW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.FMss_strchr_wrap.

(* ---- the walk's answer, read on the byte values ---- *)

Lemma nth_error_firstn_some : forall (l : list byte) n j b,
  nth_error (firstn n l) j = Some b -> (j < n)%nat /\ nth_error l j = Some b.
Proof.
  induction l as [|a l IH]; intros n j b H; [rewrite firstn_nil in H; destruct j; discriminate|].
  destruct n as [|n]; [destruct j; discriminate|].
  destruct j as [|j]; cbn in H |- *; [split; [lia | exact H]|].
  destruct (IH n j b H) as (Hj & Hn). split; [lia | exact Hn].
Qed.

Lemma chr_answer : forall x c (s : list byte),
  (BCH.chr_res x c s = 0 /\ ~ In c (map (fun b : byte => bv_unsigned b) s)) \/
  (exists j, RtSeg.first_at (map (fun b : byte => bv_unsigned b) s) c j /\ BCH.chr_res x c s = x + Z.of_nat j).
Proof.
  intros x c s. unfold BCH.chr_res.
  destruct (BSF.find_byte c s) as [i|] eqn:F.
  - right. exists i. split; [|reflexivity].
    destruct (BSF.find_byte_Some _ _ _ F) as (Hl & (b & Hn & Hb) & Hmin).
    unfold RtSeg.first_at. rewrite length_map. split; [exact Hl|]. split.
    + change 0 with ((fun b0 : byte => bv_unsigned b0) (Z_to_bv 8 0)). rewrite map_nth.
      rewrite (nth_error_nth s i (Z_to_bv 8 0) Hn). exact Hb.
    + intros Hin. rewrite firstn_map in Hin. apply in_map_iff in Hin as (b' & Eb' & Hin').
      apply In_nth_error in Hin' as (j & Hj). destruct (nth_error_firstn_some s i j b' Hj) as (Hji & Hj').
      exact (Hmin j b' Hji Hj' Eb').
  - left. split; [reflexivity|]. intros Hin. apply in_map_iff in Hin as (b & Eb & Hin).
    apply In_nth_error in Hin as (j & Hj). exact (BSF.find_byte_None _ _ F j b Hj Eb).
Qed.

(* the contracts' band room keeps a range below 2^47 *)
Lemma amem_top : forall p n, amem_range p n -> p + n <= 2 ^ 47.
Proof. intros p n H. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in H. lia. Qed.

(* a range that ends below a 16-aligned sp minus 8192 ends, rounded up to its 8-byte word, below sp - 2224 *)
Lemma round_sep : forall e sp, sp mod 16 = 0 -> e + 1 <= sp - 8192 -> e + 1 + (7 - e mod 8) <= sp - 2224.
Proof. intros e sp H1 H2. Z.div_mod_to_equations. lia. Qed.

(* ---- the strchr interceptor's fixed cells (I_strchrw.v icells_chr) ---- *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : SegBSyms B.

Local Ltac c8 M := eapply (ro_c8 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 B TB _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

Lemma icells_chr_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> BCH.icells_chr (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold BCH.icells_chr.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - c8 M.
  - c8 M.
  - c8 M.
  - apply rw_of_ro; [c1 M | vm_compute; reflexivity].
  - c8 M.
  - c1 M.
  - c1 M.
Qed.

(* the same cells on the cleaned store: each lies below 2^47 and holds the bytes it held, and the writable cell's
   addresses are writable in the image (decided) *)
Local Ltac roc RE H :=
  apply (RtBzClean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (RtBzClean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

Lemma icells_chr_of_ARm_clean : forall ly S H mem, RtBzClean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> BCH.icells_chr (RtBzClean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_chr_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - rwc RE C4.
  - roc RE C5.
  - roc RE C6.
  - roc RE C7.
Qed.

End k.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strchr : RtSeg.astrchr_realizes tfibsegs B SegRtPC.PC_strchr.
Proof.
  unfold RtSeg.astrchr_realizes.
  intros ly S W regs mem md x c s HPRE G10 G11 Hc Hx0 SX RDX AMX TX HROM.
  pose proof HPRE as (HEP & _ & _).
  pose proof HEP as (HAR & _ & HAL & _).
  pose proof (amem_top x _ AMX) as AMX'.
  pose proof RDX as (Hx & _ & _ & _).
  assert (EL : astr_len s = Z.of_nat (length s)) by reflexivity.
  (* 1. the read-only views and the cleaned store *)
  pose proof (RtBzAdapt.rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  (* 2. the stack window *)
  destruct (RtBzAdapt.stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END, ESTACK in *; lia | unfold BM.UTOP; lia | exact ST0]. }
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  (* 3. the character: a1's low byte *)
  assert (E11 : bv_unsigned (reg_get regs 11) mod 256 = c).
  { change (reg_get regs 11) with (getr regs 11). rewrite G11. unfold w64. rewrite u64z by lia.
    apply Z.mod_small. lia. }
  (* 4. the string, its NUL and the rest of the NUL's 8-byte word *)
  destruct (RtBzAdapt.bz_str_slack W mem x s SX TX ltac:(lia) ltac:(lia)) as (BUFm & SLK).
  set (slack := RtBzAdapt.tail_bytes W mem (x + astr_len s)) in *.
  pose proof (RtBzAdapt.tail_bytes_length W mem (x + astr_len s)) as LSL. fold slack in LSL.
  set (full := s ++ Z_to_bv 8 0 :: slack) in *.
  assert (LL : Z.of_nat (length full) = Z.of_nat (length s) + 1 + (7 - (x + Z.of_nat (length s)) mod 8)).
  { unfold full. rewrite length_app. cbn [length]. rewrite <- EL. lia. }
  pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as HM8.
  assert (BUF : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x full).
  { apply (bytes_at_clean _ x _ RE); [rewrite LL; unfold BM.UTOP; lia | exact BUFm]. }
  (* 5. the length the walk reads: up to the next 8-byte boundary after the stop *)
  pose proof (BCH.chr_n_le x c s) as NL. pose proof (BCH.chr_n_ge x c s) as NG.
  pose proof (BCH.pad_mono2 x (BCH.chr_n x c s) (Z.of_nat (length s) + 1) NL) as PAD.
  assert (PM : (- (x + (Z.of_nat (length s) + 1))) mod 8 = 7 - (x + Z.of_nat (length s)) mod 8)
    by (Z.div_mod_to_equations; lia).
  (* 6. the string lies outside the callee's window, up to that word's end: sp is 16-aligned *)
  assert (SEP : x + Z.of_nat (length full) <= spZ regs - 2224 \/ spZ regs <= x).
  { destruct (RtBzAdapt.sep_of_read (2 * ESTACK) W regs mem x (astr_len s + 1)
                ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as [SL|SR]; [left | right; exact SR].
    rewrite EL in SL. unfold ESTACK in SL.
    pose proof (round_sep (x + Z.of_nat (length s)) (spZ regs) HAL ltac:(lia)) as RS.
    rewrite LL. lia. }
  (* 7. the range check over the bytes the interceptor checks: chr_n <= len + 1 *)
  assert (CK : BQ.chk_ok (clean (mrestrict (w_H W) mem)) x (BCH.chr_n x c s)).
  { apply (chk_ok_clean _ x _ RE); [lia | lia |].
    exact (RtBzAdapt.chk_of_read (2 * ESTACK) W regs mem x (astr_len s + 1) (BCH.chr_n x c s)
             (astr_len s) RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)). }
  (* 8. the fixed cells *)
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_chr_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  (* 9. the run *)
  set (lo := spZ regs - 2 * ESTACK) in *.
  eapply (bz_run_clean B TB W SegRtPC.PC_strchr regs mem md _ _
            (RtBzAdapt.romN_of_rt B W mem HROM) (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - eapply RtBzAdaptP.evt_grows. apply bz_canon. apply BCH.tramp_strchr.
    eapply (BCH.istrchr_spec RIP.rip_proof SCW.chr_proof)
      with (s := x) (str := s) (slack := slack) (L := length full) (lo := lo).
    + exact G10.
    + exact ST.
    + rewrite Esp. unfold lo, ESTACK. lia.
    + unfold BR.kHighShadowEnd. unfold lo in *. lia.
    + rewrite Esp. exact Hsp47.
    + lia.
    + rewrite LL. lia.
    + rewrite firstn_all. exact BUF.
    + exact (proj2 SX).
    + unfold full. rewrite length_app. cbn [length]. lia.
    + rewrite E11. lia.
    + rewrite E11, LL. rewrite PM in PAD. lia.
    + rewrite Esp. destruct SEP as [SL|SR]; [left; exact SL | right; exact SR].
    + rewrite E11. exact CK.
    + exact M2S.
    + exact IC.
    + exact MI.
  - intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold BCH.istrchr_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Emsc & MU & WM & MI' & ST').
    destruct (bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2224 lo MU ST') as (MO & MN).
    { unfold lo, ESTACK. lia. }
    { unfold lo in *. unfold TFIB_IMG_END. lia. }
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 2224 ly S W regs mem md _ msc ms' model' HPRE
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
    + intros regs' mem' HR _. cbv beta.
      assert (A10 : getr regs' 10%bv = Z_to_bv 64 (BCH.chr_res x c s))
        by (rewrite (HR 10%bv), <- E11; reflexivity).
      rewrite A10.
      destruct (chr_answer x c s) as [(V0 & NI) | (j & FA & Vj)].
      * left. split; [rewrite V0; reflexivity | exact NI].
      * right. exists j. split; [exact FA | rewrite Vj; reflexivity].
Qed.

End s.

(* ---- the closing form: AR_laws discharged by the core's law proof, the record SegBSyms B the one residual ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strchr_closed : RtSeg.astrchr_realizes tfibsegs B SegRtPC.PC_strchr.
Proof. exact (seg_strchr B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

Print Assumptions seg_strchr_closed.
