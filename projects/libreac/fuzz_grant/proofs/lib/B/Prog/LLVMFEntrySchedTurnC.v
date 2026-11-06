(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnD), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnD.v, with its module paths changed; 151 of its 223 lines of code are new or changed and 208 lines of the source are left out. *)
(* The image-B (UBSan) walk of the call of reac_headamp_tx_effective in one
   frame-loop turn of LLVMFuzzerTestOneInput, over image B's own addresses, registers, spill slots and UBSan
   guards; the shape is image A's.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnC.v at e6bd82f51c9. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput (image B, entry 0x80a3c), segment C:
   0x81c18 (GP_eff) .. 0x81c1c (GP_effr), LLVMFEntrySchedTurnDefs.v.
     81c18 jal reac_headamp_tx_effective    a0 = t, a1 = c, a2 = p; returns eff T' t c p in a0
   The callee is image B's reac_headamp_tx_effective at 0x85c00 (AF_reac_headamp_tx_effective = 0x51c4 in
   GrantList.v), and its contract is GrantBContracts.tb_reac_headamp_tx_effective_spec. The call is made from the
   realigned stack pointer s1 = c_sp1 with the caller's sp in s0, and is handed the entry function's own frame as
   its call chain (LLVMFEntrySeat.ge_achain). The table is the live 460-byte block `gtab` names, so t > 0 picks
   the contract's block case and the table bytes the contract reads are LAY_TX's. The contract's footprint is
   empty, so every byte the turn tracks (the stack above s1, the caller's blocks, the frame on the side stack and
   its shadow) is unchanged across the call: in particular the cells ch, param and value still hold c, p and v,
   which the next segment reads back.
   What image B makes different from image A's segment C (0x81624 .. 0x8162c):
   - image A runs `mv a0,s4` and then the call; image B's a0 already holds t (`ld a0,0x98(s1)` at 0x81c14, in
     segment B), so the segment is the call alone;
   - the value v is in s4 (x20), where image A keeps it in s3 (x19); the turn counter is s5 (x21), image A's s2
     (x18); the registers the call keeps are 2 3 4 8 9 18..27 (image A: 2 3 4 8 9 18..25 27);
   - image B's contract allows tx = 0 (its table premise is `tx = 0 \/ (block /\ obj_at)`) and gives the table's
     bytes back only for tx <> 0, where image A's asks for the block and gives the bytes unconditionally; the
     contract wins, and t > 0 (from gtab) discharges both;
   - the stack the call needs is STK_reac_headamp_tx_effective = 16 + ESTACK (image A's TEFF_STK, the same
     value), and the callee's pc is BASE + AF_reac_headamp_tx_effective (pa_sigma_reac_headamp_tx_effective);
   - the image's low bound is GrantTop.IMG_LO_B, which is opaque: IMG_LO_B_val rewrites it to 0x10000 before lia. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedTurnDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* As image A's segment C does for its whole file: lia below runs on contexts with many / and mod; the
   facts it needs about them are posed by hand (dm). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* HeadampSched.frame_ok: the record the scheduler sent names a channel below 48 and a
   parameter below 3, so both fit the byte arguments of reac_headamp_tx_effective. *)
Lemma segC_cp : forall pl t i T us c p v T', 0 < t ->
  GrantSlotPlan.sched_at pl t i = (T, us) -> NextModel.next_model T t = (1, (c, p, v), T') ->
  0 <= c < 48 /\ 0 <= p < 3.
Proof.
  intros pl t i T us c p v T' Ht Hsch Hnx.
  pose proof (HeadampSched.frame_ok pl t i Ht) as FO.
  destruct (GrantSlotPlan.sched_rd pl) as [[[[sb sw] per] fr] pe].
  cbv beta iota in FO. rewrite Hsch in FO. cbv beta iota in FO. rewrite Hnx in FO. cbv beta iota in FO.
  destruct FO as (_ & _ & _ & _ & _ & _ & _ & FR1).
  destruct (FR1 eq_refl) as (Hc & Hp & _). split; assumption.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis EFF : GrantBContracts.tb_reac_headamp_tx_effective_spec B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of LLVMFEntrySchedTurnDefs.v at this section's asyms, meter and laws. This lane's own
   names (gslots_turn, gtregs, shr, G_sh, BxL, Bsp0, stk96, G_A, rs_A) take none of B, MT, LAWS. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).
#[local] Notation gtab_obj := (gtab_obj B).
#[local] Notation obj_gtab := (obj_gtab B).


(* The call of reac_headamp_tx_effective on the emitted cell: 0x81c18 .. 0x81c1c. *)
Lemma segC : seg_C_ok B MT POST.
Proof.
  intros m HTCr cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & c & p & v & T' & HR & R10 & R11 & R12 & R20).
  pose proof HR as (HT & Hm & Hsch & Hnx & Htab & Hlus & Hus & Fc & Fp & Fv).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  pose proof HT as (HTB & Hi & R21).
  pose proof HTB as (HBD & Hk & Hacc & Hbl & Hn & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27 & _).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof Htab as (Hint & Ht0 & HTl & _).
  destruct (segC_cp (c_pl cx) t i T us c p v T' Ht0 Hsch Hnx) as (Hc48 & Hp3).
  pose proof asan_consts as (C1 & _).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (GS : GE_STK = 32768) by reflexivity.
  pose proof HB as ((HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & _) & _).
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
    by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  (* the run 0x81c18 .. 0x81c1c writes no memory: the call alone *)
  assert (HS : st_ok_pi SEGS VAL E (mkSS GP_eff sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_eff ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E) by (subst E; apply gagree0).
  clear HE.
  paj_run_tok RUN HS HJ SHOK Bsp0.
  { apply awr_ok_nil. }
  lazymatch goal with HFx : frame_of E _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ =>
    rename HFx into HFr1 end.
  (* the state at the callee's entry: ra, a0 .. a2 and the registers the run kept *)
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
    rename HSx into HSc;
    prreg HSc (1%bv : bv 5) Q1; prreg HSc (10%bv : bv 5) Q10; prreg HSc (11%bv : bv 5) Q11;
    prreg HSc (12%bv : bv 5) Q12;
    pose proof (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
      HSc HAE ltac:(vm_compute; reflexivity)) as QR;
    cbn [ms_regs restrict] in QR;
    rewrite (st_ok_restrict_mkst _ _ _ _ _ HSc eq_refl); cbn [ss_pc setpc];
    rewrite pa_sigma_reac_headamp_tx_effective;
    assert (HKA : forall a, aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a; apply aview_eq_of; apply HFr1; intros (r & Hr & _); destruct Hr);
    rename msX into msc; remember mdX as mdc eqn:Hmdc
  end.
  assert (Hra : getr (ms_regs msc) 1 = w64 (BASE + GP_effr)) by (rewrite Q1; reflexivity).
  rewrite (EE 10%nat 10%bv eq_refl), R10 in Q10.
  rewrite (EE 11%nat 11%bv eq_refl), R11 in Q11.
  rewrite (EE 12%nat 12%bv eq_refl), R12 in Q12.
  assert (Usp : spZ (ms_regs msc) = c_sp1 cx).
  { unfold spZ. rewrite (QR 2%bv ltac:(cbv; tauto)), G2. apply unsigned_lit_small. lia. }
  assert (Us0 : s0Z (ms_regs msc) = spZ (c_regs cx)).
  { unfold s0Z. rewrite (QR 8%bv ltac:(cbv; tauto)), G8. apply unsigned_lit_small. lia. }
  pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & J9 & _).
  assert (HSV' : gsaved cx W3 msc).
  { destruct HSV as (S8 & S16). split.
    - rewrite <- S8. apply rdword_ext. intros kk Hkk. apply HKA.
    - intros j Hj. rewrite <- (S16 j Hj). apply rdword_ext. intros kk Hkk. apply HKA. }
  (* the call chain the callee is handed: the entry function's own frame (LLVMFEntrySeat.ge_achain) *)
  assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem msc)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
  { apply (achain_ly_top (c_ly cx)); [destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
    eapply (ge_achain B MT cx HB).
    - intros a Ha. apply J9; lia.
    - exact (proj1 HSV').
    - pose proof (proj2 HSV' 0 ltac:(lia)) as S0.
      replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S0 by lia.
      rewrite S0. reflexivity.
    - lia. }
  (* the table the callee reads: its bytes as LAY_TX names them *)
  assert (HOBJ : obj_at SEGS (mrestrict (w_H W3) (ms_mem msc)) t HeadampLayout.LAY_TX (HeadampLayout.tx_vals T')).
  { apply (gtab_obj cx ly3 S3 W3 msc). eapply gtab_keep; [exact Htab|]. intros j Hj. apply HKA. }
  assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { dm (c_sp1 cx) 32. dm (spZ (c_regs cx)) 16. dm (c_sp1 cx - spZ (c_regs cx)) 16. lia. }
  pose proof (pa_base_lo (L := grant_listing)) as HBlo. rewrite IMG_LO_B_val in HBlo.
  pose proof pa_B_ok as HBok.
  (* the callee's contract (GrantBContracts.tb_reac_headamp_tx_effective_spec) in the caller's journal *)
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W3 (ms_regs msc) (ms_mem msc) _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
      (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 mdc k STK_reac_headamp_tx_effective [] 0
      (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs msc) 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         getr regs' 10 = w64 (HeadampModel.eff T' t c p) /\
         (t <> 0 -> obj_at SEGS (mrestrict (w_H W3) mem') t HeadampLayout.LAY_TX (HeadampLayout.tx_vals T'))) HJ).
    - rewrite Usp. lia.
    - exact Ho16.
    - lia.
    - unfold STK_reac_headamp_tx_effective, ESTACK. lia.
    - unfold STK_reac_headamp_tx_effective, ESTACK. lia.
    - rewrite (QR 3%bv ltac:(cbv; tauto)), G3. exact Hgp0.
    - rewrite (QR 4%bv ltac:(cbv; tauto)), G4. exact Htp0.
    - reflexivity.
    - rewrite Hra. apply ret_ok_codeptr_v; [unfold GP_effr; lia | reflexivity].
    - rewrite Hra. unfold w64, GP_effr. rewrite unsigned_lit_small; lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      rewrite Us0. exact HCH.
    - (* tx = t is the table, a live block of the allocator (the cut's gtab), so t <> 0 and the
         contract's block case holds: In (t, TX_SIZE) (ablocks ..) and the bytes LAY_TX names *)
      intros Hpre.
      exact (EFF ly3 S3 W3 (ms_regs msc) (ms_mem msc) mdc (gch cx) t c p T' Hpre Q10 Q11 Q12
        ltac:(lia) ltac:(lia) HTl (or_intror (conj Hint HOBJ))).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HQ).
  destruct HQ as (-> & -> & -> & Q10' & Hobj).
  specialize (Hobj ltac:(lia)).
  rewrite Z.add_0_r in HJ2.
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
  assert (QP : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
               getr regs2 r0 = getr (ms_regs ms3) r0).
  { intros r0 Hr0. rewrite <- (QR r0 Hr0).
    cbv [In] in Hr0; repeat (destruct Hr0 as [<- | Hr0];
      [lazymatch goal with |- getr _ ?r = _ =>
         let z := eval vm_compute in (bv_unsigned r) in exact (HP z ltac:(unfold acallee_saved; lia)) end |]);
    destruct Hr0. }
  (* the bytes the turn tracks are kept: the callee's footprint is empty, so it writes only its stack
     window below s1 *)
  assert (HKall : forall a, gtracked cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Htr. assert (Ha : 0 <= a < 2 ^ 64) by (eapply gtracked_rng; eauto; lia).
    rewrite <- (HKA a).
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K9 & K10 & _ & K12 & _).
    destruct Htr as [Hs | [(b & n & Hin & Hb) | [Hf | Hsh]]].
    - apply K9; [lia | unfold STK_reac_headamp_tx_effective, ESTACK; lia].
    - assert (Hin3 : In (b, n) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_app_iff; left; exact Hin).
      replace a with (b + (a - b)) by lia. apply (K10 b n (a - b)); [exact Hin3 | exact Hin3 | lia | apply inFP_nil].
    - apply (K12 GE_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, fsb4; lia | apply inFP_nil].
    - apply (K12 GE_CID fp a Hfin); [|apply inFP_nil].
      right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA, fsb4. change (1024 / 8) with 128.
      rewrite <- HSH. lia. }
  apply (HTCr cx fp k acc ly3 S3 W3 (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfr HMLE).
  exists i, t, T, us, c, p, v, T'.
  split; [|split; [exact Q10' | exact (eq_trans (QP 20%bv ltac:(cbv; tauto)) R20)]].
  split.
  { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
      | cbn [ms_pc_val mkst]; exact Hra | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | repeat split; apply QP; cbv; tauto | exact Hi | exact (eq_trans (QP 21%bv ltac:(cbv; tauto)) R21)
      | intros a Htr _; exact (HKall a Htr) | | exact GSH_turn_len ].
    intros j Hj. cbn [ms_mem mkst]. rewrite HKall; [exact (HSHW j Hj)|].
    pose proof GSH_turn_len as GL. unfold GE_NSH in GL. rewrite GL in Hj.
    right; right; right. lia. }
  split; [exact Hm|]. split; [exact Hsch|]. split; [exact Hnx|].
  split; [exact (obj_gtab cx ly3 S3 W3 (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS)) t T' Hint Ht0 HTl Hobj)|].
  split; [exact Hlus|].
  split.
  { eapply gfarr_keep; [exact Hus|]. intros a Ha. rewrite Hlus in Ha. cbn [ms_mem mkst]. apply HKall.
    right; right; left. unfold GO_UNSET in Ha. lia. }
  unfold gfb in *. cbn [ms_mem mkst].
  split; [rewrite HKall; [exact Fc | right; right; left; unfold GO_CH; lia]|].
  split; [rewrite HKall; [exact Fp | right; right; left; unfold GO_PAR; lia]|].
  rewrite HKall; [exact Fv | right; right; left; unfold GO_VAL; lia].
Qed.


End c.
End b.
End a.
