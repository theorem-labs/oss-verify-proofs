(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 137 of its 178 lines of code are new or changed and 268 lines of the source are left out. *)
(* talk on image A: the epilogue +0xb4 (a0 := a1, the restores of ra and s0..s11 from the frame, sp += 144, ret) from
   a machine state that satisfies tk_inv, and the contract's apost at the ret: TK_RET of lib/A/Prog/talk_defs.v.
   Every exit of talk goes through +0xb4, so this file is the only place the walk builds the apost.
   - tk_ret_ok: the run of the fresh state tk_ss_rt to the `ret` (+0xf0), then the apost at the write set (the model
     block and the live buffers lie in low or high memory, so lib/A/Prog/fuzz_recv_ret.v's apost_leaf2 applies).
     The run writes no byte (the frame region has no write window), so the memory at the ret is the memory at +0xb4.
   - tk_post_of: talk_apost at an exit from what the pieces carry there: the model block's list and its fields
     (tk_mres), the code in a1, the attributes, and the buffers (tk_bufs). The Post's mbs / kbs / req are the call's
     (`abytes` names one list at an address).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_ret talk_c talk_defs talk_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).

(* THE EPILOGUE +0xb4 and the apost *)
Lemma tk_ret_ok : TK_RET SK B c.
Proof.
  intros regs mem md HI H23 HQ.
  unfold tk_goal.
  pose proof HC as ((HJ0 & HGX & _ & Hret & _) & _).
  unfold YK0s.ret_ok in Hret.
  pose proof HI as (HJ & Hfd & Hfs & Hsp & Hgp & Htp & _ & UN & PR).
  destruct (tk_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  (* the atoms 32..44: the entry ra, s0, s1, s2..s11 *)
  pose proof (tk_E_ext c regs []) as EX.
  assert (X0 : ew (tk_E c regs []) 32 = getr regs0 1) by exact (EX 0%nat ltac:(lia)).
  assert (X1 : ew (tk_E c regs []) 33 = getr regs0 8) by exact (EX 1%nat ltac:(lia)).
  assert (X2 : ew (tk_E c regs []) 34 = getr regs0 9) by exact (EX 2%nat ltac:(lia)).
  assert (X3 : ew (tk_E c regs []) 35 = getr regs0 18) by exact (EX 3%nat ltac:(lia)).
  assert (X4 : ew (tk_E c regs []) 36 = getr regs0 19) by exact (EX 4%nat ltac:(lia)).
  assert (X5 : ew (tk_E c regs []) 37 = getr regs0 20) by exact (EX 5%nat ltac:(lia)).
  assert (X6 : ew (tk_E c regs []) 38 = getr regs0 21) by exact (EX 6%nat ltac:(lia)).
  assert (X7 : ew (tk_E c regs []) 39 = getr regs0 22) by exact (EX 7%nat ltac:(lia)).
  assert (X8 : ew (tk_E c regs []) 40 = getr regs0 23) by exact (EX 8%nat ltac:(lia)).
  assert (X9 : ew (tk_E c regs []) 41 = getr regs0 24) by exact (EX 9%nat ltac:(lia)).
  assert (X10 : ew (tk_E c regs []) 42 = getr regs0 25) by exact (EX 10%nat ltac:(lia)).
  assert (X11 : ew (tk_E c regs []) 43 = getr regs0 26) by exact (EX 11%nat ltac:(lia)).
  assert (X12 : ew (tk_E c regs []) 44 = getr regs0 27) by exact (EX 12%nat ltac:(lia)).
  clear EX.
  (* the fresh state tk_ss_rt *)
  pose proof (tk_st_ok SK B LV c HC regs mem md [] TP_RT [] [tk_fr] [] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_fr_ok SK B c HC regs mem md [] HI) | apply Forall_nil])
    ltac:(cbn; repeat first [exact I | split]) I) as HS.
  pose proof (tk_E_env c regs []) as HEI.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs []) (mrestrict (w_H W) mem)) by constructor.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  (* +0xb4 .. +0xf0: a0 := a1, the restores, sp += 144; the run stops at the ret *)
  paj_run_tok RUN HS HJ SHOK tk_span.
  - (* the frame region has no write window *)
    intros a (r & Hin & Hr). unfold tk_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<-|[]].
    unfold tk_fr in Hr. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
  - lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
    (* the run wrote no byte *)
    assert (Hm : ms_mem ms1 = mem).
    { eapply frame_of_read_only; [|exact HF]. vm_compute. reflexivity. }
    rewrite Hm in HJ.
    prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
    prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
    prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
    prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20.
    prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
    prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
    prreg HS (27%bv : bv 5) R27.
    (* the callee-saved registers: sp = entry sp, gp / tp as at the call, s0..s11 from the frame *)
    assert (HP : aregs_preserved regs0 (ms_regs ms1)).
    { assert (ZB : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> getr (ms_regs ms1) rr = getr regs0 rr ->
                     getr (ms_regs ms1) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z))
        by (intros rr z -> Hq; exact Hq).
      intros r Hr. unfold acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      clear Hr.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]].
      - apply (ZB 2%bv 2 ltac:(apply bv_eq; reflexivity)).
        rewrite R2, (tk_E_reg c regs [] 2 2%bv), Hsp by (lia || reflexivity). unfold w64.
        rewrite unsigned_lit_small by lia.
        rewrite Z.sub_add. unfold tk_sp, spZ. apply Z_to_bv_bv_unsigned.
      - apply (ZB 3%bv 3 ltac:(apply bv_eq; reflexivity)).
        rewrite R3, (tk_E_reg c regs [] 3 3%bv) by (lia || reflexivity). exact Hgp.
      - apply (ZB 4%bv 4 ltac:(apply bv_eq; reflexivity)).
        rewrite R4, (tk_E_reg c regs [] 4 4%bv) by (lia || reflexivity). exact Htp.
      - apply (ZB 8%bv 8 ltac:(apply bv_eq; reflexivity)). rewrite R8, X1. reflexivity.
      - apply (ZB 9%bv 9 ltac:(apply bv_eq; reflexivity)). rewrite R9, X2. reflexivity.
      - apply (ZB 18%bv 18 ltac:(apply bv_eq; reflexivity)). rewrite R18, X3. reflexivity.
      - apply (ZB 19%bv 19 ltac:(apply bv_eq; reflexivity)). rewrite R19, X4. reflexivity.
      - apply (ZB 20%bv 20 ltac:(apply bv_eq; reflexivity)). rewrite R20, X5. reflexivity.
      - apply (ZB 21%bv 21 ltac:(apply bv_eq; reflexivity)). rewrite R21, X6. reflexivity.
      - apply (ZB 22%bv 22 ltac:(apply bv_eq; reflexivity)). rewrite R22, X7. reflexivity.
      - apply (ZB 23%bv 23 ltac:(apply bv_eq; reflexivity)). rewrite R23, X8. reflexivity.
      - apply (ZB 24%bv 24 ltac:(apply bv_eq; reflexivity)). rewrite R24, X9. reflexivity.
      - apply (ZB 25%bv 25 ltac:(apply bv_eq; reflexivity)). rewrite R25, X10. reflexivity.
      - apply (ZB 26%bv 26 ltac:(apply bv_eq; reflexivity)). rewrite R26, X11. reflexivity.
      - apply (ZB 27%bv 27 ltac:(apply bv_eq; reflexivity)). rewrite R27, X12. reflexivity. }
    (* a0 = a1 *)
    assert (HA0 : getr (ms_regs ms1) 10 = getr regs 11).
    { rewrite R10. apply (tk_E_reg c regs [] 11 11%bv); [lia | reflexivity]. }
    clear R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27
      X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12.
    (* the ret: pc := ra = the entry ra *)
    eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    rewrite R1, X0, Hret, Hm.
    eapply (apost_leaf2 SK B LAWS).
    + exact HJ0.
    + apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ.
    + unfold tk_sp in Hlo. exact Hlo.
    + unfold TALK_AK, TALK_AFRAME, ESTACK. lia.
    + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
    + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
    + exact HP.
    + (* the bytes outside the frame window and the write set *)
      intros a Ha Hw HE. exact (UN a Ha Hw HE).
    + exact PR.
    + (* the frame window is present: the journal's stack window holds it *)
      pose proof HJ as (_ & HXO2 & (memS & HJi & _) & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      intros a Ha. apply Hpres. unfold tk_sp in Hlo, Hhi. clear - Ha Hlo Hhi HXO2. lia.
    + (* the write set: the model block and the live buffers lie in low or high memory *)
      intros x Hx. destruct (tk_ewr_facts SK B c HC x Hx) as (_ & _ & [Hq|Hq]);
        [left | right]; unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
    + (* Q: the allocator state and the blocks as at the call, and talk_apost *)
      cbv beta. split; [destruct (tc_Sc c); reflexivity|]. split; [apply Permutation_refl|].
      exact (HQ (ms_regs ms1) HA0).
Qed.

(* THE POST at an exit, from what the pieces carry there: the model block (its list mb, its fields as talk_after
   says), the code in a1 (getr regs2 10 = w64 code after `mv a0, a1`), the attributes acc, the buffers *)
Lemma tk_post_of : forall mem code acc mb,
  amodel_at SEGS (rdW W mem) (tk_m c) mb -> tk_mres c mb ->
  code = talk_rc_model (tk_K0 c) -> acc = talk_attrs (tk_K0 c) -> tk_bufs c mem acc ->
  forall regs2, getr regs2 10 = w64 code -> talk_apost SEGS regs0 (rdW W memc) regs2 (rdW W mem).
Proof.
  intros mem code acc mb HM Hres Hrc Hacc HB regs2 H10.
  pose proof HC as (_ & HMD & _ & HNK & _ & HRQ & HRL & _).
  intros mbs0 kbs0 req0 HM0 HN0 HR0 HL0.
  assert (E1 : mbs0 = tc_mbs c).
  { destruct HM0 as ((H0 & _) & L0). destruct HMD as ((H1 & _) & L1).
    apply (abytes_unique SEGS (rdW W memc) (aarg regs0 0)); [exact H0 | exact H1 | lia]. }
  assert (E2 : kbs0 = tc_kbs c).
  { destruct HN0 as ((H0 & _) & L0). destruct HNK as ((H1 & _) & L1).
    apply (abytes_unique SEGS (rdW W memc) LA_G_NL); [exact H0 | exact H1 | lia]. }
  assert (E3 : req0 = tc_req c) by (apply (abytes_unique SEGS (rdW W memc) (aarg regs0 1)); [exact HR0 | exact HRQ | lia]).
  subst mbs0 kbs0 req0. cbv zeta. fold (tk_K0 c). rewrite <- Hacc.
  destruct HB as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [rewrite H10, Hrc; reflexivity|].
  split; [exists mb; exact (conj HM Hres)|].
  split; [exact B3|]. split; [exact B4|].
  split.
  { intros Hn H0 H1 kb (Ka & Kb & Kn) Kl. split; [exact Ka|]. split; [exact Kb|].
    intros i Hi. rewrite <- (Kn i Hi). apply (mbyte_of_aview SEGS (w_H W) (w_H W) memc mem).
    apply (B5 Hn H0 H1). unfold tk_kn in *. lia. }
  split.
  { intros Hn H0 H1 ab (Ka & Kb & Kn) Kl. split; [exact Ka|]. split; [exact Kb|].
    intros i Hi. rewrite <- (Kn i Hi). apply (mbyte_of_aview SEGS (w_H W) (w_H W) memc mem).
    apply (B6 Hn H0 H1). unfold tk_an in *. lia. }
  split; [exact B1 | exact B2].
Qed.
End w.
