(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 189 of its 230 lines of code are new or changed and 2648 lines of the source are left out. *)
(* fuzz_recv on image A: the piece RV_AT_MEMSET1 of its walk (lib/A/Prog/fuzz_recv_defs.v), the lemma rv_m1_ok.
   - +0xf4: the call of checked_memset (buf + s2, 0, s4 - s2), the chunk's zero padding [buf + clen, buf + rv_o),
     lifted onto the invariant by lib/A/Prog/fuzz_recv_kit2.v rv_intrin; the padding lies past the chunk, so the
     buffer still holds the chunk (rv_cmem);
   - +0xf8: s4 += 36; +0xfc `bltu s0, s4`:
     * len < s4 + 36: the jump to the epilogue +0x23c, where RV_RET takes over (the Post by RV_CPOST: a0 := s2,
       the chunk length);
     * else +0x100..+0x10c (s5 := 36, s6 := 2, s7 := -1, s8 := 125) to the loop head +0x110, where RV_LOOP takes
       over with s4 = rv_o + 36.
   The runs from the fresh state ss_f8 write no byte (the only region is the frame, with no write window).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_c fuzz_recv_defs fuzz_recv_kit fuzz_recv_kit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
#[local] Abbreviation lit_of_word := lib.Reusable.YP0m.lit_of_word.

(* a register of a symbolic state, as the denotation of its value *)
Local Ltac m1_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

(* the run's write permission: the frame region has no write window *)
Local Ltac m1_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia |]);
  apply awr_ok_x_nil.

(* the run kept every byte (YC4b.v kept_of_frame with no window) *)
Local Ltac m1_kept sg HFr UN :=
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ : Z => False) HFr
    ltac:(let b := fresh in let wlo := fresh in let whi := fresh in let a := fresh in
          let Hin := fresh in let Hr := fresh in let Hq := fresh in
          intros b wlo whi a Hin Hr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]);
          destruct Hin)) as UN.

(* chain a run's kept bytes and growth onto those since the call's return *)
Local Ltac m1_fold UN UNk HGc HG :=
  lazymatch type of UNk with forall a, _ -> _ -> aview ?sg ?H ?mN a = aview _ _ ?mO a =>
    lazymatch type of UN with forall a, _ -> _ -> aview _ _ mO a = aview _ _ ?m0 a =>
      let UN' := fresh "UN" in
      assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview sg H mN a = aview sg H m0 a)
        by (let a := fresh in let Ha := fresh in let Hz := fresh in
            intros a Ha Hz; rewrite (UNk _ Ha Hz); exact (UN _ Ha Hz));
      clear UN UNk; rename UN' into UN end end;
  lazymatch type of HG with mem_grows _ ?mN =>
    lazymatch type of HGc with mem_grows ?m0 _ =>
      let HG' := fresh "HGc" in
      assert (HG' : mem_grows m0 mN) by (eapply mem_grows_trans; [exact HGc | exact HG]);
      clear HGc HG; rename HG' into HGc end end.

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
Hypothesis TL : PALib B.
Hypothesis MEMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Notation W := (c_W c).
#[local] Notation memc := (c_memc c).

(* the chunk the call hands out: its length at most 4096 *)
Lemma m1_wf : nk_next (c_bs c) < nk_n_chunks (c_bs c) -> 0 <= rv_clen c <= 4096.
Proof.
  intros Hnx. pose proof HC as (_ & _ & WF & _).
  destruct WF as (Wnc & Wnx & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wcl & _).
  pose proof (Wcl (nk_next (c_bs c)) ltac:(lia)) as Hl.
  unfold rv_clen. unfold NL_CHUNKS, NL_CHUNK_MAX in *. lia.
Qed.

Lemma m1_o : 0 <= rv_clen c <= 4096 -> rv_clen c <= rv_o c <= 4096 /\ rv_o c <= rv_clen c + 3.
Proof. intros H. unfold rv_o. lia. Qed.

(* an atom register of a fresh state is the machine register *)
Lemma m1_atom : forall regs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (rv_E c regs) (SOff n 0) = getr regs r.
Proof.
  intros regs n r Hn Hr. cbn [sv_denot]. rewrite (rv_E_reg c regs n r Hn Hr), Z.add_0_r. apply lit_of_word.
Qed.

(* rv_cmem moves with the bytes *)
Lemma m1_cmem_eq : forall mem mem', rv_clen c <= rv_len c ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  rv_cmem c mem -> rv_cmem c mem'.
Proof.
  intros mem mem' Hcl U (C1 & C2 & C3 & C4).
  destruct (rv_pre_facts SK B TL c HC) as (Pb0 & Plen & Pamr & _).
  pose proof asan_consts as (_ & _ & K3 & K4 & K5).
  assert (Bb : rv_buf c + rv_len c <= 2 ^ 47) by (unfold amem_range in Pamr; destruct Pamr as [H|[_ H]]; lia).
  split; [|split; [|split]].
  - intros i Hi. rewrite U by (lia || tauto). exact (C1 i Hi).
  - intros i Hi. rewrite U by (lia || tauto). exact (C2 i Hi).
  - apply (val_mem_kept (w_H W) mem mem'); [|exact C3].
    intros k Hk. cbn in Hk. apply U; [unfold LA_G_NL, NK_NEXT; lia | tauto].
  - apply (val_mem_kept (w_H W) mem mem'); [|exact C4].
    intros k Hk. cbn in Hk. apply U; [unfold LA_G_NL, NK_MISUSE; lia | tauto].
Qed.

(* THE PIECE: the call of checked_memset at +0xf4, then +0xf8..+0xfc and the exit to +0x23c or the loop head *)
Theorem rv_m1_ok : RV_RET SK B c -> RV_LOOP SK B c -> RV_CPOST SK B c -> RV_AT_MEMSET1 SK B c.
Proof.
intros HRT HLP HCP regs mem md HI HCM Hnx R1 R10 R11 R12 HCR R20.
pose proof HC as ((_ & HGX & _) & _).
destruct (rv_pre_facts SK B TL c HC) as (Pb0 & Plen & Pamr & Pbg & Pbf & _ & _ & _ & _).
destruct (rv_sp_bounds SK B c HC) as (Hceil & Hslo & Hshi & H47 & H16 & HXO).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof (m1_wf Hnx) as Hcl.
destruct (m1_o Hcl) as (Ho1 & Ho2).
destruct HCR as (H8 & H9 & H18 & H19).
assert (Bb : rv_buf c + rv_len c <= 2 ^ 47) by (unfold amem_range in Pamr; destruct Pamr as [H|[_ H]]; lia).
unfold apart_gnl in Pbg. unfold apart_frame in Pbf. fold (rv_sp c) in Pbf.
unfold NL_CHUNK_MAX in Plen.
(* the call of checked_memset *)
unfold rv_goal. eapply SRr_bind.
{ exact (rv_intrin SK B LAWS TL c HC OSet (pa_sigma LS___asan_memset) MEMSET regs mem md (rv_buf c + rv_clen c) 0
    (rv_o c - rv_clen c) (Z_to_bv 64 (BASE + RV_F8)) HI R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia) R1
    ltac:(apply ret_ok_codeptr_v; [unfold RV_F8, AF_fuzz_recv; lia | reflexivity]) I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hset & Hout).
destruct (rv_preserved regs regs2 HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P25 & P26 & P27).
(* the buffer after the padding *)
assert (CM2 : rv_cmem c mem2).
{ destruct HCM as (M1 & M2 & M3 & M4).
  split; [|split; [|split]].
  - intros i Hi. rewrite Hout; [exact (M1 i Hi) | lia | lia |].
    clear - Pbf Hi Hcl Plen. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
  - intros i Hi. destruct (Z_lt_le_dec i (rv_clen c)) as [Ha|Ha]; [|destruct (Z_lt_le_dec i (rv_o c)) as [Hb|Hb]].
    + rewrite Hout; [exact (M2 i Hi) | lia | lia |].
      clear - Pbf Hi. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
    + replace (rv_buf c + i) with (rv_buf c + rv_clen c + (i - rv_clen c)) by ring.
      rewrite (Hset (i - rv_clen c)) by lia. discriminate.
    + rewrite Hout; [exact (M2 i Hi) | lia | lia |].
      clear - Pbf Hi. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
  - apply (val_mem_kept (w_H W) mem mem2); [|exact M3].
    intros k Hk. cbn in Hk. apply Hout.
    + unfold LA_G_NL, NK_NEXT. lia.
    + unfold LA_G_NL, NK_NEXT, NK_SIZE in *. lia.
    + clear - Hk Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_NEXT in *. lia.
  - apply (val_mem_kept (w_H W) mem mem2); [|exact M4].
    intros k Hk. cbn in Hk. apply Hout.
    + unfold LA_G_NL, NK_MISUSE. lia.
    + unfold LA_G_NL, NK_MISUSE, NK_SIZE in *. lia.
    + clear - Hk Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_MISUSE in *. lia. }
clear Hset Hout HCM.
(* the fresh state at +0xf8 *)
assert (H19' : getr regs2 19 = w64 SHADOW_OFF) by (rewrite P19; exact H19).
pose proof (rv_st_ok SK B c HC regs2 mem2 md2 RV_F8 [] [] HI2 H19' eq_refl ltac:(constructor) I I I) as HS.
pose proof (rv_E_env c regs2) as HEI.
assert (SHOK : sh_ok SEGS rv_Bx [] (rv_E c regs2) (mrestrict (w_H W) mem2)) by constructor.
pose proof HI2 as (HJ & _).
assert (E8 : ew (rv_E c regs2) 8 = Z_to_bv 64 (rv_len c))
  by (rewrite (rv_E_reg c regs2 8 8%bv) by (lia || reflexivity); rewrite P8; exact H8).
assert (E20 : ew (rv_E c regs2) 20 = Z_to_bv 64 (rv_o c))
  by (rewrite (rv_E_reg c regs2 20 20%bv) by (lia || reflexivity); rewrite P20; exact R20).
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
  by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) mem2)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS (c_G c) HGX (c_XO c) (c_OUT c)) as RUN.
pose proof (paj_run_to_x SK B LAWS (c_G c) HGX (c_XO c) (c_OUT c)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* +0xf8 s4 += 36, the branch +0xfc *)
paj_run_tok RUN HS HJ SHOK rv_span; [m1_awr |].
m1_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. m1_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
psrr_branch_tok RUN BR HS SHOK rv_span;
  rewrite branch_ltu_U, (U_atom _ 8 (rv_len c) E8 ltac:(lia)), (U_atom_off _ 20 (rv_o c) 36 E20 ltac:(lia) ltac:(lia))
    in Hc.
- (* len < s4 + 36: the epilogue *)
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rv_span RV_RT; [m1_awr |].
  m1_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. m1_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (HI3 : rv_inv SK B c rg mm mdq);
    [ apply (rv_inv_step SK B TL c HC regs2 mem2 md2 rg mm mdq (fun _ => False) HI2 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN
      | intros ?a []
      | intros ?a ?Hp; exact (apresent_grows _ _ _ _ HGc Hp)
      | m1_reg HS (2%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (3%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (4%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (26%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (27%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity) ]
    | ];
    assert (CM3 : rv_cmem c mm) by (apply (m1_cmem_eq mem2 mm); [lia | exact UN | exact CM2]);
    assert (A18 : getr rg 18 = w64 (rv_clen c))
      by (m1_reg HS (18%bv : bv 5) Q; rewrite Q, (m1_atom regs2 18 18%bv), P18 by (lia || reflexivity); exact H18);
    assert (A19 : getr rg 19 = w64 SHADOW_OFF)
      by (m1_reg HS (19%bv : bv 5) Q; rewrite Q, (m1_atom regs2 19 19%bv), P19 by (lia || reflexivity); exact H19);
    refine (HRT rg mm mdq HI3 A19 _);
    intros regs4 H4; apply (HCP rg mm mdq regs4 HI3 CM3 Hnx); rewrite H4; exact A18
  end.
- (* len >= s4 + 36: +0x100..+0x10c, the loop head with s4 = rv_o + 36 *)
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rv_span RV_LP; [m1_awr |].
  m1_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. m1_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (HI3 : rv_inv SK B c rg mm mdq);
    [ apply (rv_inv_step SK B TL c HC regs2 mem2 md2 rg mm mdq (fun _ => False) HI2 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN
      | intros ?a []
      | intros ?a ?Hp; exact (apresent_grows _ _ _ _ HGc Hp)
      | m1_reg HS (2%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (3%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (4%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (26%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity)
      | m1_reg HS (27%bv : bv 5) Q; rewrite Q; apply m1_atom; (lia || reflexivity) ]
    | ];
    assert (CM3 : rv_cmem c mm) by (apply (m1_cmem_eq mem2 mm); [lia | exact UN | exact CM2]);
    assert (A20 : getr rg 20 = w64 (rv_o c + 36))
      by (m1_reg HS (20%bv : bv 5) Q; rewrite Q, denot_lit_U, (U_atom_off _ 20 (rv_o c) 36 E20) by lia; reflexivity);
    refine (HLP (rv_o c + 36) rg mm mdq HI3 CM3 Hnx ltac:(lia) _ A20);
    split; [|split; [|split]];
    [ m1_reg HS (8%bv : bv 5) Q; rewrite Q, (m1_atom regs2 8 8%bv), P8 by (lia || reflexivity); exact H8
    | m1_reg HS (9%bv : bv 5) Q; rewrite Q, (m1_atom regs2 9 9%bv), P9 by (lia || reflexivity); exact H9
    | m1_reg HS (18%bv : bv 5) Q; rewrite Q, (m1_atom regs2 18 18%bv), P18 by (lia || reflexivity); exact H18
    | m1_reg HS (19%bv : bv 5) Q; rewrite Q, (m1_atom regs2 19 19%bv), P19 by (lia || reflexivity); exact H19 ]
  end.
Qed.
End w.
