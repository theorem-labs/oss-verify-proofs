(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* fuzz_recv on image A: the piece RV_AT_MEMCPY of its walk (lib/A/Prog/fuzz_recv_defs.v), the lemma rv_cp_ok.
   - +0xd0: the call of checked_memcpy (buf, g + 4096 * next, the chunk length s2), lifted onto the invariant by
     lib/A/Prog/fuzz_recv_kit2.v rv_intrin: the source [g + 4096 * next, + s2) is g_nl's chunk, below the
     allocator's ceiling and apart from the buffer; after the call the buffer holds the chunk (rv_cmem);
   - +0xd4..+0xe0: s4 := ((s2 + 3) >> 2) << 2 (the chunk length rounded up to 4), then `bltu s4, s0`;
   - both arms (+0xe4 s4 := len when s4 is not below len) run +0xe8..+0xf0 to the call of checked_memset at +0xf4
     with a0 = buf + s2, a1 = 0, a2 = s4 - s2, where RV_AT_MEMSET1 takes over. Since the chunk length is at most
     4096 and len at least 4096, s4 is the rounded length rv_o on both arms.
   The runs from the fresh state ss_d4 write no byte (the only region is the frame, with no write window).
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
#[local] Abbreviation zcanon_small := lib.Reusable.YP0m.zcanon_small.
#[local] Abbreviation zcanon_wrap := lib.Reusable.YP0m.zcanon_wrap.
#[local] Abbreviation lit_of_word := lib.Reusable.YP0m.lit_of_word.

(* a register of a symbolic state, as the denotation of its value *)
Local Ltac cp_reg HS r Hr :=
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
Local Ltac cp_awr :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons; [intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia |]);
  apply awr_ok_x_nil.

(* the run kept every byte (YC4b.v kept_of_frame with no window) *)
Local Ltac cp_kept sg HFr UN :=
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ : Z => False) HFr
    ltac:(let b := fresh in let wlo := fresh in let whi := fresh in let a := fresh in
          let Hin := fresh in let Hr := fresh in let Hq := fresh in
          intros b wlo whi a Hin Hr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]);
          destruct Hin)) as UN.

(* chain a run's kept bytes and growth onto those since the call's return *)
Local Ltac cp_fold UN UNk HGc HG :=
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
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Notation W := (c_W c).
#[local] Notation memc := (c_memc c).

(* the chunk the call hands out: next < n_chunks <= 64, its length at most 4096 *)
Lemma cp_wf : nk_next (c_bs c) < nk_n_chunks (c_bs c) ->
  0 <= nk_next (c_bs c) < 64 /\ 0 <= rv_clen c <= 4096.
Proof.
  intros Hnx. pose proof HC as (_ & _ & WF & _).
  destruct WF as (Wnc & Wnx & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wcl & _).
  pose proof (Wcl (nk_next (c_bs c)) ltac:(lia)) as Hl.
  unfold rv_clen. unfold NL_CHUNKS, NL_CHUNK_MAX in *. lia.
Qed.

Lemma cp_o : 0 <= rv_clen c <= 4096 -> rv_clen c <= rv_o c <= 4096 /\ rv_o c <= rv_clen c + 3.
Proof. intros H. unfold rv_o. lia. Qed.

(* s4 after +0xdc: ((s2 + 3) >>w 2) << 2 is the rounded length *)
Lemma cp_U_o : forall E, ew E 18 = Z_to_bv 64 (rv_clen c) -> 0 <= rv_clen c <= 4096 ->
  U E (SAlu ALU_SLL (SAluw ALU_SRL (SOff 18 3) (SLit 2)) (SLit 2)) = rv_o c.
Proof.
  intros E H18 Hcl.
  rewrite U_SAlu, (U_of_S E (SAluw ALU_SRL (SOff 18 3) (SLit 2))), S_SAluw, (U_SOff E 18 3), !U_SLit, H18.
  rewrite unsigned_lit_small by lia. cbn [zalu_raw].
  change (zcanon 2) with 2. change (2 mod 2 ^ 32) with 2. change (Z.land 2 31) with 2. change (Z.land 2 63) with 2.
  rewrite (zcanon_small (rv_clen c + 3)) by lia.
  rewrite (Z.mod_small (rv_clen c + 3) (2 ^ 32)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  rewrite swrap32_id by lia.
  rewrite <- (zcanon_wrap ((rv_clen c + 3) / 4)), (zcanon_small ((rv_clen c + 3) / 4)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  rewrite zcanon_small by lia. unfold rv_o. lia.
Qed.

(* a2 on the clamp arm: len + s2 * -1 *)
Lemma cp_U_sub : forall E l s, 0 <= s <= l -> l < 2 ^ 64 -> U E (SOff 8 0) = l -> U E (SOff 18 0) = s ->
  U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 18 0) (SLit (-1)))) = l - s.
Proof.
  intros E l s Hs Hl H8 H18. rewrite U_SAlu, U_SMd, U_SLit, H8, H18. cbn [zalu_raw zmd_raw].
  unfold zcanon, M64. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite Z.add_mod_idemp_r by lia.
  replace (l + s * (2 ^ 64 - 1)) with (l - s + s * 2 ^ 64) by ring.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* an atom register of a fresh state is the machine register *)
Lemma cp_atom : forall regs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (rv_E c regs) (SOff n 0) = getr regs r.
Proof.
  intros regs n r Hn Hr. cbn [sv_denot]. rewrite (rv_E_reg c regs n r Hn Hr), Z.add_0_r. apply lit_of_word.
Qed.

(* rv_cmem moves with the bytes *)
Lemma cp_cmem_eq : forall mem mem', rv_clen c <= rv_len c ->
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

(* THE PIECE: the call of checked_memcpy at +0xd0, then +0xd4..+0xf0 to the call of checked_memset at +0xf4 *)
Theorem rv_cp_ok : RV_AT_MEMSET1 SK B c -> RV_AT_MEMCPY SK B c.
Proof.
intros HM1 regs mem md HI Hnx R1 R10 R11 R12 HCR Vnx Vmi Hbuf.
pose proof HC as ((_ & HGX & _) & HNK & WF & Hgra & Hghull & _ & _ & _ & _ & _ & _ & _ & Habuf & _).
change (ard SEGS (rdW W memc)) with (aview SEGS (w_H W) memc) in Hgra, Hghull.
destruct (rv_pre_facts SK B TL c HC) as (Pb0 & Plen & Pamr & Pbg & Pbf & _ & Peg & _ & _).
destruct (rv_sp_bounds SK B c HC) as (Hceil & Hslo & Hshi & H47 & H16 & HXO).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (cp_wf Hnx) as (Hnx0 & Hcl).
destruct (cp_o Hcl) as (Ho1 & Ho2).
pose proof HI as (_ & _ & _ & Hsp & _ & _ & _ & _ & _ & UN0 & _).
destruct HCR as (H8 & H9 & H18 & H19).
assert (Bb : rv_buf c + rv_len c <= 2 ^ 47) by (unfold amem_range in Pamr; destruct Pamr as [H|[_ H]]; lia).
unfold apart_gnl in Pbg, Peg. unfold apart_frame in Pbf. fold (rv_sp c) in Pbf. unfold NL_CHUNK_MAX in Plen.
fold (rv_buf c) (rv_len c) in Habuf.
assert (Usp : spZ regs = rv_sp c - 96).
{ unfold spZ. rewrite Hsp. apply unsigned_lit_small.
  clear - Hceil Hslo Hshi H47 HXO C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia. }
(* g_nl's bytes at the call, and at mem for the chunk area *)
assert (Gdef : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> aview SEGS (w_H W) memc a <> None).
{ intros a Ha. destruct HNK as [[(_ & _ & Hby) _] HL].
  pose proof (Hby (Z.to_nat (a - LA_G_NL)) ltac:(lia)) as Hb.
  replace (LA_G_NL + Z.of_nat (Z.to_nat (a - LA_G_NL))) with a in Hb by lia.
  unfold aview; cbv beta. rewrite Hb. destruct (nth_error (c_bs c) (Z.to_nat (a - LA_G_NL))) eqn:En; [discriminate|].
  apply nth_error_None in En. lia. }
assert (Bdef : forall i, 0 <= i < rv_len c -> aview SEGS (w_H W) memc (rv_buf c + i) <> None).
{ intros i Hi. destruct Habuf as (junk & Hjl & (_ & _ & Hby) & _).
  pose proof (Hby (Z.to_nat i) ltac:(lia)) as Hb.
  replace (rv_buf c + Z.of_nat (Z.to_nat i)) with (rv_buf c + i) in Hb by lia.
  unfold aview; cbv beta. rewrite Hb. destruct (nth_error junk (Z.to_nat i)) eqn:En; [discriminate|].
  apply nth_error_None in En. lia. }
assert (Gk : forall a, LA_G_NL <= a < LA_G_NL + 262144 -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply UN0.
  - unfold LA_G_NL in *. lia.
  - clear - Ha Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL in *. lia.
  - unfold rv_ewr, LA_G_NL, NK_NEXT, NK_MISUSE, NK_SIZE in *. intros [H|[H|[H|H]]]; lia. }
(* the call of checked_memcpy *)
unfold rv_goal. eapply SRr_bind.
{ refine (rv_intrin SK B LAWS TL c HC OCpy (pa_sigma LS___asan_memcpy) MEMCPY regs mem md (rv_buf c)
    (LA_G_NL + NL_CHUNK_MAX * nk_next (c_bs c)) (rv_clen c) (Z_to_bv 64 (BASE + RV_D4)) HI R10 R11 R12
    ltac:(lia) ltac:(lia) ltac:(lia) R1 ltac:(apply ret_ok_codeptr_v; [unfold RV_D4, AF_fuzz_recv; lia | reflexivity]) _).
  unfold NL_CHUNK_MAX in *. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
  split; [|split; [|split; [|split]]].
  - intros a Ha. split.
    + rewrite Gk by lia. apply Gdef. unfold NK_SIZE. lia.
    + rewrite Usp. clear - Ha Hnx0 Hcl Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL in *. lia.
  - unfold NK_SIZE in Pbg. lia.
  - left. unfold LA_G_NL. lia.
  - apply (range_addressable_sub _ _ LA_G_NL NK_SIZE); [|lia|unfold NK_SIZE; lia].
    apply (rv_ra_kept SK B TL c HC regs mem md LA_G_NL NK_SIZE HI); [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia | exact Hgra].
  - intros Hn0. apply (rv_hull_sub _ LA_G_NL NK_SIZE); [|lia|unfold NK_SIZE; lia|exact Hn0].
    apply (rv_hull_kept SK B TL c HC regs mem md LA_G_NL NK_SIZE HI);
      [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia | unfold NK_SIZE; lia | exact Hghull]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hcp & Hout).
destruct (rv_preserved regs regs2 HP2) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P25 & P26 & P27).
(* the buffer after the copy *)
assert (CM2 : rv_cmem c mem2).
{ split; [|split; [|split]].
  - intros i Hi. rewrite (Hcp i Hi). unfold rv_next. apply Gk. unfold NL_CHUNK_MAX. lia.
  - intros i Hi. destruct (Z_lt_le_dec i (rv_clen c)) as [Hc|Hc].
    + rewrite (Hcp i ltac:(lia)), Gk by (unfold NL_CHUNK_MAX; lia). apply Gdef. unfold NL_CHUNK_MAX, NK_SIZE. lia.
    + rewrite Hout; [rewrite Hbuf by lia; exact (Bdef i Hi) | lia | lia |].
      clear - Pbf Hi. unfold ESTACK, FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
  - apply (val_mem_kept (w_H W) mem mem2); [|exact Vnx].
    intros k Hk. cbn in Hk. apply Hout.
    + unfold LA_G_NL, NK_NEXT. lia.
    + unfold LA_G_NL, NK_NEXT, NK_SIZE in *. lia.
    + clear - Hk Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_NEXT in *. lia.
  - apply (val_mem_kept (w_H W) mem mem2); [|exact Vmi].
    intros k Hk. cbn in Hk. apply Hout.
    + unfold LA_G_NL, NK_MISUSE. lia.
    + unfold LA_G_NL, NK_MISUSE, NK_SIZE in *. lia.
    + clear - Hk Hceil Hslo C1a. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK, LA_G_NL, NK_MISUSE in *. lia. }
clear Hcp Hout Gk Gdef Bdef UN0.
(* the fresh state at +0xd4 *)
assert (H19' : getr regs2 19 = w64 SHADOW_OFF) by (rewrite P19; exact H19).
pose proof (rv_st_ok SK B c HC regs2 mem2 md2 RV_D4 [] [] HI2 H19' eq_refl ltac:(constructor) I I I) as HS.
pose proof (rv_E_env c regs2) as HEI.
assert (SHOK : sh_ok SEGS rv_Bx [] (rv_E c regs2) (mrestrict (w_H W) mem2)) by constructor.
pose proof HI2 as (HJ & _).
assert (E8 : ew (rv_E c regs2) 8 = Z_to_bv 64 (rv_len c))
  by (rewrite (rv_E_reg c regs2 8 8%bv) by (lia || reflexivity); rewrite P8; exact H8).
assert (E9 : ew (rv_E c regs2) 9 = Z_to_bv 64 (rv_buf c))
  by (rewrite (rv_E_reg c regs2 9 9%bv) by (lia || reflexivity); rewrite P9; exact H9).
assert (E18 : ew (rv_E c regs2) 18 = Z_to_bv 64 (rv_clen c))
  by (rewrite (rv_E_reg c regs2 18 18%bv) by (lia || reflexivity); rewrite P18; exact H18).
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
  by reflexivity.
assert (HGc : mem_grows (mrestrict (w_H W) mem2) (mrestrict (w_H W) mem2)) by apply mem_grows_refl.
pose proof (paj_run_x SK B LAWS (c_G c) HGX (c_XO c) (c_OUT c)) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* +0xd4..+0xdc, the branch +0xe0 *)
paj_run_tok RUN HS HJ SHOK rv_span; [cp_awr |].
cp_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. cp_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
psrr_branch_tok RUN BR HS SHOK rv_span;
  rewrite branch_ltu_U, (cp_U_o _ E18 Hcl), (U_atom _ 8 (rv_len c) E8 ltac:(lia)) in Hc.
- (* the rounded length is below len *)
  apply Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK rv_span; [cp_awr |].
  cp_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. cp_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (A12 : getr rg 12 = w64 (rv_o c - rv_clen c));
    [ cp_reg HS (12%bv : bv 5) Q; rewrite Q, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (cp_U_o _ E18 Hcl), (U_atom _ 18 (rv_clen c) E18 ltac:(lia)), zcanon_small by lia; reflexivity
    | ];
    assert (A20 : getr rg 20 = w64 (rv_o c));
    [ cp_reg HS (20%bv : bv 5) Q; rewrite Q, denot_lit_U, (cp_U_o _ E18 Hcl); reflexivity | ];
    assert (A10 : getr rg 10 = w64 (rv_buf c + rv_clen c));
    [ cp_reg HS (10%bv : bv 5) Q; rewrite Q, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom _ 9 (rv_buf c) E9 ltac:(lia)), (U_atom _ 18 (rv_clen c) E18 ltac:(lia)), zcanon_small by lia;
      reflexivity
    | ];
    refine (HM1 rg mm mdq _ _ Hnx _ A10 _ A12 _ A20);
    [ apply (rv_inv_step SK B TL c HC regs2 mem2 md2 rg mm mdq (fun _ => False) HI2 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN
      | intros ?a []
      | intros ?a ?Hp; exact (apresent_grows _ _ _ _ HGc Hp)
      | cp_reg HS (2%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (3%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (4%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (26%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (27%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity) ]
    | apply (cp_cmem_eq mem2 mm); [lia | exact UN | exact CM2]
    | cp_reg HS (1%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite (img_env_codeptr _ HEI); reflexivity
    | cp_reg HS (11%bv : bv 5) Q; rewrite Q; reflexivity
    | split; [|split; [|split]];
      [ cp_reg HS (8%bv : bv 5) Q; rewrite Q, (cp_atom regs2 8 8%bv), P8 by (lia || reflexivity); exact H8
      | cp_reg HS (9%bv : bv 5) Q; rewrite Q, (cp_atom regs2 9 9%bv), P9 by (lia || reflexivity); exact H9
      | cp_reg HS (18%bv : bv 5) Q; rewrite Q, (cp_atom regs2 18 18%bv), P18 by (lia || reflexivity); exact H18
      | cp_reg HS (19%bv : bv 5) Q; rewrite Q, (cp_atom regs2 19 19%bv), P19 by (lia || reflexivity); exact H19 ] ]
  end.
- (* the rounded length is not below len: s4 := len, which is the rounded length (4096) *)
  apply Z.ltb_ge in Hc.
  assert (Heq : rv_o c = rv_len c) by lia.
  paj_run_tok RUN HS HJ SHOK rv_span; [cp_awr |].
  cp_kept (@pa_segs _ link_listing PI) HFr UNk. clear HF HFr. cp_fold UN UNk HGc HG. repeat rewrite wvb_collapse in HJ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (A12 : getr rg 12 = w64 (rv_o c - rv_clen c));
    [ cp_reg HS (12%bv : bv 5) Q; rewrite Q, denot_lit_U;
      rewrite (cp_U_sub _ (rv_len c) (rv_clen c)) by
        (lia || exact (U_atom _ 8 (rv_len c) E8 ltac:(lia)) || exact (U_atom _ 18 (rv_clen c) E18 ltac:(lia)));
      rewrite Heq; reflexivity
    | ];
    assert (A20 : getr rg 20 = w64 (rv_o c));
    [ cp_reg HS (20%bv : bv 5) Q; rewrite Q, (cp_atom regs2 8 8%bv), P8, Heq by (lia || reflexivity); exact H8 | ];
    assert (A10 : getr rg 10 = w64 (rv_buf c + rv_clen c));
    [ cp_reg HS (10%bv : bv 5) Q; rewrite Q, denot_lit_U, U_SAlu; cbn [zalu_raw];
      rewrite (U_atom _ 9 (rv_buf c) E9 ltac:(lia)), (U_atom _ 18 (rv_clen c) E18 ltac:(lia)), zcanon_small by lia;
      reflexivity
    | ];
    refine (HM1 rg mm mdq _ _ Hnx _ A10 _ A12 _ A20);
    [ apply (rv_inv_step SK B TL c HC regs2 mem2 md2 rg mm mdq (fun _ => False) HI2 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact UN
      | intros ?a []
      | intros ?a ?Hp; exact (apresent_grows _ _ _ _ HGc Hp)
      | cp_reg HS (2%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (3%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (4%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (26%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity)
      | cp_reg HS (27%bv : bv 5) Q; rewrite Q; apply cp_atom; (lia || reflexivity) ]
    | apply (cp_cmem_eq mem2 mm); [lia | exact UN | exact CM2]
    | cp_reg HS (1%bv : bv 5) Q; rewrite Q; cbn [sv_denot]; rewrite (img_env_codeptr _ HEI); reflexivity
    | cp_reg HS (11%bv : bv 5) Q; rewrite Q; reflexivity
    | split; [|split; [|split]];
      [ cp_reg HS (8%bv : bv 5) Q; rewrite Q, (cp_atom regs2 8 8%bv), P8 by (lia || reflexivity); exact H8
      | cp_reg HS (9%bv : bv 5) Q; rewrite Q, (cp_atom regs2 9 9%bv), P9 by (lia || reflexivity); exact H9
      | cp_reg HS (18%bv : bv 5) Q; rewrite Q, (cp_atom regs2 18 18%bv), P18 by (lia || reflexivity); exact H18
      | cp_reg HS (19%bv : bv 5) Q; rewrite Q, (cp_atom regs2 19 19%bv), P19 by (lia || reflexivity); exact H19 ] ]
  end.
Qed.
End w.
