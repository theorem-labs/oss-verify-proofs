(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* The head of the admission tests of fuzz_grant's entry function LLVMFuzzerTestOneInput
   on the ASan build: slots 0x80d90 .. 0x80e30 (GP_admit .. GP_mid), fuzz_grant.c:256-268.

   The harness reads the channel count back from the spill slot 64 and computes its own
   admission rule: the count is between 1 and 40 (`addi a0,s10,-1; li a1,39; bltu a1,a0`
   at 0x80d94..0x80da0), the base is not negative (`slli a0,a0,0x30; bltz a0` on the
   16-bit field at 0x80da8, 0x80dbc) and base + count is at most 48 (`add a0,s7,s10;
   slti s3,a0,49` at 0x80dc0, 0x80dc4) -- that is GrantModel.fits of the two, which is
   GrantSlotPlan.ok of the input. It then calls reac_grant_alloc_fits (0x80e28) and the
   branch at 0x80e2c into the block at 0x81a0c (__asan_handle_no_return, then abort) is
   not taken, because the call answers the same rule.

   The walk runs on a symbolic state with one region, the spill slots the tests read,
   whose values are the atoms 32..37 of the run's environment. Nothing is written, so
   the memory facts of GI_admit carry over unchanged. The three paths of the harness's
   own rule meet at 0x80e20, the cut `ah_GI` of this file. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
YC1g YC1h YC88 GrantFrame YC45 YC85 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
CtrlFinish GrantAllocFits GrantAllocate GrantEntryDefs GrantEntrySeat GrantEntryAdmitDefs
GrantEntryAdmitTail.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c Seg_admit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation hbase cx := (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx))).
Local Notation hwid cx := (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))).
Local Notation hu16 cx := (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx))).

(* Unfold the bit-vector wrappers of the engine's arithmetic, then decide the compares. *)
Local Ltac ah_unwrap :=
  unfold bv_swrap, bv_wrap, zcanon, M64 in *;
  try change (bv_modulus 64) with (2 ^ 64) in *; try change (bv_modulus 32) with (2 ^ 32) in *;
  try change (bv_half_modulus 64) with (2 ^ 63) in *; try change (bv_half_modulus 32) with (2 ^ 31) in *.
Local Ltac ah_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end;
  repeat match goal with
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---- a step that writes nothing keeps every byte ---- *)
Lemma ah_aview_pw : forall (W : world SEGS) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' a H. unfold aview, YP09.mbyte, mrestrict. rewrite H. reflexivity. Qed.

Lemma ah_rdword_pw : forall (W : world SEGS) (m m' : word -> option byte) a v,
  (forall x, m' x = m x) -> rdword (aview SEGS (w_H W) m) a = Some v ->
  rdword (aview SEGS (w_H W) m') a = Some v.
Proof.
intros W m m' a v H Hr. rewrite <- Hr. apply rdword_ext. intros i Hi. apply ah_aview_pw. exact H.
Qed.

Lemma ah_garr8_pw : forall (W : world SEGS) (m m' : word -> option byte) a l,
  (forall x, m' x = m x) -> garr8 SEGS (mrestrict (w_H W) m) a l ->
  garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' a l H Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros q Hq. unfold YP09.mbyte, mrestrict. rewrite H. exact (Hv q Hq).
Qed.

(* The base the tests pass on is the sign-extended 16-bit field, as a 64-bit word. *)
Lemma ah_mod64 : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

(* ---- the symbolic states of the two runs ---- *)
(* The spill slots the tests read, above the realigned stack pointer s1 (atom 9):
   the 16-bit field at 24, the base at 48, the frame's shadow base at 56, the channel
   count at 64, the bytes of input left at 120 and the shadow offset at 152. *)
Definition AH_Rsp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 160 0 0
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
     YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 64 (CVal 8 (SOff 35 0));
     YP09.mkChunk 120 (CVal 8 (SOff 36 0)); YP09.mkChunk 152 (CVal 8 (SOff 37 0))].
Definition ah_ss0 : sstate := mkSS GP_admit sr_atoms [AH_Rsp] None (mkFacts [] [] []).
(* 0x80e20, where the three paths of the harness's rule meet: the call reads no memory. *)
Definition AH_PC : Z := 0x770.
Definition ah_ss1 : sstate := mkSS AH_PC sr_atoms [] None (mkFacts [] [] []).

(* the value of a register of the symbolic state, from the atom facts *)
Local Ltac ah_regval HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = w64 ?v =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 =>
        rewrite at_denot_off0;
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite F; unfold w64; first [reflexivity | f_equal; lia] end
    | SOff ?n ?x =>
        match goal with F : ew Ex n = Z_to_bv 64 ?u |- _ =>
          rewrite (at_denot_off_val Ex n u x F) by lia; unfold w64; f_equal; lia end
    end end end.
(* the register r of the symbolic state, as the symbolic value the run left in it *)
Local Ltac ah_regsv HS :=
  cbn [ms_regs mkst];
  lazymatch goal with |- getr _ ?r = _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [ms_regs restrict mkst] in R; rewrite R; clear R
  end end.
(* a run whose regions have no window writes no byte *)
Local Ltac ah_nowin HF :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m ?m' =>
    let rs' := eval vm_compute in rs in change rs with rs' in HF;
    apply (at_frame_none Ex rs' m m'); [repeat constructor; cbn; lia | exact HF] end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis HFITS : treac_grant_alloc_fits_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* 0x80e20: the harness's own answer is in s3, and the call is next. Everything else is
   as the cut GI_mid will have it. *)
Definition ah_GI (cx : ecx) (fp : Z) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  ge_body cx fp AH_PC W3 ms3 GSH_tables /\ k <= 1 /\ acc <= GE_A1 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (gF cx fp + GO_A) /\
  getr (ms_regs ms3) 19 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 SHADOW_OFF /\
  getr (ms_regs ms3) 22 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 (hbase cx) /\
  getr (ms_regs ms3) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  getr (ms_regs ms3) 26 = w64 (hwid cx) /\
  gslot cx W3 ms3 88 (c_p cx + Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 120 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) /\
  gslot cx W3 ms3 64 (hwid cx) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_LIT) /\
  gslots_late cx fp W3 ms3 /\
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\ SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

(* ---- 0x80e20 .. 0x80e30: the call of reac_grant_alloc_fits and its check ---- *)
Theorem ah_call : forall POST,
  ge_from B MT POST (GI_mid B MT) -> ge_from B MT POST ah_GI.
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R26
                 & S88 & S120 & S64 & S96 & SLATE & HTAB & HWAS & HSET & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp B MT cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GE_STK in Hsp.
pose proof HB as ((_ & Hra0 & Hra4 & Hgp0 & Htp0 & _) & _).
pose proof (Seg_admit.hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
assert (Hs16 : c_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as Hdm. rewrite Hsp32, Z.add_0_r in Hdm. rewrite Hdm.
  replace (32 * (c_sp1 cx / 32)) with ((c_sp1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
(* the layout of the journal keeps the caller's chain *)
pose proof HJ as (HARJ & HlyJ & _).
pose proof HlyJ as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
(* the environment of the run *)
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (gF cx fp + GO_A)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (F19 : ew E 19 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite (EE 19%nat 19%bv eq_refl), R19, Eok; reflexivity).
assert (F20 : ew E 20 = Z_to_bv 64 t) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (F22 : ew E 22 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (F23 : ew E 23 = Z_to_bv 64 (hbase cx)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F24 : ew E 24 = Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (F26 : ew E 26 = Z_to_bv 64 (hwid cx)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
(* the machine state as the engine's symbolic state at 0x80e20 *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + AH_PC))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E ah_ss1 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold ah_ss1. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE EE.
(* 0x80e20 .. 0x80e28: the two arguments and the call *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msN) |- _ => rename msN into msC end.
assert (PC : forall x, ms_mem msC x = ms_mem ms3 x) by ah_nowin HF.
clear HF HFr HG.
pmkst HS.
rewrite pa_sigma_reac_grant_alloc_fits.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs msC) = c_sp1 cx)
  by (unfold spZ; rewrite Q2, F2; apply unsigned_lit_small; lia).
assert (Qs0 : s0Z (ms_regs msC) = spZ (c_regs cx))
  by (unfold s0Z; rewrite Q8, F8; apply unsigned_lit_small; lia).
(* the caller's chain, from the saved words of its machine frame *)
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem msC)) (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)))
                (s0Z (ms_regs msC)) (gch cx)).
{ rewrite Qs0. replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
  apply (achain_ly_top (c_ly cx) ly3); [exact Etop|].
  destruct HSV as (Hra & Hsj).
  apply (ge_achain B MT cx HB).
  - intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & FJ1 & _). apply FJ1; lia.
  - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msC) _ _ PC). exact Hra.
  - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msC) _ _ PC).
    pose proof (Hsj 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    cbn [Z.ltb] in H0. exact H0.
  - lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs msC) (ms_mem msC) _ GE_STK (spZ (c_regs cx)) []
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k
    REAC_GRANT_ALLOC_FITS_STK [] 0 (c_sp1 cx - spZ (c_regs cx)) _ (gch cx)
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
       (forall x, mem2 x = ms_mem msC x) /\
       getr regs2 10 = w64 (Z.b2z (fits (hbase cx) (hwid cx)))) HJ);
  [ rewrite Qsp; lia
  | rewrite Zminus_mod, Hs16, Hsp16; reflexivity
  | lia | unfold REAC_GRANT_ALLOC_FITS_STK, ESTACK; lia
  | unfold REAC_GRANT_ALLOC_FITS_STK, ESTACK, GE_STK; lia
  | rewrite Q3, F3; reflexivity | rewrite Q4, F4; reflexivity
  | reflexivity
  | rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite Q1, unsigned_lit_small by lia; lia
  | exact HCH
  | | intros a (r & Hr & _); destruct Hr ].
  intros HPRE1. eapply SRr_mono.
  { exact (HFITS ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ (gch cx) (hbase cx) (hwid cx) HPRE1
      ltac:(rewrite Q10, F23; reflexivity) ltac:(rewrite Q11, F26; reflexivity)
      ltac:(unfold int32; lia) ltac:(unfold int32; lia) ltac:(intros; lia)). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJf & HPf & Ha0 & Ely & ES & EW & Hmem & _).
  exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJf|]. split; [exact HPf|].
  split; [exact Ely|]. split; [exact ES|]. split; [exact EW|]. split; [exact Hmem | exact Ha0]. }
(* ---- after the call: the check at 0x80e2c ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & HJ2 & HJc & HP2 & Ely & ES & EW & Hmem & Ha0).
subst ly2 S2 W2. subst c2.
rewrite Z.add_0_r in HJ2.
assert (PM : forall x, mem2 x = ms_mem ms3 x) by (intros x; rewrite Hmem; apply PC).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W3) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Q1.
remember (havoc E 40 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall q, (q < 40)%nat -> ew E1 q = ew E q)
  by (intros q Hq; rewrite HE1; apply YN3v.ew_havoc_old; exact Hq).
assert (G19 : ew E1 19 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx))))
  by (rewrite OLD1 by lia; exact F19).
assert (G18 : ew E1 18 = Z_to_bv 64 (gF cx fp + GO_A)) by (rewrite OLD1 by lia; exact F18).
assert (G20 : ew E1 20 = Z_to_bv 64 t) by (rewrite OLD1 by lia; exact F20).
assert (G21 : ew E1 21 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD1 by lia; exact F21).
assert (G22 : ew E1 22 = Z_to_bv 64 (gSH cx fp)) by (rewrite OLD1 by lia; exact F22).
assert (G23 : ew E1 23 = Z_to_bv 64 (hbase cx)) by (rewrite OLD1 by lia; exact F23).
assert (G24 : ew E1 24 = Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (rewrite OLD1 by lia; exact F24).
assert (G26 : ew E1 26 = Z_to_bv 64 (hwid cx)) by (rewrite OLD1 by lia; exact F26).
assert (G2' : ew E1 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F2).
assert (G3' : ew E1 3 = Z_to_bv 64 (as_gp B)) by (rewrite OLD1 by lia; exact F3).
assert (G4' : ew E1 4 = Z_to_bv 64 (as_tp B)) by (rewrite OLD1 by lia; exact F4).
assert (G8' : ew E1 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite OLD1 by lia; exact F8).
assert (G9' : ew E1 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite OLD1 by lia; exact F9).
assert (G44 : ew E1 44 = Z_to_bv 64 (Z.b2z (fits (hbase cx) (hwid cx)))).
{ rewrite HE1. change 44%nat with (40 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
  cbn [nth map]. exact Ha0. }
clear HE1.
clear HJ. rename HJ2 into HJ.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
psrr_branch_pi RUNP BR HS.
{ (* the branch into 0x81a0c is taken only if the call and the harness disagree *)
  exfalso. rewrite branch_ne_U in Hc. apply (proj1 (Bool.negb_true_iff _)), Z.eqb_neq in Hc. apply Hc.
  rewrite !U_SOff, G44, G19. reflexivity. }
paj_run_to_shc RUNTOP HS HJ GP_mid; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msF end.
assert (PF : forall x, ms_mem msF x = mem2 x) by ah_nowin HF.
clear HF HFr HG.
assert (PT : forall x, ms_mem msF x = ms_mem ms3 x) by (intros x; rewrite PF; apply PM).
(* ---- 0x80e30: GI_mid ---- *)
pmkst HS.
eapply HNEXT; [exact HB | exact HJ | exact HFR | exact HMO |].
unfold GI_mid. exists t.
split.
{ unfold ge_body, gregs.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { split; [ah_regval HS|]. split; [ah_regval HS|]. split; [ah_regval HS|].
    split; [rewrite Hgp0; ah_regval HS | rewrite Htp0; ah_regval HS]. }
  split.
  { destruct HSV as (Hra & Hsj). split.
    - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact Hra.
    - intros j Hj. apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact (Hsj j Hj). }
  split.
  { intros i Hi. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msF) _ PT). exact (HSH i Hi). }
  split.
  { apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HFL. }
  split; [exact Hlen|].
  apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HIN. }
split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
split; [ah_regval HS|]. split; [ah_regval HS|]. split; [ah_regval HS|]. split; [ah_regval HS|].
split; [ah_regval HS|]. split; [ah_regval HS|]. split; [ah_regval HS|]. split; [ah_regval HS|].
assert (KSL : forall off v, gslot cx W3 ms3 off v -> gslot cx W3 msF off v)
  by (intros off v Hv; unfold gslot in Hv |- *;
      apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT); exact Hv).
split; [exact (KSL _ _ S88)|]. split; [exact (KSL _ _ S120)|].
split; [exact (KSL _ _ S64)|]. split; [exact (KSL _ _ S96)|].
split.
{ pose proof SLATE as (SMID & SL8 & SL32 & SL40 & SL72 & SL80 & SL104 & SL112 & SL128).
  pose proof SMID as (M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176).
  unfold gslots_late, gslots_mid.
  repeat match goal with |- _ /\ _ => split end; apply KSL; assumption. }
split.
{ pose proof HTAB as (Tin & Tpos & Tlen & Tb).
  split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
  intros i Hi H1 H2 H3. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msF) _ PT).
  exact (Tb i Hi H1 H2 H3). }
split.
{ unfold gfarr in HWAS |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HWAS. }
split.
{ unfold gfarr in HSET |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msF) _ _ PT). exact HSET. }
split; [exact HREL | exact HI1].
Qed.

(* The signed compare of a branch, as the engine denotes it. *)
Lemma ah_branch_lt : forall E a b,
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold Sg. reflexivity. Qed.

(* ---- 0x80d90 .. 0x80e20: the harness computes its own admission rule ---- *)
Theorem ge_admit_head : forall POST,
  ge_from B MT POST (GI_mid B MT) -> ge_from B MT POST (GI_admit B MT).
Proof.
intros POST HNEXT. pose proof (ah_call POST HNEXT) as HMID.
intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & HBODY & Hk & Hacc & HBLK & HCN & R18 & R20 & S88 & S120 & S64 & S96
                 & SLATE & HTAB & HWAS & HSET & HREL & HI1).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL
                     & Hlen & HIN).
pose proof SLATE as (SMID & SL8 & SL32 & SL40 & SL72 & SL80 & SL104 & SL112 & SL128).
pose proof SMID as (M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_grant) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (at_gsp B MT cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GE_STK in Hsp.
pose proof HB as ((_ & Hra0 & Hra4 & Hgp0 & Htp0 & _) & _).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR)
  as (HF0 & HFc & HFia & HFo & HSHeq).
assert (HSHrng : 0 <= gSH cx fp < 2 ^ 64).
{ assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  rewrite HSHeq. unfold SHADOW_OFF. lia. }
pose proof (Seg_admit.hdr_ranges (c_pl cx)) as (Ru & Rb & Ri & Rr & Rs).
assert (Eok : GrantSlotPlan.ok (c_pl cx) = fits (hbase cx) (hwid cx)) by reflexivity.
pose proof (adm_rdword_range _ _ _ _ S120) as RNL.
remember (Eimg (Ereg (ms_regs ms3)
   [Z_to_bv 64 (hu16 cx); Z_to_bv 64 (hbase cx mod 2 ^ 64); Z_to_bv 64 (gSH cx fp);
    Z_to_bv 64 (hwid cx); Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)));
    Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r Hq; subst E; apply at_ewR; exact Hq).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j
   [Z_to_bv 64 (hu16 cx); Z_to_bv 64 (hbase cx mod 2 ^ 64); Z_to_bv 64 (gSH cx fp);
    Z_to_bv 64 (hwid cx); Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx)));
    Z_to_bv 64 SHADOW_OFF] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
assert (F3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl), G3; exact Hgp0).
assert (F4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl), G4; exact Htp0).
assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 (gF cx fp + GO_A)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (F20 : ew E 20 = Z_to_bv 64 t) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F32 : ew E 32 = Z_to_bv 64 (hu16 cx)) by (exact (EX 0%nat ltac:(lia))).
assert (F33 : ew E 33 = Z_to_bv 64 (hbase cx mod 2 ^ 64)) by (exact (EX 1%nat ltac:(lia))).
assert (F34 : ew E 34 = Z_to_bv 64 (gSH cx fp)) by (exact (EX 2%nat ltac:(lia))).
assert (F35 : ew E 35 = Z_to_bv 64 (hwid cx)) by (exact (EX 3%nat ltac:(lia))).
assert (F36 : ew E 36 = Z_to_bv 64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))))
  by (exact (EX 4%nat ltac:(lia))).
assert (F37 : ew E 37 = Z_to_bv 64 SHADOW_OFF) by (exact (EX 5%nat ltac:(lia))).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U32 : U E (SOff 32 0) = hu16 cx) by (apply (U_atom E 32 (hu16 cx) F32); lia).
assert (U33 : U E (SOff 33 0) = hbase cx mod 2 ^ 64)
  by (apply (U_atom E 33 _ F33); apply Z.mod_pos_bound; lia).
assert (U35 : U E (SOff 35 0) = hwid cx) by (apply (U_atom E 35 (hwid cx) F35); lia).
(* the memory facts of the cut, for any state whose memory is this one *)
assert (MEMOK : forall msX : machine_state, (forall x, ms_mem msX x = ms_mem ms3 x) ->
   gsaved cx W3 msX /\
   gshadow cx fp W3 msX GSH_tables /\
   rdword (aview SEGS (w_H W3) (ms_mem msX)) (gF cx fp + 1016) = Some (gFL cx fp) /\
   garr8 SEGS (mrestrict (w_H W3) (ms_mem msX)) (c_p cx)
     (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
   (forall off v, gslot cx W3 ms3 off v -> gslot cx W3 msX off v) /\
   gtab B cx ly3 S3 W3 msX t (GrantSlotPlan.T_end (c_pl cx)) /\
   gfarr cx fp W3 msX GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
   gfarr cx fp W3 msX GO_SET (GrantSlotPlan.st_end (c_pl cx))).
{ intros msX PX. split.
  { destruct HSV as (Hra & Hsj). split.
    - apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact Hra.
    - intros j Hj. apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact (Hsj j Hj). }
  split.
  { intros i Hi. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msX) _ PX). exact (HSH i Hi). }
  split.
  { apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HFL. }
  split.
  { apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HIN. }
  split.
  { intros off v Hv. unfold gslot in Hv |- *.
    apply (ah_rdword_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact Hv. }
  split.
  { pose proof HTAB as (Tin & Tpos & Tlen & Tb).
    split; [exact Tin|]. split; [exact Tpos|]. split; [exact Tlen|].
    intros i Hi H1 H2 H3. rewrite (ah_aview_pw W3 (ms_mem ms3) (ms_mem msX) _ PX).
    exact (Tb i Hi H1 H2 H3). }
  split.
  { unfold gfarr in HWAS |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HWAS. }
  { unfold gfarr in HSET |- *. apply (ah_garr8_pw W3 (ms_mem ms3) (ms_mem msX) _ _ PX). exact HSET. } }
(* the cut at 0x80e20, once a path of the rule has reached it *)
assert (ATMID : forall (msX : machine_state) (mdX : Model) ssX,
   st_ok_pi SEGS VAL E ssX (restrict (w_H W3) msX) -> ss_pc ssX = AH_PC ->
   ss_resv ssX = None ->
   (forall x, ms_mem msX x = ms_mem ms3 x) ->
   getr (ms_regs msX) 2 = w64 (c_sp1 cx) ->
   getr (ms_regs msX) 8 = w64 (spZ (c_regs cx)) ->
   getr (ms_regs msX) 9 = w64 (c_sp1 cx) ->
   getr (ms_regs msX) 3 = getr (c_regs cx) 3 ->
   getr (ms_regs msX) 4 = getr (c_regs cx) 4 ->
   getr (ms_regs msX) 18 = w64 (gF cx fp + GO_A) ->
   getr (ms_regs msX) 19 = w64 (Z.b2z (GrantSlotPlan.ok (c_pl cx))) ->
   getr (ms_regs msX) 20 = w64 t ->
   getr (ms_regs msX) 21 = w64 SHADOW_OFF ->
   getr (ms_regs msX) 22 = w64 (gSH cx fp) ->
   getr (ms_regs msX) 23 = w64 (hbase cx) ->
   getr (ms_regs msX) 24 = w64 (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))) ->
   getr (ms_regs msX) 26 = w64 (hwid cx) ->
   ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
     [(GE_CID, fp)] ly3 S3 W3 (ms_mem msX) mdX k ->
   SRr SEGS W3 (mkCfg msX mdX) (POST cx)).
{ intros msX mdX ssX HSX Hpcx Hrvx PX X2 X8 X9 X3 X4 X18 X19 X20 X21 X22 X23 X24 X26 HJX.
  destruct (MEMOK msX PX) as (MSV & MSH & MFL & MIN & MSL & MTAB & MWAS & MSET).
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E ssX msX HSX Hrvx) as Hshape.
  rewrite Hpcx in Hshape.
  eapply HMID; [exact HB | exact HJX | exact HFR | exact HMO |].
  unfold ah_GI. exists t.
  split.
  { unfold ge_body, gregs.
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split; [rewrite Hshape at 1; reflexivity|].
    split;
      [ split; [exact X2|]; split; [exact X8|]; split; [exact X9|];
        split; [exact X3 | exact X4] |].
    split; [exact MSV|]. split; [exact MSH|]. split; [exact MFL|].
    split; [exact Hlen | exact MIN]. }
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBLK|]. split; [exact HCN|].
  split; [exact X18|]. split; [exact X19|]. split; [exact X20|]. split; [exact X21|].
  split; [exact X22|]. split; [exact X23|]. split; [exact X24|]. split; [exact X26|].
  split; [exact (MSL _ _ S88)|]. split; [exact (MSL _ _ S120)|].
  split; [exact (MSL _ _ S64)|]. split; [exact (MSL _ _ S96)|].
  split.
  { unfold gslots_late, gslots_mid.
    repeat match goal with |- _ /\ _ => split end; apply MSL; assumption. }
  split; [exact MTAB|]. split; [exact MWAS|]. split; [exact MSET|].
  split; [exact HREL | exact HI1]. }
(* the machine state as the engine's symbolic state at 0x80d90 *)
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GP_admit))
  (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E ah_ss0 (restrict (w_H W3) ms3)).
{ rewrite Hms. unfold ah_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold AH_Rsp. apply Forall_cons; [|apply Forall_nil].
    unfold YP09.region_ok; cbv zeta;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 24 8 (SOff 32 0) (hu16 cx));
      [ rewrite at_denot_off0; exact F32 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact M24 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 48 8 (SOff 33 0) (hbase cx mod 2 ^ 64));
      [ rewrite at_denot_off0; exact F33
      | cbn [Z.of_N]; change (8 * 8) with 64; apply Z.mod_pos_bound; lia
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact M48 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 56 8 (SOff 34 0) (gSH cx fp));
      [ rewrite at_denot_off0; exact F34 | cbn [Z.of_N]; change (8 * 8) with 64; lia
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact M56 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 64 8 (SOff 35 0) (hwid cx));
      [ rewrite at_denot_off0; exact F35 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact S64 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 120 8 (SOff 36 0)
               (c_n cx - Z.of_nat (GrantSlotPlan.pos_end (c_pl cx))));
      [ rewrite at_denot_off0; exact F36 | cbn [Z.of_N]; change (8 * 8) with 64; exact RNL
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact S120 ] |].
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS _ _ _ 152 8 (SOff 37 0) SHADOW_OFF);
      [ rewrite at_denot_off0; exact F37 | cbn [Z.of_N]; unfold SHADOW_OFF; lia
      | cbn [Z.of_N]; lia
      | cbn [N.to_nat]; apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)); exact M152 ] |].
    apply Forall_nil.
  - unfold AH_Rsp. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
  - split; [exact I | split; exact I]. }
clear HE EE EX Hms.
(* 0x80d90 .. 0x80da0: the channel count against 40 *)
paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msA end.
assert (PA : forall x, ms_mem msA x = ms_mem ms3 x) by ah_nowin HF.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* the count is 0 or more than 40: the box does not fit *)
  assert (Hf : fits (hbase cx) (hwid cx) = false).
  { apply Seg_admit.fits_false. intros (Hw & Hb0 & Hbw).
    rewrite branch_ltu_U, U_SLit, U_SOff, F35, unsigned_lit_small in Hc by lia.
    apply Z.ltb_lt in Hc. unfold zcanon, M64 in Hc.
    rewrite (Z.mod_small 39) in Hc by lia.
    rewrite (Z.mod_small (hwid cx + -1)) in Hc by lia. lia. }
  paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msB end.
  assert (PB : forall x, ms_mem msB x = ms_mem msA x) by ah_nowin HF.
  clear HF HFr HG.
  assert (PB3 : forall x, ms_mem msB x = ms_mem ms3 x) by (intros x; rewrite PB; apply PA).
  eapply (ATMID msB _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PB3);
    [ ah_regval HS | ah_regval HS | ah_regval HS
    | rewrite Hgp0; ah_regval HS | rewrite Htp0; ah_regval HS
    | ah_regval HS
    | rewrite Eok, Hf; cbn [Z.b2z]; ah_regsv HS; reflexivity
    | ah_regval HS | ah_regval HS | ah_regval HS
    | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
        by (unfold w64; apply ah_mod64); ah_regval HS
    | ah_regval HS | ah_regval HS | exact HJ ].
- (* the count is between 1 and 40 *)
  assert (Hw : 1 <= hwid cx <= 40).
  { rewrite branch_ltu_U, U_SLit, U_SOff, F35, unsigned_lit_small in Hc by lia.
    apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc.
    rewrite (Z.mod_small 39) in Hc by lia.
    assert (Hne : hwid cx <> 0).
    { intros E0. rewrite E0 in Hc.
      change ((0 + -1) mod 2 ^ 64) with (2 ^ 64 - 1) in Hc. lia. }
    rewrite (Z.mod_small (hwid cx + -1)) in Hc by lia. lia. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ; [first [apply awr_ok_nil | awr_ok_tac] |].
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msB end.
  assert (PB : forall x, ms_mem msB x = ms_mem msA x) by ah_nowin HF.
  clear HF HFr HG.
  assert (PB3 : forall x, ms_mem msB x = ms_mem ms3 x) by (intros x; rewrite PB; apply PA).
  psrr_branch_pi RUNP BR HS.
  + (* the base is negative: the box does not fit *)
    rewrite ah_branch_lt, S_SAlu, S_SLit, U32, U_SLit in Hc.
    cbn [zalu_raw] in Hc.
    assert (Hneg : hbase cx < 0).
    { destruct (Z_lt_le_dec (hbase cx) 0) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (Hu : hu16 cx < 32768) by (apply Rs; lia).
      change (Z.land (zcanon 48) 63) with 48 in Hc.
      rewrite Z.shiftl_mul_pow2 in Hc by lia.
      unfold bv_swrap, bv_wrap in Hc.
      change (bv_modulus 64) with (2 ^ 64) in Hc.
      change (bv_half_modulus 64) with (2 ^ 63) in Hc.
      rewrite (Z.mod_small (hu16 cx * 2 ^ 48 + 2 ^ 63)) in Hc by lia.
      rewrite (Z.mod_small (0 + 2 ^ 63)) in Hc by lia.
      apply Z.ltb_lt in Hc. lia. }
    assert (Hf : fits (hbase cx) (hwid cx) = false)
      by (apply Seg_admit.fits_false; intros (_ & Hb0 & _); lia).
    paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msD end.
    assert (PD : forall x, ms_mem msD x = ms_mem msB x) by ah_nowin HF.
    clear HF HFr HG.
    assert (PD3 : forall x, ms_mem msD x = ms_mem ms3 x) by (intros x; rewrite PD; apply PB3).
    eapply (ATMID msD _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PD3);
      [ ah_regval HS | ah_regval HS | ah_regval HS
      | rewrite Hgp0; ah_regval HS | rewrite Htp0; ah_regval HS
      | ah_regval HS
      | rewrite Eok, Hf; cbn [Z.b2z]; ah_regsv HS; reflexivity
      | ah_regval HS | ah_regval HS | ah_regval HS
      | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
          by (unfold w64; apply ah_mod64); ah_regval HS
      | ah_regval HS | ah_regval HS | exact HJ ].
  + (* the base is not negative: the rule is base + count against 48 *)
    rewrite ah_branch_lt, S_SAlu, S_SLit, U32, U_SLit in Hc.
    cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 48) 63) with 48 in Hc.
    rewrite Z.shiftl_mul_pow2 in Hc by lia.
    unfold bv_swrap, bv_wrap in Hc.
    change (bv_modulus 64) with (2 ^ 64) in Hc.
    change (bv_half_modulus 64) with (2 ^ 63) in Hc.
    rewrite (Z.mod_small (0 + 2 ^ 63)) in Hc by lia.
    apply Z.ltb_ge in Hc.
    assert (Hu : hu16 cx < 32768).
    { destruct (Z_lt_le_dec (hu16 cx) 32768) as [Hlt | Hge]; [exact Hlt | exfalso].
      assert (Hmod : (hu16 cx * 2 ^ 48 + 2 ^ 63) mod 2 ^ 64 = hu16 cx * 2 ^ 48 - 2 ^ 63).
      { replace (hu16 cx * 2 ^ 48 + 2 ^ 63)
          with ((hu16 cx * 2 ^ 48 - 2 ^ 63) + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite Hmod in Hc. lia. }
    assert (Hb0 : 0 <= hbase cx) by (apply Rs; exact Hu).
    assert (Hfit : fits (hbase cx) (hwid cx) = (hbase cx + hwid cx <=? 48)).
    { unfold fits.
      replace (1 <=? hwid cx) with true by (symmetry; apply Z.leb_le; lia).
      replace (hwid cx <=? 40) with true by (symmetry; apply Z.leb_le; lia).
      replace (0 <=? hbase cx) with true by (symmetry; apply Z.leb_le; lia).
      cbn [andb]. reflexivity. }
    assert (Hz : zcanon (if bv_swrap 64 (zcanon (hbase cx + hwid cx)) <? bv_swrap 64 (zcanon 49)
                         then 1 else 0) = Z.b2z (hbase cx + hwid cx <=? 48)).
    { assert (Hs1 : bv_swrap 64 (zcanon (hbase cx + hwid cx)) = hbase cx + hwid cx).
      { unfold zcanon, M64, bv_swrap, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small (hbase cx + hwid cx)) by lia.
        rewrite (Z.mod_small (hbase cx + hwid cx + 2 ^ 63)) by lia. lia. }
      assert (Hs2 : bv_swrap 64 (zcanon 49) = 49).
      { unfold zcanon, M64, bv_swrap, bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
        rewrite (Z.mod_small 49) by lia. rewrite (Z.mod_small (49 + 2 ^ 63)) by lia. lia. }
      rewrite Hs1, Hs2. unfold zcanon, M64.
      destruct (Z.ltb_spec (hbase cx + hwid cx) 49) as [Hlt | Hge].
      - replace (hbase cx + hwid cx <=? 48) with true by (symmetry; apply Z.leb_le; lia).
        cbn [Z.b2z]. apply Z.mod_small. lia.
      - replace (hbase cx + hwid cx <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
        cbn [Z.b2z]. apply Z.mod_small. lia. }
    paj_run_to_shc RUNTOP HS HJ AH_PC; [first [apply awr_ok_nil | awr_ok_tac] |].
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msN) |- _ => rename msN into msE end.
    assert (PE : forall x, ms_mem msE x = ms_mem msB x) by ah_nowin HF.
    clear HF HFr HG.
    assert (PE3 : forall x, ms_mem msE x = ms_mem ms3 x) by (intros x; rewrite PE; apply PB3).
    eapply (ATMID msE _ _ HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) PE3);
      [ ah_regval HS | ah_regval HS | ah_regval HS
      | rewrite Hgp0; ah_regval HS | rewrite Htp0; ah_regval HS
      | ah_regval HS
      | rewrite Eok, Hfit; ah_regsv HS;
        rewrite denot_lit_U, !U_SAlu, U33, U35, U_SLit;
        rewrite (Z.mod_small (hbase cx)) by lia;
        cbn [zalu_raw]; rewrite Hz; reflexivity
      | ah_regval HS | ah_regval HS | ah_regval HS
      | replace (w64 (hbase cx)) with (w64 (hbase cx mod 2 ^ 64))
          by (unfold w64; apply ah_mod64); ah_regval HS
      | ah_regval HS | ah_regval HS | exact HJ ].
Qed.

(* ---- the whole phase: 0x80d90 .. 0x80e58 ---- *)
Hypothesis HALLOC : talloc_spec B (BASE + AF_reac_grant_allocate).

Theorem ge_admit : forall POST,
  ge_from B MT POST (GI_sweep B MT) -> ge_from B MT POST (GI_admit B MT).
Proof.
intros POST HNEXT. apply ge_admit_head.
exact (ge_admit_tail B MT LAWS HALLOC POST HNEXT).
Qed.

End c.
End b.
End a.
