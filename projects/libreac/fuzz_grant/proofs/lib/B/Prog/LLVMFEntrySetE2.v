(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySetDefs.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of the last three proofs of lib/A/Prog/GrantEntrySetDefs.v (seg78,
   seg_e2, call_e2), ported from a working branch 7c8c67da870 (blob 7818e2549e1; the image-A file carries no
   licence lines, so none are copied). They sit in their own file so that LLVMFEntrySetDefs.v, which other
   phases Require, stays free of the set loop's walks.

   The end of a turn of the set loop of LLVMFuzzerTestOneInput on image B:
     GE2, 0x810b4 (the return of reac_headamp_tx_effective after an accepted set) .. 0x81140:
       0x810b4  `bne a0,s9` into the abort 0x81d98: a0 is the value read back, s9 the value set;
       0x810b8  `beqz s6` into the trap 0x81f48: s6 = 1, the `channel < 48` flag;
       0x810bc..0x810d0  s2 := 3ch; `bltu a0,s2` (a0 = slot 120 = NOT &was_set) and `bltu 2,s8` into the trap:
                the engine decides both from the facts on the slot's atom and on the parameter;
       0x810d4..0x810e0  a0 := &was_set + 3ch, `not a1,a0`, `bltu a1,s8` into the trap: the UBSan
                pointer-overflow guard, split here and refuted by hand (g_not_guard);
       0x810e4..0x81100  the shadow check and the store of 1 into was_set[ch][param];
       0x81104..0x81118  the same two guards for set_to (the second split by hand);
       0x8111c..0x81134  the shadow check and the store of the value into set_to[ch][param];
       0x81138  s4 := slot 152 (the table), 0x8113c a2 := s10 (the bytes left);
     G78, 0x81140: `addiw s5,s5,-1`, `li a3,1`, `beqz s5,0x81224` (GP_unset0), else `j 0x80ef8` (GP_set).
   Image A has none of the five UBSan guards; its turn end (0x80c24 .. 0x80c80) has the value check and the
   two stores only. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel HeadampSched reac_headamp_tx_set_c HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- image B's UBSan pointer-overflow guard on an array cell ---- *)
(* s2 := 3ch is `slli a0,s2,1; add s2,a0,s2`, which the engine keeps as ch * 3. *)
Lemma U_mul3 : forall E c, ew E 18 = w64 c -> 0 <= c < 48 -> U E (SMd M_MUL (SOff 18 0) (SLit 3)) = 3 * c.
Proof.
  intros E c H Hc. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom E 18 c H) by lia.
  change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* `not a1,a0; bltu a1,s8` with a0 = the array's address + 3ch and s8 the parameter: the
   complement of an address below 2^47 is far above any parameter, so the trap is not taken. *)
Lemma g_not_guard : forall E (nb : nat) b c q,
  ew E 18 = w64 c -> ew E nb = w64 b -> ew E 24 = w64 q ->
  0 <= c < 48 -> 0 <= q < 3 -> 0 <= b -> b + 3 * c + q < 2 ^ 47 ->
  branch_taken BC_LTU
    (sv_denot E (SAlu ALU_XOR (SAlu ALU_ADD (SMd M_MUL (SOff 18 0) (SLit 3)) (SOff nb 0)) (SLit (-1))))
    (sv_denot E (SOff 24 0)) = false.
Proof.
  intros E nb b c q H18 Hb H24 Hc Hq Hb0 Hlt.
  rewrite branch_ltu_U, g_U_not, U_SAlu. cbn [zalu_raw].
  rewrite (U_mul3 E c H18 Hc), (U_atom E nb b Hb), (U_atom E 24 q H24) by lia.
  rewrite zcanon_id by (unfold M64; lia). apply Z.ltb_ge. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The value of a register the run left as an atom of the entry registers. *)
Ltac rr_atom HS HE regs r R :=
  prreg HS r R; rewrite HE, Eimg_low in R by (unfold A_TEXT; lia);
  let nn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
  rewrite (ew_Ereg_nat regs _ nn r eq_refl) in R.

Ltac cur_ms HS := lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?m) => m
  | st_ok _ _ _ (restrict _ ?m) => m end.

(* ---- 0x81140: the end of a turn ---- *)
Definition ss78 : sstate := mkSS 0x704 sr_atoms [] None (mkFacts [(21%nat, mkAF 1 255 0)] [] []).

Lemma seg78 : forall POST n i,
  ge_from B MT POST (GI_unset0 B MT) -> (forall n', n = S n' -> ge_from B MT POST (GIn B MT n')) ->
  ge_from B MT POST (G78 B MT n i).
Proof.
  intros POST n i HU HI cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HM & H23 & H12).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (SegSetModel.rd8_range (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) as Hnr.
  change (fst (GrantSlotPlan.rd8 (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx))))) with (GrantSlotPlan.nset (c_pl cx)) in Hnr.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E21 : ew E 21 = w64 (Z.of_nat (S n)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); subst regs; exact H21).
  assert (HS : st_ok_pi SEGS VAL E ss78 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x704)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss78. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  psrr_branch_tok RUN BR HS SHOK GBspan;
    (rewrite branch_eq_U, (U_atom_off E 21 (Z.of_nat (S n)) (-1) E21), U_lit in Hc by lia).
  - (* s5 - 1 = 0: the loop is done, on to GP_unset0 (0x81224) *)
    apply Z.eqb_eq in Hc. assert (n = 0%nat) by lia. subst n.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x7e8; [first [apply awr_ok_nil | gshow] |].
    let msF := cur_ms HS in
    assert (HMEQ : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a; match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem msF) |- _ =>
        rewrite (frame_nil_eq _ _ _ _ _ eq_refl H2 a), (frame_nil_eq _ _ _ _ _ eq_refl H1 a); reflexivity end
    | apply (HU cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    rr_atom HS HE regs (2%bv : bv 5) R2. rr_atom HS HE regs (8%bv : bv 5) R8. rr_atom HS HE regs (9%bv : bv 5) R9.
    rr_atom HS HE regs (3%bv : bv 5) R3. rr_atom HS HE regs (4%bv : bv 5) R4.
    rr_atom HS HE regs (19%bv : bv 5) R19. rr_atom HS HE regs (23%bv : bv 5) R23.
    rr_atom HS HE regs (12%bv : bv 5) Y12.
    subst regs.
    apply (fin_unset0 B MT cx fp k acc ly3 S3 W3 _ _ i t); try assumption.
    all: first [ (unfold gmach, gregs; splits; try assumption; congruence)
               | lia | congruence | exact (gmem_tr cx fp W3 ms3 _ t _ _ _ HMEQ HM) ].
  - (* back to GP_set (0x80ef8) with n turns left *)
    apply Z.eqb_neq in Hc. destruct n as [|n']; [lia|].
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x4bc; [first [apply awr_ok_nil | gshow] |].
    let msF := cur_ms HS in
    assert (HMEQ : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a; match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem msF) |- _ =>
        rewrite (frame_nil_eq _ _ _ _ _ eq_refl H2 a), (frame_nil_eq _ _ _ _ _ eq_refl H1 a); reflexivity end
    | apply (HI n' eq_refl cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    rr_atom HS HE regs (2%bv : bv 5) R2. rr_atom HS HE regs (8%bv : bv 5) R8. rr_atom HS HE regs (9%bv : bv 5) R9.
    rr_atom HS HE regs (3%bv : bv 5) R3. rr_atom HS HE regs (4%bv : bv 5) R4.
    rr_atom HS HE regs (19%bv : bv 5) R19. rr_atom HS HE regs (20%bv : bv 5) R20.
    rr_atom HS HE regs (23%bv : bv 5) R23. rr_atom HS HE regs (12%bv : bv 5) Y12.
    prreg HS (21%bv : bv 5) R21. prreg HS (13%bv : bv 5) Y13.
    subst regs.
    let msF := cur_ms HS in
    assert (R21' : getr (ms_regs msF) 21 = w64 (Z.of_nat (S n')))
      by (rewrite R21, E21; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia).
    split; [|split; [exact R21' | lia]].
    apply (fin_set B MT cx fp k acc ly3 S3 W3 _ _ (S i) t); try assumption.
    all: first [ (unfold gmach, gregs; splits; try assumption; congruence)
               | lia | congruence | (rewrite R21'; f_equal; lia) | exact Y13
               | exact (gmem_tr cx fp W3 ms3 _ t _ _ _ HMEQ HM) ].
Qed.

(* ---- 0x810b4 .. 0x81140: the value read back, the guards and the two stores ---- *)
Definition F_e2 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 0 47 0); (22%nat, mkAF 1 1 0);
            (24%nat, mkAF 0 2 0); (25%nat, mkAF 0 255 0);
            (32%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (33%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0);
            (37%nat, PTRA 0); (38%nat, PTRA 0) ] []
          [ (XW, SOff 37 0); (XS, SOff 38 0) ].
(* a0 is set to s9's atom: the two are equal, which is what the check at 0x810b4 tests. *)
Definition ss_e2a : sstate := mkSS 0x678 sr_atoms [R_stk; R_c1; R_c2] None F_e2.
Definition ss_e2 : sstate := mkSS 0x678 (sr_set sr_atoms 10%bv (SOff 25 0)) [R_stk; R_c1; R_c2] None F_e2.
Definition SH_e2 : list shent := [mkSHE 37 0 1; mkSHE 38 0 1].

(* The run may write the two cells (R_c1, R_c2, in this function's frame); the stack
   slots it reads (R_stk) are read-only. *)
Ltac e2_awr fp X1 X2 E37 E38 L6 :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fpl ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fpl b0 bc lyy own) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat X1);
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite E37; unfold w64; apply unsigned_lit_small; unfold X1; lia
  | intros a Ha; right; right; right; exists GE_CID, fp; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd YP09.r_wlo YP09.r_whi] in *; rewrite L6;
    change (fs_frame_bytes GE_CID) with 1024; unfold X1 in Ha; lia
  | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 38%nat X2);
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; rewrite E38; unfold w64; apply unsigned_lit_small; unfold X2; lia
  | intros a Ha; right; right; right; exists GE_CID, fp; split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd YP09.r_wlo YP09.r_whi] in *; rewrite L6;
    change (fs_frame_bytes GE_CID) with 1024; unfold X2 in Ha; lia
  | ];
  apply awr_ok_nil.

(* The windows of the run's regions: the two cells only. *)
Ltac e2_win X1 X2 E37 E38 :=
  let x := fresh "x" in let r := fresh "r" in let Hr := fresh "Hr" in let Hx := fresh "Hx" in
  intros x (r & Hr & Hx); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [Hr | Hr];
          [ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
            first [ lia
                  | cbn [ew ewset Nat.eqb] in Hx; rewrite E37 in Hx; unfold w64 in Hx;
                    rewrite unsigned_lit_small in Hx by (unfold X1; lia); lia
                  | cbn [ew ewset Nat.eqb] in Hx; rewrite E38 in Hx; unfold w64 in Hx;
                    rewrite unsigned_lit_small in Hx by (unfold X2; lia); lia ]
          | ]);
  try destruct Hr.

Lemma seg_e2 : forall POST n i, ge_from B MT POST (G78 B MT n i) -> ge_from B MT POST (GE2 B MT n i).
Proof.
  intros POST n i HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & HC & HA & HM & R10 & R18 & R22 & R24 & R25 & R23 & R26).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H21).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof HA as HAcc.
  unfold gacc in HA. apply andb_true_iff in HA as [HAc HAq]. apply Z.ltb_lt in HAc.
  pose proof (SegSetModel.legalb_legal (gq (c_pl cx) i) (gv (c_pl cx) i) ltac:(lia) ltac:(lia) HAq) as Hleg.
  destruct (SegSetModel.legal_bound _ _ Hleg) as [Hq3 _].
  destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite HAcc in EW, ES.
  remember (gc (c_pl cx) i) as c eqn:Ec. remember (gq (c_pl cx) i) as q eqn:Eq. remember (gv (c_pl cx) i) as v eqn:Ev.
  set (X1 := gF cx fp + GO_WAS + (3 * c + q)). set (X2 := gF cx fp + GO_SET + (3 * c + q)).
  set (NS := 2 ^ 64 - 1 - (gF cx fp + GO_SET)). set (NW := 2 ^ 64 - 1 - (gF cx fp + GO_WAS)).
  assert (GW : GO_WAS = 32) by reflexivity. assert (GS : GO_SET = 240) by reflexivity.
  pose proof HM as (_ & Hsh & _ & _ & Hmid & _ & HWS & HST).
  pose proof (g_arr_usable cx fp t ly3 W3 ms3 GO_WAS (3 * c + q) HL Hsh (or_introl eq_refl) ltac:(lia)) as RA1.
  pose proof (g_arr_usable cx fp t ly3 W3 ms3 GO_SET (3 * c + q) HL Hsh (or_intror eq_refl) ltac:(lia)) as RA2.
  pose proof HJ as (HAR & _).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & HFb & _).
  rewrite L6 in HFb. change (fs_frame_bytes GE_CID) with 1024 in HFb.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [NS; NW; gF cx fp + GO_SET; gF cx fp + GO_WAS; t; X1; X2]))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) =
      nth j (map (Z_to_bv 64) [NS; NW; gF cx fp + GO_SET; gF cx fp + GO_WAS; t; X1; X2]) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; exact G9).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); subst regs; exact R18).
  assert (E22 : ew E 22 = w64 1) by (rewrite (ER 22%nat 22%bv eq_refl); subst regs; exact R22).
  assert (E24 : ew E 24 = w64 q) by (rewrite (ER 24%nat 24%bv eq_refl); subst regs; exact R24).
  assert (E25 : ew E 25 = w64 v) by (rewrite (ER 25%nat 25%bv eq_refl); subst regs; exact R25).
  assert (E32 : ew E 32 = w64 NS) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = w64 NW) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = w64 (gF cx fp + GO_SET)) by exact (EX 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = w64 (gF cx fp + GO_WAS)) by exact (EX 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = w64 t) by exact (EX 4%nat ltac:(lia)).
  assert (E37 : ew E 37 = w64 X1) by exact (EX 5%nat ltac:(lia)).
  assert (E38 : ew E 38 = w64 X2) by exact (EX 6%nat ltac:(lia)).
  assert (HS0 : st_ok_pi SEGS VAL E ss_e2a (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x678)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_e2a. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [subst mem; exact (R_stk_ok cx fp t ly3 W3 ms3 E HL E9 E32 E33 E34 E35 E36 Hmid)|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold region_ok, R_c1, R_c2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        [rewrite E37 | rewrite E38]; unfold w64; rewrite unsigned_lit_small by (unfold X1, X2, GO_WAS, GO_SET; lia);
        (split; [unfold X1, X2, GO_WAS, GO_SET; lia|]); (split; [unfold X1, X2, GO_WAS, GO_SET; lia|]); (split; [|apply Forall_nil]);
        intros o Ho; apply (apresent_writable SEGS); subst mem;
        match goal with |- apresent _ _ ?a => apply (proj1 (HFb a ltac:(unfold X1, X2, GO_WAS, GO_SET; lia))) end.
    - apply pairwise_disjoint_of_extents.
      unfold R_stk, R_c1, R_c2, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E9, E37, E38. unfold w64. rewrite !unsigned_lit_small by (unfold X1, X2, GO_WAS, GO_SET; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold X1, X2, GO_WAS, GO_SET. splits; lia.
    - unfold F_e2. split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok, PTRA. cbn [af_lo af_hi af_al2].
        rewrite E9, E18, E22, E24, E25, E32, E33, E37, E38. unfold w64.
        rewrite !unsigned_lit_small by (unfold X1, X2, NS, NW, GO_WAS, GO_SET; lia).
        change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold X1, X2, NS, NW, GO_WAS, GO_SET. splits; try lia.
      + cbn [f_alias alias_ok].
        destruct (denot_cells E (gF cx fp + GO_WAS) c q E18 E24 ltac:(lia) ltac:(lia) ltac:(unfold GO_WAS; lia) ltac:(unfold GO_WAS; lia)) as [DW _].
        destruct (denot_cells E (gF cx fp + GO_SET) c q E18 E24 ltac:(lia) ltac:(lia) ltac:(unfold GO_SET; lia) ltac:(unfold GO_SET; lia)) as [_ DS].
        split; [|split; [|exact I]].
        * rewrite (DW E35), (gsv0 E 37 X1 E37) by (unfold X1, GO_WAS; lia). reflexivity.
        * rewrite (DS E34), (gsv0 E 38 X2 E38) by (unfold X2, GO_SET; lia). reflexivity. }
  assert (HS : st_ok_pi SEGS VAL E ss_e2 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x678)) mem (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E ss_e2a _ (10%bv : bv 5) (SOff 25 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. rewrite (gsv0 E 25 v E25) by lia. subst regs. rewrite R10. reflexivity. }
  clear HS0.
  assert (SHOK : sh_ok SEGS GBx SH_e2 E (mrestrict (w_H W3) mem)).
  { unfold sh_ok, SH_e2. constructor; [|constructor; [|constructor]];
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    unfold GBx; rewrite U_lit by (unfold GSB; lia);
    [rewrite (U_atom E 37 X1 E37) by (unfold X1, GO_WAS; lia) | rewrite (U_atom E 38 X2 E38) by (unfold X2, GO_SET; lia)];
    rewrite Z.add_0_r; replace GSB with SHADOW_OFF by reflexivity; (split; [subst mem; assumption|]);
    intros a Ha; unfold X1, X2, GO_WAS, GO_SET, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
  subst mem.
  (* 0x810b4 .. 0x810e0: the value check, the flag test and the first two guards are
     decided; the run stops at the pointer-overflow guard on &was_set[ch][param]. *)
  paj_run_tok RUN HS HJ SHOK GBspan; [e2_awr fp X1 X2 E37 E38 L6 |].
  psrr_branch_tok RUN BR HS SHOK GBspan.
  { exfalso. rewrite (g_not_guard _ 35 (gF cx fp + GO_WAS) c q) in Hc
      by (first [cbn [ew ewset Nat.eqb]; assumption | unfold GO_WAS; lia]). discriminate Hc. }
  (* 0x810e4 .. 0x81118: the store into was_set, then the guard on &set_to[ch][param] *)
  paj_run_tok RUN HS HJ SHOK GBspan; [e2_awr fp X1 X2 E37 E38 L6 |].
  psrr_branch_tok RUN BR HS SHOK GBspan.
  { exfalso. rewrite (g_not_guard _ 34 (gF cx fp + GO_SET) c q) in Hc1
      by (first [cbn [ew ewset Nat.eqb]; assumption | unfold GO_SET; lia]). discriminate Hc1. }
  (* 0x8111c .. 0x81140: the store into set_to, s4 := the table, a2 := the bytes left *)
  paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x704; [e2_awr fp X1 X2 E37 E38 L6 |].
  let msF := cur_ms HS in
  assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112 \/ a = X1 \/ a = X2) ->
                 aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
  [ intros a Ha Hw;
    repeat match goal with
    | HFr : frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- aview _ _ ?m1 _ = _ =>
        rewrite (frame_wins Ex rs Hh m0 m1 (fun z => c_sp1 cx + 104 <= z < c_sp1 cx + 112 \/ z = X1 \/ z = X2) HFr);
        [ | e2_win X1 X2 E37 E38 | exact Ha | exact Hw ]
    end;
    reflexivity
  | apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
  destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
  rr_atom HS HE regs (2%bv : bv 5) Q2. rr_atom HS HE regs (8%bv : bv 5) Q8. rr_atom HS HE regs (9%bv : bv 5) Q9.
  rr_atom HS HE regs (3%bv : bv 5) Q3. rr_atom HS HE regs (4%bv : bv 5) Q4.
  rr_atom HS HE regs (19%bv : bv 5) Q19. rr_atom HS HE regs (21%bv : bv 5) Q21.
  rr_atom HS HE regs (23%bv : bv 5) Q23.
  prreg HS (20%bv : bv 5) Q20. prreg HS (12%bv : bv 5) Q12.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1
      (YP09.mkRegion (Some 37%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 1))]) HS ltac:(vm_compute; reflexivity)) as FR1;
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 2
      (YP09.mkRegion (Some 38%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 25 0))]) HS ltac:(vm_compute; reflexivity)) as FR2;
    assert (X37 : bv_unsigned (ew Ex 37) = X1)
      by (cbn [ew ewset Nat.eqb]; rewrite E37; unfold w64; apply unsigned_lit_small; unfold X1, GO_WAS; lia);
    assert (X38 : bv_unsigned (ew Ex 38) = X2)
      by (cbn [ew ewset Nat.eqb]; rewrite E38; unfold w64; apply unsigned_lit_small; unfold X2, GO_SET; lia);
    assert (D25 : sv_denot Ex (SOff 25 0) = Z_to_bv 64 v)
      by (apply gsv0; [cbn [ew ewset Nat.eqb]; exact E25 | lia]);
    assert (Q20' : getr (ms_regs msx) 20 = w64 t)
      by (rewrite Q20; cbn [ew ewset Nat.eqb]; exact E36);
    assert (Q12' : getr (ms_regs msx) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))))
      by (rewrite Q12; rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl);
          subst regs; exact R26)
  end.
  cbn [ms_mem restrict] in FR1, FR2.
  let msF := cur_ms HS in
  assert (C1 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + GO_WAS + (3 * c + q)) = Some 1);
  [ apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
    replace (gF cx fp + GO_WAS + (3 * c + q)) with (X1 + 0) by (unfold X1; lia);
    exact (field_of_regionG _ _ 37%nat X1 _ _ _ _ _ 0 1%N (SLit 1) 1 FR1 X37
             ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | ].
  let msF := cur_ms HS in
  assert (C2 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + GO_SET + (3 * c + q)) = Some v);
  [ apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
    replace (gF cx fp + GO_SET + (3 * c + q)) with (X2 + 0) by (unfold X2; lia);
    exact (field_of_regionG _ _ 38%nat X2 _ _ _ _ _ 0 1%N (SOff 25 0) v FR2 X38
             ltac:(cbn; tauto) D25 ltac:(cbn; lia) ltac:(cbn; lia))
  | ].
  let msF := cur_ms HS in
  assert (NWS : gfarr cx fp W3 msF GO_WAS (GrantSlotPlan.ws_put (gwsi (c_pl cx) i) c q 1));
  [ apply (gfarr_put cx fp W3 ms3 msF GO_WAS _ c q 1 LW ltac:(lia) ltac:(lia) ltac:(lia) HWS); [|exact C1];
    intros a Ha Hne; apply HWIN; [unfold GO_WAS in *; lia | unfold X1, X2, GO_WAS, GO_SET in *; lia]
  | ].
  let msF := cur_ms HS in
  assert (NST : gfarr cx fp W3 msF GO_SET (GrantSlotPlan.ws_put (gsti (c_pl cx) i) c q v));
  [ apply (gfarr_put cx fp W3 ms3 msF GO_SET _ c q v LS ltac:(lia) ltac:(lia) ltac:(lia) HST); [|exact C2];
    intros a Ha Hne; apply HWIN; [unfold GO_SET in *; lia | unfold X1, X2, GO_WAS, GO_SET in *; lia]
  | ].
  subst regs.
  exists t. split; [|split; [|split]].
  - unfold gcore, gmach, gregs. splits; try assumption; try congruence.
  - rewrite EW, ES.
    exact (gmem_win3 cx fp t ly3 W3 ms3 _ _ _ _ _ _ X1 X2 HL Hn HWIN
             ltac:(unfold X1, GO_WAS; lia) ltac:(unfold X2, GO_SET; lia) NWS NST HM).
  - congruence.
  - exact Q12'.
Qed.

(* ---- the call of reac_headamp_tx_effective at 0x810b0, which lands in GE2 ---- *)
Hypothesis EFFH : tb_reac_headamp_tx_effective_spec B.

(* Image B's contract for reac_headamp_tx_effective allows a null table (`tx = 0`), which
   image A's does not, and then guards the table's `obj_at` in its post by `tx <> 0`. The
   walk passes the live table (gtab gives 0 < t), so it takes the second disjunct; no branch
   of the walk changes. The check at 0x810b4 compares the value read back with the value
   set: GE2 holds a0 = the value set, by HeadampSched.eff_set_T_same. *)
Lemma call_e2 : call_e2_stmt B MT.
Proof.
  intros POST n i cx fp k acc ly3 S3 W3 regs mem md t HN HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HA
    R1 R2 R8 R9 R3 R4 R10 R11 R12 R18 R19 R20 R21 R22 R23 R24 R25 R26 HM.
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (gtables_inv (c_pl cx) (S i)) as (LT1 & _ & _ & _ & _).
  pose proof HA as HA'. unfold gacc in HA'. apply andb_true_iff in HA' as [HAc HAq]. apply Z.ltb_lt in HAc.
  pose proof (SegSetModel.legalb_legal (gq (c_pl cx) i) (gv (c_pl cx) i) ltac:(lia) ltac:(lia) HAq) as Hleg.
  destruct (SegSetModel.legal_bound _ _ Hleg) as [Hq3 _].
  destruct (gtables_S (c_pl cx) i) as (ET & _ & _). rewrite HA in ET.
  pose proof HM as ((Hra & Hsv) & _ & _ & _ & _ & HT & _).
  assert (Hs0 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (Hsv 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    exact H0. }
  assert (HinT : In (t, ALay.TX_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  eapply (gcall B MT LAWS STK_reac_headamp_tx_effective []
    (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
       getr regs' 10 = w64 (eff (gTi (c_pl cx) (S i)) t (gc (c_pl cx) i) (gq (c_pl cx) i)) /\
       (t <> 0 -> obj_at SEGS (mrestrict (w_H W3) mem') t ALay.LAY_TX (ALay.tx_vals (gTi (c_pl cx) (S i)))))
    _ 0x678 POST cx fp k ly3 S3 W3 regs mem md HB HJ R2 R8 R3 R4 R1 ltac:(lia) eq_refl Hra Hs0
    ltac:(unfold STK_reac_headamp_tx_effective, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
  - intros HPRE. exact (EFFH ly3 S3 W3 regs mem md (gch cx) t (gc (c_pl cx) i) (gq (c_pl cx) i) (gTi (c_pl cx) (S i))
      HPRE R10 R11 R12 ltac:(lia) ltac:(lia) LT1 (or_intror (conj HinT (gtabb_obj W3 _ t _ HT)))).
  - intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & H10 & _).
    apply (HN cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x678)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
    assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
    assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
    assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
    assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
    assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
    assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
    assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
    assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
    assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
    assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
    assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
    assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
    assert (P25 : getr regs2 25 = getr regs 25) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
    assert (P26 : getr regs2 26 = getr regs 26) by exact (HP 26 ltac:(unfold acallee_saved; lia)).
    exists t. split; [|split; [exact HA | split; [|split]]].
    + unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      rewrite P2, P3, P4, P8, P9, P19, P20, P21.
      splits; try reflexivity; try assumption.
    + apply (gmem_trK cx fp t ly3 W3 (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)));
        [exact HL | exact LW | exact LS | | exact HM].
      intros a Ha. exact (gkeep_call0 B MT LAWS cx fp k ly3 S3 W3 mem md STK_reac_headamp_tx_effective mem2 md2 t HB HJ HFR Hbl
        ltac:(unfold STK_reac_headamp_tx_effective, ESTACK; lia) HJc a Ha).
    + cbn [ms_regs mkst]. rewrite H10. rewrite ET. f_equal.
      apply HeadampSched.eff_set_T_same; lia.
    + cbn [ms_regs mkst]. rewrite P18, P22, P24, P25, P23, P26. splits; assumption.
Qed.

End c.
End b.
End a.
