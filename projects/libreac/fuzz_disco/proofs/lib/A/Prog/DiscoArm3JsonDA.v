(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 60 of its 91 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntRec.v, with its module names changed; 182 of its 216 lines of code are new or changed and 57 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3JsonC2M.v; 208 of its 284 lines of code are new or changed and 140 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoArm3JsonDDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition da_fa : list (nat * afact) :=
  [(18%nat, mkAF SB SB 0); (21%nat, mkAF 0 968 0); (22%nat, mkAF 2 969 0); (25%nat, mkAF 32 32 0);
   (26%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 4096 140737479966720 0); (34%nat, mkAF 33 255 0)].
Definition da_cs : list acond := [mkAC BC_LTU (SOff 21 1) (SOff 22 0)].
Definition da_al : list (sv * sv) := [(SAlu ALU_ADD (SOff 26 0) (SOff 21 0), SOff 33 0)].
Definition da_G : facts := mkFacts da_fa da_cs da_al.
Definition da_rA : YP09.region := YP09.mkRegion (Some 9%nat) 368 376 0 0 [YP09.mkChunk 368 (CVal 8 (SOff 26 1))].
Definition da_rB : YP09.region := YP09.mkRegion (Some 33%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
Definition da_ss : sstate := mkSS OEND_OFF sr_atoms [da_rA; da_rB] None da_G.
Definition da_SH : list shent := [mkSHE 33 1 2].
Definition da_Bx : sv := SOff 18 0.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma da_nowin : forall (E : env) (rs : smem) (a : Z),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a Hf (r & Hin & Hr). rewrite forallb_forall in Hf.
  pose proof (Hf r Hin) as Hq. apply Z.leb_le in Hq. lia.
Qed.

Lemma da_byte : forall (W : world SEGS) m (bufv : Z) (l : list Z) (x : Z),
  garr8 SEGS (rd W m) bufv (l ++ [0]) -> 0 <= x < jlen l ->
  val_mem SEGS (rd W m) (bufv + x) 1 (jbyte l x) /\ 0 <= jbyte l x < 256.
Proof.
  intros W m bufv l x Hg Hx. unfold jlen in Hx.
  assert (Hn : (Z.to_nat x < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
  destruct (Hg (Z.to_nat x) Hn) as [Hv Hr].
  rewrite app_nth1 in Hv, Hr by lia.
  rewrite Z2Nat.id in Hv by lia. unfold jbyte. split; [exact Hv | exact Hr].
Qed.

Lemma da_neg_not : forall (E : env) (x : Z), ew E 21 = Z_to_bv 64 x -> 0 <= x -> x + 1 < 2 ^ 64 ->
  sv_denot E (SOff 21 1) = sv_denot E (SAlu ALU_SUB (SLit 0) (SAlu ALU_XOR (SOff 21 0) (SLit (-1)))).
Proof.
  intros E x Hx H0 H1. apply U_inj.
  rewrite (U_atom_off E 21 x 1 Hx ltac:(lia) ltac:(lia)).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_lit by lia. rewrite (U_not E 21 x Hx ltac:(lia)).
  unfold zcanon, M64.
  replace (0 - (2 ^ 64 - 1 - x)) with (x + 1 + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma da_shent : forall ly S (W : world SEGS) mem md E (m : nat) p nn q lo hi,
  AR SEGS B ly S W mem md -> In (p, nn) (ablocks B ly S) ->
  U E da_Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size nn ->
  shent_ok SEGS da_Bx E (rd W mem) (mkSHE m lo hi).
Proof.
  intros ly S W mem md E m p nn q lo hi HAR Hin HB Hm Hlo Hlh Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm.
  rewrite <- (aview_rd_of SEGS).
  destruct (al_shadow _ _ LAWS ly S W mem md p nn HAR Hin) as [Hbs _].
  destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hin) as (_ & _ & _ & Happ & _).
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - intros a Ha. cbn [Z.min Z.max] in Ha.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Theorem a3j_D_A : jd_A_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin p cur count acc vpad W c HIN.
unfold joend_in, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & acc0 & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R22 & R26 & R21 & R19) & (HSP1 & HTAB & HBUF & HXS) & HSP0 & HBODY).
destruct HXS as (HFIN & Hp0 & Hcount & Hlacc & Hb125 & HAF & Hlcur & HFAcur & HMEM).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs2 & Rs4 & Rs9).
pose proof HFIN as (HJR & Hfin8 & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof HMEM as (M408 & M368 & _).
pose proof ASAN_CEIL_range as (Hceil0 & _). unfold ASAN_CEIL in Hceil0.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
pose proof (jd_count_le T1 now fin (p + 1) count acc cur HFIN HAF) as Hc7.
assert (Hp1r : p + 1 < a3_r T1 now).
{ destruct (jobjs_after_step (a3_text T1 now) fin (p + 1) count acc cur HAF) as [(Hcm & _) | (_ & Hcb & _)].
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNOWS ltac:(lia)) in Hcm.
    destruct (at_byte_true _ _ _ Hcm) as (Hlt & _). unfold a3_r. unfold jlen in Hlt. lia.
  - rewrite (json_ws_id (a3_text T1 now) (p + 1) HNOWS ltac:(lia)) in Hcb.
    destruct (at_byte_true _ _ _ Hcb) as (Hlt & _). unfold a3_r. unfold jlen in Hlt. lia. }
pose proof (jno_ws_byte (a3_text T1 now) (p + 1) HNOWS ltac:(unfold jlen, a3_r in *; lia)) as HV.
pose proof HBODY as (Tb & Gb & Lkb & Hbt & HFRM & HSHD & HOBJ & HBLK & _).
pose proof HBLK as (HPerm0 & _ & _ & _).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof HJ as (HAR3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hb16 & Hb4096 & Hbceil & Hbapp & _).
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0) as [Eq | Eq]; lia. }
rewrite Hreq in Hbceil, Hbapp.
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFsh & GWpres & _ & _ & _ & _).
unfold LLVMF_STK in GSlo.
pose proof (d_A_range cx ltac:(unfold MFRAME; lia)) as (GA1 & GA32). unfold MFRAME in GA1.
pose proof (paj_run (fx := fq) (PI := PI) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) (PI := PI) B LAWS) as RUNTO.
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (buf + p); Z_to_bv 64 (jbyte (a3_text T1 now) (p + 1))]))
  as E0 eqn:HE0.
assert (HEI0 : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EE0 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r)
  by (intros nn r Hr; rewrite HE0; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E33 : ew E0 33 = Z_to_bv 64 (buf + p)).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 33%nat with (32 + 1)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (E34 : ew E0 34 = Z_to_bv 64 (jbyte (a3_text T1 now) (p + 1))).
{ rewrite HE0, Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
  rewrite ew_Ereg_extra. reflexivity. }
assert (E21 : ew E0 21 = Z_to_bv 64 p) by (rewrite (EE0 21%nat 21%bv eq_refl); exact R21).
assert (U9 : bv_unsigned (ew E0 9) = d_A cx).
{ rewrite (EE0 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew E0 18) = SHADOW_OFF).
{ rewrite (EE0 18%nat 18%bv eq_refl), Rs2. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U21 : bv_unsigned (ew E0 21) = p) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E0 22) = a3_r T1 now).
{ rewrite (EE0 22%nat 22%bv eq_refl), R22. unfold w64. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E0 25) = 32).
{ rewrite (EE0 25%nat 25%bv eq_refl), Rs9. unfold w64. apply unsigned_lit_small. lia. }
assert (U26 : bv_unsigned (ew E0 26) = buf).
{ rewrite (EE0 26%nat 26%bv eq_refl), R26. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E0 33) = buf + p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E0 34) = jbyte (a3_text T1 now) (p + 1))
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (HGf : facts_ok E0 da_G).
{ split; [|split].
  - unfold da_G, da_fa. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U21, U22, U25, U26, U33, U34. rewrite Z.pow_0_r. rewrite !Z.mod_1_r.
    unfold SB, SHADOW_OFF in *.
    repeat split; try lia.
  - unfold da_G, da_cs. cbn [f_conds conds_ok].
    split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ltu_U, !U_SOff, U21, U22.
    rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_lt; lia.
  - unfold da_G, da_al. cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite (U_add_off_atom E0 26 0 21 0 ltac:(unfold M64; lia) ltac:(unfold M64; lia)).
    rewrite U_SOff, U26, U21, U33. rewrite zcanon_id by (unfold M64; lia). lia. }
destruct (da_byte W mem3 buf (a3_text T1 now) (p + 1) HGARR ltac:(unfold jlen, a3_r in *; lia)) as (Hvp1 & _).
assert (HRA : region_ok SEGS E0 (rd W mem3) da_rA).
{ unfold da_rA, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (d_A cx) 368 8 (SOff 26 1) (buf + 1)).
  - cbn [sv_denot]. rewrite U26. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact M368. }
assert (HRB : region_ok SEGS E0 (rd W mem3) da_rB).
{ unfold da_rB, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E0 _ (buf + p) 1 1 (SOff 34 0) (jbyte (a3_text T1 now) (p + 1))).
  - cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
  - cbn [Z.of_N]. lia.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
    replace (buf + p + 1) with (buf + (p + 1)) by lia. exact Hvp1. }
assert (HPD : pairwise_disjoint E0 [da_rA; da_rB]).
{ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, da_rA, da_rB.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33.
  split; [split; [right; lia | exact I] | split; [exact I | exact I]]. }
assert (HS : st_ok_pi (fx := fq) SEGS VAL E0 da_ss
  (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + OEND_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold da_ss. apply pa_entry_st_ok_full.
  - rewrite HE0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRA | constructor; [exact HRB | constructor]].
  - exact HPD.
  - exact HGf. }
assert (SHOK : sh_ok SEGS da_Bx da_SH E0 (rd W mem3)).
{ unfold da_SH. constructor; [|constructor].
  apply (da_shent ly3 S3 W mem3 md3 E0 33%nat buf (Z.max (slot_ser_defs.ser_cap op) 1) (buf + p) 1 2
    HAR3 Hinbuf).
  - unfold da_Bx. rewrite U_SOff, U18, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  - rewrite U_SOff, U33, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - lia.
  - lia.
  - rewrite Hreq. lia. }
clear HRA HRB HPD HGf.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' a1 b1 c1 d1 e1 f1 g1) end.
  intros a Ha. exfalso. revert Ha. apply da_nowin. vm_compute. reflexivity. }
assert (Emem1 : ms_mem ms = mem3).
{ apply functional_extensionality. intros x. apply HF. apply da_nowin. vm_compute. reflexivity. }
clear HF HFr HG.
rename ms into ms1. rename HEI into HEI1.
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 (restrict _ _) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) E1 ss1 ms1 (11%bv : bv 5) HS) as Q11a;
  let e := eval vm_compute in (sr_get (ss_regs ss1) (11%bv : bv 5)) in
  change (sr_get (ss_regs ss1) (11%bv : bv 5)) with e in Q11a;
  assert (E1_21 : ew E1 21 = Z_to_bv 64 p) by (rewrite <- E21; reflexivity);
  pose proof (ast_ok_pi_set_reg_fp (PI := PI) E1 ss1 (restrict (w_H W) ms1) (11%bv : bv 5) (SOff 21 1) HS
    ltac:(vm_compute; reflexivity)
    ltac:(cbn [ms_regs restrict]; rewrite Q11a; exact (da_neg_not E1 p E1_21 ltac:(lia) ltac:(lia)))) as HS2
end.
clear HS Q11a E1_21. rename HS2 into HS.
paj_run_to_tok RUNTO HS HJ SHOK Bspan MID_OFF.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?a1 ?b1 ?c1 ?d1 ?e1 ?f1 ?g1 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' a1 b1 c1 d1 e1 f1 g1) end.
  intros a Ha. exfalso. revert Ha. apply da_nowin. vm_compute. reflexivity. }
assert (Emem2 : ms_mem ms = ms_mem ms1).
{ apply functional_extensionality. intros x. apply HF. apply da_nowin. vm_compute. reflexivity. }
rewrite Emem1 in Emem2.
pmkst HS.
rewrite Emem2. rewrite Emem2 in HJ.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
rewrite (EE0 2%nat 2%bv eq_refl) in Q2. rewrite (EE0 3%nat 3%bv eq_refl) in Q3.
rewrite (EE0 4%nat 4%bv eq_refl) in Q4. rewrite (EE0 8%nat 8%bv eq_refl) in Q8.
rewrite (EE0 9%nat 9%bv eq_refl) in Q9. rewrite (EE0 18%nat 18%bv eq_refl) in Q18.
rewrite (EE0 19%nat 19%bv eq_refl) in Q19. rewrite (EE0 20%nat 20%bv eq_refl) in Q20.
rewrite (EE0 22%nat 22%bv eq_refl) in Q22. rewrite (EE0 25%nat 25%bv eq_refl) in Q25.
rewrite (EE0 26%nat 26%bv eq_refl) in Q26.
rewrite U33 in Q10, Q21. rewrite U21 in Q11. rewrite E34 in Q12.
apply SRr_ret.
unfold jmid, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3.
eexists. exists k, acc0.
split; [unfold cfg_at, w64; reflexivity|].
split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite Q2; exact Rsp|].
  split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [rewrite Q8; exact Rs0|].
  split; [rewrite Q9; exact Rs1|]. split; [rewrite Q18; exact Rs2|]. split; [rewrite Q20; exact Rs4|].
  rewrite Q25; exact Rs9. }
split.
{ split; [rewrite Q22; exact R22|]. split; [rewrite Q26; exact R26|].
  split; [rewrite Q10; unfold w64; f_equal; lia|].
  split; [rewrite Q11; unfold w64; reflexivity|].
  split; [rewrite Q12; unfold w64; reflexivity|].
  split; [rewrite Q21; unfold w64; f_equal; lia|].
  rewrite Q19; exact R19. }
split.
{ split; [exact HSP1|]. split; [exact HTAB|]. split; [exact HBUF|].
  split; [exact HFIN|]. split; [exact Hp0|]. split; [exact Hp1r|]. split; [lia|].
  split; [exact Hlacc|]. split; [exact HAF|]. split; [exact Hlcur|]. split; [exact HFAcur | exact HMEM]. }
split; [exact HSP0 | exact HBODY].
Qed.

End h.
End f.
End d.
