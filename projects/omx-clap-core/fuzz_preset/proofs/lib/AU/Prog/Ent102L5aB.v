(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256 d663f82d7f488d30,
   unstripped twin c90d4fa5): SEGMENT L5a of LLVMFuzzerTestOneInput (entry 0x816cc), the ACCESSOR CALL: listing
   slots 190 / 191 (+0x2f8 `mv a0,s5` at 0x819c4, +0x2fc `jal read_members` to B' 0x82554, the return site +0x300 at
   0x819cc), proved against lib/AU/Ent102CutsB.v's `seg_L5a_stmt` (cut_acc E fk t D -> cut_rm E fk t D).
   THE B' TWIN of lib/A/Prog/Ent102L5aA.v (row LL5a, seg_L5a_A, Qed at Ent102L5aA.v (sha256 a8b04836835b; internal record)): the
   body of this function is A''s with pc-relative fields only (elfdis --diff), so the proof is the A' proof with
   L := B_prog_listing and PL := lib/B/Ent102PLB.PL_102_B; the slot words the engine fetches are read from the B'
   tables by the runner, and this file names no slot word and no address.
   STATEMENT: lib/AU/Ent102CutsB.v (blob a74a7497b9d0; seg_L5a_stmt, cut_acc, cut_rm, ec_hyps's named projections
   ech_texts / ech_img / ech_ccut_ok / ech_lcut_ok, ec_img's ei_frame / ei_sio / ei_sio_frame / ei_pst_ro,
   ec_texts's et_stk / et_read_members, the budget indices 6 -> 7, ec_inv's wild budget ec_wk_caw -> ec_wk_rm and the
   row helpers ec_journal_rebase / ec_journal_unbase).
   LISTING: a Theorem Labs lane's whole-program listing of B' lib/B/Listing_prog.v (blob c97cc46b3e13; slot k = byte offset 4k
   from the entry), run with the PAListing PL_102_B of lib/B/Ent102PLB.v (blob e0348e1212c9); the image half stays
   generic ({PA : PAImg B_prog_listing}; lib/B/PAImg_prog.v is not loaded, no vm_compute on pa_val / pa_sigma).
   THE KIT TEXTS: lib/A/PRH_FnCheck.v (blob 909d5290d0ba) tread_members_specX at L := B_prog_listing - the kit's texts are
   generic over the listing class, so B' takes the same text; read_members READS ONLY (S' = S, the ledger restated at
   the same values, g_most / g_own_ran_out included, and the tree); lib/A/PRH_Base.v (blob 966b522cc722) fpre / fpostm
   / STK_read_members / prh_pst and prh_ledger's named projections; lib/A/PRH_FnPj.v (blob 838c63d8cd16) prhPj_rslot
   (the struct pj the callee only reads: here the fake frame's doc slot [fk + 32, fk + 88)).
   SHARED HELPERS (the record's one copy for B', lib/AU/Prog/Ent102CallB.v blob 1c7a402519bc): ec_ledger_cells (the ledger
   is handed to the text at the cut's own statics, g_most = PJ_ALLOC_BOUND n from ec_most and g_own_ran_out = 0 from
   ec_own_is, so the text's post gives cut_rm's ec_most / ec_own_is by prh_ledger_most / prh_ledger_own),
   ec_chain_at (the frame chain at the call) and ec_conj_split (ec_pre's parts by their statements).
   rule 24: proves function LLVMFuzzerTestOneInput (segment L5a of its walk, image B'; reuse search: the lane's index
   output, the internal file idx-llvm-newpin.txt exit=0; no released ASan walk on the #102 pins; checker R24CheckLLVMF CONFIRM; NEW walk;
   plan: the lane's note, the internal file llvm-plan.md section 3).
   FORM: the two instructions run through YC1fPx.v's paj_run_x (YC80x's runner over YCbqG's ajournal_x at
   ARx := ec_ARx), then the kit's text at the callee's entry through YCbqG's afn_pre_x_at and ajournal_x_sub - the same
   call shape as YCbqGcall.v's aj_call_x, with the symbolic run of the two instructions in place of its st_ok premise.
   The budgets move by ec_ccut_ok / ec_lcut_ok's antitonicity (read_members adds no allocator call and keeps S).
   THE WILD BUDGET: cut_acc's journal is budgeted (`exists WS, ajournal_xw .. WS /\ wbudget [] ec_wk_caw WS`).
   This row's own code makes no wild trace, and read_members' text is NOT budgeted (fpostm, no wild_room premise;
   prh_wk F_read_members = 0, so ec_wk_rm = ec_wk_caw): Ent102CutsB.v ec_journal_rebase takes the journal to the plain
   one from the entry with its depot moved to S's, the two instructions and the empty-budget call run on it, and
   ec_journal_unbase gives cut_rm's journal back at the same WS.
   NUMERALS: 760 / 768 are the lane's slot offsets (DERIVED: EC_ACC - EC_BASE, EC_AR_RM - EC_BASE, the same offsets on
   both images); 32 / 56 / 128 are LENGTHs (the doc slot's offset in the frame, sizeof(struct pj), EC_FRAME_BYTES);
   16 / 8 / 4 / 10 are the frame's shadow bytes and the granule indices of the doc slot; 144 = EC_SAVE + 16 is the kit's
   own-frame size of this body (ei_frame); 2 ^ 64 / 2 ^ 47 / 4096 / 268431360 (= SHADOW_OFF / 8) are the engine's
   range facts. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop YC88.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102CallB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Definition L5AB_K : Z := 760.
Definition L5AB_RET : Z := 768.
Definition ss_l5ab : sstate := mkSS L5AB_K sr_atoms [] None (mkFacts [] [] []).
Definition L5AB_Bx : sv := SLit SHADOW_OFF.
Definition L5AB_Bspan : Z * Z := (0, 0).

Lemma l5ab_land32 : forall x, Z.land x (-32) = x / 32 * 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma l5ab_A : forall sp0, sp0 mod 16 = 0 -> 144 <= sp0 ->
  ec_B sp0 mod 32 = 0 /\ sp0 - 144 <= ec_B sp0 <= sp0 - 128.
Proof.
intros sp0 H16 H144. unfold ec_B, EC_SAVE. rewrite l5ab_land32.
split; [rewrite Z.mod_mul by lia; reflexivity|].
pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)).
pose proof (Z.div_mod sp0 16 ltac:(lia)). lia.
Qed.

Lemma l5ab_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. unfold zmaxl. induction l as [|x t IH]; cbn [fold_right]; lia. Qed.

Lemma l5ab_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. unfold zmaxl. induction l as [|y t IH]; intros H; [destruct H|]. cbn [fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). lia.
Qed.

Lemma l5ab_floor8 : forall a b, 0 <= b < 8 -> (a * 8 + b) / 8 * 8 = a * 8.
Proof. intros a b Hb. rewrite Z.div_add_l by lia. rewrite (Z.div_small b 8) by lia. lia. Qed.

(* the doc slot [fk + 32, fk + 88) of a 32-aligned frame: its shadow granules are bytes 4 .. 10 of the frame's
   sixteen, and the hull the instrumented loads read is inside those sixteen *)
Lemma l5ab_shadow_idx : forall fk x, 0 <= fk -> fk mod 32 = 0 -> fk + 32 <= x < fk + 32 + 56 ->
  SHADOW_OFF + x / 8 = shadow_addr fk + (x - fk) / 8 /\ 4 <= (x - fk) / 8 <= 10.
Proof.
intros fk x Hfk0 Hal Hx. pose proof (Z.div_mod fk 32 ltac:(lia)) as Dfk.
assert (Efk : fk = (4 * (fk / 32)) * 8) by lia.
assert (E1 : fk / 8 = 4 * (fk / 32)) by (rewrite Efk at 1; apply Z.div_mul; lia).
assert (E2 : x / 8 = (x - fk) / 8 + 4 * (fk / 32))
  by (replace x with ((x - fk) + (4 * (fk / 32)) * 8) at 1 by lia; apply Z.div_add; lia).
split; [unfold shadow_addr; lia|].
split.
- apply Z.div_le_lower_bound; lia.
- assert (H11 : (x - fk) / 8 < 11) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma l5ab_hull_window : forall fk s, 0 <= fk -> fk mod 32 = 0 ->
  shadow_addr (fk + 32) / 8 * 8 <= s < shadow_addr (fk + 32 + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr fk <= s < shadow_addr fk + 16.
Proof.
intros fk s Hfk0 Hal Hs. pose proof (Z.div_mod fk 32 ltac:(lia)) as Dfk.
assert (E2 : (fk + 32) / 8 = 4 * (fk / 32) + 4)
  by (replace (fk + 32) with ((4 * (fk / 32) + 4) * 8) by lia; apply Z.div_mul; lia).
assert (E3 : (fk + 32 + 56 - 1) / 8 = 4 * (fk / 32) + 10)
  by (replace (fk + 32 + 56 - 1) with ((4 * (fk / 32) + 10) * 8 + 7) by lia;
      rewrite Z.div_add_l by lia; rewrite (Z.div_small 7 8) by lia; lia).
assert (E1 : fk / 8 = 4 * (fk / 32))
  by (replace fk with ((4 * (fk / 32)) * 8) at 1 by lia; apply Z.div_mul; lia).
unfold shadow_addr in *. rewrite E1. rewrite E2, E3 in Hs.
assert (HS8 : SHADOW_OFF = 268431360 * 8) by reflexivity.
destruct (Z.Even_or_Odd (fk / 32)) as [(u & Hu) | (u & Hu)].
- rewrite HS8 in Hs |- *.
  replace (268431360 * 8 + (4 * (fk / 32) + 4)) with ((268431360 + u) * 8 + 4) in Hs by lia.
  replace (268431360 * 8 + (4 * (fk / 32) + 10)) with ((268431360 + u + 1) * 8 + 2) in Hs by lia.
  rewrite (l5ab_floor8 (268431360 + u) 4 ltac:(lia)) in Hs.
  rewrite (l5ab_floor8 (268431360 + u + 1) 2 ltac:(lia)) in Hs.
  lia.
- rewrite HS8 in Hs |- *.
  replace (268431360 * 8 + (4 * (fk / 32) + 4)) with ((268431360 + u + 1) * 8 + 0) in Hs by lia.
  replace (268431360 * 8 + (4 * (fk / 32) + 10)) with ((268431360 + u + 1) * 8 + 6) in Hs by lia.
  rewrite (l5ab_floor8 (268431360 + u + 1) 0 ltac:(lia)) in Hs.
  rewrite (l5ab_floor8 (268431360 + u + 1) 6 ltac:(lia)) in Hs.
  lia.
Qed.

Lemma l5ab_rd64_keep : forall (rd rd' : reader) a v,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rd64 rd a v -> rd64 rd' a v.
Proof. intros rd rd' a v Hk H j Hj. rewrite Hk by lia. exact (H j Hj). Qed.

Lemma l5ab_aregs : forall regs0 regs' : bvmap 5 word,
  getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 8 -> getr regs' 9 = getr regs0 9 ->
  getr regs' 18 = getr regs0 18 -> getr regs' 19 = getr regs0 19 -> getr regs' 20 = getr regs0 20 ->
  getr regs' 21 = getr regs0 21 -> getr regs' 22 = getr regs0 22 -> getr regs' 23 = getr regs0 23 ->
  getr regs' 24 = getr regs0 24 -> getr regs' 25 = getr regs0 25 -> getr regs' 26 = getr regs0 26 ->
  getr regs' 27 = getr regs0 27 ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
Qed.

Lemma l5ab_aregs_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PA : @PAImg rc B_prog_listing}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing PA) -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x (@pa_segs rc B_prog_listing PA) B ARx HL.
(* THE WORLD RELATION (the free move): this run is after check_no_overread's frees, so its premise
   journal and its conclusion are over a world relation Rel (the lane uses wle' segs RZ_cf); the runner is YC1fPx.v's
   paj_run_xR, which takes Rel and its two laws *)
Variable Rel : world (@pa_segs rc B_prog_listing PA) -> world (@pa_segs rc B_prog_listing PA) -> Prop.
Hypothesis Rel_refl : forall W, Rel W W.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx Rel).

Lemma l5ab_run : forall (W : world SEGS) regs mem md doc STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k
  (Q : world SEGS -> config -> Prop),
  getr regs 21 = w64 doc ->
  AJ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  (forall regs1 mem1 md1,
     aregs_preserved regs regs1 ->
     getr regs1 1 = Z_to_bv 64 (BASE + L5AB_RET) -> getr regs1 10 = w64 doc ->
     (forall x, mem1 x = mem x) ->
     AJ STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem1 md1 k ->
     SRrG SEGS Rel W (cfg_at SEGS (SIGMA AS_read_members) regs1 mem1 md1) Q) ->
  SRrG SEGS Rel W (cfg_at SEGS (BASE + L5AB_K) regs mem md) Q.
Proof.
intros W regs mem md doc STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k Q R21 HJ HK.
remember (@Eimg rc B_prog_listing PA (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; rewrite HE; apply Eimg_low; exact Hn).
assert (HS : st_ok_pi SEGS VAL E ss_l5ab (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L5AB_K)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_l5ab. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS L5AB_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (ER : forall n (r : bv 5), (n < 32)%nat -> ew (Ereg regs []) n = getr regs r -> ew E n = getr regs r)
  by (intros n r Hn Hr; rewrite EL by (unfold A_TEXT; lia); exact Hr).
clear HE.
pose (RUN := @paj_run_xR fx rc SK B_prog_listing PL_102_B PA B PST ARx HL LAWS Rel Rel_refl Rel_trans).
unfold cfg_at.
paj_run_tok_xR RUN HS HJ SHOK L5AB_Bspan.
- intros a (r & Hr & _). destruct Hr.
- pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  apply HK.
  + apply l5ab_aregs;
    [ rewrite P2; apply ER; [lia | exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)]
    | rewrite P3; apply ER; [lia | exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)]
    | rewrite P4; apply ER; [lia | exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)]
    | rewrite P8; apply ER; [lia | exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)]
    | rewrite P9; apply ER; [lia | exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)]
    | rewrite P18; apply ER; [lia | exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)]
    | rewrite P19; apply ER; [lia | exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)]
    | rewrite P20; apply ER; [lia | exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)]
    | rewrite P21; apply ER; [lia | exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)]
    | rewrite P22; apply ER; [lia | exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)]
    | rewrite P23; apply ER; [lia | exact (ew_Ereg_nat regs _ 23 23%bv eq_refl)]
    | rewrite P24; apply ER; [lia | exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)]
    | rewrite P25; apply ER; [lia | exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)]
    | rewrite P26; apply ER; [lia | exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)]
    | rewrite P27; apply ER; [lia | exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)] ].
  + exact R1.
  + rewrite R10, <- R21. apply ER; [lia | exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)].
  + intros x. apply HF. intros (r & Hr & _). destruct Hr.
  + exact HJ.
Qed.
End R.

Section L5a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables EC_CCUT EC_LCUT : @ecx rc B_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
(* this lane is after check_no_overread's frees: its cuts and journal are at wle' over the fixed zone *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).

Lemma l5ab_slot_img : forall k e, 0 <= k < 2 ^ 40 -> plookup (ptree_of_list B_prog_listing) k = Some e ->
  in_img SEGS (BASE + k).
Proof.
intros k e Hk40 Hk. pose proof (@pa_B_ok rc B_prog_listing PA) as HB.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
rewrite Z_to_bv_unsigned in Hlo, Hhi. unfold bv_wrap in Hlo, Hhi. change (bv_modulus 64) with (2 ^ 64) in Hlo, Hhi.
rewrite Z.mod_small in Hlo, Hhi by lia.
exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia.
Qed.


Lemma l5ab_shadow_some : forall H m p j, garr8 SEGS (mrestrict H m) p ec_frame_shadow -> (j < 16)%nat ->
  aview SEGS H m (p + Z.of_nat j) <> None.
Proof.
intros H m p j HG Hj. destruct (HG j ltac:(cbn; lia)) as (HV & _). specialize (HV 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in HV. rewrite Z.add_0_r in HV. unfold aview. rewrite HV. discriminate.
Qed.

Lemma l5ab_shadow_zero : forall H m p j, garr8 SEGS (mrestrict H m) p ec_frame_shadow -> (4 <= j <= 10)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some 0.
Proof.
intros H m p j HG Hj. destruct (HG j ltac:(cbn; lia)) as (HV & _). specialize (HV 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in HV. rewrite Z.add_0_r in HV. unfold aview. rewrite HV. cbn [option_map]. f_equal.
assert (Hc : j = 4%nat \/ j = 5%nat \/ j = 6%nat \/ j = 7%nat \/ j = 8%nat \/ j = 9%nat \/ j = 10%nat) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; vm_compute; reflexivity.
Qed.

Lemma l5ab_saved_keep : forall (E : @ecx rc B_prog_listing PA) (W W' : world SEGS) mem mem',
  (forall a, e_sp0 E - 104 <= a < e_sp0 E -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  @ec_saved rc B_prog_listing PA E W mem -> @ec_saved rc B_prog_listing PA E W' mem'.
Proof.
intros E W W' mem mem' Hk Hs. unfold ec_saved in *.
destruct Hs as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
repeat split; (eapply l5ab_rd64_keep; [| eassumption]); intros j Hj; apply Hk; lia.
Qed.

Theorem seg_L5a_B :
  @seg_L5a_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    EC_CCUT EC_LCUT.
Proof.
unfold seg_L5a_stmt, ec_laneR.
intros E fk t D HYP W c Hcut.
pose proof HYP as HTX; apply ech_texts in HTX.
pose proof HYP as HIMG; apply ech_img in HIMG.
pose proof HYP as HCC; apply ech_ccut_ok in HCC.
pose proof HYP as HLC; apply ech_lcut_ok in HLC.
pose proof HTX as HTstk; apply et_stk in HTstk.
pose proof (et_read_members _ _ _ _ _ HTX) as HTrm.
pose proof HIMG as HIframe; apply ei_frame in HIframe.
pose proof (ei_sio _ _ _ _ _ _ HIMG) as HIsio.
pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as HIsiof.
pose proof (ei_pst_ro _ _ _ _ _ _ HIMG) as HIpstro.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt & k & tk & trp & Hat & Hinv & Hro0 & Hccb
  & Hlcb & Hrkd & Hfrm & HnN & R23 & Htk & R24 & Hck & HPm & HNode & Hpjf & HMost & HOwn0).
destruct Hat as (fy & Hfz & Hkept & ->).
destruct Hinv as ((WS0 & HJw & HWB) & HOWN & HLED & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES
  & HMN).
destruct HOWN as (pos & Hown & Hfkeq & Hfk0 & Hflagw). subst own.
(* THE WILD BUDGET: the plain journal from the entry with its depot moved to S's (Ent102CutsB.v ec_journal_rebase); the
   two instructions and the empty-budget read_members call run on it, and ec_journal_unbase returns cut_rm's journal at
   the same budget WS0 (ec_wk_rm = ec_wk_caw: prh_wk F_read_members = 0) *)
assert (HJ : ajournal_xR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E)
  (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly S Hp W mem md k)
  by (eapply ec_journal_rebaseR; exact HJw).
assert (Ewk : ec_wk_rm = ec_wk_caw) by (vm_compute; reflexivity).
destruct HLED as (most0 & own0 & HLED0).
(* the ledger at this cut's two statics, g_most = PJ_ALLOC_BOUND n (ec_most) and g_own_ran_out = 0 (ec_own_is), by
   the record's one copy lib/AU/Prog/Ent102CallB.v ec_ledger_cells *)
pose proof (ec_ledger_cells B ly S Hp W mem Lam peak cnt SIZE_MAX 0 most0 own0 (PJ_ALLOC_BOUND (e_n E)) 0
  HLED0 HMost HOwn0) as HLED.
destruct Hrkd as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27) & R21).
destruct Hfrm as (Hsaved & Hshadow & Hal32).
assert (HPREparts : afn_pre_x SEGS B ARc LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [] /\
  s0Z (e_regs E) < YM05.alloc_ceiling /\ raZ (e_regs E) = EC_RA /\ frames (e_S E) = []).
{ clear - HPRE. unfold ec_pre in HPRE. ec_conj_split HPRE.
  split; [assumption | split; [assumption | split; assumption]]. }
destruct HPREparts as (HPREX & Hs0 & HraE & HfrE).
pose proof HPREX as (_ & _ & Hra40 & _ & _).
pose proof HJw as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HAR as (HARcf & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_val rc) as Hcv.
pose proof (@pa_B_ok rc B_prog_listing PA) as HB.
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).
(* the budget's monotonicity, by index, from ec_ccut_ok / ec_lcut_ok *)
assert (HCCm : forall i j, (i <= j)%nat -> EC_CCUT E j <= EC_CCUT E i)
  by (intros i j Hij; exact (proj2 (HCC E i j) Hij)).
assert (HLCm : forall i j, (i <= j)%nat -> EC_LCUT E j <= EC_LCUT E i)
  by (intros i j Hij; exact (proj2 (HLC E i j) Hij)).
(* the frame of this body *)
destruct (l5ab_A (e_sp0 E) Hal16 ltac:(lia)) as (HA32 & HAlo & HAhi).
change (ec_B (e_sp0 E)) with (e_B E) in HA32, HAlo, HAhi.
(* the fake frame *)
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, HfrE; left; reflexivity).
destruct (alc_frames SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md LLVMF_FS_CLASS pos HARcf Hin)
  as (Gal & Gapp & _ & _).
destruct (alc_sep SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md HARcf) as (_ & Gfor).
rewrite Forall_forall in Gfor. destruct (Gfor _ Hin) as (Glo & Ghi). cbn [fst snd] in Glo, Ghi.
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = 128) by (vm_compute; reflexivity).
rewrite HFB in Gapp, Ghi. rewrite <- Hfkeq in Gal, Gapp, Glo, Ghi.
(* the stack read_members takes *)
assert (HSTK : 0 <= STK_read_members /\ STK_read_members + (e_sp0 E - e_B E) <= LLVMF_STK).
{ pose proof HTstk as Hs. pose proof HIframe as Hf.
  unfold STK_LLVMFuzzerTestOneInput in Hs. unfold EC_SAVE in Hf.
  match type of Hs with _ + zmaxl ?l <= _ =>
    assert (Hm : STK_read_members <= zmaxl l)
      by (apply l5ab_zmaxl_in; cbn [In]; repeat (first [left; reflexivity | right])) end.
  pose proof (pi_frame_nonneg F_read_members) as Hn1.
  pose proof (l5ab_zmaxl_nonneg [STK_pj_get; STK_pj_get_str]) as Hn2.
  unfold STK_read_members in *. lia. }
destruct HSTK as (HSTK0' & HSTK1).
(* the call site *)
unfold EC_ACC, EC_BASE.
change (@pa_val rc B_prog_listing PA A_TEXT + 0x2f8) with (BASE + L5AB_K).
apply (l5ab_run (fx := fy) SK B PST ARc LAWS WLE' (wle'_refl SEGS _) (wle'_trans SEGS _) W regs mem md (ec_doc fk) LLVMF_STK (e_sp0 E) [] (e_ly E)
  (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly S Hp k _ R21 HJ).
intros regs1 mem1 md1 HP1 R1 R10 Hm1 HJ1.
assert (Em : mem1 = mem) by (apply functional_extensionality; exact Hm1). subst mem1. clear Hm1.
assert (Q2 : getr regs1 2 = getr regs 2) by exact (HP1 2 ltac:(unfold acallee_saved; lia)).
assert (Q8 : getr regs1 8 = getr regs 8) by exact (HP1 8 ltac:(unfold acallee_saved; lia)).
assert (Q3 : getr regs1 3 = getr regs 3) by exact (HP1 3 ltac:(unfold acallee_saved; lia)).
assert (Q4 : getr regs1 4 = getr regs 4) by exact (HP1 4 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs1 = e_B E) by (unfold spZ; rewrite Q2, R2; apply unsigned_lit_small; lia).
assert (Us0 : s0Z regs1 = e_sp0 E) by (unfold s0Z; rewrite Q8, R8; apply unsigned_lit_small; lia).
assert (Ura : raZ regs1 = BASE + L5AB_RET) by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold L5AB_RET; lia).
(* the return pc is a text address of the image *)
assert (Himg : in_img SEGS (BASE + L5AB_RET)).
{ assert (Hk : exists e, plookup (ptree_of_list B_prog_listing) 768 = Some e) by (eexists; vm_compute; reflexivity).
  destruct Hk as (e & Hk). exact (l5ab_slot_img 768 e ltac:(lia) Hk). }
assert (HimgB : kImgLo <= BASE + L5AB_RET < kImgEnd).
{ pose proof (alx_img SEGS B ARc LAWS ly S Hp W mem md HAR) as (Hseg & _).
  pose proof (lo_img _ (alx_layout_ok SEGS B ARc LAWS ly S Hp W mem md HAR)) as (Li0 & _ & Li1 & _).
  destruct Himg as (sg & Hsg & Hsa). destruct (Hseg sg Hsg) as (Hs1 & Hs2). lia. }
(* the callee's text *)
assert (HrmK : forall a, ec_doc fk <= a < ec_doc fk + 56 -> ~ (spZ regs1 - STK_read_members <= a < spZ regs1)).
{ intros a Ha. unfold ec_doc in Ha. rewrite Usp. lia. }
assert (Hra64 : 0 <= raZ (e_regs E) < 2 ^ 64)
  by (unfold raZ; apply bv_unsigned_in_range).
assert (Hs064 : 0 <= bv_unsigned (getr (e_regs E) 8) < 2 ^ 64)
  by apply bv_unsigned_in_range.
assert (Hsp8 : (e_sp0 E) mod 8 = 0)
  by (apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as (q & Hq);
      rewrite Z.mod_divide by lia; exists (2 * q); lia).
assert (Hchain : exists ch1, achain ly (aview SEGS (w_H W) mem) (spZ regs1) (s0Z regs1) ch1).
{ rewrite Usp, Us0. destruct Hsaved as (Sra & Ss0 & _).
  destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (e_B E) (e_sp0 E) (raZ (e_regs E)) (bv_unsigned (getr (e_regs E) 8))
    Sra Ss0 Hra64 Hs064 ltac:(unfold s0Z in Hs0; exact Hs0) Hra40 ltac:(lia) Hsp8 ltac:(lia) ltac:(lia))
    as (ch1 & Hch1 & _).
  exists ch1. exact Hch1. }
destruct Hchain as (ch1 & Hch1).
assert (HPRE1 : afn_pre_x SEGS B ARc STK_read_members ly S Hp W regs1 mem md1 ch1).
{ eapply (afn_pre_x_atR SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E)
    (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly S Hp W mem md1 k regs1 STK_read_members (e_B E - e_sp0 E) ch1 HJ1).
  - rewrite Usp. lia.
  - pose proof (Z.div_mod (e_B E) 32 ltac:(lia)). pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)).
    rewrite Z.mod_divide by lia. exists (2 * (e_B E / 32) - e_sp0 E / 16). lia.
  - lia.
  - exact HSTK0'.
  - lia.
  - rewrite R1. apply ret_ok_codeptr_v; unfold L5AB_RET; [lia | reflexivity].
  - rewrite Ura. unfold kImgLo in HimgB. lia.
  - rewrite Q3, R3. exact (proj1 (proj2 (proj2 (proj2 HPREX)))).
  - rewrite Q4, R4. exact (proj1 (proj2 (proj2 (proj2 (proj2 HPREX))))).
  - exact Hch1. }
(* read_members' text is NOT crossing (no free): its plain SRr lifts to SRr' (YA0nH.SRr_SRr'), its post's journal at wle
   is read at wle' (YCbqG.ajournal_xwR_mono with YA0nH.wle_wle') where it composes with the lane's *)
eapply (SRrG_mono SEGS WLE').
{ apply (SRr_SRr' SEGS (@YGcfRehidePost.RZ_cf rc)).
  apply (HTrm fy ly S Hp W regs1 mem md1 ch1 (ec_doc fk) t D Lam peak cnt SIZE_MAX 0 (PJ_ALLOC_BOUND (e_n E)) 0).
  - split; [exact HPRE1|]. split; [exact HRO|]. split.
    + rewrite Usp, Eshi. lia.
    + split; [rewrite Ura; unfold kImgEnd in HimgB; lia|exact Hfz].
  - exact R10.
  - exact HNode.
  - unfold prhPj_rslot. unfold ec_doc. split; [lia|]. split.
    { right; left. exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite <- Hfkeq, HFB. lia. }
    split.
    { unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
    split; [exact HrmK|].
    split.
    + intros x Hx. exists 0. split; [|left; reflexivity].
      destruct (l5ab_shadow_idx fk x ltac:(lia) Hal32 ltac:(lia)) as (Eidx & Hix4 & Hix10).
      unfold shadow_of_addr. rewrite Eidx.
      replace ((x - fk) / 8) with (Z.of_nat (Z.to_nat ((x - fk) / 8))) by (rewrite Z2Nat.id; lia).
      apply l5ab_shadow_zero; [exact Hshadow|].
      split; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; cbn [Z.of_nat]; lia.
    + intros s Hs. destruct (l5ab_hull_window fk s ltac:(lia) Hal32 Hs) as (Hs1 & Hs2).
      replace s with (shadow_addr fk + Z.of_nat (Z.to_nat (s - shadow_addr fk))) by (rewrite Z2Nat.id; lia).
      apply l5ab_shadow_some; [exact Hshadow|].
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. cbn [Z.of_nat]. lia.
  - exact HLED. }
intros W2 c2 Hle Hpost.
unfold fpostm, fpost, apost_base_x, fQmn in Hpost.
destruct Hpost as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & HP2 & Hpq & Hmn2).
destruct Hpq as (-> & -> & Hab & HLED2 & _ & HNode2).
pose proof HJc as (_ & Hly2 & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
assert (HJ2 : ajournal_xR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E)
  (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E) ([] ++ [(LLVMF_FS_CLASS, pos)]) ly2 S Hp W2 mem2
  md2 (k + k1)).
{ eapply (ajournal_x_subR SEGS B PST ARc LAWS pa_segs_low WLE' (wle'_trans SEGS _));
    [exact HJ1
    | apply (YCbqG.ajournal_xwR_mono SEGS B PST ARc (@wle SEGS) WLE' (wle_wle' SEGS _)); exact HJc
    | rewrite Usp; lia | rewrite Usp; lia |].
  intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbn [app] in HJ2.
(* what the call keeps *)
assert (KST : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (e_B E - STK_read_members <= a < e_B E) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. apply K1; [exact Ha | rewrite Usp; exact Hn]. }
assert (KFR : forall a, fk <= a < fk + 128 \/ shadow_addr fk <= a < shadow_addr fk + 16 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (K4 LLVMF_FS_CLASS pos a Hin).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfkeq, HFB. change (128 / 8) with 16. lia.
  - exact (inFP_nil a). }
assert (KIM : forall a, in_img SEGS a -> ec_static_free B a -> ~ Exists (in_zr a) PST ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Hi (Ho & He) Hp'. apply K3; [exact Hi | exact Ho | exact He | exact Hp' |].
  apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by exact (l5ab_aregs_trans regs regs1 regs2 HP1 HP2).
assert (M2 : getr regs2 2 = getr regs 2) by exact (P 2 ltac:(unfold acallee_saved; lia)).
assert (M3 : getr regs2 3 = getr regs 3) by exact (P 3 ltac:(unfold acallee_saved; lia)).
assert (M4 : getr regs2 4 = getr regs 4) by exact (P 4 ltac:(unfold acallee_saved; lia)).
assert (M8 : getr regs2 8 = getr regs 8) by exact (P 8 ltac:(unfold acallee_saved; lia)).
assert (M9 : getr regs2 9 = getr regs 9) by exact (P 9 ltac:(unfold acallee_saved; lia)).
assert (M18 : getr regs2 18 = getr regs 18) by exact (P 18 ltac:(unfold acallee_saved; lia)).
assert (M19 : getr regs2 19 = getr regs 19) by exact (P 19 ltac:(unfold acallee_saved; lia)).
assert (M20 : getr regs2 20 = getr regs 20) by exact (P 20 ltac:(unfold acallee_saved; lia)).
assert (M21 : getr regs2 21 = getr regs 21) by exact (P 21 ltac:(unfold acallee_saved; lia)).
assert (M23 : getr regs2 23 = getr regs 23) by exact (P 23 ltac:(unfold acallee_saved; lia)).
assert (M26 : getr regs2 26 = getr regs 26) by exact (P 26 ltac:(unfold acallee_saved; lia)).
assert (M27 : getr regs2 27 = getr regs 27) by exact (P 27 ltac:(unfold acallee_saved; lia)).
exists ly2, S, Hp, regs2, mem2, md2, [(LLVMF_FS_CLASS, pos)], Lam, peak, cnt, (k + k1), tk, trp.
split.
{ exists fy. split; [exact Hfz|]. split; [exact Hkept|].
  unfold cfg_at, EC_AR_RM, EC_BASE. rewrite R1. reflexivity. }
split.
{ (* cut_rm's journal at cut_acc's budget WS0, unbased (read_members' text is the empty-budget one) *)
  split; [exists WS0; split; [eapply ec_journal_unbaseR; [exact HJw | exact HJ2] | rewrite Ewk; exact HWB]|].
  split.
  { exists pos. split; [reflexivity|]. unfold frame_addr, flag_addr in *. rewrite EF2.
    split; [exact Hfkeq|]. split; [exact Hfk0|].
    eapply l5ab_rd64_keep; [|exact Hflagw]. intros j Hj. apply KFR. left. unfold EC_FRAME_BYTES. lia. }
  split; [exists (PJ_ALLOC_BOUND (e_n E)), 0; exact HLED2|].
  split.
  { apply (HIsiof (aview SEGS (w_H W) mem)); [|exact HSIO].
    intros a Ha. destruct (HIsio a Ha) as (Hf & Hi & Hp'). exact (KIM a Hi Hf Hp'). }
  split.
  { intros a Hro Ho He. rewrite (KIM a); [exact (HRO a Hro Ho He) | | split; [exact Ho | exact He] |].
    - destruct Hro as [(s & Hs & _ & Hsa) | Hr]; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)].
    - intros Hp'. exact (HIpstro a Hp' Hro). }
  split; [exact HLIVE|].
  split; [exact HROOM|].
  split; [exact HCNT|].
  split; [exact HPRE|].
  split; [rewrite Hab; exact HPAY|].
  split; [rewrite Hab; exact HPERM|].
  split.
  { intros i Hi. rewrite <- (HBYTES i Hi).
    destruct HPAY as [Hn0|Hpn]; [lia|].
    apply (K2 (e_p E) (e_n E) i); [exact Hpn | rewrite Hab; exact Hpn | | exact (inFP_nil _)].
    pose proof (req_size_pos (e_n E) ltac:(lia)). lia. }
  exact (Hmn2 HMN). }
split; [exact Hro0|].
split.
{ lazymatch goal with |- _ + EC_CCUT _ ?j <= _ =>
    lazymatch type of Hccb with _ + EC_CCUT _ ?i <= _ => pose proof (HCCm i j ltac:(lia)) end end. lia. }
split.
{ lazymatch goal with |- _ + EC_LCUT _ ?j <= _ =>
    lazymatch type of Hlcb with _ + EC_LCUT _ ?i <= _ => pose proof (HLCm i j ltac:(lia)) end end. lia. }
split.
{ split; [|rewrite M21; exact R21].
  split; [rewrite M2; exact R2|].
  split; [rewrite M3; exact R3|].
  split; [rewrite M4; exact R4|].
  split; [rewrite M8; exact R8|].
  split; [rewrite M9; exact R9|].
  split; [rewrite M18; exact R18|].
  split; [rewrite M19; exact R19|].
  split; [rewrite M20; exact R20|].
  split; [rewrite M26; exact R26|].
  rewrite M27; exact R27. }
split.
{ split.
  - apply (l5ab_saved_keep E W W2 mem mem2); [|exact Hsaved].
    intros a Ha. apply KST; lia.
  - split; [|exact Hal32].
    eapply garr8_aview; [|exact Hshadow].
    intros i Hi. cbn [length ec_frame_shadow repeat app] in Hi. apply KFR. right. lia. }
split; [exact HnN|].
split; [rewrite M23; exact R23|].
split; [exact Htk|].
split; [exact Hck|].
split; [exact HPm|].
split; [exact HNode2|].
split.
{ (* THE FREE ORDER IS KEPT (PRH_PjOrder.pj_foR_frame): read_members writes only its own frame, so the bytes of the
     tree's footprint - the doc slot in the fake frame and the harness blocks - are the same after the call, and each
     is still present (the frame law and the blocks law of the post-call state) *)
  pose proof HJc as (HAR2 & _). pose proof HAR2 as (HAR2cf & _).
  destruct (alc_frames SEGS B (AR_laws_ok_cf SEGS B) ly2 S Hp W2 mem2 md2 LLVMF_FS_CLASS pos HAR2cf Hin)
    as (_ & _ & Gpr2 & _).
  assert (EFa : frame_addr ly2 LLVMF_FS_CLASS pos = fk)
    by (rewrite Hfkeq; unfold frame_addr; rewrite EF2; reflexivity).
  rewrite HFB, EFa in Gpr2.
  unfold ec_pjf in Hpjf |- *. intros n Hn. destruct (Hpjf n Hn) as (F & HF & HFm).
  exists F. split; [|exact HFm].
  eapply PRH_PjOrder.pj_foR_frame; [exact HF | exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF) |].
  intros x [Hx | ((a0 & k0) & HinD & Hx)].
  - unfold ec_doc in Hx. split.
    + apply S1Ledger.prh_mbyte_of_aview. apply KFR. left. lia.
    + intros _. apply (apresent_writable SEGS). exact (proj1 (Gpr2 x ltac:(lia))).
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    pose proof (S1Ledger.prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAX 0 a0 k0 _ _ HLED
      (Permutation_in _ (Permutation_sym HPm) HinD)) as (Hk0 & Hb & _).
    assert (Hb2 : In (a0 - cf_head, k0 + cf_head) (ablocks B ly2 S)) by (rewrite Hab; exact Hb).
    pose proof cf_head_nonneg as C0.
    assert (Hrq : k0 + cf_head <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    split.
    + apply S1Ledger.prh_mbyte_of_aview.
      replace x with (a0 - cf_head + (x - (a0 - cf_head))) by lia.
      apply (K2 (a0 - cf_head) (k0 + cf_head) (x - (a0 - cf_head)) Hb Hb2); [lia | exact (inFP_nil _)].
    + intros _. apply (apresent_writable SEGS).
      pose proof (alc_blocks SEGS B (AR_laws_ok_cf SEGS B) ly2 S Hp W2 mem2 md2 _ _ HAR2cf Hb2)
        as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr x ltac:(lia))). }
split; [pose proof HLED2 as Gmost; apply PRH_Base.prh_ledger_most in Gmost; exact Gmost|].
pose proof HLED2 as Gown; apply PRH_Base.prh_ledger_own in Gown; exact Gown.
Qed.

End L5a.

Check seg_L5a_B.
Print Assumptions seg_L5a_B.
