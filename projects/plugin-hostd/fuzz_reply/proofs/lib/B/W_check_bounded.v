(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's check_bounded, a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), after lib/A/W_check_bounded.v (7086983dbc8), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v and lib/A/ACbk.v, with its loop in the form of lib/A/AC8b.v tcbb_loopX. *)
(* check_bounded() at 0x856a0 (image B; 0x85304 in A) walks the g_nsrc entries of the relay table g_src and aborts when an entry's
   used or cap is out of bounds.  The loop is its own lemma (cb_loopX), from a fresh symbolic state at the
   loop head, by induction on the entries left; the outer walk runs to the loop head, takes the lemma, and
   splices its result back with jafter_stretch_pi.  B's UBSan traps (all to `unimp` at 0x85764; UBSan is trap mode in
   this pin) are refuted from the same facts: the pointer-overflow trap `bltu t1,a2` (0x856ec) by trap_ptr_bltu (t1 = P + 56 i >= P),
   the null check `seqz/xor/beqz` (0x856f0-0x856f8) by trap_null_xor_folded (the runner folds seqz t1 to 0), and the
   base's alignment and null check `beqz a6` (0x856fc) by the runner itself from a6 = 1 (trap_w_base_ok at the loop's
   entry, a live block is 16-aligned and >= 4096).  The trap lemmas are lib/B/W_traps.v's.  The abort arms are refuted from the contract's
   functional half; the two shadow checks per entry are decided inside paj_run_tok. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_journal W_contract W_img W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x.
(* route R: the leaf contract twins (a Theorem Labs lane's W_contract_leaf_xR.v, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_leaf_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_check_bounded : Z := AF_fr_check_bounded.
Definition A_check_boundedP : Z := BASE + A_check_bounded.
Definition A_cb_loop : Z := AF_fr_check_bounded + 0x4c.
Definition A_cb_exit : Z := AF_fr_check_bounded + 0xb0.
(* The four image objects the walk reads (the GOT slot of the shadow cell, the shadow cell, g_nsrc and g_src)
   are apart.  The abstract placement PAImg does not fix the objects' values relative to each other, so this
   is a Section hypothesis, discharged at the pinned placement PB_fr (W_img.v) by vm_compute. *)
Definition cb_objs_apart : Prop :=
let g := VAL (A_OBJ 0) in let c := VAL (A_OBJ 30) in let ns := VAL A_g_nsrc in let sr := VAL A_g_src in
(ns + 4 <= sr \/ sr + 8 <= ns) /\ (ns + 4 <= g \/ g + 8 <= ns) /\ (ns + 4 <= c \/ c + 8 <= ns) /\
(sr + 8 <= g \/ g + 8 <= sr) /\ (sr + 8 <= c \/ c + 8 <= sr).
(* ---- THE GENERIC WALK (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): check_bounded over any allocator relation
   ARx with its laws, stated as W_contract_x.cb_spec_x.  The Section hypotheses beyond the AR walk's: PST / ARx / hl /
   LAWS (the generic relation), HP0 (the unit's hidden-head set is empty in every ARx state: fuzz_reply calls no poison
   routine; a Theorem Labs lane's ruling, so YCbqG.ARx_shadow_law's premise holds at every state: W_journal_x's
   range_addressable_of_block_hp0_x).  A's IMGC / BLKN (W_kit_x.v Section g, for blk_off_imgP_x) are not taken:
   image B's walk never separates the block from the image top (no blk_off_imgP in its AR form). ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis CBAP : cb_objs_apart.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let HG0 : gx_ok SEGS B [] := gx_ok_nil SEGS B.
Let RUN := paj_run_x_x B PST ARx LAWS [] HG0 0 []. Let RUNTO := paj_run_to_x_x B PST ARx LAWS [] HG0 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx [] 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition CB_PHI : Z := 140737479966720.
(* the loop head 0x856ec: t1 = P+56i (entry i), a5 = P+32+56i (cap of entry i), a1 = entries left, a2 = P,
   a3 = SB, a4 = (P <> 0) = 1, a6 = (P % 8 = 0 && P <> 0) = 1, a7 = 6000, t0 = 631 *)
Definition BxL : sv := SOff 13 0.
Definition cbl_regions : smem :=
[ YP09.mkRegion (Some 15%nat) (-8) 8 0 0 [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition cbl_facts : facts :=
mkFacts [ (6%nat, mkAF 4096 CB_PHI 3); (13%nat, mkAF SB SB 0); (14%nat, mkAF 1 1 0); (15%nat, mkAF 4096 CB_PHI 3);
(16%nat, mkAF 1 1 0); (32%nat, mkAF 0 6000 0); (33%nat, mkAF 0 20191 0) ] [] [].
Definition ss_cbl : sstate := mkSS A_cb_loop sr_atoms cbl_regions None cbl_facts.
Definition cbl_SH : list shent := [ mkSHE 6 24 32; mkSHE 6 32 40 ].
Definition cbl_extra (u c : Z) : list word := map (Z_to_bv 64) [u; c].
Definition CB_CLOB : list (bv 5) := [6; 7; 10; 11; 15; 28]%bv.
Definition CB_KEPT : list (bv 5) := [1; 2; 3; 4; 5; 8; 9; 12; 13; 14; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.
Lemma cb_clob_kept : forall r : bv 5, reg_in r CB_CLOB = false -> r = 0%bv \/ In r CB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Ltac cb_nowr := let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin; destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
(* after a run whose regions have no writable window: the memory the run ends in is the one it began in *)
Ltac cb_meq MEQ MEQ' :=
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict ?H ?msx), HFr : frame_of _ _ _ _ |- _ =>
lazymatch type of MEQ with forall x, mrestrict _ _ x = mrestrict _ ?m0 x =>
assert (MEQ' : forall x, mrestrict H (ms_mem msx) x = mrestrict H m0 x)
by (let x := fresh "x" in intros x; rewrite HFr; [apply MEQ | cb_nowr]) end end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end; clear MEQ.
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
Ltac cb_awr := first [ awr_any | cbn [ss_mem add_cond]; awr_any |
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [ss_mem add_cond ss_cbl cbl_regions In] in Hin; destruct Hin as [<- | []];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia ].
Lemma cb_loopX_x : forall (k : nat) (i n P N : Z) W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc kk,
Z.of_nat k = n - i -> 0 <= i < n -> n < 2 ^ 31 ->
AJG STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc kk ->
In (P, N) (ablocks B lyc Sc) -> 56 * n <= req_size N ->
getr regs 6 = w64 (P + 56 * i) -> getr regs 15 = w64 (P + 32 + 56 * i) ->
getr regs 11 = w64 (n - i) -> getr regs 12 = w64 P -> getr regs 13 = w64 SB ->
getr regs 14 = w64 1 -> getr regs 16 = w64 1 -> getr regs 17 = w64 6000 -> getr regs 5 = w64 631 ->
(forall j, i <= j < n -> cb_entry_ok W memc P j) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cb_loop)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cb_exit)) mem' (seg_rom SEGS)) md' /\
AJG STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' kk /\
(forall r, In r CB_KEPT -> getr regs' r = getr regs r) /\
(forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) memc x)).
Proof.
induction k as [|k IH]; intros i n P N W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc kk
Hk Hi Hn HJ HPin HPN H6 H15 H11 H12 H13 H14 H16 H17 H5 HENT; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAR : ARx lyc Sc Hpc W memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc P N HAR HPin) as (HP16 & HP4096 & HPceil & HPh_ia & _ & _).
pose proof (proj1 HPh_ia) as HPh.
assert (PB : 4096 <= P /\ P + 56 * n <= 0x7fffff800000) by lia.
assert (P8 : P = 8 * (P / 8)).
{ pose proof (Z.div_mod P 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (P / 16)) with ((2 * (P / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
destruct (HENT i ltac:(lia)) as (u & c & Mu & Mc & Ru & Ruc & Rc).
remember (Eimg (Ereg regs (cbl_extra u c))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (cbl_extra u c)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E6 : ew E 6 = Z_to_bv 64 (P + 56 * i)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact H6).
assert (E13 : ew E 13 = Z_to_bv 64 SB) by (rewrite (EEo 13%nat 13%bv eq_refl); exact H13).
assert (E14 : ew E 14 = Z_to_bv 64 1) by (rewrite (EEo 14%nat 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 (P + 32 + 56 * i)) by (rewrite (EEo 15%nat 15%bv eq_refl); exact H15).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (rewrite (EEo 16%nat 16%bv eq_refl); exact H16).
assert (E32 : ew E 32 = Z_to_bv 64 u) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok_pi SEGS VAL E ss_cbl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cb_loop)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cbl. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cbl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E15, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS E _ (P + 32 + 56 * i) (-8) 8 (SOff 32 0) u);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (P + 32 + 56 * i + -8) with (P + 56 * i + 24) by lia. exact Mu.
  + apply (chunk_ok_val SEGS E _ (P + 32 + 56 * i) 0 8 (SOff 33 0) c);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (P + 32 + 56 * i + 0) with (P + 56 * i + 32) by lia. exact Mc.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [cbl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E6, E13, E14, E15, E16, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert P8 HP4096 HPceil HPN Hi Ru Ruc Rc C1. clear. unfold CB_PHI, SB. intros.
  repeat match goal with |- _ /\ _ => split end; try lia;
  rewrite P8; first [ replace (8 * (P / 8) + 32 + 56 * i) with ((P / 8 + 4 + 7 * i) * 8) by ring; apply Z_mod_mult
  | replace (8 * (P / 8) + 56 * i) with ((P / 8 + 7 * i) * 8) by ring; apply Z_mod_mult ]. }
clear HE.
assert (HBx : U E BxL = SHADOW_OFF) by (unfold BxL; rewrite (U_atom E 13 SB E13) by (unfold SB; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxL cbl_SH E (mrestrict (w_H W) memc)).
{ constructor; [|constructor; [|constructor]].
  - eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc P N (P + 56 * i + 24) 8 HAR HPin); lia.
    + exact HBx.
    + rewrite (U_atom E 6 _ E6) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - eapply shent_ok_of_range.
    + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc P N (P + 56 * i + 32) 8 HAR HPin); lia.
    + exact HBx.
    + rewrite (U_atom E 6 _ E6) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
assert (E5 : ew E 5 = Z_to_bv 64 631) by (rewrite (EEo 5%nat 5%bv eq_refl); exact H5).
assert (E11 : ew E 11 = Z_to_bv 64 (n - i)) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 P) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E17 : ew E 17 = Z_to_bv 64 6000) by (rewrite (EEo 17%nat 17%bv eq_refl); exact H17).
assert (USR : U E (SAlu ALU_SRL (SOff 33 0) (SLit 5)) = c / 32).
{ rewrite U_SAlu, (U_atom E 33 c E33), U_lit by lia. cbn [zalu_raw]. change (Z.land 5 63) with 5.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. unfold zcanon, M64.
  apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
assert (C631 : c / 32 < 631) by (apply Z.div_lt_upper_bound; lia).
unfold A_cb_loop.
(* 0x856ec bltu t1,a2: the UBSan pointer-overflow trap, never taken: t1 = P + 56 i >= P *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite (trap_ptr_bltu E (SOff 12 0) (SOff 6 0) P (P + 56 * i) (U_atom E 12 P E12 ltac:(lia)) (U_atom E 6 _ E6 ltac:(lia)) ltac:(lia)) in Hc.
  discriminate.
- paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; cb_awr. }
  assert (MEQ1 : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) memc x) by (intros x; apply HFr; cb_nowr).
  clear HF HFr HG.
  (* 0x856f8 beqz a0: the UBSan null-check trap, never taken; the next one, 0x856fc beqz a6, the runner decides from
     the loop state's fact a6 = 1 *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite (trap_null_xor_folded E 14 E14) in Hc0. discriminate.
  + paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; cb_awr. }
    cb_meq MEQ1 MEQ2.
    (* 0x85718 bltu a7,t2: used > LINE_LIMIT, the abort arm *)
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * exfalso. rewrite branch_ltu_U, (U_atom E 17 6000 E17), (U_atom E 32 u E32) in Hc1 by lia.
      apply Z.ltb_lt in Hc1. lia.
    * paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; cb_awr. }
      cb_meq MEQ2 MEQ3.
      (* 0x85734 bltu a0,t2: cap < used, the abort arm *)
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- exfalso. rewrite branch_ltu_U, (U_atom E 33 c E33), (U_atom E 32 u E32) in Hc2 by lia;
           apply Z.ltb_lt in Hc2; lia.
      -- paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; cb_awr. }
         cb_meq MEQ3 MEQ4.
         (* 0x8573c bgeu a0,t0: cap >= 2 * (LINE_LIMIT + 4096), the abort arm *)
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ exfalso. rewrite branch_geu_U, USR, (U_atom E 5 631 E5) in Hc3 by lia.
            apply (proj1 (Bool.negb_true_iff _)) in Hc3. apply Z.ltb_ge in Hc3. lia.
         ++ paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; cb_awr. }
            cb_meq MEQ4 MEQ5.
            (* 0x8574c bnez a1: entries left *)
            psrr_branch_tok RUN BR HS SHOK Bspan.
            ** rewrite branch_ne_U, (U_atom_off E 11 (n - i) (-1) E11), U_lit in Hc4 by lia.
               assert (Hlt : i + 1 < n) by (destruct (Z.eqb_spec (n - i + -1) 0); [discriminate | lia]).
               paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_bounded + 76). { apply awr_ok_x_of0; cb_awr. }
               cb_meq MEQ5 MEQ6.
               pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ CB_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
               cbn [ms_regs restrict] in HK.
               prreg HS (6%bv : bv 5) N6. prreg HS (11%bv : bv 5) N11. prreg HS (15%bv : bv 5) N15.
               rewrite E6, unsigned_lit_small in N6 by lia. rewrite E11, unsigned_lit_small in N11 by lia.
               rewrite E15, unsigned_lit_small in N15 by lia.
               lazymatch type of MEQ6 with forall x, mrestrict ?H0 ?m0 x = _ =>
                 assert (MEQf : mrestrict H0 m0 = mrestrict (w_H W) memc) by (apply functional_extensionality; exact MEQ6) end.
               pmkst HS.
               eapply SRr_mono.
               { unfold A_cb_loop in IH.
                 eapply (IH (i + 1) n P N W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc kk);
                 [ lia | lia | lia | exact HJ | exact HPin | exact HPN
                 | cbn [ms_regs]; rewrite N6; unfold w64; f_equal; lia
                 | cbn [ms_regs]; rewrite N15; unfold w64; f_equal; lia
                 | cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia
                 | cbn [ms_regs]; rewrite (HK 12%bv ltac:(cbv; tauto)); exact H12
                 | cbn [ms_regs]; rewrite (HK 13%bv ltac:(cbv; tauto)); exact H13
                 | cbn [ms_regs]; rewrite (HK 14%bv ltac:(cbv; tauto)); exact H14
                 | cbn [ms_regs]; rewrite (HK 16%bv ltac:(cbv; tauto)); exact H16
                 | cbn [ms_regs]; rewrite (HK 17%bv ltac:(cbv; tauto)); exact H17
                 | cbn [ms_regs]; rewrite (HK 5%bv ltac:(cbv; tauto)); exact H5
                 | intros j Hj; cbn [ms_mem]; unfold cb_entry_ok; rewrite MEQf; exact (HENT j ltac:(lia)) ]. }
               cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & MEQ7).
               split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split.
               { intros r Hr. rewrite (HK3 r Hr). cbn [ms_regs]. exact (HK r Hr). }
               intros x. rewrite MEQ7. cbn [ms_mem]. apply MEQ6.
            ** rewrite branch_ne_U, (U_atom_off E 11 (n - i) (-1) E11), U_lit in Hc4 by lia.
               assert (Heq : i + 1 = n) by (destruct (Z.eqb_spec (n - i + -1) 0); [lia | discriminate]).
               paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_bounded + 176). { apply awr_ok_x_of0; cb_awr. }
               cb_meq MEQ5 MEQ6.
               pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ CB_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
               cbn [ms_regs restrict] in HK.
               pmkst HS.
               apply SRr_ret. split; [reflexivity|].
               lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
               split; [reflexivity|]. split; [exact HJ|]. split; [exact HK | exact MEQ6].
Qed.
(* presence across the runs: chain every run's mem_grows from the entry memory to the current one *)
Ltac cb_pres :=
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
repeat match goal with
| HG' : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), Hp : apresent ?H ?m1 a |- _ =>
  lazymatch goal with _ : apresent H m2 a |- _ => fail | _ => idtac end;
  assert (apresent H m2 a) by (eapply apresent_grows; [exact HG' | exact Hp])
end; assumption.
(* the outer walk's regions: only the stack region has a writable window, so a byte outside the frame is
   outside every region's window *)
Ltac cb_nowr5 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [<- | Hin];
 [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ 2) = _ |- _ => rewrite Hu in Hr end;
  first [lia | match goal with Hno : ~ _ |- _ => apply Hno; unfold CB_STK in *; lia end] |]);
destruct Hin.
(* the entry 0x856a0 *)
(* a byte that stays present stays writable, in the same world (W_list_drop's writable_kept_w at wle refl) *)
Lemma cb_writable_kept : forall (W : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W) m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W) m') a.
Proof.
intros W m m' a Hp Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Definition Bx : sv := SOff 34 0.
Definition cb_regions : smem :=
[ stack_region CB_STK; got_regionP; bcell_regionP 34;
YP09.mkRegion (Some A_g_nsrc) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
YP09.mkRegion (Some A_g_src) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition cb_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF 0 (2 ^ 32 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0);
(34%nat, mkAF SB SB 0) ] [] [].
Definition ss_cb : sstate := mkSS A_check_bounded sr_atoms cb_regions None cb_facts.
Definition cb_SH : list shent := [].
Definition cb_extra (n P : Z) : list word := map (Z_to_bv 64) [n mod 2 ^ 32; P; SB].
Lemma cb_entry_x : forall W ly S Hp regs mem md ch n P,
afn_pre_x SEGS B ARx CB_STK ly S Hp W regs mem md ch ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 (n mod 2 ^ 32) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_src) 8 P -> 0 <= P < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cb_extra n P))) ss_cb
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_boundedP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cb_SH (Eimg (Ereg regs (cb_extra n P))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch n P HPRE Mn MP RP.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CB_STK = 16) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)) as Rn.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cb_extra n P))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (n mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 31)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 4 ltac:(lia)) as HnsR. pose proof (pa_obj_img 5 ltac:(lia)) as HsrR.
change (A_OBJ 4) with A_g_nsrc in HnsR. change (A_OBJ 5) with A_g_src in HsrR.
pose proof CBAP as (D1 & D2 & D3 & D4 & D5). cbv zeta in D1, D2, D3, D4, D5.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 31)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_cb, A_check_boundedP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cb_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite (EO 30%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 30%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 34 0) SB);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* unfold A_g_nsrc. rewrite (VBO 4%nat ltac:(lia)). fold A_g_nsrc. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_nsrc) 0 4 (SOff 32 0) (n mod 2 ^ 32));
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mn.
* unfold A_g_src. rewrite (VBO 5%nat ltac:(lia)). fold A_g_src. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL A_g_src) 0 8 (SOff 33 0) P);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact MP.
+ apply pairwise_disjoint_of_extents. unfold cb_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
unfold A_g_nsrc, A_g_src. rewrite (VBO 0%nat ltac:(lia)), (VBO 30%nat ltac:(lia)), (VBO 4%nat ltac:(lia)), (VBO 5%nat ltac:(lia)).
fold A_g_nsrc A_g_src. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HnsR HsrR D1 D2 D3 D4 D5. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Rn RP. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cb_SH. constructor.
Qed.
Theorem pb_check_bounded_x : cb_spec_x B PST ARx A_check_boundedP.
Proof.
intros W ly S Hp regs mem md ch n P N HPRE Rn Mn MP RP HBLK HENT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cb_entry_x W ly S Hp regs mem md ch n P HPRE Mn MP RP) as [HS SHOK].
assert (HJ : AJG CB_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp W mem md 0)
by (apply ajournal_gx_nil_x; exact (ajournal_x_init SEGS B PST ARx CB_STK [] ly S Hp W regs mem md ch HPRE)).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs (cb_extra n P))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (n mod 2 ^ 32)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cb_extra n P)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_check_boundedP) with (Z_to_bv 64 A_check_boundedP).
unfold A_check_boundedP, A_check_bounded.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CB_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno; apply (aview_kept_out E _ (w_H W) mem (ms_mem ms) HFr a Ha); cb_nowr5).
psrr_branch_tok RUN BR HS SHOK Bspan.
-
(* g_nsrc <= 0: no entry, straight to the return *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0; awr_any. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CB_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno;
    match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by cb_nowr5 end;
    apply KEEP0; assumption).
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (cb_extra n P) HS); [exact HAE | vm_compute; reflexivity] end.
+ cbn [ms_mem]. cb_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP1 a Ha Hno)|].
  apply cb_writable_kept. clear Ha Hno. revert a. cb_pres.
+ exact I.
-
(* g_nsrc > 0: the loop over the entries *)
assert (Hn0 : 0 < n).
{ cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
  lazymatch type of Hc with bv_signed ?z < _ => assert (Hz : bv_signed z = 0) by reflexivity; rewrite Hz in Hc end.
  assert (Hsx : bv_unsigned (sv_denot E (SExt true 32 (SOff 32 0))) = sx32 (n mod 2 ^ 32)).
  { rewrite U_sext32'. f_equal. apply (U_atom E 32 _ E32). pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)). lia. }
  destruct (Z_lt_le_dec n 0) as [Hneg | Hpos].
  - assert (Hm : n mod 2 ^ 32 = n + 2 ^ 32) by (rewrite <- (Z.mod_add n 1 (2 ^ 32)) by lia; apply Z.mod_small; lia).
    rewrite Hm in Hsx. unfold sx32 in Hsx. rewrite Z.mod_small in Hsx by lia.
    destruct (Z.ltb_spec (n + 2 ^ 32) (2 ^ 31)); [lia|].
    rewrite bv_signed_hi in Hc by (rewrite Hsx; lia). rewrite Hsx in Hc. lia.
  - rewrite Z.mod_small in Hsx by lia. unfold sx32 in Hsx. rewrite Z.mod_small in Hsx by lia.
    destruct (Z.ltb_spec n (2 ^ 31)); [|lia].
    rewrite bv_signed_small in Hc by (rewrite Hsx; lia). rewrite Hsx in Hc. exact Hc. }
destruct (HBLK Hn0) as [HPin HPN].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md P N HAR HPin) as (HP16 & HP4096 & HPceil & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (P8 : P = 8 * (P / 8)).
{ pose proof (Z.div_mod P 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
  rewrite D at 2. replace (16 * (P / 16)) with ((2 * (P / 16)) * 8) by ring. rewrite Z.div_mul by lia. lia. }
assert (SXn : sext 64 (bv_extract 0 32 (ew E 32)) = w64 n).
{ assert (Hd : sext 64 (bv_extract 0 32 (ew E 32)) = sv_denot E (SExt true 32 (SOff 32 0)))
  by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  rewrite Hd. apply bv_eq. rewrite U_sext32'. change (bv_unsigned (sv_denot E (SOff 32 0))) with (U E (SOff 32 0)).
  rewrite (U_atom E 32 _ E32) by (pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)); lia).
  rewrite Z.mod_small by lia. unfold sx32. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec n (2 ^ 31)); [|lia]. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_bounded + 76). { apply awr_ok_x_of0; awr_any. exact Usp. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CB_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hno;
    match goal with H : frame_of ?Ev _ (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      rewrite (aview_kept_out Ev _ (w_H W) (ms_mem ms) (ms_mem ms0) H a Ha) by cb_nowr5 end;
    apply KEEP0; assumption).
prreg HS (5%bv : bv 5) T5. prreg HS (6%bv : bv 5) T6. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
prreg HS (13%bv : bv 5) T13. prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
prreg HS (17%bv : bv 5) T17.
rewrite E33 in T6, T12. rewrite SXn in T11. rewrite E34 in T13.
rewrite E33, unsigned_lit_small in T15 by lia. rewrite E33 in T14, T16.
(* the trap facts' positive-P premise; named HPpos, since HP0 is the Section's head-set hypothesis *)
assert (HPpos : 0 < P < 2 ^ 64) by lia.
assert (HP8 : P mod 8 = 0) by (rewrite P8; rewrite Z.mul_comm; apply Z_mod_mult).
rewrite (trap_w_snez P HPpos) in T14. rewrite (trap_w_base_ok P HPpos HP8) in T16.
(* the entries are bytes of the block g_src points at, which the runs to here (writing only the frame) kept *)
assert (KB : forall a, P <= a < P + 56 * n -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof HJ as HJ0. apply ajournal_gx_nil_x in HJ0.
  destruct HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). replace a with (P + (a - P)) by lia.
  apply (F2 P N (a - P) HPin HPin); [lia | apply inFP_nil]. }
assert (HENT0 : forall j, 0 <= j < n -> cb_entry_ok W (ms_mem ms0) P j).
{ intros j Hj. destruct (HENT j Hj) as (u & c & Mu & Mc & Ru). exists u, c. split; [|split; [|exact Ru]].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms0)); [intros q Hq; apply KB; lia | exact Mu].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms0)); [intros q Hq; apply KB; lia | exact Mc]. }
pmkst HS.
eapply SRr_bind.
{ unfold A_cb_loop.
  eapply (cb_loopX_x (Z.to_nat n) 0 n P N W (ms_regs ms0) (ms_mem ms0) _ CB_STK (spZ regs) [] ly S Hp W mem md [] ly S Hp 0);
  [ lia | lia | lia | exact HJ | exact HPin | exact HPN
  | rewrite T6; unfold w64; f_equal; lia
  | rewrite T15; unfold w64; f_equal; lia
  | rewrite T11; f_equal; lia
  | exact T12
  | exact T13
  | exact T14
  | exact T16
  | exact T17
  | exact T5
  | intros j Hj; apply HENT0; lia ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & MEQ3).
assert (HGL : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) mem3)) by (intros x Hx; rewrite MEQ3; exact Hx).
(* back after the loop, at 0x85750: splice the loop's result into the outer state *)
jafter_stretch_pi HS 35%nat regs3 (mrestrict (w_H W) mem3) CB_CLOB (AF_fr_check_bounded + 176) HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. destruct (cb_clob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
{ cbn [ms_mem restrict].
  assert (MEQf : mrestrict (w_H W) mem3 = mrestrict (w_H W) (ms_mem ms0)) by (apply functional_extensionality; exact MEQ3).
  rewrite MEQf. repeat apply Forall_cons; try apply Forall_nil; split; intros; first [reflexivity | assumption]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs3) CB_CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs (cb_extra n P)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Usp3 : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOK2 : sh_ok SEGS Bx cb_SH Ea (mrestrict (w_H W) mem3)) by (unfold sh_ok, cb_SH; constructor).
paj_run_tok_x RUN HS HJ3 SHOK2 Bspan. { apply awr_ok_x_of0; awr_any. exact Usp3. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CB_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  match goal with H : frame_of Ea _ (mrestrict (w_H W) mem3) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
  rewrite (aview_kept_out Ea _ (w_H W) mem3 (ms_mem ms1) H a Ha)
  by (let r := fresh in let Hin := fresh in let Hr := fresh in
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
       rewrite ?Usp3 in Hr; first [lia | apply Hno; unfold CB_STK in *; lia] |]); destruct Hin) end.
  rewrite (aview_eq_of SEGS _ _ _ a (MEQ3 (Z_to_bv 64 a))). apply KEEP1; assumption. }
prreg HS (1%bv : bv 5) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold aleafx_post_x.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1; rewrite OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [|split; [|split; [|split]]].
+ cbn [ms_mem]. apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs). exact HJ3.
+ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (cb_extra n P) HS); [exact HAEa | vm_compute; reflexivity] end.
+ cbn [ms_mem]. cb_pres.
+ cbn [ms_mem]. intros a Ha Hno. split; [exact (KEEP2 a Ha Hno)|].
  apply cb_writable_kept. clear Ha Hno. revert a. cb_pres.
+ exact I.
Qed.

(* ---- route R (group G7-leaf-AB, for a Theorem Labs lane's top_x at R): pb_check_bounded_x at a world relation R, a LIFT with
   no re-proof.  The strict SRr run becomes SRrG SEGS R by SRr_SRrG (WLE_R), and the post's G-journal
   (aleafx_post_x -> aleafx_post_xR) goes to R by W_journal_x.ajournal_gx_xR_mono; W_contract_leaf_xR.v
   cb_spec_xR_of_x is those two steps. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Theorem pb_check_bounded_xR : cb_spec_xR B PST ARx R A_check_boundedP.
Proof. apply (cb_spec_xR_of_x B PST ARx R WLE_R). exact pb_check_bounded_x. Qed.
End wR.

End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_check_bounded's statement is the AR
   walk's, byte-identical, now a corollary of pb_check_bounded_x at ARx := ARi0 (cgif's AR with the head set empty),
   PST := [].  Its Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS: the
   instance builds it once, W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The bridge is W_contract_x
   cb_spec_x_AR0; HP0 at ARi0 is ARi0_hp0. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis CBAP : cb_objs_apart.
Theorem pb_check_bounded : cb_spec B A_check_boundedP.
Proof.
apply cb_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
eapply pb_check_bounded_x; eassumption.
Qed.
End cAR.
End b.
End a.
(* the four image objects the walk reads are apart at the pinned placement PB_fr (lib/B/W_img.v) *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cb_objs_apart_fr : cb_objs_apart (PI := PB_fr).
Proof.
  unfold cb_objs_apart, A_g_nsrc, A_g_src. cbv zeta.
  assert (E0 : pa_val (PAImg := PB_fr) (A_OBJ 0) = 0x9df50) by (vm_compute; reflexivity).
  assert (E30 : pa_val (PAImg := PB_fr) (A_OBJ 30) = 0xa6638) by (vm_compute; reflexivity).
  assert (E4 : pa_val (PAImg := PB_fr) (A_OBJ 4) = 0x5d8d20) by (vm_compute; reflexivity).
  assert (E5 : pa_val (PAImg := PB_fr) (A_OBJ 5) = 0x5d8d40) by (vm_compute; reflexivity).
  rewrite E0, E30, E4, E5. lia.
Qed.
End fr.

