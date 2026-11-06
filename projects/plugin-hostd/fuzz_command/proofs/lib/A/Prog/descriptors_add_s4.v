(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the middle segment of descriptors_add's ASan walk (plugin-hostd/fuzz_command):
   from the join of record()'s two arms (0x8ceac) to the call of xstrdup (0x8ceec), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment that re-seeds at a join and splits on one branch). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas descriptors_add_s1 descriptors_add_m descriptors_add_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the join's symbolic state (0x8ceac): the frame with the caller's seven saved registers (atoms 32..38), the slot
   as the atom of s0, whose window is the two words the segment writes (c->fn and c->nargs) *)
Definition da_extraJ (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) da_saved.
Definition da_slotJ : YP09.region := YP09.mkRegion (Some 8%nat) 0 CALL_SIZE 0 8 [].
Definition da_rsJ : smem := [da_frameM; da_slotJ].
Definition da_factsJ : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (19%nat, mkAF A_G_REC A_G_REC 3); (20%nat, mkAF DA_SB DA_SB 0)] [] [].
Definition ss_daJ : sstate := mkSS DA_JOIN sr_atoms da_rsJ None da_factsJ.
Definition da_BxJ : sv := SOff 20 0.
Definition da_SHJ : list shent := [mkSHE 8 0 CALL_SIZE].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition da_EJ (regsc regs : bvmap 5 word) : env := Eimg (Ereg regsc (da_extraJ regs)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
#[local] Set Default Proof Using "All".
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* --- the join's seed -------------------------------------------------------------------------------------- *)
Lemma da_join : forall lyc Sc (Wc : world SEGS) memc mdc (regsc regs : bvmap 5 word) sp0 c,
AR SEGS B lyc Sc Wc memc mdc ->
bv_unsigned (getr regsc 2) = sp0 - 64 -> sp0 mod 16 = 0 -> 2 ^ 46 + 64 <= sp0 <= 2 ^ 47 ->
da_frame_at (mrestrict (w_H Wc) memc) sp0 regs ->
getr regsc 8 = Z_to_bv 64 c -> da_slot_ok c ->
getr regsc 19 = Z_to_bv 64 A_G_REC -> getr regsc 20 = Z_to_bv 64 DA_SB ->
st_ok_pi SEGS VAL (da_EJ regsc regs) ss_daJ
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + DA_JOIN)) memc (seg_rom SEGS)))
/\ sh_ok SEGS da_BxJ da_SHJ (da_EJ regsc regs) (mrestrict (w_H Wc) memc).
Proof.
intros lyc Sc Wc memc mdc regsc regs sp0 c HAR Hsp Hsp16 Hsp47 Hfr H8 Hc H19 H20.
destruct (da_slot_bounds c Hc) as (Hcb & Hc8 & Hcs).
set (E := da_EJ regsc regs).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. unfold da_EJ. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (da_extraJ regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold da_EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E19 : ew E 19 = Z_to_bv 64 A_G_REC) by (rewrite (EL 19%nat 19%bv eq_refl); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 DA_SB) by (rewrite (EL 20%nat 20%bv eq_refl); exact H20).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite E8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U19 : bv_unsigned (ew E 19) = A_G_REC) by (rewrite E19; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U20 : bv_unsigned (ew E 20) = DA_SB) by (rewrite E20; apply unsigned_lit_small; unfold DA_SB; lia).
split; [| exact (da_slot_sh_ok B TL HB VOBJS cmd_prog_img cmd_prog_writable lyc Sc Wc memc mdc E 8 20 c HAR Hc E8 E20)].
rewrite restrict_mkst_fx. unfold ss_daJ.
apply pa_entry_st_ok_full.
- subst E. unfold da_EJ. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold da_rsJ, da_frameM, da_slotJ.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (Hfj : forall j r, nth_error da_saved j = Some r ->
      YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp0 - 64)
        (YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
    { intros j r Hj. assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
      apply (da_frame_chunk B TL HB VOBJS cmd_prog_img cmd_prog_writable E _ sp0 regs j r Hj Hfr).
      rewrite EX by (cbn in Hj7; lia). unfold da_extraJ.
      apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
    repeat apply Forall_cons; try apply Forall_nil;
    [exact (Hfj 0%nat 1 eq_refl) | exact (Hfj 1%nat 8 eq_refl) | exact (Hfj 2%nat 9 eq_refl)
    | exact (Hfj 3%nat 18 eq_refl) | exact (Hfj 4%nat 19 eq_refl) | exact (Hfj 5%nat 20 eq_refl) | exact (Hfj 6%nat 21 eq_refl)].
  + rewrite U8. split; [unfold A_G_REC, OFF_CALLS in *; lia|].
    split; [unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (cmd_prog_writable lyc Sc Wc memc mdc); [exact HAR|].
    destruct Hc as [(kk & Hkk & ->) | ->]; [apply recb_grec_in | apply recb_spill_in];
    unfold REC_CALLS_MAX, A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, SC_SIZE, CALL_SIZE in *; lia.
- apply pairwise_disjoint_of_extents.
  unfold da_rsJ, da_frameM, da_slotJ, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in *. repeat split; lia.
- split; [|split; exact I]. cbn [da_factsJ f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, U8, U19, U20.
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hsp16' : (sp0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  unfold DA_SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | reflexivity | lia].
Qed.

(* the section hypotheses of the two files this segment builds on, as one prefix each *)
#[local] Notation S1 f := (f B TL HB VOBJS cmd_prog_img cmd_prog_writable).
#[local] Notation S2 f := (f B MT TL HB VOBJS cmd_prog_img cmd_prog_writable SIGP TXSTRDUP TMIX_CALL MTL
  cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart cmd_heap_tail_vis).
(* a run of this segment writes only the slot's first 8 bytes (c->fn and c->nargs) *)
Lemma da_keep_slot : forall E rs (H : word -> bool) (m m' : word -> option byte) c,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> c <= a < c + 8) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' c Hfr Hw a Ha Hn. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. exact (Hn (Hw a Hin)).
Qed.
(* the caller's saved registers stay in the frame while the segment's runs keep the stack *)
Lemma da_frame_kept : forall (W : world SEGS) m m' sp0 regs,
(forall a, sp0 - 64 <= a < sp0 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
da_frame_at (mrestrict (w_H W) m) sp0 regs -> da_frame_at (mrestrict (w_H W) m') sp0 regs.
Proof.
intros W m m' sp0 regs HK Hfr j r Hj.
assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length da_saved] in Hj7.
apply (val_mem_view SEGS (w_H W) m'). intros kk Hkk.
rewrite HK by lia.
exact (aval_mem_view SEGS (w_H W) m _ 8%nat _ (Hfr j r Hj) kk Hkk).
Qed.
(* a byte outside the slot's two words is in no window of this segment's states *)
Ltac da_winJ U8 :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros a (r & Hin & Ha);
lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
[ lia | rewrite U8 in Ha; lia ].

(* --- the segment from the join to the call of xstrdup ------------------------------------------------------ *)
Lemma da_segB : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate)
  (O : list (Z * Z)),
afn_pre SEGS B DESCRIPTORS_ADD_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX -> blocks_bytes S + LIVE_DESCRIPTORS_ADD uri <= LIVE_MAX ->
mo_ok MT S (XM_DESCRIPTORS_ADD MT R uri) ->
da_join_K B MT ly S W regs mem md R uri O pu.
Proof.
intros ly S W regs mem md ch pu uri R O HPRE HROD H10 Hpu HO HEV HLIVE0 HMOK.
intros lyc Sc Wc regsc memc mdc k bl0 rd0 Rb Qb c HJ Hk HRG Hfr HA0 Hbl0 Hc HNC1 HSP0 HK HKB Hmodel
  HOb1 HOb2 HOb3 HML HBB0 HSTR.
destruct HSTR as (x0 & -> & HBLK & HSTRx & HNL).
pose proof (S2 da_heap_pos lyc Sc Wc memc mdc pu _ (proj1 HJ) HBLK) as Hpu4096.
assert (HLIVE : blocks_bytes Sc + LIVE_XSTRDUP x0 <= LIVE_MAX) by (unfold LIVE_DESCRIPTORS_ADD in HLIVE0; cbn [sarg] in HLIVE0; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : DESCRIPTORS_ADD_STK = 16560) by reflexivity.
pose proof (proj1 HJ) as HARc.
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R19 & R20 & R22).
pose proof HA0 as (Hg8 & Hs8 & Hap & HC0 & HAN0 & HRP0 & HSC0 & HOWN0).
pose proof HC0 as (Hlen16 & HlenQ & Vnc0 & HCA0 & HSP0' & HSPL0).
pose proof HSC0 as (Vrf & Vcd & Vnr & Vst & Vho & Rrf & Rcd & Rnr & Rst & Rho).
assert (Hcok : da_slot_ok c) by (rewrite Hc; apply da_slot_okP; lia).
destruct (da_slot_bounds c Hcok) as (Hcb & Hc8 & Hcs).
assert (Hsp : bv_unsigned (getr regsc 2) = spZ regs - 64) by (rewrite R2; apply unsigned_lit_small; lia).
destruct (da_join lyc Sc Wc memc mdc regsc regs (spZ regs) c HARc Hsp Hal16 ltac:(lia) Hfr R8 Hcok R19 R20) as [HS SHOK].
set (E := da_EJ regsc regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold da_EJ; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. subst E. unfold da_EJ. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (da_extraJ regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold da_EJ. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
assert (U8 : bv_unsigned (ew E 8) = c)
  by (rewrite (EL 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (U19 : bv_unsigned (ew E 19) = A_G_REC)
  by (rewrite (EL 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U20 : bv_unsigned (ew E 20) = DA_SB)
  by (rewrite (EL 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold DA_SB; lia).
assert (R22' : forall (r : bv 5), 22 <= bv_unsigned r <= 27 -> getr regsc r = getr regs r).
{ intros r Hr. pose proof (R22 (bv_unsigned r) Hr) as Hx. rewrite Z_to_bv_bv_unsigned in Hx. exact Hx. }
(* 0x8ceac .. 0x8ced8: the two instrumented checks on c and c + 4, c->fn := 22, c->nargs := 0 *)
paj_run_tok RUN HS HJ SHOK da_Bspan.
{ unfold ss_daJ, da_rsJ, da_frameM, da_slotJ. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat); [reflexivity | exact U8 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_slot B TL HB VOBJS cmd_prog_img cmd_prog_writable _ _ _ _ _ _ _ _ c); [exact Hcok | unfold CALL_SIZE; lia]. }
da_fold_md. rename HFr into HFr1. rename HG into HG1. clear HF.
(* 0x8cedc: bnez s1 on the string the caller passed *)
psrr_branch_tok RUN BR HS SHOK da_Bspan.
- (* s1 <> 0: xstrdup copies the uri the caller passed *)
  (* the string's address is in s1 (pu, a heap address >= 4096): the branch is taken *)
  paj_run_to_tok RUNTO HS HJ SHOK da_Bspan DA_CALL_XS.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen with (n := 8%nat); [reflexivity | exact U8 | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (S1 da_awr_slot _ _ _ _ _ _ _ _ c); [exact Hcok | unfold CALL_SIZE; lia]. }
  da_fold_md. rename HFr into HFr2. rename HG into HG2. clear HF.
  pmkst HS;
  prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (10%bv : bv 5) P10;
  prreg HS (18%bv : bv 5) P18; prreg HS (19%bv : bv 5) P19; prreg HS (20%bv : bv 5) P20;
  prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22a; prreg HS (23%bv : bv 5) P23a;
  prreg HS (24%bv : bv 5) P24a; prreg HS (25%bv : bv 5) P25a; prreg HS (26%bv : bv 5) P26a;
  prreg HS (27%bv : bv 5) P27a;
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
    assert (KPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc mm a = rdW Wc memc a) by
      (intros a Ha Hn; rewrite (da_keep_slot _ _ _ _ _ c HFr2 ltac:(da_winJ U8) a Ha Hn);
       exact (da_keep_slot _ _ _ _ _ c HFr1 ltac:(da_winJ U8) a Ha Hn));
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let rr := eval vm_compute in (nth 1 (ss_mem ssx) da_frameM) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 rr HS ltac:(vm_compute; reflexivity)) as HRs;
      cbn [ms_mem restrict mkst] in HRs end;
    assert (Hfn' : aval_mem (rdW Wc mm) c 4 22) by
      (apply (aval_mem_view SEGS); eapply (S2 da_field E _ 8%nat c _ 0 56 0 8 0 4 (SLit 22) 22);
       [exact HRs | exact U8 | repeat (first [left; reflexivity | right]) | reflexivity
       | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | lia | reflexivity]);
    assert (Hna' : aval_mem (rdW Wc mm) (c + 4) 4 0) by
      (apply (aval_mem_view SEGS); eapply (S2 da_field E _ 8%nat c _ 0 56 0 8 4 4 (SLit 0) 0);
       [exact HRs | exact U8 | repeat (first [left; reflexivity | right]) | reflexivity
       | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | lia | reflexivity]);
    assert (Hfr' : da_frame_at (mrestrict (w_H Wc) mm) (spZ regs) regs) by
      (apply (da_frame_kept Wc memc mm (spZ regs) regs);
       [intros a Ha; apply KPJ; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia | exact Hfr]);
    assert (HNC1' : (length (r_calls Rb) < 16)%nat ->
       aval_mem (rdW Wc mm) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls Rb)) + 1)) by
      (intros Hlt kk Hkk; rewrite KPJ by (unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *; lia);
       exact (HNC1 Hlt kk Hkk));
    assert (HK' : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
       ~ (c <= a < c + 8) ->
       ~ ((length (r_calls Rb) < 16)%nat /\ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
       rdW Wc mm a = rd0 a) by
      (intros a Ha N1 N3; rewrite KPJ by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia);
       exact (HK a Ha N3));
    assert (HKB' : forall q kk i, In (q, kk) bl0 -> 0 <= i < kk -> rdW Wc mm (q + i) = rd0 (q + i)) by
      (intros q kk i Hin Hi; pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq];
       destruct (S2 da_blk_not_PG lyc Sc Wc memc mdc q kk (q + i) HARc ltac:(rewrite Hbl0; exact Hin) ltac:(lia))
         as [Hnp Hr];
       destruct (S2 da_notPG_win c (q + i) Hcok Hnp) as [N1 _];
       rewrite (KPJ (q + i) Hr ltac:(lia)); exact (HKB q kk i Hin Hi));
    assert (HRG' : da_regsM regs rg c pu) by
      (unfold da_regsM;
       split; [rewrite P2, (EL 2%nat 2%bv eq_refl); exact R2|];
       split; [rewrite P3, (EL 3%nat 3%bv eq_refl); exact R3|];
       split; [rewrite P4, (EL 4%nat 4%bv eq_refl); exact R4|];
       split; [rewrite P8, (EL 8%nat 8%bv eq_refl); exact R8|];
       split; [(first [rewrite P9 | rewrite P10]; cbn [sv_denot]; rewrite ?Z.add_0_r, (EL 9%nat 9%bv eq_refl), R9, ?Z_to_bv_bv_unsigned; reflexivity)|];
       split; [rewrite P18; cbn [sv_denot]; rewrite U8; reflexivity|];
       split; [rewrite P19, (EL 19%nat 19%bv eq_refl); exact R19|];
       split; [rewrite P20, (EL 20%nat 20%bv eq_refl); exact R20|];
       split; [rewrite P21; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, U8, (EL 20%nat 20%bv eq_refl), R20;
               rewrite da_srl3_lit by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia);
               rewrite da_add_lit; reflexivity|];
       intros r Hr;
       assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
       repeat (destruct Hr' as [-> | Hr']); [| | | | | subst r];
       [ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P22a
       | replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P23a
       | replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P24a
       | replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P25a
       | replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P26a
       | replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P27a ];
       [ rewrite (EL 22%nat (22%bv : bv 5) eq_refl) | rewrite (EL 23%nat (23%bv : bv 5) eq_refl)
       | rewrite (EL 24%nat (24%bv : bv 5) eq_refl) | rewrite (EL 25%nat (25%bv : bv 5) eq_refl)
       | rewrite (EL 26%nat (26%bv : bv 5) eq_refl) | rewrite (EL 27%nat (27%bv : bv 5) eq_refl) ];
       apply R22';
       match goal with |- _ <= ?x <= _ => let v := eval vm_compute in x in change x with v end; lia);
    assert (H10' : getr rg 10 = Z_to_bv 64 pu) by (first [rewrite P9 | rewrite P10]; cbn [sv_denot]; rewrite ?Z.add_0_r, (EL 9%nat 9%bv eq_refl), R9, ?Z_to_bv_bv_unsigned; reflexivity);
    assert (HSTR' : astr_atR (rdW Wc mm) pu x0) by
      (apply (S2 da_heap_str_kept lyc Sc Wc memc mdc _ pu x0 HARc HBLK HSTRx);
       intros a Ha Hn; destruct (S2 da_notPG_win c a Hcok Hn) as [N1 _]; apply KPJ; [exact Ha | lia]);
    exact (S2 da_segC ly S W regs mem md ch R (Some x0) O lyc Sc Wc rg mm mdq k bl0 rd0 Rb Qb c pu x0
      HPRE HROD HJ Hk HRG' H10' Hfr' HA0 Hbl0 Hc HNC1' HSP0 Hfn' Hna' HK' HKB' Hmodel HOb1 HOb2 HOb3 HO
      HML HMOK HEV HLIVE eq_refl HBLK HSTR' HNL HBB0)
  end.
- (* s1 = 0 is impossible: s1 holds pu, a heap address *)
  exfalso. rewrite YI04.branch_ne_U in Hc0. apply negb_false_iff, Z.eqb_eq in Hc0.
  revert Hc0. unfold U. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
  rewrite (EL 9%nat 9%bv eq_refl), R9. rewrite !unsigned_lit_small by lia. lia.
Qed.

End e.
End f.
End d.
