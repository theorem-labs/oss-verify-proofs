(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the store block of plugin-hostd/fuzz_command's sup_broadcast walk (0x8b00c ..
   0x8b044, entered at 0x8afec after rec_calls_free or at 0x8b00c from the table arm), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v: the two inline store4 checks of c->fn and c->nargs are removed by the
   shadow entry of the slot [c, c + 8), the stores c->fn := REC_BROADCAST and c->nargs := 0 are admitted by the
   footprint of the program's statics, and arg_line's call follows (sup_broadcast_s4.v).
   Pass-4/5 re-fit: the segment ends at apost_baseF and passes the rounding-mode-0 premise
   HFRM on to sb_mid; statement pass 5 removed its astack_pres premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_canonical_c xstrdup_c hand_back_c rec_calls_free_c arg_line_c answer_c sup_broadcast_c PaNoChain sup_broadcast_s1 sup_broadcast_s2
sup_broadcast_s3 sup_broadcast_s4.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state of the store block: s1 = c (atom 9), s2 = the shadow base (atom 18), the frame's four saved words
   as the extra atoms 32..35; the slot [c, c + 8) is written, the frame only read *)
Definition sbs_slot : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition sbs_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 0x5e3750 0x5e3be0 3); (18%nat, mkAF SB_SB SB_SB 0)] [] [].
Definition ss_sbs (pc0 : Z) : sstate := mkSS pc0 sr_atoms [sbs_slot; sbt_stack] None sbs_facts.
Definition sbs_Bx : sv := SOff 18 0.
Definition sbs_SH : list shent := [mkSHE 9 0 8].
Definition sbs_Bspan : Z * Z := (SB_SB, SB_SB + 2 ^ 44 - 1).

Lemma sb_le_byte_range : forall v n k, 0 <= YO0f.le_byte v n k < 256.
Proof. intros v n k. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

(* the slot after the two stores: c->fn = REC_BROADCAST and c->nargs = 0 *)
Definition sbs_slot2 : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8
[YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 5))].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma sb_aval_of_val_mem : forall H mem a n v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.mod_small by apply sb_le_byte_range. reflexivity.
Qed.
Lemma sb_val_mem_of_aval : forall H mem a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv kk Hk. specialize (Hv kk Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat kk)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. apply (f_equal (Z_to_bv 8)) in Hv. rewrite Z_to_bv_bv_unsigned in Hv. rewrite Hv. reflexivity.
Qed.

(* a chunk of a region of the symbolic state shows its value in memory (A/AF0x.v's st_ok_chunk_val over SEGS) *)
Lemma sb_chunk_val : forall (H : word -> bool) E ss ms i r j off (n : N) e v,
st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
pose proof (st_ok_mem_ok SEGS E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok SEGS E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* the program's statics are writable (YCbq.v's prog_rw, one of the walk hypotheses) *)
Hypothesis PRW : prog_rw SEGS B.
(* fields of cmd_img_facts (CmdRecBase.v) and lemmas of CmdRecFacts.v, under their final names and forms until
   the kit has them (statement pass 3) *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

Let MID := sb_mid B MT HB LAWS MTL VOBJS SIGP cif_prog_img cif_prog_not_ro cif_relro_img cmd_ro_in_img cmd_ro_ok_of_aro
TARG_LINE TANSWER.

(* the store block's symbolic entry *)
Lemma sbs_entry : forall ly S (W : world SEGS) regsP memP md pc0 (ra s0 s1 s2 c : Z),
AR SEGS B ly S W memP md ->
0 <= ra < 2 ^ 64 -> 0 <= s0 < 2 ^ 64 -> 0 <= s1 < 2 ^ 64 -> 0 <= s2 < 2 ^ 64 ->
2 ^ 46 <= spZ regsP <= 2 ^ 47 - 32 -> spZ regsP mod 16 = 0 ->
getr regsP 9 = w64 c -> sb_slot c -> getr regsP 18 = Z_to_bv 64 SB_SB ->
aval_mem (rdW W memP) (spZ regsP + 24) 8 ra -> aval_mem (rdW W memP) (spZ regsP + 16) 8 s0 ->
aval_mem (rdW W memP) (spZ regsP + 8) 8 s1 -> aval_mem (rdW W memP) (spZ regsP) 8 s2 ->
st_ok_pi SEGS VAL (Eimg (Ereg regsP (sbt_extra ra s0 s1 s2))) (ss_sbs pc0)
(restrict (w_H W) (mkst regsP (Z_to_bv 64 (BASE + pc0)) memP (seg_rom SEGS))) /\
sh_ok SEGS sbs_Bx sbs_SH (Eimg (Ereg regsP (sbt_extra ra s0 s1 s2))) (mrestrict (w_H W) memP).
Proof.
intros ly S W regsP memP md pc0 ra s0 s1 s2 c HAR Hra Hs0 Hs1 Hs2 Hsp Hsp16 H9 Hsl H18 Vra Vs0 Vs1 Vs2.
pose proof (sb_slot_range c Hsl) as Hcr.
set (E := Eimg (Ereg regsP (sbt_extra ra s0 s1 s2))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsP r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp : bv_unsigned (ew E 2) = spZ regsP) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U9 : bv_unsigned (ew E 9) = c) by (rewrite (EE 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SB_SB) by (rewrite (EE 18%nat 18%bv eq_refl), H18; apply unsigned_lit_small; unfold SB_SB; lia).
assert (E32 : ew E 32 = Z_to_bv 64 ra) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsP _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 s0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsP _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsP _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsP _ 3)).
pose proof (bv_unsigned_in_range 64 (getr regsP 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
split.
- rewrite restrict_mkst_fx. unfold ss_sbs. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, sbs_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply PRW. apply (HPROG B HB). apply (sb_slot_pg c); [exact Hsl | lia].
    * unfold region_ok, sbt_stack. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (chunk_ok_val SEGS E _ (spZ regsP) 0 8 (SOff 35 0) s2); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (sb_val_mem_of_aval _ _ _ _ _ Vs2)]
      | apply (chunk_ok_val SEGS E _ (spZ regsP) 8 8 (SOff 34 0) s1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (sb_val_mem_of_aval _ _ _ _ _ Vs1)]
      | apply (chunk_ok_val SEGS E _ (spZ regsP) 16 8 (SOff 33 0) s0); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (sb_val_mem_of_aval _ _ _ _ _ Vs0)]
      | apply (chunk_ok_val SEGS E _ (spZ regsP) 24 8 (SOff 32 0) ra); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact (sb_val_mem_of_aval _ _ _ _ _ Vra)] ].
  + apply pairwise_disjoint_of_extents. unfold sbs_slot, sbt_stack, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof asan_consts as (C1 & _). repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [sbs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U18. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    destruct Hsl as [(i & Hi & ->) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_REC_SPILL, SB_SB in *;
    repeat match goal with |- _ /\ _ => split end; try lia; Z.div_mod_to_equations; lia.
- unfold sh_ok, sbs_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memP E sbs_Bx 9 c 8 c 0 8).
  + destruct Hsl as [(i & Hi & Ec) | Ec].
    * apply (cmd_addressable_in SEGS B LAWS HB ly S W memP md (0xada00, 0x5e3b00 - 0xada00) c 8 HAR);
      [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
      | cbn [fst snd]; lia | cbn [fst snd]; subst c; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *; lia].
    * apply (cmd_addressable_in SEGS B LAWS HB ly S W memP md (0x5e3be0, 0x5e3c18 - 0x5e3be0) c 8 HAR);
      [unfold Tfib_zero_shadow; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | reflexivity
      | cbn [fst snd]; subst c; unfold A_REC_SPILL; lia | cbn [fst snd]; subst c; unfold A_REC_SPILL; lia].
  + unfold U, sbs_Bx. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U18.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* the store block, from 0x8afec (after rec_calls_free) or 0x8b00c (table arm), to arg_line's call and on *)
Lemma sb_store : forall ly S W regs mem md ch pl line R O lyP SP (WP : world SEGS) regsP memP mdP pc0 c F Omid,
pc0 = SB_RET_RCF \/ pc0 = SB_STORE ->
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyP SP WP memP mdP (rec_spill_frees R) ->
spZ regsP = spZ regs - 32 ->
getr regsP 8 = w64 pl -> getr regsP 9 = w64 c -> getr regsP 18 = Z_to_bv 64 SB_SB ->
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsP (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aval_mem (rdW WP memP) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW WP memP) (spZ regs - 16) 8 (s0Z regs) ->
aval_mem (rdW WP memP) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
aval_mem (rdW WP memP) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
arodata_okP SEGS RLO RHI B (rdW WP memP) ->
sb_slot c ->
(forall bl' (rd' : reader) p k s,
 (forall a, inFP cmd_PG a -> ~ (c <= a < c + 16) -> rd' a = rdW WP memP a) ->
 (forall pn, In pn Omid -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rdW WP memP (fst pn + j)) ->
 (forall pn, In pn Omid -> In pn bl') ->
 aval_mem rd' (c + CALL_OFF_FN) 4 REC_BROADCAST ->
 aval_mem rd' (c + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (c + CALL_OFF_ARGS) 8 p ->
 In (p, k) bl' -> 4096 <= p -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
 astr_atR rd' p s -> (forall pn, In pn Omid -> iv_apart p k (fst pn) (snd pn)) ->
 iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
 rec_repL bl' rd' (rec_record R REC_BROADCAST [s]) (Omid ++ [(p, k)])) ->
((exists kk, nth_error (r_calls (rec_record R REC_BROADCAST [canon line])) kk = Some (REC_BROADCAST, [canon line]) /\
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat kk) \/
 (c = A_REC_SPILL /\ (REC_BROADCAST, [canon line]) = r_spill (rec_record R REC_BROADCAST [canon line]))) ->
astr_atR (rdW WP memP) pl line -> Z.of_nat (length line) + 1 <= LMAX + 1 ->
in_blockA (ablocks B lyP SP) pl (Z.of_nat (length line) + 1) ->
Permutation (ablocks B ly S) (ablocks B lyP SP ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn Omid -> In pn O) -> (forall pn, In pn O -> In pn Omid \/ In pn F) ->
(forall pn, In pn Omid -> In pn (ablocks B lyP SP)) ->
mo_le MT S SP (rec_spill_frees R * mo_free MT) ->
SRr SEGS WP (cfg_at SEGS (BASE + pc0) regsP memP mdP)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O)).
Proof.
intros ly S W regs mem md ch pl line R O lyP SP WP regsP memP mdP pc0 c F Omid
Hpc0 HPRE HFRM Hfr8 HREC Hev Hlive HMOK HJ Hsp H8 H9 H18 Hcs Vra Vs0 Vs1 Vs2 HROD Hsl HRECs HCE
HSTR HLEN HBLK HP0 HF0 HOm1 HOm2 HOmX HMLE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARP & _).
pose proof (sb_slot_range c Hsl) as Hcr.
destruct (sbs_entry lyP SP WP regsP memP mdP pc0 (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18)) c
  HARP) as [HS SHOK];
[apply bv_unsigned_in_range | apply bv_unsigned_in_range | apply bv_unsigned_in_range | apply bv_unsigned_in_range
| rewrite Hsp; lia | rewrite Hsp, Zminus_mod, Hal16; reflexivity | exact H9 | exact Hsl | exact H18
| rewrite Hsp; replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia; exact Vra
| rewrite Hsp; replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia; exact Vs0
| rewrite Hsp; replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia; exact Vs1
| rewrite Hsp; exact Vs2 |].
remember (sbt_extra (raZ regs) (s0Z regs) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))) as X eqn:HX.
remember (Eimg (Ereg regsP X)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsP X) E) by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsP r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (U9 : bv_unsigned (ew E 9) = c) by (rewrite (EE 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
clear HE.
unfold cfg_at. change (w64 (BASE + pc0)) with (Z_to_bv 64 (BASE + pc0)).
unfold ss_sbs in HS. unfold cfg_at in *.
assert (SAME : forall (pc1 : Z), st_ok_pi SEGS VAL E (mkSS pc1 sr_atoms [sbs_slot; sbt_stack] None sbs_facts)
 (restrict (w_H WP) (mkst regsP (Z_to_bv 64 (BASE + pc1)) memP (seg_rom SEGS))) ->
 SRr SEGS WP (mkCfg (mkst regsP (Z_to_bv 64 (BASE + pc1)) memP (seg_rom SEGS)) mdP)
 (apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R) (sb_post B MT ly S R line O)) ->
 True) by (intros; exact I).
clear SAME.
destruct Hpc0 as [-> | ->]; unfold SB_RET_RCF, SB_STORE, AF_sup_broadcast in HS |- *;
(paj_run_tok RUN HS HJ SHOK sbs_Bspan;
 [ cbn [ss_mem]; eapply (awr_ok_cons_gen B E sbs_slot [sbt_stack] _ _ _ _ _ _ _ _ 9%nat c); [reflexivity | exact U9 | | awr_ok_tac];
   intros a Ha; cbn [YP09.r_wlo YP09.r_whi sbs_slot] in Ha; unfold awr_byte, awr_prog_or_caller; do 4 right; left;
   split; [apply (sb_slot_fp c a O Hsl); lia|];
   split; [apply (HPROG B HB); apply (sb_slot_pg c a Hsl); lia | apply cif_prog_img; apply (sb_slot_pg c a Hsl); lia]
 | idtac ]);
(pmkst HS;
 lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end;
 (* the block writes only the slot's first eight bytes *)
 assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW WP (ms_mem ms) a = rdW WP memP a) by
 (intros a Ha Hna; apply (kept_of_frame (segs:=SEGS) E _ (w_H WP) memP (ms_mem ms) (fun a => c <= a < c + 8) HFr);
  [ intros b wlo whi a' Hin Hr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9, ?Usp in Hr; lia|]);
    destruct Hin
  | exact Ha | exact Hna ]);
 lazymatch type of HS with st_ok _ ?Ew _ _ =>
 assert (U9w : bv_unsigned (ew Ew 9) = c) by (cbn [ew ewset Nat.eqb]; exact U9);
 assert (VFN : aval_mem (rdW WP (ms_mem ms)) (c + CALL_OFF_FN) 4 REC_BROADCAST) by
 (apply sb_aval_of_val_mem;
  replace (c + CALL_OFF_FN) with (base_val Ew (YP09.r_base sbs_slot2) + 0)
    by (cbn [YP09.r_base base_val sbs_slot2]; rewrite U9w; unfold CALL_OFF_FN; lia);
  eapply (sb_chunk_val (w_H WP) Ew _ ms 0%nat sbs_slot2 1%nat 0 4 (SLit 5) 5);
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia | cbn; lia ]);
 assert (VNA : aval_mem (rdW WP (ms_mem ms)) (c + CALL_OFF_NARGS) 4 0) by
 (apply sb_aval_of_val_mem;
  replace (c + CALL_OFF_NARGS) with (base_val Ew (YP09.r_base sbs_slot2) + 4)
    by (cbn [YP09.r_base base_val sbs_slot2]; rewrite U9w; unfold CALL_OFF_NARGS; lia);
  eapply (sb_chunk_val (w_H WP) Ew _ ms 0%nat sbs_slot2 0%nat 4 4 (SLit 0) 0);
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | cbn; lia | cbn; lia ]) end;
 prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2; prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9;
 prreg HS (10%bv : bv 5) P10; prreg HS (11%bv : bv 5) P11; prreg HS (18%bv : bv 5) P18;
 prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
 prreg HS (19%bv : bv 5) P19; prreg HS (20%bv : bv 5) P20; prreg HS (21%bv : bv 5) P21; prreg HS (22%bv : bv 5) P22;
 prreg HS (23%bv : bv 5) P23; prreg HS (24%bv : bv 5) P24; prreg HS (25%bv : bv 5) P25; prreg HS (26%bv : bv 5) P26;
 prreg HS (27%bv : bv 5) P27;
 clear HF HFr HG;
 apply (MID ly S W regs mem md ch pl line R O lyP SP WP (ms_regs ms) (ms_mem ms) mdv c F Omid);
 [ exact HPRE | exact HFRM | exact Hfr8 | exact HREC | exact Hev | exact Hlive | exact HMOK | exact HJ
 | unfold spZ at 1; rewrite P2, (EE 2%nat 2%bv eq_refl); exact Hsp
 | rewrite P1; unfold SB_RET_AL, AF_sup_broadcast; reflexivity
 | rewrite P8, (EE 8%nat 8%bv eq_refl); exact H8
 | rewrite P9, (EE 9%nat 9%bv eq_refl); exact H9
 | rewrite P10, (EE 9%nat 9%bv eq_refl); exact H9
 | rewrite P11, (EE 8%nat 8%bv eq_refl); exact H8
 | intros r Hr Hr2 Hr8 Hr9 Hr18;
   assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
     by (unfold acallee_saved in Hr; lia);
   destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
   (etransitivity;
    [ first [exact P3 | exact P4 | exact P19 | exact P20 | exact P21 | exact P22 | exact P23 | exact P24
            | exact P25 | exact P26 | exact P27]
    | etransitivity;
      [ first [exact (EE 3%nat 3%bv eq_refl) | exact (EE 4%nat 4%bv eq_refl) | exact (EE 19%nat 19%bv eq_refl)
              | exact (EE 20%nat 20%bv eq_refl) | exact (EE 21%nat 21%bv eq_refl) | exact (EE 22%nat 22%bv eq_refl)
              | exact (EE 23%nat 23%bv eq_refl) | exact (EE 24%nat 24%bv eq_refl) | exact (EE 25%nat 25%bv eq_refl)
              | exact (EE 26%nat 26%bv eq_refl) | exact (EE 27%nat 27%bv eq_refl)]
      | exact (Hcs _ Hr Hr2 Hr8 Hr9 Hr18) ] ])
 | intros kk Hkk; rewrite KEEP by lia; exact (Vra kk Hkk)
 | intros kk Hkk; rewrite KEEP by lia; exact (Vs0 kk Hkk)
 | intros kk Hkk; rewrite KEEP by lia; exact (Vs1 kk Hkk)
 | intros kk Hkk; rewrite KEEP by lia; exact (Vs2 kk Hkk)
 | intros a H1 H2 H3; rewrite KEEP; [exact (HROD a H1 H2 H3) | |];
   [ destruct H1 as [(sg & Hsg & _ & Hr) | Hr]; [pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))); lia | unfold CMD_RLO, CMD_RHI in Hr; lia]
   | intros Hin; exact (cif_prog_not_ro a (sb_slot_pg c a Hsl ltac:(lia)) H1) ]
 | exact Hsl | exact VNA
 | intros bl' rd' p k s HK1 HK2 HK3 Hn1 Ha0 Hin Hp4 Hk1 Hk2 Hstr Hap Hap1 Hap2;
   apply (HRECs bl' rd' p k s);
   [ intros a Hpg Hna; rewrite HK1 by (first [exact Hpg | lia]); apply KEEP;
     [pose proof (pa_segs_low a (cif_prog_img a Hpg)); lia | lia]
   | intros pn Hpn j Hj; rewrite (HK2 pn Hpn j Hj); apply KEEP;
     [ pose proof (al_blocks _ _ LAWS _ _ _ _ _ (fst pn) (snd pn) HARP
         ltac:(replace (fst pn, snd pn) with pn by (destruct pn; reflexivity); exact (HOmX pn Hpn))) as (_ & Hb4 & Hbc & _);
       pose proof (req_size_pos (snd pn) ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst pn) (snd pn) HARP
         ltac:(replace (fst pn, snd pn) with pn by (destruct pn; reflexivity); exact (HOmX pn Hpn))) as (_ & _ & _ & _ & _ & _ & Hm); lia)); lia
     | intros Hc; apply (blk_img SEGS B LAWS lyP SP WP memP mdP (fst pn) (snd pn) (fst pn + j) HARP
         ltac:(replace (fst pn, snd pn) with pn by (destruct pn; reflexivity); exact (HOmX pn Hpn))
         ltac:(pose proof (req_size_pos (snd pn) ltac:(destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst pn) (snd pn) HARP
           ltac:(replace (fst pn, snd pn) with pn by (destruct pn; reflexivity); exact (HOmX pn Hpn))) as (_ & _ & _ & _ & _ & _ & Hm); lia)); lia));
       apply cif_prog_img; apply (sb_slot_pg c _ Hsl); lia ]
   | exact HK3
   | intros kk Hkk; rewrite (HK1 (c + CALL_OFF_FN + Z.of_nat kk));
     [ exact (VFN kk Hkk)
     | apply (sb_slot_pg c _ Hsl); unfold CALL_OFF_FN in *; cbn in Hkk; lia
     | unfold CALL_OFF_FN in *; cbn in Hkk; lia ]
   | exact Hn1 | exact Ha0 | exact Hin | exact Hp4 | exact Hk1 | exact Hk2 | exact Hstr | exact Hap | exact Hap1 | exact Hap2 ]
 | exact HCE
 | destruct HBLK as (pb & kb & Hinb & Hpb1 & Hpb2);
   destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HARP Hinb) as (_ & Hb4 & Hbc & _ & _ & _ & Hkb);
   pose proof (req_size_pos kb ltac:(lia)) as [_ Hrq];
   pose proof (blk_off_imgP B lyP SP WP memP mdP pb kb HARP Hinb) as Hoff; unfold off_img in Hoff;
   destruct HSTR as [HSb HSn]; split; [intros ii Hii | exact HSn];
   rewrite length_app in Hii; cbn [length] in Hii;
   rewrite KEEP by lia; exact (HSb ii ltac:(rewrite length_app; cbn [length]; lia))
 | exact HLEN | exact HBLK | exact HP0 | exact HF0 | exact HOm1 | exact HOm2 | exact HOmX | exact HMLE ]).
Qed.

End e.
End f.
End d.
