(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsRet.v, with its module names changed; 1162 of its 1245 lines of code are new or changed and 582 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string): the stretch PS_SCAN (offset 132) .. PS_DEC (offset 328).
   The scan loop, the fuzz_malloc call at 200 and its three arms. Contract: lib/A/Prog/S4_PsBase.v
   (ps_pre / ps_at_scanP / ps_seg_scanP / ps_at_decP / ps_at_ret0P / ps_postP, and their stable P := True forms); the
   stretch takes the other cuts as Section hypotheses, so it composes by `apply`.
   KIT: the kit's cut 7cdbb61b5fa0 (earlier the old-pin acceptance kit of record a working branch
   a941cee76c3f + engine a Theorem Labs lane s1b 459129c18903 + listing v4; S4 working branch
   322e57164236). Blob ids as the kit's cut 7cdbb61b5fa0 carries them: lib/A/PRH_Base.v ef7c8ca98529,
   lib/A/PRH_FnReader.v f1ae32e3b2cd, lib/A/PRH_FnAlloc.v 4d8aeba047e5, lib/Reusable/YGcfRoomLive.v edc1017de99c;
   this row's S4_PsBase.v and S4_PsSrc.v; the engine set (YCbqG 219748197d6b, YC80x 14f84f225e8f with srr_inv_laws and
   the _inv runner lemmas, YC1fPx 7814b594066f with paj_run_x_inv / paj_run_to_x_inv, YCbqGcall c1fcd07d2537);
   YSRrMemnorm.v 5ffa8525936b (srr_inv_call) and YAkMemnorm.v 96c72061b4d4; PRW_CallerJ 473f33abadbc, PRW_StepKit
   0df3991c13f4 (walk-S7B preset-tree-at-2026-10-29T13-38-38Z.tsv (sha256 d07ac858278b; internal record): pa_slot_lt_ceil_b); listing Listing_prog.v 7ed1529926bd, PAImg_prog.v
   505a51ff7d08 (the A' listing of record).
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z). An SRr post is opaque once Qed, so the end-state invariant is in
   the stretch's statement: ps_seg_scan_cntP is over a Variable P of the memory with srr_inv_laws segs P (PLAW) and,
   because the stretch crosses the fuzz_malloc call, srr_inv_call segs P (PCALL). Proved from the run: the cut's
   P mem (ps_carryP's last conjunct) is the invariant premise of every runner segment (the twins paj_run_x_inv /
   paj_run_to_x_inv at P with PLAW); a branch keeps the state, so P with it; the run's own post gives P at the next cut
   (the loop head at x', the NULL return, the decode head). At the fuzz_malloc call the keep COMES FROM THE TEXT:
   tfuzz_malloc_specX's post is m-form (fpostm, its Q is fQmn mem Q0 with mem the memory at the call), so P after the
   call is PCALL over the post's own keep conjunct, and the return site's cut sc_after_at carries P at the memory after
   the call. The top instantiates P once as ps_mn D (ps_mn_laws, ps_mn_call).
   THE CALL'S TEXT (PRH_FnAlloc 4d8aeba047e5 at the cut) is POST-IMPLICATION: no position at entry;
   its post transfers any position at the call's state S = pi_S D, by its own event list (E = [] on a NULL, [HMal
   (Q + 1 + cf_head)] on a block). The NULL arms of ps_Qres take the first transfer as it is (ps_rpos D [] S2); on a
   block the second is ps_alloc's ps_rpos_mal, carried to the bad escape's fuzz_free and to the success return. No
   grant list and no agreement premise: the transfer is keyed on the instance's own result.
   THE HULL: the call's budget [HMal (Q + 1 + cf_head)] is the text's over its all-granted events at their first event
   (S4_PsBase.ps_hull_mal, from ps_pre); the call's post use hull_used S S2 [HMal ..] is read at the all-granted list
   (S4_PsBase.ps_hull_used_mal) and is the use part of every arm's ps_rpos.
   THE CALL'S fpre (PRH_Base ef7c8ca98529) asks `raZ regs < YM05.alloc_ceiling` (the jal's return pc is the listing
   slot BASE + PS_OFF + 204, below the ceiling by PRW_StepKit.pa_slot_lt_ceil_b on a closed goal) and FRM0-ENTRY's
   frm_zero (S4_PsBase.ps_frm0, from the entry's own fpre).
   The stable ps_seg_scan_cnt is the P := True corollary. Against the preview statement it LOST the keep argument
   sc_mnk and the position argument sc_rp (the callee's text now carries both); its one other argument is sc_cnt
   (the two live counts at the entry state, which S4_PsTop derives from the text's peak premises, ps_cnts). The
   statement moved for the callee's TEXT, not for the invariant (a Theorem Labs lane 12:22Z (3)); consumer: S4_PsTop.v.
   THE RETURN SITE (sc_after; the stops below are the engine's own, from its run over the listing of record, no
   disassembly cited): at 204 `beqz a0` (taken: the run to the NULL return 1284, ps_seg_ret0, with the chosen failure
   or the refusal, ps_Qres's first two Some arms); not taken, the run stops at the `bgeu s4, a1` of 224 after `mv s2, a0`,
   the shadow check of s9 (its load reads the region's 0, sa_zshadow, so its branch folds) and `ld a1, 0(s1)` (the
   caller's word text + len); taken is refuted (the scan found a quote after p + 1, so p + 1 < text + len); not taken,
   the run to 328 PS_DEC through the constant block (15 registers and the three stack words of ps_dec_consts) and
   `mv s3, s2` (ps_seg_dec at out = w = res, r = p + 1, done = []).
   Numerals: offsets INSIDE parse_string (132, 148, 152, 172, 192, 200, 204, 224, 328, 1284) are DERIVED, measured
   on lib/A/Listing_prog.v by the engine; 25452 + offset (25584, 25780, 26736) is the listing offset PS_OFF + offset (A' slot 6363),
   checked by vm_compute; 34 / 92 (WORD: the quote and the backslash of the model, PjGrammar.scan); the constant block's
   34 32 92 101 91 47 98 8 113 102 12 110 10 114 116 and 55296 56320 -56613888 (= 18446744073652937728 mod 2 ^ 64)
   (WORD, read off the engine's state by reflexivity); 8, 24, 32, 144 (LENGTH: a word, the cursor struct, the frame
   window the block writes, parse_string's frame); 16560 / 16416 (LENGTH: STK_parse_string / STK_fuzz_malloc of
   PRH_Base.v, DERIVED: the `change` that seats them is checked by conversion); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (LENGTH: the
   shadow span and the stack bounds); atom indices (10, 24, 25, 32, ...) are DERIVED engine numbering. No ADDRESS
   literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
(* the memnorm keep's runner twins (YSRrMemnorm Requires YAkMemnorm only: no LiaTwx2 `lia ::=` reaches this file) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_HShadow S4_PsBase S4_PsSrc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit.
(* the re-hiding move's SRr' / SRrG / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- THE MODEL SIDE: PjGrammar.scan over rest_atR. The statements and the arithmetic are the released plain
   proof's (lib/Prog/parse_string_loops.v psl_rest_cons / psl_rest_end / psl_scan_q / psl_seqz / ps_scan_loop);
   those proofs are for a different engine and a different byte type, so only the statements are reused. ---- *)
Lemma sc_rest_cons : forall tb text x c, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c ->
  rest_atR tb text x = c :: rest_atR tb text (x + 1).
Proof.
  intros tb text x c Hx Hc. unfold rest_atR.
  assert (Hs : forall (l : list Z) k v, nth_error l k = Some v -> skipn k l = v :: skipn (S k) l).
  { intros l. induction l as [|h t IH]; intros k v H; destruct k; cbn in *; try discriminate.
    - injection H as ->. reflexivity.
    - apply IH. exact H. }
  rewrite (Hs tb _ c Hc).
  replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia. reflexivity.
Qed.
Lemma sc_rest_end : forall tb text x, Z.of_nat (length tb) <= x - text -> rest_atR tb text x = [].
Proof. intros tb text x Hx. unfold rest_atR. apply skipn_all2. lia. Qed.
Lemma sc_scan_q : forall r, PjGrammar.scan (34 :: r) = Some 0%nat.
Proof. reflexivity. Qed.
Lemma sc_scan_bs1 : PjGrammar.scan [92] = None.
Proof. reflexivity. Qed.

(* one turn of the loop, on the model: the cursor moves by 1, or by 2 after a backslash *)
Lemma sc_step_scan : forall tb text x c,
  text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c -> c <> 34 ->
  PjGrammar.scan (rest_atR tb text x) =
  option_map (fun Q => (Q + Z.to_nat ((if Z.eqb c 92 then x + 2 else x + 1) - x))%nat)
             (PjGrammar.scan (rest_atR tb text (if Z.eqb c 92 then x + 2 else x + 1))).
Proof.
  intros tb text x c Hx Hc H34. rewrite (sc_rest_cons tb text x c Hx Hc).
  destruct (Z.eqb_spec c 92) as [E92|E92].
  - subst c. destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He.
    + rewrite (sc_rest_cons tb text (x + 1) e ltac:(lia) He), PjGrammar.scan_bs.
      replace (x + 1 + 1) with (x + 2) by lia.
      destruct (PjGrammar.scan (rest_atR tb text (x + 2))) as [Q|]; cbn [option_map]; [|reflexivity].
      f_equal. lia.
    + apply nth_error_None in He.
      rewrite (sc_rest_end tb text (x + 1)) by lia. rewrite (sc_rest_end tb text (x + 2)) by lia.
      rewrite sc_scan_bs1. reflexivity.
  - rewrite (PjGrammar.scan_ndq c _ H34 E92).
    destruct (PjGrammar.scan (rest_atR tb text (x + 1))) as [Q|]; cbn [option_map]; [|reflexivity].
    f_equal. lia.
Qed.

(* the machine's next cursor is exactly the model's: a0 + (c =? 92) + 1 *)
Lemma sc_seqz : forall c, 0 <= c < 256 ->
  zalu_raw 63 64 ALU_SLTU (zcanon (c + -92)) (zcanon 1) = if c =? 92 then 1 else 0.
Proof.
  intros c Hc. cbn [zalu_raw]. unfold zcanon, M64.
  change (1 mod 2 ^ 64) with 1.
  destruct (Z.eqb_spec c 92) as [E|E].
  - rewrite E. change ((92 + -92) mod 2 ^ 64) with 0. reflexivity.
  - replace ((c + -92) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* ---- THE SYMBOLIC STATE AT THE LOOP HEAD (offset 132). Atoms: 10 = a0 = x the cursor, 12 = a2 = 34, 24 = s8 =
   the shadow base, 32 = the byte at x (one `extra` word of the environment). The one region is the single text
   byte the turn reads; it is READ-ONLY (wlo = whi = 0), so the write premise of the runner is awr_ok_nil. ---- *)
Definition SC_Bx : sv := SOff 24 0.
Definition SC_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition sc_regions : smem := [ YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))] ].
Definition sc_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sc : sstate := mkSS (PS_OFF + PS_SCAN) sr_atoms sc_regions None sc_facts.

Section sc. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* the image instances of record, as the contract binds them (S4_PsBase.v:97-99) *)
#[local] Instance SC_PrhImg : PrhImg := prh_img_A.
#[local] Instance SC_PAListing : PAListing A_prog_listing := PL_prog_A.
#[local] Instance SC_PAImg : PAImg A_prog_listing := PI_prog_A.
#[local] Notation segs := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine's laws, at the second instance's head length, exactly as the contract states them *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : @PALib _ A_prog_listing SC_PAImg B.
Hypothesis PST_ok : forall a, Exists (in_zr a) (prh_pst ) -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* the callee's kit text, as the contract's Section hypothesis *)
Hypothesis HMALLOC : tfuzz_malloc_specX B ARx SK.
Variable CTX : list (list Z).
Variable CW : list (list Z).
(* the other cuts of the walk in their stable form: the stable statement ps_seg_scan_cnt (the P := True corollary at the
   end of the file) takes them, so it composes by `apply` as before *)
Hypothesis HRET0 : ps_seg_ret0 B ARx SK CTX CW.
Hypothesis HDEC : ps_seg_dec B ARx SK CTX CW.
(* S4_PsSrc.v's two image facts (the text across the call, ps_src_after_call), owner: the slice's assembly *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.

Definition SC_E (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).

Lemma sc_ew_reg : forall regs c n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (SC_E regs c) n = getr regs r.
Proof.
  intros regs c n r Hn H32. unfold SC_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hn).
Qed.
Lemma sc_ew_byte : forall regs c, ew (SC_E regs c) 32 = Z_to_bv 64 c.
Proof.
  intros regs c. unfold SC_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace 32%nat with (32 + 0)%nat by lia. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ==== THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z): the stretch over an invariant P of the memory with its runner
   laws, and, since the stretch crosses the fuzz_malloc call, srr_inv_call segs P (YSRrMemnorm 5ffa8525936b). The
   other cuts are taken in their P form. ==== *)
Section scP.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.
Hypothesis HRET0P : ps_seg_ret0P B ARx SK P CTX CW.
Hypothesis HDECP : ps_seg_decP B ARx SK P CTX CW.

(* the entry state of one turn: the symbolic state at offset 132 and the (empty) shadow-entry list *)
Lemma sc_entry : forall D ly S Hp W regs mem md x c,
  ps_at_scanP B ARx SK P D ly S Hp W regs mem md x ->
  nth_error (pi_tb D) (Z.to_nat (x - pi_text D)) = Some c ->
  st_ok_pi segs VAL (SC_E regs c) ss_sc
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PS_OFF + PS_SCAN))) mem (seg_rom segs)))
  /\ sh_ok segs SC_Bx [] (SC_E regs c) (mrestrict (w_H W) mem).
Proof.
intros D ly S Hp W regs mem md x c HAT Hc.
pose proof HAT as (HC & HSH & _ & _ & _ & _ & _ & _ & HPJ & _ & _ & R10 & _ & R12 & _ & _ & _ & Hx & _).
pose proof HC as (_ & _ & _ & HSRC & _).
pose proof HSH as (R24 & _ & _).
pose proof HSRC as (HBY & Htext0 & Hceil & Hamr & _ & _).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the byte at x: its value and its range, from the text's garr8 *)
assert (Hj : (Z.to_nat (x - pi_text D) < length (pi_tb D))%nat)
  by (apply nth_error_Some; rewrite Hc; discriminate).
assert (Hnth : nth (Z.to_nat (x - pi_text D)) (pi_tb D) 0 = c)
  by (rewrite (nth_error_nth _ _ 0 Hc); reflexivity).
destruct (HBY (Z.to_nat (x - pi_text D)) Hj) as [HV HR]. rewrite Hnth in HV, HR.
replace (pi_text D + Z.of_nat (Z.to_nat (x - pi_text D))) with x in HV by lia.
(* the cursor's range: above 4096 by src_rd, below the shadow span's reach by the allocator ceiling *)
assert (Hxlo : 4096 <= x) by lia.
assert (Hxhi : x <= 2 ^ 47 - 1) by lia.
rewrite restrict_mkst_fx.
set (E := SC_E regs c) in *.
assert (E10 : ew E 10 = w64 x) by (subst E; rewrite (sc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)); exact R10).
assert (E12 : ew E 12 = w64 34) by (subst E; rewrite (sc_ew_reg regs c 12 12%bv eq_refl ltac:(lia)); exact R12).
assert (E24 : ew E 24 = w64 SHADOW_OFF) by (subst E; rewrite (sc_ew_reg regs c 24 24%bv eq_refl ltac:(lia)); exact R24).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; apply sc_ew_byte).
assert (U10 : bv_unsigned (ew E 10) = x) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- unfold ss_sc. apply pa_entry_st_ok_full.
  + subst E. unfold SC_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sc_regions. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ x 0 1 (SOff 32 0) c).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * cbn. lia.
    * rewrite Z.add_0_r. exact HV.
  + exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [sc_facts f_atoms atoms_ok].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    * rewrite U10. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * rewrite U32. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * rewrite U24. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* the two atom values the engine's obligations speak of: the shadow base and the cursor *)
Lemma sc_U_Bx : forall D regs c, ps_sh_regs D regs -> U (SC_E regs c) SC_Bx = SHADOW_OFF.
Proof.
intros D regs c (R24 & _ & _). unfold SC_Bx. apply (U_atom _ 24 SHADOW_OFF).
- rewrite (sc_ew_reg regs c 24 24%bv eq_refl ltac:(lia)). exact R24.
- unfold SHADOW_OFF. lia.
Qed.
Lemma sc_U_x : forall regs c x, getr regs 10 = w64 x -> 0 <= x < 2 ^ 64 ->
  U (SC_E regs c) (SOff 10 0) = x.
Proof.
intros regs c x R10 Hx. apply (U_atom _ 10 x); [|exact Hx].
rewrite (sc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)). exact R10.
Qed.

(* the obligation one turn raises, over any env that holds the shadow base in s8 and the cursor in a0 *)
Lemma sc_obl_ok : forall E (W : world segs) mem x,
  ew E 24 = w64 SHADOW_OFF -> ew E 10 = w64 x -> 0 <= x < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x 1 ->
  range_addressable (rd_of segs (mrestrict (w_H W) mem)) (U E SC_Bx) (U E (SOff 10 0)) 1.
Proof.
intros E W mem x E24 E10 Hx HRA. unfold SC_Bx.
rewrite (U_atom E 24 SHADOW_OFF E24 ltac:(unfold SHADOW_OFF; lia)).
rewrite (U_atom E 10 x E10 Hx). exact HRA.
Qed.

(* the next cursor the turn computes: a0 + (c =? 92) + 1, exactly the model's step *)
Lemma sc_next_cursor : forall E c x,
  ew E 32 = Z_to_bv 64 c -> ew E 10 = w64 x -> 0 <= c < 256 -> 0 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 32 (-92)) (SLit 1)) (SOff 10 0)) (SLit 1))
  = w64 (if Z.eqb c 92 then x + 2 else x + 1).
Proof.
intros E c x E32 E10 Hc Hx. unfold w64 in E10. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !U_SAlu, !U_SLit, (U_SOff E 10), (U_SOff E 32), E32, E10.
rewrite (unsigned_lit_small c) by lia. rewrite (unsigned_lit_small x) by lia.
rewrite (sc_seqz c Hc).
rewrite (zcanon_id (if Z.eqb c 92 then 1 else 0)) by (destruct (Z.eqb c 92); unfold M64; lia).
rewrite (zcanon_id (x + 0)) by (unfold M64; lia).
cbn [zalu_raw].
rewrite (zcanon_id ((if Z.eqb c 92 then 1 else 0) + (x + 0))) by (destruct (Z.eqb c 92); unfold M64; lia).
rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite zcanon_id by (destruct (Z.eqb c 92); unfold M64; lia).
destruct (Z.eqb c 92); lia.
Qed.

(* a refused scan makes no allocator event, so the walk's charge is 0 *)
Lemma sc_held_none : forall x, PjGrammar.scan x = None ->
  PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace x) = 0.
Proof.
intros x H. unfold PRH_Charge.prh_held, PRH_Charge.prhPs_gtrace, PjGrammar.jr_string.
rewrite H. cbn. lia.
Qed.

(* a run that writes nothing leaves the memory alone *)
Lemma sc_frame_id : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> m' = m.
Proof.
intros E rs m m' HF Hro. apply functional_extensionality. intros y. apply HF.
intros (r & Hin & Ha). pose proof (Hro r Hin). lia.
Qed.
(* the environment the two shadow-check atoms extend: every atom of the entry env is kept *)
Lemma sc_ew_ext2 : forall regs c w0 w1 n, (n < 512)%nat ->
  ew (ewset (ewset (SC_E regs c) 512 w0) 513 w1) n = ew (SC_E regs c) n.
Proof. intros regs c w0 w1 n Hn. rewrite !ew_ewset_other by lia. reflexivity. Qed.
(* a register the turn leaves alone still holds its entry value *)
Lemma sc_reg_kept : forall (H : word -> bool) ss ms regs c w0 w1 (r : bv 5) n,
  st_ok_pi segs VAL (ewset (ewset (SC_E regs c) 512 w0) 513 w1) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros H ss ms regs c w0 w1 r n HS Hr Hn H32.
rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r, sc_ew_ext2 by lia.
rewrite (sc_ew_reg regs c n r Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hb; unfold bv_modulus in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* the kept relation does not look at the materialised vm pages *)
Lemma sc_kept_wvb : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 X,
  cj_kept SK segs B (prh_pst ) STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ->
  cj_kept SK segs B (prh_pst ) STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2
    (with_vm_backing (m_vm_lazy md2) X md2).
Proof.
intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 X (H1 & H2 & H3 & H4 & REST).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [|exact REST].
eapply aos_step_same_io; [exact H4|]. apply same_io_materialized, same_but_materialized_wvb_any.
Qed.
(* a register the turn leaves alone, read off the symbolic state *)
Ltac sc_kr HS := eapply (sc_reg_kept _ _ _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | reflexivity | lia].
(* the same at a call: the runner hands the state at the callee's entry as st_ok of the setpc'd state *)
Lemma sc_reg_kept_ok : forall (H : word -> bool) ss ms regs c w0 w1 (r : bv 5) n,
  st_ok segs (ewset (ewset (SC_E regs c) 512 w0) 513 w1) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  getr (ms_regs ms) r = getr regs r.
Proof.
intros H ss ms regs c w0 w1 r n HS Hr Hn H32.
rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r, sc_ew_ext2 by lia.
rewrite (sc_ew_reg regs c n r Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hb; unfold bv_modulus in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
Ltac sc_kr_ok HS := eapply (sc_reg_kept_ok _ _ _ _ _ _ _ _ _ HS); [vm_compute; reflexivity | reflexivity | lia].
(* the request the found path makes: a0 - s4 + 1 = x - p, i.e. Q + 1 *)
Lemma sc_q1 : forall E x p,
  ew E 10 = w64 x -> ew E 20 = w64 (p + 1) -> 0 <= p -> p + 1 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SOff 10 1) (SMd M_MUL (SOff 20 0) (SLit 18446744073709551615))) = w64 (x - p).
Proof.
intros E x p E10 E20 Hp Hx. unfold w64 in E10, E20. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd, U_SLit, (U_SOff E 10), (U_SOff E 20), E10, E20.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small (p + 1)) by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
Z.div_mod_to_equations. lia.
Qed.

(* fuzz_malloc's post body at the call of offset 200 (n := Q + 1, S := pi_S D): the Q0 under fpostm's fQmn, copied
   verbatim from tfuzz_malloc_specX (lib/A/PRH_FnAlloc.v; its comments left out). The third conjunct is the call's hull
   use (at most its one event HMal (n + cf_head)); the fifth is the batch's OUTCOME clause (a granted request at a
   consumer position is not refused); the refused arm of parse_string's text reads its exclusion conjunct off it
   (S4_PsBase.ps_excl_of_malloc) *)
Definition ps_malloc_KM (D : ps_in) (Q : nat) :
  alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    exists res, getr regs' 10 = w64 res /\ room_live_cf S' /\
    PresetHullBudget.hull_used (pi_S D) S' [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] /\
    (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) -> PRH_Base.prh_run_at sm x os i [] ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S') /\
    (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
       PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)])%nat
         H0 hist' S') /\
    (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
       (i : nat) (H0 : list Z) (hist : list YG00.chunk),
       PresetRoomPos.iface_room_pos sm x os i H0 hist (pi_S D) ->
       PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ->
       PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)]) -> pi_cnt D <> pi_fail D ->
       res <> 0 /\
       exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)])%nat
         H0 hist' S') /\
    prh_alloc_post B (Z.of_nat Q + 1) (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_Lam D) (pi_peak D) (pi_cnt D)
      (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) res ly' S' Hp' W' mem'.

(* the found path (the byte at the cursor is the quote): offsets 192..200, the fuzz_malloc call and its arms. The
   stretch's pieces run at wle into S4_PsBase's hand-off form ps_finP (the post of a run that may reach the bad
   escape's fuzz_free through the decode stretch) *)
Definition sc_found_at (D : ps_in) : Prop :=
  forall regs mem md x,
    ps_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x ->
    nth_error (pi_tb D) (Z.to_nat (x - pi_text D)) = Some 34 ->
    SRr segs (pi_W D) (cfg_at segs (ps_pc PS_SCAN) regs mem md) (ps_finP B ARx SK P CW D).

(* THE LOOP. The measure is the bytes left, text + len - x; one turn reads one byte and moves the cursor on by
   one, or by two after a backslash, so the measure falls. *)
Lemma sc_loop : forall D, ps_pre B ARx CTX CW D -> sc_found_at D ->
  forall n x regs mem md, (Z.to_nat (pi_text D + pi_len D - x) <= n)%nat ->
  ps_at_scanP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x ->
  SRr segs (pi_W D) (cfg_at segs (ps_pc PS_SCAN) regs mem md) (ps_finP B ARx SK P CW D).
Proof.
intros D HPRE HFOUND n. induction n as [|n IH]; intros x regs mem md Hn HAT.
{ exfalso. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _). lia. }
pose proof HAT as (HC & HSH & HGP & _ & _ & _ & _ & HLED & HPJ & HROD & R2 & R10 & R11 & R12 & R8 & R9 & R20 & Hx & Heq).
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & HMN).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof HSRC as (HBY & Ht4096 & Htceil & Htamr & HRA & _).
pose proof asan_consts as (C1 & _).
assert (Hx47 : x < 2 ^ 47) by lia.
assert (Hj : (Z.to_nat (x - pi_text D) < length (pi_tb D))%nat) by lia.
destruct (nth_error (pi_tb D) (Z.to_nat (x - pi_text D))) as [c|] eqn:Hbyte;
  [|apply nth_error_None in Hbyte; lia].
destruct (Z.eq_dec c 34) as [E34|E34]; [subst c; exact (HFOUND regs mem md x HAT Hbyte)|].
assert (HR256 : 0 <= c < 256).
{ destruct (HBY (Z.to_nat (x - pi_text D)) Hj) as [_ HR].
  rewrite (nth_error_nth _ _ 0 Hbyte) in HR. exact HR. }
destruct (sc_entry D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x c HAT Hbyte) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (SC_E regs c)) by (unfold SC_E; apply Eimg_env).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B (prh_pst ) ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B (prh_pst ) ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at, ps_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HMN SC_Bspan.
- (* the shadow obligation of the turn's one byte: the text is addressable by src_rd *)
  cbn [ms_mem mkst]. rewrite (sc_U_Bx D regs c HSH), (sc_U_x regs c x R10 ltac:(lia)).
  eapply range_addressable_sub; [exact HRA | lia | lia].
- (* the write premise: the turn's one region is read-only *)
  unfold ss_sc, sc_regions. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- (* at the `beq a3, a2` of offset 152. The turn has written nothing, so the memory is the entry's. *)
  assert (Emem : ms_mem ms = mem).
  { eapply sc_frame_id; [exact HF|].
    intros r Hin. unfold ss_sc, sc_regions in Hin. cbn in Hin.
    destruct Hin as [<-|[]]. cbn. lia. }
  psrr_branch_tok RUN BR HS SHOK SC_Bspan.
  + (* the quote: excluded, the byte is not 34 *)
    exfalso. rewrite branch_eq_U in Hc.
    rewrite (U_atom _ 32 c), (U_atom _ 12 34) in Hc.
    * apply Z.eqb_eq in Hc. exact (E34 Hc).
    * rewrite sc_ew_ext2 by lia. rewrite (sc_ew_reg regs c 12 12%bv eq_refl ltac:(lia)). exact R12.
    * lia.
    * rewrite sc_ew_ext2 by lia. apply sc_ew_byte.
    * lia.
  + (* not the quote: the cursor moves on, to the `bltu a0, a1` of offset 172 *)
    clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HMN SC_Bspan.
    * (* no shadow load in 152..172, so no obligation is left; the write premise: still read-only *)
      intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
    * (* the next cursor x' and the `bltu a0, a1` condition *)
      pose proof (sc_next_cursor (ewset (ewset (SC_E regs c) 512 w) 513 w0) c x
        ltac:(rewrite sc_ew_ext2 by lia; apply sc_ew_byte)
        ltac:(rewrite sc_ew_ext2 by lia; rewrite (sc_ew_reg regs c 10 10%bv eq_refl ltac:(lia)); exact R10)
        HR256 ltac:(lia)) as HA0.
      assert (U11 : U (ewset (ewset (SC_E regs c) 512 w) 513 w0) (SOff 11 0) = pi_text D + pi_len D).
      { apply U_atom; [|lia]. rewrite sc_ew_ext2 by lia.
        rewrite (sc_ew_reg regs c 11 11%bv eq_refl ltac:(lia)). exact R11. }
      psrr_branch_tok RUN BR HS SHOK SC_Bspan.
      -- (* taken: x' < text + len, back to the loop head at 132 *)
         rewrite branch_ltu_U, U11 in Hc. unfold U at 1 in Hc. rewrite HA0 in Hc. unfold w64 in Hc.
         rewrite unsigned_lit_small in Hc by (destruct (Z.eqb c 92); lia).
         apply Z.ltb_lt in Hc.
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN SC_Bspan (PS_OFF + PS_SCAN).
         ++ intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
         ++ (* the loop head again, at x' *)
            assert (Emem1 : ms_mem ms1 = mem).
            { rewrite <- Emem.
              eapply eq_trans; [eapply sc_frame_id;
                [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia] |].
              eapply sc_frame_id; [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia]. }
            assert (Hx' : x + 1 <= (if Z.eqb c 92 then x + 2 else x + 1) <= x + 2)
              by (destruct (Z.eqb c 92); lia).
            pmkst HS.
            assert (EPC : BASE + 25584 = ps_pc PS_SCAN) by (unfold ps_pc; vm_compute; reflexivity).
            rewrite EPC.
            rewrite !wvb_collapse in HJ.
            apply (IH (if Z.eqb c 92 then x + 2 else x + 1) (ms_regs ms1) (ms_mem ms1)
                     (with_vm_backing (m_vm_lazy md) mat1 md)); [lia|].
            rewrite Emem1 in HJ |- *. rewrite Emem1 in HMN.
            assert (K2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv) by sc_kr HS.
            assert (K3 : getr (ms_regs ms1) 3%bv = getr regs 3%bv) by sc_kr HS.
            assert (K4 : getr (ms_regs ms1) 4%bv = getr regs 4%bv) by sc_kr HS.
            assert (K8 : getr (ms_regs ms1) 8%bv = getr regs 8%bv) by sc_kr HS.
            assert (K9 : getr (ms_regs ms1) 9%bv = getr regs 9%bv) by sc_kr HS.
            assert (K11 : getr (ms_regs ms1) 11%bv = getr regs 11%bv) by sc_kr HS.
            assert (K12 : getr (ms_regs ms1) 12%bv = getr regs 12%bv) by sc_kr HS.
            assert (K20 : getr (ms_regs ms1) 20%bv = getr regs 20%bv) by sc_kr HS.
            assert (K23 : getr (ms_regs ms1) 23%bv = getr regs 23%bv) by sc_kr HS.
            assert (K24 : getr (ms_regs ms1) 24%bv = getr regs 24%bv) by sc_kr HS.
            assert (K25 : getr (ms_regs ms1) 25%bv = getr regs 25%bv) by sc_kr HS.
            assert (K10 : getr (ms_regs ms1) 10%bv = w64 (if Z.eqb c 92 then x + 2 else x + 1)).
            { rewrite (st_ok_pi_restrict_reg _ _ _ _ (10%bv : bv 5) HS). exact HA0. }
            unfold ps_at_scanP.
            split.
            { split; [exact HJ|]. split; [apply sc_kept_wvb; exact HKEPT|].
              split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME | exact HMN]. }
            split; [unfold ps_sh_regs; rewrite K24, K23, K25; exact HSH|].
            split; [unfold ps_gptp; rewrite K3, K4; exact HGP|].
            split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            split; [exact HLED|]. split; [exact HPJ|]. split; [exact HROD|].
            split; [rewrite K2; exact R2|]. split; [exact K10|].
            split; [rewrite K11; exact R11|]. split; [rewrite K12; exact R12|].
            split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9|].
            split; [rewrite K20; exact R20|].
            split; [lia|].
            (* the scan equation one step on: the model's step is the machine's *)
            rewrite Heq, (sc_step_scan (pi_tb D) (pi_text D) x c ltac:(lia) Hbyte E34).
            destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (if Z.eqb c 92 then x + 2 else x + 1)))
              as [Q|]; cbn [option_map]; [|reflexivity].
            f_equal. destruct (Z.eqb c 92); lia.
      -- (* not taken: x' >= text + len, so the text has no closing quote: `j 1284`, the NULL return *)
         rewrite branch_ltu_U, U11 in Hc. unfold U at 1 in Hc. rewrite HA0 in Hc. unfold w64 in Hc.
         rewrite unsigned_lit_small in Hc by (destruct (Z.eqb c 92); lia).
         apply Z.ltb_ge in Hc.
         assert (Hnone : PjGrammar.scan (ps_x D) = None).
         { rewrite Heq, (sc_step_scan (pi_tb D) (pi_text D) x c ltac:(lia) Hbyte E34).
           rewrite (sc_rest_end (pi_tb D) (pi_text D)) by (destruct (Z.eqb c 92); lia). reflexivity. }
         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HMN SC_Bspan (PS_OFF + PS_RET0).
         ++ intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
         ++ assert (Emem1 : ms_mem ms1 = mem).
            { rewrite <- Emem.
              eapply eq_trans; [eapply sc_frame_id;
                [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia] |].
              eapply sc_frame_id; [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia]. }
            pmkst HS.
            assert (EPC : BASE + 26736 = ps_pc PS_RET0) by (unfold ps_pc; vm_compute; reflexivity).
            rewrite EPC.
            rewrite !wvb_collapse in HJ.
            apply ps_finP_of_postP. apply (HRET0P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (ms_regs ms1) (ms_mem ms1)
                     (with_vm_backing (m_vm_lazy md) mat1 md) HPRE).
            rewrite Emem1 in HJ |- *. rewrite Emem1 in HMN.
            assert (K2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv) by sc_kr HS.
            assert (K3 : getr (ms_regs ms1) 3%bv = getr regs 3%bv) by sc_kr HS.
            assert (K4 : getr (ms_regs ms1) 4%bv = getr regs 4%bv) by sc_kr HS.
            pose proof HPRE as (_ & _ & _ & _ & _ & _ & HROOM & _).
            unfold ps_at_ret0P.
            split.
            { exists 0, []. split; [apply ps_wb_nil|].
              split; [exact HJ|]. split; [apply sc_kept_wvb; exact HKEPT|].
              split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME | exact HMN]. }
            split; [unfold ps_gptp; rewrite K3, K4; exact HGP|].
            split; [rewrite K2; exact R2|].
            split; [exact HROOM|].
            split; [rewrite (sc_held_none _ Hnone); lia|].
            unfold ps_Qres. rewrite Hnone.
            split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HLED|].
            split; [exact HPJ|]. apply ps_rpos_nil.
Qed.

(* the found path up to the fuzz_malloc call: the state at the callee's entry (pc = fuzz_malloc, ra = the return
   site at offset 204, a0 = Q + 1), the memory and the journal of the scan state *)
Definition sc_call_at (D : ps_in) : Prop :=
  forall regs mem md Q,
    ps_carryP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) mem md 0 [] ->
    ps_sh_regs D regs -> ps_gptp D regs ->
    prh_ledger B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) mem (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) ->
    pj_in_okR segs (mrestrict (w_H (pi_W D)) mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
    arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H (pi_W D)) mem) ->
    getr regs 2 = w64 (PS_SP D) -> getr regs 1 = w64 (ps_pc 204) -> getr regs 10 = w64 (Z.of_nat Q + 1) ->
    getr regs 8 = w64 (pi_q D) -> getr regs 9 = w64 (pi_q D + 8) -> getr regs 20 = w64 (pi_p D + 1) ->
    getr regs 11 = w64 (pi_text D + pi_len D) ->
    PjGrammar.scan (ps_x D) = Some Q ->
    SRr segs (pi_W D) (cfg_at segs (pa_sigma AS_fuzz_malloc) regs mem md) (ps_finP B ARx SK P CW D).

Lemma sc_found_of_call : forall D, ps_pre B ARx CTX CW D -> sc_call_at D -> sc_found_at D.
Proof.
intros D HPRE HCALL regs mem md x HAT Hbyte.
pose proof HAT as (HC & HSH & HGP & _ & _ & _ & _ & HLED & HPJ & HROD & R2 & R10 & R11 & R12 & R8 & R9 & R20 & Hx & Heq).
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & HMN).
pose proof HPJ as (_ & _ & _ & _ & _ & Htpos & Htlen & Hple & Hlen & _).
pose proof HSRC as (HBY & Ht4096 & Htceil & Htamr & HRA & _).
pose proof asan_consts as (C1 & _).
destruct (sc_entry D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md x 34 HAT Hbyte) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (SC_E regs 34)) by (unfold SC_E; apply Eimg_env).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B (prh_pst ) ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at, ps_pc, w64. rewrite <- Z.add_assoc.
paj_run_tok_x_inv RUN HS HJ SHOK HMN SC_Bspan.
- cbn [ms_mem mkst]. rewrite (sc_U_Bx D regs 34 HSH), (sc_U_x regs 34 x R10 ltac:(lia)).
  eapply range_addressable_sub; [exact HRA | lia | lia].
- unfold ss_sc, sc_regions. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (Emem : ms_mem ms = mem).
  { eapply sc_frame_id; [exact HF|].
    intros r Hin. unfold ss_sc, sc_regions in Hin. cbn in Hin.
    destruct Hin as [<-|[]]. cbn. lia. }
  psrr_branch_tok RUN BR HS SHOK SC_Bspan.
  + (* the quote: offsets 192..200, to the jal *)
    clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HMN SC_Bspan.
    * intros a (r & Hin & Ha). cbn in Hin. destruct Hin as [<-|[]]. cbn in Ha. lia.
    * (* at fuzz_malloc's entry: ra = the return site at 204, a0 = x - p = Q + 1 *)
      assert (Emem0 : ms_mem ms0 = mem).
      { rewrite <- Emem. eapply sc_frame_id;
          [eassumption | intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; lia]. }
      pmkst HS.
      rewrite ?wvb_collapse in HJ. rewrite Emem0 in HMN.
      assert (K1 : getr (ms_regs ms0) 1%bv = w64 (ps_pc 204)).
      { rewrite (st_ok_restrict_reg segs _ _ _ _ (1%bv : bv 5) HS).
        etransitivity; [exact (codeptr_val _ 25656 HEI0)|].
        unfold w64, ps_pc. f_equal; try (vm_compute; reflexivity). }
      assert (K10 : getr (ms_regs ms0) 10%bv = w64 (x - pi_p D)).
      { rewrite (st_ok_restrict_reg segs _ _ _ _ (10%bv : bv 5) HS).
        apply sc_q1; [| | lia | lia].
        - rewrite sc_ew_ext2 by lia. rewrite (sc_ew_reg regs 34 10 10%bv eq_refl ltac:(lia)). exact R10.
        - rewrite sc_ew_ext2 by lia. rewrite (sc_ew_reg regs 34 20 20%bv eq_refl ltac:(lia)). exact R20. }
      assert (K2 : getr (ms_regs ms0) 2%bv = getr regs 2%bv) by sc_kr_ok HS.
      assert (K3 : getr (ms_regs ms0) 3%bv = getr regs 3%bv) by sc_kr_ok HS.
      assert (K4 : getr (ms_regs ms0) 4%bv = getr regs 4%bv) by sc_kr_ok HS.
      assert (K8 : getr (ms_regs ms0) 8%bv = getr regs 8%bv) by sc_kr_ok HS.
      assert (K9 : getr (ms_regs ms0) 9%bv = getr regs 9%bv) by sc_kr_ok HS.
      assert (K11 : getr (ms_regs ms0) 11%bv = getr regs 11%bv) by sc_kr_ok HS.
      assert (K20 : getr (ms_regs ms0) 20%bv = getr regs 20%bv) by sc_kr_ok HS.
      assert (K23 : getr (ms_regs ms0) 23%bv = getr regs 23%bv) by sc_kr_ok HS.
      assert (K24 : getr (ms_regs ms0) 24%bv = getr regs 24%bv) by sc_kr_ok HS.
      assert (K25 : getr (ms_regs ms0) 25%bv = getr regs 25%bv) by sc_kr_ok HS.
      apply (HCALL (ms_regs ms0) (ms_mem ms0) (with_vm_backing (m_vm_lazy md) mat0 md)
               (Z.to_nat (x - (pi_p D + 1)))); rewrite ?Emem0 in HJ |- *.
      -- split; [exact HJ|]. split; [apply sc_kept_wvb; exact HKEPT|].
         split; [exact HSAVED|]. split; [exact HSRC|]. split; [exact HHOME | exact HMN].
      -- unfold ps_sh_regs. rewrite K24, K23, K25. exact HSH.
      -- unfold ps_gptp. rewrite K3, K4. exact HGP.
      -- exact HLED.
      -- exact HPJ.
      -- exact HROD.
      -- rewrite K2. exact R2.
      -- exact K1.
      -- rewrite K10. rewrite Z2Nat.id by lia. f_equal. lia.
      -- rewrite K8. exact R8.
      -- rewrite K9. exact R9.
      -- rewrite K20. exact R20.
      -- rewrite K11. exact R11.
      -- rewrite Heq, (sc_rest_cons (pi_tb D) (pi_text D) x 34 ltac:(lia) Hbyte), sc_scan_q. reflexivity.
  + (* not the quote: excluded, the byte is 34 *)
    exfalso. revert Hc.
    rewrite (denot_lit_U _ (SOff 32 0)), (denot_lit_U _ (SOff 12 0)), (U_atom _ 32 34), (U_atom _ 12 34).
    * vm_compute. intros H. discriminate H.
    * rewrite sc_ew_ext2 by lia. rewrite (sc_ew_reg regs 34 12 12%bv eq_refl ltac:(lia)). exact R12.
    * lia.
    * rewrite sc_ew_ext2 by lia. apply sc_ew_byte.
    * lia.
Qed.

(* ---- THE fuzz_malloc CALL (offset 200). ---- *)
(* the two live counts tfuzz_malloc_specX asks (PRH_FnAlloc blob 4d8aeba047e5 :273-274), at the entry's allocator
   state: the scan writes no allocator state, so the call's state is the entry's *)
Definition sc_cnt (D : ps_in) : Prop :=
  YGcfRoomLive.sec_cnt (pi_S D) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 (pi_S D) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* the state at the return site (offset 204): what the call leaves, with P at its memory *)
Definition sc_after_at (D : ps_in) : Prop :=
  forall Q regsc memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
    ps_carryP B ARx SK P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) memc mdc 0 [] ->
    ps_sh_regs D regsc -> ps_gptp D regsc ->
    prh_ledger B (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) memc (pi_Lam D) (pi_peak D) (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) ->
    pj_in_okR segs (mrestrict (w_H (pi_W D)) memc) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
    arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H (pi_W D)) memc) ->
    getr regsc 2 = w64 (PS_SP D) -> getr regsc 8 = w64 (pi_q D) -> getr regsc 9 = w64 (pi_q D + 8) ->
    getr regsc 20 = w64 (pi_p D + 1) -> getr regsc 11 = w64 (pi_text D + pi_len D) ->
    PjGrammar.scan (ps_x D) = Some Q ->
    ajournal_x (SK := SK) segs B (prh_pst ) ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
      (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S2 Hp2 W2 mem2 md2 (0 + k1) ->
    ajournal_x (SK := SK) segs B (prh_pst ) ARx (STK_fuzz_malloc + 0) (PS_WSP D + (PS_SP D - PS_WSP D) + 0) []
      (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
    aregs_preserved regsc regs2 ->
    ps_malloc_KM D Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
    P mem2 ->
    SRr segs W2 (mkCfg (mkst regs2 (w64 (ps_pc 204)) mem2 (seg_rom segs)) md2) (ps_finP B ARx SK P CW D).

(* the call: aj_call_xW at fuzz_malloc's kit text; its live counts are the argument, the room position and the memnorm
   keep across it are the text's own (its position conjunct, fpostm's keep), and the return pc is a listing slot below
   the ceiling *)
Lemma sc_call_of_after : forall D, ps_pre B ARx CTX CW D -> sc_cnt D -> sc_after_at D -> sc_call_at D.
Proof.
intros D HPRE [HSEC H24] HAFTER regs mem md Q HC HSH HGP HLED HPJ HROD R2 R1 R10 R8 R9 R20 R11 HSCAN.
pose proof HC as (HJ & HKEPT & HSAVED & HSRC & HHOME & HMN).
pose proof HPRE as (HFPRE & HCLOS & HCH0 & _ & _ & HGAP & HROOM & HCNTS & _ & HPJ0 & Hpl & _ & HWIN & Hspq & Hqe & _ &
  _ & _ & _ & _ & HLIVE).
pose proof HFPRE as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _ & HTOP & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & _).
assert (FR : PS_FRAME = 144) by (vm_compute; reflexivity).
assert (STKs : @STK_fuzz_malloc prh_img_A + 144 <= @STK_parse_string prh_img_A) by (vm_compute; congruence).
assert (Rsp : spZ regs = PS_SP D).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold PS_SP. lia. }
(* the request bound and the room at the malloc (the cut's per-event premise at its first event, ps_live_bb) *)
destruct HLIVE as [HLQ HLEV].
pose proof (HLQ Q HSCAN) as HMAX. pose proof (ps_live_bb B D Q HSCAN HLEV) as HBB.
unfold LIVE_parse_string in HMAX.
(* fpre's return-address bound: ra is the jal's return pc, the listing slot BASE + (PS_OFF + 204) (closed goals only) *)
assert (HRAC : raZ regs < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1. unfold w64, ps_pc. rewrite <- Z.add_assoc.
  assert (Hk : 0 <= PS_OFF + 204 < 2 ^ 40) by (vm_compute; split; congruence).
  pose proof (pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_prog_A) (PI := PI_prog_A) (PS_OFF + 204) Hk
    ltac:(vm_compute; reflexivity)) as Hc.
  rewrite unsigned_lit_small; [exact Hc | vm_compute; split; congruence]. }
(* the frame chain from q at the call view: the walk wrote nothing at or above the entry sp but the caller's word
   [q, q + 8), which still holds p *)
destruct (ps_chain_call D (aview segs (w_H (pi_W D)) mem) (ps_chain0_of_pre B ARx CTX CW D HPRE) HGAP ltac:(lia))
  as [ch1 Hch1].
{ intros a Ha.
  destruct (Z_lt_dec a (pi_q D)) as [Hlo|Hlo]; [|destruct (Z_lt_dec a (pi_q D + 8)) as [Hhi|Hhi]].
  - pose proof HKEPT as (_ & _ & _ & _ & _ & K1 & _).
    apply K1; [lia | lia | intros (r & Hr & Hrq); destruct Hr as [<-|[]]; cbn in Hrq; lia].
  - assert (Hk : (Z.to_nat (a - pi_q D) < 8)%nat) by lia.
    pose proof (proj1 HPJ _ Hk) as V1. pose proof (proj1 HPJ0 _ Hk) as V2.
    replace (pi_q D + Z.of_nat (Z.to_nat (a - pi_q D))) with a in V1, V2 by lia.
    unfold aview. rewrite V1, V2. reflexivity.
  - pose proof HKEPT as (_ & _ & _ & _ & _ & K1 & _).
    apply K1; [lia | lia | intros (r & Hr & Hrq); destruct Hr as [<-|[]]; cbn in Hrq; lia]. }
unfold cfg_at.
eapply SRr_bind.
{ apply (aj_call_xW SK segs B (prh_pst ) ARx cf_head LAWS (@pa_segs_low _ _ PI_prog_A) (pi_W D) regs mem
    (pa_sigma AS_fuzz_malloc) (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D)
    (pi_mem D) (pi_md D) [] (pi_ly D) (pi_S D) (pi_Hp D) md 0 (@STK_fuzz_malloc prh_img_A) 0 [] (PS_SP D - PS_WSP D)
    (w64 (ps_pc 204)) ch1
    (* the text's m-form Q at this call: fQmn mem (ps_malloc_KM D Q), spelled out (PRH_Base fQmn, by conversion) *)
    (fun ly' S' Hp' W' regs' mem' md' => ps_malloc_KM D Q ly' S' Hp' W' regs' mem' md' /\
       (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')) HJ).
  - rewrite Rsp. lia.
  - unfold PS_SP, PS_WSP. rewrite FR. Z.div_mod_to_equations. lia.
  - unfold PS_SP, PS_WSP. rewrite FR. lia.
  - vm_compute. congruence.
  - unfold PS_SP, PS_WSP, PS_WSTK. rewrite FR.
    assert (E : spZ (pi_regs D) - 144 - (spZ (pi_regs D) + pi_e D) = -(144 + pi_e D)) by ring.
    rewrite E, Z.sub_opp_r, Z.add_assoc. apply Zplus_le_compat_r. exact STKs.
  - lia.
  - reflexivity.
  - unfold PS_SP, PS_WSP. rewrite FR. lia.
  - rewrite (proj1 HGP). exact Hgp.
  - rewrite (proj2 HGP). exact Htp.
  - exact R1.
  - unfold w64, ps_pc. rewrite <- Z.add_assoc.
    apply (ret_ok_codeptr_v (PI := PI_prog_A) (PS_OFF + 204)).
    + vm_compute. split; congruence.
    + vm_compute. reflexivity.
  - vm_compute. congruence.
  - replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) by (unfold PS_WSP; ring).
    replace (s0Z regs) with (pi_q D)
      by (unfold s0Z; rewrite R8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    exact Hch1.
  - intros HPRE1 _.
    eapply SRr_mono.
    { apply (HMALLOC (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) regs mem md ch1 (Z.of_nat Q + 1) (pi_Lam D) (pi_peak D)
        (pi_cnt D) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D)).
      - split; [exact HPRE1|]. split; [exact HROD|].
        split; [rewrite Rsp; unfold PS_SP; rewrite FR; lia|]. split; [exact HRAC|]. exact (ps_frm0 B ARx CTX CW D HPRE).
      - exact HROOM.
      - apply (prh_univ_closure_malloc B CTX HCLOS). vm_compute. discriminate.
      - exact HSEC.
      - exact H24.
      - (* the hull budget: the text's over the all-granted events, at their first event (S4_PsBase.ps_hull_mal) *)
        exact (ps_hull_mal B ARx CTX CW D Q HPRE HSCAN).
      - exact R10.
      - lia.
      - exact HMAX.
      - exact HLED.
      - (* The batch kit tfuzz_malloc_specX: the bytes bound under cnt <> fail *)
        exact (fun _ => HBB). }
    intros W' c' _ H. apply fpostW_x_of_apost. exact H.
  - intros a (r & Hin & _). destruct Hin. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & _ & HP & HKM & HKEEP).
(* P after the call: the carry's P at the call memory mem, carried by srr_inv_call over the text's keep conjunct *)
exact (HAFTER Q regs mem md ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HC HSH HGP HLED HPJ HROD R2 R8 R9 R20 R11 HSCAN
  HJ2 HJc HP HKM (PCALL mem mem2 HKEEP HMN)).
Qed.

(* ---- THE RETURN SITE (offset 204). Atoms: 10 = a0 = res, 2 = sp, 9 = s1 = q + 8, 20 = s4 = p + 1, 24 = s8 = the
   shadow base, 25 = s9 = the shadow cell of q + 8, 32 = text + len (the one `extra` word of the environment; a1 is a
   caller-saved register the call clobbers). Regions: that shadow cell (0, by the stack's zero shadow), the caller's
   word at q + 8 (text + len, by pj_in_okR), and the 32 bytes of the frame the constant block writes. ---- *)
Definition sa_regions : smem :=
  [ YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 2%nat) 0 32 0 32 [] ].
Definition sa_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_sa : sstate := mkSS (PS_OFF + 204) sr_atoms sa_regions None sa_facts.

(* the shadow cell of the caller's word is zero: q + 8 is on the real stack, and the journal keeps the stack's
   zero shadow at every state (AR_laws_x field alx_zshadow_byte) *)
Lemma sa_zshadow : forall D ly2 S2 Hp2 W2 mem2 md2,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> ly_stk_lo ly2 <= pi_q D + 8 < ly_stk_hi ly2 ->
  aview segs (w_H W2) mem2 (SHADOW_OFF + (pi_q D + 8) / 8) = Some 0.
Proof.
intros D ly2 S2 Hp2 W2 mem2 md2 HAR Hr.
exact (alx_zshadow_byte segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (pi_q D + 8) HAR Hr).
Qed.

(* a present zero shadow byte read as a one-byte value (PRW_StepKit.v val_mem_zero8, at one byte) *)
Lemma sa_val0 : forall (H : word -> bool) mem a, aview segs H mem a = Some 0 -> val_mem segs (mrestrict H mem) a 1 0.
Proof.
intros H mem a Hz j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (aview_byte segs H mem a 0 Hz) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
(* a word written as its 64-bit residue *)
Lemma sa_val_mod : forall m a v, val_mem segs m a 8 (v mod 2 ^ 64) -> val_mem segs m a 8 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* a register whose symbolic value is a register atom of the return site's environment *)
Lemma sa_reg_atom : forall (H : word -> bool) ss ms regs c (r r0 : bv 5) n,
  st_ok_pi segs VAL (SC_E regs c) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r0 -> (n < 32)%nat ->
  getr (ms_regs ms) r = getr regs r0.
Proof.
intros H ss ms regs c r r0 n HS Hr Hn H32.
rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
rewrite (denot_lit_U _ (SOff n 0)), U_SOff, Z.add_0_r.
rewrite (sc_ew_reg regs c n r0 Hn H32). unfold zcanon, M64.
rewrite Z.mod_small by (pose proof (bv_unsigned_in_range 64 (getr regs r0)) as Hb; unfold bv_modulus in Hb; lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* a register whose symbolic value is the extra atom 32 (text + len) *)
Lemma sa_reg_tl : forall (H : word -> bool) ss ms regs c (r : bv 5),
  st_ok_pi segs VAL (SC_E regs c) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff 32 0 ->
  getr (ms_regs ms) r = Z_to_bv 64 c.
Proof.
intros H ss ms regs c r HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr.
cbn [sv_denot]. rewrite sc_ew_byte, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* a register whose symbolic value is a literal *)
Lemma sa_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) z,
  st_ok_pi segs VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros H E ss ms r z HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. reflexivity. Qed.
(* the shadow hull of a range below the stack bound lies below 2 ^ 46 (FuzzStrdup.v sd_hull_low, verbatim) *)
Lemma sa_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
(* the two stack budgets as closed literals (lia reads neither definition) *)
Ltac sa_lits := repeat match goal with
  | H : context [@STK_parse_string ?I] |- _ => change (@STK_parse_string I) with 16560 in H
  | |- context [@STK_parse_string ?I] => change (@STK_parse_string I) with 16560
  | H : context [@STK_fuzz_malloc ?I] |- _ => change (@STK_fuzz_malloc I) with 16416 in H
  | |- context [@STK_fuzz_malloc ?I] => change (@STK_fuzz_malloc I) with 16416
  end.

(* a successful scan leaves a non-negative charge *)
Lemma sa_held : forall x Q, PjGrammar.scan x = Some Q -> 0 <= PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace x).
Proof.
intros x Q H. pose proof cf_head_nonneg as Hh.
destruct (PjGrammar.decode x) as [sr|] eqn:Hd.
- assert (Eg : PRH_Charge.prhPs_gtrace x = [PjGrammar.EAlloc (Datatypes.S Q)]).
  { unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. cbv beta. rewrite H, Hd. reflexivity. }
  rewrite Eg. unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia.
- assert (Eg : PRH_Charge.prhPs_gtrace x = [PjGrammar.EAlloc (Datatypes.S Q); PjGrammar.EFree (Datatypes.S Q)]).
  { unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. cbv beta. rewrite H, Hd. reflexivity. }
  rewrite Eg. unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia.
Qed.

(* the symbolic state at the return site 204, from the concrete facts after the call *)
Lemma sa_entry : forall D (W : world segs) regs mem ly S Hp md,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= pi_q D + 8 < ly_stk_hi ly ->
  getr regs 2 = w64 (PS_SP D) -> getr regs 9 = w64 (pi_q D + 8) -> getr regs 24 = w64 SHADOW_OFF ->
  getr regs 25 = w64 (SHADOW_OFF + (pi_q D + 8) / 8) ->
  val_mem segs (mrestrict (w_H W) mem) (pi_q D + 8) 8 (pi_text D + pi_len D) ->
  (forall a, PS_SP D <= a < PS_SP D + 32 -> apresent (w_H W) mem a) ->
  2 ^ 46 <= PS_SP D <= 2 ^ 47 -> PS_SP D mod 16 = 0 -> PS_SP D + 32 <= pi_q D -> pi_q D + 16 <= 2 ^ 47 ->
  0 <= pi_text D + pi_len D < 2 ^ 64 ->
  st_ok_pi segs VAL (SC_E regs (pi_text D + pi_len D)) ss_sa
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PS_OFF + 204))) mem (seg_rom segs))).
Proof.
intros D W regs mem ly S Hp md HAR Hq R2 R9 R24 R25 V9 Hpres Hsp Hsp16 Hspq Hq47 Htl.
pose proof (sa_zshadow D ly S Hp W mem md HAR Hq) as Z25.
set (tl := pi_text D + pi_len D) in *.
set (E := SC_E regs tl).
assert (Hd8 : 0 <= (pi_q D + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (U2 : bv_unsigned (ew E 2) = PS_SP D)
  by (subst E; rewrite (sc_ew_reg regs tl 2 2%bv eq_refl ltac:(lia)), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = pi_q D + 8)
  by (subst E; rewrite (sc_ew_reg regs tl 9 9%bv eq_refl ltac:(lia)), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (subst E; rewrite (sc_ew_reg regs tl 24 24%bv eq_refl ltac:(lia)), R24; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + (pi_q D + 8) / 8)
  by (subst E; rewrite (sc_ew_reg regs tl 25 25%bv eq_refl ltac:(lia)), R25; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tl) by (subst E; apply sc_ew_byte).
rewrite restrict_mkst_fx.
unfold ss_sa. apply pa_entry_st_ok_full.
- subst E. unfold SC_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sa_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U25. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply sa_val0. exact Z25.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ _ 0 8 (SOff 32 0) tl);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact V9.
  + rewrite U2. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. unfold sa_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U25, U9, U2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *.
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [sa_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U2; change (2 ^ 4) with 16; lia|].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U24; rewrite Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; lia
         | exact I].
Qed.

(* ---- WHAT A RUN FROM THE RETURN SITE KEEPS. Its one write window is the 32 frame bytes [sp, sp + 32) the constant
   block stores into; every carried fact speaks about bytes below sp (the image, the statics, the heads, the text and
   every shadow byte) or at or above sp + 40 (the saved registers, the caller's cursor struct at q). ---- *)
Lemma sa_keep : forall D ly S Hp W mem md mem' md',
  ps_pre B ARx CTX CW D -> ARx ly S Hp W mem md ->
  ly_stk_lo ly = ly_stk_lo (pi_ly D) -> ly_stk_hi ly = ly_stk_hi (pi_ly D) ->
  (forall x : word, ~ (PS_SP D <= bv_unsigned x < PS_SP D + 32) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') -> same_but_materialized md md' ->
  (cj_kept SK segs B (prh_pst ) STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
     (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md ->
   cj_kept SK segs B (prh_pst ) STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
     (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem' md') /\
  (ps_saved D W mem -> ps_saved D W mem') /\
  (src_rd W mem (pi_text D) (pi_tb D) -> src_rd W mem' (pi_text D) (pi_tb D)) /\
  (pj_in_okR segs (mrestrict (w_H W) mem) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
   pj_in_okR segs (mrestrict (w_H W) mem') (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)) /\
  (arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
   arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem')) /\
  (forall Lam pk c f r mo ow, prh_ledger B ly S Hp W mem Lam pk c f r mo ow -> prh_ledger B ly S Hp W mem' Lam pk c f r mo ow) /\
  (forall v, rd32 (aview segs (w_H W) mem) (as_errno B) v -> rd32 (aview segs (w_H W) mem') (as_errno B) v) /\
  (forall a n, 0 <= a -> a + n <= YM05.alloc_ceiling -> prhReader_vis W mem a n -> prhReader_vis W mem' a n).
Proof.
intros D ly S Hp W mem md mem' md' HPRE HAR Eslo Eshi HM HG Hsame.
pose proof HPRE as ((HPX & _ & _) & _ & _ & _ & _ & HGAP & _ & _ & _ & HIN0 & Hpl & _ & HWIN & Hq1 & Hq2 & _ & HSRC0 & _).
pose proof HPX as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & _ & Hetop & _).
pose proof HIN0 as (_ & _ & _ & _ & Hq8 & Ht0 & Ht62 & Htp & Hlen & _).
pose proof HSRC0 as (_ & H4096 & Htc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
sa_lits.
assert (Hsp : PS_SP D = spZ (pi_regs D) - 144) by (unfold PS_SP; change PS_FRAME with 144; reflexivity).
assert (HAlo : forall a, 0 <= a < PS_SP D -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
{ intros a Ha. apply aview_eq_of. apply HM. rewrite unsigned_lit_small by lia. lia. }
assert (HAhi : forall a, PS_SP D + 32 <= a < 2 ^ 64 -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
{ intros a Ha. apply aview_eq_of. apply HM. rewrite unsigned_lit_small by lia. lia. }
split.
{ intros HK. eapply (cj_kept_trans SK segs B (prh_pst ) ARx cf_head LAWS); [exact HK | | exact HAR0 | exact HAR | | | |].
  - apply (cj_kept_exec SK segs B (prh_pst ) ARx cf_head LAWS (@pa_segs_low _ _ PI_prog_A) STK_parse_string
      (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [] ly S Hp W mem md mem' md' (fun a => PS_SP D <= a < PS_SP D + 32) HAR).
    + rewrite Eslo. exact Hceil.
    + rewrite Eslo. sa_lits. lia.
    + rewrite Eshi. lia.
    + exact HM.
    + intros a Ha. left. sa_lits. lia.
    + exact Hsame.
  - sa_lits. lia.
  - lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
split.
{ unfold ps_saved. cbn zeta. intros (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  repeat split; (eapply val_mem_kept; [intros k Hk; apply HAhi; cbn in Hk; lia | eassumption]). }
split.
{ intros (Hb & H4096' & Hceil' & Hamr & Hra & Hhu).
  split; [|split; [exact H4096'|split; [exact Hceil'|split; [exact Hamr|split]]]].
  - intros j Hj. destruct (Hb j Hj) as [V R]. split; [|exact R].
    eapply val_mem_kept; [|exact V]. intros k Hk. apply HAlo. cbn in Hk. lia.
  - eapply range_addressable_agree; [|exact Hra]. intros x Hx. apply HAlo. unfold shadow_of_addr.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    unfold SHADOW_OFF. lia.
  - intros Hn s Hs. pose proof (sa_hull_low (pi_text D) _ s ltac:(lia) Hn ltac:(lia) Hs). rewrite HAlo by lia.
    exact (Hhu Hn s Hs). }
split.
{ intros (Vp & Ve & Vd & Hrw & Hq8' & Ht0' & Ht62' & Htp' & Hlen' & Hg & Hqt & Hd).
  split; [eapply val_mem_kept; [intros k Hk; apply HAhi; cbn in Hk; lia | exact Vp]|].
  split; [eapply val_mem_kept; [intros k Hk; apply HAhi; cbn in Hk; lia | exact Ve]|].
  split; [eapply val_mem_kept; [intros k Hk; apply HAhi; cbn in Hk; lia | exact Vd]|].
  split; [intros x Hx; apply (writable_at_grows segs _ _ x HG); apply Hrw; exact Hx|].
  do 5 (split; [assumption|]).
  split; [|split; assumption].
  intros j Hj. destruct (Hg j Hj) as [V R]. split; [|exact R].
  eapply val_mem_kept; [|exact V]. intros k Hk. apply HAlo. cbn in Hk. lia. }
split.
{ intros H a Hro Hno Her. rewrite (HAlo a); [exact (H a Hro Hno Her)|].
  pose proof (@pa_segs_low _ _ PI_prog_A a (psrc_ro_img a Hro)). lia. }
split.
{ intros Lam pk c f r mo ow (HGl & HND & HF & HPm).
  assert (HPS : forall a n, In (a, n) prh_pst -> forall i, 0 <= i < n ->
    aview segs (w_H W) mem' (a + i) = aview segs (w_H W) mem (a + i)).
  { intros a n Hin i Hi. apply HAlo.
    assert (Hx : Exists (in_zr (a + i)) prh_pst)
      by (apply Exists_exists; exists (a, n); split; [exact Hin|]; unfold in_zr; cbn [fst snd]; lia).
    destruct (PST_ok _ Hx) as [Hi' _]. pose proof (@pa_segs_low _ _ PI_prog_A _ Hi'). lia. }
  destruct HGl as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & Grest).
  split; [|split; [exact HND|split; [|exact HPm]]].
  - split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_live)); [cbn; tauto | lia] | exact G1]|].
    split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_peak)); [cbn; tauto | lia] | exact G2]|].
    split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_count)); [cbn; tauto | lia] | exact G3]|].
    split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_fail)); [cbn; tauto | lia] | exact G4]|].
    split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_ran_out)); [cbn; tauto | lia] | exact G5]|].
    split; [split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_most)); [cbn; tauto | lia] | exact G6]
                   | exact G6b]|].
    split; [split; [eapply val_mem_kept; [intros i Hi; apply (HPS _ (Z.of_nat pi_gz_own_ran_out)); [cbn; tauto | lia] | exact G7]
                   | exact G7b]|].
    exact Grest.
  - apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (H0 & H1 & H2 & H3 & H4).
    cbn [fst snd] in *. split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR H1) as (_ & H4096b & Hcb & _).
    pose proof (req_size_pos (k + cf_head) (Z.add_nonneg_nonneg _ _ H0 Hh0)) as [Rq _].
    eapply val_mem_kept; [|exact H4]. intros i Hi. apply HAlo. cbn in Hi. lia. }
split.
{ intros v H k Hk. destruct (pal_env B TL) as ((Herr0 & Herr4) & _).
  rewrite (HAlo (as_errno B + Z.of_nat k)) by lia. exact (H k Hk). }
intros a n Ha0 Han (Hra & Hhu). split.
- eapply range_addressable_agree; [|exact Hra]. intros x Hx. apply HAlo. unfold shadow_of_addr.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold SHADOW_OFF. lia.
- intros Hn s Hs. pose proof (sa_hull_low a n s Ha0 Hn ltac:(lia) Hs). rewrite HAlo by lia. exact (Hhu Hn s Hs).
Qed.

(* the write premise of every run from the return site: the one writable region is [sp, sp + 32), inside parse_string's
   own window below the entry sp *)
Ltac sa_awr U2 Hsp Hwsp Hwstk e :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- 144 - e));
  [ reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ].
(* the bytes a run from the return site may write: [sp, sp + 32) *)
Ltac sa_inw U2 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros (r & Hin & Hr); vm_compute in Hin;
  destruct Hin as [Hq|[Hq|[Hq|[]]]]; subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?U2 in Hr; lia.

(* THE RETURN SITE (offset 204): `beqz a0` to the NULL return 1284; else `mv s2, a0`, the shadow check of s9 (its load
   reads the region's 0, so its branch folds), `ld a1, 0(s1)`, the `bgeu s4, a1` the run stops at (224), the constant
   block (15 registers and the three stack words), `mv s3, s2`, PS_DEC at 328. Offsets DERIVED: the engine's stops over
   the listing of record (PS_OFF + 204 / 224 / 328 / 1284). *)
(* the return site: the NULL arms keep fuzz_malloc's identity transfer, the block arm carries its HMal transfer into
   ps_alloc (ps_rpos_mal) *)
Lemma sc_after : forall D, ps_pre B ARx CTX CW D -> sc_after_at D.
Proof.
intros D HPRE Q regsc memc mdc ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HC HSH HGP HLED HPJ HROD R2 R8 R9 R20 R11 HSCAN
  HJ2 HJc HP HKM HMN2.
pose proof HPRE as ((HPX & HROD0 & HSTKHI) & HUNIV & HCH & HCLOW & HCW & HGAP & HROOM0 & (HWR0 & HCNTS0) & H100 & HIN0
  & Hpl & Hnth & HWIN & Hq1 & Hq2 & HRA0 & HSRC0 & HHOME0 & HLED0 & HCNT & HLIVE).
pose proof HPX as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HC as (HJ & HK & HSV & HSRC & HHOME & _).
pose proof (ajx_ar HJ) as HARc.
pose proof (ajx_ar HJ2) as HAR2. pose proof (ajx_ly HJ2) as Hly2. pose proof (ajx_pres HJ2) as Jpres2.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (ajx_hi HJc) as G1. pose proof (ajx_img HJc) as G3.
pose proof HPJ as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Htp & Hlen & Hg & Hqt & Hd).
pose proof HSRC as (_ & H4096t & Htc & _).
pose proof HLED as Hcnt0; apply ps_led_glob, ps_glob_cnt in Hcnt0.
pose proof HSH as (S24 & S23 & S25).
pose proof cf_head_nonneg as Hh0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HKM as (res & R10 & Hroom2 & HHU & HRP0 & HRP1 & HOUT & HAP).
(* the call's hull use, read at the all-granted list: the use part of every ps_rpos below *)
pose proof (ps_hull_used_mal D Q S2 HSCAN HHU) as HHU2.
assert (HQ1 : 0 <= Z.of_nat Q + 1) by lia.
sa_lits.
assert (Hsp : PS_SP D = spZ (pi_regs D) - 144) by (unfold PS_SP; change PS_FRAME with 144; reflexivity).
assert (Hwsp : PS_WSP D = spZ (pi_regs D) + pi_e D) by reflexivity.
assert (Hwstk : PS_WSTK D = 16560 + pi_e D) by (unfold PS_WSTK; sa_lits; reflexivity).
(* the registers the callee keeps (aregs_preserved) *)
assert (P2 : getr regs2 2%bv = getr regsc 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3%bv = getr regsc 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4%bv = getr regsc 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8%bv = getr regsc 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9%bv = getr regsc 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20%bv = getr regsc 20%bv) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23%bv = getr regsc 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24%bv = getr regsc 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25%bv = getr regsc 25%bv) by exact (HP 25 ltac:(unfold acallee_saved; lia)).
(* the rest of the text after the opening quote is not empty: the scan found a quote in it *)
assert (Hp1 : pi_p D + 1 < pi_text D + pi_len D).
{ destruct (Z_lt_le_dec (pi_p D + 1) (pi_text D + pi_len D)) as [Hl|Hl]; [exact Hl|]. exfalso.
  unfold ps_x, rest_atR in HSCAN. rewrite skipn_all2 in HSCAN by lia. discriminate. }
(* the stack at and above the call's sp is the callee journal's (its window lies below that sp) *)
assert (Hkst : forall a, PS_SP D <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H (pi_W D)) memc a).
{ intros a Ha. apply G1; lia. }
(* ---- the carried facts at the return site ---- *)
assert (HK2 : cj_kept SK segs B (prh_pst ) STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
  (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2).
{ eapply (cj_kept_trans SK segs B (prh_pst ) ARx cf_head LAWS); [exact HK | | exact HAR0 | exact HARc | | | |].
  - exact (cj_kept_of_journal SK segs B (prh_pst ) ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [(pi_q D, pi_q D + 8)] HJc).
  - sa_lits. lia.
  - lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
assert (HSV2 : ps_saved D W2 mem2).
{ unfold ps_saved in *. cbn zeta in *. destruct HSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
  repeat split; (eapply val_mem_kept; [intros i Hi; apply Hkst; cbn in Hi; lia | eassumption]). }
(* the allocator's three arms, read through: the blocks only grow, the post ledger holds every entry block, and the
   text is still at its home at the call's allocator state with the post's hidden heads *)
assert (HARM : (forall x, In x (ablocks B (pi_ly D) (pi_S D)) -> In x (ablocks B ly2 S2)) /\
  (exists Lam2 pk2 c2 f2 r2 mo2 ow2, prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 pk2 c2 f2 r2 mo2 ow2 /\ forall x, In x (pi_Lam D) -> In x Lam2) /\
  prhReader_home B (pi_ly D) (pi_S D) Hp2 (pi_Lam D) (pi_text D) (pi_len D)).
{ destruct HAP as [(Hcf & Hres & EHp & Eab & HL2) | [(Hcf & Hres & EHp & Eab & _ & _ & HL2) |
    (Hcf & H4096 & H16 & Hnl & EHp & Eab & _ & _ & _ & HL2)]].
  - split; [rewrite Eab; tauto|]. split; [do 7 eexists; split; [exact HL2 | tauto]|]. rewrite EHp. exact HHOME.
  - split; [rewrite Eab; tauto|]. split; [do 7 eexists; split; [exact HL2 | tauto]|]. rewrite EHp. exact HHOME.
  - split; [rewrite Eab; intros x Hx; apply in_or_app; left; exact Hx|].
    split; [do 7 eexists; split; [exact HL2 | intros x Hx; right; exact Hx]|].
    destruct HHOME as [Hk | (b & m & Hin & Hnh & Hb & Hm)]; [left; exact Hk|].
    right. exists b, m. split; [exact Hin|]. split; [|split; assumption].
    rewrite EHp. intros [Eb | Hi]; [|exact (Hnh Hi)].
    (* b = res - cf_head: the old block (b, m) and the new one are both live after, apart, and both non-empty *)
    assert (Hm0 : 0 <= m) by lia.
    assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; left; exact Hin).
    assert (Hnew2 : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
      by (rewrite Eab; apply in_or_app; right; left; reflexivity).
    assert (Hne : (b, m) <> (res - cf_head, Z.of_nat Q + 1 + cf_head)).
    { intros E. rewrite E in Hin. clear E.
      destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hnew2) as (_ & _ & _ & _ & _ & Hpw).
      rewrite Eab in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw. clear El.
      pose proof (pairwise_In2 zdisjoint _ (res - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
        (res - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
        (map (fun b : Z * Z => (fst b, req_size (snd b))) l1) (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
        ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Dj.
      unfold zdisjoint in Dj. cbn [fst snd] in Dj. pose proof (req_size_pos (Z.of_nat Q + 1 + cf_head) (Z.add_nonneg_nonneg _ _ HQ1 Hh0)). lia. }
    pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hin2 Hnew2 Hne) as Hdj.
    pose proof (req_size_pos m Hm0). pose proof (req_size_pos (Z.of_nat Q + 1 + cf_head) (Z.add_nonneg_nonneg _ _ HQ1 Hh0)).
    unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. clear Hne. lia. }
destruct HARM as (Eab_incl & (Lam2 & pk2 & c2 & f2 & r2 & mo2 & ow2 & HL2 & Hincl) & HHOMEc).
(* the text across the call (S4_PsSrc.v), at the call's journal (its first heads are not read by the journal) *)
assert (SP0 : prhReader_home B (pi_ly D) (pi_S D) Hp2 (pi_Lam D) (pi_text D) (Z.of_nat (length (pi_tb D))))
  by (rewrite Hlen; exact HHOMEc).
assert (SP1 : forall a, inFP [] a -> ~ (pi_text D <= a < pi_text D + Z.of_nat (length (pi_tb D))))
  by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
assert (SP2 : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
assert (SP3 : forall p n, In (p, n) (ablocks B (pi_ly D) (pi_S D)) -> ~ In p Hp2 ->
  In (p, n) (ablocks B ly2 S2) /\ ~ In p Hp2) by (intros p n Hin Hnh; exact (conj (Eab_incl _ Hin) Hnh)).
assert (SP4 : forall b m, In (b, m) (pi_Lam D) -> In (b - cf_head, m + cf_head) (ablocks B (pi_ly D) (pi_S D))).
{ intros b m Hin. pose proof HLED as HF; apply ps_led_blocks in HF.
  pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (_ & Hab & _). exact Hab. }
assert (SP5 : forall b m, In (b, m) (pi_Lam D) ->
  0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) Hp2).
{ intros b m Hin. pose proof HL2 as (_ & _ & HF2 & _).
  pose proof (proj1 (Forall_forall _ _) HF2 (b, m) (Hincl _ Hin)) as (Hm0 & Hab & Hhp & _). exact (conj Hm0 (conj Hab Hhp)). }
assert (SP6 : forall h, In h Hp2 -> exists k, 0 <= k /\ In (h, k) (ablocks B ly2 S2)).
{ intros h Hh. pose proof HL2 as (_ & _ & HF2 & HP2m). apply (Permutation_in _ HP2m) in Hh.
  apply in_map_iff in Hh as ((a & m) & Ea & Hin). cbn [fst] in Ea.
  pose proof (proj1 (Forall_forall _ _) HF2 (a, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
  exists (m + cf_head). split; [lia|]. rewrite <- Ea. exact Hab. }
destruct (ps_src_after_call B ARx SK LAWS ZSA IMGV _ _ _ (pi_ly D) (pi_S D) Hp2 (pi_W D) memc mdc ly2 S2 Hp2 W2 mem2 md2 k1
  (pi_Lam D) (pi_text D) (pi_tb D) HJc HSRC SP0 SP1 SP2 SP3 SP4 SP5 SP6) as [HSRC2 HHOME2].
rewrite Hlen in HHOME2.
assert (HIN2 : pj_in_okR segs (mrestrict (w_H W2) mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)).
{ split; [eapply val_mem_kept; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Vp]|].
  split; [eapply val_mem_kept; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Ve]|].
  split; [eapply val_mem_kept; [intros i Hi; apply Hkst; cbn in Hi; lia | exact Vd]|].
  split; [intros x Hx; apply (apresent_writable segs); apply Jpres2; lia|].
  do 5 (split; [assumption|]).
  split; [exact (proj1 HSRC2)|]. split; assumption. }
assert (HROD2 : arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W2) mem2)).
{ intros a Hro Hno Her.
  rewrite (G3 a (psrc_ro_img a Hro) Hno Her (fun Hx => prh_pst_not_ro a Hx Hro) (fp_spares_closed [] a SP2)).
  exact (HROD a Hro Hno Her). }
(* ---- the symbolic state at 204 ---- *)
assert (HS : st_ok_pi segs VAL (SC_E regs2 (pi_text D + pi_len D)) ss_sa
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (PS_OFF + 204))) mem2 (seg_rom segs)))).
{ apply (sa_entry D W2 regs2 mem2 ly2 S2 Hp2 md2 HAR2).
  - rewrite Eslo, Eshi. lia.
  - rewrite P2. exact R2.
  - rewrite P9. exact R9.
  - rewrite P24. exact S24.
  - rewrite P25. exact S25.
  - pose proof HIN2 as (_ & Ve2 & _). exact Ve2.
  - intros a Ha. apply Jpres2. lia.
  - lia.
  - rewrite Hsp, Zminus_mod, Hal16. reflexivity.
  - lia.
  - lia.
  - lia. }
set (E := SC_E regs2 (pi_text D + pi_len D)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, SC_E; apply Eimg_env).
assert (SHOK : sh_ok segs SC_Bx [] E (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
assert (U2 : bv_unsigned (ew E 2) = PS_SP D)
  by (unfold E; rewrite (sc_ew_reg regs2 _ 2 2%bv eq_refl ltac:(lia)), P2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (E10 : ew E 10 = w64 res) by (unfold E; rewrite (sc_ew_reg regs2 _ 10 10%bv eq_refl ltac:(lia)); exact R10).
assert (U20 : bv_unsigned (ew E 20) = pi_p D + 1)
  by (unfold E; rewrite (sc_ew_reg regs2 _ 20 20%bv eq_refl ltac:(lia)), P20, R20; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pi_text D + pi_len D)
  by (unfold E; rewrite sc_ew_byte; apply unsigned_lit_small; lia).
assert (Rres : 0 <= res < 2 ^ 64).
{ destruct HAP as [(_ & -> & _) | [(_ & -> & _) | (_ & H4096 & _ & _ & _ & Eab & _)]]; [lia | lia |].
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (res - cf_head) (Z.of_nat Q + 1 + cf_head) HAR2
    ltac:(rewrite Eab; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hc & _).
  pose proof (req_size_pos (Z.of_nat Q + 1 + cf_head) (Z.add_nonneg_nonneg _ _ HQ1 Hh0)). lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B (prh_pst ) ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B (prh_pst ) ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold ps_pc, w64. rewrite <- Z.add_assoc.
psrr_branch_tok RUN BR HS SHOK SC_Bspan.
- (* ==== `beqz a0` TAKEN: the allocator returned NULL; offset 204 to the NULL return 1284 ==== *)
  rewrite branch_eq_U, (U_atom _ 10 res E10 Rres), U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. subst res.
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN2 SC_Bspan (PS_OFF + PS_RET0); [sa_awr U2 Hsp Hwsp Hwstk (pi_e D)|].
  assert (HM : forall x : word, ~ (PS_SP D <= bv_unsigned x < PS_SP D + 32) ->
    mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x).
  { intros x Hx. apply HFr. intros Hin. apply Hx. revert Hin. sa_inw U2. }
  destruct (sa_keep D ly2 S2 Hp2 W2 mem2 md2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) HPRE HAR2 Eslo Eshi HM HG
    (same_but_materialized_wvb_any md2 mat))
    as (KK & KSV & KSRC & KIN & KROD & KLED & KERR & KVIS).
  assert (K2 : getr (ms_regs ms) 2%bv = getr regs2 2%bv)
    by (apply (sa_reg_atom _ _ _ _ _ _ _ 2%nat HS); [reflexivity | reflexivity | lia]).
  assert (K3 : getr (ms_regs ms) 3%bv = getr regs2 3%bv)
    by (apply (sa_reg_atom _ _ _ _ _ _ _ 3%nat HS); [reflexivity | reflexivity | lia]).
  assert (K4 : getr (ms_regs ms) 4%bv = getr regs2 4%bv)
    by (apply (sa_reg_atom _ _ _ _ _ _ _ 4%nat HS); [reflexivity | reflexivity | lia]).
  assert (HCOM : (exists k, ps_carryP B ARx SK P D ly2 S2 Hp2 W2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) k []) /\
    ps_gptp D (ms_regs ms) /\ getr (ms_regs ms) 2 = w64 (PS_SP D)).
  { split; [exists (0 + k1); exact (conj HJ2 (conj (KK HK2) (conj (KSV HSV2) (conj (KSRC HSRC2) (conj HHOME2 HMN2)))))|].
    split; [unfold ps_gptp; rewrite K3, K4, P3, P4; exact HGP | rewrite K2, P2; exact R2]. }
  pmkst HS.
  assert (EPC : BASE + 26736 = ps_pc PS_RET0) by (unfold ps_pc; vm_compute; reflexivity).
  rewrite EPC.
  apply ps_finP_of_postP. apply (HRET0P D ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) HPRE).
  destruct HCOM as (HCA & HCG & HC2).
  destruct HAP as [(Hcf & _ & EHp & Eab & HL) | [(Hcf & _ & EHp & Eab & HNP & HERR & HL) | (_ & H4096 & _)]];
    [| | lia].
  + (* the chosen failure (cnt = fail) *)
    split; [apply ps_carryPw_nil; exact HCA|]. split; [exact HCG|]. split; [exact HC2|]. split; [exact Hroom2|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab;
            pose proof (sa_held _ _ HSCAN); lia|].
    unfold ps_Qres. rewrite HSCAN. left.
    split; [exact Hcf|]. split; [reflexivity|]. split; [exact EHp|]. split; [exact Eab|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab; reflexivity|].
    rewrite Z.mod_small in HL by lia.
    split; [exact (KLED _ _ _ _ _ _ _ HL)|]. split; [exact (KIN HIN2)|].
    exact (conj HHU2 (HRP0 eq_refl)).
  + (* the refusal (cnt <> fail, malloc_cf_null_post) *)
    split; [apply ps_carryPw_nil; exact HCA|]. split; [exact HCG|]. split; [exact HC2|]. split; [exact Hroom2|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab;
            pose proof (sa_held _ _ HSCAN); lia|].
    unfold ps_Qres. rewrite HSCAN. right; left.
    split; [exact Hcf|]. split; [reflexivity|]. split; [exact EHp|]. split; [exact Eab|].
    split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab; reflexivity|].
    split; [exact HNP|]. split; [exact (KERR _ HERR)|].
    (* the batch text's outcome exclusion (PRH_FnReader f1ae32e3b2cd :624-629), from the malloc's outcome clause *)
    split; [exact (ps_excl_of_malloc D Q S2 0 HSCAN Hcf eq_refl HOUT)|].
    (* the ledger: the callee's refusal arm VERBATIM, the count `(cnt + 1) mod 2 ^ 64` kept (:634-635) *)
    split; [exact (KLED _ _ _ _ _ _ _ HL)|]. split; [exact (KIN HIN2)|].
    exact (conj HHU2 (HRP0 eq_refl)).
- (* ==== `beqz a0` NOT TAKEN: the new block, offsets 208..328 ==== *)
  rewrite branch_eq_U, (U_atom _ 10 res E10 Rres), U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc.
  (* the position transfer of this call: fuzz_malloc's own HMal arm, keyed on the block it returned *)
  assert (HRPS : ps_rpos_mal D Q S2) by exact (conj HHU2 (HRP1 Hc)).
  destruct HAP as [(_ & Hz & _) | [(_ & Hz & _) | (Hcf & H4096 & H16 & Hnl & EHp & Eab & Hra & Hhu & Hbytes & HL)]];
    [exfalso; exact (Hc Hz) | exfalso; exact (Hc Hz) |].
  clear Hc.
  assert (Hin_o : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S2))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin_o) as (_ & _ & Hco & _).
  pose proof (req_size_pos (Z.of_nat Q + 1 + cf_head) (Z.add_nonneg_nonneg _ _ HQ1 Hh0)) as [Rq1 Rq2].
  (* 204..224: mv s2, a0; the shadow check of s9 (folded); ld a1, 0(s1); stuck at the bgeu *)
  paj_run_tok_x_inv RUN HS HJ2 SHOK HMN2 SC_Bspan; [sa_awr U2 Hsp Hwsp Hwstk (pi_e D)|].
  rename HFr into HFr1, HG into HG1, ms into ms1, mat into mat1. clear HF.
  assert (HM1 : forall x : word, ~ (PS_SP D <= bv_unsigned x < PS_SP D + 32) ->
    mrestrict (w_H W2) (ms_mem ms1) x = mrestrict (w_H W2) mem2 x).
  { intros x Hx. apply HFr1. intros Hin. apply Hx. revert Hin. sa_inw U2. }
  psrr_branch_tok RUN BR HS SHOK SC_Bspan.
  + (* `bgeu s4, a1` TAKEN: p + 1 >= text + len, refuted *)
    exfalso. rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite !U_SOff, U20, U32 in Hc. rewrite !zcanon_id in Hc by (unfold M64; lia). lia.
  + clear Hc.
    (* 224..328: the constant block, mv s3, s2 *)
    paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN2 SC_Bspan (PS_OFF + PS_DEC); [sa_awr U2 Hsp Hwsp Hwstk (pi_e D)|].
    assert (HM2 : forall x : word, ~ (PS_SP D <= bv_unsigned x < PS_SP D + 32) ->
      mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) (ms_mem ms1) x).
    { intros x Hx. apply HFr. intros Hin. apply Hx. revert Hin. sa_inw U2. }
    assert (HM : forall x : word, ~ (PS_SP D <= bv_unsigned x < PS_SP D + 32) ->
      mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x)
      by (intros x Hx; rewrite (HM2 x Hx); exact (HM1 x Hx)).
    assert (HGt : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)))
      by (intros x Hx; exact (HG x (HG1 x Hx))).
    rewrite wvb_collapse in HJ2.
    destruct (sa_keep D ly2 S2 Hp2 W2 mem2 md2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) HPRE HAR2 Eslo Eshi HM HGt
      (same_but_materialized_wvb_any md2 mat))
      as (KK & KSV & KSRC & KIN & KROD & KLED & KERR & KVIS).
    (* the registers at PS_DEC *)
    assert (K2 : getr (ms_regs ms) 2%bv = getr regs2 2%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 2%nat HS); [reflexivity | reflexivity | lia]).
    assert (K3 : getr (ms_regs ms) 3%bv = getr regs2 3%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 3%nat HS); [reflexivity | reflexivity | lia]).
    assert (K4 : getr (ms_regs ms) 4%bv = getr regs2 4%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 4%nat HS); [reflexivity | reflexivity | lia]).
    assert (K8 : getr (ms_regs ms) 8%bv = getr regs2 8%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 8%nat HS); [reflexivity | reflexivity | lia]).
    assert (K9 : getr (ms_regs ms) 9%bv = getr regs2 9%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 9%nat HS); [reflexivity | reflexivity | lia]).
    assert (K20 : getr (ms_regs ms) 20%bv = getr regs2 20%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 20%nat HS); [reflexivity | reflexivity | lia]).
    assert (K23 : getr (ms_regs ms) 23%bv = getr regs2 23%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 23%nat HS); [reflexivity | reflexivity | lia]).
    assert (K24 : getr (ms_regs ms) 24%bv = getr regs2 24%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 24%nat HS); [reflexivity | reflexivity | lia]).
    assert (K25 : getr (ms_regs ms) 25%bv = getr regs2 25%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 25%nat HS); [reflexivity | reflexivity | lia]).
    (* s2 = s3 = out (a0 = res), a1 = text + len (the word at q + 8) *)
    assert (K18 : getr (ms_regs ms) 18%bv = getr regs2 10%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 10%nat HS); [reflexivity | reflexivity | lia]).
    assert (K19 : getr (ms_regs ms) 19%bv = getr regs2 10%bv)
      by (apply (sa_reg_atom _ _ _ _ _ _ _ 10%nat HS); [reflexivity | reflexivity | lia]).
    assert (K11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 (pi_text D + pi_len D))
      by (apply (sa_reg_tl _ _ _ _ _ _ HS); reflexivity).
    (* the three surrogate constants the block stored at sp + 24, sp + 16, sp + 8 (WORD 55296, 56320, -56613888) *)
    assert (HREG : region_ok segs E (mrestrict (w_H W2) (ms_mem ms))
      (YP09.mkRegion (Some 2%nat) 0 32 0 32 [YP09.mkChunk 16 (CVal 8 (SLit 56320));
         YP09.mkChunk 8 (CVal 8 (SLit 18446744073652937728)); YP09.mkChunk 24 (CVal 8 (SLit 55296))]))
      by exact (st_ok_region_nth segs E _ _ 2%nat _ HS eq_refl).
    assert (V24 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (PS_SP D + 24) 8 55296).
    { apply (slot_of_region segs E _ (PS_SP D) _ 0 32 0 32 24 (SLit 55296) 55296 HREG U2); [cbn; tauto | reflexivity | lia]. }
    assert (V16 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (PS_SP D + 16) 8 56320).
    { apply (slot_of_region segs E _ (PS_SP D) _ 0 32 0 32 16 (SLit 56320) 56320 HREG U2); [cbn; tauto | reflexivity | lia]. }
    assert (V8 : val_mem segs (mrestrict (w_H W2) (ms_mem ms)) (PS_SP D + 8) 8 (-56613888)).
    { apply sa_val_mod. change ((-56613888) mod 2 ^ 64) with 18446744073652937728.
      apply (slot_of_region segs E _ (PS_SP D) _ 0 32 0 32 8 (SLit 18446744073652937728) 18446744073652937728 HREG U2);
        [cbn; tauto | reflexivity | lia]. }
    pmkst HS.
    assert (EPC : BASE + 25780 = ps_pc PS_DEC) by (unfold ps_pc; vm_compute; reflexivity).
    rewrite EPC.
    apply ps_finP_hand. apply (HDECP D ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) res res (pi_p D + 1) Q HPRE).
    split; [exists (0 + k1); exact (conj HJ2 (conj (KK HK2) (conj (KSV HSV2) (conj (KSRC HSRC2) (conj HHOME2 HMN2)))))|].
    split.
    { (* the one fuzz_malloc's allocation (ps_alloc) *)
      split; [exact Hcf|]. split; [exact H4096|]. split; [exact H16|]. split; [exact EHp|]. split; [exact Eab|].
      split; [rewrite Z.mod_small in HL by lia; exact (KLED _ _ _ _ _ _ _ HL)|].
      split; [apply KVIS; [lia | lia | exact (conj Hra Hhu)]|].
      split; [exact Hroom2|]. split; [exact HRPS|].
      rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab, bsum_app.
      cbn [bsum fold_right snd]. lia. }
    split; [unfold ps_sh_regs; rewrite K24, K23, K25, P24, P23, P25; exact HSH|].
    split; [unfold ps_gptp; rewrite K3, K4, P3, P4; exact HGP|].
    split.
    { (* ps_dec_consts: the fifteen constant registers and the three stack words *)
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [apply (sa_reg_lit _ _ _ _ _ _ HS); reflexivity|].
      split; [exact V24|]. split; [exact V16 | exact V8]. }
    split; [exact (KIN HIN2)|].
    split; [exact (KROD HROD2)|].
    split; [exact HSCAN|].
    split; [rewrite K2, P2; exact R2|].
    split; [rewrite K18, R10; reflexivity|].
    split; [rewrite K19, R10; reflexivity|].
    split; [rewrite K20, P20; exact R20|].
    split; [rewrite K11; reflexivity|].
    split; [rewrite K8, P8; exact R8|].
    split; [rewrite K9, P9; exact R9|].
    (* ps_dec_rel at done = []: nothing decoded yet, the read cursor at p + 1 *)
    exists []. split; [unfold bytes_at; apply garr8_nil|]. split; [cbn [length Z.of_nat]; lia|].
    split; [intros sx rx Hdx; exact Hdx|]. split; [intros Hdx; exact Hdx|].
    split; [lia|]. split; [lia|]. split; [lia|].
    replace (pi_p D + 1 - (pi_p D + 1)) with 0 by lia. cbn [Z.to_nat]. rewrite Nat.sub_0_r. exact HSCAN.
Qed.

(* THE STRETCH in the generic-P form, from its one explicit argument of record: fuzz_malloc's two live counts at the
   entry's allocator state (sc_cnt). The position transfer and the memnorm keep after the call are the text's own. *)
Theorem ps_seg_scan_cntP : forall D, ps_pre B ARx CTX CW D -> sc_cnt D ->
  forall ly S Hp W regs mem md x, ps_at_scanP B ARx SK P D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_SCAN) regs mem md)
    (ps_postPR B ARx SK P (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros D HPRE HCNT ly S Hp W regs mem md x HAT.
pose proof HAT as (_ & _ & _ & Ely & ES & EHp & EW & _). subst ly S Hp W.
apply ps_finP_SRr'.
apply (sc_loop D HPRE (sc_found_of_call D HPRE (sc_call_of_after D HPRE HCNT (sc_after D HPRE)))
  (Z.to_nat (pi_text D + pi_len D - x)) x regs mem md); [lia | exact HAT].
Qed.
End scP.

(* THE STABLE STATEMENT: the P := (fun _ => True) instance of ps_seg_scan_cntP (srr_inv_laws_True, srr_inv_call_True,
   ps_seg_ret0_of_True / ps_seg_dec_of_True for the other cuts, ps_carryP_T / ps_postP_T for the cut and the post).
   It is the preview statement (at the cursor set CW for DW) less the keep argument sc_mnk and the position argument
   sc_rp: the statement moved for the callee's TEXT (fuzz_malloc's text is m-form and post-implication now), not for
   the invariant (exempt from the byte-identical rule, a Theorem Labs lane 12:22Z (3)). Consumer: S4_PsTop.v. *)
Theorem ps_seg_scan_cnt : forall D, ps_pre B ARx CTX CW D -> sc_cnt D ->
  forall ly S Hp W regs mem md x, ps_at_scan B ARx SK D ly S Hp W regs mem md x ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (ps_pc PS_SCAN) regs mem md)
    (ps_postR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) CW D).
Proof.
intros D HPRE HCNT ly S Hp W regs mem md x HAT.
assert (HR : ps_seg_ret0P B ARx SK (fun _ => True) CTX CW) by (apply ps_seg_ret0_of_True; exact HRET0).
assert (HD : ps_seg_decP B ARx SK (fun _ => True) CTX CW) by (apply ps_seg_dec_of_True; exact HDEC).
assert (HA : ps_at_scanP B ARx SK (fun _ => True) D ly S Hp W regs mem md x).
{ destruct HAT as (Hc & HAT). split; [apply ps_carryP_T; exact Hc | exact HAT]. }
unfold SRr'. eapply (SRrG_mono segs (wle' segs YGcfRehidePost.RZ_cf));
  [exact (ps_seg_scan_cntP (fun _ => True) srr_inv_laws_True srr_inv_call_True HR HD
    D HPRE HCNT ly S Hp W regs mem md x HA)|].
intros W' c' _ HQ. apply ps_postPR_T. exact HQ.
Qed.

End sc.
