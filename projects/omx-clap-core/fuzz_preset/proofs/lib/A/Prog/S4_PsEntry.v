(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_ctrl_identity_poll_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlIdentityPollBlock.v, with its module paths, module names and numbers changed; 695 of its 772 lines of code are new or changed and 346 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/FuzzStrdup.v, with its module names changed; 517 of its 577 lines of code are new or changed and 712 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string): the ENTRY stretch, offsets 0..131 of parse_string (DERIVED), from the
   entry to the scan loop head PS_SCAN (132) or the NULL return PS_RET0 (1284). The contract is S4_PsBase.v; this
   file proves its ps_seg_entry, with ps_seg_scan and ps_seg_ret0 as Section hypotheses.
   KIT: the kit's cut 7cdbb61b5fa0; this file is INT102-READY there. Earlier it was on the KIT PREVIEW, walkkit-next
   0afb3f76c28 (position pass + S' = S sweep), NOT on the kit of record; its acceptance artifact on the kit of
   record preset-tree-at-2026-10-29T08-11-33Z.tsv (sha256 494eefc5b155; internal record) was commit preset-tree-at-2026-10-29T08-27-48Z.tsv (sha256 d86722ddcdf6; internal record) (same proof, its own header names
   a3bdeca3920; it carries no preview text). Blob ids at the cut (git ls-tree 7cdbb61b5fa0), as the kit's cut
   preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) carries them:
     lib/A/PRH_Base.v ef7c8ca98529, lib/A/PRH_FnReader.v f1ae32e3b2cd, lib/A/PRH_FnAlloc.v 4d8aeba047e5,
     lib/A/PRH_Img.v 934516a622e8, lib/A/PRH_Reader.v 4266e709561a, lib/A/PRH_Charge.v 2b0b34262818,
     lib/Spec/PjGrammar.v 5d4026de2876, lib/Spec/PresetRoomPos.v 943d62290e8e,
     lib/Spec/PresetLiveBounds.v f78da450d5f6, lib/Prog/Ledger.v 93c436f951b0,
     lib/Reusable/YCbqG.v 219748197d6b (AR_laws_x with hl), YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f,
     YCbqGcall.v c1fcd07d2537, lib/A/Listing_prog.v 7ed1529926bd, lib/A/PAImg_prog.v 505a51ff7d08,
     lib/A/Prog/PRW_CallerJ.v 473f33abadbc, PRW_StepKit.v 0df3991c13f4.
   THE POSITION (post-implication). This stretch allocates nothing, so the astate at both
   exits IS the entry's and its own events are none: the NULL return's ps_Qres None arm takes the identity transfer
   ps_rpos D [] (pi_S D) (S4_PsBase.ps_rpos_nil), and ps_at_scan pins S = pi_S D by reflexivity. No step lemma, no
   stand-in.
   THE OFFSETS below are not measured off a disassembly: the symbolic engine produced each one while running the
   listing of record (PI_prog_A), and the proof fails if any is wrong.
   THE INSTRUCTIONS (every numeral below is a DERIVED byte offset inside parse_string, a frame LENGTH, or a WORD
   constant; none is an ADDRESS):
     0        addi sp,sp,-144                          (LENGTH: PS_FRAME)
     4..52    the 13 saves: ra 136, s0 128, s1 120, s2 112, s3 104, s4 96, s5 88, s6 80, s7 72, s8 64, s9 56,
              s10 48, s11 40                           (DERIVED frame offsets) -> ps_saved
     56,60    auipc a1 ; ld a1,1676(a1)                 the GOT slot A_OBJ 0 (got_regionP)
     64       ld s8,0(a1)                               the shadow base A_OBJ 12 (bcell_regionP)
     68       mv s0,a0                                  s0 = q
     72..84   srli s7,a0,3; add s7,s7,s8; lbu a0,0(s7); bnez a0 -> 1408   NOT taken: the shadow entry
              mkSHE 10 0 24 (from ps_pre's range_addressable q 24) folds the load to 0
     88       addi s1,s0,8                              s1 = q + 8
     92..104  the same check for q + 8 (s9 = its shadow cell); bnez -> 1416   NOT taken
     108      ld s4,0(s0)                               s4 = p           (pj_in_okR, the q region's chunk at 0)
     112      ld a1,0(s1)                               a1 = text + len  (pj_in_okR, its chunk at 8)
     116      addi s4,s4,1
     120      bgeu s4,a1 -> 1284                        taken: the rest after the quote is empty, so
                                                        PjGrammar.scan (ps_x D) = None and ps_Qres' None arm holds
     124,128  li a2,34 ; mv a0,s4                       (WORD 34, the ASCII double quote), fall into PS_SCAN at 132
   The journal starts at the widened window with ajournal_x_init_W (PRW_CallerJ.v) and the carried cj_kept is built
   by cj_kept_exec over each of the two straight-line runs and chained by cj_kept_trans. The stretch allocates
   nothing and makes no call, so the allocator state, the heap set and the world are the entry's throughout.
   THE GENERIC-P FORM (a Theorem Labs lane 12:18Z / 12:22Z; base 44a91d58bb5, S4_PsBase.v
   a59ce5bfcbe3, Section gp). An SRr post is OPAQUE once Qed, so an end-state invariant must be in the segment's
   statement: ps_entry_holdsP : ps_seg_entryP P is stated over any memory invariant P with srr_inv_laws segs P (the one
   premise: the stretch makes NO call, so no srr_inv_call). P of the end memory is PROVED FROM THE RUN, never from where
   the body stores: it starts as ps_seg_entryP's premise P (pi_mem D); each of the two runs goes through its
   YSRrMemnorm twin (paj_run_x_inv / paj_run_to_x_inv at P with PLAW; tactics paj_run_tok_x_inv / paj_run_to_tok_x_inv),
   which takes HPM of the start memory and gives HPM of the end memory; the branch at 120 does not change the state.
   Both exits pass the last run's HPM as ps_carryP's last conjunct. The symbolic runs, frames and obligations are those
   of the stable proof. ps_entry_holds keeps its stable statement, byte-identical, as the P := (fun _ => True)
   instance (ps_seg_entry_of_True / ps_seg_scan_of_True / ps_seg_ret0_of_True, srr_inv_laws_True of S4_PsBase.v).
   YSRrMemnorm.v 5ffa8525936b (the cut's) Requires YAkMemnorm 96c72061b4d4 only: neither
   loads LiaTwx2, so lia here is the lia this proof was first built with. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
(* YK06 is NOT imported here: its plain constant alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling
   that the journal, astk_ok and asan_consts speak about *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit S4_PsBase.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* as the walk templates (FuzzStrdup.v, CtrlChecksumVerify.v) set it: lia reads a division as an atom, and the
   division bounds below are supplied by Z.div_pos / Z.div_le_upper_bound / Z.div_lt_upper_bound *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the base's instance constants are Local to its module: reached here by their qualified names, so that every
   term this file builds (segs, STK_parse_string, PALib's instance) is syntactically the base's *)
Module PSB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.S4_PsBase.

Section pe. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
(* the image instances of record: the base's own (S4_PsBase.v), never left to inference *)
#[local] Existing Instance PSB.PS_PrhImg.
#[local] Existing Instance PSB.PS_PAListing | 0.
#[local] Existing Instance PSB.PS_PAImg | 0.
#[local] Notation segs := (@pa_segs _ A_prog_listing PSB.PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PSB.PS_PAImg).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PSB.PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PSB.PS_PAImg A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
#[local] Notation PST := (prh_pst).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the program listing's library facts, over the PROGRAM instance: over a per-function listing PALib is vacuous *)
Hypothesis TL : @PALib _ A_prog_listing PSB.PS_PAImg B.
(* the two exits of this stretch, stable form (S4_PsBase.v): the premises of the P := True instance ps_entry_holds *)
Hypothesis HSCAN : ps_seg_scan B ARx SK CTX CW.
Hypothesis HRET0 : ps_seg_ret0 B ARx SK CTX CW.

(* ---- the entry symbolic state. Atom indices are the engine's numbering (DERIVED): 0..31 the registers,
   32 = p, 33 = text + len, 34 = the shadow base; 241 = A_OBJ 0 (the GOT slot), 253 = A_OBJ 12 (the variable). ---- *)
Definition PE_Bx : sv := SOff 34 0.
Definition PE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the ONE shadow entry: ps_pre's range_addressable over the caller's 24-byte cursor struct at q *)
Definition PE_SH : list shent := [ mkSHE 10 0 24 ].
Definition pe_qregion : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
(* LENGTH 144: parse_string's own frame (PS_FRAME, checked by pe_frame) *)
Definition pe_regions : smem := [ stack_region 144; got_regionP; bcell_regionP 34; pe_qregion ].
Definition pe_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 24) 3);
           (34%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pe : sstate := mkSS PS_OFF sr_atoms pe_regions None pe_facts.
Definition pe_extra (D : ps_in) : list word := [w64 (pi_p D); w64 (pi_text D + pi_len D); w64 SHADOW_OFF].
Definition PE_E (D : ps_in) : env := @Eimg _ A_prog_listing PSB.PS_PAImg (Ereg (pi_regs D) (pe_extra D)).

(* ---- the image numbers this stretch needs, all by computation on the generated listing ---- *)
Lemma pe_sigma : SIGMA AS_parse_string = BASE + PS_OFF.
Proof. vm_compute. reflexivity. Qed.
Lemma pe_stk : 144 <= STK_parse_string.
Proof. vm_compute. discriminate. Qed.
Lemma pe_stk2 : 16384 <= STK_parse_string.
Proof. vm_compute. discriminate. Qed.
Lemma pe_frame : PS_FRAME = 144.
Proof. vm_compute. reflexivity. Qed.
(* the two exit pcs, in the listing's own offsets *)
Lemma pe_pc_exit : forall off z, z = PS_OFF + off -> BASE + z = ps_pc off.
Proof. intros off z ->. unfold ps_pc. rewrite Z.add_assoc. reflexivity. Qed.
(* the allocator's statics (the five of alloc.c and #102's g_most / g_own_ran_out) lie in the image *)
Lemma pe_globs :
  0 <= pi_g_live /\ pi_g_live + Z.of_nat pi_gz_live <= YImgTop.IMG_TOP /\
  0 <= pi_g_peak /\ pi_g_peak + Z.of_nat pi_gz_peak <= YImgTop.IMG_TOP /\
  0 <= pi_g_count /\ pi_g_count + Z.of_nat pi_gz_count <= YImgTop.IMG_TOP /\
  0 <= pi_g_fail /\ pi_g_fail + Z.of_nat pi_gz_fail <= YImgTop.IMG_TOP /\
  0 <= pi_g_ran_out /\ pi_g_ran_out + Z.of_nat pi_gz_ran_out <= YImgTop.IMG_TOP /\
  0 <= pi_g_most /\ pi_g_most + Z.of_nat pi_gz_most <= YImgTop.IMG_TOP /\
  0 <= pi_g_own_ran_out /\ pi_g_own_ran_out + Z.of_nat pi_gz_own_ran_out <= YImgTop.IMG_TOP.
Proof. repeat split; vm_compute; discriminate. Qed.

(* ---- the environment at the entry ---- *)
Lemma pe_Ereg : forall (D : ps_in) (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (PE_E D) n = getr (pi_regs D) r.
Proof.
intros D n r Hn Hlt. unfold PE_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat (pi_regs D) _ n r Hn).
Qed.
Lemma pe_E : forall D, getr (pi_regs D) 10 = w64 (pi_q D) ->
  ew (PE_E D) 10 = Z_to_bv 64 (pi_q D) /\
  ew (PE_E D) 32 = Z_to_bv 64 (pi_p D) /\
  ew (PE_E D) 33 = Z_to_bv 64 (pi_text D + pi_len D) /\
  ew (PE_E D) 34 = Z_to_bv 64 SHADOW_OFF /\
  ew (PE_E D) (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) /\
  ew (PE_E D) (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)).
Proof.
intros D H10. unfold PE_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat (pi_regs D) _ 10 10%bv eq_refl); exact H10|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia);
        replace 32%nat with (32 + 0)%nat by lia; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia);
        replace 33%nat with (32 + 1)%nat by lia; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia);
        replace 34%nat with (32 + 2)%nat by lia; rewrite ew_Ereg_extra; reflexivity|].
split; [apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia | apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia].
Qed.

(* ---- the entry state: st_ok_pi and sh_ok at parse_string's first slot ---- *)
Lemma pe_entry : forall (D : ps_in),
  afn_pre_x segs B ARx STK_parse_string (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) ->
  getr (pi_regs D) 10 = w64 (pi_q D) ->
  pj_in_okR segs (mrestrict (w_H (pi_W D)) (pi_mem D)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
  fwin (pi_ly D) (pi_W D) (pi_regs D) (pi_mem D) (pi_e D) ->
  spZ (pi_regs D) <= pi_q D -> pi_q D + 24 <= spZ (pi_regs D) + pi_e D ->
  range_addressable (aview segs (w_H (pi_W D)) (pi_mem D)) SHADOW_OFF (pi_q D) 24 ->
  st_ok_pi segs VAL (PE_E D) ss_pe
    (restrict (w_H (pi_W D)) (mkst (pi_regs D) (Z_to_bv 64 (BASE + PS_OFF)) (pi_mem D) (seg_rom segs)))
  /\ sh_ok segs PE_Bx PE_SH (PE_E D) (mrestrict (w_H (pi_W D)) (pi_mem D)).
Proof.
intros D HPRE H10 HIN HWIN Hq1 Hq2 HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Hvp & Hvtl & Hvd & Hrw & Hq8 & Htext0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pe_stk as HSTK.
pose proof (pe_Ereg D 2 2%bv eq_refl ltac:(lia)) as E2.
destruct (pe_E D H10) as (E10 & E32 & E33 & E34 & Eo0 & Eo12).
destruct (alx_const segs B ARx LAWS (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) HAR)
  as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (Hg0 : YImgTop.IMG_LO <= VAL (A_OBJ 0) /\ VAL (A_OBJ 0) + 8 <= YImgTop.IMG_TOP)
  by (vm_compute; split; discriminate).
assert (Hg12 : YImgTop.IMG_LO <= VAL (A_OBJ 12) /\ VAL (A_OBJ 12) + 8 <= YImgTop.IMG_TOP)
  by (vm_compute; split; discriminate).
rewrite YImgTop.IMG_LO_val, YImgTop.IMG_TOP_val in Hg0, Hg12.
assert (Hgc : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12)) by (vm_compute; discriminate).
assert (Usp : bv_unsigned (ew (PE_E D) 2) = spZ (pi_regs D)) by (rewrite E2; reflexivity).
assert (Uq : bv_unsigned (ew (PE_E D) 10) = pi_q D) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ush : bv_unsigned (ew (PE_E D) 34) = SHADOW_OFF)
  by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Ug0 : bv_unsigned (ew (PE_E D) (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite Eo0; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (Ug12 : bv_unsigned (ew (PE_E D) (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite Eo12; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite restrict_mkst_fx.
split.
- unfold ss_pe. apply pa_entry_st_ok_full.
  + unfold PE_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pe_regions, stack_region, got_regionP, bcell_regionP, pe_qregion.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    * rewrite Ug0. split; [lia|]. split; [pose proof (pa_val_range (A_OBJ 0)); lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs (PE_E D) _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (pi_W D)) (pi_mem D) _ _ Kgot).
    * rewrite Ug12. split; [lia|]. split; [pose proof (pa_val_range (A_OBJ 12)); lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs (PE_E D) _ (VAL (A_OBJ 12)) 0 8 PE_Bx SHADOW_OFF);
        [cbn [sv_denot PE_Bx]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (pi_W D)) (pi_mem D) _ _ Kcell).
    * rewrite Uq. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val segs (PE_E D) _ (pi_q D) 0 8 (SOff 32 0) (pi_p D));
           [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Hvp.
      -- apply (chunk_ok_val segs (PE_E D) _ (pi_q D) 8 8 (SOff 33 0) (pi_text D + pi_len D));
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact Hvtl.
  + apply pairwise_disjoint_of_extents.
    unfold pe_regions, stack_region, got_regionP, bcell_regionP, pe_qregion, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, Uq, Ug0, Ug12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + split; [|split; [exact I | exact I]].
    cbn [pe_facts f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
            split; [lia|]; split; [exact Hal16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Uq; change (2 ^ 3) with 8;
            split; [lia|]; split; [exact Hq8 | lia]|].
    split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ush. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, PE_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H (pi_W D)) (pi_mem D) (PE_E D) PE_Bx 10%nat (pi_q D) 24 (pi_q D) 0 24 HRA).
  + unfold U, PE_Bx. cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* ---- WHAT THE STRETCH KEEPS. The only bytes it writes are its own frame [sp - 144, sp); everything the carried
   facts speak about is either below alloc_ceiling (the image, the statics, the blocks, the text and every shadow
   byte of it) or at or above sp (the caller's cursor struct at q). ---- *)
Definition pe_keep (W : world segs) (m m' : word -> option byte) (sp : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 144 <= a < sp) ->
     aview segs (w_H W) m' a = aview segs (w_H W) m a) /\
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m').

Lemma pe_keep_trans : forall W m1 m2 m3 sp,
  pe_keep W m1 m2 sp -> pe_keep W m2 m3 sp -> pe_keep W m1 m3 sp.
Proof.
intros W m1 m2 m3 sp [A1 G1] [A2 G2]. split.
- intros a Ha Hn. rewrite (A2 a Ha Hn). exact (A1 a Ha Hn).
- intros x Hx. exact (G2 x (G1 x Hx)).
Qed.

Lemma pe_val : forall W m m' sp a n v,
  pe_keep W m m' sp -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= sp - 144 \/ sp <= a) ->
  val_mem segs (mrestrict (w_H W) m) a n v -> val_mem segs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' sp a n v [A _] Ha Han Hout Hv.
apply (val_mem_kept segs (w_H W) (w_H W) m m' a n v); [|exact Hv].
intros k Hk. apply A; lia.
Qed.

Lemma pe_garr : forall W m m' sp a l,
  pe_keep W m m' sp -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (a + Z.of_nat (length l) <= sp - 144 \/ sp <= a) ->
  garr8 segs (mrestrict (w_H W) m) a l -> garr8 segs (mrestrict (w_H W) m') a l.
Proof.
intros W m m' sp a l HK Ha Hal Hout H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pe_val W m m' sp (a + Z.of_nat j) 1 (nth j l 0) HK); [lia | lia | lia | exact Hv].
Qed.

Lemma pe_rw : forall W m m' sp a n,
  pe_keep W m m' sp -> rd_rw segs (mrestrict (w_H W) m) a n -> rd_rw segs (mrestrict (w_H W) m') a n.
Proof.
intros W m m' sp a n [_ G] H x Hx.
exact (writable_at_grows segs (mrestrict (w_H W) m) (mrestrict (w_H W) m') x G (H x Hx)).
Qed.

(* a shadow byte of an application address is far below the stack *)
Lemma pe_shadow_in : forall x, 0 <= x -> x < YM05.alloc_ceiling -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 46.
Proof.
intros x H0 H1. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
(* FuzzStrdup.v sd_hull_low, verbatim *)
Lemma pe_hull_in : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.

Lemma pe_src : forall W m m' sp p l,
  pe_keep W m m' sp -> YM05.alloc_ceiling + 16384 <= sp ->
  src_rd W m p l -> src_rd W m' p l.
Proof.
intros W m m' sp p l HK Hsp (Hb & H4096 & Hceil & Hamr & Hra & Hhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [apply (pe_garr W m m' sp p l HK); [lia | lia | left; lia | exact Hb]|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|].
split.
- apply (range_addressable_agree (aview segs (w_H W) m) (aview segs (w_H W) m') SHADOW_OFF p
           (Z.of_nat (length l))); [|exact Hra].
  intros x Hx. unfold shadow_of_addr.
  pose proof (pe_shadow_in x ltac:(lia) ltac:(lia)) as Hb2.
  apply (proj1 HK); lia.
- intros Hn s Hs. pose proof (pe_hull_in p (Z.of_nat (length l)) s ltac:(lia) Hn ltac:(lia) Hs) as Hsb.
  rewrite (proj1 HK s ltac:(lia) ltac:(lia)). exact (Hhull Hn s Hs).
Qed.

Lemma pe_pjin : forall W m m' sp q text len p d tb,
  pe_keep W m m' sp -> sp <= q -> q + 24 <= 2 ^ 64 -> YM05.alloc_ceiling + 16384 <= sp ->
  text + len <= YM05.alloc_ceiling ->
  pj_in_okR segs (mrestrict (w_H W) m) q text len p d tb ->
  pj_in_okR segs (mrestrict (w_H W) m') q text len p d tb.
Proof.
intros W m m' sp q text len p d tb HK Hq Hq64 Hsp Htxt
  (Hvp & Hvtl & Hvd & Hrw & Hq8 & Ht0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [apply (pe_val W m m' sp q 8 p HK); [lia | lia | right; lia | exact Hvp]|].
split; [apply (pe_val W m m' sp (q + 8) 8 (text + len) HK); [lia | lia | right; lia | exact Hvtl]|].
split; [apply (pe_val W m m' sp (q + 16) 4 d HK); [lia | lia | right; lia | exact Hvd]|].
split; [exact (pe_rw W m m' sp q 24 HK Hrw)|].
split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl62|]. split; [exact Hptl|].
split; [exact Hlen|].
split; [apply (pe_garr W m m' sp text tb HK); [lia | lia | left; lia | exact Hgarr]|].
split; [exact Hdisj | exact Hd32].
Qed.

#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PSB.PS_PAImg).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PSB.PS_PAImg).
Lemma pe_ro_img : forall a, in_roP segs RLO RHI a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr];
  [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ A_prog_listing PSB.PS_PAImg a Hr)].
Qed.
Lemma pe_ro : forall W m m' sp,
  pe_keep W m m' sp -> YM05.alloc_ceiling + 16384 <= sp ->
  arodata_okP segs RLO RHI B (aview segs (w_H W) m) ->
  arodata_okP segs RLO RHI B (aview segs (w_H W) m').
Proof.
intros W m m' sp HK Hsp H a Hro Hn He.
pose proof (pa_segs_low a (pe_ro_img a Hro)) as Hl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (proj1 HK a ltac:(lia) ltac:(lia)). exact (H a Hro Hn He).
Qed.

Lemma pe_ledger : forall W m m' sp ly S Hp md Lam peak cnt fail ran most own,
  pe_keep W m m' sp -> ARx ly S Hp W m md -> YM05.alloc_ceiling + 16384 <= sp ->
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros W m m' sp ly S Hp md Lam peak cnt fail ran most own HK HAR Hsp (Hglob & Hnd & Hall & Hperm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pe_globs as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
rewrite YImgTop.IMG_TOP_val in A2, A4, A6, A8, A10, A12, A14.
pose proof (@cf_head_nonneg cp) as Hhead.
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- destruct Hglob as (V1 & V2 & V3 & V4 & V5 & (V6 & V6b) & (V7 & V7b) & Hnum).
  split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V1]|].
  split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V2]|].
  split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V3]|].
  split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V4]|].
  split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V5]|].
  split; [split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V6] | exact V6b]|].
  split; [split; [apply (pe_val W m m' sp _ _ _ HK); [lia | lia | left; lia | exact V7] | exact V7b]|].
  exact Hnum.
- rewrite Forall_forall in Hall |- *. intros ak Hak.
  destruct (Hall ak Hak) as (Hk0 & Hin & Hhp & Hal & Hv).
  split; [exact Hk0|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact Hal|].
  destruct (alx_blocks segs B ARx LAWS ly S Hp W m md _ _ HAR Hin) as (_ & H4096 & Hc & _).
  assert (Hrs : 1 <= req_size (snd ak + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (snd ak + cf_head) 0); lia).
  apply (pe_val W m m' sp (fst ak - cf_head) 8 (snd ak) HK); [lia | lia | left; lia | exact Hv].
Qed.

(* ---- the 13 saved registers, read back out of the frame's chunks ---- *)
Lemma pe_slot : forall (E : env) (m : word -> option byte) (sp0 : Z) cs lo hi wlo whi (od : Z) (rn : nat) (w : word),
  region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = sp0 ->
  ew E rn = w ->
  In (YP09.mkChunk od (CVal 8 (SOff rn 0))) cs ->
  val_mem segs m (sp0 + od) 8 (bv_unsigned w).
Proof.
intros E m sp0 cs lo hi wlo whi od rn w HR H2 Hw Hin.
apply (slot_of_region segs E m sp0 cs lo hi wlo whi od (SOff rn 0) (bv_unsigned w) HR H2 Hin).
- cbn [sv_denot]. rewrite Hw, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (u64_range w).
Qed.

(* the same at ps_saved's address PS_SP D + off: the chunk sits at off - 144 from the entry sp *)
Lemma pe_slot_at : forall (D : ps_in) (E : env) (m : word -> option byte) cs lo hi wlo whi (off od : Z) (rn : nat)
  (w : word),
  region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ (pi_regs D) ->
  od = off - 144 ->
  ew E rn = w ->
  In (YP09.mkChunk od (CVal 8 (SOff rn 0))) cs ->
  val_mem segs m (PS_SP D + off) 8 (bv_unsigned w).
Proof.
intros D E m cs lo hi wlo whi off od rn w HR H2 Hod Hw Hin.
replace (PS_SP D + off) with (spZ (pi_regs D) + od) by (unfold PS_SP; rewrite pe_frame; lia).
exact (pe_slot E m _ cs lo hi wlo whi od rn w HR H2 Hw Hin).
Qed.
Ltac pe_in := cbn [In]; repeat first [left; reflexivity | right].
(* ps_saved from the frame region's 13 chunks: (offset in the frame, chunk offset from the entry sp, register) *)
Ltac pe_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 :=
  unfold ps_saved; cbn zeta;
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 136 (-8) 1 _ HREG Usp eq_refl E1); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 128 (-16) 8 _ HREG Usp eq_refl E8); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 120 (-24) 9 _ HREG Usp eq_refl E9); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 112 (-32) 18 _ HREG Usp eq_refl E18); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 104 (-40) 19 _ HREG Usp eq_refl E19); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 96 (-48) 20 _ HREG Usp eq_refl E20); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 88 (-56) 21 _ HREG Usp eq_refl E21); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 80 (-64) 22 _ HREG Usp eq_refl E22); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 72 (-72) 23 _ HREG Usp eq_refl E23); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 64 (-80) 24 _ HREG Usp eq_refl E24); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 56 (-88) 25 _ HREG Usp eq_refl E25); pe_in|];
  split; [apply (pe_slot_at D _ _ _ _ _ _ _ 48 (-96) 26 _ HREG Usp eq_refl E26); pe_in|];
  apply (pe_slot_at D _ _ _ _ _ _ _ 40 (-104) 27 _ HREG Usp eq_refl E27); pe_in.

(* the shadow cell of an address: `srli r, x, 3; add r, r, s8` with s8 the shadow base *)
Lemma pe_shcell : forall (b : word) (v : Z),
  bv_unsigned b = SHADOW_OFF -> 0 <= v < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 v) (Z_to_bv 64 3)) b = w64 (SHADOW_OFF + v / 8).
Proof.
intros b v Hb Hv. unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v) by lia. change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd0 : 0 <= v / 8) by (apply Z.div_pos; lia).
assert (Hd1 : v / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
rewrite (Z.mod_small (v / 8)) by lia. rewrite Hb.
rewrite !Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.

(* ---- the write premise of each straight-line run: the engine writes only inside the stack region ---- *)
Ltac pe_awr D Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- pi_e D));
  [ reflexivity
  | rewrite Usp; lia
  | cbn [YP09.r_wlo stack_region]; lia
  | cbn [YP09.r_whi stack_region]; lia
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi got_regionP]; lia|];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi bcell_regionP]; lia|];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi pe_qregion]; lia|];
    apply awr_ok_nil ].

(* every byte the run may write lies in [sp - 144, sp): the three other regions have an empty write window *)
Ltac pe_inw Usp :=
  intros ?a (?r & ?Hin & ?Hr); vm_compute in Hin;
  destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; subst;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia.

(* after the second run: the frame and the growth from the entry (pe_keep), and the carried cj_kept from the entry,
   built by ONE cj_kept_exec over the union of the two runs' write windows (both inside [sp - 144, sp)) *)
Ltac pe_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ :=
  lazymatch type of HFr1 with frame_of ?E1 ?rs1 _ _ =>
  lazymatch type of HFr with frame_of ?E2 ?rs2 (mrestrict _ ?m1) (mrestrict _ ?m2) =>
  let HW1 := fresh "HW1" in let HW2 := fresh "HW2" in let KA2 := fresh "KA2" in
  assert (HW1 : forall a, in_wrange E1 rs1 a -> spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pe_inw Usp;
  assert (HW2 : forall a, in_wrange E2 rs2 a -> spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pe_inw Usp;
  assert (KA2 : pe_keep (pi_W D) m1 m2 (spZ (pi_regs D)))
    by (split; [|exact HG]; intros a Ha Hn; apply aview_eq_of; apply HFr;
        rewrite unsigned_lit_small by lia; intros Hin; exact (Hn (HW2 a Hin)));
  pose proof (pe_keep_trans _ _ _ _ _ KA1 KA2) as KA;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdF) _ =>
  assert (KJ : cj_kept SK segs B PST STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
                 (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) (pi_ly D) (pi_S D) (pi_W D) m2 mdF)
  by (apply (cj_kept_exec SK segs B PST ARx _ LAWS HSEGLOW STK_parse_string (spZ (pi_regs D))
              [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) m2 mdF
              (fun a => in_wrange E1 rs1 a \/ in_wrange E2 rs2 a) HAR);
      [ lia | lia | lia
      | intros x Hx; rewrite (HFr x (fun H => Hx (or_intror H))); exact (HFr1 x (fun H => Hx (or_introl H)))
      | intros a [Hin|Hin]; left; [pose proof (HW1 a Hin) | pose proof (HW2 a Hin)]; lia
      | first [ apply same_but_materialized_wvb_any
              | eapply same_but_materialized_trans; apply same_but_materialized_wvb_any ] ])
  end end end.

(* ---- THE GENERIC-P STRETCH: any memory invariant P with srr_inv_laws (no call, so no srr_inv_call) ---- *)
Section peP.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* the two exits of this stretch in the generic-P form (S4_PsBase.v Section gp) *)
Hypothesis HSCANP : ps_seg_scanP B ARx SK P CTX CW.
Hypothesis HRET0P : ps_seg_ret0P B ARx SK P CTX CW.

Theorem ps_entry_holdsP : ps_seg_entryP B ARx SK P CTX CW.
Proof.
unfold ps_seg_entryP. intros D HPRE HPM.
(* the runs are at wle (ps_finP, S4_PsBase's hand-off form); the scan exit is a stretch that may cross the bad
   escape's fuzz_free (ps_finP_hand), the NULL exit ends at wle (ps_finP_of_postP) *)
apply ps_finP_SRr'.
pose proof HPRE as (HFPRE & HUNIV & HCHAIN & HCLOW & HCW & HQG & HROOM & (HWR & HCNTS) & H10 & HIN & HPLT & HNTH & HWIN
  & HQ1 & HQ2 & HRA & HSRC & HHOME & HLED & HCNT & HLIVE).
pose proof HFPRE as (HPRE0 & HROD & HTOP64).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Hvp & Hvtl & Hvd & Hrw & Hq8 & Htext0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof HSRC as (_ & _ & HSRCC & _).
(* the text below the ceiling: src_rd's own bound (the batch kit PRH_Base: src_rd keeps `p + len <= alloc_ceiling`, the
   former `+ 8` slack is gone; pe_pjin needs no slack) *)
assert (HTXT : pi_text D + pi_len D <= YM05.alloc_ceiling) by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pe_stk as HSTK. pose proof pe_stk2 as HSTK2. pose proof pe_frame as HFRAME.
pose proof (@pa_segs_low _ A_prog_listing PSB.PS_PAImg) as HSEGLOW.
assert (HSPLO : YM05.alloc_ceiling + 16384 <= spZ (pi_regs D)) by lia.
pose proof (pe_Ereg D 1 1%bv eq_refl ltac:(lia)) as E1.
pose proof (pe_Ereg D 2 2%bv eq_refl ltac:(lia)) as E2.
pose proof (pe_Ereg D 3 3%bv eq_refl ltac:(lia)) as E3.
pose proof (pe_Ereg D 4 4%bv eq_refl ltac:(lia)) as E4.
pose proof (pe_Ereg D 8 8%bv eq_refl ltac:(lia)) as E8.
pose proof (pe_Ereg D 9 9%bv eq_refl ltac:(lia)) as E9.
pose proof (pe_Ereg D 18 18%bv eq_refl ltac:(lia)) as E18.
pose proof (pe_Ereg D 19 19%bv eq_refl ltac:(lia)) as E19.
pose proof (pe_Ereg D 20 20%bv eq_refl ltac:(lia)) as E20.
pose proof (pe_Ereg D 21 21%bv eq_refl ltac:(lia)) as E21.
pose proof (pe_Ereg D 22 22%bv eq_refl ltac:(lia)) as E22.
pose proof (pe_Ereg D 23 23%bv eq_refl ltac:(lia)) as E23.
pose proof (pe_Ereg D 24 24%bv eq_refl ltac:(lia)) as E24.
pose proof (pe_Ereg D 25 25%bv eq_refl ltac:(lia)) as E25.
pose proof (pe_Ereg D 26 26%bv eq_refl ltac:(lia)) as E26.
pose proof (pe_Ereg D 27 27%bv eq_refl ltac:(lia)) as E27.
destruct (pe_E D H10) as (E10 & E32 & E33 & E34 & Eo0 & Eo12).
assert (Usp : bv_unsigned (ew (PE_E D) 2) = spZ (pi_regs D)) by (rewrite E2; reflexivity).
assert (Uq : bv_unsigned (ew (PE_E D) 10) = pi_q D) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew (PE_E D) 32) = pi_p D) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Utl : bv_unsigned (ew (PE_E D) 33) = pi_text D + pi_len D)
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (Ush : bv_unsigned (ew (PE_E D) 34) = SHADOW_OFF)
  by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HEI : img_env VAL A_LIM (PE_E D)) by (unfold PE_E; apply Eimg_env).
destruct (pe_entry D HPRE0 H10 HIN HWIN HQ1 HQ2 HRA) as [HS SHOK].
pose proof (ajournal_x_init_W SK segs B PST ARx STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)]
  (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) HPRE0 HWIN) as HJ.
(* HPM : P (pi_mem D), the invariant at the entry memory; each run below carries it to its end memory *)
pose (RUN := paj_run_x_inv (SK := SK) (PL := PSB.PS_PAListing) (PI := PSB.PS_PAImg) B PST ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PSB.PS_PAListing) (PI := PSB.PS_PAImg) B PST ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PSB.PS_PAImg)).
rewrite pe_sigma. unfold cfg_at. change (w64 (BASE + PS_OFF)) with (Z_to_bv 64 (BASE + PS_OFF)).
(* ---- offsets 0..119: the frame, the 13 saves, the shadow base, the two folded shadow checks, p and text + len ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PE_Bspan; [pe_awr D Usp|].
assert (HW1 : forall a, in_wrange (PE_E D) (ss_mem ss_pe) a ->
                spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pe_inw Usp.
assert (KA1 : pe_keep (pi_W D) (pi_mem D) (ms_mem ms) (spZ (pi_regs D))).
{ split; [|exact HG].
  intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros Hin. exact (Hn (HW1 a Hin)). }
rename HFr into HFr1. clear HF HG.
psrr_branch_tok RUN BR HS SHOK PE_Bspan.
- (* the bgeu at 120 is TAKEN: p + 1 >= text + len, so nothing is left after the quote *)
  assert (HGE : pi_text D + pi_len D <= pi_p D + 1).
  { rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite !U_SOff, Up, Utl in Hc. rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
  assert (HNONE : PjGrammar.scan (ps_x D) = None).
  { unfold ps_x, rest_atR. rewrite skipn_all2 by lia. reflexivity. }
  (* the grammar's trace of a refused string is empty, so the call holds no bytes *)
  assert (HTR : PRH_Charge.prhPs_gtrace (ps_x D) = []).
  { unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. rewrite HNONE. reflexivity. }
  (* offsets 120..1283: the taken branch, straight to the NULL return *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PE_Bspan (PS_OFF + 1284); [pe_awr D Usp|].
  pe_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  pose proof (st_ok_region_nth segs (PE_E D) _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HREG.
  cbn [ms_mem restrict] in HREG.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    rewrite (pe_pc_exit PS_RET0 z ltac:(vm_compute; reflexivity)) end.
  apply ps_finP_of_postP. eapply (HRET0P D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D)); [exact HPRE|].
  split; [|split; [|split; [|split; [|split]]]].
  + exists 0, []. split; [apply ps_wb_nil|]. split; [exact HJ|].
    split; [exact KJ|].
    split.
    { pe_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. }
    split; [exact (pe_src (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_text D) (pi_tb D) KA HSPLO HSRC)|].
    split; [exact HHOME | exact HPM].
  + split; [rewrite R3; exact E3 | rewrite R4; exact E4].
  + rewrite R2, Usp. unfold w64, PS_SP. rewrite HFRAME. f_equal; lia.
  + exact HROOM.
  + rewrite HTR. unfold PRH_Charge.prh_held.
    cbn [PjGrammar.held PjGrammar.calls length Z.of_nat]. lia.
  + unfold ps_Qres. rewrite HNONE.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (pe_ledger (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_ly D) (pi_S D) (pi_Hp D)
                     (pi_md D) _ _ _ _ _ _ _ KA HAR HSPLO HLED)|].
    split; [exact (pe_pjin (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_q D) (pi_text D) (pi_len D)
             (pi_p D) (pi_d D) (pi_tb D) KA HQ1 ltac:(lia) HSPLO HTXT HIN)|].
    (* the stretch allocates nothing: the astate is the entry's, and the transfer is the identity *)
    apply ps_rpos_nil.
- (* the bgeu at 120 is NOT taken: p + 1 < text + len, fall into the scan head with x = p + 1 *)
  assert (HLT : pi_p D + 1 < pi_text D + pi_len D).
  { rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    rewrite !U_SOff, Up, Utl in Hc. rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
  (* offsets 120..131: li a2, 34 and mv a0, s4 *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PE_Bspan (PS_OFF + 132); [pe_awr D Usp|].
  pe_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
  prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12. prreg HS (20%bv : bv 5) R20.
  prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
  pose proof (st_ok_region_nth segs (PE_E D) _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HREG.
  cbn [ms_mem restrict] in HREG.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    rewrite (pe_pc_exit PS_SCAN z ltac:(vm_compute; reflexivity)) end.
  apply ps_finP_hand. eapply (HSCANP D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) _ _ _ (pi_p D + 1)); [exact HPRE|].
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  + split; [exact HJ|]. split; [exact KJ|].
    split.
    { pe_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. }
    split; [exact (pe_src (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_text D) (pi_tb D) KA HSPLO HSRC)|].
    split; [exact HHOME | exact HPM].
  + split; [rewrite R24; rewrite E34; reflexivity|].
    split; [rewrite R23, E10; rewrite (pe_shcell (ew (PE_E D) 34) (pi_q D) Ush ltac:(lia)); reflexivity|].
    rewrite R25, Uq.
    rewrite (pe_shcell (ew (PE_E D) 34) (pi_q D + 8) Ush ltac:(lia)). reflexivity.
  + split; [rewrite R3; exact E3 | rewrite R4; exact E4].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + exact (pe_ledger (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_ly D) (pi_S D) (pi_Hp D)
             (pi_md D) _ _ _ _ _ _ _ KA HAR HSPLO HLED).
  + exact (pe_pjin (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) (pi_q D) (pi_text D) (pi_len D)
             (pi_p D) (pi_d D) (pi_tb D) KA HQ1 ltac:(lia) HSPLO HTXT HIN).
  + exact (pe_ro (pi_W D) (pi_mem D) (ms_mem ms0) (spZ (pi_regs D)) KA HSPLO HROD).
  + split; [rewrite R2, Usp; unfold w64, PS_SP; rewrite HFRAME; f_equal; lia|].
    split; [rewrite R10, Up; reflexivity|].
    split; [rewrite R11, E33; reflexivity|].
    split; [rewrite R12; reflexivity|].
    split; [rewrite R8, E10; reflexivity|].
    split; [rewrite R9, E10; rewrite unsigned_lit_small by lia; reflexivity|].
    split; [rewrite R20, Up; reflexivity|].
    split; [lia|].
    replace (pi_p D + 1 - (pi_p D + 1)) with 0 by lia. cbn [Z.to_nat].
    unfold ps_x. destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (pi_p D + 1))) eqn:Es;
      cbn [option_map]; [rewrite Nat.add_0_r; reflexivity | reflexivity].
Qed.
End peP.

(* ---- the stable statement, unchanged: the P := (fun _ => True) instance of ps_entry_holdsP ---- *)
Theorem ps_entry_holds : ps_seg_entry B ARx SK CTX CW.
Proof.
apply (proj1 (ps_seg_entry_of_True B ARx SK CTX CW)).
exact (ps_entry_holdsP (fun _ => True) srr_inv_laws_True
  (proj2 (ps_seg_scan_of_True B ARx SK CTX CW) HSCAN) (proj2 (ps_seg_ret0_of_True B ARx SK CTX CW) HRET0)).
Qed.

End pe.
