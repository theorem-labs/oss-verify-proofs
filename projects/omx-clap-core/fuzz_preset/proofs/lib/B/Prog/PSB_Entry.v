(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 494 of its 580 lines of code are new or changed and 2700 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan): the ENTRY stretch of the walk, offsets 0..147 of
   parse_string (DERIVED), from the entry to the scan loop head PSB_SCAN (148) or the NULL return PSB_RET0 (1256).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). The function proof is psb_holds (PSB_Top.v); the lane's reuse
   search is the record file r24-index.txt (sha256 e7c12b08eeb1; internal record) (donor: none; templates T1-T3).
   The contract is PSB_Base.v: this file proves psb_seg_entryP, with psb_seg_scanP and psb_seg_ret0P (the two exits)
   as the premises of its theorem psb_entry_holdsP, over a GENERIC memory invariant P (a Theorem Labs lane 12:18Z / 12:22Z:
   an SRr post is OPAQUE once Qed, so an end-state invariant must be in the segment's statement). The old statement
   psb_entry_holds is its corollary at P := fun _ => True (psb_seg_*_of_True, srr_inv_laws_True); it did not move.
   The kit's text is tparse_string_specX (lib/A/PRH_FnReader.v f1ae32e3b2cd at the kit's cut 7cdbb61b5fa0) at image B's instances
   (prh_img_B, B_prog_listing, PL_prog_B, PI_prog_B), through this row's PS_Gen.v / PSB_Base.v (generic-P from base
   3d53a181c75, a working branch).
   THE INVARIANT: P stays ABSTRACT here (the top instantiates it once as ps_mn D). The stretch makes no call, so it
   takes srr_inv_laws segs P only (no srr_inv_call): HPM : P (pi_mem D) is psb_seg_entryP's premise, then each of the
   two straight-line runs is YC1fPx.v's invariant twin (paj_run_x_m_inv / paj_run_to_x_m_inv at P with PLAW,
   tactics paj_run_tok_x_inv / paj_run_to_tok_x_inv), which hands P of the run's end memory; the branch at 136 keeps
   the machine state. Both exits (PSB_RET0 with ps_at_ret0P, PSB_SCAN with psb_at_scanP) take HPM as ps_carryP's last
   conjunct.
   FILE SET: every non-lane file as the kit's cut carries it (YCbqG.v 219748197d6b, B Listing_prog.v c97cc46b3e13,
   PRW_StepKit.v 0df3991c13f4, YSRrMemnorm.v 5ffa8525936b, YAkMemnorm.v 96c72061b4d4); earlier engine and YCbqG.v from
   a working branch 63997a07aa6, listing a working branch 7c8ffeba5035, PRW_StepKit walk-S7B b77dc99e0b5, YSRrMemnorm.v
   a1c1ece77b14. Reading aid: WalkS4's image-A entry stretch (a working branch, lib/A/Prog/S4_PsEntry.v),
   same logic over image A's registers; nothing is Required from it.
   THE INSTRUCTIONS (the neutral listing of the rebuilt image B,
   the neutral listing parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record)):
     0        addi sp,sp,-144                          the frame (LENGTH: PS_FRAME, checked by pse_frame)
     4..52    the 13 saves ra 136 .. s11 40           -> ps_saved
     56       mv s0,a0                                 s0 = q
     60,64    andi a0,a0,7; bnez -> unimp              UBSan alignment of q: NOT taken, the engine folds it from the
                                                       fact q mod 8 = 0 (pj_in_okR)
     68..76   auipc; ld a0 (the GOT slot A_OBJ 0); ld s7,0(a0)   s7 = the shadow base (got_regionP, bcell_regionP)
     80..92   srli s6,s0,3; add s6,s6,s7; lbu; bnez -> errpath   NOT taken: the shadow entry mkSHE 10 0 24 (ps_pre's
                                                       range_addressable q 24) folds the load to 0
     96,100   ld s4,0(s0); addi s4,s4,1                s4 = p + 1 (pj_in_okR, the q region's chunk at 0)
     104,108  li a0,2; bltu s4,a0 -> unimp             UBSan pointer wrap: NOT taken, folded from the fact 1 <= p
     112..128 addi s1,s0,8; the same shadow check for q + 8 (s8 = its shadow cell): NOT taken
     132      ld a1,0(s1)                              a1 = text + len (pj_in_okR, the chunk at 8)
     136      bgeu s4,a1 -> 1256                       TAKEN: nothing is left after the quote, so
                                                       PjGrammar.scan (ps_x D) = None and ps_Qres' None arm holds
     140,144  li a2,34; mv a0,s4                       fall into PSB_SCAN at 148 with x = p + 1
   The journal starts at the widened window (STK_parse_string + e, sp + e) with YCbqGcallW.v's ajournal_x_init_W;
   the carried cj_kept is ONE cj_kept_exec over the union of the two straight-line runs' write windows (both inside
   the frame). The stretch allocates nothing and makes no call: the allocator state, the heap set and the world are
   the entry's throughout.
   Numerals: the cut offsets 148 / 1256 are PSB_Base's PSB_SCAN / PSB_RET0 (by name); 144 (LENGTH: parse_string's
   frame, = PS_FRAME by pse_frame), 136 .. 40 and -8 .. -104 (DERIVED: the save slots in the frame and the same slots
   from the entry sp), 16384 (LENGTH: a lower bound of STK_parse_string, by computation), 24 / 16 / 8 (LENGTH: the
   cursor struct, its two read words, a word), register numbers 1 .. 27 (WORD), atom indices 32 / 33 / 34 (DERIVED:
   the engine's numbering of the extra atoms SHADOW_OFF, p, text + len) and 2 / 10 (the stack and q atoms), 34 (WORD:
   the double-quote byte), 3 (WORD: the shift of a shadow cell), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 62 / 2 ^ 64 (LENGTH:
   the shadow span, the stack band, pj_in_okR's text bound, machine words), 4 / 3 / 0 (LENGTH: log2 alignments).
   No ADDRESS: every address is a pa_val / pa_sigma of lib/B/PAImg_prog.v or a PSB_Base name, computed where compared. *)
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
(* YK06 is NOT imported: its plain constant alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcallW.
(* the runner's invariant twins (paj_run_x_m_inv, paj_run_to_x_m_inv, their tactics) are YC1fPx's; override-free *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* lia reads a division as an atom; the division bounds are supplied by Z.div_pos / Z.div_lt_upper_bound *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry symbolic state. Atom indices are the engine's numbering (DERIVED): 0..31 the registers, 32 = the
   shadow base SHADOW_OFF, 33 = p, 34 = text + len; A_OBJ 0 the GOT slot, A_OBJ 12 the shadow-base cell. ---- *)
Definition PSE_Bx : sv := SOff 32 0.
Definition PSE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the ONE shadow entry: ps_pre's range_addressable over the caller's 24-byte cursor struct at q *)
Definition PSE_SH : list shent := [mkSHE 10 0 24].
(* the cursor struct's two words the stretch reads (p at q, text + len at q + 8), read-only *)
Definition pse_qregion : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition pse_regions : smem := [stack_region 144; got_regionP; bcell_regionP 32; pse_qregion].
(* the facts: sp 16-aligned in the stack band; q 8-aligned in it (the UBSan alignment check folds); the shadow
   base; 1 <= p (the UBSan wrap check of p + 1 folds) and 1 <= text + len, both below pj_in_okR's 2 ^ 62 *)
Definition pse_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 (2 ^ 62) 0); (34%nat, mkAF 1 (2 ^ 62) 0)] [] [].
Definition ss_pse : sstate := mkSS PSB_OFF sr_atoms pse_regions None pse_facts.

Section pse. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* the image instances of record: PSB_Base.v's own, never left to inference *)
#[local] Existing Instance PSB_PrhImg.
#[local] Existing Instance PSB_PAListing | 0.
#[local] Existing Instance PSB_PAImg | 0.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation VAL := (@pa_val _ B_prog_listing PSB_PAImg).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PSB_PAImg).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PSB_PAImg).
#[local] Notation ps_in := (ps_in (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_SP := (PS_SP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PST := (prh_pst (PI := PSB_PrhImg)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* ---- the Section hypotheses of the brief (the internal file STRETCH-BRIEF.md), verbatim; the stretch makes no call ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).

Definition pse_extra (D : ps_in) : list word := [w64 SHADOW_OFF; w64 (pi_p D); w64 (pi_text D + pi_len D)].
Definition PSE_E (D : ps_in) : env := @Eimg _ B_prog_listing PSB_PAImg (Ereg (pi_regs D) (pse_extra D)).

(* ---- the image numbers this stretch needs, all by computation on the generated listing / PrhImg ---- *)
Lemma pse_stk : 144 <= STK_parse_string (PI := PSB_PrhImg).
Proof. vm_compute. discriminate. Qed.
Lemma pse_stk2 : 16384 <= STK_parse_string (PI := PSB_PrhImg).
Proof. vm_compute. discriminate. Qed.
Lemma pse_frame : PS_FRAME (PI := PSB_PrhImg) = 144.
Proof. vm_compute. reflexivity. Qed.
(* the two exit pcs, in the listing's own offsets *)
Lemma pse_pc_exit : forall off z, z = PSB_OFF + off -> BASE + z = psb_pc off.
Proof. intros off z ->. unfold psb_pc. rewrite Z.add_assoc. reflexivity. Qed.
(* the two image words the stretch reads (the GOT slot and the shadow-base cell) lie below the stack band *)
Lemma pse_objs : 0 <= VAL (A_OBJ 0) /\ VAL (A_OBJ 0) + 8 <= 2 ^ 46 /\ 0 <= VAL (A_OBJ 12) /\ VAL (A_OBJ 12) + 8 <= 2 ^ 46.
Proof. repeat split; vm_compute; discriminate. Qed.
(* the program's statics lie in the image (PST_ok), so below kLowMemEnd *)
Lemma pse_pst_k : forall i g gz k, nth_error PST i = Some (g, gz) -> 0 <= k < gz -> 0 <= g + k < kLowMemEnd.
Proof.
intros i g gz k Hi Hk.
assert (Hx : Exists (in_zr (g + k)) PST).
{ apply Exists_exists. exists (g, gz). split; [exact (nth_error_In _ _ Hi) | unfold in_zr; cbn [fst snd]; lia]. }
exact (@pa_segs_low _ B_prog_listing PSB_PAImg (g + k) (proj1 (PST_ok (g + k) Hx))).
Qed.

(* ---- the environment at the entry ---- *)
Lemma pse_Ereg : forall (D : ps_in) (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (PSE_E D) n = getr (pi_regs D) r.
Proof.
intros D n r Hn Hlt. unfold PSE_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat (pi_regs D) _ n r Hn).
Qed.
Lemma pse_E : forall D, getr (pi_regs D) 10 = w64 (pi_q D) ->
  ew (PSE_E D) 10 = Z_to_bv 64 (pi_q D) /\
  ew (PSE_E D) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (PSE_E D) 33 = Z_to_bv 64 (pi_p D) /\
  ew (PSE_E D) 34 = Z_to_bv 64 (pi_text D + pi_len D) /\
  ew (PSE_E D) (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) /\
  ew (PSE_E D) (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)).
Proof.
intros D H10. unfold PSE_E.
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
Lemma pse_entry : forall (D : ps_in),
  afn_pre_x segs B ARx STK_parse_string (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) ->
  getr (pi_regs D) 10 = w64 (pi_q D) ->
  pj_in_okR segs (mrestrict (w_H (pi_W D)) (pi_mem D)) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
  fwin (pi_ly D) (pi_W D) (pi_regs D) (pi_mem D) (pi_e D) ->
  spZ (pi_regs D) <= pi_q D -> pi_q D + 24 <= spZ (pi_regs D) + pi_e D ->
  range_addressable (aview segs (w_H (pi_W D)) (pi_mem D)) SHADOW_OFF (pi_q D) 24 ->
  st_ok_pi segs VAL (PSE_E D) ss_pse
    (restrict (w_H (pi_W D)) (mkst (pi_regs D) (Z_to_bv 64 (BASE + PSB_OFF)) (pi_mem D) (seg_rom segs)))
  /\ sh_ok segs PSE_Bx PSE_SH (PSE_E D) (mrestrict (w_H (pi_W D)) (pi_mem D)).
Proof.
intros D HPRE H10 HIN HWIN Hq1 Hq2 HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Hvp & Hvtl & Hvd & Hrw & Hq8 & Htext0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pse_stk as HSTK. pose proof pse_objs as (Hg0a & Hg0b & Hg12a & Hg12b).
pose proof (pse_Ereg D 2 2%bv eq_refl ltac:(lia)) as E2.
destruct (pse_E D H10) as (E10 & E32 & E33 & E34 & Eo0 & Eo12).
destruct (alx_const segs B ARx LAWS (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) HAR)
  as (Kcell0 & _ & Kgot0 & _).
assert (Kgot : rdword (aview segs (w_H (pi_W D)) (pi_mem D)) (VAL (A_OBJ 0)) = Some (VAL (A_OBJ 12))).
{ rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot0. exact Kgot0. }
assert (Kcell : rdword (aview segs (w_H (pi_W D)) (pi_mem D)) (VAL (A_OBJ 12)) = Some SHADOW_OFF).
{ rewrite (pal_cell B TL) in Kcell0. exact Kcell0. }
assert (Hgc : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 0)) by exact (pal_got_cell B TL).
assert (Usp : bv_unsigned (ew (PSE_E D) 2) = spZ (pi_regs D)) by (rewrite E2; reflexivity).
assert (Uq : bv_unsigned (ew (PSE_E D) 10) = pi_q D) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ush : bv_unsigned (ew (PSE_E D) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Up : bv_unsigned (ew (PSE_E D) 33) = pi_p D) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Utl : bv_unsigned (ew (PSE_E D) 34) = pi_text D + pi_len D)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (Ug0 : bv_unsigned (ew (PSE_E D) (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite Eo0; apply unsigned_lit_small; pose proof (@pa_val_range _ B_prog_listing PSB_PAImg (A_OBJ 0)); lia).
assert (Ug12 : bv_unsigned (ew (PSE_E D) (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite Eo12; apply unsigned_lit_small; pose proof (@pa_val_range _ B_prog_listing PSB_PAImg (A_OBJ 12)); lia).
rewrite restrict_mkst_fx.
split.
- unfold ss_pse. apply pa_entry_st_ok_full.
  + unfold PSE_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pse_regions, stack_region, got_regionP, bcell_regionP, pse_qregion.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
    * rewrite Ug0. split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs (PSE_E D) _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (@pa_val_range _ B_prog_listing PSB_PAImg (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (pi_W D)) (pi_mem D) _ _ Kgot).
    * rewrite Ug12. split; [lia|]. split; [lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs (PSE_E D) _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H (pi_W D)) (pi_mem D) _ _ Kcell).
    * rewrite Uq. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val segs (PSE_E D) _ (pi_q D) 0 8 (SOff 33 0) (pi_p D));
           [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Hvp.
      -- apply (chunk_ok_val segs (PSE_E D) _ (pi_q D) 8 8 (SOff 34 0) (pi_text D + pi_len D));
           [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact Hvtl.
  + apply pairwise_disjoint_of_extents.
    unfold pse_regions, stack_region, got_regionP, bcell_regionP, pse_qregion, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, Uq, Ug0, Ug12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + split; [|split; [exact I | exact I]].
    cbn [pse_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uq, Ush, Up, Utl. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hal16 | exact Hq8 | lia].
- unfold sh_ok, PSE_SH. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H (pi_W D)) (pi_mem D) (PSE_E D) PSE_Bx 10%nat (pi_q D) 24 (pi_q D) 0 24 HRA).
  + unfold U, PSE_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
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
Definition pse_keep (W : world segs) (m m' : word -> option byte) (sp : Z) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 144 <= a < sp) ->
     aview segs (w_H W) m' a = aview segs (w_H W) m a) /\
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m').

Lemma pse_keep_trans : forall W m1 m2 m3 sp,
  pse_keep W m1 m2 sp -> pse_keep W m2 m3 sp -> pse_keep W m1 m3 sp.
Proof.
intros W m1 m2 m3 sp [A1 G1] [A2 G2]. split.
- intros a Ha Hn. rewrite (A2 a Ha Hn). exact (A1 a Ha Hn).
- intros x Hx. exact (G2 x (G1 x Hx)).
Qed.

(* a value the stretch does not touch, byte by byte *)
Lemma pse_valk : forall W m m' sp a n v,
  pse_keep W m m' sp ->
  (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ (sp - 144 <= a + k < sp)) ->
  val_mem segs (mrestrict (w_H W) m) a n v -> val_mem segs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' sp a n v [A _] Hk Hv.
apply (val_mem_kept segs (w_H W) (w_H W) m m' a n v); [|exact Hv].
intros k Hk'. destruct (Hk k Hk') as [H1 H2]. exact (A (a + k) H1 H2).
Qed.

(* a value wholly below the frame or at / above sp *)
Lemma pse_val : forall W m m' sp a n v,
  pse_keep W m m' sp -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= sp - 144 \/ sp <= a) ->
  val_mem segs (mrestrict (w_H W) m) a n v -> val_mem segs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' sp a n v HK Ha Han Hout. apply (pse_valk W m m' sp a n v HK). intros k Hk. lia.
Qed.

Lemma pse_garr : forall W m m' sp a l,
  pse_keep W m m' sp -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  (a + Z.of_nat (length l) <= sp - 144 \/ sp <= a) ->
  garr8 segs (mrestrict (w_H W) m) a l -> garr8 segs (mrestrict (w_H W) m') a l.
Proof.
intros W m m' sp a l HK Ha Hal Hout H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pse_val W m m' sp (a + Z.of_nat j) 1 (nth j l 0) HK); [lia | lia | lia | exact Hv].
Qed.

Lemma pse_rw : forall W m m' sp a n,
  pse_keep W m m' sp -> rd_rw segs (mrestrict (w_H W) m) a n -> rd_rw segs (mrestrict (w_H W) m') a n.
Proof.
intros W m m' sp a n [_ G] H x Hx.
exact (writable_at_grows segs (mrestrict (w_H W) m) (mrestrict (w_H W) m') x G (H x Hx)).
Qed.

(* a shadow byte of an application address is far below the stack *)
Lemma pse_shadow_in : forall x, 0 <= x -> x < YM05.alloc_ceiling -> 0 <= SHADOW_OFF + x / 8 < 2 ^ 46.
Proof.
intros x H0 H1. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
(* the shadow hull of an application range is far below the stack *)
Lemma pse_hull_in : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.

Lemma pse_src : forall W m m' sp p l,
  pse_keep W m m' sp -> YM05.alloc_ceiling + 16384 <= sp ->
  src_rd W m p l -> src_rd W m' p l.
Proof.
intros W m m' sp p l HK Hsp (Hb & H4096 & Hceil & Hamr & Hra & Hhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [apply (pse_garr W m m' sp p l HK); [lia | lia | left; lia | exact Hb]|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hamr|].
split.
- apply (range_addressable_agree (aview segs (w_H W) m) (aview segs (w_H W) m') SHADOW_OFF p
           (Z.of_nat (length l))); [|exact Hra].
  intros x Hx. unfold shadow_of_addr.
  pose proof (pse_shadow_in x ltac:(lia) ltac:(lia)) as Hb2.
  apply (proj1 HK); lia.
- intros Hn s Hs. pose proof (pse_hull_in p (Z.of_nat (length l)) s ltac:(lia) Hn ltac:(lia) Hs) as Hsb.
  rewrite (proj1 HK s ltac:(lia) ltac:(lia)). exact (Hhull Hn s Hs).
Qed.

Lemma pse_pjin : forall W m m' sp q text len p d tb,
  pse_keep W m m' sp -> sp <= q -> q + 24 <= 2 ^ 64 -> YM05.alloc_ceiling + 16384 <= sp ->
  text + len <= YM05.alloc_ceiling ->
  pj_in_okR segs (mrestrict (w_H W) m) q text len p d tb ->
  pj_in_okR segs (mrestrict (w_H W) m') q text len p d tb.
Proof.
intros W m m' sp q text len p d tb HK Hq Hq64 Hsp Htxt
  (Hvp & Hvtl & Hvd & Hrw & Hq8 & Ht0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [apply (pse_val W m m' sp q 8 p HK); [lia | lia | right; lia | exact Hvp]|].
split; [apply (pse_val W m m' sp (q + 8) 8 (text + len) HK); [lia | lia | right; lia | exact Hvtl]|].
split; [apply (pse_val W m m' sp (q + 16) 4 d HK); [lia | lia | right; lia | exact Hvd]|].
split; [exact (pse_rw W m m' sp q 24 HK Hrw)|].
split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl62|]. split; [exact Hptl|].
split; [exact Hlen|].
split; [apply (pse_garr W m m' sp text tb HK); [lia | lia | left; lia | exact Hgarr]|].
split; [exact Hdisj | exact Hd32].
Qed.

Lemma pse_ro_img : forall a, in_roP segs RLO RHI a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr];
  [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ B_prog_listing PSB_PAImg a Hr)].
Qed.
Lemma pse_ro : forall W m m' sp,
  pse_keep W m m' sp -> YM05.alloc_ceiling + 16384 <= sp ->
  arodata_okP segs RLO RHI B (aview segs (w_H W) m) ->
  arodata_okP segs RLO RHI B (aview segs (w_H W) m').
Proof.
intros W m m' sp HK Hsp H a Hro Hn He.
pose proof (@pa_segs_low _ B_prog_listing PSB_PAImg a (pse_ro_img a Hro)) as Hl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (proj1 HK a ltac:(lia) ltac:(lia)). exact (H a Hro Hn He).
Qed.

Lemma pse_ledger : forall W m m' sp ly S Hp md Lam peak cnt fail ran most own,
  pse_keep W m m' sp -> ARx ly S Hp W m md -> YM05.alloc_ceiling + 16384 <= sp ->
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own ->
  prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros W m m' sp ly S Hp md Lam peak cnt fail ran most own HK HAR Hsp (Hglob & Hnd & Hall & Hperm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hhead.
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- destruct Hglob as (V1 & V2 & V3 & V4 & V5 & (V6 & V6r) & (V7 & V7r) & Hnum).
  split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V1];
          intros k Hk; pose proof (pse_pst_k 0 _ _ k eq_refl Hk); lia|].
  split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V2];
          intros k Hk; pose proof (pse_pst_k 1 _ _ k eq_refl Hk); lia|].
  split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V3];
          intros k Hk; pose proof (pse_pst_k 2 _ _ k eq_refl Hk); lia|].
  split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V4];
          intros k Hk; pose proof (pse_pst_k 3 _ _ k eq_refl Hk); lia|].
  split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V5];
          intros k Hk; pose proof (pse_pst_k 4 _ _ k eq_refl Hk); lia|].
  (* the #102 cells g_most / g_own_ran_out (the sixth and seventh prh_pst cells) *)
  split; [split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V6];
          intros k Hk; pose proof (pse_pst_k 5 _ _ k eq_refl Hk); lia | exact V6r]|].
  split; [split; [apply (pse_valk W m m' sp _ _ _ HK); [|exact V7];
          intros k Hk; pose proof (pse_pst_k 6 _ _ k eq_refl Hk); lia | exact V7r]|].
  exact Hnum.
- rewrite Forall_forall in Hall |- *. intros ak Hak.
  destruct (Hall ak Hak) as (Hk0 & Hin & Hhp & Hal & Hv).
  split; [exact Hk0|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact Hal|].
  destruct (alx_blocks segs B ARx LAWS ly S Hp W m md _ _ HAR Hin) as (_ & H4096 & Hc & _).
  assert (Hrs : 1 <= req_size (snd ak + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (snd ak + cf_head) 0); lia).
  apply (pse_val W m m' sp (fst ak - cf_head) 8 (snd ak) HK); [lia | lia | left; lia | exact Hv].
Qed.

(* ---- the 13 saved registers, read back out of the frame's chunks ---- *)
Lemma pse_slot : forall (E : env) (m : word -> option byte) (sp0 : Z) cs lo hi wlo whi (od : Z) (rn : nat) (w : word),
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
Lemma pse_slot_at : forall (D : ps_in) (E : env) (m : word -> option byte) cs lo hi wlo whi (off od : Z) (rn : nat)
  (w : word),
  region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = spZ (pi_regs D) ->
  od = off - 144 ->
  ew E rn = w ->
  In (YP09.mkChunk od (CVal 8 (SOff rn 0))) cs ->
  val_mem segs m (PS_SP D + off) 8 (bv_unsigned w).
Proof.
intros D E m cs lo hi wlo whi off od rn w HR H2 Hod Hw Hin.
replace (PS_SP D + off) with (spZ (pi_regs D) + od) by (unfold PS_Gen.PS_SP; rewrite pse_frame; lia).
exact (pse_slot E m _ cs lo hi wlo whi od rn w HR H2 Hw Hin).
Qed.
Ltac pse_in := cbn [In]; repeat first [left; reflexivity | right].
(* ps_saved from the frame region's 13 chunks: (offset in the frame, chunk offset from the entry sp, register) *)
Ltac pse_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 :=
  unfold ps_saved; cbn zeta;
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 136 (-8) 1 _ HREG Usp eq_refl E1); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 128 (-16) 8 _ HREG Usp eq_refl E8); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 120 (-24) 9 _ HREG Usp eq_refl E9); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 112 (-32) 18 _ HREG Usp eq_refl E18); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 104 (-40) 19 _ HREG Usp eq_refl E19); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 96 (-48) 20 _ HREG Usp eq_refl E20); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 88 (-56) 21 _ HREG Usp eq_refl E21); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 80 (-64) 22 _ HREG Usp eq_refl E22); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 72 (-72) 23 _ HREG Usp eq_refl E23); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 64 (-80) 24 _ HREG Usp eq_refl E24); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 56 (-88) 25 _ HREG Usp eq_refl E25); pse_in|];
  split; [apply (pse_slot_at D _ _ _ _ _ _ _ 48 (-96) 26 _ HREG Usp eq_refl E26); pse_in|];
  apply (pse_slot_at D _ _ _ _ _ _ _ 40 (-104) 27 _ HREG Usp eq_refl E27); pse_in.

(* the shadow cell of an address: `srli r, x, 3; add r, r, s7` with s7 the shadow base *)
Lemma pse_shcell : forall (b : word) (v : Z),
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

(* ---- the (mixed) write premise of each straight-line run: the engine writes only inside the stack region, which
   lies in the widened window [sp - STK_parse_string, sp + e) ---- *)
Ltac pse_wr Usp HSTK He0 :=
  intros ?a (?r & ?Hin & ?Hr); left; left; vm_compute in Hin;
  destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; subst;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia.

(* every byte the run may write lies in [sp - 144, sp): the three other regions have an empty write window *)
Ltac pse_inw Usp :=
  intros ?a (?r & ?Hin & ?Hr); vm_compute in Hin;
  destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; subst;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia.

(* after the second run: the frame and the growth from the entry (pse_keep), and the carried cj_kept from the
   entry, built by ONE cj_kept_exec over the union of the two runs' write windows (both inside [sp - 144, sp)) *)
Ltac pse_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ :=
  lazymatch type of HFr1 with frame_of ?E1 ?rs1 _ _ =>
  lazymatch type of HFr with frame_of ?E2 ?rs2 (mrestrict _ ?m1) (mrestrict _ ?m2) =>
  let HW1 := fresh "HW1" in let HW2 := fresh "HW2" in let KA2 := fresh "KA2" in
  assert (HW1 : forall a, in_wrange E1 rs1 a -> spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pse_inw Usp;
  assert (HW2 : forall a, in_wrange E2 rs2 a -> spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pse_inw Usp;
  assert (KA2 : pse_keep (pi_W D) m1 m2 (spZ (pi_regs D)))
    by (split; [|exact HG]; intros a Ha Hn; apply aview_eq_of; apply HFr;
        rewrite unsigned_lit_small by lia; intros Hin; exact (Hn (HW2 a Hin)));
  pose proof (pse_keep_trans _ _ _ _ _ KA1 KA2) as KA;
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdF) _ =>
  assert (KJ : cj_kept (SK := SK) segs B PST STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
                 (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) (pi_ly D) (pi_S D) (pi_W D) m2 mdF)
  by (apply (cj_kept_exec (SK := SK) segs B PST ARx LAWS HSEGLOW STK_parse_string (spZ (pi_regs D))
              [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) m2 mdF
              (fun a => in_wrange E1 rs1 a \/ in_wrange E2 rs2 a) HAR);
      [ lia | lia | lia
      | intros x Hx; rewrite (HFr x (fun H => Hx (or_intror H))); exact (HFr1 x (fun H => Hx (or_introl H)))
      | intros a [Hin|Hin]; left; [pose proof (HW1 a Hin) | pose proof (HW2 a Hin)]; lia
      | first [ apply same_but_materialized_wvb_any
              | eapply same_but_materialized_trans; apply same_but_materialized_wvb_any ] ])
  end end end.

(* ==== THE ENTRY STRETCH: from ps_pre at parse_string's entry to its two exits, whose stretches are the premises,
   over a generic memory invariant P (no call: srr_inv_laws only) ==== *)
Theorem psb_entry_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P ->
  psb_seg_scanP B ARx SK CTX CW P -> psb_seg_ret0P B ARx SK CTX CW P -> psb_seg_entryP B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW HSCAN HRET0.
unfold psb_seg_entryP. intros D HPRE HPM.
(* the runs are at wle (PS_Gen's hand-off form ps_finP); the scan exit is a stretch that may cross the bad escape's
   fuzz_free (ps_finP_hand), the NULL exit ends at wle (ps_finP_of_postP) *)
apply ps_finP_SRr'.
pose proof HPRE as (HFPRE & HUNIV & HCHAIN & HCUR & HCLOW & HQG & HROOM & HPKSEC & HPK24 & H10 & HIN & HPLT & HNTH & HWIN
  & HQ1 & HQ2 & HRA & HSRC & HHOME & HLED & HCNT & HLIVE).
pose proof HFPRE as (HPRE0 & HROD & HTOP64).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Hvp & Hvtl & Hvd & Hrw & Hq8 & Htext0 & Htl62 & Hptl & Hlen & Hgarr & Hdisj & Hd32).
pose proof HSRC as (_ & _ & HSRCC & _).
(* the text's ceiling (src_rd at the kit's cut, PRH_Base.v :1660: no `+ 8`, K0-SRC-CEIL) *)
assert (HTXT : pi_text D + pi_len D <= YM05.alloc_ceiling) by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pse_stk as HSTK. pose proof pse_stk2 as HSTK2. pose proof pse_frame as HFRAME.
pose proof (@pa_segs_low _ B_prog_listing PSB_PAImg) as HSEGLOW.
assert (HSPLO : YM05.alloc_ceiling + 16384 <= spZ (pi_regs D)) by lia.
pose proof (pse_Ereg D 1 1%bv eq_refl ltac:(lia)) as E1.
pose proof (pse_Ereg D 2 2%bv eq_refl ltac:(lia)) as E2.
pose proof (pse_Ereg D 3 3%bv eq_refl ltac:(lia)) as E3.
pose proof (pse_Ereg D 4 4%bv eq_refl ltac:(lia)) as E4.
pose proof (pse_Ereg D 8 8%bv eq_refl ltac:(lia)) as E8.
pose proof (pse_Ereg D 9 9%bv eq_refl ltac:(lia)) as E9.
pose proof (pse_Ereg D 18 18%bv eq_refl ltac:(lia)) as E18.
pose proof (pse_Ereg D 19 19%bv eq_refl ltac:(lia)) as E19.
pose proof (pse_Ereg D 20 20%bv eq_refl ltac:(lia)) as E20.
pose proof (pse_Ereg D 21 21%bv eq_refl ltac:(lia)) as E21.
pose proof (pse_Ereg D 22 22%bv eq_refl ltac:(lia)) as E22.
pose proof (pse_Ereg D 23 23%bv eq_refl ltac:(lia)) as E23.
pose proof (pse_Ereg D 24 24%bv eq_refl ltac:(lia)) as E24.
pose proof (pse_Ereg D 25 25%bv eq_refl ltac:(lia)) as E25.
pose proof (pse_Ereg D 26 26%bv eq_refl ltac:(lia)) as E26.
pose proof (pse_Ereg D 27 27%bv eq_refl ltac:(lia)) as E27.
destruct (pse_E D H10) as (E10 & E32 & E33 & E34 & Eo0 & Eo12).
assert (Usp : bv_unsigned (ew (PSE_E D) 2) = spZ (pi_regs D)) by (rewrite E2; reflexivity).
assert (Uq : bv_unsigned (ew (PSE_E D) 10) = pi_q D) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ush : bv_unsigned (ew (PSE_E D) 32) = SHADOW_OFF)
  by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Up : bv_unsigned (ew (PSE_E D) 33) = pi_p D) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Utl : bv_unsigned (ew (PSE_E D) 34) = pi_text D + pi_len D)
  by (rewrite E34; apply unsigned_lit_small; lia).
assert (HEI : img_env VAL A_LIM (PSE_E D)) by (unfold PSE_E; apply Eimg_env).
destruct (pse_entry D HPRE0 H10 HIN HWIN HQ1 HQ2 HRA) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) segs B PST ARx STK_parse_string (pi_e D) [(pi_q D, pi_q D + 8)]
  (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_regs D) (pi_mem D) (pi_md D) (pi_ch D) HPRE0 HWIN) as HJ.
(* HPM : P (pi_mem D), the invariant at the entry memory; each run below carries it to its end memory *)
pose (RUN := paj_run_x_m_inv (SK := SK) (PL := PSB_PAListing) (PI := PSB_PAImg) B PST ARx LAWS PST_ok P PLAW).
pose (RUNTO := paj_run_to_x_m_inv (SK := SK) (PL := PSB_PAListing) (PI := PSB_PAImg) B PST ARx LAWS PST_ok P PLAW).
pose (BR := paj_branch (PI := PSB_PAImg)).
rewrite PSB_entry_sigma. unfold cfg_at. change (w64 (BASE + PSB_OFF)) with (Z_to_bv 64 (BASE + PSB_OFF)).
(* ---- offsets 0..135: the frame, the 13 saves, the q alignment check, the shadow base, the two folded shadow
   checks, p + 1 and its wrap check, text + len; the run stops at the bgeu ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PSE_Bspan; [pse_wr Usp HSTK He0|].
assert (HW1 : forall a, in_wrange (PSE_E D) (ss_mem ss_pse) a ->
                spZ (pi_regs D) - 144 <= a < spZ (pi_regs D)) by pse_inw Usp.
assert (KA1 : pse_keep (pi_W D) (pi_mem D) (ms_mem ms) (spZ (pi_regs D))).
{ split; [|exact HG].
  intros a Ha Hn. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros Hin. exact (Hn (HW1 a Hin)). }
rename HFr into HFr1. clear HF HG.
psrr_branch_tok RUN BR HS SHOK PSE_Bspan.
- (* the bgeu at 136 is TAKEN: p + 1 >= text + len, so nothing is left after the quote *)
  assert (HGE : pi_text D + pi_len D <= pi_p D + 1).
  { rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite !U_SOff, Up, Utl in Hc. rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
  assert (HNONE : PjGrammar.scan (ps_x D) = None).
  { unfold ps_x, rest_atR. rewrite skipn_all2 by lia. reflexivity. }
  (* the grammar's trace of a refused string is empty, so the call holds no bytes *)
  assert (HTR : PRH_Charge.prhPs_gtrace (ps_x D) = []).
  { unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. rewrite HNONE. reflexivity. }
  (* offsets 136..1255: the taken branch, straight to the NULL return *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PSE_Bspan (PSB_OFF + PSB_RET0); [pse_wr Usp HSTK He0|].
  pse_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  pose proof (st_ok_region_nth segs (PSE_E D) _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HREG.
  cbn [ms_mem restrict] in HREG.
  lazymatch goal with |- SRr _ _ (mkCfg ?mF _) _ => rename mF into msF end.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    rewrite (pse_pc_exit PSB_RET0 z ltac:(vm_compute; reflexivity)) end.
  apply ps_finP_of_postP. eapply (HRET0 D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D)); [exact HPRE|].
  split; [|split; [|split; [|split; [|split]]]].
  + exists 0, []. split; [apply ps_wb_nil|]. split; [exact HJ|].
    split; [exact KJ|].
    split.
    { pse_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. }
    split; [exact (pse_src (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_text D) (pi_tb D) KA HSPLO HSRC)|].
    split; [exact HHOME | exact HPM].
  + split; [rewrite R3; exact E3 | rewrite R4; exact E4].
  + rewrite R2, Usp. unfold w64, PS_Gen.PS_SP. rewrite HFRAME. f_equal; lia.
  + exact HROOM.
  + rewrite HTR. unfold PRH_Charge.prh_held.
    cbn [PjGrammar.held PjGrammar.calls length Z.of_nat]. lia.
  + unfold ps_Qres. rewrite HNONE.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (pse_ledger (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_ly D) (pi_S D) (pi_Hp D)
                     (pi_md D) _ _ _ _ _ _ _ KA HAR HSPLO HLED)|].
    split; [exact (pse_pjin (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_q D) (pi_text D) (pi_len D)
             (pi_p D) (pi_d D) (pi_tb D) KA HQ1 ltac:(lia) HSPLO HTXT HIN)|].
    (* no allocator call: E = [] and the state is the entry's, so every position is kept (f97c's None arm) *)
    exact (ps_rpos_nil (L := B_prog_listing) (PA := PSB_PAImg) D).
- (* the bgeu at 136 is NOT taken: p + 1 < text + len, fall into the scan head with x = p + 1 *)
  assert (HLT : pi_p D + 1 < pi_text D + pi_len D).
  { rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    rewrite !U_SOff, Up, Utl in Hc. rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
  (* offsets 136..147: li a2, 34 and mv a0, s4 *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PSE_Bspan (PSB_OFF + PSB_SCAN); [pse_wr Usp HSTK He0|].
  pse_kept D Usp HAR HSEGLOW KA1 HFr1 HFr HG KA KJ.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
  prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12. prreg HS (20%bv : bv 5) R20.
  prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24.
  pose proof (st_ok_region_nth segs (PSE_E D) _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HREG.
  cbn [ms_mem restrict] in HREG.
  lazymatch goal with |- SRr _ _ (mkCfg ?mF _) _ => rename mF into msF end.
  pmkst HS.
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?z)] =>
    rewrite (pse_pc_exit PSB_SCAN z ltac:(vm_compute; reflexivity)) end.
  apply ps_finP_hand. eapply (HSCAN D (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) _ _ _ (pi_p D + 1) HPRE).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  + split; [exact HJ|]. split; [exact KJ|].
    split.
    { pse_saved_tac D HREG Usp E1 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27. }
    split; [exact (pse_src (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_text D) (pi_tb D) KA HSPLO HSRC)|].
    split; [exact HHOME | exact HPM].
  + split; [rewrite R23; rewrite E32; reflexivity|].
    split; [rewrite R22, E10; rewrite (pse_shcell (ew (PSE_E D) 32) (pi_q D) Ush ltac:(lia)); reflexivity|].
    rewrite R24, Uq.
    rewrite (pse_shcell (ew (PSE_E D) 32) (pi_q D + 8) Ush ltac:(lia)). reflexivity.
  + split; [rewrite R3; exact E3 | rewrite R4; exact E4].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + exact (pse_ledger (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_ly D) (pi_S D) (pi_Hp D)
             (pi_md D) _ _ _ _ _ _ _ KA HAR HSPLO HLED).
  + exact (pse_pjin (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) (pi_q D) (pi_text D) (pi_len D)
             (pi_p D) (pi_d D) (pi_tb D) KA HQ1 ltac:(lia) HSPLO HTXT HIN).
  + exact (pse_ro (pi_W D) (pi_mem D) (ms_mem msF) (spZ (pi_regs D)) KA HSPLO HROD).
  + split; [rewrite R2, Usp; unfold w64, PS_Gen.PS_SP; rewrite HFRAME; f_equal; lia|].
    split; [rewrite R10, Up; reflexivity|].
    split; [rewrite R11, E34; reflexivity|].
    split; [rewrite R12; reflexivity|].
    split; [rewrite R8, E10; reflexivity|].
    split; [rewrite R9, E10; rewrite unsigned_lit_small by lia; reflexivity|].
    split; [rewrite R20, Up; reflexivity|].
    split; [lia|].
    replace (pi_p D + 1 - (pi_p D + 1)) with 0 by lia. cbn [Z.to_nat].
    unfold ps_x. destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (pi_p D + 1))) eqn:Es;
      cbn [option_map]; [rewrite Nat.add_0_r; reflexivity | reflexivity].
Qed.
(* the stable statement: the P := fun _ => True instance (psb_seg_*_of_True, srr_inv_laws_True); it did not move *)
Theorem psb_entry_holds : forall CTX CW,
  psb_seg_scan B ARx SK CTX CW -> psb_seg_ret0 B ARx SK CTX CW -> psb_seg_entry B ARx SK CTX CW.
Proof.
intros CTX CW HSCAN HRET0.
apply (proj1 (psb_seg_entry_of_True B ARx SK CTX CW)).
apply (psb_entry_holdsP CTX CW (fun _ => True) (srr_inv_laws_True (L := B_prog_listing) (PA := PSB_PAImg))).
- exact (proj2 (psb_seg_scan_of_True B ARx SK CTX CW) HSCAN).
- exact (proj2 (psb_seg_ret0_of_True B ARx SK CTX CW) HRET0).
Qed.
(* the audit: inside the Section, the hypotheses the proofs use; after it, the closed statements and their axioms *)
Print Assumptions psb_entry_holdsP.
Print Assumptions psb_entry_holds.

End pse.

Check psb_entry_holdsP.
Print Assumptions psb_entry_holdsP.
Check psb_entry_holds.
Print Assumptions psb_entry_holds.
