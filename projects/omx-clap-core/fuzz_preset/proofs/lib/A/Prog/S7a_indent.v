(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1693 of its 1918 lines of code are new or changed and 2561 lines of the source are left out. *)
(* fuzz_preset image A' (the #102 asan pin 1be0f53d), slice S7a: the program walk of indent (A' 0x886e0, 28
   instructions) over the ONE image-A program listing (lib/A/Listing_prog.v, h-verbs-1), generic in the image facts
   (Context PAImg) and in the allocator relation ARx (LAWS : AR_laws_x), concluding K0's text tindent_specX. THIS
   VERSION is on the kit's CUT 7cdbb61b5fa0 (merged forward into the batch prep on the batch kit's tip 44123abafeb7, whose texts it was
   re-fitted to; the cut's PRH_FnWriter / PRH_FnAlloc are the batch kit's bytes): every file but the lane's is the cut's (the A'
   listings v3, Listing_prog 7ed1529926bd / PAImg_prog 505a51ff7d08; CfParamsPreset b60d0f63c926). Relocated from the
   old-pin donor commit 30d755abfe58 by alreloc c4338d099cfb8025 (it moved only the entry address
   in two comments), re-fitted to the #102 texts: the ledger's two #102 cells (Section variables rmost / rown, fixed
   across indent's run), put's NULL arm keyed on f' = 1 with some history, fpre's rounding mode (frm_zero), and the batch kit's
   per-event premises: indent's consumer window prh_cons_from and live room prh_live_evs over its puts' events give
   each put's (S7a_WriterRet.prhWriter_cons_at / prhWriter_live_evs_at), and the post is prhWriter_ret_ok under
   prh_granted (DEAD-INDENT). PRW_StepKit (the S7b walk's) is taken with it (pa_slot_lt_ceil_b discharges fpre's raZ
   bound at both jal sites).
   THE GENERIC-P FORM (h-hpreset-7 12:18Z / 12:22Z): every segment is stated `forall P, srr_inv_laws
   SEGS P -> ...` (and `srr_inv_call SEGS P ->` where it crosses put's text) with P on its start and end memory, because
   an SRr post is OPAQUE once Qed, so an end-state invariant must be in the segment's statement; indent_holds
   instantiates P once (srr_inv_laws_imp / srr_inv_call_imp, memnorm over YAkMemnorm). ind_latch and ind_k13 are
   their P := fun _ => True corollaries, byte-identical to 6492e80df47.
   THE MODEL-RUN POSITION (tindent_specX and tput_specX, the batch kit's PRH_FnWriter.v): indent takes the run's next events as its
   ENTRY premise, `prh_run_at .. rp_i (prhWriter_evs [] st (wind ..))`, and posts the EXACT advance under the
   outcomes ok of its prhWriter_ret_ok. Each put call gets its event premise (tput_specX :476-477) from that list by
   S7a_WriterRet.prhWriter_ev_at, and the position after it by prhWriter_ret_pos_step (the event count is a function
   of the start and end state, prhW_evs_len). No named argument: indent_holds takes only put's text and the image
   facts. EXEMPT (statements moved for a TEXT, not for P): ind_pretty0 / ind_epi (and their P-forms), ind_call_put,
   ind_body, ind_pre, ind_iter, ind_holds_fixed (put's event premise and per-arm post; indent's entry premise and
   exact advance; indent's cut `spZ regs + 16 <= o` and entry record). Consumers: only this file. NO GAP: both put
   calls discharge put's one record (tput_specX :465-467) from indent's entry record (tindent_specX :659-661) by
   ind_rec_kept - the 16 bytes below o lie at or above indent's entry sp, outside the struct and the buffer, so
   neither indent's saves nor any put write them.
  rule 24: `proof-index indent` lists only plain/U lib/Prog/indent.v (SR framework, another vocabulary: a
   reading aid, never Required or copied); no ARx-form indent walk on the released refs or the named live heads.
   Engine: YC80x / YC1fPx (paj_run_x), the journal-free steps (branch, ret) YC1fP's; the call of put is
   YCbqGcallW's aj_call_xWR at wle' (its text is in the caller-window form fpostWmR); the after-call step is PRW_StepKit's.
   THE RE-HIDING MOVE (the texts as PRH_FnWriter.v states them): put's run crosses fuzz_realloc, so a segment whose
   run or continuation passes a put call concludes SRr' SEGS RZ_cf, and a journal carried after a put is at
   wle' SEGS RZ_cf (aj_call_xWR, the _invR runners, paj_branchR, SRr'_bind / SRr'_mono; a terminal ret is lifted by
   SRr_SRr'). The pretty = 0 arm calls no put: its SRr walk lifts by ind_srr_lift. The texts' new premise
   `length rp_os <= 4` is the section hypothesis HOS, which the put call passes to HPUT.
   NO IMAGE VALUE IS TYPED HERE: indent's entry is 4 * its generated slot (PAImg_prog A_prog_slot), and the two
   .rodata literals the code forms are read out of the generated listing itself (ind_addhi_off below reads the addend
   of the PAddHi at a named slot), so a re-pin is a regeneration, not a rewrite.
   Numerals: 4 (LENGTH: instruction bytes), 9 / 15 (indent's slots that form the two literals), 1 / 2 (LENGTH: the
   literals' lengths, a2 at the calls), 2 ^ 44 (LENGTH: the shadow span), 2 ^ 46 / 2 ^ 47 (LENGTH: the stack atom's
   range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit S7a_WriterRet S7a_WriterLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YCbqGcallW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia never sees a division here: each x / 8 is named and bounded first (set ... ; clearbody) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* no implicit sink: lib/A has no ASan sink instance, and the plain one (YI5b) would resolve silently *)
#[global] Remove Hints YI5b.src0_sink_head.

(* ---- indent's place in the generated listing, and the .rodata addends the listing carries ---- *)
Definition IND_SLOT : nat := A_prog_slot AS_indent.
Definition AF_indent : Z := 4 * Z.of_nat IND_SLOT.
Definition ind_addhi_off (k : nat) : Z :=
  match nth (IND_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ _ off => off
  | PLdHi _ _ _ _ off _ _ => off
  | _ => 0
  end.
Definition ind_addhi_atom (k : nat) : nat :=
  match nth (IND_SLOT + k) A_prog_listing (PW 0) with
  | PAddHi _ _ _ a _ => a
  | PLdHi _ _ _ a _ _ _ => a
  | _ => O
  end.

(* the space loop's count step `addiw s0, s0, -1` on a positive C int (YF0r v_addiw_dec's proof, for this file) *)
Lemma ind_addiw_dec : forall c, 1 <= c < 2 ^ 31 -> v_addiw (Z_to_bv 64 c) (-1) = Z_to_bv 64 (c - 1).
Proof.
intros c Hc. unfold v_addiw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. f_equal.
change (2 ^ 31)%Z with 2147483648 in Hc. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ind_dec : forall (E : env) c, ew E 8 = Z_to_bv 64 c -> 1 <= c < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff 8 0) (SLit (-1))) = Z_to_bv 64 (c - 1).
Proof.
intros E c H8 Hc.
change (sv_denot E (SAluw ALU_ADD (SOff 8 0) (SLit (-1))))
  with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SOff 8 0))) (low32 (sv_denot E (SLit (-1)))))).
change (sv_denot E (SLit (-1))) with (Z_to_bv 64 (-1)).
rewrite aluw_addi_lit.
assert (H0 : sv_denot E (SOff 8 0) = Z_to_bv 64 c).
{ cbn [sv_denot]. rewrite H8, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
rewrite H0. apply ind_addiw_dec. exact Hc.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* K0's named room predicate (PRH_Base.v PrhRoomLive, owner h-mani-a8): the walk only carries it *)
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the two literals the code forms: the newline at indent + 4 * 9, the two spaces at indent + 4 * 15 *)
Definition IND_NL : Z := VAL (ind_addhi_atom 9) + ind_addhi_off 9.
Definition IND_SP : Z := VAL (ind_addhi_atom 15) + ind_addhi_off 15.

Definition ind_Bx : sv := SOff 32 0.
Definition ind_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ind_ss0 : sstate :=
  mkSS AF_indent sr_atoms [stack_region (pi_frame F_indent)] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis TL : PALib B.
(* image fact of the instance, discharged at PI_prog_A by A_entry_indent *)
Hypothesis Hent : SIGMA AS_indent = BASE + AF_indent.
(* the universe closure both texts take (the batch kit's PRH_Base.v prh_univ_closure B CTX0) *)
Variable CTX0 : list (list Z).
(* the position interface the texts carry (lib/Spec/PresetRoomPos.v): fixed across indent's calls, only the index
   and the history advance *)
Variable rp_sm : list Z -> Z * Z.
Variable rp_x : list Z.
Variable rp_os : list (option nat * option nat * option nat).
(* the texts' bound on the interface's outcome list (tput_specX / tindent_specX, right after iface_room_pos): fixed
   with rp_os, passed to put's text at each call *)
Hypothesis HOS : (length rp_os <= 4)%nat.
Variable rp_H0 : list Z.
(* the #102 ledger's two cells g_most / g_own_ran_out (PRH_Base.v prh_ledger's `most own`, kit walkkit-next
   decff67d721f), named rmost / rown here (`own` is the journals' ownership argument): indent writes neither, so they
   are fixed across indent's run, as the texts state them *)
Variable rmost rown : Z.
(* the callee's text tput_specX (PRH_FnWriter.v: SRr' SEGS RZ_cf, the post fpostWmR at wle'): the slice's own put
   walk proves it *)
Hypothesis HPUT : tput_specX (PA := PA) B ARx SK CTX0.
(* IMAGE FACT (discharged at PI_prog_A from the generated image and its const-shadow cells, AF0m Tfib_const_shadow):
   the two .rodata literals of indent ("\n" at IND_NL, "  " at IND_SP; no kit name gives a literal's address, K0's
   PRH_FnWriter.v "named gap"). In any allocator state whose read-only bytes are the image's, each literal is a
   readable source (src_rd: its bytes from arodata, its shadow from the const cells ARx keeps, alx_const_cells) and
   kept_at's image-string case holds (kept_img: ro bytes, const-shadow cells) *)
Hypothesis HLIT : forall ly S Hp (W : world SEGS) mem md,
  ARx ly S Hp W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  (src_rd W mem IND_NL [10] /\ kept_at B [] IND_NL 1) /\ (src_rd W mem IND_SP [32; 32] /\ kept_at B [] IND_SP 2).
(* IMAGE FACT (discharged at PI_prog_A: the SEVEN statics of prh_pst are writable, outside every read-only segment
   and outside the relro range): no read-only image byte is a program static *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).

Let RUN := paj_run_x (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS.
Let RUNTO := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS.
Let BR := paj_branch (PI := PA).
Let BRR := paj_branchR (PI := PA) (wle' SEGS RZ_cf).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).

(* ---- the entry state: indent's own frame, no shadow entry (indent itself checks no shadow byte) ---- *)
Lemma ind_entry : forall ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARx STK_indent ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ind_ss0
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + AF_indent)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS ind_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HAP.
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HK3 : 0 <= pi_frame F_indent) by (vm_compute; discriminate).
set (E := Eimg (Ereg regs [])).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split; [|constructor].
rewrite restrict_mkst_fx. unfold ind_ss0. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* ---- the loop head (indent + 4 * 16, the `li a2, 2` of the space loop), seated FRESH: sp is atom 2 (indent's entry
   sp - 32), s0 / s1 / s2 the count / o / IND_SP as register atoms, and indent's frame [sp, sp + 32) holds the saved
   s2, s1, s0, ra of the entry as atoms 32 .. 35, READ-ONLY (write window empty: from the loop head on, indent stores
   nothing, so a run from a seat keeps every byte of memory) ---- *)
Definition IND_K16 : Z := AF_indent + 4 * 16.
(* the call's return site (slot 20) and the epilogue (slot 22) *)
Definition IND_K20 : Z := AF_indent + 4 * 20.
Definition IND_K22 : Z := AF_indent + 4 * 22.
(* a slot offset as the literal the symbolic run prints, COMPUTED from the listing (never typed: it moves with a
   re-pin, h-rw-pre-1's derived-value trap) *)
Ltac ind_lit t := let v := eval vm_compute in t in exact v.
Definition ind_ssk (k : Z) : sstate :=
  mkSS k sr_atoms
    [YP09.mkRegion (Some 2%nat) 0 32 0 0
       [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
        YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0))]]
    None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition ind_ss16 : sstate := ind_ssk IND_K16.
Definition ind_x16 (regs : bvmap 5 word) : list word := [getr regs 18; getr regs 9; getr regs 8; getr regs 1].

Lemma ind_seat : forall k (W : world SEGS) (regs regs1 : bvmap 5 word) mem1,
  spZ regs1 mod 16 = 0 ->
  (forall a, spZ regs1 <= a < spZ regs1 + 32 -> apresent (w_H W) mem1 a) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1 + 8) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1 + 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1 + 24) 8 (bv_unsigned (getr regs 1)) ->
  2 ^ 46 <= spZ regs1 <= 2 ^ 47 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (ind_x16 regs))) (ind_ssk k)
    (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 (BASE + k)) mem1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS ind_Bx [] (Eimg (Ereg regs1 (ind_x16 regs))) (mrestrict (w_H W) mem1).
Proof.
intros k W regs regs1 mem1 Hal Hpres V0 V8 V16 V24 Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (ind_x16 regs))).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 (ind_x16 regs)) kk)
  by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (VB : base_val E (Some 2%nat) = spZ regs1) by (cbn [base_val]; exact Usp).
assert (E32 : ew E 32 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (DEN : forall (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned w)).
{ intros n w Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
split; [|constructor].
rewrite restrict_mkst_fx. unfold ind_ssk. apply pa_entry_st_ok_full.
- subst E. apply (regs_ok_agree 32 (Ereg regs1 (ind_x16 regs))).
  + split; [intros kk Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  + vm_compute. reflexivity.
  + apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
  split; [lia|]. split; [lia|]. split.
  { intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia. }
  pose proof (u64_range (getr regs 18)). pose proof (u64_range (getr regs 9)).
  pose proof (u64_range (getr regs 8)). pose proof (u64_range (getr regs 1)).
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ (spZ regs1) 0 8 (SOff 32 0) (bv_unsigned (getr regs 18)));
      [exact (DEN 32%nat _ E32) | zside | zside | rewrite Z.add_0_r; exact V0].
  + apply (chunk_ok_val SEGS E _ (spZ regs1) 8 8 (SOff 33 0) (bv_unsigned (getr regs 9)));
      [exact (DEN 33%nat _ E33) | zside | zside | exact V8].
  + apply (chunk_ok_val SEGS E _ (spZ regs1) 16 8 (SOff 34 0) (bv_unsigned (getr regs 8)));
      [exact (DEN 34%nat _ E34) | zside | zside | exact V16].
  + apply (chunk_ok_val SEGS E _ (spZ regs1) 24 8 (SOff 35 0) (bv_unsigned (getr regs 1)));
      [exact (DEN 35%nat _ E35) | zside | zside | exact V24].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* ---- memory transfer: a stretch that keeps every byte below alloc_ceiling and every byte of the struct keeps the
   writer's state at o and the ledger (their reads are the statics, the block heads, the buffer and its shadow, all
   below alloc_ceiling, and the struct's four fields) ---- *)
Lemma ind_out_kept : forall (W : world SEGS) mem mem' Lam o buf (st : WriterApp.wst),
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, o <= a < o + 32 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling) ->
  prhWriter_out W mem Lam o buf st -> prhWriter_out W mem' Lam o buf st.
Proof.
intros W mem mem' Lam o buf st Hlow Hstr Hbuf
  (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VM : forall a n v, (0 <= Z.of_nat n)%Z -> (forall k, (k < n)%nat -> aview SEGS (w_H W) mem' (a + Z.of_nat k) = aview SEGS (w_H W) mem (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v _ Hk Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros k Hk'. rewrite <- (Z2Nat.id k) by lia. apply Hk. lia. }
split; [exact Ho8|]. split; [exact Hbr|]. split; [exact Hcr|].
split; [eapply VM; [lia | intros k Hk; apply Hstr; lia | exact V0]|].
split; [eapply VM; [lia | intros k Hk; apply Hstr; lia | exact V8]|].
split; [eapply VM; [lia | intros k Hk; apply Hstr; lia | exact V16]|].
split; [eapply VM; [lia | intros k Hk; apply Hstr; lia | exact V24]|].
split; [exact Hf01|]. split; [exact Hbok|].
destruct Harm as [Hz | (Hgrid & Hin & Hlen & (rest & Hrl & Hba) & Hsh)]; [left; exact Hz|].
assert (Hcap0 : WriterApp.w_cap st <> 0).
{ destruct Hgrid as (j & Hj & Hc). intros Hz. rewrite Hz in Hc.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
destruct (Hbuf Hcap0) as (Hb0 & Hbc).
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [exact Hlen|].
split.
{ exists rest. split; [exact Hrl|]. intros j Hj. destruct (Hba j Hj) as (Hv & Hr). split; [|exact Hr].
  eapply VM; [lia | intros kk Hkk; apply Hlow; cbn [length] in Hj; lia | exact Hv]. }
intros Hnf. destruct (Hsh Hnf) as (Hra & Hhv). split.
- intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr, SHADOW_OFF. apply Hlow.
  set (q := x / 8) in *.
  assert (Hq0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
  assert (Hq8 : 8 * q <= x) by (unfold q; apply Z.mul_div_le; lia).
  clearbody q. lia.
- intros s Hs. rewrite Hlow; [apply (Hhv s Hs)|].
  unfold shadow_addr, shadow_of_addr, SHADOW_OFF in Hs |- *.
  set (q1 := buf / 8) in *. set (q2 := (buf + WriterApp.w_cap st - 1) / 8) in *.
  assert (Hq10 : 0 <= q1) by (unfold q1; apply Z.div_pos; lia).
  assert (Hq18 : 8 * q1 <= buf) by (unfold q1; apply Z.mul_div_le; lia).
  assert (Hq20 : 0 <= q2) by (unfold q2; apply Z.div_pos; lia).
  assert (Hq28 : 8 * q2 <= buf + WriterApp.w_cap st - 1) by (unfold q2; apply Z.mul_div_le; lia).
  clearbody q1 q2.
  set (r1 := (2147450880 + q1) / 8) in *. set (r2 := (2147450880 + q2) / 8) in *.
  assert (Hr10 : 0 <= r1) by (unfold r1; apply Z.div_pos; lia).
  assert (Hr18 : 8 * r1 <= 2147450880 + q1) by (unfold r1; apply Z.mul_div_le; lia).
  assert (Hr20 : 0 <= r2) by (unfold r2; apply Z.div_pos; lia).
  assert (Hr28 : 8 * r2 <= 2147450880 + q2) by (unfold r2; apply Z.mul_div_le; lia).
  clearbody r1 r2. lia.
Qed.

(* a 16-aligned address strictly below a 16-aligned ceiling leaves 8 bytes below it *)
Lemma ind_al16_room : forall p c, p mod 16 = 0 -> c mod 16 = 0 -> p < c -> p + 8 <= c.
Proof.
intros p c Hp Hc Hlt.
pose proof (Z.div_mod p 16 ltac:(lia)) as Ep. pose proof (Z.div_mod c 16 ltac:(lia)) as Ec.
rewrite Hp in Ep. rewrite Hc in Ec.
set (qp := p / 16) in *. set (qc := c / 16) in *. clearbody qp qc. lia.
Qed.

(* the ledger over a stretch that keeps every byte below alloc_ceiling: its reads are the five statics (in the
   image, below kLowMemEnd) and the block heads (16-aligned, inside live blocks below alloc_ceiling) *)
Lemma ind_ledger_kept : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown -> prh_ledger B ly S Hp W mem' Lam peak cnt fail ran rmost rown.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran HAR Hlow (Hg & Hnd & Hbl & Hperm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as (HCV1 & HCV2).
assert (VM : forall a (n : nat) v, (forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < YM05.alloc_ceiling) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hr Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros k Hk. rewrite <- (Z2Nat.id k) by lia. apply Hlow. apply Hr. lia. }
assert (ST : forall a (n : nat), 0 <= a -> a + Z.of_nat n <= kLowMemEnd ->
  forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < YM05.alloc_ceiling) by (intros; lia).
destruct Hg as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & Gr).
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- split; [eapply VM; [apply ST; vm_compute; discriminate | exact G1]|].
  split; [eapply VM; [apply ST; vm_compute; discriminate | exact G2]|].
  split; [eapply VM; [apply ST; vm_compute; discriminate | exact G3]|].
  split; [eapply VM; [apply ST; vm_compute; discriminate | exact G4]|].
  split; [eapply VM; [apply ST; vm_compute; discriminate | exact G5]|].
  split; [split; [eapply VM; [apply ST; vm_compute; discriminate | exact G6] | exact G6b]|].
  split; [split; [eapply VM; [apply ST; vm_compute; discriminate | exact G7] | exact G7b]|].
  exact Gr.
- eapply Forall_impl; [|exact Hbl]. intros [a k] (Hk0 & Hin & HinHp & Ha16 & Hv). cbn [fst snd] in *.
  split; [exact Hk0|]. split; [exact Hin|]. split; [exact HinHp|]. split; [exact Ha16|].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin) as (Hp16 & Hp4 & Hpc & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hrs : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbv iota; lia).
  assert (H8 : a - cf_head + 8 <= YM05.alloc_ceiling).
  { apply ind_al16_room; [exact Hp16 | | lia].
    pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(lia)) as Ec. rewrite HCV2 in Ec.
    rewrite Ec. set (q := YM05.alloc_ceiling / 4096). clearbody q.
    replace (4096 * q + 0) with ((256 * q) * 16) by lia. apply Z_mod_mult. }
  eapply VM; [intros kk Hkk; lia | exact Hv].
Qed.

(* ---- the trivial invariant: every segment's old statement is its P-form at P := fun _ => True ---- *)
Lemma ind_laws_true : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma ind_call_true : srr_inv_call SEGS (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.
(* a journal at wle is one at wle' (YCbqG ajournal_xbR_mono at wle_wle') *)
Lemma ind_aj_lift : forall STK sp0 FP ly S Hp (W : world SEGS) mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) STK sp0 FP ly S Hp W mem md own
    ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_xbR_mono (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (@wle SEGS) (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)
  STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.
(* a walk that calls no put: its SRr to fpostW is an SRr' to the R form at wle' (SRr_SRr', the journal lifted) *)
Lemma ind_srr_lift : forall STK d FP (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W0 c,
  SRr SEGS W0 c (fpostW B ARx SK STK d FP regs ly S Hp W mem md Q) ->
  SRr' SEGS RZ_cf W0 c (fpostWR B ARx SK (wle' SEGS RZ_cf) STK d FP regs ly S Hp W mem md Q).
Proof.
intros STK d FP regs ly S Hp W mem md Q W0 c H.
apply (SRr'_mono SEGS RZ_cf W0 c _ _ (SRr_SRr' SEGS RZ_cf W0 c _ H)).
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & H1 & H2 & H3 & H4 & H5).
exists ly', S', Hp', regs', mem', md', k.
split; [exact H1|]. split; [exact (ind_aj_lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2)|].
split; [exact H3 | split; [exact H4 | exact H5]].
Qed.
Lemma ind_fpostW_drop : forall STK d FP (regs : bvmap 5 word) ly S Hp (W : world SEGS) mem md
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (R : (word -> option byte) -> Prop) W' c',
  fpostWR B ARx SK (wle' SEGS RZ_cf) STK d FP regs ly S Hp W mem md
    (fun ly' S' Hp' W' regs' mem' md' => Q ly' S' Hp' W' regs' mem' md' /\ R mem') W' c' ->
  fpostWR B ARx SK (wle' SEGS RZ_cf) STK d FP regs ly S Hp W mem md Q W' c'.
Proof.
intros STK d FP regs ly S Hp W mem md Q R W' c' (ly' & S' & Hp' & regs' & mem' & md' & k & H1 & H2 & H3 & H4 & H5 & _).
exists ly', S', Hp', regs', mem', md', k.
split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | exact H5]]]].
Qed.

(* ---- the arm pretty = 0: the body runs from the entry to the return, with no call and no write but its own
   frame; so the writer's state at o and the ledger are the entry's, and the run of puts is empty ---- *)
Lemma ind_pretty0_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W regs mem md ch o depth d buf (st : WriterApp.wst) Lam peak ran
    (rp_i : nat) (rp_hist : list YG00.chunk),
  fpre B ARx STK_indent ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  getr regs 10 = w64 o -> getr regs 11 = w64 0 -> getr regs 12 = w64 depth ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown -> P mem ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_indent) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st [] ly' S' Hp' W' regs' mem' md') /\
          P mem')).
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
intros ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i rp_hist HPRE HROOM HPOS H10 H11 H12 HWIN Hol Hoh HOUT HLED HPM.
(* this arm calls no put: the walk below is its SRr walk, lifted *)
apply ind_srr_lift.
pose proof HPRE as (HAP & HRO & HSTKTOP).
destruct (ind_entry ly S Hp W regs mem md ch HAP) as (HS & SHOK).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HK3 : 0 <= pi_frame F_indent) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (ajournal_x_init_W SK SEGS B (@prh_pst prh_img_A) ARx STK_indent d
  (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := Eimg (Ereg regs [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = getr regs 11)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (U11 : U E (SOff 11 0) = 0) by (apply (U_atom E 11%nat 0); [rewrite E11, H11; reflexivity | lia]).
unfold cfg_at. rewrite Hent.
change (w64 (BASE + AF_indent)) with (Z_to_bv 64 (BASE + AF_indent)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM ind_Bspan.
{ eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- d));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia | cbn [YP09.r_whi stack_region]; lia
  | apply awr_ok_nil]. }
psrr_branch_tok RUN BR HS SHOK ind_Bspan.
2:{ match goal with Hc : branch_taken _ _ _ = false |- _ =>
      rewrite branch_eq_U, U11, (U_lit E 0 ltac:(lia)) in Hc; discriminate Hc end. }
match goal with Hc : branch_taken _ _ _ = true |- _ => clear Hc end.
paj_run_tok_x_inv RUNI HS HJ SHOK HPM ind_Bspan.
{ eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- d));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia | cbn [YP09.r_whi stack_region]; lia
  | apply awr_ok_nil]. }
(* the return at slot 27: every callee-saved register and ra are back at their entry atoms *)
rewrite wvb_collapse in HJ.
apply (RET W E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat1.
assert (HAG : env_agree 32 (Ereg regs []) E).
{ split; [intros k Hk; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HP : aregs_preserved regs (ms_regs ms0)).
{ pose proof HS as HS'. unfold st_ok_pi in HS'.
  eapply (aregs_preserved_of_st_ok SEGS); [exact HS' | exact HAG | vm_compute; reflexivity]. }
assert (Hra1 : getr (ms_regs ms0) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W) E _ ms0 1%bv HS).
  match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
(* only indent's own frame [sp - 32, sp) changed, over both stretches *)
assert (NOW : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 32 \/ spZ regs <= a) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout.
  assert (NW : forall rs, (forall r, In r rs -> YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = -32 /\ YP09.r_whi r = 0) ->
    ~ in_wrange E rs a).
  { intros rs Hrs (r & Hr & Hra'). destruct (Hrs r Hr) as (Hb & Hl & Hh). rewrite Hb, Hl, Hh in Hra'.
    cbn [base_val] in Hra'. rewrite Usp in Hra'. lia. }
  apply aview_eq_of. rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |].
  all: rewrite unsigned_lit_small by lia; apply NW; intros r Hr.
  all: first [unfold ind_ss0 in Hr | idtac]; cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | []].
  all: cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region]; rewrite ?HKf; repeat split; reflexivity. }
exists ly, S, Hp, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md) mat1 md), 0.
split.
{ rewrite wvb_collapse, Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ pose proof (ajournal_x_materialize (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low rc A_prog_listing PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) as HJ1.
  rewrite wvb_collapse in HJ1. exact HJ1. }
split; [intros a Ha _; apply NOW; [lia | lia]|].
split; [exact HP|].
split; [|exact HPM].
split; [exact HROOM|].
apply (prhWriter_ret_pos_nil B rp_sm rp_x rp_os rp_H0 rp_i rp_hist).
- apply (ind_out_kept W mem (ms_mem ms0) Lam o buf st); [| | |exact HOUT].
  + intros a Ha. apply NOW; lia.
  + intros a Ha. apply NOW; lia.
  + intros Hc. pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
    destruct HOUT as (_ & _ & Hcr & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction|].
    pose proof (proj1 (Forall_forall _ _) Hbl _ Hin) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hinb) as (_ & Hp4 & Hpc & _).
    pose proof (@cf_head_nonneg cp) as Hch0.
    assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
    rewrite Hreq in Hpc. lia.
- apply (ind_ledger_kept ly S Hp W mem (ms_mem ms0) md); [exact HAR | intros a Ha; apply NOW; lia | exact HLED].
- apply Permutation_refl.
- exact HPOS.
Qed.

(* the P := fun _ => True corollary of ind_pretty0_P; its post moved for the TEXT (kit-oldpin b501d43ce5af's exact
   advance, tindent_specX :455-461) *)
Lemma ind_pretty0 : forall ly S Hp W regs mem md ch o depth d buf (st : WriterApp.wst) Lam peak ran
    (rp_i : nat) (rp_hist : list YG00.chunk),
  fpre B ARx STK_indent ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  getr regs 10 = w64 o -> getr regs 11 = w64 0 -> getr regs 12 = w64 depth ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_indent) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st [] ly' S' Hp' W' regs' mem' md')).
Proof.
intros ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i rp_hist HPRE HROOM HPOS H10 H11 H12 HWIN Hol Hoh HOUT HLED.
eapply (SRr'_mono SEGS RZ_cf); [exact (ind_pretty0_P (fun _ => True) ind_laws_true ly S Hp W regs mem md ch o depth d buf st Lam peak ran
  rp_i rp_hist HPRE HROOM HPOS H10 H11 H12 HWIN Hol Hoh HOUT HLED I)|].
intros W' c' _ H. exact (ind_fpostW_drop _ _ _ _ _ _ _ _ _ _ _ (fun _ => True) _ _ H).
Qed.

(* ---- put's one record from o (tput_specX case 1) depends only on the 16 bytes below o ---- *)
Lemma ind_rec_kept : forall (rd rd' : reader) o,
  (forall a, o - 16 <= a < o -> rd' a = rd a) ->
  (exists ra, rdword rd (o - 8) = Some ra /\ exists nfp, rdword rd (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  (exists ra, rdword rd' (o - 8) = Some ra /\ exists nfp, rdword rd' (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
Proof.
intros rd rd' o Hk (ra & Hra & nfp & Hnfp & Hlt). exists ra. split.
- rewrite <- Hra. unfold rdword. rewrite !Hk by lia. reflexivity.
- exists nfp. split; [|exact Hlt]. rewrite <- Hnfp. unfold rdword. rewrite !Hk by lia. reflexivity.
Qed.

(* ---- a call of put from indent's frame (sp1 = indent's entry sp - 32): put's text tput_specX through the engine's
   caller-window call rule at wle', YCbqGcallW.aj_call_xWR. put's window e1 = 32 + d covers indent's frame and indent's own caller window,
   so put's widened journal (STK_put + 32 + d) (sp1 + 32 + d) is indent's (STK_indent + d) (sp + d). put's footprint
   lies in indent's caller window (the struct) or is indent's entry buffer (in FP) or a block made since entry. ---- *)
Lemma ind_call_put_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall W0 W (regsc : bvmap 5 word) memc mdc FP ly S Hp mem md lyc Sc Hpc k sp d o s (bs : list Z)
    buf (st : WriterApp.wst) Lam peak ran (raw : word) chc (rp_i : nat) (rp_hist : list YG00.chunk),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W0 mem md []
    lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw -> bv_unsigned raw < YM05.alloc_ceiling ->
  achain lyc (aview SEGS (w_H W) memc) (sp - 32) (s0Z regsc) chc ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  room_live_cf Sc -> prh_univ_closure B CTX0 ->
  (* FRM0-ENTRY (fpre's last conjunct, lib/A/PRH_Base.v fpre): the entry rounding mode, which indent's own
     fpre gives and nothing in indent changes; put's fpre asks it *)
  YK0o.frm_zero (@YK11.fp_csr fx) -> sp + 32 <= ly_stk_hi lyc ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  (* put's consumer window (tput_specX, the batch kit), supplied by the caller from its own (prhWriter_cons_at) *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  getr regsc 10 = w64 o -> getr regsc 11 = w64 s -> getr regsc 12 = w64 (Z.of_nat (length bs)) ->
  sp <= o -> o + 32 <= sp + d ->
  prhWriter_out W memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  src_rd W memc s bs ->
  prhWriter_src_home B lyc Sc Lam buf (WriterApp.w_cap st) s (Z.of_nat (length bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length bs) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* put's live room at each of its events (tput_specX, the batch kit), supplied by the caller (prhWriter_live_evs_at) *)
  prh_live_evs Sc (prhWriter_evs [] st [bs]) ->
  (forall a, inFP (prhWriter_fp buf (WriterApp.w_cap st)) a ->
     inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  (* put's one record (tput_specX :453-455 on the cut 7cdbb61b5fa0), carried as this call lemma's ARGUMENT *)
  (spZ regsc + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) memc) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  (* put's run event (tput_specX :476-477), supplied by the caller from its own entry list (prhWriter_ev_at) *)
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  P memc ->
  SRr' SEGS RZ_cf W (mkCfg (YK11.mkst regsc (Z_to_bv 64 (SIGMA AS_put)) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W0 mem md []
         ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       (forall a, sp - 32 <= a < sp + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       aregs_preserved regsc regs2 /\ room_live_cf S2 /\
       prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st bs o W2 mem2 S2 /\
       prhWriter_retg B lyc Sc Lam peak ran rmost rown o buf st [bs] ly2 S2 Hp2 W2 regs2 mem2 md2 /\ P mem2).
Proof.
intros P PLAW PCALL.
intros W0 W regsc memc mdc FP ly S Hp mem md lyc Sc Hpc k sp d o s bs buf st Lam peak ran raw chc rp_i rp_hist
  HJ Hsp Hal Hd0 Hd16 Hgp Htp Hra Hraw Hra4 Hrawc Hch HRO HROOM HUNIV HFRM HSTKTOP HPOS HCONS H10 H11 H12 Hol Hoh HOUT HLED HSRC HHOME HLEN HMAX HLIVE HFPB HCHO HEV HPMc.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
assert (HTOPc : spZ regsc + 64 <= ly_stk_hi lyc) by (rewrite Hsp; lia).
assert (HCUT : spZ regsc + 16 <= o) by (rewrite Hsp; lia).
assert (HRAc : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite Hra; exact Hrawc).
eapply (SRr'_mono SEGS RZ_cf).
{ apply (YCbqGcallW.aj_call_xWR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA)
    (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf) W regsc memc (SIGMA AS_put)
    (STK_indent + d) (sp + d) FP ly S Hp W0 mem md [] lyc Sc Hpc mdc k STK_put (32 + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) (- (32 + d)) raw chc
    (fQmn memc (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
       (prhWriter_grows st bs = false ->
          PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\
       (prhWriter_grows st bs = true -> forall f', val_mem SEGS (mrestrict (w_H W') mem') (o + 24) 4 f' ->
          (f' = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S') /\
          (f' = 1 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S')) /\
       exists ok, prhWriter_ret_ok B ok lyc Sc Lam peak ran rmost rown o buf st [bs] ly' S' Hp' W' regs' mem' md' /\
         prh_granted ok (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k ok st [bs]))) HJ).
  - rewrite Hsp. lia.
  - rewrite Z.mod_opp_l_z; [reflexivity | lia |]. rewrite Z.add_mod, Hd16 by lia. reflexivity.
  - lia.
  - exact HK2.
  - lia.
  - lia.
  - rewrite Z.add_mod, Hd16 by lia. reflexivity.
  - lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - replace (sp + d + - (32 + d)) with (sp - 32) by lia. exact Hch.
  - intros HAPc HWc. unfold cfg_at in HPUT.
    pose proof (HPUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist rmost rown lyc Sc Hpc W regsc memc mdc chc o s (Z.of_nat (length bs)) (32 + d) buf st bs Lam peak ran
      (conj HAPc (conj HRO (conj HTOPc (conj HRAc HFRM)))) HROOM HPOS HOS HCONS HUNIV H10 H11 H12
        (or_introl HCUT) HCHO HWc ltac:(lia) ltac:(lia) HOUT HLED HSRC eq_refl HHOME HEV HLEN HMAX HLIVE)
      as HC.
    exact HC.
  - intros a Ha. cbn [prhWriter_cfp] in Ha. destruct Ha as (r & [<- | Hr] & Hra').
    + right; right; right. cbn [fst snd] in Hra'. lia.
    + destruct (HFPB a (ex_intro _ r (conj Hr Hra'))) as [Hf | Ht]; [left; exact Hf | right; left; exact Ht]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc & HJ2 & _ & HX & HP & HKP).
unfold fQmn in HKP. destruct HKP as ((HQ1 & HQN & HQG & HQ2) & HMN).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [exact Hc|]. split; [exact HJ2|].
split; [|split; [exact HP | split; [exact HQ1 | split; [exact (conj HQN HQG) | split; [exact HQ2 |
  exact (PCALL memc mem2 HMN HPMc)]]]]].
intros a Ha Hn. apply HX; [lia | exact Hn].
Qed.

(* ---- read-only image bytes survive a journal: the image clause keeps every image byte that is not runtime-owned,
   not errno, not a program static (HPSTRO) and not the sink head (an FP of stack / heap ranges above 0 opens no
   sink) ---- *)
Lemma ind_arodata_kept : forall STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k,
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) STK sp0 FP ly S Hp W mem md own
    ly2 S2 Hp2 W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k HJ Hsk HRO a Hro Hown Herr.
pose proof (ajxR_img HJ) as F3.
rewrite (F3 a); [exact (HRO a Hro Hown Herr) | | exact Hown | exact Herr | exact (HPSTRO a Hro) | exact (fp_spares_closed FP a Hsk)].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)].
Qed.

(* ---- a literal of the read-only image is a writer source at every state: kept_at's image cases read no ledger,
   and no allocator block byte is an image byte (YCbqG blk_img_x), so the literal is outside the buffer ---- *)
Lemma ind_kept_lam : forall Lam p n, 0 < n -> kept_at B [] p n -> kept_at B Lam p n.
Proof.
intros Lam p n Hn [(b & m & Hin & _) | [Hz | Hi]]; [destruct Hin | right; left; exact Hz | right; right; exact Hi].
Qed.

Lemma ind_kept_img : forall p n a, kept_at B [] p n -> p <= a < p + n -> in_img SEGS a.
Proof.
intros p n a [(b & m & Hin & _) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] Ha; [destruct Hin| |].
all: destruct (Hro a Ha) as (Hr & _); destruct Hr as [(sg & Hsg & _ & Hr) | Hr];
  [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)].
Qed.

Lemma ind_src_home : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran buf (st : WriterApp.wst) p n,
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  (WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam) ->
  0 <= WriterApp.w_cap st -> 0 < n ->
  kept_at B [] p n ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) p n.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran buf st p n HAR HLED HIN Hc0 Hn HK.
split; [left; exact (ind_kept_lam Lam p n Hn HK)|].
destruct (Z.eq_dec (WriterApp.w_cap st) 0) as [Hz | Hnz]; [left; exact Hz|]. right.
destruct (Z_le_gt_dec (p + n) buf) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (buf + WriterApp.w_cap st) p) as [H2 | H2]; [right; exact H2|].
exfalso. pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
pose proof (proj1 (Forall_forall _ _) Hbl _ (HIN Hnz)) as (Hk0 & Hinb & _). cbn [fst snd] in *.
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
set (x := Z.max p buf).
apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md
  (buf - cf_head) (WriterApp.w_cap st + cf_head) x HAR Hinb).
- rewrite Hreq. unfold x. lia.
- apply (ind_kept_img p n x HK). unfold x. lia.
Qed.

(* ---- one round of the space loop: a fresh seat at the loop head (slot 16) runs to the put call (slot 19) and the
   call returns at slot 20, where ind_latch takes over. Continuation form: the continuation is handed put's post. ---- *)
Lemma ind_body_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W mem md lyc Sc Hpc (W1 : world SEGS) (regs regs1 : bvmap 5 word) memc md1 k FP sp d
    o cnt buf (st : WriterApp.wst) Lam peak ran (rp_i : nat) (rp_hist : list YG00.chunk)
    (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
    lyc Sc Hpc W1 memc md1 k ->
  spZ regs1 = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> 2 ^ 46 <= sp - 32 -> sp + d <= 2 ^ 47 ->
  sp + 32 <= ly_stk_hi lyc -> sp <= o -> o + 32 <= sp + d ->
  getr regs1 8 = Z_to_bv 64 cnt -> 1 <= cnt < 2 ^ 31 ->
  getr regs1 9 = w64 o -> getr regs1 18 = w64 IND_SP -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
  val_mem SEGS (mrestrict (w_H W1) memc) (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) memc) (sp - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) memc) (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) memc) (sp - 8) 8 (bv_unsigned (getr regs 1)) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) memc) ->
  ARx lyc Sc Hpc W1 memc md1 ->
  room_live_cf Sc -> prh_univ_closure B CTX0 -> YK0o.frm_zero (@YK11.fp_csr fx) ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist Sc ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [[32; 32]])) ->
  prhWriter_out W1 memc Lam o buf st ->
  prh_ledger B lyc Sc Hpc W1 memc Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  Z.of_nat (length (WriterApp.w_text st)) + 2 + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs Sc (prhWriter_evs [] st [[32; 32]]) ->
  (forall a, inFP (prhWriter_fp buf (WriterApp.w_cap st)) a ->
     inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  (* put's one record at the seat (the argument ind_call_put passes to put's text) *)
  (sp - 32 + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W1) memc) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W1) memc) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  (* put's run event at the seat (the caller derives it from its entry list by prhWriter_ev_at) *)
  (prhWriter_grows st [32; 32] = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st [32; 32])) ->
  P memc ->
  (forall ly2 S2 Hp2 (W2 : world SEGS) regs2 mem2 md2 k1,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
       ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     (forall a, sp - 32 <= a < sp + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a) ->
     (forall rr, acallee_saved rr -> getr regs2 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)) ->
     room_live_cf S2 ->
     prhWriter_put_pos rp_sm rp_x rp_os rp_H0 rp_i rp_hist st [32; 32] o W2 mem2 S2 ->
     prhWriter_retg B lyc Sc Lam peak ran rmost rown o buf st [[32; 32]] ly2 S2 Hp2 W2 regs2 mem2 md2 -> P mem2 ->
     SRr' SEGS RZ_cf W2 (mkCfg (YK11.mkst regs2 (Z_to_bv 64 (BASE + IND_K20)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K16)) memc (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
intros ly S Hp W mem md lyc Sc Hpc W1 regs regs1 memc md1 k FP sp d o cnt buf st Lam peak ran rp_i rp_hist Q
  HJ Hsp Hal Hd0 Hd16 Hlo Hhi HTOP Hol Hoh H8 Hcnt H9 H18 Hgp Htp V0 V8 V16 V24 HRO HAR HROOM HUNIV HFRM HPOS HCONS HOUT HLED
  HLEN HMAX HLIVE HFPB HCH0 HEV HPM HC.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstat.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
destruct (ind_seat IND_K16 W1 regs regs1 memc) as (HS & SHOK).
- rewrite Hsp, Zminus_mod, Hal. reflexivity.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
- rewrite Hsp. exact V0.
- rewrite Hsp. replace (sp - 32 + 8) with (sp - 24) by lia. exact V8.
- rewrite Hsp. replace (sp - 32 + 16) with (sp - 16) by lia. exact V16.
- rewrite Hsp. replace (sp - 32 + 24) with (sp - 8) by lia. exact V24.
- rewrite Hsp. lia.
- set (E := Eimg (Ereg regs1 (ind_x16 regs))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 (ind_x16 regs)) kk)
    by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
  assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM ind_Bspan.
  { eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- (32 + d)));
    [reflexivity | rewrite Usp, Hsp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  (* the stop is put's entry: the stretch slots 16..18 (li a2,2; mv a0,s1; mv a1,s2) stores nothing, so ra = A_TEXT +
     IND_K20, a0 = s1 = o, a1 = s2 = IND_SP, a2 = 2 (measured, the internal file build-20261029T092817Z.log) *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Rra. prreg_norm Rra.
  prreg HS (2%bv : bv 5) R2. prreg_norm R2.
  prreg HS (3%bv : bv 5) Rgp. prreg_norm Rgp.
  prreg HS (4%bv : bv 5) Rtp. prreg_norm Rtp.
  prreg HS (8%bv : bv 5) R8. prreg_norm R8.
  prreg HS (9%bv : bv 5) R9. prreg_norm R9.
  prreg HS (10%bv : bv 5) R10. prreg_norm R10.
  prreg HS (11%bv : bv 5) R11. prreg_norm R11.
  prreg HS (12%bv : bv 5) R12. prreg_norm R12.
  assert (E3 : ew E 3 = getr regs1 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs1 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
  assert (E8 : ew E 8 = getr regs1 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 8 8%bv eq_refl)).
  assert (E9 : ew E 9 = getr regs1 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 9 9%bv eq_refl)).
  assert (E18 : ew E 18 = getr regs1 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 18 18%bv eq_refl)).
  rewrite ?E3, ?Hgp in Rgp. rewrite ?E4, ?Htp in Rtp. rewrite E8, H8 in R8. rewrite E9, H9 in R9, R10.
  rewrite E18, H18 in R11.
  assert (K20 : BASE + IND_K20 = BASE + ltac:(ind_lit IND_K20)) by (f_equal; vm_compute; reflexivity).
  rewrite <- K20 in Rra.
  assert (Rsp : spZ (ms_regs ms) = sp - 32) by (unfold spZ; rewrite R2, E2; exact Hsp).
  (* memory: the seated frame is read-only and the stretch stores nothing, so the view agrees everywhere *)
  assert (NOW : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc a).
  { intros a Ha. apply aview_eq_of. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by lia. intros (rr & Hrr & Hra').
    unfold ind_ssk in Hrr. cbn [ss_mem In] in Hrr. destruct Hrr as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hra'. lia. }
  pose proof (@alloc_ceiling_value rc) as HCV.
  assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc a)
    by (intros a Ha; apply NOW; lia).
  assert (HSTR : forall a, o <= a < o + 32 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc a)
    by (intros a Ha; apply NOW; lia).
  (* the call's premises at the stop's memory *)
  assert (HARc : ARx lyc Sc Hpc W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1))
    by exact (ajxR_ar HJ).
  assert (HRO2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W1) (ms_mem ms))).
  { intros a Hro Hown Herr. rewrite NOW; [exact (HRO a Hro Hown Herr)|].
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)]).
    destruct Hi as (sg & Hsg & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))). unfold kLowMemEnd in *. lia. }
  destruct (HLIT lyc Sc Hpc W1 (ms_mem ms) _ HARc HRO2) as (_ & HSRC & HKSP).
  assert (Hbok : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
  { intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction | exact Hin]. }
  assert (Hc0 : 0 <= WriterApp.w_cap st) by (destruct HOUT as (_ & _ & Hcr & _); lia).
  assert (Hbufb : WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling).
  { intros Hc. pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
    pose proof (proj1 (Forall_forall _ _) Hbl _ (Hbok Hc)) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & Hp4 & Hpcb & _).
    pose proof (@cf_head_nonneg cp) as Hch0.
    match type of Hpcb with context [req_size ?x] =>
      assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
    rewrite Hreq in Hpcb. lia. }
  pose proof (ind_out_kept W1 memc (ms_mem ms) Lam o buf st HLOW HSTR Hbufb HOUT) as HOUT2.
  pose proof (ind_ledger_kept lyc Sc Hpc W1 memc (ms_mem ms) md1 Lam peak _ _ ran HAR HLOW HLED) as HLED2.
  pose proof (ind_src_home lyc Sc Hpc W1 (ms_mem ms) _ Lam peak _ _ ran buf st IND_SP 2 HARc HLED2 Hbok Hc0
    ltac:(lia) HKSP) as HHOME.
  (* BASE is the image instance's text base (a field of PA): never vm_compute a term that holds it *)
  pose proof (@pa_B_ok _ _ PA) as HBASE.
  assert (RTO : YK0s.ret_ok (Z_to_bv 64 (BASE + IND_K20))) by (rewrite K20; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (R4096 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + IND_K20))) by (rewrite K20, unsigned_lit_small by lia; lia).
  (* the return pc of the jal is a listing slot, below the ceiling (PRW_StepKit.pa_slot_lt_ceil_b, WalkS7b) *)
  assert (RLT : bv_unsigned (Z_to_bv 64 (BASE + IND_K20)) < YM05.alloc_ceiling)
    by (rewrite K20, unsigned_lit_small by lia;
        exact (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) ltac:(ind_lit IND_K20) ltac:(lia) ltac:(vm_compute; reflexivity))).
  assert (HCH : achain lyc (aview SEGS (w_H W1) (ms_mem ms)) (sp - 32) (s0Z (ms_regs ms)) []).
  { left. split; [left | reflexivity]. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia. }
  (* every callee-saved register at the stop is the seat's: the stretch writes only a0, a1, a2 *)
  assert (CS : forall rr, acallee_saved rr -> getr (ms_regs ms) (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)).
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
                  rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    repeat destruct Hr' as [-> | Hr']; try subst rr;
    match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
      let Hq := fresh "Hq" in prreg HS (Z_to_bv 5 n) Hq; rewrite Hq end;
    rewrite EL by (unfold A_TEXT; lia);
    match goal with |- ew _ ?m = getr _ ?rg => exact (ew_Ereg_nat regs1 _ m rg eq_refl) end. }
  assert (HCHO : spZ (ms_regs ms) + 16 <= o ->
    exists ra, rdword (aview SEGS (w_H W1) (ms_mem ms)) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W1) (ms_mem ms)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
  { rewrite Rsp. intros Hc. apply (ind_rec_kept (aview SEGS (w_H W1) memc) _ o); [| exact (HCH0 Hc)].
    intros a Ha. apply NOW. lia. }
  eapply (SRr'_bind SEGS RZ_cf).
  { exact (ind_call_put_P P PLAW PCALL W W1 (ms_regs ms) (ms_mem ms) _ FP ly S Hp mem md lyc Sc Hpc k sp d o IND_SP [32; 32]
      buf st Lam peak ran (Z_to_bv 64 (BASE + IND_K20)) [] rp_i rp_hist
      HJ Rsp Hal Hd0 Hd16 Rgp Rtp Rra RTO R4096 RLT HCH HRO2 HROOM HUNIV HFRM HTOP HPOS HCONS R10 R11 R12 Hol Hoh
      HOUT2 HLED2 HSRC HHOME HLEN HMAX HLIVE HFPB HCHO HEV HPM). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HWK & HP & HQ1 & HQP & HQ2 & HPM2).
  apply (HC ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HJ2).
  + intros a Ha Hn. rewrite (HWK a Ha Hn). apply NOW. lia.
  + intros rr Hrr. rewrite (HP rr Hrr). exact (CS rr Hrr).
  + exact HQ1.
  + exact HQP.
  + exact HQ2.
  + exact HPM2.
Qed.

(* ---- the loop latch (slot 20: addiw s0, s0, -1; bnez s0 -> slot 16, else slot 22) from a fresh seat, in
   continuation form: the count drops by one, memory is unchanged (the seat is read-only), every other callee-saved
   register is kept, and the journal is the same one ---- *)
Lemma ind_latch_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W mem md ly1 S1 Hp1 W1 (regs regs1 : bvmap 5 word) mem1 md1 k1 FP sp d cnt
    (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
    ly1 S1 Hp1 W1 mem1 md1 k1 -> P mem1 ->
  spZ regs1 = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> 2 ^ 46 <= sp - 32 -> sp + d <= 2 ^ 47 ->
  getr regs1 8 = Z_to_bv 64 cnt -> 1 <= cnt < 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
       ly1 S1 Hp1 W1 mem3 md3 k1 -> P mem3 ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a) ->
     getr regs3 8 = Z_to_bv 64 (cnt - 1) ->
     (forall rr, acallee_saved rr -> rr <> 8 -> getr regs3 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)) ->
     SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + (if cnt - 1 =? 0 then IND_K22 else IND_K16))) mem3
       (YK11.seg_rom SEGS)) md3) Q) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K20)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RUNTOI := paj_run_to_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
intros ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d cnt Q HJ HPM Hsp Hal Hd0 Hd16 Hlo Hhi
  H8 Hr V0 V8 V16 V24 HK.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstat.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
destruct (ind_seat IND_K20 W1 regs regs1 mem1) as (HS & SHOK).
- rewrite Hsp, Zminus_mod, Hal. reflexivity.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
- rewrite Hsp. exact V0.
- rewrite Hsp. replace (sp - 32 + 8) with (sp - 24) by lia. exact V8.
- rewrite Hsp. replace (sp - 32 + 16) with (sp - 16) by lia. exact V16.
- rewrite Hsp. replace (sp - 32 + 24) with (sp - 8) by lia. exact V24.
- rewrite Hsp. lia.
- set (E := Eimg (Ereg regs1 (ind_x16 regs))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 (ind_x16 regs)) kk)
    by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
  assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
  assert (E8 : ew E 8 = Z_to_bv 64 cnt) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
  assert (D0 : forall (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = w).
  { intros n w Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  assert (DEC : sv_denot E (SAluw ALU_ADD (SOff 8 0) (SLit (-1))) = Z_to_bv 64 (cnt - 1)) by (apply ind_dec; [exact E8 | lia]).
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM ind_Bspan.
  { eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- (32 + d)));
    [reflexivity | rewrite Usp, Hsp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  psrr_branch_tokR RUN BRR HS SHOK ind_Bspan.
  all: match goal with Hc : branch_taken _ _ _ = ?bb |- _ =>
    rewrite branch_ne_U in Hc; unfold U in Hc; rewrite DEC in Hc;
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc;
    rewrite !unsigned_lit_small in Hc by lia end.
  all: match goal with Hc : negb (?x =? 0) = ?bb |- _ =>
    first [ assert (Hz : x <> 0) by (destruct (Z.eqb_spec x 0); [discriminate Hc | assumption])
          | assert (Hz : x = 0) by (destruct (Z.eqb_spec x 0); [assumption | discriminate Hc]) ] end.
  (* the taken arm runs to the loop head, the other to the epilogue *)
  1: paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM ind_Bspan IND_K16.
  3: paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM ind_Bspan IND_K22.
  all: try (eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- (32 + d)));
    [reflexivity | rewrite Usp, Hsp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]).
  (* both runs ran from read-only seats: memory is the seat's everywhere *)
  all: assert (MEM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; apply aview_eq_of; rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |];
        rewrite unsigned_lit_small by lia; intros (rr & Hrr & Hra');
        match type of Hrr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hrr end;
        destruct Hrr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; lia).
  all: rewrite (st_ok_pi_restrict_mkst (w_H W1) E _ ms0 HS ltac:(vm_compute; reflexivity)).
  all: assert (GR : forall rr : bv 5, getr (ms_regs ms0) rr = sv_denot E (sr_get (ss_regs _) rr))
         by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms0 rr HS)).
  all: match goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (BASE + ?pc)) _ _ |} _ =>
    let v := eval vm_compute in pc in change pc with v end.
  all: first
    [ match type of Hz with ?x <> 0 =>
        replace (ltac:(ind_lit IND_K16) : Z) with (if x =? 0 then IND_K22 else IND_K16)
          by (destruct (Z.eqb_spec x 0); [contradiction | vm_compute; reflexivity]) end
    | match type of Hz with ?x = 0 =>
        replace (ltac:(ind_lit IND_K22) : Z) with (if x =? 0 then IND_K22 else IND_K16) by (rewrite Hz; vm_compute; reflexivity) end ].
  all: apply (HK (ms_regs ms0) (ms_mem ms0) _ HJ HPM MEM).
  all: try (rewrite GR; match goal with |- sv_denot ?E0 ?e = _ => let v := eval vm_compute in e in change e with v end;
            exact DEC).
  all: intros rr Hrr Hn8; unfold acallee_saved in Hrr;
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
                  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
    rewrite GR; repeat destruct Hr' as [-> | Hr']; try subst rr;
    match goal with |- sv_denot ?E0 ?e = _ => let v := eval vm_compute in e in change e with v end;
    apply D0; rewrite EL by (unfold A_TEXT; lia);
    match goal with |- ew _ ?n = getr _ ?rg => exact (ew_Ereg_nat regs1 _ n rg eq_refl) end.
Qed.

(* the old statement, the P := fun _ => True corollary of ind_latch_P (byte-identical to 6492e80df47) *)
Lemma ind_latch : forall ly S Hp W mem md ly1 S1 Hp1 W1 (regs regs1 : bvmap 5 word) mem1 md1 k1 FP sp d cnt
    (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
    ly1 S1 Hp1 W1 mem1 md1 k1 ->
  spZ regs1 = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> 2 ^ 46 <= sp - 32 -> sp + d <= 2 ^ 47 ->
  getr regs1 8 = Z_to_bv 64 cnt -> 1 <= cnt < 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
       ly1 S1 Hp1 W1 mem3 md3 k1 ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a) ->
     getr regs3 8 = Z_to_bv 64 (cnt - 1) ->
     (forall rr, acallee_saved rr -> rr <> 8 -> getr regs3 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)) ->
     SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + (if cnt - 1 =? 0 then IND_K22 else IND_K16))) mem3
       (YK11.seg_rom SEGS)) md3) Q) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K20)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d cnt Q HJ Hsp Hal Hd0 Hd16 Hlo Hhi
  H8 Hr V0 V8 V16 V24 HK.
apply (ind_latch_P (fun _ => True) ind_laws_true ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d cnt Q
  HJ I Hsp Hal Hd0 Hd16 Hlo Hhi H8 Hr V0 V8 V16 V24).
intros regs3 mem3 md3 HJ3 _ MEM H83 HCS3. exact (HK regs3 mem3 md3 HJ3 MEM H83 HCS3).
Qed.

(* ---- the epilogue (slot 22 to the return at slot 27) from a fresh seat: it reloads ra, s0, s1, s2 from indent's
   frame and pops it, so every callee-saved register is the entry's again, and memory changes nowhere outside the
   frame; the run of puts made so far (its post prhWriter_ret over P) is carried to the return ---- *)
Lemma ind_epi_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W (regs : bvmap 5 word) mem md ly1 S1 Hp1 W1 (regs1 : bvmap 5 word) mem1 md1 k1 d
    o buf (st : WriterApp.wst) Lam peak ran PP (rp_i : nat),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 -> P mem1 ->
  spZ regs1 = spZ regs - 32 -> spZ regs mod 16 = 0 -> 0 <= d -> d mod 16 = 0 ->
  2 ^ 46 <= spZ regs - 32 -> spZ regs + d <= 2 ^ 47 -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  YK0s.ret_ok (getr regs 1) ->
  (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
     aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  room_live_cf S1 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st PP ly1 S1 Hp1 W1 regs1 mem1 md1 ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K22)) mem1 (YK11.seg_rom SEGS)) md1)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st PP ly' S' Hp' W' regs' mem' md') /\
          P mem')).
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
intros ly S Hp W regs mem md ly1 S1 Hp1 W1 regs1 mem1 md1 k1 d o buf st Lam peak ran PP rp_i
  HJ HPM Hsp Hal Hd0 Hd16 Hlo Hhi Hol Hoh Hra HCS V0 V8 V16 V24 HWK HROOM HRET.
pose proof (ajxR_ar HJ) as HAR1. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstat.
pose proof Hstat as (_ & _ & Hceil & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
destruct (ind_seat IND_K22 W1 regs regs1 mem1) as (HS & SHOK).
- rewrite Hsp, Zminus_mod, Hal. reflexivity.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
- rewrite Hsp. exact V0.
- rewrite Hsp. replace (spZ regs - 32 + 8) with (spZ regs - 24) by lia. exact V8.
- rewrite Hsp. replace (spZ regs - 32 + 16) with (spZ regs - 16) by lia. exact V16.
- rewrite Hsp. replace (spZ regs - 32 + 24) with (spZ regs - 8) by lia. exact V24.
- rewrite Hsp. lia.
- set (E := Eimg (Ereg regs1 (ind_x16 regs))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 (ind_x16 regs)) kk)
    by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
  assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
  assert (E32 : ew E 32 = getr regs 18) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
  assert (E33 : ew E 33 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
  assert (E34 : ew E 34 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
  assert (E35 : ew E 35 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
  assert (D0 : forall (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = w).
  { intros n w Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  paj_run_tok_x_invR RUNI HS HJ SHOK HPM ind_Bspan.
  { eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- (32 + d)));
    [reflexivity | rewrite Usp, Hsp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  try rewrite wvb_collapse in HJ.
  (* the return: a step that keeps the world, lifted to SRr' *)
  apply (SRr_SRr' SEGS RZ_cf).
  apply (RET W1 E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat1.
  assert (GR : forall rr : bv 5, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs _) rr))
    by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms rr HS)).
  assert (HP : aregs_preserved regs (ms_regs ms)).
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    rewrite GR.
    repeat destruct Hr' as [-> | Hr']; try (subst r);
      match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end.
    all: first
      [ (cbn [sv_denot]; rewrite Usp, Hsp, Z.sub_add; apply Z_to_bv_bv_unsigned)
      | (apply D0; first [exact E32 | exact E33 | exact E34])
      | (apply D0; rewrite EL by (unfold A_TEXT; lia);
         match goal with |- ew _ ?n = getr _ ?r => rewrite (ew_Ereg_nat regs1 _ n r eq_refl) end;
         apply HCS; lia) ]. }
  assert (Hra1 : getr (ms_regs ms) 1 = getr regs 1).
  { rewrite GR. match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end.
    apply D0. exact E35. }
  (* only indent's frame [sp - 32, sp) is in the seated state's write windows *)
  assert (NOW : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 32 \/ spZ regs <= a) ->
    aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha Hout.
    assert (NW : forall rs, (forall r, In r rs -> YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = 0 /\ YP09.r_whi r = 0) ->
      ~ in_wrange E rs a).
    { intros rs Hrs (r & Hr & Hra'). destruct (Hrs r Hr) as (Hb & Hl & Hh). rewrite Hb, Hl, Hh in Hra'.
      cbn [base_val] in Hra'. rewrite Usp, Hsp in Hra'. lia. }
    apply aview_eq_of. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by lia. apply NW. intros r Hr.
    unfold ind_ssk in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. repeat split; reflexivity. }
  pose proof (@alloc_ceiling_value rc) as HCV.
  pose proof Hstat as (_ & _ & _ & Hslo & Hshi & _).
  assert (HCB : YM05.alloc_ceiling <= spZ regs - 32) by lia.
  assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; apply NOW; lia).
  pose proof (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low rc A_prog_listing PA)
      (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) as HJ1.
  try rewrite wvb_collapse in HJ1.
  exists ly1, S1, Hp1, (ms_regs ms), (ms_mem ms).
  match type of HJ1 with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ => exists mdx end.
  exists k1.
  split.
  { try rewrite wvb_collapse. rewrite Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split; [exact HJ1|].
  split; [intros a Ha Hn; rewrite NOW by lia; exact (HWK a Ha Hn)|].
  split; [exact HP|].
  split; [|exact HPM].
  split; [exact HROOM|].
  destruct HRET as (ok & HRO1 & G1 & HPOS).
  destruct (prhWriter_blk_of_ret_ok B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRO1 G1)
    as (ran' & buf' & Lam' & peak' & Hoks & HOUT1 & HLED1 & HBLK).
  exists ok. split; [|split; [exact G1 | exact HPOS]].
  apply (prhWriter_ret_ok_of_blk B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ran' buf' Lam' peak' Hoks);
    [| | exact HBLK | exact G1].
  + apply (ind_out_kept W1 mem1 (ms_mem ms) Lam' o buf'); [exact HLOW | intros a Ha; apply NOW; lia | | exact HOUT1].
    intros Hc. pose proof HLED1 as Hbl. apply prh_ledger_blocks in Hbl.
    destruct HOUT1 as (_ & _ & Hcr & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction|].
    pose proof (proj1 (Forall_forall _ _) Hbl _ Hin) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR1 Hinb) as (_ & Hp4 & Hpc & _).
    pose proof (@cf_head_nonneg cp) as Hch0.
    match type of Hpc with context [req_size ?x] =>
      assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
    rewrite Hreq in Hpc. lia.
  + apply (ind_ledger_kept ly1 S1 Hp1 W1 mem1 (ms_mem ms) md1); [exact HAR1 | exact HLOW | exact HLED1].
Qed.

(* the P := fun _ => True corollary of ind_epi_P; its premise and post moved for the TEXT (kit-oldpin b501d43ce5af's
   exact advance, tindent_specX :455-461) *)
Lemma ind_epi : forall ly S Hp W (regs : bvmap 5 word) mem md ly1 S1 Hp1 W1 (regs1 : bvmap 5 word) mem1 md1 k1 d
    o buf (st : WriterApp.wst) Lam peak ran P (rp_i : nat),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
  spZ regs1 = spZ regs - 32 -> spZ regs mod 16 = 0 -> 0 <= d -> d mod 16 = 0 ->
  2 ^ 46 <= spZ regs - 32 -> spZ regs + d <= 2 ^ 47 -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  YK0s.ret_ok (getr regs 1) ->
  (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
     aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  room_live_cf S1 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st P ly1 S1 Hp1 W1 regs1 mem1 md1 ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K22)) mem1 (YK11.seg_rom SEGS)) md1)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st P ly' S' Hp' W' regs' mem' md')).
Proof.
intros ly S Hp W regs mem md ly1 S1 Hp1 W1 regs1 mem1 md1 k1 d o buf st Lam peak ran P rp_i
  HJ Hsp Hal Hd0 Hd16 Hlo Hhi Hol Hoh Hra HCS V0 V8 V16 V24 HWK HROOM HRET.
eapply (SRr'_mono SEGS RZ_cf); [exact (ind_epi_P (fun _ => True) ind_laws_true ly S Hp W regs mem md ly1 S1 Hp1 W1 regs1 mem1 md1 k1
  d o buf st Lam peak ran P rp_i HJ I Hsp Hal Hd0 Hd16 Hlo Hhi Hol Hoh Hra HCS V0 V8 V16 V24 HWK HROOM HRET)|].
intros W' c' _ H. exact (ind_fpostW_drop _ _ _ _ _ _ _ _ _ _ _ (fun _ => True) _ _ H).
Qed.
(* ---- block bookkeeping for the loop (WalkS7b's PRW_pj_write.v pjw_pair_dec / pjw_two_in_split / pjw_fresh_block,
   restated here over this file's names): a block at the head of a permutation of the later block list is not in the
   rest - two copies of a nonempty block would break the allocator's pairwise disjointness ---- *)
Definition ind_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma ind_two_in_split : forall (x : Z * Z) (l : list (Z * Z)),
  (2 <= count_occ ind_pair_dec l x)%nat ->
  exists l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3.
Proof.
intros x l. induction l as [|a l IH]; cbn [count_occ]; [lia|].
destruct (ind_pair_dec a x) as [->|Hne]; intros Hc.
- assert (Hin : In x l) by (apply (count_occ_In ind_pair_dec); lia).
  apply in_split in Hin as (m1 & m2 & ->). exists [], m1, m2. reflexivity.
- destruct (IH Hc) as (l1 & l2 & l3 & ->). exists (a :: l1), l2, l3. reflexivity.
Qed.

Lemma ind_fresh_block : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 x l,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> Permutation (ablocks B ly2 S2) (x :: l) -> 0 < req_size (snd x) ->
  ~ In x l.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 x l HAR Hperm Hpos Hin.
assert (Hx2 : In x (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hc : (2 <= count_occ ind_pair_dec (ablocks B ly2 S2) x)%nat).
{ rewrite (proj1 (Permutation_count_occ ind_pair_dec _ _) Hperm x).
  cbn [count_occ]. destruct (ind_pair_dec x x) as [_|Hne]; [|exfalso; exact (Hne eq_refl)].
  pose proof (proj1 (count_occ_In ind_pair_dec l x) Hin). lia. }
destruct (ind_two_in_split x _ Hc) as (m1 & m2 & m3 & Hsp).
destruct x as [p nn]. cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p nn HAR Hx2) as (_ & _ & _ & _ & _ & Hpw).
pose proof (YCbq.pairwise_In2 zdisjoint
  (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly2 S2))
  (p, req_size nn) (p, req_size nn)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m1)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m2)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) m3) Hpw) as Hd.
rewrite Hsp, !map_app in Hd. cbn [map] in Hd. rewrite ?map_app in Hd. cbn [map] in Hd. specialize (Hd eq_refl).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- the writer's buffer is an allocator block below alloc_ceiling ---- *)
Lemma ind_buf_bound : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran o buf (st : WriterApp.wst),
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  prhWriter_out W mem Lam o buf st ->
  WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran o buf st HAR HLED HOUT Hc.
pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
destruct HOUT as (_ & _ & Hcr & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction|].
pose proof (proj1 (Forall_forall _ _) Hbl _ Hin) as (Hk0 & Hinb & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & Hp4 & Hpc & _).
pose proof (@cf_head_nonneg cp) as Hch0.
match type of Hpc with context [req_size ?x] =>
  assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
rewrite Hreq in Hpc. lia.
Qed.

(* ---- the writer footprint opens no sink: the struct is on the stack, the buffer block's base is >= 4096 ---- *)
Lemma ind_cfp_nosink : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran o buf (st : WriterApp.wst),
  ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  (WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam) -> 0 < o ->
  ~ YI16.sink_open_fp (prhWriter_cfp o buf (WriterApp.w_cap st)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran o buf st HAR HLED HIN Ho (r & Hr & Hr0).
cbn [prhWriter_cfp In] in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Hr0; lia|].
unfold prhWriter_fp in Hr.
destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [Hz | Hnz]; [destruct Hr|].
pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
pose proof (proj1 (Forall_forall _ _) Hbl _ (HIN Hnz)) as (_ & Hinb & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & Hp4 & _).
cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hr0. lia.
Qed.

(* ---- the current buffer is the entry's (in FP) or a block made since the entry ---- *)
Lemma ind_fp_tmp : forall ly S Lam peak buf (st : WriterApp.wst) ly1 S1 Hp1 (W1 : world SEGS) mem1 md1 Lam1 peak1 buf1
    (st1 : WriterApp.wst) o,
  ARx ly1 S1 Hp1 W1 mem1 md1 -> 0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 st1 ->
  forall a, inFP (prhWriter_fp buf1 (WriterApp.w_cap st1)) a ->
    inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a \/ in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a.
Proof.
intros ly S Lam peak buf st ly1 S1 Hp1 W1 mem1 md1 Lam1 peak1 buf1 st1 o HAR1 Hc0
  [(Hc & -> & _ & _ & _) | (Hlt & l1 & l2 & b1 & b2 & Harm & _ & _ & HP)] a Ha.
- left. rewrite Hc in Ha. destruct Ha as (r & Hr & Hra). exists r. split; [right; exact Hr | exact Hra].
- right. unfold prhWriter_fp in Ha. rewrite (proj2 (Z.eqb_neq (WriterApp.w_cap st1) 0)) in Ha by lia.
  destruct Ha as (r & Hr & Hra). cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra.
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hpos : 0 < req_size (WriterApp.w_cap st1 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st1 + cf_head) 0); cbv iota; lia).
  pose proof (ind_fresh_block ly1 S1 Hp1 W1 mem1 md1 (buf1 - cf_head, WriterApp.w_cap st1 + cf_head) (b1 ++ b2)
    HAR1 HP Hpos) as Hfr.
  exists (buf1 - cf_head), (WriterApp.w_cap st1 + cf_head). split; [|split; [|exact Hra]].
  + eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity].
  + destruct Harm as [(Hz & _ & _ & Hb1 & Hb2) | (Hnz & _ & Hab)].
    * subst b1. rewrite <- Hb2. exact Hfr.
    * rewrite Hab. intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | [Heq | Hin]].
      -- apply Hfr. apply in_or_app. left. exact Hin.
      -- injection Heq as _ Heq2. lia.
      -- apply Hfr. apply in_or_app. right. exact Hin.
Qed.

(* ---- the writer's capacity is on its grid ---- *)
Lemma ind_out_grid : forall (W : world SEGS) mem Lam o buf (st : WriterApp.wst),
  prhWriter_out W mem Lam o buf st -> prhWriter_capgrid (WriterApp.w_cap st).
Proof.
intros W mem Lam o buf st (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (Hg & _)]); [left; exact Hz | right; exact Hg].
Qed.

(* ---- a run's writer post and its position move to a memory that agrees everywhere (the latch's read-only seat,
   the stop after k13): the outcomes ok and the state S2 are kept ---- *)
Lemma ind_retpos_mem : forall ly S Lam peak ran o buf (st : WriterApp.wst) PP ly2 S2 Hp2 (W2 : world SEGS) regs2 mem2
    md2 regs3 mem3 md3 rp_i,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st PP ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st PP ly2 S2 Hp2 W2 regs3 mem3 md3.
Proof.
intros ly S Lam peak ran o buf st PP ly2 S2 Hp2 W2 regs2 mem2 md2 regs3 mem3 md3 rp_i HAR2 Ho0 Ho64 MEM
  (ok & HRO2 & G2 & HPOS).
destruct (prhWriter_blk_of_ret_ok B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRO2 G2)
  as (ran' & buf' & Lam' & peak' & Hoks & HOUT & HLED & HBLK).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply MEM; lia).
exists ok. split; [|split; [exact G2 | exact HPOS]].
apply (prhWriter_ret_ok_of_blk B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ran' buf' Lam' peak' Hoks);
  [| | exact HBLK | exact G2].
- apply (ind_out_kept W2 mem2 mem3 Lam' o buf' _ HLOW); [intros a Ha; apply MEM; lia | | exact HOUT].
  exact (ind_buf_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR2 HLED HOUT).
- exact (ind_ledger_kept ly2 S2 Hp2 W2 mem2 mem3 md2 _ _ _ _ _ HAR2 HLOW HLED).
Qed.

(* ---- the run's pieces: a newline, then pairs of spaces ---- *)
Lemma ind_rep_len : forall m, length (concat (repeat [32; 32] m)) = (2 * m)%nat.
Proof. induction m as [|m IH]; [reflexivity|]. cbn [repeat concat]. rewrite app_length, IH. cbn [length]. lia. Qed.

Lemma ind_rep_snoc : forall (x : list Z) m, repeat x m ++ [x] = repeat x (S m).
Proof. intros x m. induction m as [|m IH]; [reflexivity|]. cbn [repeat app]. rewrite IH. reflexivity. Qed.

Lemma ind_wind_split : forall (j m : nat) depth, (j + m)%nat = Z.to_nat depth ->
  WriterValue.wind true depth = ([10] :: repeat [32; 32] j) ++ repeat [32; 32] m.
Proof.
intros j m depth Hjm. unfold WriterValue.wind. rewrite <- Hjm, repeat_app. reflexivity.
Qed.

(* ---- one more round fits the text budget of indent's whole run ---- *)
Lemma ind_round_budget : forall ok (st : WriterApp.wst) (j m : nat) depth,
  (j + S m)%nat = Z.to_nat depth ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (WriterValue.wind true depth))) + 1
    <= prhWriter_WMAX ->
  Z.of_nat (length (WriterApp.w_text (prhWriter_putN ok st ([10] :: repeat [32; 32] j)))) + 2 + 1
    <= prhWriter_WMAX.
Proof.
intros ok st j m depth Hjm HLB.
pose proof (prhWriter_putN_len_le ok st ([10] :: repeat [32; 32] j)) as H1.
cbn [concat] in H1. rewrite app_length, ind_rep_len in H1. cbn [length] in H1.
rewrite (ind_wind_split j (S m) depth Hjm), concat_app in HLB. cbn [concat] in HLB.
rewrite !app_length, !ind_rep_len in HLB. cbn [length] in HLB. lia.
Qed.

(* ---- one more round's put has its live room at each event (the batch kit's prh_live_evs), from indent's at its entry over
   its whole run (S7a_WriterRet.prhWriter_live_evs_at; the allocator moved by the buffer's change only,
   prhWriter_blk_bb) ---- *)
Lemma ind_round_live : forall ly S Lam peak buf (st : WriterApp.wst) ly1 S1 Lam1 peak1 buf1 ok (j m : nat) depth,
  (j + Datatypes.S m)%nat = Z.to_nat depth ->
  0 <= WriterApp.w_cap st ->
  prhWriter_blk B ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 (prhWriter_putN ok st ([10] :: repeat [32; 32] j)) ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wind true depth)) ->
  prh_live_evs S1 (prhWriter_evs [] (prhWriter_putN ok st ([10] :: repeat [32; 32] j)) [[32; 32]]).
Proof.
intros ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 ok j m depth Hjm Hc0 HBLK HLV.
pose proof (prhWriter_blk_bb B ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 _ Hc0 HBLK) as HBB.
rewrite (ind_wind_split j (Datatypes.S m) depth Hjm) in HLV. cbn [repeat] in HLV.
exact (prhWriter_live_evs_at S S1 st ([10] :: repeat [32; 32] j) [32; 32] (repeat [32; 32] m) ok Hc0 HLV HBB).
Qed.

(* ---- the space loop, from the loop head with n rounds left: n rounds (ind_body, then ind_latch), then the epilogue
   (ind_epi); the run of puts grows from [10] :: (depth - n) space pairs to indent's whole run wind true depth ---- *)
Lemma ind_iter_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall (n : nat) ly S Hp W (regs : bvmap 5 word) mem md ch o depth d buf (st : WriterApp.wst)
    Lam peak ran (rp_i : nat) ly1 S1 Hp1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 k1,
  fpre B ARx STK_indent ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  spZ regs + 16 <= o ->
  (exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  2 ^ 46 <= spZ regs - 32 -> spZ regs + d <= 2 ^ 47 ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat (WriterValue.wind true depth))) + 1
    <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wind true depth)) ->
  (1 <= n)%nat -> Z.of_nat n <= depth < 2 ^ 31 ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 -> P mem1 ->
  spZ regs1 = spZ regs - 32 ->
  (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  getr regs1 8 = Z_to_bv 64 (Z.of_nat n) -> getr regs1 9 = w64 o -> getr regs1 18 = w64 IND_SP ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
     aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  room_live_cf S1 ->
  prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st
    ([10] :: repeat [32; 32] (Z.to_nat depth - n)) ly1 S1 Hp1 W1 regs1 mem1 md1 ->
  (* indent's entry premise (tindent_specX :667), constant through the loop *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wind true depth)) ->
  (* indent's consumer window (tindent_specX, the batch kit), constant through the loop *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st (WriterValue.wind true depth))) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K16)) mem1 (YK11.seg_rom SEGS)) md1)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st (WriterValue.wind true depth)
            ly' S' Hp' W' regs' mem' md') /\
          P mem')).
Proof.
intros P PLAW PCALL.
induction n as [|n IH];
  intros ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i ly1 S1 Hp1 W1 regs1 mem1 md1 k1
    HPRE HUNIV HWIN Hol Hoh Hcut HCHe Hlo Hhi HOUT HLED HLENT HMAX HLIVET Hn Hdep HJ HPM Hsp HCS H8 H9 H18 V0 V8 V16 V24 HWK
    HROOM HRET HEVS HCONSE; [lia|].
pose proof HPRE as (HAP & HROe & HSTKTOP). pose proof HSTKTOP as (_ & _ & HFRM).
pose proof HAP as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & _).
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof (ajxR_ar HJ) as HAR1. pose proof (ajxR_ly HJ) as HLE.
assert (HTOP1 : spZ regs + 32 <= ly_stk_hi ly1)
  by (destruct HLE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _); rewrite Hsh; lia).
assert (Hc0e : 0 <= WriterApp.w_cap st) by (destruct HOUT as (_ & _ & Hcr & _); lia).
assert (Hboke : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction | exact Hin]. }
assert (HcntW : 0 <= WriterApp.w_cnt st)
  by (pose proof HLED as Hbd; apply prh_ledger_bounds in Hbd; destruct Hbd as (_ & _ & Hc & _); lia).
assert (HNS : ~ YI16.sink_open_fp (prhWriter_cfp o buf (WriterApp.w_cap st)))
  by (apply (ind_cfp_nosink ly S Hp W mem md Lam peak _ _ ran o buf st HARe HLED Hboke); lia).
pose proof (ind_arodata_kept _ _ _ ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 HJ HNS HROe) as HRO1.
(* the writer's state now, and the position at the exact advance of its outcomes ok *)
destruct HRET as (ok & HRK & G1 & rp_hist1 & HPOS1).
destruct (prhWriter_blk_of_ret_ok B ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRK G1)
  as (ran1 & buf1 & Lam1 & peak1 & Hoks & HOUT1 & HLED1 & HBLK).
assert (Hjm : (Z.to_nat depth - Datatypes.S n + Datatypes.S n)%nat = Z.to_nat depth) by lia.
pose proof (ind_round_budget ok st (Z.to_nat depth - Datatypes.S n) n depth Hjm HLENT) as HLEN1.
pose proof (ind_round_live ly S Lam peak buf st ly1 S1 Lam1 peak1 buf1 ok (Z.to_nat depth - Datatypes.S n) n depth Hjm
  Hc0e HBLK HLIVET) as HLIVE1.
(* the loop call's consumer window: indent's, split after the puts made so far (prhWriter_cons_at) *)
assert (HCONS1 : PRH_Base.prh_cons_from rp_sm rp_x rp_os
  (Nat.add rp_i (length (prhWriter_evs ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n)))))
  (length (prhWriter_evs [] (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))) [[32; 32]]))).
{ apply (prhWriter_cons_at rp_sm rp_x rp_os rp_i st _ [32; 32] (repeat [32; 32] n) ok).
  pose proof HCONSE as HE. rewrite (ind_wind_split (Z.to_nat depth - Datatypes.S n) (Datatypes.S n) depth Hjm) in HE.
  exact HE. }
pose proof (ind_fp_tmp ly S Lam peak buf st ly1 S1 Hp1 W1 mem1 md1 Lam1 peak1 buf1 _ o HAR1 Hc0e HBLK) as HFPB1.
assert (Hgp1 : getr regs1 3 = w64 (as_gp B)) by (rewrite <- Hgp; exact (HCS 3 ltac:(lia))).
assert (Htp1 : getr regs1 4 = w64 (as_tp B)) by (rewrite <- Htp; exact (HCS 4 ltac:(lia))).
assert (Hcnt1 : 1 <= Z.of_nat (Datatypes.S n) < 2 ^ 31) by lia.
pose proof (ind_buf_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR1 HLED1 HOUT1) as HB1.
assert (HCB : YM05.alloc_ceiling <= spZ regs - 32) by lia.
(* the round: indent's frame and its caller window outside the struct and the buffer are kept by put *)
assert (NOTCFP : forall a, spZ regs - 32 <= a < spZ regs + d -> ~ (o <= a < o + 32) ->
   ~ inFP (prhWriter_cfp o buf1 (WriterApp.w_cap (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))))) a).
{ intros a Ha Hno (r & Hr & Hrb). cbn [prhWriter_cfp In] in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Hrb; lia|].
  unfold prhWriter_fp in Hr.
  match type of Hr with context [?c =? 0] => destruct (Z.eqb_spec c 0) as [Hz | Hnz]; [destruct Hr|] end.
  cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hrb.
  destruct (HB1 Hnz) as (Hb0 & Hbc). pose proof HOUT1 as (_ & _ & Hcr1 & _).
  match type of Hrb with context [req_size ?x] =>
    assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
  rewrite Hreq in Hrb. lia. }
(* the loop call's one record: the 16 bytes below o lie in indent's caller window, outside the struct and the
   entry buffer (below alloc_ceiling), so every put kept them (HWK) and the entry record carries over *)
pose proof (ind_buf_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ HARe HLED HOUT) as HB0.
assert (NOTCFP0 : forall a, spZ regs <= a < o -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a).
{ intros a Ha (r & Hr & Hrb). cbn [prhWriter_cfp In] in Hr. destruct Hr as [<- | Hr]; [cbn [fst snd] in Hrb; lia|].
  unfold prhWriter_fp in Hr.
  match type of Hr with context [?c =? 0] => destruct (Z.eqb_spec c 0) as [Hz | Hnz]; [destruct Hr|] end.
  cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hrb.
  destruct (HB0 Hnz) as (Hb0 & Hbc).
  match type of Hrb with context [req_size ?x] =>
    assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
  rewrite Hreq in Hrb. lia. }
assert (HCH1 : spZ regs - 32 + 16 <= o ->
  exists ra, rdword (aview SEGS (w_H W1) mem1) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W1) mem1) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ intros _. apply (ind_rec_kept (aview SEGS (w_H W) mem) _ o); [| exact HCHe].
  intros a Ha. apply HWK; [lia | apply NOTCFP0; lia]. }
(* the loop call's run event: indent's entry list, split after the puts made so far (prhWriter_ev_at) *)
assert (HEV1 : prhWriter_grows (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))) [32; 32] = true ->
  WriterApp.w_cnt (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))) <>
    WriterApp.w_fail (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))) ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os)
    (Nat.add rp_i (length (prhWriter_evs ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))))) =
  Some (prhWriter_ev (prhWriter_putN ok st ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n))) [32; 32])).
{ apply (prhWriter_ev_at rp_sm rp_x rp_os rp_i _ st _ [32; 32] (repeat [32; 32] n) ok); [|reflexivity].
  pose proof HEVS as HE. rewrite (ind_wind_split (Z.to_nat depth - Datatypes.S n) (Datatypes.S n) depth Hjm) in HE.
  exact HE. }
eapply (ind_body_P P PLAW PCALL ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 (prhWriter_cfp o buf (WriterApp.w_cap st))
  (spZ regs) d o (Z.of_nat (Datatypes.S n)) buf1 _ Lam1 peak1 ran1 _ rp_hist1 _ HJ Hsp Hal Hd0 Hd16 Hlo Hhi HTOP1 Hol Hoh
  H8 Hcnt1 H9 H18 Hgp1 Htp1 V0 V8 V16 V24 HRO1 HAR1 HROOM HUNIV HFRM HPOS1 HCONS1 HOUT1 HLED1 HLEN1 HMAX HLIVE1 HFPB1 HCH1 HEV1 HPM).
intros ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HJ2 HWK2 HCS2 HROOM2 HPOS2 HRET2 HPM2.
pose proof (ajxR_ar HJ2) as HAR2.
(* the run so far plus this put, at the exact advance (prhWriter_ret_pos_step) *)
pose proof (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i _ rp_hist1 ly S Lam peak ran rmost rown o buf st
  ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n)) [32; 32]
  ok ran1 buf1 Lam1 peak1 ly1 S1 Hp1 W1 mem1 ly2 S2 Hp2 W2 regs2 mem2 md2 HcntW eq_refl Hoks G1 HOUT1 HLED1 HBLK
  HPOS2 HRET2) as HRET12.
assert (EP : ([10] :: repeat [32; 32] (Z.to_nat depth - Datatypes.S n)) ++ [[32; 32]] =
             [10] :: repeat [32; 32] (Z.to_nat depth - n)).
{ cbn [app]. f_equal. rewrite ind_rep_snoc. f_equal. lia. }
rewrite EP in HRET12.
assert (FR2 : forall a, spZ regs - 32 <= a < spZ regs -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha; apply HWK2; [lia | apply NOTCFP; lia]).
assert (VK : forall a v, spZ regs - 32 <= a -> a + 8 <= spZ regs ->
   val_mem SEGS (mrestrict (w_H W1) mem1) a 8 v -> val_mem SEGS (mrestrict (w_H W2) mem2) a 8 v).
{ intros a v Ha1 Ha2 Hv. eapply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 mem2); [|exact Hv].
  intros kk Hkk. apply FR2. lia. }
assert (R2e : getr regs2 2 = getr regs1 2) by exact (HCS2 2 ltac:(unfold acallee_saved; lia)).
assert (R8e : getr regs2 8 = getr regs1 8) by exact (HCS2 8 ltac:(unfold acallee_saved; lia)).
assert (Hsp2 : spZ regs2 = spZ regs - 32) by (unfold spZ in *; rewrite R2e; exact Hsp).
(* the latch *)
apply (ind_latch_P P PLAW ly S Hp W mem md ly2 S2 Hp2 W2 regs regs2 mem2 md2 (k1 + k2) (prhWriter_cfp o buf (WriterApp.w_cap st))
  (spZ regs) d (Z.of_nat (Datatypes.S n)) _ HJ2 HPM2 Hsp2 Hal Hd0 Hd16 Hlo Hhi ltac:(rewrite R8e; exact H8) Hcnt1
  (VK (spZ regs - 32) _ ltac:(lia) ltac:(lia) V0) (VK (spZ regs - 24) _ ltac:(lia) ltac:(lia) V8) (VK (spZ regs - 16) _ ltac:(lia) ltac:(lia) V16)
  (VK (spZ regs - 8) _ ltac:(lia) ltac:(lia) V24)).
intros regs3 mem3 md3 HJ3 HPM3 MEM3 H83 HCS3.
assert (C3 : forall rr, acallee_saved rr -> rr <> 8 -> getr regs3 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr))
  by (intros rr Hrr Hn8; rewrite (HCS3 rr Hrr Hn8); exact (HCS2 rr Hrr)).
assert (R2f : getr regs3 2 = getr regs1 2) by exact (C3 2 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (R9f : getr regs3 9 = getr regs1 9) by exact (C3 9 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (R18f : getr regs3 18 = getr regs1 18) by exact (C3 18 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (Hsp3 : spZ regs3 = spZ regs - 32) by (unfold spZ in *; rewrite R2f; exact Hsp).
assert (HCS3e : forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
  by (intros r Hr; rewrite (C3 r ltac:(unfold acallee_saved; lia) ltac:(lia)); exact (HCS r Hr)).
assert (V3 : forall a v, spZ regs - 32 <= a -> a + 8 <= spZ regs ->
   val_mem SEGS (mrestrict (w_H W1) mem1) a 8 v -> val_mem SEGS (mrestrict (w_H W2) mem3) a 8 v).
{ intros a v Ha1 Ha2 Hv. eapply (val_mem_kept SEGS (w_H W1) (w_H W2) mem1 mem3); [|exact Hv].
  intros kk Hkk. rewrite MEM3 by lia. apply FR2. lia. }
assert (HWK3 : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
   aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnf. rewrite MEM3 by lia.
  assert (Hno : ~ (o <= a < o + 32))
    by (intros Ho; apply Hnf; exists (o, o + 32); split; [left; reflexivity | cbn [fst snd]; lia]).
  rewrite (HWK2 a ltac:(lia) (NOTCFP a ltac:(lia) Hno)). exact (HWK a Ha Hnf). }
pose proof (ind_retpos_mem ly S Lam peak ran o buf st _ ly2 S2 Hp2 W2 regs2 mem2 md2 regs3 mem3 md3 rp_i HAR2
  ltac:(lia) ltac:(lia) MEM3 HRET12) as HRET3.
destruct n as [|n'].
- (* the last round: the count reaches 0, the epilogue *)
  replace (if Z.of_nat 1 - 1 =? 0 then IND_K22 else IND_K16) with IND_K22 by reflexivity.
  replace (Z.to_nat depth - 0)%nat with (Z.to_nat depth) in HRET3 by lia.
  change (WriterValue.wind true depth) with ([10] :: repeat [32; 32] (Z.to_nat depth)).
  exact (ind_epi_P P PLAW ly S Hp W regs mem md ly2 S2 Hp2 W2 regs3 mem3 md3 (k1 + k2) d o buf st Lam peak ran _ rp_i
    HJ3 HPM3 Hsp3 Hal Hd0 Hd16 Hlo Hhi Hol Hoh Hra HCS3e
    (V3 (spZ regs - 32) _ ltac:(lia) ltac:(lia) V0) (V3 (spZ regs - 24) _ ltac:(lia) ltac:(lia) V8) (V3 (spZ regs - 16) _ ltac:(lia) ltac:(lia) V16)
    (V3 (spZ regs - 8) _ ltac:(lia) ltac:(lia) V24)
    HWK3 HROOM2 HRET3).
- (* more rounds: the loop head again *)
  replace (if Z.of_nat (Datatypes.S (Datatypes.S n')) - 1 =? 0 then IND_K22 else IND_K16) with IND_K16
    by (destruct (Z.eqb_spec (Z.of_nat (Datatypes.S (Datatypes.S n')) - 1) 0); [lia | reflexivity]).
  exact (IH ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i ly2 S2 Hp2 W2 regs3 mem3 md3 (k1 + k2)
    HPRE HUNIV HWIN Hol Hoh Hcut HCHe Hlo Hhi HOUT HLED HLENT HMAX HLIVET ltac:(lia) ltac:(lia) HJ3 HPM3 Hsp3 HCS3e
    ltac:(rewrite H83; f_equal; lia) ltac:(rewrite R9f; exact H9) ltac:(rewrite R18f; exact H18)
    (V3 (spZ regs - 32) _ ltac:(lia) ltac:(lia) V0) (V3 (spZ regs - 24) _ ltac:(lia) ltac:(lia) V8) (V3 (spZ regs - 16) _ ltac:(lia) ltac:(lia) V16)
    (V3 (spZ regs - 8) _ ltac:(lia) ltac:(lia) V24)
    HWK3 HROOM2 HRET3 HEVS HCONSE).
Qed.

(* ---- the blez on a sign-extended C int: taken exactly when the int is <= 0 ---- *)
Lemma ind_blez : forall depth, - 2 ^ 31 <= depth < 2 ^ 31 ->
  branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 depth) = (depth <=? 0).
Proof.
intros depth Hd. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with 9223372036854775808. change (bv_modulus 64) with 18446744073709551616.
rewrite !Z.mod_small by lia.
replace (0 + 9223372036854775808 - 9223372036854775808) with 0 by lia.
replace (depth + 9223372036854775808 - 9223372036854775808) with depth by lia.
destruct (Z.ltb_spec 0 depth), (Z.leb_spec depth 0); cbn [negb]; first [reflexivity | exfalso; lia].
Qed.

(* ---- a value stored in memory survives a stretch whose view agrees on its bytes ---- *)
Lemma ind_val_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H' m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA HV k Hk.
pose proof (HV k Hk) as Hb. pose proof (HA (a + Z.of_nat k) ltac:(lia)) as Hx.
unfold aview in Hx. rewrite Hb in Hx. cbn [option_map] in Hx.
destruct (mbyte SEGS (mrestrict H' m') (a + Z.of_nat k)) as [b|] eqn:Eb; try rewrite Eb in Hx;
  cbn [option_map] in Hx; [|discriminate Hx].
injection Hx as Hx. f_equal. apply bv_eq. exact Hx.
Qed.

(* ---- indent's frame (below its entry sp, above alloc_ceiling) is outside the writer's footprint: the struct is at
   o >= the entry sp, the buffer block below alloc_ceiling ---- *)
Lemma ind_cfp_frame : forall o buf cap a,
  a < o -> (cap <> 0 -> 0 <= buf /\ buf + cap <= YM05.alloc_ceiling) -> 0 <= cap -> YM05.alloc_ceiling <= a ->
  ~ inFP (prhWriter_cfp o buf cap) a.
Proof.
intros o buf cap a Ho Hb Hc Ha (r & Hin & Hr).
cbn [prhWriter_cfp In] in Hin. destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|].
unfold prhWriter_fp in Hin. destruct (Z.eqb_spec cap 0) as [Hz | Hnz].
{ destruct Hin. }
cbn [ablocks_fp map In] in Hin. destruct Hin as [<- | []]. cbn [fst snd] in Hr.
destruct (Hb Hnz) as (Hb0 & Hb1). pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hreq : req_size (cap + cf_head) = cap + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); cbv iota; lia).
rewrite Hreq in Hr. lia.
Qed.

(* ---- after indent's first put call: a fresh seat at the return site (slot 13, the blez on s0) runs to the
   epilogue (slot 22) when depth <= 0, else through the s2 load (slots 14-15) to the loop head (slot 16); in
   continuation form: memory is the seat's, every callee-saved register but s2 is kept, s2 holds IND_SP at the loop
   head, and the journal is the same one ---- *)
Lemma ind_k13_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W mem md ly1 S1 Hp1 W1 (regs regs1 : bvmap 5 word) mem1 md1 k1 FP sp d depth
    (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
    ly1 S1 Hp1 W1 mem1 md1 k1 -> P mem1 ->
  spZ regs1 = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> 2 ^ 46 <= sp - 32 -> sp + d <= 2 ^ 47 ->
  getr regs1 8 = w64 depth -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
       ly1 S1 Hp1 W1 mem3 md3 k1 -> P mem3 ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a) ->
     (forall rr, acallee_saved rr -> rr <> 18 -> getr regs3 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)) ->
     (0 < depth -> getr regs3 18 = w64 IND_SP) ->
     SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + (if depth <=? 0 then IND_K22 else IND_K16))) mem3
       (YK11.seg_rom SEGS)) md3) Q) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNTOI := paj_run_to_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
intros ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d depth Q HJ HPM Hsp Hal Hd0 Hd16 Hlo Hhi
  H8 Hdep V0 V8 V16 V24 HK.
pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstat.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
destruct (ind_seat (AF_indent + 4 * 13) W1 regs regs1 mem1) as (HS & SHOK).
- rewrite Hsp, Zminus_mod, Hal. reflexivity.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
- rewrite Hsp. exact V0.
- rewrite Hsp. replace (sp - 32 + 8) with (sp - 24) by lia. exact V8.
- rewrite Hsp. replace (sp - 32 + 16) with (sp - 16) by lia. exact V16.
- rewrite Hsp. replace (sp - 32 + 24) with (sp - 8) by lia. exact V24.
- rewrite Hsp. lia.
- set (E := Eimg (Ereg regs1 (ind_x16 regs))) in *.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 (ind_x16 regs)) kk)
    by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
  assert (EI : forall kk, (A_TEXT <= kk < A_LIM)%nat -> ew E kk = Z_to_bv 64 (VAL kk))
    by (intros kk Hk; subst E; apply Eimg_img; exact Hk).
  assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
  assert (E8 : ew E 8 = Z_to_bv 64 depth)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact H8).
  assert (D0 : forall (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = w).
  { intros n w Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned. }
  assert (D8 : sv_denot E (SOff 8 0) = Z_to_bv 64 depth) by (apply D0; exact E8).
  psrr_branch_tokR RUN BRR HS SHOK ind_Bspan.
  all: match goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite D8 in Hc; change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc; rewrite (ind_blez depth Hdep) in Hc end.
  all: match goal with Hc : (?x <=? 0) = ?bb |- _ =>
    first [ assert (Hz : x <= 0) by (apply Z.leb_le; exact Hc)
          | assert (Hz : 0 < x) by (apply Z.leb_gt; exact Hc) ] end.
  (* the taken arm is at the epilogue already, the other runs the s2 load to the loop head *)
  1: paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM ind_Bspan IND_K22.
  3: paj_run_to_tok_x_invR RUNTOI HS HJ SHOK HPM ind_Bspan IND_K16.
  all: try (eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- (32 + d)));
    [reflexivity | rewrite Usp, Hsp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]).
  (* the run went from a read-only seat: memory is the seat's everywhere *)
  all: assert (MEM : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a)
    by (intros a Ha; apply aview_eq_of; rewrite (HFr (Z_to_bv 64 a)); [reflexivity |];
        rewrite unsigned_lit_small by lia; intros (rr & Hrr & Hra');
        match type of Hrr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hrr end;
        destruct Hrr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; lia).
  all: rewrite (st_ok_pi_restrict_mkst (w_H W1) E _ ms HS ltac:(vm_compute; reflexivity)).
  all: assert (GR : forall rr : bv 5, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs _) rr))
         by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms rr HS)).
  all: match goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (BASE + ?pc)) _ _ |} _ =>
    let v := eval vm_compute in pc in change pc with v end.
  all: first
    [ replace (ltac:(ind_lit IND_K22) : Z) with (if depth <=? 0 then IND_K22 else IND_K16)
        by (destruct (Z.leb_spec depth 0); [vm_compute; reflexivity | lia])
    | replace (ltac:(ind_lit IND_K16) : Z) with (if depth <=? 0 then IND_K22 else IND_K16)
        by (destruct (Z.leb_spec depth 0); [lia | vm_compute; reflexivity]) ].
  all: apply (HK (ms_regs ms) (ms_mem ms) _ HJ HPM MEM).
  (* the callee-saved registers but s2: the seat's atoms *)
  1, 3: intros rr Hrr Hn18; unfold acallee_saved in Hrr;
    assert (Hr' : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
                  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
    rewrite GR; repeat destruct Hr' as [-> | Hr']; try subst rr;
    match goal with |- sv_denot ?E0 ?e = _ => let v := eval vm_compute in e in change e with v end;
    apply D0; rewrite EL by (unfold A_TEXT; lia);
    match goal with |- ew _ ?n = getr _ ?rg => exact (ew_Ereg_nat regs1 _ n rg eq_refl) end.
  1: intros Hpos; lia.
  (* s2 at the loop head: the auipc / addi pair of slots 14-15 forms the two-space literal *)
  intros _. rewrite GR.
  match goal with |- sv_denot ?E0 ?e = _ => let v := eval vm_compute in e in change e with v end.
  cbn [sv_denot]. rewrite EI by (unfold A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (apply pa_val_range).
  unfold w64, IND_SP.
  match goal with |- Z_to_bv 64 (VAL ?a + ?off) = _ =>
    replace (ind_addhi_atom 15) with a by (vm_compute; reflexivity);
    replace (ind_addhi_off 15) with off by (vm_compute; reflexivity) end.
  reflexivity.
Qed.

(* the old statement, the P := fun _ => True corollary of ind_k13_P (byte-identical to 6492e80df47) *)
Lemma ind_k13 : forall ly S Hp W mem md ly1 S1 Hp1 W1 (regs regs1 : bvmap 5 word) mem1 md1 k1 FP sp d depth
    (Q : world SEGS -> config -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
    ly1 S1 Hp1 W1 mem1 md1 k1 ->
  spZ regs1 = sp - 32 -> sp mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> 2 ^ 46 <= sp - 32 -> sp + d <= 2 ^ 47 ->
  getr regs1 8 = w64 depth -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 32) 8 (bv_unsigned (getr regs 18)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 24) 8 (bv_unsigned (getr regs 9)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 16) 8 (bv_unsigned (getr regs 8)) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (sp - 8) 8 (bv_unsigned (getr regs 1)) ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (sp + d) FP ly S Hp W mem md []
       ly1 S1 Hp1 W1 mem3 md3 k1 ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) mem1 a) ->
     (forall rr, acallee_saved rr -> rr <> 18 -> getr regs3 (Z_to_bv 5 rr) = getr regs1 (Z_to_bv 5 rr)) ->
     (0 < depth -> getr regs3 18 = w64 IND_SP) ->
     SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + (if depth <=? 0 then IND_K22 else IND_K16))) mem3
       (YK11.seg_rom SEGS)) md3) Q) ->
  SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d depth Q HJ Hsp Hal Hd0 Hd16 Hlo Hhi
  H8 Hdep V0 V8 V16 V24 HK.
apply (ind_k13_P (fun _ => True) ind_laws_true ly S Hp W mem md ly1 S1 Hp1 W1 regs regs1 mem1 md1 k1 FP sp d depth Q
  HJ I Hsp Hal Hd0 Hd16 Hlo Hhi H8 Hdep V0 V8 V16 V24).
intros regs3 mem3 md3 HJ3 _ MEM HKEEP H18. exact (HK regs3 mem3 md3 HJ3 MEM HKEEP H18).
Qed.

(* ---- the arm pretty <> 0, from the entry through the first put call (the newline, slot 12) and the blez at slot 13,
   in continuation form: the continuation gets put's post over [[10]] at slot 22 (depth <= 0) or at the loop head,
   slot 16, with s2 = the two-space literal (depth > 0) ---- *)
Lemma ind_pre_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W regs mem md ch o pretty depth d buf (st : WriterApp.wst) Lam peak ran
    (rp_i : nat) (rp_hist : list YG00.chunk) (Q : world SEGS -> config -> Prop),
  fpre B ARx STK_indent ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* the first put's consumer window (the caller derives it from indent's by prhWriter_cons_at) *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [[10]])) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 pretty -> getr regs 12 = w64 depth ->
  0 < pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  spZ regs + 16 <= o ->
  (exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  Z.of_nat (length (WriterApp.w_text st)) + 1 + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* the first put's run event (the caller derives it from indent's entry list by prhWriter_ev_at) *)
  (prhWriter_grows st [10] = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st [10])) ->
  prh_live_evs S (prhWriter_evs [] st [[10]]) -> P mem ->
  (forall ly1 S1 Hp1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 k1,
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (STK_indent + d) (spZ regs + d)
       (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W mem md [] ly1 S1 Hp1 W1 mem1 md1 k1 ->
     spZ regs1 = spZ regs - 32 ->
     (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     getr regs1 8 = w64 depth -> getr regs1 9 = w64 o ->
     val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
     val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
     val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
     val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
     (forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
        aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
     room_live_cf S1 ->
     prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st [[10]] ly1 S1 Hp1 W1 regs1 mem1 md1 ->
     P mem1 ->
     if depth <=? 0
     then SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K22)) mem1 (YK11.seg_rom SEGS)) md1) Q
     else (getr regs1 18 = w64 IND_SP ->
           SRr' SEGS RZ_cf W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + IND_K16)) mem1 (YK11.seg_rom SEGS)) md1) Q)) ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_indent) regs mem md) Q.
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
intros ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran rp_i rp_hist Q HPRE HROOM HPOS HCONS HUNIV
  H10 H11 H12 Hpr Hdep Hcut HCHe HWIN Hol Hoh HOUT HLED HLEN HMAX HEV0 HLIVE HPM HC.
pose proof HPRE as (HAP & HRO & HSTKTOP). pose proof HSTKTOP as (_ & _ & HFRM).
destruct (ind_entry ly S Hp W regs mem md ch HAP) as (HS & SHOK).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (@pa_B_ok _ _ PA) as HBASE.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
assert (Hlo : 2 ^ 46 <= spZ regs - 32) by lia.
assert (Hhi : spZ regs + d <= 2 ^ 47) by lia.
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (YCbqGcallW.ajournal_x_init_WR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
  STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := Eimg (Ereg regs [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs []) kk)
  by (intros kk Hk; subst E; apply Eimg_low; exact Hk).
assert (EI : forall kk, (A_TEXT <= kk < A_LIM)%nat -> ew E kk = Z_to_bv 64 (VAL kk))
  by (intros kk Hk; subst E; apply Eimg_img; exact Hk).
assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat -> ew E n = getr regs r)
  by (intros n r Hn Hlt; rewrite EL by exact Hlt; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E2 : ew E 2 = getr regs 2) by exact (ER 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = getr regs 11) by exact (ER 11%nat 11%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (U11 : U E (SOff 11 0) = pretty) by (apply (U_atom E 11%nat pretty); [rewrite E11, H11; reflexivity | lia]).
unfold cfg_at. rewrite Hent.
change (w64 (BASE + AF_indent)) with (Z_to_bv 64 (BASE + AF_indent)).
paj_run_tok_x_invR RUNI HS HJ SHOK HPM ind_Bspan.
{ eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- d));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia | cbn [YP09.r_whi stack_region]; lia
  | apply awr_ok_nil]. }
psrr_branch_tokR RUN BRR HS SHOK ind_Bspan.
1:{ match goal with Hc : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U, U11, (U_lit E 0 ltac:(lia)) in Hc; apply Z.eqb_eq in Hc; lia end. }
match goal with Hc : branch_taken _ _ _ = false |- _ => clear Hc end.
(* slots 6-12: s0 = depth, s1 = o, a1 = the newline, a2 = 1, a0 = o, then the jal into put *)
paj_run_tok_x_invR RUNI HS HJ SHOK HPM ind_Bspan.
all: try (eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (- d));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia | cbn [YP09.r_whi stack_region]; lia
  | apply awr_ok_nil]).
(* the four saves, read off the call state's frame region (s2, s1, s0, ra at sp - 32 .. sp - 8) *)
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & HMR & _) & _).
match type of HMR with Forall _ ?rs => let v := eval vm_compute in rs in change rs with v in HMR end.
apply Forall_cons_iff in HMR as [HR0 _].
destruct HR0 as (_ & _ & _ & HCK).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HCK. rewrite Usp in HCK.
apply Forall_cons_iff in HCK as [C0 HCK]. apply Forall_cons_iff in HCK as [C8 HCK].
apply Forall_cons_iff in HCK as [C16 HCK]. apply Forall_cons_iff in HCK as [C24 _].
assert (E1 : ew E 1 = getr regs 1) by exact (ER 1%nat 1%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E8 : ew E 8 = getr regs 8) by exact (ER 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E9 : ew E 9 = getr regs 9) by exact (ER 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E18 : ew E 18 = getr regs 18) by exact (ER 18%nat 18%bv eq_refl ltac:(unfold A_TEXT; lia)).
pose proof (u64_range (getr regs 18)). pose proof (u64_range (getr regs 9)).
pose proof (u64_range (getr regs 8)). pose proof (u64_range (getr regs 1)).
assert (DV : forall (n : nat) (w : word), ew E n = w -> sv_denot E (SOff n 0) = Z_to_bv 64 (bv_unsigned w))
  by (intros n w Hn; cbn [sv_denot]; rewrite Hn, Z.add_0_r; reflexivity).
assert (F0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 32) 8 (bv_unsigned (getr regs 18))).
{ replace (spZ regs - 32) with (spZ regs + -32) by lia.
  exact (val_of_chunk_ok SEGS E _ (spZ regs) (-32) 8%N (SOff 18 0) (bv_unsigned (getr regs 18)) C0
    (DV 18%nat _ E18) ltac:(zside) ltac:(zside)). }
assert (F8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))).
{ replace (spZ regs - 24) with (spZ regs + -24) by lia.
  exact (val_of_chunk_ok SEGS E _ (spZ regs) (-24) 8%N (SOff 9 0) (bv_unsigned (getr regs 9)) C8
    (DV 9%nat _ E9) ltac:(zside) ltac:(zside)). }
assert (F16 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 16) 8 (bv_unsigned (getr regs 8))).
{ replace (spZ regs - 16) with (spZ regs + -16) by lia.
  exact (val_of_chunk_ok SEGS E _ (spZ regs) (-16) 8%N (SOff 8 0) (bv_unsigned (getr regs 8)) C16
    (DV 8%nat _ E8) ltac:(zside) ltac:(zside)). }
assert (F24 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (spZ regs - 8) 8 (bv_unsigned (getr regs 1))).
{ replace (spZ regs - 8) with (spZ regs + -8) by lia.
  exact (val_of_chunk_ok SEGS E _ (spZ regs) (-8) 8%N (SOff 1 0) (bv_unsigned (getr regs 1)) C24
    (DV 1%nat _ E1) ltac:(zside) ltac:(zside)). }
(* only indent's own frame [sp - 32, sp) changed, over both stretches *)
assert (NOW : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 32 \/ spZ regs <= a) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout.
  assert (NW : forall rs, (forall r, In r rs -> YP09.r_base r = Some 2%nat /\ YP09.r_wlo r = -32 /\ YP09.r_whi r = 0) ->
    ~ in_wrange E rs a).
  { intros rs Hrs (r & Hr & Hra'). destruct (Hrs r Hr) as (Hb & Hl & Hh). rewrite Hb, Hl, Hh in Hra'.
    cbn [base_val] in Hra'. rewrite Usp in Hra'. lia. }
  apply aview_eq_of. rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |].
  all: rewrite unsigned_lit_small by lia; apply NW; intros r Hr.
  all: first [unfold ind_ss0 in Hr | idtac]; cbn [ss_mem add_cond In] in Hr; destruct Hr as [<- | []].
  all: cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region]; rewrite ?HKf; repeat split; reflexivity. }
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply NOW; lia).
assert (HSTR : forall a, o <= a < o + 32 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply NOW; lia).
(* the registers at put's entry *)
assert (HCS0 : forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia.
  rewrite (st_ok_restrict_reg SEGS (w_H W) E _ ms0 _ HS).
  repeat destruct Hr' as [-> | Hr']; try subst r;
  match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end;
  cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
  match goal with |- ew _ ?n = getr _ ?rg => exact (ER n rg eq_refl ltac:(unfold A_TEXT; lia)) end. }
pmkst HS.
prreg HS (1%bv : bv 5) Rra. prreg_norm Rra.
prreg HS (2%bv : bv 5) R2. prreg_norm R2.
prreg HS (3%bv : bv 5) Rgp. prreg_norm Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg_norm Rtp.
prreg HS (8%bv : bv 5) R8. prreg_norm R8.
prreg HS (9%bv : bv 5) R9. prreg_norm R9.
prreg HS (10%bv : bv 5) R10. prreg_norm R10.
prreg HS (11%bv : bv 5) R11. prreg_norm R11.
prreg HS (12%bv : bv 5) R12. prreg_norm R12.
assert (E3 : ew E 3 = getr regs 3) by exact (ER 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E4 : ew E 4 = getr regs 4) by exact (ER 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E10 : ew E 10 = getr regs 10) by exact (ER 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)).
assert (E12 : ew E 12 = getr regs 12) by exact (ER 12%nat 12%bv eq_refl ltac:(unfold A_TEXT; lia)).
rewrite ?E3, ?Hgp in Rgp. rewrite ?E4, ?Htp in Rtp.
rewrite E12, H12 in R8. rewrite E10, H10 in R9, R10.
rewrite EI in R11 by (unfold A_TEXT, A_LIM; lia).
rewrite unsigned_lit_small in R11 by (apply pa_val_range).
assert (R11' : getr (ms_regs ms0) 11 = w64 IND_NL).
{ rewrite R11. unfold w64, IND_NL.
  match goal with |- Z_to_bv 64 (VAL ?a + ?off) = _ =>
    replace (ind_addhi_atom 9) with a by (vm_compute; reflexivity);
    replace (ind_addhi_off 9) with off by (vm_compute; reflexivity) end.
  reflexivity. }
assert (K13 : BASE + (AF_indent + 4 * 13) = BASE + ltac:(ind_lit (AF_indent + 4 * 13))) by (f_equal; vm_compute; reflexivity).
rewrite <- K13 in Rra.
assert (Rsp : spZ (ms_regs ms0) = spZ regs - 32).
{ unfold spZ at 1. rewrite R2, Usp, unsigned_lit_small by lia. lia. }
(* the call's premises at put's entry *)
assert (HCH : achain ly (aview SEGS (w_H W) (ms_mem ms0)) (spZ regs - 32) (s0Z (ms_regs ms0)) []).
{ left. split; [|reflexivity]. unfold s0Z. rewrite R8. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  destruct (Z_lt_le_dec depth 0) as [Hn | Hp0].
  - right; left. rewrite <- (Z.mod_unique depth (2 ^ 64) (-1) (depth + 2 ^ 64)) by lia. lia.
  - left. rewrite Z.mod_small by lia. lia. }
assert (HRO2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms0))).
{ intros a Hro Hown Herr.
  assert (Hi : in_img SEGS a)
    by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)]).
  destruct Hi as (sg & Hsg & Hr). pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))).
  rewrite NOW; [exact (HRO a Hro Hown Herr) | unfold kLowMemEnd in *; lia | unfold kLowMemEnd in *; lia]. }
pose proof (ajxR_ar HJ) as HARc.
destruct (HLIT ly S Hp W (ms_mem ms0) _ HARc HRO2) as ((HSRC & HKNL) & _).
assert (Hbok : WriterApp.w_cap st <> 0 -> In (buf, WriterApp.w_cap st) Lam).
{ intros Hc. destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction | exact Hin]. }
assert (Hc0 : 0 <= WriterApp.w_cap st) by (destruct HOUT as (_ & _ & Hcr & _); lia).
assert (Hbufb : WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling).
{ intros Hc. pose proof HLED as Hbl. apply prh_ledger_blocks in Hbl.
  pose proof (proj1 (Forall_forall _ _) Hbl _ (Hbok Hc)) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & Hp4 & Hpcb & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  match type of Hpcb with context [req_size ?x] =>
    assert (Hreq : req_size x = x) by (unfold req_size; destruct (Z.eqb_spec x 0); cbv iota; lia) end.
  rewrite Hreq in Hpcb. lia. }
pose proof (ind_out_kept W mem (ms_mem ms0) Lam o buf st HLOW HSTR Hbufb HOUT) as HOUT2.
pose proof (ind_ledger_kept ly S Hp W mem (ms_mem ms0) md Lam peak _ _ ran HAR HLOW HLED) as HLED2.
pose proof (ind_src_home ly S Hp W (ms_mem ms0) _ Lam peak _ _ ran buf st IND_NL 1 HARc HLED2 Hbok Hc0
  ltac:(lia) HKNL) as HHOME.
assert (RTO : YK0s.ret_ok (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))))
  by (rewrite K13; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R4096 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))))
  by (rewrite K13, unsigned_lit_small by lia; lia).
assert (RLT : bv_unsigned (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))) < YM05.alloc_ceiling)
  by (rewrite K13, unsigned_lit_small by lia;
      exact (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) ltac:(ind_lit (AF_indent + 4 * 13)) ltac:(lia) ltac:(vm_compute; reflexivity))).
assert (HTOP : spZ regs + 32 <= ly_stk_hi ly) by lia.
assert (HFPB : forall a, inFP (prhWriter_fp buf (WriterApp.w_cap st)) a ->
  inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a \/ in_tmp_block (ablocks B ly S) (ablocks B ly S) a).
{ intros a (r & Hr & Hra'). left. exists r. split; [cbn [prhWriter_cfp In]; right; exact Hr | exact Hra']. }
(* the first call's one record: indent's own entry record (o >= spZ regs + 16): [o - 16, o) is at or above spZ regs,
   where indent's saves do not write *)
assert (HCHO : spZ (ms_regs ms0) + 16 <= o ->
  exists ra, rdword (aview SEGS (w_H W) (ms_mem ms0)) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) (ms_mem ms0)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ intros _. apply (ind_rec_kept (aview SEGS (w_H W) mem) _ o); [| exact HCHe].
  intros a Ha. apply NOW; lia. }
eapply (SRr'_bind SEGS RZ_cf).
{ exact (ind_call_put_P P PLAW PCALL W W (ms_regs ms0) (ms_mem ms0) _ (prhWriter_cfp o buf (WriterApp.w_cap st)) ly S Hp mem md
    ly S Hp 0 (spZ regs) d o IND_NL [10] buf st Lam peak ran (Z_to_bv 64 (BASE + (AF_indent + 4 * 13))) [] rp_i rp_hist
    HJ Rsp Hal Hd0 Hd16 Rgp Rtp Rra RTO R4096 RLT HCH HRO2 HROOM HUNIV HFRM HTOP HPOS HCONS R10 R11' R12 Hol Hoh
    HOUT2 HLED2 HSRC HHOME HLEN HMAX HLIVE HFPB HCHO HEV0 HPM). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HWK & HP & HQ1 & HQP & HQ2 & HPM2).
(* put's return at slot 13: the callee-saved registers are put's entry's, the frame is outside put's footprint *)
pose proof (ajxR_ar HJ2) as HAR2.
(* the run [[10]] at the exact advance: the empty run at the call, then this put (prhWriter_ret_pos_step) *)
assert (HcntW : 0 <= WriterApp.w_cnt st)
  by (pose proof HLED as Hbd; apply prh_ledger_bounds in Hbd; destruct Hbd as (_ & _ & Hc & _); lia).
assert (HOK0 : prh_oks [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st []) (prhWriter_reqs [] st [])
  rmost ran ran).
{ rewrite prhW_k_nil. unfold prh_oks. split; [intros i Hi; exfalso; lia|].
  split; [left; reflexivity|]. intros i Hi; exfalso; lia. }
assert (GR0 : prh_granted [] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [] st [])).
{ rewrite prhW_k_nil. intros i Hi; exfalso; lia. }
assert (HBLK0 : prhWriter_blk B ly S Lam peak buf st ly S Lam peak buf (prhWriter_putN [] st [])).
{ unfold prhWriter_blk. left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. apply Permutation_refl. }
pose proof (prhWriter_ret_pos_step B rp_sm rp_x rp_os rp_H0 rp_i rp_i rp_hist ly S Lam peak ran rmost rown o buf st [] [10]
  [] ran buf Lam peak ly S Hp W (ms_mem ms0) ly2 S2 Hp2 W2 regs2 mem2 md2 HcntW (eq_sym (Nat.add_0_r rp_i))
  HOK0 GR0 HOUT2 HLED2 HBLK0 HQP HQ2) as HRP2.
assert (P2 : getr regs2 2 = getr (ms_regs ms0) 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms0) 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms0) 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (Hsp2 : spZ regs2 = spZ regs - 32) by (unfold spZ at 1; rewrite P2; exact Rsp).
assert (HCS2 : forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP r ltac:(unfold acallee_saved; lia)). exact (HCS0 r Hr). }
assert (HFK : forall x, spZ regs - 32 <= x < spZ regs ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) (ms_mem ms0) x).
{ intros x Hx. apply HWK; [lia|].
  apply (ind_cfp_frame o buf (WriterApp.w_cap st) x); [lia | exact Hbufb | exact Hc0 | lia]. }
assert (G0 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)))
  by (apply (ind_val_kept (w_H W) (w_H W2) (ms_mem ms0) mem2);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply HFK; lia | exact F0]).
assert (G8 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)))
  by (apply (ind_val_kept (w_H W) (w_H W2) (ms_mem ms0) mem2);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply HFK; lia | exact F8]).
assert (G16 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)))
  by (apply (ind_val_kept (w_H W) (w_H W2) (ms_mem ms0) mem2);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply HFK; lia | exact F16]).
assert (G24 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)))
  by (apply (ind_val_kept (w_H W) (w_H W2) (ms_mem ms0) mem2);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply HFK; lia | exact F24]).
apply (ind_k13_P P PLAW ly S Hp W mem md ly2 S2 Hp2 W2 regs regs2 mem2 md2 _ _ (spZ regs) d depth Q HJ2 HPM2 Hsp2 Hal Hd0 Hd16
  Hlo Hhi ltac:(rewrite P8; exact R8) Hdep G0 G8 G16 G24).
intros regs3 mem3 md3 HJ3 HPM3 MEM HKEEP H18.
(* the stop: hand put's post, moved to the stop's registers and memory, to the continuation *)
assert (K2 : getr regs3 2 = getr regs2 2) by exact (HKEEP 2 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (Hsp3 : spZ regs3 = spZ regs - 32) by (unfold spZ at 1; rewrite K2; exact Hsp2).
assert (HCS3 : forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HKEEP r ltac:(unfold acallee_saved; lia) ltac:(lia)). exact (HCS2 r Hr). }
assert (H8_3 : getr regs3 8 = w64 depth).
{ transitivity (getr regs2 8); [exact (HKEEP 8 ltac:(unfold acallee_saved; lia) ltac:(lia)) | rewrite P8; exact R8]. }
assert (H9_3 : getr regs3 9 = w64 o).
{ transitivity (getr regs2 9); [exact (HKEEP 9 ltac:(unfold acallee_saved; lia) ltac:(lia)) | rewrite P9; exact R9]. }
assert (T0 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)))
  by (apply (ind_val_kept (w_H W2) (w_H W2) mem2 mem3);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply MEM; lia | exact G0]).
assert (T8 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)))
  by (apply (ind_val_kept (w_H W2) (w_H W2) mem2 mem3);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply MEM; lia | exact G8]).
assert (T16 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)))
  by (apply (ind_val_kept (w_H W2) (w_H W2) mem2 mem3);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply MEM; lia | exact G16]).
assert (T24 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)))
  by (apply (ind_val_kept (w_H W2) (w_H W2) mem2 mem3);
      [intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply MEM; lia | exact G24]).
assert (HWK3 : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite (MEM a ltac:(lia)), (HWK a ltac:(lia) Hn). apply NOW; lia. }
pose proof (ind_retpos_mem ly S Lam peak ran o buf st [[10]] ly2 S2 Hp2 W2 regs2 mem2 md2 regs3 mem3 md3 rp_i HAR2
  ltac:(lia) ltac:(lia) MEM HRP2) as HRET3.
pose proof (HC ly2 S2 Hp2 W2 regs3 mem3 md3 _ HJ3 Hsp3 HCS3 H8_3 H9_3 T0 T8 T16 T24 HWK3 HQ1 HRET3 HPM3) as HQ.
destruct (depth <=? 0) eqn:Hdz; [exact HQ |].
exact (HQ (H18 ltac:(apply Z.leb_gt in Hdz; lia))).
Qed.

(* ---- indent's walk for the section's position interface: pretty = 0 is ind_pretty0; else ind_pre (entry, the
   newline, the blez), then the epilogue at once (depth <= 0) or the space loop ind_iter with depth rounds ---- *)
Theorem ind_holds_fixed_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall (rp_i : nat) (rp_hist : list YG00.chunk) ly S Hp W regs mem md ch o pretty depth d buf
    (st : WriterApp.wst) Lam peak ran,
  fpre B ARx STK_indent ly S Hp W regs mem md ch ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* indent's consumer window (tindent_specX, the batch kit): its puts' grows are consumer events *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i
    (length (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth))) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 pretty -> getr regs 12 = w64 depth ->
  0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= depth < 2 ^ 31 ->
  spZ regs + 16 <= o ->
  (exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
     exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  (* indent's entry premise (tindent_specX :667): the run's next events are its puts', all granted *)
  prh_run_at rp_sm rp_x rp_os rp_i (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) ->
  Z.of_nat (length (WriterApp.w_text st)) +
    Z.of_nat (length (concat (WriterValue.wind (negb (pretty =? 0)) depth))) + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  (* the live room at each of its events (tindent_specX, the batch kit: PRH_Base.prh_live_evs) *)
  prh_live_evs S (prhWriter_evs [] st (WriterValue.wind (negb (pretty =? 0)) depth)) -> P mem ->
  SRr' SEGS RZ_cf W (cfg_at SEGS (SIGMA AS_indent) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ_cf) STK_indent d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (fun ly' S' Hp' W' regs' mem' md' => (room_live_cf S' /\
          prhWriter_ret_pos B rp_sm rp_x rp_os rp_H0 rp_i ly S Lam peak ran rmost rown o buf st
            (WriterValue.wind (negb (pretty =? 0)) depth) ly' S' Hp' W' regs' mem' md') /\ P mem')).
Proof.
intros P PLAW PCALL.
intros rp_i rp_hist ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran
  HPRE HROOM HPOS HCONS HUNIV H10 H11 H12 Hpr Hdep Hcut HCHe HWIN Hol Hoh HOUT HLED HEVS HLEN HMAX HLIVE HPM.
destruct (Z.eq_dec pretty 0) as [-> | Hpn].
{ exact (ind_pretty0_P P PLAW ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i rp_hist HPRE HROOM HPOS H10 H11 H12
    HWIN Hol Hoh HOUT HLED HPM). }
assert (Hpb : negb (pretty =? 0) = true) by (destruct (Z.eqb_spec pretty 0); [contradiction | reflexivity]).
rewrite Hpb in HEVS, HLEN, HLIVE, HCONS |- *.
pose proof HPRE as (HAP & HROe & HSTKTOP).
pose proof HAP as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HK1 : STK_indent = pi_frame F_indent + STK_put) by reflexivity.
assert (HK2 : 0 <= STK_put) by (vm_compute; discriminate).
assert (HKf : pi_frame F_indent = 32) by (vm_compute; reflexivity).
assert (Hlo : 2 ^ 46 <= spZ regs - 32) by lia.
assert (Hhi : spZ regs + d <= 2 ^ 47) by lia.
(* the first put's budgets, from the whole run's *)
assert (HLEN1 : Z.of_nat (length (WriterApp.w_text st)) + 1 + 1 <= prhWriter_WMAX).
{ unfold WriterValue.wind in HLEN. cbn [concat] in HLEN. rewrite app_length, ind_rep_len in HLEN.
  cbn [length] in HLEN. lia. }
(* the first put's live room and consumer window, from indent's (nothing put yet) *)
assert (Hc0e : 0 <= WriterApp.w_cap st) by (destruct HOUT as (_ & _ & Hcr & _); lia).
assert (HLIVE1 : prh_live_evs S (prhWriter_evs [] st [[10]]))
  by exact (prhWriter_live_evs_at S S st [] [10] (repeat [32; 32] (Z.to_nat depth)) [] Hc0e HLIVE eq_refl).
assert (HCONS1 : PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [[10]]))).
{ pose proof (prhWriter_cons_at rp_sm rp_x rp_os rp_i st [] [10] (repeat [32; 32] (Z.to_nat depth)) [] HCONS) as H.
  change (length (prhWriter_evs [] st [])) with 0%nat in H. change (prhWriter_putN [] st []) with st in H.
  rewrite Nat.add_0_r in H. exact H. }
(* the first put's run event, from indent's entry list (prhWriter_ev_at with nothing put yet) *)
assert (HEV0 : prhWriter_grows st [10] = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st [10])).
{ intros Hg Hc. rewrite <- (Nat.add_0_r rp_i).
  exact (prhWriter_ev_at rp_sm rp_x rp_os rp_i _ st [] [10] (repeat [32; 32] (Z.to_nat depth)) [] HEVS eq_refl Hg Hc). }
apply (ind_pre_P P PLAW PCALL ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran rp_i rp_hist _ HPRE HROOM HPOS
  HCONS1 HUNIV H10 H11 H12 ltac:(lia) Hdep Hcut HCHe HWIN Hol Hoh HOUT HLED HLEN1 HMAX HEV0 HLIVE1 HPM).
intros ly1 S1 Hp1 W1 regs1 mem1 md1 k1 HJ1 Hsp1 HCS1 H81 H91 V0 V8 V16 V24 HWK1 HROOM1 HRET1 HPM1.
destruct (Z.leb_spec depth 0) as [Hd | Hd].
- (* depth <= 0: no space; the epilogue at once *)
  replace (WriterValue.wind true depth) with [[10]]
    by (unfold WriterValue.wind; replace (Z.to_nat depth) with 0%nat by lia; reflexivity).
  exact (ind_epi_P P PLAW ly S Hp W regs mem md ly1 S1 Hp1 W1 regs1 mem1 md1 k1 d o buf st Lam peak ran [[10]] rp_i
    HJ1 HPM1 Hsp1 Hal Hd0 Hd16 Hlo Hhi Hol Hoh Hra HCS1 V0 V8 V16 V24 HWK1 HROOM1 HRET1).
- (* depth > 0: the space loop, depth rounds *)
  intros H181.
  replace (Z.to_nat depth - Z.to_nat depth)%nat with 0%nat in * by lia.
  exact (ind_iter_P P PLAW PCALL (Z.to_nat depth) ly S Hp W regs mem md ch o depth d buf st Lam peak ran rp_i ly1 S1 Hp1 W1 regs1
    mem1 md1 k1 HPRE HUNIV HWIN Hol Hoh Hcut HCHe Hlo Hhi HOUT HLED HLEN HMAX HLIVE ltac:(lia) ltac:(lia) HJ1 HPM1 Hsp1 HCS1
    ltac:(rewrite Z2Nat.id by lia; exact H81) H91 H181 V0 V8 V16 V24 HWK1 HROOM1
    ltac:(rewrite Nat.sub_diag; exact HRET1) HEVS HCONS).
Qed.

End h.

(* ---- THE WALK of indent (A' 0x886e0): the kit's text tindent_specX (lib/A/PRH_FnWriter.v at the batch kit's 44123abafeb7:
   the entry premises prh_cons_from / prh_run_at / prh_live_evs over its puts' events `prhWriter_evs [] st P`, and the
   exact advance `exists ok, prhWriter_ret_ok ok .. most own .. /\ prh_granted ok .. /\ exists hist', pos (rp_i +
   length (prhWriter_evs ok st P))`), from put's text tput_specX (this slice's own put walk proves it) and the
   instance's image facts (HLIT, HPSTRO, Hent: discharged at PI_prog_A by S7a_indent_wit.v). The memory invariant of every segment is
   instantiated ONCE here: P := `memnorm mem -> memnorm m` for indent's entry memory mem (YSRrMemnorm.srr_inv_laws_imp
   over srr_inv_laws_memnorm_k, srr_inv_call_imp), so the post is fpostWmR's at wle'. The texts are PRH_FnWriter.v's;
   the bound `length rp_os <= 4` is introduced here and reaches put's text as the section hypothesis HOS. ---- *)
Theorem indent_holds : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) (HL : Z),
  AR_laws_x SEGS B ARx HL -> PALib B -> SIGMA AS_indent = BASE + AF_indent ->
  forall (CTX0 : list (list Z)),
  tput_specX (PA := PA) B ARx SK CTX0 ->
  (forall ly S Hp (W : world SEGS) mem md,
     ARx ly S Hp W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
     (src_rd W mem IND_NL [10] /\ kept_at B [] IND_NL 1) /\ (src_rd W mem IND_SP [32; 32] /\ kept_at B [] IND_SP 2)) ->
  (forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A)) ->
  tindent_specX (PA := PA) B ARx SK CTX0.
Proof.
intros B ARx HL LAWS TL Hent CTX0 HPUT HLIT HPSTRO.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist rmost rown ly S Hp W regs mem md ch o pretty depth d buf st Lam peak ran.
intros HPRE HROOM HPOS HOS HCONS HUNIV H10 H11 H12 Hpr Hdep Hcut HCHe HWIN Hol Hoh HOUT HLED HEVS HLEN HMAX HLIVE.
unfold fpostWmR, fQmn.
eapply ind_holds_fixed_P with (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
all: first
  [ exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))
  | exact (srr_inv_call_imp SEGS mem)
  | exact (fun H => H)
  | eassumption ].
Qed.

End W.
