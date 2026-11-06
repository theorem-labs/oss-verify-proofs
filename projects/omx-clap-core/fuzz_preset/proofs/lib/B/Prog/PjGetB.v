(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x830dc .. 0x831f4, 71 instructions, no call), in the form of this lane's
   lib/A/W_send_line_entry.v (a segment into a loop head) and of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v.  The statement is W_drain_cx.v dr_pro_stmt.

   The prologue saves the 13 callee-saved registers at 232(sp) .. 328(sp) of its 336-byte frame, keeps the
   relay entry s in s6 and its field addresses s->buf / s->used / s->cap in s10 / s11 / s9, spills
   &s->npartial, &s->overlong, &s->held to 208(sp) / 96(sp) / 128(sp), takes g_s by PAddHi (A_OBJ 22) into
   s2 with g_s >> 3 in s1 and (g_s + 4) >> 3 in s0, loads the shadow base from the GOT (A_OBJ 0 -> A_OBJ 32)
   into s5, and writes the shifted field addresses of g_s and the shadow addresses of s's cells into the
   frame.  No call, no shadow check, no store outside [sp0 - 336, sp0): every representation the outer loop's
   head carries lies below alloc_ceiling + 8 (a live block, the image band) and moves across the stores. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_drain_pro.v, with its module paths, module names and numbers changed; 1682 of its 1766 lines of code are new or changed and 1187 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d, unstripped twin c90d4fa54d43): the program walks of
   fuzz_preset's pj_get_str (34 words, entry pa_sigma AS_pj_get_str) and pj_get (112 words, entry pa_sigma AS_pj_get) over
   a Theorem Labs lane's whole-program listing lib/B/Listing_prog.v of the #102 pins (c97cc46b3e13 at the cut: the listing
   8bcc2c9e7809 at commit d42e123915ae with its header comment only changed), against
   the texts tpj_get_str_specX / tpj_get_specX (lib/A/PRH_FnPj.v 5aca5cbe2cfb at the kit cut
   7cdbb61b5fa0; the two texts are character-identical to f97c8b2f046b's:
   S' = S, the reader's name bound in pj_cstrR, the m-form post over YAkMemnorm.memnorm, fpre's bound
   raZ regs < YM05.alloc_ceiling and its FRM0-ENTRY frm_zero conjunct (PRH_Base.v ef7c8ca98529), the Batch-2
   ledger prh_ledger .. most own): pj_get_holds_B_top /
   pj_get_str_holds_B_top at the end, at the unit's image instance (B := YD2l.TfibB, ARx := ARcf at CfParams_preset;
   PALib and the laws by lib/B/PALibB.v), from pj_get_holds_B_K0 / pj_get_str_holds_B_K0 (generic in B, ARx, LAWS, PALib).
   RELOCATED B -> B' (h-rw-pre-5, 2026-10-29) from the signed old-pin walk origin/cold/h-rw-pre-5-b-pjget 062542d01e8
   (blob ae1372130547; pin f8f98a95, twin 3b5e1a09, listing v4): pj_get / pj_get_str are instruction-EQUAL in B and B'
   (the internal file INSN-COMPARE-9e1283d1.md), so the walk is unchanged but for the listing offset of pj_get's loop head (21048 on B, slot
   5217; 22060 on B', slot 5470; now computed at its two use sites from AF_pgB, not typed), the return-address lower
   bound at pj_get_str's call of pj_get (it went through the image-A name IMG_LO via a hypothesis PAB on pa_lo; it now
   follows from pa_B_ok's 0 <= BASE and the jal's own listing offset, so no image bound is cited) and the ledger's two
   #102 cells (most own, carried through unchanged: pj_get writes no static).
   They are the instances at YAkMemnorm.memnorm (laws srr_inv_laws_memnorm_k) of the walks against tpj_get_specXP /
   tpj_get_str_specXP (lib/A/Prog/S6PjStrcmp.v section (4): the texts with fQmn's memnorm generalised to any memory
   invariant P with srr_inv_laws), converted by S6PjStrcmp.v tpj_get_specX_of_P / tpj_get_str_specX_of_P. In SRr form.
   Generic in the image facts (Context PAImg B_prog_listing, the image facts Hent / Hobj discharged at
   PI_prog_B by computation at the end) and in the allocator relation ARx (LAWS : AR_laws_x .. cf_head, at
   CfParams_preset). fpre's raZ bound at pj_get_str's call of pj_get comes from the jal's own return pc
   (PRW_StepKit.pa_slot_lt_ceil_b, WalkS7b c50d0958c0b).
   THE KEEP: every walk runs with an invariant (runner twins YC1fPx.paj_run_x_inv / paj_run_to_x_inv over YC80x's
   srr_inv_laws, after c-omx-alloc's YC80x collapse);
   branches and returns leave the memory. The function-level theorems instantiate it ONCE at their top as
   m |-> (P mem -> P m) (srr_inv_laws_imp). The member loop's segment lemmas pgl_loopP / pgl_startP have the generic-P
   form (h-hpreset-7 12:18Z / 12:22Z): any R with srr_inv_laws SEGS R and srr_inv_call SEGS R (the loop crosses the
   strcmp call, whose row keeps YAkMemnorm.memnorm only); their statements changed for the INVARIANT's sake, so the
   statements before the keep (a43c94406a1) stay byte-identical as the corollaries pgl_loop / pgl_start at
   R := fun _ => True. Consumers of these segment lemmas: none outside this file (none told). pj_get_str's call of pj_get
   keeps P by tpj_get_specXP's last conjunct; no callee here has a memnorm entry premise, so srr_inv_mn is not used.
   STRUCTURE: image A's twins (WalkS6, origin/cold/h-hpreset-7-walk-S6) lib/A/Prog/S6PjGetStr.v and S6PjGet.v; the
   image-free pieces are IMPORTED from lib/A/Prog/S6PjCommon.v (WalkS6) and lib/A/Prog/S6PjStrcmp.v (this branch,
   shared with WalkS6). The walk is image B's: frame sizes, seats and return slots from B's listing.
   B differs from A by the UBSan trap checks (`andi; bnez` to an unimp on a misaligned pointer; pj_get's
   pointer-overflow checks before keys[i] and before kids + 56 i), each a branch refuted by the tree's facts.
   #102 TREE: the kit cut 7cdbb61b5fa0 (the #102 integration f44822dff082 + the P'' universe set + the kit texts; S1Ledger.v
   8cf15eeb6311, lib/B/PALibB.v 5baa19c890f7, lib/Reusable/YCej.v 71ae24321ba4, the engine set, image tables and listings
   of the #102 pins), merged forward into this row; the shared image-free files lib/A/Prog/S6PjCommon.v f3ddc9375b1d
   (gs_cstr_kept holds under cstr_ok's `p + len + 1` ceiling), S6PjStrcmp.v de1559aa1234 (the ledger's `most own`) and
   PRW_StepKit.v 0df3991c13f4 (the S7b walk c50d0958c0b, pa_slot_lt_ceil_b), one copy each, as the cut carries them.
   The top theorems pj_get_holds_B_top / pj_get_str_holds_B_top take ONE hypothesis, ASC : astrcmp_realizes_xrom (the
   strcmp row at the wrapper, family 1b's text, owner c-libc-stdio), by name; the call goes through c-omx-alloc's
   aj_strcmp_at_xrom. pj_get_holds_B_K0 / pj_get_str_holds_B_K0 also take LAWS and TL (PALib) for any B, ARx;
   pj_get_holds_B_inst / pj_get_str_holds_B_inst are the same for any P with srr_inv_laws and srr_inv_call
   (P := YAkMemnorm.memnorm: srr_inv_laws_memnorm_k, srr_inv_call by identity). Print Assumptions: the
   primitive-integer / primitive-string axioms and functional_extensionality_dep only.
   Rule 24: no donor and no image-B walk (proof-index pj_get / pj_get_str exit 0: released hits are the plain /
   UBSan images only; 662-ref one-ref-per-call git grep by name and by the A / B entry addresses, 0 failures;
   a Theorem Labs lane's internal file b-pjget-r24-hits.tsv); the old SR-form B ports are at another pin.
   Numerals: 16 / 96 (LENGTH: the frames of pj_get_str and pj_get, B's pi_frame F_pj_get_str / F_pj_get), 24 / 28
   (LENGTH: node-header and return-slot offsets), 4 / 6 (WORD: the tags of PjTree.JStr / JObj), 8 / 3 / 4 / 7 (LENGTH: word,
   granule log, stack alignment, granule mask), 56 (LENGTH: a node), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 47 - 2 ^ 23 (DERIVED:
   shadow and stack bounds); atom indices (DERIVED: the engine's numbering). No address literal: addresses are pa_sigma /
   pa_val of PAImg_prog.v, offsets computed from its slots. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnPj CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon S6PjStrcmp.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
(* the PLAIN build's sink head must never fill SK here (YC1fP.v:23-33 does the same): every SK below is explicit *)
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* pj_get_str's offset in the listing (DERIVED: its slot times 4, PAImg_prog B_entry_pj_get_str) *)
Definition AF_gsB : Z := 4 * Z.of_nat (B_prog_slot AS_pj_get_str).
(* the shadow base atom (an extra env slot, 32) and the span the token engine checks it against *)
Definition GS_BxB : sv := SOff 32 0.
Definition GS_BspanB : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 16 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition gs_regionsB : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition gs_factsB : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_gsB : sstate := mkSS AF_gsB sr_atoms gs_regionsB None gs_factsB.
(* ---- the seat after the call, at the call's return slot (AF_gsB + 28), over the registers the call returns: sp is atom 2
   (the entry sp - 16), s0 the shadow base (atom 8, the second stretch's shadow base), a0 the member pj_get returned
   (atom 10); the frame holds the entry s0 (atom 32) and ra (atom 33); when a0 <> 0 the member's type word (atom 34)
   and str word (atom 35) ---- *)
Definition GS_Bx2B : sv := SOff 8 0.
Definition gs_stk2B : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition gs_nodeB : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0))].
Definition gs_facts0B : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition gs_facts2B : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (10%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3)] [] [].
Definition ss_gs2B : sstate := mkSS (AF_gsB + 28) sr_atoms [gs_stk2B; gs_nodeB] None gs_facts2B.
Definition ss_gs0B : sstate := mkSS (AF_gsB + 28) sr_atoms [gs_stk2B] None gs_facts0B.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg B_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).

Definition gs_EB (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition gs_E2B (regs : bvmap 5 word) (s0 ra ty st : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (map (Z_to_bv 64) [s0; ra; ty; st])).
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_B (pgb_Hent / pgb_Hobj at the end): pj_get_str's entry (DERIVED: slot
   * 4, PAImg_prog B_entry_pj_get_str), the GOT word of the shadow base and the shadow cell lie in the image's
   segments *)
Hypothesis Hent : SIGMA AS_pj_get_str = BASE + AF_gsB.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* the memory invariant the walk keeps (the layering hold, 2026-10-29: the m-form over a generic P; the text is the
   instance at YAkMemnorm.memnorm, through S6PjStrcmp.v tpj_get_str_specX_of_P) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* alloc.c's statics (prh_img_B's generated addresses) are below YM05.alloc_ceiling *)
Lemma gs_pst_lowB : forall a, Exists (in_zr a) PST -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* a harness block of the ledger lies below YM05.alloc_ceiling, its head too *)
Lemma gs_lam_lowB : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 4096 <= a - 16 /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
    In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & Hhp & _).
change (@cf_head CP) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
rewrite gs_req in Hc by lia. repeat split; try lia; assumption.
Qed.

Lemma gs_framesB : STK_pj_get_str (PI := prh_img_B) = 16 + STK_pj_get (PI := prh_img_B) /\
  STK_pj_get (PI := prh_img_B) = 96 + 2 * ESTACK.
Proof. split; vm_compute; reflexivity. Qed.

Lemma gs_entryB : forall ly S Hp W (regs : bvmap 5 word) mem md ch,
  afn_pre_x SEGS B ARx (STK_pj_get_str (PI := prh_img_B)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (gs_EB regs) ss_gsB (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gsB)) mem (seg_rom SEGS))) /\
  sh_ok SEGS GS_BxB [] (gs_EB regs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (Hobj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
destruct gs_framesB as [FS FS2].
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := gs_EB regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold gs_EB; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold gs_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold gs_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_gsB. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gs_regionsB, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 GS_BxB SHADOW_OFF);
    [cbn [sv_denot GS_BxB]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold gs_regionsB, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS FS2 Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [gs_factsB f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS FS2 Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* a shadow check of a load from the member node (atom 10) inside the kids block's user range *)
Ltac gs_shB EM F8 S08 F10 Hz Hbs :=
lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
cbn [ms_mem]; rewrite ?EM; unfold GS_Bx2B;
rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
rewrite ?F8, ?S08, ?F10, ?Hz; unfold w64;
rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia);
rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
  change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
eapply block_shadow_range; [exact Hbs | lia | lia].

Theorem pj_get_str_holds_B :
  tpj_get_specXP (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK P ->
  tpj_get_str_specXP (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK P.
Proof.
intros GET. unfold tpj_get_str_specXP.
intros ly S Hp W regs mem md ch o k kname t D Lam peak cnt fail ran most own [HPRE [HROD [HTOP [HRAZ HFRM]]]] H10 H11 HO HK HLED.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct gs_framesB as [FS FS2]. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (gs_entryB ly S Hp W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (gs_EB regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold gs_EB; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold gs_EB; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
(* the walk keeps m |-> (P mem -> P m) (YSRrMemnorm.srr_inv_laws_imp); at entry it is P mem -> P mem *)
pose proof (srr_inv_laws_imp SEGS P mem PLAW) as RLAW.
assert (HPM : P mem -> P mem) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_B) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_gsB)) with (Z_to_bv 64 (BASE + AF_gsB)).
(* ---- slots 0-6: the frame, s0 = the shadow base, the call of pj_get ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM GS_BspanB; [gs_awr regs Usp|].
(* ---- the call state: the frame's two words written, every other byte as at entry ---- *)
clear HF HG.
assert (Hsp47 : YM05.alloc_ceiling <= spZ regs - STK_pj_get_str (PI := prh_img_B) /\ spZ regs <= 2 ^ 47) by lia.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hn. apply (gs_mr_keep E (ss_mem ss_gsB) _ _ a HFr); [|exact Ha].
  intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp in Hr|..]; lia. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hn; unfold aview, mbyte; rewrite (KM a Ha Hn); reflexivity).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KA; lia).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (HspT : spZ (ms_regs ms) = spZ regs - 16)
  by (unfold spZ at 1; rewrite R2, Usp; rewrite unsigned_lit_small by lia; lia).
(* pj_get's premises at the call state *)
assert (HROD1 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) (ms_mem ms)))
  by exact (gs_rod_kept B W W mem (ms_mem ms) HROD KL).
assert (HK1 : cstr_ok (PA := PA) W (ms_mem ms) k kname) by exact (gs_cstr_kept W W mem (ms_mem ms) k kname HK KL).
assert (HLED1 : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own HLED).
  - intros a Ha. apply KL. exact (gs_pst_lowB a Ha).
  - intros a k0 i Hin Hi. change (@cf_head CP) with 16.
    destruct (gs_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own a k0 HAR HLED Hin) as (H4 & Hk0 & Hc & _). apply KL. lia.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
assert (HO1 : o = 0 \/ pj_nodeR SEGS (mrestrict (w_H W) (ms_mem ms)) (prh_lin Lam) o t D /\
  prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_B)) ly S W (ms_regs ms) (ms_mem ms) o).
{ destruct HO as [Ho0 | (Hnode & Hrs)]; [left; exact Ho0 | right].
  destruct Hrs as (H4096 & Hplace & Hamr & Hwin & HRA & HHU).
  unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hamr.
  split.
  - apply (pj_nodeR_frame SEGS t (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) (prh_lin Lam) o D Hnode).
    apply gs_agree. intros x Hx. destruct Hx as [Hx | (b & Hb & Hx)].
    + apply KM; [lia|]. intros Hc. apply (Hwin x Hx). lia.
    + pose proof (pj_nodeR_lblk t _ _ _ _ Hnode b Hb) as Hl. unfold prh_lin in Hl. destruct b as [a0 k0].
      destruct (gs_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own a0 k0 HAR HLED Hl) as (H4 & _ & Hc & _).
      unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply KM; lia.
  - split; [exact H4096|]. split.
    { destruct Hplace as [Hp1 | [Hp2 | Hp3]]; [left; exact Hp1 | right; left; exact Hp2 | right; right; rewrite HspT; lia]. }
    split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; exact Hamr|].
    split; [intros a Ha; rewrite HspT; intros Hc; apply (Hwin a Ha); lia|].
    split.
    + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KL. lia.
    + intros s0 Hs. pose proof (gs_hull_low o 56 s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs). rewrite KL by lia. apply HHU. exact Hs. }
assert (Ha0 : getr (ms_regs ms) 10 = w64 o) by (rewrite R10, E10; exact H10).
assert (Ha1 : getr (ms_regs ms) 11 = w64 k) by (rewrite R11, E11; exact H11).
(* ---- the call of pj_get, by its text ---- *)
assert (HTOP1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite HspT; lia).
eapply SRr_bind.
{ eapply (aj_call_x_sp (SK := SK) SEGS B PST ARx LAWS Hsegs W E _ ms (STK_pj_get_str (PI := prh_img_B)) (spZ regs) []
    ly S Hp W mem md [] ly S Hp _ 0 (STK_pj_get (PI := prh_img_B)) [] (-16) _ [] _ HS eq_refl HJ).
  - exact HspT.
  - reflexivity.
  - lia.
  - rewrite FS2. lia.
  - rewrite FS. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - (* the return pc BASE + AF_gsB + 28 is at least 4096: 0 <= BASE (pa_B_ok) and the jal's listing offset, computed *)
    pose proof (@pa_B_ok _ _ PA) as HB.
    lazymatch eval vm_compute in AF_gsB with ?n => assert (EAF0 : AF_gsB = n) by (vm_compute; reflexivity) end.
    rewrite ?EAF0. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite R8, E32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SHADOW_OFF. lia.
  - intros HPRE1.
    (* fpre's return-address bound, from the jal's own return pc (a listing literal) *)
    assert (HRAZ1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
    { unfold raZ. rewrite R1. pose proof (@pa_B_ok _ _ PA) as HB.
      lazymatch eval vm_compute in AF_gsB with ?n => assert (EAF0 : AF_gsB = n) by (vm_compute; reflexivity) end.
      pose proof (pa_slot_lt_ceil_b (PL := PL_prog_B) (PI := PA) (AF_gsB + 28)
        ltac:(rewrite EAF0; lia) ltac:(vm_compute; reflexivity)) as HSL.
      pose proof asan_consts as (CA & _). rewrite EAF0 in HSL. rewrite ?EAF0. rewrite unsigned_lit_small by lia. lia. }
    exact (GET ly S Hp W (ms_regs ms) (ms_mem ms) _ [] o k kname t D Lam peak cnt fail ran most own
      (conj HPRE1 (conj HROD1 (conj HTOP1 (conj HRAZ1 HFRM)))) Ha0 Ha1 HO1 HK1 HLED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ2).
(* ---- after the call: registers, the frame's two words, the results ---- *)
destruct HQ2 as ((EHp & ES2 & Eab & HLED2 & HROOM2 & HRES2) & HKP). subst Hp2.
(* the keep across the call: the walk's keep up to the call, then the callee's own *)
assert (HPM2 : P mem -> P mem2) by (intros h; exact (HKP (HPM h))). clear HPM HKP. rename HPM2 into HPM.
assert (P2 : getr regs2 2%bv = getr (ms_regs ms) 2%bv).
{ pose proof (HP2 2 ltac:(unfold acallee_saved; lia)) as H. replace (Z_to_bv 5 2) with (2%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (P8 : getr regs2 8%bv = getr (ms_regs ms) 8%bv).
{ pose proof (HP2 8 ltac:(unfold acallee_saved; lia)) as H. replace (Z_to_bv 5 8) with (8%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (Sp2 : spZ regs2 = spZ regs - 16) by (unfold spZ; rewrite P2; exact HspT).
assert (S08 : getr regs2 8%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite P8, R8, E32; reflexivity).
assert (E8 : ew E 8 = getr regs 8%bv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
set (s0e := bv_unsigned (getr regs 8%bv)). set (rae := bv_unsigned (getr regs 1%bv)).
assert (Hs0r : 0 <= s0e < 2 ^ 64) by (subst s0e; pose proof (bv_unsigned_in_range 64 (getr regs 8%bv)) as H; exact H).
assert (Hrar : 0 <= rae < 2 ^ 64) by (subst rae; pose proof (bv_unsigned_in_range 64 (getr regs 1%bv)) as H; exact H).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & KJc & _).
assert (VSL : forall od e v, In (YP09.mkChunk od (CVal 8 e))
    [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  (od = -16 \/ od = -8) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + od) 8 v).
{ intros od e v Hin Hod He Hv.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (st_ok_region_nth SEGS E ss _ 0 (YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0
      [YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS eq_refl) as RG0 end.
  pose proof (slot_of_region SEGS E _ (spZ regs) _ _ _ _ _ od e v RG0 Usp Hin He Hv) as V0.
  cbn [ms_mem restrict] in V0.
  apply (val_mem_kept SEGS (w_H W) (w_H W2) (ms_mem ms) mem2 (spZ regs + od) 8 v); [|exact V0].
  intros kk Hkk. apply KJc; lia. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + -16) 8 s0e).
{ apply (VSL (-16) (SOff 8 0) s0e (or_introl eq_refl) (or_introl eq_refl)); [|exact Hs0r].
  cbn [sv_denot]. rewrite E8, Z.add_0_r. subst s0e. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (VRA : val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs + -8) 8 rae).
{ apply (VSL (-8) (SOff 1 0) rae (or_intror (or_introl eq_refl)) (or_intror eq_refl)); [|exact Hrar].
  cbn [sv_denot]. rewrite E1, Z.add_0_r. subst rae. rewrite Z_to_bv_bv_unsigned. reflexivity. }
clear VSL KJc.
(* the return slot's offset, computed (no typed value) *)
lazymatch eval vm_compute in (AF_gsB + 28) with ?n => assert (EAF : AF_gsB + 28 = n) by (vm_compute; reflexivity) end.
rewrite <- EAF.
(* ---- the tail with a0 = 0 ---- *)
match goal with |- ?G => assert (TAIL0 : getr regs2 10%bv = w64 0 ->
  (o = 0 \/ o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D /\
     prhPj_get_str_res (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D kname 0) -> G) end.
{ intros Hz0 HR0.
  set (EZ := gs_E2B regs2 s0e rae 0 0).
  assert (EL2 : forall n, (n < A_TEXT)%nat -> ew EZ n = ew (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; 0; 0])) n)
    by (intros n Hn; subst EZ; unfold gs_E2B; apply Eimg_low; exact Hn).
  assert (F2 : ew EZ 2 = getr regs2 2%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
  assert (F8 : ew EZ 8 = getr regs2 8%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
  assert (F32 : ew EZ 32 = Z_to_bv 64 s0e)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F33 : ew EZ 33 = Z_to_bv 64 rae)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Usp2 : bv_unsigned (ew EZ 2) = spZ regs - 16) by (rewrite F2; exact Sp2).
  assert (HEI2 : img_env VAL A_LIM EZ) by (subst EZ; unfold gs_E2B; apply Eimg_env).
  assert (HS2 : st_ok_pi SEGS VAL EZ ss_gs0B
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_gsB + 28))) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_gs0B. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold gs_stk2B. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp2.
      split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 0 8 (SOff 32 0) s0e);
          [cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact VS0.
      + apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 8 8 (SOff 33 0) rae);
          [cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
        replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact VRA.
    - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [gs_facts0B f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp2, F8, S08, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  pose proof (st_ok_pi_pin_reg' (PI := PA) EZ ss_gs0B _ 10%bv 0 HS2 ltac:(cbn [ms_regs restrict mkst]; exact Hz0) eq_refl) as HS3.
  clear HS2.
  assert (SHOK3 : sh_ok SEGS GS_Bx2B [] EZ (mrestrict (w_H W2) mem2)) by constructor.
  paj_run_tok_x_inv RUN HS3 HJ2 SHOK3 HPM GS_BspanB; [gs_awr0|].
  (* slots 7, 23-26: a0 = 0, the frame back, ret *)
  eapply (RET W2 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  assert (EM : ms_mem ms0 = mem2).
  { apply functional_extensionality. intros x. apply HF. intros (r & Hin & Hr). vm_compute in Hin.
    destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  prreg HS3 (1%bv : bv 5) G1. prreg HS3 (2%bv : bv 5) G2. prreg HS3 (8%bv : bv 5) G8. prreg HS3 (10%bv : bv 5) G10.
  assert (GF2 : getr (ms_regs ms0) 2%bv = getr regs 2%bv).
  { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  assert (GF8 : getr (ms_regs ms0) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (rewrite HE; split; [intros n Hn; unfold gs_EB; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HAEZ : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; 0; 0])) EZ)
    by (split; [intros n Hn; subst EZ; unfold gs_E2B; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF] gs_kept HS HAE ltac:(vm_compute; reflexivity)) as K1.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) EZ _ _ regs2 _ gs_kept HS3 HAEZ ltac:(vm_compute; reflexivity)) as K3.
  unfold fpost, apost_base_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
  split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
  split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
  split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms0) K1 HP2 K3 GF2 GF8)|].
    split; [|exact HPM].
  split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EM; exact HLED2|]. split; [exact HROOM2|].
  destruct HR0 as [Ho0 | (Hon & Hnd & Hgs)].
  - left. split; [exact Ho0 | rewrite G10; reflexivity].
  - right. split; [exact Hon|]. split; [rewrite EM; exact Hnd|]. exists 0. split; [rewrite G10; reflexivity | rewrite EM; exact Hgs]. }
(* ---- the tail with a0 = the member pj_get found ---- *)
match goal with |- ?G => assert (TAIL2 : forall z (members : list (list Z * jv)) i v kids Di,
  t = JObj members -> o <> 0 -> getr regs2 10%bv = w64 z ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) o t D ->
  nth_error members i = Some (kname, v) ->
  (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname) ->
  rd_u64 SEGS (mrestrict (w_H W2) mem2) (o + 24) kids -> z = kids + 56 * Z.of_nat i ->
  pj_nodeR SEGS (mrestrict (w_H W2) mem2) (prh_lin Lam) z v Di -> incl Di D -> G) end.
{ intros z members i v kids Di Et Hon Hz Hnode2 Hnth Hfirst Hkids Ez Hnodez Hincl.
  pose proof HJ2 as (HAR2 & _).
  (* the object's kids block, a live harness block, holds the member's node *)
  pose proof Hnode2 as Hnode2'. rewrite Et in Hnode2'. cbn [pj_nodeR] in Hnode2'.
  destruct Hnode2' as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hhdr0 & Es0 & En0 & Hc0 & Hcap0 & _).
  destruct Hhdr0 as (_ & _ & _ & _ & Hk0 & _).
  pose proof (gs_val8_uniq _ _ _ _ (proj2 Hkids) (proj2 Hk0) (proj1 Hkids) (proj1 Hk0)) as EK. subst kids0.
  pose proof (pj_nth_lenR members i (kname, v) Hnth) as Hil.
  destruct Hcap0 as [(Hc00 & _) | (Hcp & Hlk & _)]; [lia|].
  unfold prh_lin in Hlk.
  destruct (gs_lam_lowB ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail ran most own kids (56 * cap0) HAR2 HLED2 Hlk)
    as (Hk4 & _ & Hkc & Hkab & Hkhp).
  assert (Hzr : 4096 <= z /\ z + 56 <= kids + 56 * cap0) by (subst z; lia).
  (* the member's type and str words *)
  destruct (gs_node_hdr _ _ _ _ _ Hnodez) as (numz & strz & kidsz & keysz & nz & capz & Hhdrz).
  destruct Hhdrz as ((Hz8 & _) & (Hty0 & Hty) & _ & (Hst0 & Hst) & _).
  (* the shadow of the kids block's user bytes (AR_laws_x field 14, alx_hshadow, at the harness head cf_head) *)
  destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp W2 mem2 md2 (kids - 16) (56 * cap0 + 16) HAR2 Hkab Hkhp) as [Hbs _].
  change (@cf_head CP) with 16 in Hbs. rewrite gs_req in Hbs by lia.
  replace (kids - 16 + 16) with kids in Hbs by lia. replace (56 * cap0 + 16 - 16) with (56 * cap0) in Hbs by lia.
  assert (Hzz : 0 <= z < 2 ^ 64) by lia.
  set (EZ := gs_E2B regs2 s0e rae (tag v) strz).
  assert (EL2 : forall n, (n < A_TEXT)%nat -> ew EZ n = ew (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) n)
    by (intros n Hn; subst EZ; unfold gs_E2B; apply Eimg_low; exact Hn).
  assert (F2 : ew EZ 2 = getr regs2 2%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
  assert (F8 : ew EZ 8 = getr regs2 8%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
  assert (F10 : ew EZ 10 = getr regs2 10%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
  assert (F32 : ew EZ 32 = Z_to_bv 64 s0e)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F33 : ew EZ 33 = Z_to_bv 64 rae)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F34 : ew EZ 34 = Z_to_bv 64 (tag v))
    by (rewrite EL2 by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (F35 : ew EZ 35 = Z_to_bv 64 strz)
    by (rewrite EL2 by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Usp2 : bv_unsigned (ew EZ 2) = spZ regs - 16) by (rewrite F2; exact Sp2).
  assert (Uz : bv_unsigned (ew EZ 10) = z) by (rewrite F10, Hz; unfold w64; apply unsigned_lit_small; exact Hzz).
  assert (HEI2 : img_env VAL A_LIM EZ) by (subst EZ; unfold gs_E2B; apply Eimg_env).
  assert (HS2 : st_ok_pi SEGS VAL EZ ss_gs2B
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (AF_gsB + 28))) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_gs2B. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold gs_stk2B, gs_nodeB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite Usp2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 0 8 (SOff 32 0) s0e);
            [cbn [sv_denot]; rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          replace (spZ regs - 16 + 0) with (spZ regs + -16) by lia. exact VS0.
        * apply (chunk_ok_val SEGS EZ _ (spZ regs - 16) 8 8 (SOff 33 0) rae);
            [cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia. exact VRA.
      + rewrite Uz. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS EZ _ z 0 4 (SOff 34 0) (tag v));
            [cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          rewrite Z.add_0_r. exact Hty.
        * apply (chunk_ok_val SEGS EZ _ z 16 8 (SOff 35 0) strz);
            [cbn [sv_denot]; rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
          exact Hst.
    - apply pairwise_disjoint_of_extents. unfold gs_stk2B, gs_nodeB, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?Usp2, ?Uz.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - split; [|split; [exact I | exact I]].
      cbn [gs_facts2B f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp2, Uz, F8, S08, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (SHOK2 : sh_ok SEGS GS_Bx2B [] EZ (mrestrict (w_H W2) mem2)) by constructor.
  (* the shadow checks of the member's loads: inside the kids block's user range *)
  assert (UB : U EZ GS_Bx2B = SHADOW_OFF)
    by (unfold GS_Bx2B; exact (U_atom EZ 8 SHADOW_OFF (eq_trans F8 S08) ltac:(unfold SHADOW_OFF; lia))).
  assert (UZ : U EZ (SOff 10 0) = z) by exact (U_atom EZ 10 z (eq_trans F10 Hz) Hzz).
  paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM GS_BspanB.
  all: try gs_awr0.
  all: try (match goal with |- range_addressable _ _ _ _ => idtac end;
    cbn [ms_mem]; rewrite ?UB, ?UZ;
    change (rd_of SEGS (mrestrict (w_H W2) mem2)) with (aview SEGS (w_H W2) mem2);
    eapply (block_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF kids (56 * cap0)); [exact Hbs | lia | lia]).
  gs_memeq HF EM1. clear HF HG.
  (* the registers the caller kept, for the post *)
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (rewrite HE; split; [intros n Hn; unfold gs_EB; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HAEZ : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) EZ)
    by (split; [intros n Hn; subst EZ; unfold gs_E2B; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF] gs_kept HS HAE ltac:(vm_compute; reflexivity)) as K1.
  (* slot 14: bne a1, a2 on the member's type word against JStr's tag *)
  psrr_branch_tok RUN BR HS2 SHOK2 GS_BspanB.
  - (* taken: the member is not a string; a0 = 0, the frame back, ret *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc v F34. rewrite U_SLit in Hc.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia).
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM GS_BspanB; [gs_awr0|].
    gs_memeq HF EM2. clear HF HG.
    eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS2 with st_ok_pi _ _ ?E'' _ (restrict _ ?msF) =>
      assert (EMf : ms_mem msF = mem2) by (rewrite EM2; exact EM1);
      assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag v; strz])) E'')
        by (eapply env_agree_trans; [exact HAEZ | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E'' _ _ regs2 _ gs_kept HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3 end.
    prreg HS2 (1%bv : bv 5) G1. prreg HS2 (2%bv : bv 5) G2. prreg HS2 (8%bv : bv 5) G8. prreg HS2 (10%bv : bv 5) G10.
    rewrite ?ew_ewset_other in G1 by lia. rewrite ?ew_ewset_other in G2 by lia. rewrite ?ew_ewset_other in G8 by lia.
    assert (GF2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv).
    { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
    assert (GF8 : getr (ms_regs ms1) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
    unfold fpost, apost_base_x.
    lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
    split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
    split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms1) K1 HP2 K3 GF2 GF8)|].
    split; [|exact HPM].
    split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EMf; exact HLED2|]. split; [exact HROOM2|].
    right. split; [exact Hon|]. split; [rewrite EMf; exact Hnode2|]. exists 0. split; [rewrite G10; reflexivity|].
    rewrite EMf, Et. unfold prhPj_get_str_res. right. exists i, v, kids.
    split; [exact Hnth|]. split; [exact Hfirst|]. split; [exact Hkids|].
    destruct v; try reflexivity. exfalso. apply Hc. reflexivity.
  - (* not taken: the member is a string; a0 = its str word *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc v F34. rewrite U_SLit in Hc.
    rewrite (zcanon_id 4) in Hc by (unfold M64; lia).
    apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (gs_tag4 v Hc) as (s & ->).
    paj_run_tok_x_inv RUN HS2 HJ2 SHOK2 HPM GS_BspanB.
    all: try gs_awr0.
    all: try gs_shB EM1 F8 S08 F10 Hz Hbs.
    gs_memeq HF EM2. clear HF HG.
    eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS2 with st_ok_pi _ _ ?E'' _ (restrict _ ?msF) =>
      assert (EMf : ms_mem msF = mem2) by (rewrite EM2; exact EM1);
      assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [s0e; rae; tag (JStr s); strz])) E'')
        by (eapply env_agree_trans; [exact HAEZ | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E'' _ _ regs2 _ gs_kept HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3 end.
    prreg HS2 (1%bv : bv 5) G1. prreg HS2 (2%bv : bv 5) G2. prreg HS2 (8%bv : bv 5) G8. prreg HS2 (10%bv : bv 5) G10.
    rewrite ?ew_ewset_other in G1 by lia. rewrite ?ew_ewset_other in G2 by lia. rewrite ?ew_ewset_other in G8 by lia.
    rewrite ?ew_ewset_other in G10 by lia.
    assert (GF2 : getr (ms_regs ms1) 2%bv = getr regs 2%bv).
    { rewrite G2, Usp2. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
    assert (GF8 : getr (ms_regs ms1) 8%bv = getr regs 8%bv) by (rewrite G8, F32; unfold s0e; apply Z_to_bv_bv_unsigned).
    (* the member's string, from its node *)
    pose proof Hnodez as Hnz. cbn [pj_nodeR] in Hnz.
    destruct Hnz as (_ & _ & num1 & str1 & kids1 & keys1 & n1 & cap1 & Hh1 & _ & _ & _ & _ & k1' & Hcs & ED).
    destruct Hh1 as (_ & _ & _ & (Hs10 & Hs1) & _).
    pose proof (gs_val8_uniq _ _ _ _ Hst Hs1 Hst0 Hs10) as Estr. subst str1.
    unfold fpost, apost_base_x.
    lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, Hp, r, m, d, (0 + k1) end.
    split; [cbn [ms_regs]; rewrite G1, F33; unfold rae; rewrite Z_to_bv_bv_unsigned, Hra; reflexivity|].
    split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
    split; [exact (gs_aregs regs (ms_regs ms) regs2 (ms_regs ms1) K1 HP2 K3 GF2 GF8)|].
    split; [|exact HPM].
    split; [reflexivity|]. split; [exact ES2|]. split; [exact Eab|]. split; [rewrite EMf; exact HLED2|]. split; [exact HROOM2|].
    right. split; [exact Hon|]. split; [rewrite EMf; exact Hnode2|]. exists strz. split; [rewrite G10, F35; reflexivity|].
    rewrite EMf, Et. unfold prhPj_get_str_res. right. exists i, (JStr s), kids.
    split; [exact Hnth|]. split; [exact Hfirst|]. split; [exact Hkids|].
    split; [rewrite <- Ez; split; [exact Hst0 | exact Hst]|].
    exists k1'. split; [exact Hcs|]. apply Hincl. rewrite ED. left. reflexivity. }
destruct HRES2 as [(Ho0 & Hz0) | (Hon & Hnode2 & z & Hz & Hres)].
{ apply TAIL0; [exact Hz0 | left; exact Ho0]. }
destruct t as [| | | txt bits | s | items | members]; cbn [prhPj_get_res] in Hres;
  try (subst z; apply TAIL0; [exact Hz | right; split; [exact Hon|]; split; [exact Hnode2 | reflexivity]]).
destruct Hres as [(Hnone & ->) | (i & v & kids & Di & Hnth & Hfirst & Hkids & Ez & Hnodez & Hincl)].
- apply TAIL0; [exact Hz | right; split; [exact Hon|]; split; [exact Hnode2|]]. cbn [prhPj_get_str_res]. left. split; [exact Hnone | reflexivity].
- exact (TAIL2 z members i v kids Di eq_refl Hon Hz Hnode2 Hnth Hfirst Hkids Ez Hnodez Hincl).
Qed.

End f.
End d.

(* pj_get's offset in the listing (DERIVED: its slot times 4) *)
Definition AF_pgB : Z := 4 * Z.of_nat (B_prog_slot AS_pj_get).
Definition PG_BxB : sv := SOff 32 0.
Definition PG_BspanB : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 96 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition pg_regionsB : smem := [stack_region 96; got_regionP; bcell_regionP 32].
Definition pg_factsB : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pgB : sstate := mkSS AF_pgB sr_atoms pg_regionsB None pg_factsB.
(* the node's header words the code reads (atom 10 = o): type (atom 33), kids (34), keys (35), n (36) *)
Definition pg_nodeB : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 56 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0));
    YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0))].
(* ---- the member loop's seat, at the loop head (AF_pgB + 180, slot 45: `seqz a0, s2`), over the registers the loop
   holds: s0 = o (the node, atom 8), s1 = k, s2 = s9 = keys + 8 i (atoms 18 / 25), s3 = the shadow base (atom 19),
   s4 = - 56 i, s5 = i, s6 = n, s7 = keys (atom 23), s8 = 1; the frame of 96 bytes below the entry sp holds the eleven
   saved registers (atoms 34 .. 44, offsets 8 .. 88); the node's kids word (atom 33, offset 24) and the i-th key word
   (atom 32, at keys + 8 i) ---- *)
Definition pg_saves : list (Z * bv 5) :=
  [(8, 25%bv); (16, 24%bv); (24, 23%bv); (32, 22%bv); (40, 21%bv); (48, 20%bv); (56, 19%bv); (64, 18%bv);
   (72, 9%bv); (80, 8%bv); (88, 1%bv)].
Definition PGL_Bx : sv := SOff 19 0.
Definition pgl_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 96 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
     YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 48 (CVal 8 (SOff 39 0));
     YP09.mkChunk 56 (CVal 8 (SOff 40 0)); YP09.mkChunk 64 (CVal 8 (SOff 41 0)); YP09.mkChunk 72 (CVal 8 (SOff 42 0));
     YP09.mkChunk 80 (CVal 8 (SOff 43 0)); YP09.mkChunk 88 (CVal 8 (SOff 44 0))].
Definition pgl_node : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition pgl_key : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition pgl_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (8%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (18%nat, mkAF 4096 (2 ^ 47 - 8) 3); (25%nat, mkAF 4096 (2 ^ 47 - 8) 3); (23%nat, mkAF 4096 (2 ^ 47) 3);
           (24%nat, mkAF 1 1 0); (21%nat, mkAF 0 (2 ^ 44) 0)] [] [].
Definition ss_pgl : sstate := mkSS (AF_pgB + 180) sr_atoms [pgl_stk; pgl_node; pgl_key] None pgl_facts.

Section dg. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg B_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).

(* the entry env: the registers, the shadow base (atom 32) and the node header words (atoms 33 .. 36: type, kids, keys,
   n; zero when there is no node) *)
Definition pg_EB (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)).
(* the loop seat's env: the loop's registers, the i-th key word (atom 32), the kids word (atom 33), and the entry's
   eleven saved registers in the frame's offset order (atoms 34 .. 44) *)
Definition pgl_E (regsL regs : bvmap 5 word) (xi kd : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regsL (Z_to_bv 64 xi :: Z_to_bv 64 kd :: map (fun sr => getr regs (snd sr)) pg_saves)).

Section fg.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_B (pgb_Hent_get / pgb_Hobj at the end): pj_get's entry, the GOT word of
   the shadow base and the shadow cell in the image *)
Hypothesis Hent : SIGMA AS_pj_get = BASE + AF_pgB.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
(* the memory invariant the walk keeps (the layering hold, 2026-10-29: the m-form over a generic P) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS P.
(* the invariant crosses the strcmp call, whose row keeps YAkMemnorm.memnorm only (h-hpreset-7 12:22Z) *)
Hypothesis PCALL : srr_inv_call SEGS P.
(* the callee: c-libc-stdio's strcmp row at the wrapper, by name (YGcallMxmn.v astrcmp_realizes_xrom, family 1b:
   the read-only premise as arodata_okP, the YAkMemnorm keep last); the call goes through aj_strcmp_at_xrom *)
Hypothesis ASC : astrcmp_realizes_xrom SEGS B ARx (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) (SIGMA AS___wrap_strcmp).
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

Lemma pg_frameB : STK_pj_get (PI := prh_img_B) = 96 + 2 * ESTACK.
Proof. vm_compute. reflexivity. Qed.

(* ---- the post: the text's lambda, named ---- *)
Definition pg_postB (ly : alayout) (S : astate) (Hp : list Z) (o : Z) (t : jv) (D Lam : list (Z * Z)) (kname : list Z)
  (peak cnt fail ran most own : Z) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' _ =>
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
  (room_live_cf S -> room_live_cf S') /\
  (o = 0 /\ getr regs' 10 = w64 0 \/
   o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) o t D /\
   exists z, getr regs' 10 = w64 z /\ prhPj_get_res (PA := PA) (mrestrict (w_H W') mem') (prh_lin Lam) o t D kname z).
(* the post with the keep of P: tpj_get_specXP's lambda, named *)
Definition pg_postPB (mem : word -> option byte) (ly : alayout) (S : astate) (Hp : list Z) (o : Z) (t : jv)
  (D Lam : list (Z * Z)) (kname : list Z) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
  pg_postB ly S Hp o t D Lam kname peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' /\ (P mem -> P mem').
(* the callee-saved registers (YG0d.v acallee_saved), as register names *)
Definition pg_allB : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma pg_aregsB : forall (regs regsF : bvmap 5 word),
  (forall r : bv 5, In r pg_allB -> getr regsF r = getr regs r) -> aregs_preserved regs regsF.
Proof.
intros regs regsF H r Hr. apply H. unfold pg_allB. apply in_map. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [cbn; tauto .. |].
assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct H0 as [-> | H0]; [cbn; tauto|]). subst r. cbn; tauto.
Qed.
(* alloc.c's statics (prh_img_B's generated addresses) are below YM05.alloc_ceiling *)
Lemma pg_pst_lowB : forall a, Exists (in_zr a) PST -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a H. apply Exists_exists in H as (r & Hin & Hr). pose proof asan_consts as (C1 & _).
vm_compute in Hin. unfold in_zr in Hr.
repeat (destruct Hin as [<- | Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* a harness block of the ledger lies below YM05.alloc_ceiling, its head too *)
Lemma pg_lam_lowB : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 4096 <= a - 16 /\ 0 <= k /\ a + k <= YM05.alloc_ceiling /\
    In (a - 16, k + 16) (ablocks B ly S) /\ In (a - 16) Hp.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk0 & Hab & Hhp & _).
change (@cf_head CP) with 16 in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - 16) (k + 16) HAR Hab) as (_ & H4096 & Hc & _).
rewrite gs_req in Hc by lia. repeat split; try lia; assumption.
Qed.
(* the ledger at a memory that agrees below YM05.alloc_ceiling *)
Lemma pg_ledger_keptB : forall ly S Hp W mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HL KL.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HL).
- intros a Ha. apply KL. exact (pg_pst_lowB a Ha).
- intros a k0 i Hin Hi. change (@cf_head CP) with 16.
  destruct (pg_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own a k0 HAR HL Hin) as (H4 & Hk0 & Hc & _).
  pose proof asan_consts as (C1 & _). apply KL. lia.
- intros a k0 _ H. exact H.
- apply Permutation_refl.
Qed.
(* an invariant of the end memory, moved into the post's lambda (an fpost's memory is its config's) *)
Lemma pg_keepB : forall regs ly S Hp W mem md
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : (word -> option byte) -> Prop) W' c',
  fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md Q W' c' ->
  R (ms_mem (cfg_ms c')) ->
  fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
    (fun ly' S' Hp' W'' regs' mem' md' => Q ly' S' Hp' W'' regs' mem' md' /\ R mem') W' c'.
Proof.
intros regs ly S Hp W mem md Q R W' c' H HR. unfold fpost, apost_base_x in *.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & -> & HJ & HA & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [reflexivity|]. split; [exact HJ|]. split; [exact HA|].
split; [exact HQ | exact HR].
Qed.
(* every exit: the registers back, the journal from the entry, the memory below YM05.alloc_ceiling as at entry *)
Lemma pg_finB : forall ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memF mdF k0 ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall r : bv 5, In r pg_allB -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  getr regsF 10%bv = w64 res ->
  (o = 0 /\ res = 0 \/ o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o t D /\
     prhPj_get_res (PA := PA) (mrestrict (w_H W) memF) (prh_lin Lam) o t D kname res) ->
  fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
    (pg_postB ly S Hp o t D Lam kname peak cnt fail ran most own) W
    (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res
  HAR HLED HJ KL Hra Hkept G1 G10 HR.
unfold fpost, apost_base_x.
exists ly, S, Hp, regsF, memF, (with_vm_backing (m_vm_lazy mdF) mat mdF), k0.
split; [rewrite G1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact (pg_aregsB regs regsF Hkept)|].
unfold pg_postB. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (pg_ledger_keptB ly S Hp W mem md memF Lam peak cnt fail ran most own HAR HLED KL)|].
split; [intros H; exact H|].
destruct HR as [(Ho0 & ->) | (Hon & Hnd & Hres)]; [left; split; [exact Ho0 | exact G10]|].
right. split; [exact Hon|]. split; [exact Hnd|]. exists res. split; [exact G10 | exact Hres].
Qed.
(* the same with the keep of P (the function-level exits) *)
Lemma pg_finPB : forall ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memF mdF k0 ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall r : bv 5, In r pg_allB -> getr regsF r = getr regs r) -> getr regsF 1%bv = getr regs 1%bv ->
  getr regsF 10%bv = w64 res ->
  (o = 0 /\ res = 0 \/ o <> 0 /\ pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o t D /\
     prhPj_get_res (PA := PA) (mrestrict (w_H W) memF) (prh_lin Lam) o t D kname res) ->
  (P mem -> P memF) ->
  fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
    (pg_postPB mem ly S Hp o t D Lam kname peak cnt fail ran most own) W
    (mkCfg (mkst regsF (v_jalr (getr regsF 1%bv) 0) memF (seg_rom SEGS)) (with_vm_backing (m_vm_lazy mdF) mat mdF)).
Proof.
intros ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own regsF memF mdF mat k0 res
  HAR HLED HJ KL Hra Hkept G1 G10 HR KP.
unfold fpost, apost_base_x.
exists ly, S, Hp, regsF, memF, (with_vm_backing (m_vm_lazy mdF) mat mdF), k0.
split; [rewrite G1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
split; [exact (pg_aregsB regs regsF Hkept)|].
unfold pg_postPB. split; [|exact KP].
unfold pg_postB. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (pg_ledger_keptB ly S Hp W mem md memF Lam peak cnt fail ran most own HAR HLED KL)|].
split; [intros H; exact H|].
destruct HR as [(Ho0 & ->) | (Hon & Hnd & Hres)]; [left; split; [exact Ho0 | exact G10]|].
right. split; [exact Hon|]. split; [exact Hnd|]. exists res. split; [exact G10 | exact Hres].
Qed.

Lemma pg_entryB : forall ly S Hp W (regs : bvmap 5 word) mem md ch xs,
  afn_pre_x SEGS B ARx (STK_pj_get (PI := prh_img_B)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (pg_EB regs xs) ss_pgB (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pgB)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PG_BxB [] (pg_EB regs xs) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch xs HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
pose proof (pal_got_cell B TL) as HgcD.
assert (HgL : forall i, 0 <= i < 8 -> 0 <= VAL (A_OBJ 0) + i < kLowMemEnd /\ 0 <= VAL (A_OBJ 12) + i < kLowMemEnd).
{ intros i Hi. destruct (Hobj i Hi) as [H1 H2]. split; apply (@pa_segs_low _ _ PA); assumption. }
destruct (HgL 0 ltac:(lia)) as [HgotR HcellR]. destruct (HgL 7 ltac:(lia)) as [HgotR7 HcellR7].
pose proof pg_frameB as FS.
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := pg_EB regs xs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold pg_EB; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold pg_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold pg_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_pgB. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pg_regionsB, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PG_BxB SHADOW_OFF);
    [cbn [sv_denot PG_BxB]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold pg_regionsB, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pg_factsB f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the tree's footprint (header and blocks) is off the image and outside pj_get's stack window *)
Lemma pg_footB : forall ly S Hp W mem md regs o t D Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_B) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) o t D ->
  prhPj_rslot (PA := PA) B (STK_pj_get (PI := prh_img_B)) ly S W regs mem o ->
  forall x, pj_footR o D x ->
  0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= x < spZ regs).
Proof.
intros ly S Hp W mem md regs o t D Lam peak cnt fail ran most own HAR HL Hlo Hn Hrs x Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hrs as (H4096 & Hplace & Hamr & Hwin & _).
assert (Hamr' : o + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
destruct Hx as [Hx | (b & Hb & Hx)].
- split; [lia|]. split; [|exact (Hwin x Hx)].
  destruct Hplace as [(p & n & Hin & Hp1 & Hp2) | [(cid & pos & Hin & Hp1 & Hp2) | (Hsp1 & Hsp2)]].
  + refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_introl _))).
    exists p, n. split; [exact Hin | lia].
  + refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_intror (or_introl _)))).
    exists cid, pos. split; [exact Hin | lia].
  + intros Himg. pose proof (@pa_segs_low _ _ PA x Himg). pose proof pg_frameB.
    assert (ESTACK = 4096) by reflexivity. unfold kLowMemEnd in *. lia.
- pose proof (pj_nodeR_lblk t _ _ _ _ Hn b Hb) as Hl. unfold prh_lin in Hl. destruct b as [a0 k0].
  destruct (pg_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own a0 k0 HAR HL Hl) as (H4 & Hk0 & Hc & Hab & _).
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  split; [lia|]. split; [|lia].
  refine (proj2 (alx_client_img SEGS B ARx LAWS ly S Hp W mem md x HAR (or_introl _))).
  exists (a0 - 16), (k0 + 16). split; [exact Hab|]. rewrite gs_req by lia. lia.
Qed.

(* zcanon (the engine's 64-bit wrap) through + and *, and under Z_to_bv 64 *)
Lemma pgl_w64_zc : forall z, Z_to_bv 64 (zcanon z) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma pgl_w64_wrap_add : forall v c, Z_to_bv 64 (bv_wrap 64 v + c) = Z_to_bv 64 (v + c).
Proof.
intros v c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma pgl_zc_add : forall x y, zcanon (zcanon x + zcanon y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. rewrite <- Z.add_mod by lia. reflexivity. Qed.
Lemma pgl_zc_mul : forall x y, zcanon (zcanon x * zcanon y) = zcanon (x * y).
Proof. intros x y. unfold zcanon, M64. rewrite <- Z.mul_mod by lia. reflexivity. Qed.
Lemma pgl_zc_wrap : forall z, zcanon (bv_wrap 64 z) = zcanon z.
Proof.
intros z. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
(* the arithmetic of a refuted UBSan trap branch: drop each zcanon whose argument is in range, then split each test *)
Ltac pgl_zc H :=
  repeat match type of H with context [zcanon ?x] =>
    rewrite (zcanon_id x) in H by (unfold M64; repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia)
  end.
Ltac pgl_ltb H := repeat match type of H with context [?a <? ?b] => destruct (Z.ltb_spec a b) end.
(* a register at the loop head reached from the entry, in U form over the entry env *)
Ltac pg_head_reg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let G := fresh "G" in
    pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
    lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end;
    rewrite G, denot_lit_U; clear G;
    repeat first [rewrite U_SAlu | rewrite U_SOff | rewrite U_SLit]; cbn [zalu_raw];
    rewrite ?ew_ewset_other by lia
  end.
(* the loop registers at the back edge, from the state HS, each against the entry's or the next index's value *)
Ltac pgl_ireg HS OLD :=
  lazymatch goal with |- getr _ ?r = _ =>
    let G := fresh "G" in
    pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
    lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end;
    rewrite G, denot_lit_U; clear G;
    repeat first [rewrite U_SAlu | rewrite U_SOff | rewrite U_SLit]; cbn [zalu_raw];
    rewrite ?ew_ewset_other by lia; rewrite ?OLD by lia
  end.
Ltac pgl_iregs HS OLD ER :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- getr _ ?r = _ =>
      pgl_ireg HS OLD;
      lazymatch goal with |- context [ew _ ?q] => rewrite (ER q r) by (lia || reflexivity) end
  end.
(* a register at a loop exit, from the state HS: the frame's saved word (EX), a kept register (ER, then KR), sp (U2) *)
Ltac pgl_back HS OLD EX ER U2 KR :=
  lazymatch goal with |- getr _ ?r = _ =>
    let G := fresh "G" in
    pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as G;
    lazymatch type of G with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l r) in change (sr_get l r) with e in G end;
    rewrite G; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite ?OLD by lia;
    first [ lazymatch goal with |- context [ew _ ?q] =>
              let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
            rewrite EX by (unfold A_TEXT; lia); cbn [nth map pg_saves snd]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            reflexivity
          | rewrite U2, Z.sub_add; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lazymatch goal with |- context [ew _ ?q] => rewrite (ER q r) by (lia || reflexivity) end;
            rewrite Z.add_0_r, Z_to_bv_bv_unsigned; apply KR ]
  end.
(* the trivial invariant (the P := True corollaries) *)
Lemma pgl_true_laws : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.
(* ======== the member loop (slots 45 .. 66 and the found tail 80 .. 101), one lemma at the loop head ======== *)
Section loop.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (o k : Z) (kname : list Z)
  (members : list (list Z * jv)) (D Lam : list (Z * Z)) (peak cnt fail ran most own num kids keys n cap : Z) (Di : list (Z * Z)).
Hypothesis HPRE : afn_pre_x SEGS B ARx (STK_pj_get (PI := prh_img_B)) ly S Hp W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem).
Hypothesis HK : cstr_ok (PA := PA) W mem k kname.
Hypothesis HLED : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.
Hypothesis Hnode : pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) o (JObj members) D.
Hypothesis HFT : forall x, pj_footR o D x ->
  0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= x < spZ regs).
Hypothesis HRA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o 56.
Hypothesis Hh : pj_hdrR SEGS (mrestrict (w_H W) mem) o 6 num 0 kids keys n cap.
Hypothesis En : n = Z.of_nat (length members).
Hypothesis Hn0 : n <> 0.
Hypothesis Hcn : n <= cap.
Hypothesis Hcap : cap = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap /\ prh_lin Lam kids (56 * cap) /\ prh_lin Lam keys (8 * cap).
Hypothesis ED : D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di.
Hypothesis HM : pj_memsR SEGS (mrestrict (w_H W) mem) (prh_lin Lam)
  (pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam)) kids keys members Di.
Hypothesis H11 : getr regs 11 = w64 k.
Hypothesis Hon : o <> 0.
Hypothesis Ho4096 : 4096 <= o.
Hypothesis Ho47 : o + 56 <= 2 ^ 47.

(* the loop's state at the loop head, before member i *)
Definition pgl_inv (i : nat) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (k0 : Z) : Prop :=
  Z.of_nat i < n /\
  AJ (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memL mdL k0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a) /\
  Forall (fun sr => val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 96 + fst sr) 8 (bv_unsigned (getr regs (snd sr))))
    pg_saves /\
  getr regsL 2 = Z_to_bv 64 (spZ regs - 96) /\ getr regsL 3 = getr regs 3 /\ getr regsL 4 = getr regs 4 /\
  getr regsL 8 = w64 o /\ getr regsL 9 = w64 k /\ getr regsL 18 = w64 (keys + 8 * Z.of_nat i) /\
  getr regsL 19 = w64 SHADOW_OFF /\ getr regsL 20 = w64 (- (56 * Z.of_nat i)) /\ getr regsL 21 = w64 (Z.of_nat i) /\
  getr regsL 22 = w64 n /\ getr regsL 23 = w64 keys /\ getr regsL 24 = w64 1 /\
  getr regsL 25 = w64 (keys + 8 * Z.of_nat i) /\ getr regsL 26 = getr regs 26 /\ getr regsL 27 = getr regs 27 /\
  (forall j nm u, (j < i)%nat -> nth_error members j = Some (nm, u) -> nm <> kname).

(* the generic-P form (h-hpreset-7 12:18Z / 12:22Z): any invariant R with srr_inv_laws, and srr_inv_call because the
   loop crosses the strcmp call *)
Lemma pgl_loopP : forall (R : (word -> option byte) -> Prop), srr_inv_laws SEGS R ->
  srr_inv_call SEGS R ->
  forall (j i : nat) regsL memL mdL k0, (length members - i = j)%nat ->
  pgl_inv i regsL memL mdL k0 -> R memL ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_pgB + 180))) memL (seg_rom SEGS)) mdL)
    (fun W' c' => fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
      (pg_postB ly S Hp o (JObj members) D Lam kname peak cnt fail ran most own) W' c' /\ R (ms_mem (cfg_ms c'))).
Proof.
intros R RLAW RCALL.
induction j as [j IH] using lt_wf_ind. intros i regsL memL mdL k0 Hj INV HPM.
destruct INV as (Hi & HJ & KF & HFR & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27
  & Hpre).
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pg_frameB as FS. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlo : YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_B)) by lia.
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KF; lia).
(* the object's two blocks *)
destruct Hcap as [(Hc0 & _) | (Hcp & Hlk & Hly)]; [lia|]. unfold prh_lin in Hlk, Hly.
destruct (pjs_lam_blk B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own keys (8 * cap) HAR HLED Hly)
  as (Hy16 & Hy4096 & _ & Hyc & _ & _ & _ & Hybs & _ & _ & _).
destruct (pjs_lam_blk B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own kids (56 * cap) HAR HLED Hlk)
  as (Hk16 & Hk4096 & _ & Hkc & _ & _ & _ & _ & _ & _ & _).
(* the member i: its key word xi in keys, its name, its node *)
destruct (nth_error members i) as [[nm u]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
destruct (pjs_mems_nth _ _ _ _ _ _ _ _ _ _ HM Ei) as (xi & kb & D1 & (Hxi0 & Hxi) & Hcs & Hnd & Hinc & HinD).
pose proof Hh as (_ & _ & _ & _ & (Hkd0 & Hkd) & _).
assert (Hxi1 : val_mem SEGS (mrestrict (w_H W) memL) (keys + 8 * Z.of_nat i) 8 xi).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem memL _ 8 xi); [|exact Hxi]. intros q Hq. apply KL. lia. }
assert (Hkd1 : val_mem SEGS (mrestrict (w_H W) memL) (o + 24) 8 kids).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem memL _ 8 kids); [|exact Hkd]. intros q Hq.
  pose proof (HFT (o + q + 24) ltac:(unfold pj_footR; left; lia)) as (Hr & _ & Hw).
  replace (o + 24 + q) with (o + q + 24) by lia. apply KF; assumption. }
(* the node apart from the keys block (the tree's blocks avoid its header) *)
assert (Hap : pj_apartR D o) by exact (proj1 (proj2 Hnode)).
assert (HinY : In (keys, 8 * cap) D) by (rewrite ED; destruct (Z.eqb_spec cap 0); [lia | right; left; reflexivity]).
assert (Dny : o + 56 <= keys + 8 * Z.of_nat i \/ keys + 8 * Z.of_nat i + 8 <= o).
{ destruct (Z_le_gt_dec (o + 56) (keys + 8 * Z.of_nat i)); [left; lia|].
  destruct (Z_le_gt_dec (keys + 8 * Z.of_nat i + 8) o); [right; lia|]. exfalso.
  destruct (Z_le_gt_dec o (keys + 8 * Z.of_nat i)).
  - apply (Hap _ (keys + 8 * Z.of_nat i) HinY); [unfold pj_holdsR; cbn [fst snd]; lia | lia].
  - apply (Hap _ o HinY); [unfold pj_holdsR; cbn [fst snd]; lia | lia]. }
assert (Dfr : o + 56 <= spZ regs - 96 \/ spZ regs <= o).
{ destruct (Z_le_gt_dec (o + 56) (spZ regs - 96)); [left; lia|]. destruct (Z_le_gt_dec (spZ regs) o); [right; lia|].
  exfalso. destruct (Z_le_gt_dec o (spZ regs - 96)).
  - destruct (HFT (spZ regs - 96) ltac:(unfold pj_footR; left; lia)) as (_ & _ & Hw). apply Hw. lia.
  - destruct (HFT o ltac:(unfold pj_footR; left; lia)) as (_ & _ & Hw). apply Hw. lia. }
pose proof Hh as ((Hal8 & _) & _).
(* ---- the seat at the loop head ---- *)
set (E := pgl_E regsL regs xi kids).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pgl_E; apply Eimg_env).
assert (EL : forall q, (q < A_TEXT)%nat ->
  ew E q = ew (Ereg regsL (Z_to_bv 64 xi :: Z_to_bv 64 kids :: map (fun sr => getr regs (snd sr)) pg_saves)) q)
  by (intros q Hq; subst E; unfold pgl_E; apply Eimg_low; exact Hq).
assert (EX : forall j0, (32 + j0 < A_TEXT)%nat ->
  ew E (32 + j0) = nth j0 (Z_to_bv 64 xi :: Z_to_bv 64 kids :: map (fun sr => getr regs (snd sr)) pg_saves) (Z_to_bv 64 0))
  by (intros j0 Hj0; rewrite EL by exact Hj0; apply ew_Ereg_extra).
assert (ER : forall q (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew E q = getr regsL r)
  by (intros q r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsL _ q r Hr)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 96)
  by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); rewrite R2; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = o)
  by (rewrite (ER 8%nat 8%bv) by (lia || reflexivity); rewrite R8; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = keys + 8 * Z.of_nat i)
  by (rewrite (ER 25%nat 25%bv) by (lia || reflexivity); rewrite R25; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = keys + 8 * Z.of_nat i)
  by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); rewrite R18; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = keys)
  by (rewrite (ER 23%nat 23%bv) by (lia || reflexivity); rewrite R23; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF)
  by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); rewrite R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E 24) = 1)
  by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); rewrite R24; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = Z.of_nat i)
  by (rewrite (ER 21%nat 21%bv) by (lia || reflexivity); rewrite R21; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = n)
  by (rewrite (ER 22%nat 22%bv) by (lia || reflexivity); rewrite R22; unfold w64; apply unsigned_lit_small; lia).
rewrite Forall_forall in HFR.
assert (HS : st_ok_pi SEGS VAL E ss_pgl
  (restrict (w_H W) (mkst regsL (Z_to_bv 64 (BASE + (AF_pgB + 180))) memL (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pgl. apply pa_entry_st_ok_full.
  - subst E; unfold pgl_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pgl_stk, pgl_node, pgl_key.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2, ?U8, ?U25.
    all: try ((split; [lia|]); (split; [lia|]); (split; [intros q Hq; lia|])).
    all: repeat apply Forall_cons; try apply Forall_nil.
    all: eapply (chunk_ok_val SEGS _ _ _ _ 8 _ _);
      [ cbn [sv_denot]; lazymatch goal with |- context [ew _ ?q] =>
          let j0 := eval vm_compute in (q - 32)%nat in change q with (32 + j0)%nat end;
        rewrite EX by (unfold A_TEXT; lia); cbn [nth map pg_saves snd]; rewrite Z.add_0_r;
        rewrite ?unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
        first [ exact Hxi0 | exact Hkd0
              | lazymatch goal with |- 0 <= bv_unsigned ?b < _ => exact (bv_unsigned_in_range 64 b) end ]
      | cbn; lia
      | change (N.to_nat 8) with 8%nat;
        first [ rewrite Z.add_0_r; exact Hxi1 | exact Hkd1
              | lazymatch goal with |- val_mem _ _ (_ + ?off) _ (bv_unsigned (getr regs ?r)) =>
                  apply (HFR (off, r)); cbn [pg_saves In]; tauto end ] ].
  - apply pairwise_disjoint_of_extents. unfold pgl_stk, pgl_node, pgl_key, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U8, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [pgl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U8, U25, U18, U23, U19, U24, U21. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PGL_Bx [] E (mrestrict (w_H W) memL)) by constructor.
(* the walk keeps R (laws RLAW); HPM, from the loop state, holds it here *)
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_B) (PI := PA)).
(* ---- slots 45 .. : the UBSan checks on keys + 8 i, the key word, the strcmp call ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr0|].
gs_memeq HF EM1. clear HF HG HFr.
(* slot 48: bnez (i >> 60), the index overflow trap: refuted, i < 2 ^ 44 *)
psrr_branch_tok RUN BR HS SHOK PG_BspanB.
{ exfalso. rewrite branch_ne_U in Hc. repeat first [rewrite U_SAlu in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
  cbn [zalu_raw] in Hc. rewrite U21, Z.add_0_r in Hc.
  rewrite (zcanon_id (Z.of_nat i)), (zcanon_id 60), (zcanon_id 0) in Hc by (unfold M64; lia).
  change (Z.land 60 63) with 60 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). cbn in Hc. discriminate Hc. }
clear Hc. paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr0|].
gs_memeq HF EM2. clear HF HG HFr.
(* slot 49: bltu s2, s7 (keys + 8 i below keys), the pointer-overflow trap: refuted *)
psrr_branch_tok RUN BR HS SHOK PG_BspanB.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. rewrite !U_SOff in Hc. rewrite U18, U23, !Z.add_0_r in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). lia. }
clear Hc.
(* the shadow of keys[i]: inside the keys block's user range, at the current memory *)
assert (HRAY : range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF (keys + 8 * Z.of_nat i) 8).
{ eapply range_addressable_agree; [|exact (block_shadow_range _ _ keys (8 * cap) (keys + 8 * Z.of_nat i) 8 Hybs
    ltac:(lia) ltac:(lia))].
  intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KL. lia. }
(* slots 50 .. 58: beqz s7 and the alignment trap decided by the seat's facts; the shadow check of keys[i]; a0 = keys[i],
   a1 = k; the strcmp call *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB.
{ cbn [ms_mem]. rewrite EM2, EM1. unfold PGL_Bx. rewrite !U_SOff, U19, U18, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  change (rd_of SEGS (mrestrict (w_H W) memL)) with (aview SEGS (w_H W) memL). exact HRAY. }
{ gs_awr0. }
gs_memeq HF EM3. clear HF HG HFr.
(* ---- the strcmp call (slot 59): a0 = keys[i] (member i's key), a1 = k ---- *)
pmkst HS.
prreg HS (10%bv : bv 5) Ga0. prreg HS (11%bv : bv 5) Ga1. prreg HS (2%bv : bv 5) Gsp. prreg HS (1%bv : bv 5) Gra.
prreg HS (3%bv : bv 5) Ggp. prreg HS (4%bv : bv 5) Gtp.
assert (HspT : spZ (ms_regs ms1) = spZ regs + -96) by (unfold spZ at 1; rewrite Gsp, U2; lia).
rewrite EM3, EM2, EM1 in HJ, HPM |- *.
(* the two strings' premises at the call: member i's key in its harness block, the key k by cstr_ok *)
pose proof HJ as (HARc & _).
assert (HLED1 : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W memL Lam peak cnt fail ran most own)
  by exact (pg_ledger_keptB ly S Hp W mem md memL Lam peak cnt fail ran most own HAR HLED KL).
assert (Hcs1 : pj_cstrR SEGS (mrestrict (w_H W) memL) (prh_lin Lam) xi kb nm).
{ destruct Hcs as (Hl & Hlen & H32 & Hnz & Hg). split; [exact Hl|]. split; [exact Hlen|]. split; [exact H32|].
  split; [exact Hnz|].
  apply (gs_garr8_move W W mem memL xi xi (nm ++ [0]) Hg). intros j0 Hj0. apply KL.
  unfold prh_lin in Hl. destruct (pg_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own xi kb HAR HLED Hl) as (_ & _ & Hc & _).
  rewrite length_app in Hj0. cbn [length] in Hj0. lia. }
assert (HK1 : cstr_ok (PA := PA) W memL k kname) by exact (gs_cstr_kept W W mem memL k kname HK KL).
assert (Hsp' : YM05.alloc_ceiling + 2 * ESTACK <= spZ (ms_regs ms1)) by lia.
destruct (pjs_key_strcmp_pre B ARx LAWS ly S Hp W memL _ (ms_regs ms1) Lam peak cnt fail ran most own xi kb nm HARc HLED1 Hcs1
  Hsp') as (Px0 & Pkx0 & Pkx32 & Pxk & Pfx & Psx & Pbx & Pmx & Prx & Phx & Ptx).
destruct (pjs_k_strcmp_pre W (ms_regs ms1) memL k kname HK1 Hsp')
  as (Py0 & Pky0 & Pky32 & Pyk & Pfy & Psy & Pby & Pmy & Pry & Phy & Pty).
eapply SRr_bind.
{ eapply (aj_strcmp_at_xrom (SK := SK) SEGS B PST ARx (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) LAWS Hsegs
    (SIGMA AS___wrap_strcmp) ASC W (ms_regs ms1) memL
    (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp _ k0 xi k
    (Z.of_nat (length nm)) (Z.of_nat (length kname)) (-96) _ HJ).
  - rewrite Ga0. change 32%nat with (32 + 0)%nat. rewrite EX by (unfold A_TEXT; lia). reflexivity.
  - rewrite Ga1, (ER 9%nat 9%bv) by (lia || reflexivity). exact R9.
  - exact Px0.
  - exact Py0.
  - exact Pkx0.
  - exact Pkx32.
  - exact Pxk.
  - exact Pky0.
  - exact Pky32.
  - exact Pyk.
  - exact HspT.
  - reflexivity.
  - lia.
  - rewrite FS. lia.
  - rewrite Ggp, (ER 3%nat 3%bv) by (lia || reflexivity). rewrite R3. exact Hgp.
  - rewrite Gtp, (ER 4%nat 4%bv) by (lia || reflexivity). rewrite R4. exact Htp.
  - exact Gra.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - exact Pfx.
  - exact Pfy.
  - exact Psx.
  - exact Psy.
  - intros a Ha. rewrite <- HspT. exact (Pbx a Ha).
  - intros a Ha. rewrite <- HspT. exact (Pby a Ha).
  - exact Pmx.
  - exact Pmy.
  - exact Prx.
  - exact Phx.
  - exact Pry.
  - exact Phy.
  - exact Ptx.
  - exact Pty.
  - exact (gs_rod_kept B W W mem memL HROD KL). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & HKP).
(* the keep across the call: the walk's keep up to the call, then the row's *)
assert (HPM2 : R mem2) by exact (RCALL _ _ HKP HPM). clear HPM HKP. rename HPM2 into HPM.
(* ---- after the call: the seat kept (the call writes only its own window below the frame), a0 = v ---- *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ cbn [ms_mem restrict]. rewrite EM3, EM2, EM1.
  repeat constructor; intros a Ha;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?ew_ewset_other in Ha by lia; rewrite ?U2, ?U8, ?U25 in Ha;
    first [ lia
          | apply (mbyte_of_aview SEGS); apply Hfr2; [lia|]; intros Hw;
            first [ lia | destruct (HFT a ltac:(unfold pj_footR; left; lia)) as (_ & _ & Hw'); apply Hw'; lia ] ]. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc (ewset E 512 w) 48 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HSX.
assert (HIM1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD1 : forall q, (q < 48)%nat -> q <> 512%nat -> ew E1 q = ew E q)
  by (intros q Hq Hq'; rewrite HE1, ew_havoc_old by exact Hq; apply ew_ewset_other; lia).
assert (E1a0 : ew E1 52 = v) by (rewrite HE1, <- Hv; reflexivity).
assert (SHOK1 : sh_ok SEGS PGL_Bx [] E1 (mrestrict (w_H W) mem2)) by constructor.
clear HS SHOK. rename HSX into HS. rename SHOK1 into SHOK.
(* slot 60: beqz a0 *)
psrr_branch_tok RUN BR HS SHOK PG_BspanB.
- (* a0 = 0: the names are equal, member i is the found one *)
  rewrite branch_eq_U, U_SLit, U_SOff, E1a0, Z.add_0_r in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64) by exact (bv_unsigned_in_range 64 v).
  apply Z.eqb_eq in Hc. rewrite zcanon_id in Hc by (unfold M64; lia).
  assert (Ev : v = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  pose proof Hcs1 as (_ & _ & _ & _ & Hgx). pose proof HK1 as ((Hgk & _) & _).
  assert (Enm : nm = kname) by (apply (pjs_strcmp_iff W memL xi nm k kname Hgx Hgk); apply Hcmp; exact Ev).
  subst nm.
  (* the shadow of the node's kids word at the memory after the call *)
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hw; rewrite Hfr2 by lia; apply KF; assumption).
  assert (HRAO : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF (o + 24) 8).
  { eapply range_addressable_agree; [|exact (range_addressable_sub _ _ o 56 (o + 24) 8 HRA ltac:(lia) ltac:(lia))].
    intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KM2; lia. }
  (* slots 80 .. : the kids word, kids + 56 i, the pointer-overflow traps *)
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB.
  { cbn [ms_mem mkst]. unfold PGL_Bx. rewrite !U_SOff. rewrite !OLD1 by lia. rewrite U19, U8, Z.add_0_r.
    rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
    change (rd_of SEGS (mrestrict (w_H W) mem2)) with (aview SEGS (w_H W) mem2). exact HRAO. }
  { gs_awr0. }
  gs_memeq HF EM4. clear HF HG HFr.
  assert (U33 : bv_unsigned (ew E 33) = kids)
    by (change 33%nat with (32 + 1)%nat; rewrite EX by (unfold A_TEXT; lia); cbn [nth]; apply unsigned_lit_small; lia).
  (* slot 92: beq (kids <> 0) (kids + 56 i = 0), the null-pointer trap: refuted, kids >= 4096 *)
  clear Hc. psrr_branch_tok RUN BR HS SHOK PG_BspanB.
  { exfalso. rewrite branch_eq_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?OLD1 in Hc by lia.
    rewrite ?U33, ?U21, ?Z.add_0_r in Hc. pgl_zc Hc. pgl_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
  clear Hc. paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB; [gs_awr0|].
  gs_memeq HF EM5. clear HF HG HFr.
  (* slot 93: bltu (kids + 56 i) kids, the pointer-overflow trap: refuted *)
  psrr_branch_tok RUN BR HS SHOK PG_BspanB.
  { exfalso. rewrite branch_ltu_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?OLD1 in Hc by lia.
    rewrite ?U33, ?U21, ?Z.add_0_r in Hc. pgl_zc Hc. pgl_ltb Hc; cbn in Hc; try discriminate Hc; lia. }
  clear Hc. paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB; [gs_awr0|].
  gs_memeq HF EM6. clear HF HG HFr.
  (* slot 99: bnez (mulh i 56 <> sra (56 i) 63), the multiply-overflow trap: refuted *)
  psrr_branch_tok RUN BR HS SHOK PG_BspanB.
  { exfalso. rewrite branch_ne_U in Hc.
    repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw zmd_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?OLD1 in Hc by lia.
    rewrite ?U33, ?U21, ?Z.add_0_r in Hc. pgl_zc Hc.
    rewrite (swrap64_id (Z.of_nat i)), (swrap64_id 56), (swrap64_id (Z.of_nat i * 56)) in Hc by (unfold half64; lia).
    change (Z.of_N 64) with 64 in Hc. change (Z.land 63 63) with 63 in Hc.
    rewrite !Z.shiftr_div_pow2 in Hc by lia.
    rewrite (Z.div_small (Z.of_nat i * 56) (2 ^ 63)), (Z.div_small (Z.of_nat i * 56) (2 ^ 64)) in Hc by lia.
    cbn in Hc. discriminate Hc. }
  (* slots 100, 101 and 67 .. 79: a0 = kids - s4 = kids + 56 i, the eleven registers back, ret *)
  clear Hc. paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB; [gs_awr0|].
  gs_memeq HF EM7. clear HF HG HFr.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  assert (EMF : ms_mem ms5 = mem2) by (rewrite EM7, EM6, EM5, EM4; reflexivity).
  (* the registers at the return: a0 = kids + 56 i; the eleven saved registers from the frame; sp, gp, tp, s10, s11 kept *)
  pose proof (st_ok_pi_restrict_reg (PI := PA) _ _ _ _ (10%bv : bv 5) HS) as G10.
  lazymatch type of G10 with _ = sv_denot _ (sr_get ?l _) =>
    let e := eval vm_compute in (sr_get l (10%bv : bv 5)) in change (sr_get l (10%bv : bv 5)) with e in G10 end.
  rewrite denot_lit_U in G10.
  repeat first [rewrite U_SAlu in G10 | rewrite U_SMd in G10 | rewrite U_SOff in G10 | rewrite U_SLit in G10].
  cbn [zalu_raw zmd_raw] in G10. rewrite ?ew_ewset_other in G10 by lia. rewrite ?OLD1 in G10 by lia.
  rewrite ?U33, ?Z.add_0_r in G10.
  rewrite (ER 20%nat 20%bv), R20 in G10 by (lia || reflexivity). unfold w64 in G10. rewrite Z_to_bv_unsigned in G10.
  rewrite pgl_zc_wrap, pgl_zc_mul, pgl_zc_add, pgl_w64_zc in G10.
  replace (- (56 * Z.of_nat i) * -1 + kids) with (kids + 56 * Z.of_nat i) in G10 by lia.
  assert (KR : forall r : bv 5, getr regsL r = getr regs r -> getr regsL r = getr regs r) by (intros r Hr; exact Hr).
  assert (GB : forall r : bv 5, In r (1%bv :: pg_allB) -> getr (ms_regs ms5) r = getr regs r).
  { intros r Hr. cbn [pg_allB map In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [pgl_back HS OLD1 EX ER U2 KR; first [exact R3 | exact R4 | exact R26 | exact R27] |]).
    destruct Hr. }
  (* the node and the found member at the exit memory *)
  assert (KMF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms5) a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite EMF; apply KM2; assumption).
  assert (NF : pj_nodeR SEGS (mrestrict (w_H W) (ms_mem ms5)) (prh_lin Lam) o (JObj members) D).
  { apply (gs_node_kept W mem (ms_mem ms5) _ o (JObj members) D Hnode). intros x Hx.
    destruct (HFT x Hx) as (Hr & Hni & Hw). split; [exact Hr|]. split; [exact Hni|]. exact (KMF x Hr Hw). }
  pose proof NF as NF'. cbn [pj_nodeR] in NF'.
  destruct NF' as (_ & _ & num' & str' & kids' & keys' & n' & cap' & Hh' & Es' & En' & Hcn' & Hcap' & Di' & ED' & HM').
  cbn [tag] in Hh'. subst str'.
  pose proof Hh' as (_ & _ & _ & _ & (Hk0' & Hk') & _).
  assert (HkdF : val_mem SEGS (mrestrict (w_H W) (ms_mem ms5)) (o + 24) 8 kids).
  { apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem ms5) _ 8 kids); [|exact Hkd]. intros q Hq.
    pose proof (HFT (o + q + 24) ltac:(unfold pj_footR; left; lia)) as (Hr & _ & Hw).
    replace (o + 24 + q) with (o + q + 24) by lia. apply KMF; assumption. }
  pose proof (gs_val8_uniq _ _ _ _ Hk' HkdF Hk0' Hkd0) as Ekd. subst kids'.
  split; [|exact HPM].
  eapply (pg_finB ly S Hp W regs mem md o (JObj members) D kname Lam peak cnt fail ran most own _ _ _ _ _
    (kids + 56 * Z.of_nat i) HAR HLED HJ2).
  + intros a Ha. apply KMF; lia.
  + exact Hra.
  + intros r Hr. apply GB. right. exact Hr.
  + apply GB. left. reflexivity.
  + exact G10.
  + right. split; [exact Hon|]. split; [exact NF|].
    exact (pjs_res_found (PA := PA) (mrestrict (w_H W) (ms_mem ms5)) (prh_lin Lam) o members D kname num' kids keys' n' cap'
      Di' i u Hh' ED' HM' Ei Hpre).
- (* a0 <> 0: the names differ *)
  rewrite branch_eq_U, U_SLit, U_SOff, E1a0, Z.add_0_r in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64) by exact (bv_unsigned_in_range 64 v).
  apply Z.eqb_neq in Hc. rewrite zcanon_id in Hc by (unfold M64; lia).
  pose proof Hcs1 as (_ & _ & _ & _ & Hgx). pose proof HK1 as ((Hgk & _) & _).
  assert (Hne : nm <> kname).
  { intros Enm. apply Hc.
    assert (Ev : v = w64 0) by (apply Hcmp; apply (pjs_strcmp_iff W memL xi nm k kname Hgx Hgk); exact Enm).
    rewrite Ev. reflexivity. }
  clear Hc.
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
    by (intros a Ha Hw; rewrite Hfr2 by lia; apply KF; assumption).
  pose proof (pjs_pre_step members kname i nm u Hpre Ei Hne) as Hpre'.
  (* slots 61 .. 65: s5 = i + 1, s4 = s4 - 56, s2 += 8, s9 += 8, bne n (i + 1) *)
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB; [gs_awr0|].
  gs_memeq HF EM4. clear HF HG HFr.
  psrr_branch_tok RUN BR HS SHOK PG_BspanB.
  + (* taken: n <> i + 1, back to the loop head with member i + 1 *)
    rewrite branch_ne_U in Hc. repeat first [rewrite U_SAlu in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?OLD1 in Hc by lia.
    rewrite U21, U22, ?Z.add_0_r in Hc. pgl_zc Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM PG_BspanB (AF_pgB + 180); [gs_awr0|].
    gs_memeq HF EM5. clear HF HG HFr.
    pmkst HS.
    assert (Hoff : forall sr, In sr pg_saves -> 8 <= fst sr <= 88)
      by (intros sr Hsr; cbn [pg_saves In] in Hsr; repeat (destruct Hsr as [<- | Hsr]; [cbn [fst]; lia |]); destruct Hsr).
    (* the loop head's listing offset, computed from the listing (no typed offset: it moves with pj_get's slot) *)
    lazymatch eval vm_compute in (AF_pgB + 180) with ?n => change (BASE + n) with (BASE + (AF_pgB + 180)) end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rB _ ?mB _) ?dB) _ =>
      eapply (IH (length members - Datatypes.S i)%nat ltac:(lia) (Datatypes.S i) rB mB dB _ eq_refl) end.
    unfold pgl_inv. rewrite EM5, EM4.
    repeat rewrite wvb_collapse in HJ2. rewrite EM5, EM4 in HJ2.
    split; [lia|]. split; [exact HJ2|]. split; [intros a Ha Hw; apply KM2; assumption|].
    split.
    { apply Forall_forall. intros sr Hsr. pose proof (Hoff sr Hsr) as Ho.
      apply (val_mem_kept SEGS (w_H W) (w_H W) memL mem2 _ 8 _); [|exact (HFR sr Hsr)].
      intros q Hq. apply Hfr2; lia. }
    pgl_iregs HS OLD1 ER.
    all: try (rewrite pgl_w64_zc; rewrite ?R3, ?R4, ?R26, ?R27, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    all: try (rewrite pgl_w64_zc; rewrite ?R2, ?R8, ?R9, ?R18, ?R19, ?R20, ?R21, ?R22, ?R23, ?R24, ?R25; unfold w64;
              rewrite Z_to_bv_unsigned, pgl_w64_wrap_add; f_equal; lia).
    exact Hpre'.
    first [exact HPM | rewrite ?EM5, ?EM4 in HPM |- *; exact HPM].
  + (* not taken: n = i + 1, no member matched: a0 = 0, the eleven registers back, ret *)
    rewrite branch_ne_U in Hc. repeat first [rewrite U_SAlu in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
    cbn [zalu_raw] in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite ?OLD1 in Hc by lia.
    rewrite U21, U22, ?Z.add_0_r in Hc. pgl_zc Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_tok_x_inv RUN HS HJ2 SHOK HPM PG_BspanB; [gs_awr0|].
    gs_memeq HF EM5. clear HF HG HFr.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (MSF := msF) in * end.
    assert (EMF : ms_mem MSF = mem2) by (subst MSF; rewrite EM5, EM4; reflexivity).
    pose proof (st_ok_pi_restrict_reg (PI := PA) _ _ _ _ (10%bv : bv 5) HS) as G10.
    lazymatch type of G10 with _ = sv_denot _ (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l (10%bv : bv 5)) in change (sr_get l (10%bv : bv 5)) with e in G10 end.
    cbn [sv_denot] in G10.
    assert (KR : forall r : bv 5, getr regsL r = getr regs r -> getr regsL r = getr regs r) by (intros r Hr; exact Hr).
    assert (GB : forall r : bv 5, In r (1%bv :: pg_allB) -> getr (ms_regs MSF) r = getr regs r).
    { intros r Hr. cbn [pg_allB map In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [pgl_back HS OLD1 EX ER U2 KR; first [exact R3 | exact R4 | exact R26 | exact R27] |]).
      destruct Hr. }
    assert (KMF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
      aview SEGS (w_H W) (ms_mem MSF) a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite EMF; apply KM2; assumption).
    assert (NF : pj_nodeR SEGS (mrestrict (w_H W) (ms_mem MSF)) (prh_lin Lam) o (JObj members) D).
    { apply (gs_node_kept W mem (ms_mem MSF) _ o (JObj members) D Hnode). intros x Hx.
      destruct (HFT x Hx) as (Hr & Hni & Hw). split; [exact Hr|]. split; [exact Hni|]. exact (KMF x Hr Hw). }
    split; [|exact HPM].
    eapply (pg_finB ly S Hp W regs mem md o (JObj members) D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ2).
    * intros a Ha. apply KMF; lia.
    * exact Hra.
    * intros r Hr. apply GB. right. exact Hr.
    * apply GB. left. reflexivity.
    * rewrite G10. reflexivity.
    * right. split; [exact Hon|]. split; [exact NF|]. apply (pjs_res_none (PA := PA)).
      intros j0 nm' u' Hj0 Ej0. apply (Hpre' j0 nm' u'); [lia | exact Ej0].
Qed.

(* the loop entered at member 0, its state given by the run from the entry *)
Lemma pgl_startP : forall (R : (word -> option byte) -> Prop), srr_inv_laws SEGS R ->
  srr_inv_call SEGS R ->
  forall regsL memL mdL k0,
  AJ (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memL mdL k0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a) ->
  Forall (fun sr => val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 96 + fst sr) 8 (bv_unsigned (getr regs (snd sr))))
    pg_saves ->
  R memL ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 96) -> getr regsL 3 = getr regs 3 -> getr regsL 4 = getr regs 4 ->
  getr regsL 8 = w64 o -> getr regsL 9 = w64 k -> getr regsL 18 = w64 keys ->
  getr regsL 19 = w64 SHADOW_OFF -> getr regsL 20 = w64 0 -> getr regsL 21 = w64 0 ->
  getr regsL 22 = w64 n -> getr regsL 23 = w64 keys -> getr regsL 24 = w64 1 ->
  getr regsL 25 = w64 keys -> getr regsL 26 = getr regs 26 -> getr regsL 27 = getr regs 27 ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_pgB + 180))) memL (seg_rom SEGS)) mdL)
    (fun W' c' => fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
      (pg_postB ly S Hp o (JObj members) D Lam kname peak cnt fail ran most own) W' c' /\ R (ms_mem (cfg_ms c'))).
Proof.
intros R RLAW RCALL regsL memL mdL k0 HJ KF HFR HPM R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
apply (pgl_loopP R RLAW RCALL (length members - 0)%nat 0%nat regsL memL mdL k0 eq_refl); [|exact HPM].
unfold pgl_inv. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.add_0_r, Z.opp_0.
split; [lia|]. split; [exact HJ|]. split; [exact KF|]. split; [exact HFR|].
repeat (split; [assumption|]). intros j nm u Hj. lia.
Qed.

(* the two statements before the keep (a43c94406a1), byte-identical, as corollaries at R := fun _ => True (h-hpreset-7
   12:18Z condition (1): these statements changed for the invariant's sake) *)
Lemma pgl_loop : forall (j i : nat) regsL memL mdL k0, (length members - i = j)%nat ->
  pgl_inv i regsL memL mdL k0 ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_pgB + 180))) memL (seg_rom SEGS)) mdL)
    (fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
      (pg_postB ly S Hp o (JObj members) D Lam kname peak cnt fail ran most own)).
Proof.
intros j i regsL memL mdL k0 Hj INV. eapply SRr_mono.
{ exact (pgl_loopP (fun _ => True) pgl_true_laws (fun _ _ _ _ => I) j i regsL memL mdL k0 Hj INV I). }
cbv beta. intros W' c' _ (H & _). exact H.
Qed.
Lemma pgl_start : forall regsL memL mdL k0,
  AJ (STK_pj_get (PI := prh_img_B)) (spZ regs) [] ly S Hp W mem md [] ly S Hp W memL mdL k0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
     aview SEGS (w_H W) memL a = aview SEGS (w_H W) mem a) ->
  Forall (fun sr => val_mem SEGS (mrestrict (w_H W) memL) (spZ regs - 96 + fst sr) 8 (bv_unsigned (getr regs (snd sr))))
    pg_saves ->
  getr regsL 2 = Z_to_bv 64 (spZ regs - 96) -> getr regsL 3 = getr regs 3 -> getr regsL 4 = getr regs 4 ->
  getr regsL 8 = w64 o -> getr regsL 9 = w64 k -> getr regsL 18 = w64 keys ->
  getr regsL 19 = w64 SHADOW_OFF -> getr regsL 20 = w64 0 -> getr regsL 21 = w64 0 ->
  getr regsL 22 = w64 n -> getr regsL 23 = w64 keys -> getr regsL 24 = w64 1 ->
  getr regsL 25 = w64 keys -> getr regsL 26 = getr regs 26 -> getr regsL 27 = getr regs 27 ->
  SRr SEGS W (mkCfg (mkst regsL (Z_to_bv 64 (BASE + (AF_pgB + 180))) memL (seg_rom SEGS)) mdL)
    (fpost (PI := prh_img_B) (PA := PA) B ARx SK (STK_pj_get (PI := prh_img_B)) [] regs ly S Hp W mem md
      (pg_postB ly S Hp o (JObj members) D Lam kname peak cnt fail ran most own)).
Proof.
intros regsL memL mdL k0 HJ KF HFR R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27. eapply SRr_mono.
{ exact (pgl_startP (fun _ => True) pgl_true_laws (fun _ _ _ _ => I) regsL memL mdL k0 HJ KF HFR I
    R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27). }
cbv beta. intros W' c' _ (H & _). exact H.
Qed.
End loop.

Theorem pj_get_holds_B : tpj_get_specXP (cp := CP) (PI := prh_img_B) (PA := PA) B ARx SK P.
Proof.
unfold tpj_get_specXP.
intros ly S Hp W regs mem md ch o k kname t D Lam peak cnt fail ran most own [HPRE [HROD [HTOP [HRAZ HFRM]]]] H10 H11 HO HK HLED.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pg_frameB as FS. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hlo : YM05.alloc_ceiling <= spZ regs - STK_pj_get (PI := prh_img_B)) by lia.
(* the node's header words, when there is a node (atoms 33 .. 36) *)
assert (HHD : exists ty kids keys nn, o <> 0 -> exists num str cap,
  pj_hdrR SEGS (mrestrict (w_H W) mem) o ty num str kids keys nn cap /\ ty = tag t).
{ destruct HO as [Ho0 | (Hnode & _)]; [exists 0, 0, 0, 0; intros H; contradiction|].
  destruct (gs_node_hdr _ _ _ _ _ Hnode) as (num & str & kids & keys & nn & cap & Hh).
  exists (tag t), kids, keys, nn. intros _. exists num, str, cap. split; [exact Hh | reflexivity]. }
destruct HHD as (ty & kids & keys & nn & HHD).
set (xs := [ty; kids; keys; nn]).
destruct (pg_entryB ly S Hp W regs mem md ch xs HPRE) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
remember (pg_EB regs xs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pg_EB; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) n)
  by (intros n Hn; subst E; unfold pg_EB; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E)
  by (rewrite HE; split; [intros n Hn; unfold pg_EB; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
(* the walk keeps m |-> (P mem -> P m) (YSRrMemnorm.srr_inv_laws_imp); at entry it is P mem -> P mem *)
pose proof (srr_inv_laws_imp SEGS P mem PLAW) as RLAW.
assert (HPM : P mem -> P mem) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS _ RLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PA B PST ARx _ LAWS _ RLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_B) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_pgB)) with (Z_to_bv 64 (BASE + AF_pgB)).
(* ---- slots 0-10: the frame, the nine saves, beqz a0 ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr regs Usp|].
gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KO0. clear HF HG HFr.
psrr_branch_tok RUN BR HS SHOK PG_BspanB.
- (* o = 0: the nine registers back, ret with a0 = o = 0 *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_eq in Hc. rewrite U_SOff, E10, H10, Z.add_0_r in Hc. unfold w64 in Hc.
  assert (Ho0 : o = 0).
  { destruct HO as [Ho0 | (_ & Hrs)]; [exact Ho0|]. destruct Hrs as (H4096 & _ & Hamr & _).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
    rewrite unsigned_lit_small, zcanon_id in Hc by (unfold M64; lia). lia. }
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr regs Usp|].
  gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KO1. clear HF HG HFr.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ (1%bv :: 10%bv :: pg_allB) HS HAE ltac:(vm_compute; reflexivity)) as KK.
  eapply (pg_finPB ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ).
  + intros a Ha. rewrite KO1, KO0 by lia. reflexivity.
  + exact Hra.
  + intros r Hr. apply KK. right; right; exact Hr.
  + apply KK. left; reflexivity.
  + transitivity (getr regs 10%bv); [exact (KK 10%bv ltac:(right; left; reflexivity)) | rewrite H10, Ho0; reflexivity].
  + left. split; [exact Ho0 | reflexivity].
  + exact HPM.
- (* o <> 0: the node *)
  rewrite branch_eq_U, U_SLit in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply Z.eqb_neq in Hc. rewrite U_SOff, E10, H10, Z.add_0_r in Hc. unfold w64 in Hc.
  assert (Hon : o <> 0) by (intros ->; apply Hc; reflexivity).
  destruct HO as [Ho0 | (Hnode & Hrs)]; [contradiction|].
  destruct (HHD Hon) as (num & str & cap & Hh & Ety).
  pose proof Hrs as (H4096 & Hplace & Hamr & Hwin & HRA & HHU).
  assert (Ho47 : o + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
  pose proof (pg_footB ly S Hp W mem md regs o t D Lam peak cnt fail ran most own HAR HLED Hlo Hnode Hrs) as HFT.
  assert (KR : forall x, pj_footR o D x -> mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
  { intros x Hx. destruct (HFT x Hx) as (Hr & Hn & Hw). exact (gs_raw_of_aview _ _ mem (ms_mem ms) x Hr Hn (KO0 x Hr Hw)). }
  assert (Hh1 : pj_hdrR SEGS (mrestrict (w_H W) (ms_mem ms)) o ty num str kids keys nn cap).
  { apply (pj_hdrR_frame SEGS _ _ o ty num str kids keys nn cap Hh). apply gs_agree. intros x Hx. apply KR. left. exact Hx. }
  assert (HRA1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF o 56).
  { eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KO0; lia. }
  destruct Hh1 as ((Hal8 & _) & (Hty0 & Hty) & _ & _ & (Hk0 & Hk) & (Hy0 & Hy) & (Hn0 & Hn) & _).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E33 : ew E 33 = Z_to_bv 64 ty)
    by (rewrite EL by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E34 : ew E 34 = Z_to_bv 64 kids)
    by (rewrite EL by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E35 : ew E 35 = Z_to_bv 64 keys)
    by (rewrite EL by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (E36 : ew E 36 = Z_to_bv 64 nn)
    by (rewrite EL by (unfold A_TEXT; lia); change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
  assert (Uo : base_val E (Some 10%nat) = o)
    by (cbn [base_val]; rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
  (* the node is apart from the frame (outside the stack window) and from the GOT word and the cell (image bytes) *)
  assert (Dfr : o + 56 <= spZ regs - 96 \/ spZ regs <= o).
  { destruct (Z_le_gt_dec (o + 56) (spZ regs - 96)); [left; lia|]. destruct (Z_le_gt_dec (spZ regs) o); [right; lia|].
    exfalso. destruct (Z_le_gt_dec o (spZ regs - 96)); [apply (Hwin (spZ regs - 96)) | apply (Hwin o)]; lia. }
  assert (Dimg : forall g, (forall i, 0 <= i < 8 -> in_img SEGS (g + i)) -> o + 56 <= g \/ g + 8 <= o).
  { intros g Hg. destruct (Z_le_gt_dec (o + 56) g); [left; lia|]. destruct (Z_le_gt_dec (g + 8) o); [right; lia|].
    exfalso. destruct (Z_le_gt_dec o g).
    - assert (Hf : pj_footR o D g) by (unfold pj_footR; left; lia).
      destruct (HFT g Hf) as (_ & Hn' & _). apply Hn'. replace g with (g + 0) by lia. apply Hg. lia.
    - assert (Hf : pj_footR o D o) by (unfold pj_footR; left; lia).
      destruct (HFT o Hf) as (_ & Hn' & _). apply Hn'. replace o with (g + (o - g)) by lia. apply Hg. lia. }
  pose proof (Dimg (VAL (A_OBJ 0)) (fun i Hi => proj1 (Hobj i Hi))) as Dgot.
  pose proof (Dimg (VAL (A_OBJ 12)) (fun i Hi => proj2 (Hobj i Hi))) as Dcell.
  assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
    by (subst E; unfold pg_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
    by (subst E; unfold pg_EB; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssq _ =>
    pose proof (st_ok_pi_add_region (PI := PA) E ssq _ pg_nodeB HS ltac:(vm_compute; reflexivity)) as HSN end.
  lazymatch type of HSN with ?P -> ?Q -> _ => assert (HRN : P); [|assert (HDN : Q); [|specialize (HSN HRN HDN)]] end.
  { unfold region_ok, pg_nodeB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
    rewrite Uo. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS E _ o 0 4 (SOff 33 0) ty); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
      rewrite Z.add_0_r. exact Hty.
    - apply (chunk_ok_val SEGS E _ o 24 8 (SOff 34 0) kids); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hk].
    - apply (chunk_ok_val SEGS E _ o 32 8 (SOff 35 0) keys); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hy].
    - apply (chunk_ok_val SEGS E _ o 40 8 (SOff 36 0) nn); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact Hn]. }
  { apply all_disjoint_of_extents. unfold pg_nodeB, extent_of_region. cbn [ss_mem add_cond map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite Uo. cbn [base_val]. rewrite Usp.
    match goal with |- context [ew E ?g0] => lazymatch eval vm_compute in (Nat.eqb g0 (A_OBJ 0)) with true =>
      change (ew E g0) with (ew E (A_OBJ 0)) end end.
    match goal with |- context [ew E ?g1] => lazymatch eval vm_compute in (Nat.eqb g1 (A_OBJ 12)) with true =>
      change (ew E g1) with (ew E (A_OBJ 12)) end end.
    rewrite Eo0, Eo12, !unsigned_lit_small by lia.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
  clear HS HRN HDN. rename HSN into HS.
  (* the node pointer's range and alignment, for the token engine's shadow checks *)
  pose proof (st_ok_pi_add_fact (PI := PA) E _ _ 10%nat (mkAF 4096 (2 ^ 47 - 56) 3) HS) as HSF.
  lazymatch type of HSF with ?P -> _ => assert (HAF : P); [|specialize (HSF HAF); clear HS HAF; rename HSF into HS] end.
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, H10. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 3) with 8. repeat split; lia. }
  (* ---- slots 11-22: s1, s0, the shadow base, the node's type, bne type 6 ---- *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB.
  all: try (gs_awr_any regs Usp).
  all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
    cbn [ms_mem]; unfold PG_BxB; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
    rewrite ?E32, ?E10, ?H10; unfold w64;
    rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
    lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
      change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
    eapply range_addressable_sub; [exact HRA1 | lia | lia]).
  gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KO1. clear HF HG HFr.
  rewrite Ety in E33.
  (* the post at any exit after the node seat: the node kept at the exit memory *)
  assert (NODEK : forall memF, (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
      aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) ->
    pj_nodeR SEGS (mrestrict (w_H W) memF) (prh_lin Lam) o t D).
  { intros memF KF. apply (gs_node_kept W mem memF _ o t D Hnode). intros x Hx.
    destruct (HFT x Hx) as (Hr & Hni & Hw). split; [exact Hr|]. split; [exact Hni|]. exact (KF x Hr Hw). }
  clear Hc. psrr_branch_tok RUN BR HS SHOK PG_BspanB.
  + (* taken: not an object; a0 = 0, the nine registers back, ret *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc t E33. rewrite U_SLit in Hc.
    rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr_any regs Usp|].
    gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KO2. clear HF HG HFr.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
      assert (HAE' : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E')
        by (eapply env_agree_trans; [exact HAE | split; [intros n' Hn'; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
      pose proof (regs_kept_of_st_ok_pi (PI := PA) E' _ _ regs _ (1%bv :: pg_allB) HS HAE' ltac:(vm_compute; reflexivity)) as KK;
      assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
        by (intros a Ha Hw; rewrite KO2, KO1, KO0 by assumption; reflexivity) end.
    prreg HS (10%bv : bv 5) G10.
    eapply (pg_finPB ly S Hp W regs mem md o t D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ).
    * intros a Ha. apply KF; lia.
    * exact Hra.
    * intros r Hr. apply KK. right; exact Hr.
    * apply KK. left; reflexivity.
    * rewrite G10. reflexivity.
    * right. split; [exact Hon|]. split; [exact (NODEK _ KF)|].
      destruct t; cbn [prhPj_get_res]; try reflexivity. exfalso. apply Hc. reflexivity.
    * exact HPM.
  + (* not taken: an object *)
    rewrite branch_ne_U in Hc. gs_tag_in Hc t E33. rewrite U_SLit in Hc.
    rewrite (zcanon_id 6) in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc.
    destruct (gs_tag6 t Hc) as (members & ->).
    (* the header words of the object, as the tree states them *)
    pose proof Hnode as Hnode'. cbn [pj_nodeR] in Hnode'.
    destruct Hnode' as (_ & _ & num0 & str0 & kids0 & keys0 & n0 & cap0 & Hhdr0 & Es0 & En0 & Hcn0 & Hcap0 & Di & ED & Hmems).
    pose proof Hh as (_ & _ & _ & _ & (Hk0e & Hke) & (Hy0e & Hye) & (Hn0e & Hne) & _).
    pose proof Hhdr0 as (_ & _ & _ & _ & (Hk0' & Hk') & (Hy0' & Hy') & (Hn0' & Hn') & _).
    pose proof (gs_val8_uniq _ _ _ _ Hke Hk' Hk0e Hk0') as Ekids. subst kids0.
    pose proof (gs_val8_uniq _ _ _ _ Hye Hy' Hy0e Hy0') as Ekeys. subst keys0.
    pose proof (gs_val8_uniq _ _ _ _ Hne Hn' Hn0e Hn0') as Enn. subst n0.
    (* the views of the current memory outside the window, against the entry's *)
    assert (HRAK : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
        aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) -> range_addressable (aview SEGS (w_H W) m') SHADOW_OFF o 56).
    { intros m' KF. eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KF; lia. }
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msq) =>
      assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
        aview SEGS (w_H W) (ms_mem msq) a = aview SEGS (w_H W) mem a)
        by (intros a Ha Hw; rewrite KO1, KO0 by assumption; reflexivity) end.
    clear KO0 KO1.
    (* ---- slots 23-29: n = node[40], beqz n ---- *)
    paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB.
    all: try (gs_awr_any regs Usp).
    all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
      cbn [ms_mem]; unfold PG_BxB; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
      rewrite ?E32, ?E10, ?H10; unfold w64;
      rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
      lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
        change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
      eapply range_addressable_sub; [apply HRAK; exact KC | lia | lia]).
    gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KN. clear HF HG HFr.
    lazymatch type of KN with forall a, _ -> _ -> aview _ _ ?m' a = _ =>
      assert (KC' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
        aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
    clear KN KC. rename KC' into KC.
    clear Hc. psrr_branch_tok RUN BR HS SHOK PG_BspanB.
    * (* n = 0: no member; a0 = 0, the nine registers back, ret *)
      rewrite branch_eq_U, U_SLit, U_SOff in Hc. rewrite ?ew_ewset_other in Hc by lia.
      rewrite E36, Z.add_0_r, unsigned_lit_small, zcanon_id, (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc.
      assert (Hm0 : members = []) by (destruct members; [reflexivity | cbn [length] in Enn; lia]). subst members.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM PG_BspanB; [gs_awr_any regs Usp|].
      gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KN. clear HF HG HFr.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
      lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
        assert (HAE' : env_agree 32 (Ereg regs (Z_to_bv 64 SHADOW_OFF :: map (Z_to_bv 64) xs)) E')
          by (eapply env_agree_trans; [exact HAE | split; [intros n' Hn''; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
        pose proof (regs_kept_of_st_ok_pi (PI := PA) E' _ _ regs _ (1%bv :: pg_allB) HS HAE' ltac:(vm_compute; reflexivity)) as KK;
        assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a)
          by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
      prreg HS (10%bv : bv 5) G10.
      eapply (pg_finPB ly S Hp W regs mem md o (JObj []) D kname Lam peak cnt fail ran most own _ _ _ _ _ 0 HAR HLED HJ).
      -- intros a Ha. apply KF; lia.
      -- exact Hra.
      -- intros r Hr. apply KK. right; exact Hr.
      -- apply KK. left; reflexivity.
      -- rewrite G10. reflexivity.
      -- right. split; [exact Hon|]. split; [exact (NODEK _ KF)|].
         cbn [prhPj_get_res]. left. split; [intros nm u Hin; destruct Hin | reflexivity].
      -- exact HPM.
    * (* n <> 0: the keys word, s5 = 0, s6 = keys, s7 = its shadow, to the loop head *)
      rewrite branch_eq_U, U_SLit, U_SOff in Hc. rewrite ?ew_ewset_other in Hc by lia.
      rewrite E36, Z.add_0_r, unsigned_lit_small, zcanon_id, (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PG_BspanB (AF_pgB + 180).
      all: try (gs_awr_any regs Usp).
      all: try (lazymatch goal with |- range_addressable _ _ _ _ => idtac end;
        cbn [ms_mem]; unfold PG_BxB; rewrite !U_SOff; rewrite ?ew_ewset_other by lia;
        rewrite ?E32, ?E10, ?H10; unfold w64;
        rewrite ?unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite ?zcanon_id by (unfold M64, SHADOW_OFF; lia);
        lazymatch goal with |- range_addressable (rd_of ?sg (mrestrict ?H ?m)) _ _ _ =>
          change (rd_of sg (mrestrict H m)) with (aview sg H m) end;
        eapply range_addressable_sub; [apply HRAK; exact KC | lia | lia]).
      gs_keep HFr Usp (spZ regs - STK_pj_get (PI := prh_img_B)) (spZ regs) KN. clear HF HG HFr.
      lazymatch type of KN with forall a, _ -> _ -> aview _ _ ?m' a = _ =>
        assert (KC' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_pj_get (PI := prh_img_B) <= a < spZ regs) ->
          aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) by (intros a Ha Hw; rewrite KN, KC by assumption; reflexivity) end.
      clear KN KC. rename KC' into KC.
      (* ---- the loop head (slot 45): the loop lemma at member 0 ---- *)
      cbn [tag] in Hhdr0. subst str0.
      repeat rewrite wvb_collapse in HJ.
      pmkst HS.
      lazymatch eval vm_compute in (AF_pgB + 180) with ?n => change (BASE + n) with (BASE + (AF_pgB + 180)) end.
      (* the frame region of the seat: the eleven saved words *)
      lazymatch type of HS with st_ok_pi _ _ ?E' ?ssq (restrict _ ?msL) =>
        pose proof (st_ok_region_nth SEGS E' (abs_ss VAL ssq) _ 1 _ HS eq_refl) as RG;
        set (EL' := E') in *; set (msLL := msL) in * end.
      cbn [ms_mem restrict] in RG.
      assert (HFR0 : Forall (fun sr => val_mem SEGS (mrestrict (w_H W) (ms_mem msLL)) (spZ regs - 96 + fst sr) 8
        (bv_unsigned (getr regs (snd sr)))) pg_saves).
      { apply Forall_forall. intros sr Hsr. cbn [pg_saves In] in Hsr.
        repeat (destruct Hsr as [<- | Hsr];
          [cbn [fst snd];
           lazymatch goal with |- val_mem _ _ (_ - 96 + ?off) _ (bv_unsigned (getr regs ?r)) =>
             let od := eval vm_compute in (off - 96) in
             let q := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
             replace (spZ regs - 96 + off) with (spZ regs + od) by lia;
             apply (slot_of_region SEGS EL' _ (spZ regs) _ _ _ _ _ od (SOff q 0) (bv_unsigned (getr regs r)) RG);
             [ subst EL'; rewrite ?ew_ewset_other by lia; exact Usp
             | cbn [In]; repeat first [left; reflexivity | right]
             | subst EL'; cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite EL by (unfold A_TEXT; lia);
               rewrite (ew_Ereg_nat regs _ q r) by reflexivity; rewrite Z.add_0_r; reflexivity
             | exact (bv_unsigned_in_range 64 _) ]
           end |]).
        destruct Hsr. }
      assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
      assert (Hkeys : 4096 <= keys /\ keys < 2 ^ 47).
      { destruct Hcap0 as [(Hc0 & _) | (Hcp & _ & Hly)]; [lia|].
        destruct (pg_lam_lowB ly S Hp W mem md Lam peak cnt fail ran most own keys (8 * cap0) HAR HLED Hly) as (Hq4 & _ & Hqc & _). lia. }
      (* the registers at the loop head *)
      assert (G2 : getr (ms_regs msLL) 2 = Z_to_bv 64 (spZ regs - 96)).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite Usp. f_equal. apply zcanon_id. unfold M64. lia. }
      assert (G3 : getr (ms_regs msLL) 3 = getr regs 3).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl).
        rewrite Z.add_0_r, zcanon_id by (unfold M64; exact (bv_unsigned_in_range 64 _)).
        apply Z_to_bv_bv_unsigned. }
      assert (G4 : getr (ms_regs msLL) 4 = getr regs 4).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl).
        rewrite Z.add_0_r, zcanon_id by (unfold M64; exact (bv_unsigned_in_range 64 _)).
        apply Z_to_bv_bv_unsigned. }
      assert (G26 : getr (ms_regs msLL) 26 = getr regs 26).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl).
        rewrite Z.add_0_r, zcanon_id by (unfold M64; exact (bv_unsigned_in_range 64 _)).
        apply Z_to_bv_bv_unsigned. }
      assert (G27 : getr (ms_regs msLL) 27 = getr regs 27).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl).
        rewrite Z.add_0_r, zcanon_id by (unfold M64; exact (bv_unsigned_in_range 64 _)).
        apply Z_to_bv_bv_unsigned. }
      assert (G8 : getr (ms_regs msLL) 8 = w64 o).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E10, H10. unfold w64. rewrite unsigned_lit_small by lia.
        rewrite Z.add_0_r, zcanon_id by (unfold M64; lia). reflexivity. }
      assert (G9 : getr (ms_regs msLL) 9 = w64 k).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E11, H11. unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r, pgl_zc_wrap.
        apply pgl_w64_zc. }
      assert (G18 : getr (ms_regs msLL) 18 = w64 keys).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E35, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
        reflexivity. }
      assert (G23 : getr (ms_regs msLL) 23 = w64 keys).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E35, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
        reflexivity. }
      assert (G25 : getr (ms_regs msLL) 25 = w64 keys).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E35, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
        reflexivity. }
      assert (G22 : getr (ms_regs msLL) 22 = w64 nn).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E36, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
        reflexivity. }
      assert (G19 : getr (ms_regs msLL) 19 = w64 SHADOW_OFF).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
        rewrite Z.add_0_r, zcanon_id by (unfold M64, SHADOW_OFF; lia). reflexivity. }
      assert (G20 : getr (ms_regs msLL) 20 = w64 0) by (pg_head_reg HS; reflexivity).
      assert (G21 : getr (ms_regs msLL) 21 = w64 0) by (pg_head_reg HS; reflexivity).
      assert (G24 : getr (ms_regs msLL) 24 = w64 1).
      { pg_head_reg HS. subst EL'. rewrite ?ew_ewset_other by lia. rewrite E35, unsigned_lit_small by lia. rewrite Z.add_0_r.
        unfold zcanon, M64. rewrite (Z.mod_small keys), (Z.mod_small 0) by lia.
        destruct (Z.ltb_spec 0 keys); [reflexivity | lia]. }
      subst nn.
      (* the loop at the invariant m |-> (P mem -> P m), instantiated once here *)
      assert (RCALLI : srr_inv_call SEGS (fun m => P mem -> P m))
        by (intros m m' Hm h1 h2; exact (PCALL m m' Hm (h1 h2))).
      eapply SRr_mono.
      { eapply (pgl_startP ly S Hp W regs mem md ch o k kname members D Lam peak cnt fail ran most own num0 kids keys
          (Z.of_nat (length members)) cap0 Di); first [exact RLAW | exact RCALLI | eassumption | reflexivity]. }
      cbv beta. intros W' c' _ (Hf & Hr). exact (pg_keepB _ _ _ _ _ _ _ _ (fun m => P mem -> P m) W' c' Hf Hr).
Qed.

End fg.
End dg.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
(* ======== the instance: image B's whole-program listing PI_prog_B; the image facts by computation ======== *)
Lemma pgb_Hent_str : @pa_sigma _ B_prog_listing PI_prog_B AS_pj_get_str = @pa_val _ B_prog_listing PI_prog_B A_TEXT + AF_gsB.
Proof. vm_compute. reflexivity. Qed.
Lemma pgb_Hent_get : @pa_sigma _ B_prog_listing PI_prog_B AS_pj_get = @pa_val _ B_prog_listing PI_prog_B A_TEXT + AF_pgB.
Proof. vm_compute. reflexivity. Qed.
(* the GOT word of the shadow base lies in the RELRO range, the shadow cell in the last (writable) load segment *)
Lemma pgb_Hobj : forall i, 0 <= i < 8 ->
  in_img (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B (A_OBJ 0) + i) /\
  in_img (@pa_segs _ B_prog_listing PI_prog_B) (@pa_val _ B_prog_listing PI_prog_B (A_OBJ 12) + i).
Proof.
intros i Hi. change (@pa_val _ B_prog_listing PI_prog_B) with B_prog_val. rewrite B_prog_obj0, B_prog_obj12.
change (@pa_segs _ B_prog_listing PI_prog_B) with rsegs. split.
- apply B_prog_relro. unfold B_prog_relro_lo, B_prog_relro_hi. lia.
- unfold in_img. eexists. split; [right; right; right; left; reflexivity|].
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
Qed.

Variable SK : YI16.sink_head.
#[local] Notation SEGSB := (@pa_segs _ B_prog_listing PI_prog_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGSB -> (word -> option byte) -> Model -> Prop.
(* the allocator relation's engine laws, at the harness head of CfParams_preset (discharged at the unit's instance) *)
Hypothesis LAWS : AR_laws_x SEGSB B ARx (@cf_head CfParams_preset).
(* the unit's image binding of B at PI_prog_B (owner a Theorem Labs lane; the other image-B lanes take the same) *)
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
(* the memory invariant (generic until the YAk spelling of fQmn) and the strcmp call keeping it *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGSB P.
Hypothesis PCALL : srr_inv_call SEGSB P.
(* the strcmp row (YGcallMxmn.v astrcmp_realizes_xrom; owner c-libc-stdio), by name *)
Hypothesis ASC : astrcmp_realizes_xrom SEGSB B ARx (@pa_relro_lo _ _ PI_prog_B) (@pa_relro_hi _ _ PI_prog_B)
  (@pa_sigma _ B_prog_listing PI_prog_B AS___wrap_strcmp).

(* The texts at image B: the program listing PI_prog_B and the generated image record prh_img_B *)
Theorem pj_get_holds_B_inst :
  tpj_get_specXP (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P.
Proof.
eapply pj_get_holds_B; first [ eassumption | exact pgb_Hent_get | exact pgb_Hobj ].
Qed.
Theorem pj_get_str_holds_B_inst :
  tpj_get_str_specXP (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P.
Proof.
eapply pj_get_str_holds_B;
  first [ eassumption | exact pgb_Hent_str | exact pgb_Hobj | exact pj_get_holds_B_inst ].
Qed.
End inst.

(* ======== the texts (PRH_FnPj.v 5aca5cbe2cfb at the kit cut 7cdbb61b5fa0, character-identical to
   at the #102 kit tip, 908f34f0beaa: fQmn over YAkMemnorm.memnorm) at PI_prog_B:
   the P-instance at YAkMemnorm.memnorm (laws YSRrMemnorm.srr_inv_laws_memnorm_k), converted by S6PjStrcmp.v
   tpj_get_specX_of_P / tpj_get_str_specX_of_P ======== *)
Section k0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Notation SEGSB := (@pa_segs _ B_prog_listing PI_prog_B).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGSB -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGSB B ARx (@cf_head CfParams_preset).
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis ASC : astrcmp_realizes_xrom SEGSB B ARx (@pa_relro_lo _ _ PI_prog_B) (@pa_relro_hi _ _ PI_prog_B)
  (@pa_sigma _ B_prog_listing PI_prog_B AS___wrap_strcmp).
Theorem pj_get_holds_B_K0 :
  tpj_get_specX (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
apply tpj_get_specX_of_P.
exact (pj_get_holds_B_inst SK B ARx LAWS TL (YAkMemnorm.memnorm SEGSB) (srr_inv_laws_memnorm_k SEGSB) (fun m m' H => H)
  ASC).
Qed.
Theorem pj_get_str_holds_B_K0 :
  tpj_get_str_specX (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK.
Proof.
apply tpj_get_str_specX_of_P.
exact (pj_get_str_holds_B_inst SK B ARx LAWS TL (YAkMemnorm.memnorm SEGSB) (srr_inv_laws_memnorm_k SEGSB) (fun m m' H => H)
  ASC).
Qed.
End k0.

(* ======== the top at the unit's image instance (lib/B/PALibB.v 5baa19c890f7, h-rw-man-5 palib102bj ed438196d17c):
   B := YD2l.TfibB, ARx := ARcf at CfParams_preset; PALib by exvi_eh_palib, the laws by exvi_eh_laws. Required HERE,
   after every walk proof, because PALibB's closure (YStrtodRowX -> lib/Lib/Mem.v) loads lib/Lib/LiaTwx2.v, which
   redefines lia. The one remaining hypothesis is c-libc-stdio's strcmp row. ======== *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Notation SEGSB := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CfParams_preset) SEGSB TB).
Hypothesis ASC : astrcmp_realizes_xrom SEGSB TB ARI (@pa_relro_lo _ _ PI_prog_B) (@pa_relro_hi _ _ PI_prog_B)
  (@pa_sigma _ B_prog_listing PI_prog_B AS___wrap_strcmp).
Theorem pj_get_holds_B_top :
  tpj_get_specX (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARI SK.
Proof. exact (pj_get_holds_B_K0 SK TB ARI PALibB.exvi_eh_laws PALibB.exvi_eh_palib ASC). Qed.
Theorem pj_get_str_holds_B_top :
  tpj_get_str_specX (cp := CfParams_preset) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) TB ARI SK.
Proof. exact (pj_get_str_holds_B_K0 SK TB ARI PALibB.exvi_eh_laws PALibB.exvi_eh_palib ASC). Qed.
End top.

Print Assumptions pj_get_holds_B_K0.
Print Assumptions pj_get_str_holds_B_K0.
Print Assumptions pj_get_holds_B_top.
Print Assumptions pj_get_str_holds_B_top.
Set Printing All.
Check pj_get_holds_B_K0.
Check pj_get_str_holds_B_K0.
Check pj_get_holds_B_top.
Check pj_get_str_holds_B_top.
Unset Printing All.
(* the wrong-image check: every PA / L / PI argument of the tops names image B' (PI_prog_B, B_prog_listing, prh_img_B) *)
Set Printing Implicit. Unset Printing Notations.
About pj_get_holds_B_top.
About pj_get_str_holds_B_top.
Unset Printing Implicit. Set Printing Notations.
