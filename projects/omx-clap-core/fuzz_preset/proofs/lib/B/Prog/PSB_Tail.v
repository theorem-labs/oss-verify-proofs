(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 1110 of its 1140 lines of code are new or changed and 322 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan): the three TAIL stretches of the walk, proved against the
   cut layer lib/A/Prog/PS_Gen.v + lib/B/Prog/PSB_Base.v on the kit's cut 7cdbb61b5fa0 (earlier the OLD-PIN ACCEPTANCE base
   6225fcbb328, kit 4f18c75d4900; generic P, a Theorem Labs lane 12:18Z / 12:22Z):
   psb_ret0_holdsP (from PSB_RET0), psb_retok_holdsP (from PSB_RETOK) and psb_free_holdsP (from PSB_FREE), each stated
   over a memory invariant P (srr_inv_laws segs P; the free also srr_inv_call segs P, as it crosses the kit call
   fuzz_free), carried at the cut (ps_carryP: ps_carry with `/\ P mem` last) and ending in ps_postP P CW D. P stays
   ABSTRACT here: every engine run is the invariant twin paj_run_x_inv at P with its laws; at a return ps_closeP (or
   fpostW_x_of_kept with ps_QP) takes P from the carry. The memnorm instance (PS_Gen's ps_mn D) is taken ONCE, at the
   function's top, never in this file.
   THE FREE CALL has NO open premise: fuzz_free's text (the kit's cut 7cdbb61b5fa0, PRH_FnAlloc.v blob 4d8aeba047e5) posts
   the m-form fpostbm, so P across the call is the TEXT's memnorm keep through srr_inv_call. It takes
   NO position (POST-IMPLICATION form): its live count ccnt24 at the call is ps_pre's class-24 peak at the all-granted
   events' second state (PS_Gen.ps_count24_free), and its post transfers any position by [HFr m], which extends the
   cut's malloc transfer (ps_alloc's ps_rpos_mal, [HMal m]) to the bad-escape arm's [HMal m; HFr m]. fpre's two last
   conjuncts at the call (stack top, raZ below the ceiling) are discharged here. (Before the #102 re-fit, lane PstrBp:
   the old kit f668aebf57c4 took iface_room_pos and ccnt24 by PresetCfnB.counts_of_room_pos_rl.)
   THE HULL: the free's `p <> 0 -> hull_budget S []` is ps_pre's budget less the malloc's use, which the cut's
   ps_rpos_mal carries (PS_Gen.ps_hull_free); its post's hull_used S S2 [] keeps that use for the bad-escape arm's
   ps_rpos; the success arm's post takes the use from ps_rpos_mal.
   THE STABLE STATEMENTS psb_ret0_holds / psb_retok_holds / psb_free_holds are the P := (fun _ => True) corollaries
   (srr_inv_laws_True, srr_inv_call_True, psb_seg_*_of_True). psb_ret0_holds and psb_retok_holds are at their
   statements of record (d19ced981f4), UNMOVED. psb_free_holds MOVED for the callee's TEXT only: its two open premises
   of record (the live count, psb_free_rp) are gone; the text took the room position at f668aebf57c4, takes none now;
   the kit's primed tfuzz_free_specX ends at wle' segs RZ_cf, so its NULL-return premise is the ret0 stretch over that
   relation (psb_seg_ret0R) and its conclusion psb_seg_free is SRr' segs RZ_cf.
   rule 24: proves no function (kind: segment lemma). The function is parse_string B (lane BParseString); its reuse
   search is the record file r24-index.txt (sha256 e7c12b08eeb1; internal record) (checker CONFIRM; donor none).
   FILE SET: every non-lane file as the kit's cut 7cdbb61b5fa0 carries it (PRH_Base.v ef7c8ca98529, PRH_FnAlloc.v
   4d8aeba047e5, PRH_FnReader.v f1ae32e3b2cd, YGcfRoomLive.v edc1017de99c; YCbqG.v 219748197d6b, YGcallcf.v
   8645fa6a514f, YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f, YCbqGcall.v c1fcd07d2537, YSRrMemnorm.v 5ffa8525936b
   (srr_inv_call); B listing c97cc46b3e13 / 15fab93fe702) and this row's shared text-across-a-call lemma
   lib/B/Prog/PSB_Src.v; earlier the lane's acceptance base 6225fcbb328 (the kit-oldpin 4f18c75d4900, engine s1b of
   c-omx-alloc-preset-s1b 459129c18903). TEMPLATES (read, adapted, not required): WalkS4's image-A S4_PsRet.v and
   S4_PsFree.v (the gp form a working branch 18d97df47d0).
   THE CODE (the neutral listing parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record); every offset is a
   DERIVED byte offset from parse_string's B entry):
     1248  mv a0, s2; 1252 jal fuzz_free           PSB_FREE: every bad escape
     1256  li s2, 0                                PSB_RET0: the join of every refusing path
     1260  mv a0, s2                               PSB_EPI: the epilogue, shared by both returns
     1264..1312  the 13 reloads ra 136, s0 128, .., s11 40 off the body sp (ps_saved)
     1316  addi sp, sp, 144; 1320 ret
     1324  srli a0, s3, 3; add a0, a0, s7; lb a0, 0(a0); bnez a0 -> 1376 (partial granule, back to 1340)
     1340  li a0, -1; sb zero, 0(s3) (the NUL at w); beq s4, a0 -> 1372 (UBSan unimp, not taken: r <> -1)
     1352  lbu a0, 0(s6); bnez a0 -> 1536 (q's shadow cell; errpath_store8)
     1360  addi s4, s4, 1; 1364 sd s4, 0(s0) (PSB_CURSOR_STORE: the caller word in->p); 1368 j 1260
   The epilogue is proved ONCE (psb_epiPR, from 1256 or from 1260, over a world relation R); psb_ret0_holdsPR is
   psb_epiPR at 1256.
   Numerals: 144 (LENGTH: PS_FRAME, checked by vm_compute), the frame offsets -8 .. -104 off the entry sp (DERIVED:
   PS_FRAME - 136 .. PS_FRAME - 40) and 40 / 136 (LENGTH: the lowest / highest saved slot off the body sp), 1260
   (DERIVED offset PSB_EPI), atom indices 0..64 (DERIVED: the symbolic engine's numbering: 0..31 the entry registers,
   32..63 the current registers = 32 + the register number, 64 the shadow-base atom of the epilogue), register numbers
   1 2 3 4 8 10 18 22 23 (WORD), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 62 / 2 ^ 47 - 8 / 2 ^ 47 - 24 (DERIVED: the shadow
   span, the stack band and the text / block bounds), 4 / 3 / 0 (DERIVED: log2 of the 16-, 8-, 1-byte alignments),
   4096 (LENGTH: the least block address), 1 / 8 / 16 / 24 / 64 (LENGTH: a byte, a word, two words, the cursor
   struct, fpre's stack-top gap), 2 ^ 40 (LENGTH: the listing's code span), 2 (LENGTH: instruction alignment).
   No ADDRESS literal: every pc is psb_pc / BASE + PSB_* or a PrhImg field, compared by vm_compute. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall YCbqGcallW.
(* memnorm and its keep (the runner twins paj_run_x_inv, paj_run_tok_x_inv are YC1fPx's); no YAjMemnorm (LiaTwx2) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base PSB_Src.
(* the re-hiding move: SRrG / SRr' / SRr_SRrG / wle' (YA0nH) at preset's zone YGcfRehidePost.RZ_cf (the kit's primed
   tfuzz_free_specX: SRr' with fpostbm at wle') *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the live count at the free call is ps_pre's class-24 peak at the second state (PS_Gen.ps_count24_free,
   the post-implication form): no room position, so no harness contract *)
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state shapes (no image value: atoms only) ---- *)
(* DERIVED: the epilogue's first instruction, `mv a0, s2` *)
Definition PSB_EPI : Z := 1260.
(* the current registers as the environment's atoms 32..63 *)
Definition psb_cur (regs : bvmap 5 word) : list word := map (getr regs) all_regs.
(* the register file at 1256 / 1260: every register is its current atom, but sp (the entry sp atom 2 less the frame)
   and gp / tp (the entry's atoms: ps_gptp) *)
Definition psb_sr_epi : list sv :=
  SLit 0 :: SOff 33 0 :: SOff 2 (-144) :: SOff 3 0 :: SOff 4 0 :: map (fun i => SOff (32 + i) 0) (seq 5 27).
(* parse_string's frame below the entry sp (atom 2), read-only here: the 13 saved registers as the entry's atoms *)
Definition psb_frame_region : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 0 0
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27 0)) ].
Definition psb_facts_epi : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition PSB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition PSB_Bx_epi : sv := SOff 64 0.
(* ---- the state at PSB_RETOK: the epilogue's register atoms, but s6 (x22) in the SHAPE the ASan token engine matches
   (the shadow cell of s0 = q: (q >> 3) + s7, as the prologue builds it at B offsets 80-84), the one written byte at
   w = s3 (atom 51) and the caller's cursor word at q = s0 (atom 40); the frame region rides along for the epilogue.
   r = s4 (atom 52) carries its range, which decides the UBSan check `beq s4, a0` (a0 = -1) at offset 1348. ---- *)
Definition psb_sr_retok : list sv :=
  [SLit 0; SOff 33 0; SOff 2 (-144); SOff 3 0; SOff 4 0;
   SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0;
   SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0; SOff 52 0; SOff 53 0;
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SOff 55 0);
   SOff 55 0; SOff 56 0; SOff 57 0; SOff 58 0; SOff 59 0; SOff 60 0; SOff 61 0; SOff 62 0; SOff 63 0].
Definition psb_w_region : YP09.region := YP09.mkRegion (Some 51%nat) 0 1 0 1 [].
Definition psb_q_region : YP09.region := YP09.mkRegion (Some 40%nat) 0 8 0 8 [].
Definition psb_facts_retok : facts :=
  mkFacts [(51%nat, mkAF 4096 (2 ^ 47 - 8) 0); (40%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
           (55%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (52%nat, mkAF 0 (2 ^ 62) 0);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition psb_SH_retok : list shent := [mkSHE 51 0 1; mkSHE 40 0 8].
Definition PSB_Bx_retok : sv := SOff 55 0.

Section pst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* image B's instances (PSB_Base.v's), the ones the engine's tactics infer; every statement below names them *)
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation VAL := (@pa_val _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
#[local] Notation EB := (Eimg (L := B_prog_listing) (PI := PSB_PAImg)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation PST := (prh_pst (PI := PSB_PrhImg)).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
#[local] Notation KEPT := (cj_kept (SK := SK) segs B PST).
#[local] Notation LEDGER := (prh_ledger (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_in := (ps_in (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_SP := (PS_SP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_FRAME := (PS_FRAME (PI := PSB_PrhImg)).
#[local] Notation ps_carryP := (ps_carryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_pre := (ps_pre (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx).
#[local] Notation ps_postP := (ps_postP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_Qres := (ps_Qres (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_gptp := (ps_gptp (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_alloc := (ps_alloc (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_saved := (ps_saved (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_at_ret0P :=
  (ps_at_ret0P (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
(* the R forms beside (PS_Gen): the post, the carry and the NULL return's cut over a world relation R *)
#[local] Notation ps_postPR := (ps_postPR (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_carryPwR := (ps_carryPwR (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).
#[local] Notation ps_at_ret0PR :=
  (ps_at_ret0PR (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK).

(* ---- the Section hypotheses (the internal file STRETCH-BRIEF.md) ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis TL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).

(* ---- the environment: atoms 0..31 the entry registers, 32..63 the current ones ---- *)
Lemma psb_ew_hi : forall R X n, (32 <= n < A_TEXT)%nat -> ew (EB (Ereg R X)) n = nth (n - 32) X (Z_to_bv 64 0).
Proof.
intros R X n Hn. rewrite Eimg_low by lia. unfold Ereg. cbn [ew].
replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
Lemma psb_ew_lo : forall R X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EB (Ereg R X)) n = getr R r.
Proof.
intros R X n r H. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat R X n r H).
Qed.
Lemma psb_frame : PS_FRAME = 144.
Proof. vm_compute. reflexivity. Qed.

Ltac psb_reg_tac Hsp Hgp Htp HFR :=
  match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | rewrite (psb_ew_lo _ _ 2 2 eq_refl), Hsp; unfold w64, PS_Gen.PS_SP, spZ; rewrite HFR; f_equal; lia
  | rewrite (psb_ew_lo _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
  | rewrite (psb_ew_lo _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp ].

Lemma psb_regs_ok_epi : forall (D : ps_in) regs, getr regs 2 = w64 (PS_SP D) -> ps_gptp D regs ->
  regs_ok (EB (Ereg (pi_regs D) (psb_cur regs))) psb_sr_epi regs.
Proof.
intros D regs Hsp [Hgp Htp]. pose proof psb_frame as HFR.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [psb_reg_tac Hsp Hgp Htp HFR|]). destruct Hr.
Qed.

(* the kept relation does not look at the model's materialised pages *)
Lemma psb_kept_md : forall STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3,
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.
(* the same over a world relation R *)
Lemma psb_kept_mdR : forall (R : world segs -> world segs -> Prop) STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3,
  cj_keptR (SK := SK) segs B PST R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  cj_keptR (SK := SK) segs B PST R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
intros R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.

Ltac psb_chunk Ei Hs HFR :=
  lazymatch goal with |- YP09.chunk_ok _ ?E0 ?m ?b {| c_off := ?o; YP09.c_val := CVal 8 ?e |} =>
  lazymatch type of Hs with val_mem _ _ _ _ ?v =>
    apply (chunk_ok_val _ E0 m b o 8 e v);
    [ cbn [sv_denot]; rewrite Ei, Z.add_0_r; reflexivity
    | lazymatch goal with |- 0 <= ?vv < _ => replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity;
        try unfold raZ; apply u64_range end
    | cbn; lia
    | lazymatch type of Hs with val_mem _ _ ?a _ _ =>
        replace (b + o) with a by (unfold PS_Gen.PS_SP; rewrite HFR; lia) end;
      exact Hs ]
  end end.

(* ---- THE EPILOGUE, once: from 1256 (s2 := 0) or from 1260 (s2 = res), to the return, ending in ps_postPR P R CW D, at
   any memory invariant P with the runner laws (the run is the twin at P; the return keeps the memory) and over a world
   relation R (reflexive, transitive, containing wle): the NULL return is reached on both sides of the bad escape's
   fuzz_free, after it with the cut at wle' segs RZ_cf; psb_ret0_holdsP is its use at wle. ---- *)
Lemma psb_epiPR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle segs W W' -> R W W') ->
  forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall CTX CW (D : ps_in) ly S Hp W regs mem md k FPs WS o res,
  ps_pre CTX CW D ->
  YCbqGwild.wbudget CW 0 WS ->
  ps_carryPwR P R D ly S Hp W mem md k FPs WS ->
  ps_gptp D regs -> getr regs 2 = w64 (PS_SP D) ->
  (o = PSB_RET0 /\ res = 0 \/ o = PSB_EPI /\ getr regs 18 = w64 res) ->
  room_live_cf S ->
  ps_Qres D res ly S Hp W mem md ->
  SRrG segs R W (cfg_at segs (psb_pc o) regs mem md) (ps_postPR P R CW D).
Proof.
intros R Rr Rt Rsub P PLAW CTX CW D ly S Hp W regs mem md k FPs WS o res HPRE HBW (HJw & HK & HSV & HSRC & HHOME & HMN)
  HGT Hsp Ho HRL HQ.
(* the cut's journal is at a BUDGET WS (the bad escape's fuzz_free may store a cursor trace); the run takes it at the
   rebased entry state (YCbqGwild.ajournal_xw_rebaseR: budget [] from the entry with the cut's depot), and the close
   puts the budget back (PS_Gen.ps_closePwR, ajournal_xw_unbase0R at the cut's wild-part inclusion) *)
pose proof (ajxR_wild HJw) as HWI.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) segs B PST ARx R _ _ _ _ _ (pi_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJw)
  as HJ.
clear HJw.
pose proof HPRE as ((HPX & _) & _).
pose proof HPX as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof psb_frame as HFR.
assert (Rsp : 2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47) by lia.
pose proof (psb_regs_ok_epi D regs Hsp HGT) as HRO.
assert (E1 : ew (EB (Ereg (pi_regs D) (psb_cur regs))) 1 = getr (pi_regs D) 1) by exact (psb_ew_lo _ _ 1 1 eq_refl).
assert (E50 : ew (EB (Ereg (pi_regs D) (psb_cur regs))) 50 = getr regs 18)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); reflexivity).
assert (HAE : env_agree 32 (Ereg (pi_regs D) (psb_cur regs)) (EB (Ereg (pi_regs D) (psb_cur regs))))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HEI : img_env VAL A_LIM (EB (Ereg (pi_regs D) (psb_cur regs)))) by apply Eimg_env.
assert (Usp : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 2) = spZ (pi_regs D))
  by (rewrite (psb_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (HS : st_ok_pi segs VAL (EB (Ereg (pi_regs D) (psb_cur regs)))
  (mkSS (PSB_OFF + o) psb_sr_epi [psb_frame_region] None psb_facts_epi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + o))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, psb_frame_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    destruct HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    repeat apply Forall_cons; [..|apply Forall_nil].
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 1 1 eq_refl) S1 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 8 8 eq_refl) S2 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 9 9 eq_refl) S3 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 18 18 eq_refl) S4 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 19 19 eq_refl) S5 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 20 20 eq_refl) S6 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 21 21 eq_refl) S7 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 22 22 eq_refl) S8 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 23 23 eq_refl) S9 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 24 24 eq_refl) S10 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 25 25 eq_refl) S11 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 26 26 eq_refl) S12 HFR.
    + psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 27 27 eq_refl) S13 HFR.
  - exact (conj I I).
  - split; [|split; [exact I | exact I]]. cbn [psb_facts_epi f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16. lia. }
assert (SHOK : sh_ok segs PSB_Bx_epi [] (EB (Ereg (pi_regs D) (psb_cur regs))) (mrestrict (w_H W) mem))
  by (unfold sh_ok; apply Forall_nil).
remember (EB (Ereg (pi_regs D) (psb_cur regs))) as E eqn:HE.
clear HE HRO.
(* the run keeps P (YC1fPx.v's twin at P over R, laws PLAW): HMN is P of the end memory after it *)
pose (RUN := @paj_run_x_invR fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW R Rr Rt).
pose (RET := @paj_ret_at fx rc _ PSB_PAListing PSB_PAImg).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + o) with (BASE + (PSB_OFF + o)) by lia.
assert (HQ0 : forall regs2 md2, getr regs2 10 = w64 res ->
  ajournal_xR (SK := SK) segs B PST ARx R (PS_Gen.PS_WSTK D) (PS_Gen.PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D)
    (set_depot (st_depot S) (pi_S D)) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem md2 k ->
  cj_keptR (SK := SK) segs B PST R STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] FPs
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem md2 ->
  P mem -> aregs_preserved (pi_regs D) regs2 ->
  ps_postPR P R CW D W (mkCfg (YK11.mkst regs2 (YK11.getr (pi_regs D) 1) mem (YK11.seg_rom segs)) md2)).
{ intros regs2 md2 H10 HJ2 HK2 HPm HP.
  apply (ps_closePwR (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P R CW D ly S Hp W regs2 mem
    md2 k FPs WS (st_depot S) Hstk0 HBW HJ2 HWI HK2 HP); [|exact HPm].
  exact (ps_Q_of_res (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B D res ly S Hp W regs2 mem md2
    H10 HRL HQ). }
destruct Ho as [[-> ->] | [-> H18]].
- paj_run_tok_x_invR RUN HS HJ SHOK HMN PSB_Bspan;
    [cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (Emem : ms_mem msn = mem)
      by (apply functional_extensionality; intros x; apply HF; intros (r & Hin & Hr);
          cbn [ss_mem In] in Hin; destruct Hin as [<- | []];
          cbn [psb_frame_region YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; lia) end.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  (* the return step is the plain one: an SRr fact is an SRrG fact at every R containing wle *)
  apply (SRr_SRrG segs R Rsub).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite Emem, R1, E1. rewrite Hra. rewrite Emem in HJ, HMN.
  apply HQ0.
  + rewrite R10. reflexivity.
  + apply (ajournal_x_materializeR segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) R); exact HJ.
  + apply (psb_kept_mdR R _ _ _ _ _ _ _ _ _ _ _ _ _ md); [exact HK|].
    eapply same_but_materialized_trans; apply same_but_materialized_wvb_any.
  + exact HMN.
  + exact (aregs_preserved_of_st_ok segs _ _ _ _ (pi_regs D) (psb_cur regs) HS HAE ltac:(vm_compute; reflexivity)).
- paj_run_tok_x_invR RUN HS HJ SHOK HMN PSB_Bspan;
    [cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (Emem : ms_mem msn = mem)
      by (apply functional_extensionality; intros x; apply HF; intros (r & Hin & Hr);
          cbn [ss_mem In] in Hin; destruct Hin as [<- | []];
          cbn [psb_frame_region YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; lia) end.
  prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1.
  apply (SRr_SRrG segs R Rsub).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite Emem, R1, E1. rewrite Hra. rewrite Emem in HJ, HMN.
  apply HQ0.
  + rewrite R10, E50. exact H18.
  + apply (ajournal_x_materializeR segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) R); exact HJ.
  + apply (psb_kept_mdR R _ _ _ _ _ _ _ _ _ _ _ _ _ md); [exact HK|].
    eapply same_but_materialized_trans; apply same_but_materialized_wvb_any.
  + exact HMN.
  + exact (aregs_preserved_of_st_ok segs _ _ _ _ (pi_regs D) (psb_cur regs) HS HAE ltac:(vm_compute; reflexivity)).
Qed.

(* ---- STRETCH 1: the NULL return, from PSB_RET0, at any P with the runner laws, over a world relation R (after the
   bad escape's fuzz_free at wle' segs RZ_cf); psb_ret0_holdsP is its instance at wle ---- *)
Theorem psb_ret0_holdsPR : forall CTX CW (P : (word -> option byte) -> Prop) (R : world segs -> world segs -> Prop),
  (forall W, R W W) -> (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle segs W W' -> R W W') ->
  srr_inv_laws segs P -> psb_seg_ret0PR B ARx SK CTX CW P R.
Proof.
intros CTX CW P R Rr Rt Rsub PLAW D ly S Hp W regs mem md HPRE ((k & WS & HBW & HC) & HGT & Hsp & HRL & _ & HQ).
exact (psb_epiPR R Rr Rt Rsub P PLAW CTX CW D ly S Hp W regs mem md k [] WS PSB_RET0 0 HPRE HBW HC HGT Hsp
  (or_introl (conj eq_refl eq_refl)) HRL HQ).
Qed.
Theorem psb_ret0_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> psb_seg_ret0P B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW.
exact (psb_ret0_holdsPR CTX CW P (@wle segs) (wle_refl segs) (wle_trans segs) (fun W W' H => H) PLAW).
Qed.
(* its stable statement (d19ced981f4), the P := (fun _ => True) instance, and its form over R *)
Theorem psb_ret0_holds : forall CTX CW, psb_seg_ret0 B ARx SK CTX CW.
Proof.
intros CTX CW. apply (psb_seg_ret0_of_True B ARx SK CTX CW).
apply psb_ret0_holdsP. exact srr_inv_laws_True.
Qed.
Theorem psb_ret0_holdsR : forall CTX CW (R : world segs -> world segs -> Prop),
  (forall W, R W W) -> (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle segs W W' -> R W W') ->
  psb_seg_ret0R B ARx SK CTX CW R.
Proof.
intros CTX CW R Rr Rt Rsub. apply (psb_seg_ret0R_of_True B ARx SK CTX CW R).
exact (psb_ret0_holdsPR CTX CW (fun _ => True) R Rr Rt Rsub srr_inv_laws_True).
Qed.

(* ---- the success tail's helpers ---- *)
(* s6's SHAPE at PSB_RETOK: the shadow cell of q, as the ASan token engine writes it *)
Lemma psb_s6_denot : forall E q, bv_unsigned (ew E 40) = q -> bv_unsigned (ew E 55) = SHADOW_OFF ->
  0 <= q < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 40 0) (SLit 3)) (SOff 55 0)) = w64 (SHADOW_OFF + q / 8).
Proof.
intros E q H40 H55 Hq. cbn [sv_denot]. rewrite H40, H55, !Z.add_0_r.
assert (Hd : 0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite !(Z.mod_small (q / 8)) by lia. rewrite (Z.mod_small (q / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
lia.
Qed.

Ltac psb_reg2 Hsp Hgp Htp HFR Hs6e :=
  match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  first
  [ rewrite Hs6e; assumption
  | cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite (psb_ew_lo _ _ 2 2 eq_refl), Hsp; unfold w64, PS_Gen.PS_SP, spZ; rewrite HFR; f_equal; lia
    | rewrite (psb_ew_lo _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp
    | rewrite (psb_ew_lo _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp ] ].

Lemma psb_regs_ok_retok : forall (D : ps_in) regs, getr regs 2 = w64 (PS_SP D) -> ps_gptp D regs ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 22 = w64 (SHADOW_OFF + pi_q D / 8) ->
  getr regs 8 = w64 (pi_q D) -> 0 <= pi_q D < 2 ^ 47 ->
  regs_ok (EB (Ereg (pi_regs D) (psb_cur regs))) psb_sr_retok regs.
Proof.
intros D regs Hsp [Hgp Htp] H23 H22 Hq8 Hqr. pose proof psb_frame as HFR.
assert (E40 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 40) = pi_q D)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite Hq8; unfold w64; apply unsigned_lit_small; lia).
assert (E55 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 55) = SHADOW_OFF)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (psb_s6_denot _ _ E40 E55 Hqr) as Hs6e.
apply regs_ok_by_cases. intros rr Hrr. cbv [all_regs In] in Hrr.
repeat (destruct Hrr as [<-|Hrr]; [psb_reg2 Hsp Hgp Htp HFR Hs6e|]). destruct Hrr.
Qed.

(* the block the one fuzz_malloc made is NOT a block of the entry state *)
Lemma psb_newblk : forall (D : ps_in) ly S Hp W mem md out Q,
  ps_alloc D ly S Hp W mem out Q -> ARx ly S Hp W mem md ->
  ~ In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B (pi_ly D) (pi_S D)).
Proof.
intros D ly S Hp W mem md out Q HAL HAR Hin.
pose proof cf_head_nonneg as CH0.
pose proof HAL as (_ & _ & _ & _ & Hab & _).
assert (Hin' : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin') as (_ & _ & _ & _ & _ & Hpw).
assert (Hrq : 0 < req_size (Z.of_nat Q + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
rewrite Hab in Hpw. apply in_split in Hin as (l1 & l2 & El). rewrite El in Hpw.
pose proof (pairwise_In2 zdisjoint _ (out - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
  (out - cf_head, req_size (Z.of_nat Q + 1 + cf_head))
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l1)
  (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) [] Hpw
  ltac:(rewrite <- app_assoc, !map_app; reflexivity)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* byte windows a two-store run leaves alone, and the shadow arithmetic at the RunCeil ceiling *)
Lemma psb_val_mem_keep : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v H HV kk Hk. rewrite H by lia. exact (HV kk Hk). Qed.
Lemma psb_garr8_keep : forall (m m' : word -> option byte) p l,
  (forall x, p <= x < p + Z.of_nat (length l) -> mbyte segs m' x = mbyte segs m x) ->
  garr8 segs m p l -> garr8 segs m' p l.
Proof.
intros m m' p l H HG j Hj. destruct (HG j Hj) as [HV Hb]. split; [|exact Hb].
apply (psb_val_mem_keep m m' _ 1 _); [|exact HV]. intros x Hx. apply H. cbn in Hx. lia.
Qed.
Lemma psb_forall_skipn : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
Proof.
intros P n. induction n as [|n IH]; intros l H; [exact H|].
destruct l as [|a l]; cbn; [constructor|]. apply IH. inversion H; assumption.
Qed.
Lemma psb_ro_img : forall a,
  in_roP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) a -> in_img segs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PSB_PAImg a Hr)].
Qed.
Lemma psb_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma psb_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (P2 : 0 <= (SHADOW_OFF + x / 8) / 8) by (apply Z.div_pos; unfold SHADOW_OFF; lia).
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
Lemma psb_shadow_out : forall p len x, in_app p len -> p + len <= YM05.alloc_ceiling -> p <= x < p + len ->
  ~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hc Hx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma psb_hull_out : forall p len x n s, in_app p len -> p + len <= YM05.alloc_ceiling -> p <= x -> 0 < n ->
  x + n <= p + len ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
intros p len x n s Happ Hc Hx Hn Hxn Hs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
assert (P1 : 0 <= x / 8) by (apply Z.div_pos; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(discriminate)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(reflexivity)) as M1.
assert (P3 : (x + n - 1) / 8 <= YM05.alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (YM05.alloc_ceiling / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(discriminate)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(reflexivity)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.

Section retok.
(* the head is at least one shadow granule wide (the kit's ONE spelling, PRH_Base.v prh_head_wide, walkkit 9d109484e53;
   discharged at the preset instance by a Theorem Labs lane's preset_head_wide): at cf_head = 0 the NUL store at w = out would
   overwrite the new block's head word, which the ledger reads *)
Hypothesis HW : prh_head_wide.

(* ---- STRETCH 2: the success tail, from PSB_RETOK. ONE run from 1324 to the `ret` at 1320 (the epilogue at 1260 run
   in the same symbolic state, the frame region carried along): the shadow check of w (token engine, discharged by
   the new block's prhReader_vis), the NUL store at w, the UBSan check r <> -1 (decided by r's range), the shadow
   check of q (zero: the real stack's shadow law), s4 + 1, the cursor store at q (PSB_CURSOR_STORE), j 1260, the
   epilogue. The post is ps_Qres's success arm at the written memory, with P of it (the run's twin at P). ---- *)
Theorem psb_retok_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> psb_seg_retokP B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW D ly S Hp W regs mem md out w r Q HPRE HAT.
destruct HAT as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & (H23 & H22 & H24) & HGT & HIN & HSCAN
  & Hsp & H18 & H19 & H20 & H8 & H9 & Hr & (s & Hdec & Hbytes & Hlen) & Hlow & Hhigh).
pose proof HPRE as ((HPX & HROD) & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & Hplt & Hq34 & HWIN & Hqlo & Hqhi & HRA24 & _).
pose proof HPX as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as CH0.
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_hi HJ) as JF1.
pose proof (ajx_blk HJ) as JF2. pose proof (ajx_img HJ) as JF3. pose proof (ajx_frm HJ) as JF4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Jpres. pose proof (ajx_stk HJ) as Jstk.
pose proof (ajx_extra HJ) as JX. pose proof (ajx_qt HJ) as JQT.
pose proof HAL as (Hcnt & Hout4096 & Hout16 & HHp & Hab & HLED & HVIS & HRL & HRP & HBBal).
pose proof HIN0 as (HV0 & HV8 & HV16 & HRW & Hq8 & Htext0 & Htl & Hptext & Hlentb & Hgtb & Hqtext & Hd32).
(* the closing quote is inside the text, so the new cursor p + Q + 2 is too *)
assert (HQr : pi_p D + 1 + Z.of_nat Q < pi_text D + pi_len D).
{ destruct (PjGrammar.scan_quote _ _ HSCAN) as [HQlt _].
  unfold ps_x, rest_atR in HQlt. rewrite length_skipn in HQlt. lia. }
pose proof psb_frame as HFR.
(* DERIVED (vm_compute on the generated PRH_ImgB value): parse_string's stack budget covers its own frame *)
assert (HSTKge : 144 <= STK_parse_string) by (vm_compute; discriminate).
assert (Hinb : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & Hbpw).
assert (Hrq2 : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
assert (Hwb : out - cf_head <= w < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)) by lia.
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
assert (Hqstk : ly_stk_lo ly <= pi_q D /\ pi_q D + 8 <= ly_stk_hi ly).
{ destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _). rewrite Elo, Ehi. split; lia. }
assert (Hqsh : aview segs (w_H W) mem (SHADOW_OFF + pi_q D / 8) = Some 0)
  by (apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md); [exact HARc | lia]).
(* the register and value bounds *)
assert (Hqlo46 : 2 ^ 46 <= pi_q D) by lia.
assert (Hqhi47 : pi_q D + 24 <= 2 ^ 47) by lia.
assert (Hq64 : 0 <= pi_q D < 2 ^ 64) by lia.
assert (Hw4096 : 4096 <= w) by lia.
assert (Hw64 : 0 <= w < 2 ^ 64) by lia.
assert (Hwapp : app_addr w) by (eapply in_app_addr; [exact Hbapp | exact Hwb]).
(* the shadow of the caller's cursor word is zero at the current state *)
assert (HRAq : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (pi_q D) 8).
{ apply (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF (pi_q D) 8 Hq8 eq_refl).
  intros i Hi. replace i with 0 by lia. rewrite Z.add_0_r. unfold shadow_of_addr. exact Hqsh. }
pose proof HVIS as (HRAout & HHULLout).
(* the environment *)
assert (E51 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 51) = w)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H19; unfold w64; apply unsigned_lit_small; lia).
assert (E40 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 40) = pi_q D)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H8; unfold w64; apply unsigned_lit_small; lia).
assert (E55 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 55) = SHADOW_OFF)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H23; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E52 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 52) = r)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H20; unfold w64; apply unsigned_lit_small; lia).
assert (E50 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 50) = out)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H18; unfold w64; apply unsigned_lit_small; lia).
assert (Esp2 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 2) = spZ (pi_regs D))
  by (rewrite (psb_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (HEI : img_env VAL A_LIM (EB (Ereg (pi_regs D) (psb_cur regs)))) by apply Eimg_env.
assert (HS1 : st_ok_pi segs VAL (EB (Ereg (pi_regs D) (psb_cur regs)))
  (mkSS (PSB_OFF + PSB_RETOK) psb_sr_retok [psb_w_region; psb_q_region; psb_frame_region] None psb_facts_retok)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSB_RETOK))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply (psb_regs_ok_retok D regs); try assumption; lia.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [..|apply Forall_nil]; unfold region_ok, psb_w_region, psb_q_region, psb_frame_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E51. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable segs). apply Hbpres. lia.
    + rewrite E40. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable segs). apply Jpres. unfold PS_WSP, PS_WSTK. lia.
    + rewrite Esp2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      destruct HSV as (SV1 & SV2 & SV3 & SV4 & SV5 & SV6 & SV7 & SV8 & SV9 & SV10 & SV11 & SV12 & SV13).
      repeat apply Forall_cons; [..|apply Forall_nil].
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 1 1 eq_refl) SV1 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 8 8 eq_refl) SV2 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 9 9 eq_refl) SV3 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 18 18 eq_refl) SV4 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 19 19 eq_refl) SV5 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 20 20 eq_refl) SV6 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 21 21 eq_refl) SV7 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 22 22 eq_refl) SV8 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 23 23 eq_refl) SV9 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 24 24 eq_refl) SV10 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 25 25 eq_refl) SV11 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 26 26 eq_refl) SV12 HFR.
      * psb_chunk (psb_ew_lo (pi_regs D) (psb_cur regs) 27 27 eq_refl) SV13 HFR.
  - apply pairwise_disjoint_of_extents.
    unfold psb_w_region, psb_q_region, psb_frame_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E51, E40, Esp2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [psb_facts_retok f_atoms atoms_ok].
    split; [|split; [|split; [|split; [|split; [|exact I]]]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite E51. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite E40. change (2 ^ 3) with 8. lia.
    + rewrite E55. rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF. lia.
    + rewrite E52. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite Esp2. change (2 ^ 4) with 16. lia. }
assert (SHOK1 : sh_ok segs PSB_Bx_retok psb_SH_retok (EB (Ereg (pi_regs D) (psb_cur regs))) (mrestrict (w_H W) mem)).
{ repeat apply Forall_cons; [..|apply Forall_nil].
  - apply (shent_ok_of_range segs (w_H W) mem _ PSB_Bx_retok 51 out (Z.of_nat Q + 1) w 0 1 HRAout).
    + unfold U, PSB_Bx_retok. cbn [sv_denot]. rewrite E55, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    + unfold U. cbn [sv_denot]. rewrite E51, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range segs (w_H W) mem _ PSB_Bx_retok 40 (pi_q D) 8 (pi_q D) 0 8 HRAq).
    + unfold U, PSB_Bx_retok. cbn [sv_denot]. rewrite E55, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    + unfold U. cbn [sv_denot]. rewrite E40, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia. }
assert (E1 : ew (EB (Ereg (pi_regs D) (psb_cur regs))) 1 = getr (pi_regs D) 1) by exact (psb_ew_lo _ _ 1 1 eq_refl).
assert (HAE : env_agree 32 (Ereg (pi_regs D) (psb_cur regs)) (EB (Ereg (pi_regs D) (psb_cur regs))))
  by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
(* the charge of the one granted run: [EAlloc (S Q)], i.e. Q + 1 user bytes and one head *)
assert (Htr : PRH_Charge.prhPs_gtrace (ps_x D) = [PjGrammar.EAlloc (Datatypes.S Q)]).
{ unfold PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. rewrite HSCAN, Hdec. reflexivity. }
assert (HTR : PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D)) = Z.of_nat Q + 1 + cf_head).
{ rewrite Htr. unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia. }
assert (HCH8 : 8 <= cf_head) by exact HW.
assert (Hsepw : forall b m x, In (b, m) (ablocks B ly S) -> (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head) ->
  b <= x < b + req_size m -> x <> w).
{ intros b m x Hbm Hne Hx Exw. subst x.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md b m _ _ HARc Hbm Hinb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
remember (EB (Ereg (pi_regs D) (psb_cur regs))) as E eqn:HE.
(* the run keeps P (YC1fPx.v's twin at P, laws PLAW): HMN is P of the end memory after it *)
pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
pose (RET := @paj_ret_at fx rc _ PSB_PAListing PSB_PAImg).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_RETOK) with (BASE + (PSB_OFF + PSB_RETOK)) by lia.
paj_run_tok_x_inv RUN HS1 HJ SHOK1 HMN PSB_Bspan.
+ cbn [ss_mem]. intros a (rg & Hin & Hrg). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [psb_w_region psb_q_region psb_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    rewrite ?E51, ?E40, ?Esp2 in Hrg.
  * right; right; left. exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
    split; [exact Hinb|]. split; [|lia]. exact (psb_newblk D ly S Hp W mem md out Q HAL HARc).
  * left. unfold PS_WSP, PS_WSTK. lia.
  * exfalso. lia.
+ (* ---- the final state, at the `ret`: the model after the run ---- *)
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m1 |} _ => remember m1 as md1 eqn:Emd1 end.
  assert (Hsbm : same_but_materialized md md1) by (rewrite Emd1; apply same_but_materialized_wvb_any).
  (* the two written words, read off the final symbolic state *)
  pose proof (st_ok_mem_ok segs _ _ _ HS1) as (_ & HRS & _).
  cbn [abs_ss setpc ss_mem restrict ms_mem] in HRS.
  apply Forall_cons_iff in HRS as (HRw & HRS). apply Forall_cons_iff in HRS as (HRq & _).
  destruct HRw as (_ & _ & _ & HCw). destruct HRq as (_ & _ & _ & HCq).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCw, HCq.
  rewrite !ew_ewset_other in HCw by lia. rewrite !ew_ewset_other in HCq by lia.
  rewrite E51 in HCw. rewrite E40 in HCq.
  pose proof (Forall_inv HCw) as HC0. pose proof (Forall_inv HCq) as HC1.
  assert (Hvw : val_mem segs (mrestrict (w_H W) (ms_mem ms)) w 1 0).
  { replace w with (w + 0) by lia.
    refine (val_of_chunk_ok segs _ _ w 0 1%N (SLit 0) 0 HC0 eq_refl _ _); cbn; lia. }
  assert (Hvq : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (pi_q D) 8 (r + 1)).
  { replace (pi_q D) with (pi_q D + 0) by lia.
    refine (val_of_chunk_ok segs _ _ (pi_q D) 0 8%N (SOff 52 1) (r + 1) HC1 _ _ _); [| cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E52. reflexivity. }
  (* every other byte is the pre-run one *)
  assert (Hkm : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 1) -> ~ (pi_q D <= a < pi_q D + 8) ->
    mbyte segs (mrestrict (w_H W) (ms_mem ms)) a = mbyte segs (mrestrict (w_H W) mem) a).
  { intros a Ha Hwa Hqa. unfold mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by lia. intros (rg & Hin & Hrg). cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbn [psb_w_region psb_q_region psb_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
      rewrite ?E51, ?E40, ?Esp2 in Hrg; lia. }
  assert (Hkv : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 1) -> ~ (pi_q D <= a < pi_q D + 8) ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hwa Hqa; unfold aview; rewrite (Hkm a Ha Hwa Hqa); reflexivity).
  (* the kept relation: the run's two writes (the new block's byte w, the caller's word FP), then from entry *)
  assert (HKx : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [(w, w + 1)]
      ly S W mem md ly S W (ms_mem ms) md1).
  { apply (cj_kept_exec (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg) _ _ _ _ ly S Hp W mem md _ _
      (fun a => (w <= a < w + 1) \/ (pi_q D <= a < pi_q D + 8)) HARc).
    - rewrite Elo. exact Hceil.
    - rewrite Elo. lia.
    - rewrite Ehi. lia.
    - intros x Hx. apply HFr. intros (rg & Hin & Hrg). apply Hx. cbn [ss_mem In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]];
        cbn [psb_w_region psb_q_region psb_frame_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
        rewrite ?E51, ?E40, ?Esp2 in Hrg; lia.
    - intros a [Ha|Ha].
      + right; right. split; [exists (w, w + 1); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb | lia].
      + right; left. exists (pi_q D, pi_q D + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    - exact Hsbm. }
  assert (HKf : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
      (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W (ms_mem ms) md1).
  { eapply (cj_kept_trans (SK := SK) segs B PST ARx LAWS) with (FP1 := []) (FP2 := [(w, w + 1)]) (Hpc := pi_Hp D) (Hp2 := Hp);
      [exact HK | exact HKx | exact HAR0 | exact HARc | lia | lia | |].
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - intros a (rg & [<-|[]] & Ha). cbn [fst snd] in Ha. right; left.
      exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb|].
      split; [exact (psb_newblk D ly S Hp W mem md out Q HAL HARc) | lia]. }
  (* ---- ps_Qres's success arm at the written memory ---- *)
  assert (HVIS1 : prhReader_vis W (ms_mem ms) out (Z.of_nat Q + 1)).
  { split.
    - apply (range_addressable_agree (aview segs (w_H W) mem)); [|exact HRAout].
      intros x Hx. assert (Hx47 : 0 <= x < 2 ^ 47) by lia. pose proof (psb_shadow_low x Hx47) as Hs.
      assert (Hsw : ~ (out - cf_head <= shadow_of_addr SHADOW_OFF x < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)))
        by (apply (psb_shadow_out _ _ x Hbapp Hbceil); lia).
      apply Hkv; lia.
    - intros Hn0 s0 Hs0.
      assert (Hl : 0 <= s0 < 2 ^ 46) by (apply (psb_hull_low out (Z.of_nat Q + 1) s0); [lia | lia | lia | exact Hs0]).
      assert (Ho : ~ (out - cf_head <= s0 < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head)))
        by (apply (psb_hull_out _ _ out (Z.of_nat Q + 1) s0 Hbapp Hbceil); [lia | lia | lia | exact Hs0]).
      rewrite Hkv by lia. exact (HHULLout Hn0 s0 Hs0). }
  assert (Hxbytes : Forall (fun b => 0 <= b < 256) (ps_x D)).
  { unfold ps_x, rest_atR. apply psb_forall_skipn. apply Forall_forall. intros c Hc.
    apply In_nth with (d := 0) in Hc as (j & Hj & <-). exact (proj2 (Hgtb j Hj)). }
  assert (HCB : pj_cbytesR segs (mrestrict (w_H W) (ms_mem ms)) out s).
  { split; [exact (PjGrammar.G1_4_bytes _ _ _ Hxbytes Hdec)|].
    unfold bytes_at in Hbytes.
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    destruct (Nat.lt_ge_cases j (length s)) as [Hjs|Hjs].
    - rewrite app_nth1 by exact Hjs. destruct (Hbytes j Hjs) as [HV Hb]. split; [|exact Hb].
      eapply (psb_val_mem_keep _ _ _ 1 _); [|exact HV]. intros x Hx. cbn in Hx. apply Hkm; lia.
    - assert (Ej : j = length s) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      split; [|lia]. replace (out + Z.of_nat (length s)) with w by lia. exact Hvw. }
  assert (HLED1 : LEDGER ly S Hp W (ms_mem ms) ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D)).
  { destruct HLED as (HG0 & Hnd & Hfa & Hperm).
    split; [|split; [exact Hnd | split; [|exact Hperm]]].
    - assert (Hst : forall a, Exists (in_zr a) PST ->
        mbyte segs (mrestrict (w_H W) (ms_mem ms)) a = mbyte segs (mrestrict (w_H W) mem) a).
      { intros a Ha. destruct (PST_ok a Ha) as [Hi _]. pose proof (@pa_segs_low _ _ PSB_PAImg a Hi) as Hal.
        apply Hkm; [lia | | lia].
        intros Hwa. apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HARc Hinb); [lia | exact Hi]. }
      destruct HG0 as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Gn).
      split; [|split; [|split; [|split; [|split; [|split; [split; [|exact G6r]|split; [split; [|exact G7r]|exact Gn]]]]]]];
        (eapply psb_val_mem_keep; [|eassumption]); intros x Hx; apply Hst; unfold prh_pst;
        repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
    - apply Forall_forall. intros [a kk] Hin.
      pose proof (proj1 (Forall_forall _ _) Hfa (a, kk) Hin) as (Hk0 & Hab' & Hhp & Ha16 & Hhv). cbn [fst snd] in *.
      split; [exact Hk0|]. split; [exact Hab'|]. split; [exact Hhp|]. split; [exact Ha16|].
      destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hab') as (_ & Ha4096 & Haceil & _ & _ & _).
      assert (Hrqa : kk + cf_head <= req_size (kk + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
      eapply (psb_val_mem_keep _ _ _ 8 _); [|exact Hhv]. intros x Hx. apply Hkm; [lia | | lia].
      destruct Hin as [Ea | Hin'].
      + injection Ea as <- <-. lia.
      + enough (x <> w) by lia. apply (Hsepw (a - cf_head) (kk + cf_head) x Hab'); [|lia].
        intros Ee. injection Ee as Ee1 _. cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hno Hnd0]. apply Hno.
        clear - Hin' Ee1. revert Hin'. induction (pi_Lam D) as [|[a0 k0] L IH]; intros Hin'; [destruct Hin'|].
        destruct Hin' as [Eh | Ht]; cbn [map fst];
          [injection Eh as Ea Ek; subst a0 k0; replace out with a by lia; constructor | constructor; exact (IH Ht)]. }
  assert (HPJ : pj_in_okR segs (mrestrict (w_H W) (ms_mem ms)) (pi_q D) (pi_text D) (pi_len D)
      (pi_p D + Z.of_nat Q + 2) (pi_d D) (pi_tb D)).
  { pose proof HIN as (_ & HVc8 & HVc16 & _ & _ & _ & _ & _ & _ & Hgtbc & _ & _).
    split; [replace (pi_p D + Z.of_nat Q + 2) with (r + 1) by lia; exact Hvq|].
    split; [eapply (psb_val_mem_keep _ _ _ 8 _); [|exact HVc8]; intros x Hx; apply Hkm; lia|].
    split; [eapply (psb_val_mem_keep _ _ _ 4 _); [|exact HVc16]; intros x Hx; apply Hkm; lia|].
    split; [intros x Hx; apply (apresent_writable segs); eapply apresent_grows; [exact HG|];
            apply Jpres; unfold PS_WSP, PS_WSTK; lia|].
    split; [exact Hq8|]. split; [exact Htext0|]. split; [exact Htl|]. split; [lia|].
    split; [exact Hlentb|]. split; [|split; [exact Hqtext | exact Hd32]].
    eapply (psb_garr8_keep _ _ _ _); [|exact Hgtbc]. intros x Hx. rewrite Hlentb in Hx.
    apply Hkm; [lia | | lia].
    (* the text lies apart from the new block *)
    destruct HHOME as [[(b & m & Hbm & Hbt & Htb) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & Hnb & Hbt & Htb)].
    - destruct HLED as (_ & Hnd & Hfa & _).
      pose proof (proj1 (Forall_forall _ _) Hfa (b, m) (or_intror Hbm)) as (Hm0 & Hab' & _ & _ & _).
      cbn [fst snd] in *.
      assert (Hrqb : m + cf_head <= req_size (m + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
      enough (x <> w) by lia. apply (Hsepw (b - cf_head) (m + cf_head) x Hab'); [|lia].
      intros Ee. injection Ee as Ee1 _. cbn [map fst] in Hnd. inversion Hnd as [|x0 l0 Hno Hnd0]. apply Hno.
      clear - Hbm Ee1. revert Hbm. induction (pi_Lam D) as [|[a0 k0] L IH]; intros Hbm; [destruct Hbm|].
      destruct Hbm as [Eh | Ht]; cbn [map fst];
        [injection Eh as Ea Ek; subst a0 k0; replace out with b by lia; constructor | constructor; exact (IH Ht)].
    - enough (x <> w) by lia. intros Exw. subst x. destruct (Hro w Hx) as (Hri & _ & _).
      apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HARc Hinb); [lia | exact (psb_ro_img w Hri)].
    - enough (x <> w) by lia. intros Exw. subst x. destruct (Hro w Hx) as (Hri & _ & _).
      apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HARc Hinb); [lia | exact (psb_ro_img w Hri)].
    - assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
      enough (x <> w) by lia. apply (Hsepw b m x Hbm); [|lia].
      intros Ee. injection Ee as Eb _. apply Hnb. rewrite HHp, Eb. left. reflexivity. }
  lazymatch type of HS1 with st_ok_pi _ _ ?E2 _ _ =>
    assert (HAE2 : env_agree 32 (Ereg (pi_regs D) (psb_cur regs)) E2)
      by (destruct HAE as [HA1 HA2]; split;
          [intros n Hn; rewrite !ew_ewset_other by lia; apply HA1; exact Hn | rewrite !ed_ewset; exact HA2]) end.
  (* ---- the return ---- *)
  prreg HS1 (10%bv : bv 5) R10. prreg HS1 (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS1 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. rewrite R1, E1, Hra.
  unfold PS_Gen.ps_postP.
  (* the success path stores no wild trace: the post at budget [] (within the cursor set's) *)
  eapply (YCbqGwild.fpostW_xb_of_kept (SK := SK) segs B PST ARx (YCbqGwild.wbudget CW 0) STK_parse_string (pi_e D) _
    (pi_regs D) _ _ _ _ _ _ _ [(pi_q D, pi_q D + 8)] [] ly S Hp W _ (ms_mem ms) _ k []).
  * exact Hstk0.
  * apply ps_wb_nil.
  * apply (ajournal_x_materialize segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg)). exact HJ.
  * apply (psb_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HKf). apply same_but_materialized_wvb_any.
  * intros a Ha. exact Ha.
  * exact (aregs_preserved_of_st_ok segs _ _ _ _ (pi_regs D) (psb_cur regs) HS1 HAE2 ltac:(vm_compute; reflexivity)).
  * (* ps_QP: the post body, and P at the written memory *)
    split; [|exact HMN].
    exists out. split; [rewrite R10; unfold w64; rewrite <- E50; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [exact HRL|]. split; [rewrite HTR; exact HBBal|].
    (* the hull use: the malloc's, which the cut's ps_rpos_mal carries (the success path makes no other call) *)
    split; [exact (proj1 HRP)|].
    unfold ps_QresK. rewrite HSCAN. right; right; right.
    split; [exact Hcnt|]. split; [exact Hout4096|]. split; [exact Hout16|].
    exists s, (rest_atR (pi_tb D) (pi_text D) (r + 1)). split; [exact Hdec|].
    split; [exact HHp|]. split; [exact Hab|]. split; [exact HVIS1|]. split; [exact HCB|].
    split; [exact HLED1|]. split; [exact HPJ|].
    (* the live requests and the position after the success arm's E = [HMal m] (ps_alloc's blocks and ps_rpos_mal) *)
    rewrite (ps_evs_ok _ Q _ HSCAN Hdec).
    exact (conj (ps_live_app (L := B_prog_listing) (PA := PSB_PAImg) B D ly S _ _ Hab) (proj2 HRP)).
Qed.
(* its stable statement (d19ced981f4), the P := (fun _ => True) instance *)
Theorem psb_retok_holds : forall CTX CW, psb_seg_retok B ARx SK CTX CW.
Proof.
intros CTX CW. apply (psb_seg_retok_of_True B ARx SK CTX CW).
apply psb_retok_holdsP. exact srr_inv_laws_True.
Qed.
End retok.

Section free.
(* the callee text this stretch calls (the internal file STRETCH-BRIEF.md): fuzz_free at image B's instances *)
Hypothesis HFREE : tfuzz_free_specX B ARx SK.
(* IMAGE FACTS of the shared text-across-a-call lemma lib/B/Prog/PSB_Src.v (a working branch 60cea7f5c19,
   BParseString's agreement), verbatim: the image's zero-shadow ranges are granule-aligned; its shadow is present *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : psb_img_shadow_vis ARx.

(* a frame chain from v whose next frame word is below the ceiling (the kit's prh_cur_low) is at most ONE record *)
Lemma psb_chain_one : forall ly (rd : reader) sp v ch,
  achain ly rd sp v ch -> YM05.alloc_ceiling <= v ->
  (forall w, rdword rd (v - 16) = Some w -> w < YM05.alloc_ceiling) ->
  ch = [] \/ exists w nfp, ch = [(v, w, nfp)] /\ rdword rd (v - 8) = Some w.
Proof.
intros ly rd sp v ch [(_ & ->) | (_ & _ & _ & H4 & _)] Hv Hlow; [left; reflexivity|].
destruct ch as [|[[fp ra] nfp] rest]; [left; reflexivity|].
cbn [fpchain] in H4. destruct H4 as (Efp & _ & Hra & Hnfp & _ & Hrest). subst fp.
pose proof (Hlow nfp Hnfp) as Hn.
assert (Hbad : bad_next v (ly_top ly) nfp = true)
  by (unfold bad_next; apply orb_true_iff; left; apply orb_true_iff; left; apply Z.leb_le; lia).
rewrite Hbad in Hrest. subst rest. right. exists ra, nfp. split; [reflexivity | exact Hra].
Qed.

(* the last element of a list removed again *)
Lemma psb_rm_last : forall (E b1 b2 : list (Z * Z)) x, b1 ++ x :: b2 = E ++ [x] -> ~ In x E -> b1 ++ b2 = E.
Proof.
intros E b1 b2 x Heq Hn. revert Heq. induction b2 as [|y b2' _] using rev_ind; intros Heq.
- apply app_inj_tail in Heq as [Heq _]. rewrite app_nil_r. exact Heq.
- rewrite app_comm_cons, app_assoc in Heq. apply app_inj_tail in Heq as [Heq _].
  exfalso. apply Hn. rewrite <- Heq. apply in_or_app. right. left. reflexivity.
Qed.

(* the kept relation at R from a callee's journal at R and at ANY budget WS (YCbqGcallW.cj_kept_of_journalR at WS = [],
   the same proof: cj_keptR reads no budget); fuzz_free's journal is at wle' segs RZ_cf *)
Lemma psb_kept_of_journal_wR : forall (R : world segs -> world segs -> Prop)
  STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR,
  ajournal_xwR (SK := SK) segs B PST ARx R STKf sp FPc lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  cj_keptR (SK := SK) segs B PST R STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2.
Proof.
intros R STKf sp FPc lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 WS OR HJ.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hrel.
pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_hi HJ) as F1. pose proof (ajxR_blk HJ) as F2.
pose proof (ajxR_img HJ) as F3. pose proof (ajxR_frm HJ) as F4. pose proof (ajxR_gone HJ) as Hgone.
pose proof (ajxR_extra HJ) as F5.
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hrel|]. split; [exact Hio|].
split; [rewrite Hfrs; reflexivity|].
split; [intros a Ha Hw _; exact (F1 a Ha Hw)|].
split; [intros p m i H1 H2 Hi Hf _; exact (F2 p m i H1 H2 Hi Hf)|].
split; [exact Hgone|].
split; [intros a Hi Hn He Hp Hs _; exact (F3 a Hi Hn He Hp Hs)|].
split; [intros cid pos a Hin Hr Hf _; exact (F4 cid pos a Hin Hr Hf)|].
intros a Hx He _. exact (F5 a Hx He).
Qed.

(* the 13 saved slots survive a stretch that keeps their bytes *)
Lemma psb_saved_keep : forall (D : ps_in) W mem W2 mem2,
  (forall x, PS_SP D + 40 <= x < PS_SP D + 144 -> mbyte segs (rdW W2 mem2) x = mbyte segs (rdW W mem) x) ->
  ps_saved D W mem -> ps_saved D W2 mem2.
Proof.
intros D W mem W2 mem2 HK (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
unfold PS_Gen.ps_saved. cbv zeta.
repeat match goal with |- _ /\ _ => split end;
  (eapply psb_val_mem_keep; [|eassumption]); intros x Hx; apply HK; lia.
Qed.

(* ---- STRETCH 3: a bad escape, from PSB_FREE: `mv a0, s2` (1248), `jal fuzz_free` (1252) by YCbqGwild.v's
   aj_call_xb_sp to the kit's tfuzz_free_specX, back at 1256 = PSB_RET0 with the block freed (Hp, the blocks and the ledger
   back to the entry's), so ps_at_ret0P P holds (ps_Qres's bad-escape arm) and the ret0 stretch finishes. The callee's
   chain from s0 = q is PS_Gen's ps_chain_call_offq (at most one record), its trace the closure's cursor conjunct
   with ps_cur_call_offq; the text survives by PSB_Src.v's psb_src_after_call.
   THE STRETCH, at any P with the runner and call laws, with NO open premise: fuzz_free's text (the kit's cut 7cdbb61b5fa0,
   PRH_FnAlloc.v blob 4d8aeba047e5, POST-IMPLICATION) takes no position; its live count `ccnt24 S <= L24 + DRV` at the
   call state (asked for p <> 0) is ps_pre's class-24 peak at the second state of the all-granted events
   (PS_Gen.ps_count24_free); its post transfers every position by HFr (n + cf_head), which extends the cut's malloc
   transfer (ps_alloc's ps_rpos_mal) to the bad-escape arm's [HMal ..; HFr ..]. P across the call is the TEXT's: its
   m-form post (fpostbm, fQmn) gives the memnorm keep from the call-time memory, and srr_inv_call turns it into P.
   fpre's last conjuncts: the callee's sp is the body's (below the entry sp, which has 64 bytes of stack above it), its
   ra the jal's return pc PSB_RET0, a listing slot below CEIL_MIN <= alloc_ceiling, and frm_zero the entry's (the same
   fx). The run 1248 -> 1252 is the invariant twin at P. ---- *)
Theorem psb_free_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P -> psb_seg_ret0PR B ARx SK CTX CW P (wle' segs YGcfRehidePost.RZ_cf) ->
  psb_seg_freeP B ARx SK CTX CW P.
Proof.
intros CTX CW P PLAW PCALL HR0 D ly S Hp W regs mem md out Q HPRE HAT.
(* the run 1248 -> 1252 is at wle, into PS_Gen's hand-off form ps_finP; the call crosses the free (ps_finP_hand), and
   from its post state on the journal and the kept relation are at wle' segs RZ_cf *)
apply ps_finP_SRr'.
destruct HAT as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & HGT & HIN & HROD & HSCAN & HDEC & Hsp & H18 & H8).
pose proof HPRE as ((HPX & _ & H64 & _ & HFRM) & HCLOS & _ & _ & _ & Hgap & _ & _ & _ & _ & _ & _ & _ & HWIN & Hqlo & Hqhi & _).
pose proof HPX as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as CH0.
pose proof (ajx_ar HJ) as HARc. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_hi HJ) as JF1.
pose proof (ajx_blk HJ) as JF2. pose proof (ajx_img HJ) as JF3. pose proof (ajx_frm HJ) as JF4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Jpres. pose proof (ajx_stk HJ) as Jstk.
pose proof (ajx_extra HJ) as JX. pose proof (ajx_qt HJ) as JQT.
pose proof HAL as (Hcnt & Hout4096 & Hout16 & HHp & Hab & HLED & HVIS & HRL & HRP & HBBal).
(* the live count at the call state: ps_pre's class-24 peak, at the all-granted events' second state (the bad escape) *)
pose proof (ps_count24_free (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D Q ly S
  (out - cf_head) HPRE HSCAN HDEC Hab) as Hcnt24.
pose proof HIN as (HV0 & HV8 & HV16 & HRW & Hq8 & Htext0 & Htl & Hptext & Hlentb & Hgtb & Hqtext & Hd32).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof psb_frame as HFR. pose proof HFR as HFR'. unfold PS_Gen.PS_FRAME in HFR'.
(* DERIVED (vm_compute on the generated PRH_ImgB value): parse_string's budget covers its frame and fuzz_free's *)
assert (HSTKff : STK_fuzz_free + 144 <= STK_parse_string) by (vm_compute; discriminate).
assert (HSTKff0 : 0 <= STK_fuzz_free) by (vm_compute; discriminate).
assert (HB4096 : 4096 <= BASE) by (vm_compute; discriminate).
pose proof (@pa_B_ok _ _ PSB_PAImg) as HBok.
(* DERIVED: the return site PSB_RET0 is a code offset, even, inside the listing span *)
assert (Hko : 0 <= PSB_OFF + PSB_RET0 < 2 ^ 40 /\ (PSB_OFF + PSB_RET0) mod 2 = 0).
{ assert (Hb : ((0 <=? PSB_OFF + PSB_RET0) && (PSB_OFF + PSB_RET0 <? 2 ^ 40) && ((PSB_OFF + PSB_RET0) mod 2 =? 0))%bool
    = true) by (vm_compute; reflexivity).
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia. }
assert (Rsp : 2 ^ 46 <= spZ (pi_regs D) <= 2 ^ 47) by lia.
assert (Hinb : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
  by (rewrite Hab; apply in_or_app; right; left; reflexivity).
pose proof (psb_newblk D ly S Hp W mem md out Q HAL HARc) as Hnew.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & Hbpw).
assert (Hrq2 : Z.of_nat Q + 1 + cf_head <= req_size (Z.of_nat Q + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); lia).
assert (Eout0 : (out =? 0) = false) by (apply Z.eqb_neq; lia).
(* the new block's address is no entry harness block's (the ledger's NoDup) *)
assert (HoutL : forall b m, In (b, m) (pi_Lam D) -> b <> out).
{ intros b m Hbm Eb. pose proof HLED as (_ & Hnd & _). cbn [map fst] in Hnd.
  inversion Hnd as [|x0 l0 Hno Hnd0]. apply Hno.
  clear - Hbm Eb. revert Hbm. induction (pi_Lam D) as [|[a0 k0] L IH]; intros Hbm; [destruct Hbm|].
  destruct Hbm as [Eh | Ht]; cbn [map fst];
    [injection Eh as Ea0 Ek0; subst a0 k0; rewrite <- Eb; constructor | constructor; exact (IH Ht)]. }
assert (Hnotin : ~ In (out - cf_head) (pi_Hp D)).
{ intros Hin. pose proof HLED as (_ & _ & _ & Hperm). rewrite HHp in Hperm. cbn [map fst] in Hperm.
  apply Permutation_cons_inv in Hperm.
  assert (Hin2 : In (out - cf_head) (map (fun ak => fst ak - cf_head) (pi_Lam D)))
    by (eapply Permutation_in; [exact Hperm | exact Hin]).
  apply in_map_iff in Hin2 as ([a kk] & Ea & Hak). cbn [fst] in Ea. apply (HoutL a kk Hak). lia. }
(* a byte of another live block is no byte of the new block *)
assert (Hsepn : forall b m x, In (b, m) (ablocks B ly S) -> (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head) ->
  b <= x < b + req_size m -> ~ (out - cf_head <= x < out - cf_head + req_size (Z.of_nat Q + 1 + cf_head))).
{ intros b m x Hbm Hne Hx Hxo.
  pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md b m _ _ HARc Hbm Hinb Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the text lies apart from the freed block (its home) *)
assert (HFPtext : forall a, inFP (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)]) a ->
  ~ (pi_text D <= a < pi_text D + Z.of_nat (length (pi_tb D)))).
{ intros a Ha Htx. apply inFP_ablocks_fp_inv in Ha as (p & n & [Epn | []] & Ha). injection Epn as <- <-.
  rewrite Hlentb in Htx.
  destruct HHOME as [[(b & m & Hbm & Hbt & Htb) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & Hnb & Hbt & Htb)].
  - pose proof HLED as (_ & _ & Hfa & _).
    pose proof (proj1 (Forall_forall _ _) Hfa (b, m) (or_intror Hbm)) as (Hm0 & Hab' & _).
    cbn [fst snd] in Hm0, Hab'.
    assert (Hrqb : m + cf_head <= req_size (m + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
    apply (Hsepn (b - cf_head) (m + cf_head) a Hab'); [| lia | exact Ha].
    intros Ee. injection Ee as Ee1 _. apply (HoutL b m Hbm). lia.
  - destruct (Hro a Htx) as (Hri & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HARc Hinb); [lia | exact (psb_ro_img a Hri)].
  - destruct (Hro a Htx) as (Hri & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HARc Hinb); [lia | exact (psb_ro_img a Hri)].
  - assert (Hrqb : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    apply (Hsepn b m a Hbm); [| lia | exact Ha].
    intros Ee. injection Ee as Eb _. apply Hnb. rewrite HHp, Eb. left. reflexivity. }
(* the freed block opens no sink (it lies above page 0) *)
assert (HSNK : ~ YI16.sink_open_fp (ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)])).
{ intros (rr & Hrr & H0). unfold ablocks_fp in Hrr. cbn [map] in Hrr. destruct Hrr as [<- | []].
  cbn [fst snd] in H0. lia. }
(* ---- the symbolic state at 1248: the epilogue's register atoms, no region ---- *)
assert (Esp2 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 2) = spZ (pi_regs D))
  by (rewrite (psb_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (E50 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 50) = out)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H18; unfold w64; apply unsigned_lit_small; lia).
assert (E40 : bv_unsigned (ew (EB (Ereg (pi_regs D) (psb_cur regs))) 40) = pi_q D)
  by (rewrite psb_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth psb_cur map all_regs];
      rewrite H8; unfold w64; apply unsigned_lit_small; lia).
assert (E3 : ew (EB (Ereg (pi_regs D) (psb_cur regs))) 3 = getr (pi_regs D) 3) by exact (psb_ew_lo _ _ 3 3 eq_refl).
assert (E4 : ew (EB (Ereg (pi_regs D) (psb_cur regs))) 4 = getr (pi_regs D) 4) by exact (psb_ew_lo _ _ 4 4 eq_refl).
assert (HEI : img_env VAL A_LIM (EB (Ereg (pi_regs D) (psb_cur regs)))) by apply Eimg_env.
assert (HS : st_ok_pi segs VAL (EB (Ereg (pi_regs D) (psb_cur regs)))
  (mkSS (PSB_OFF + PSB_FREE) psb_sr_epi [] None psb_facts_epi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSB_FREE))) mem (seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (psb_regs_ok_epi D regs Hsp HGT).
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; [exact I | exact I]]. cbn [psb_facts_epi f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Esp2. change (2 ^ 4) with 16. lia. }
assert (SHOK : sh_ok segs PSB_Bx_epi [] (EB (Ereg (pi_regs D) (psb_cur regs))) (mrestrict (w_H W) mem))
  by (unfold sh_ok; apply Forall_nil).
remember (EB (Ereg (pi_regs D) (psb_cur regs))) as E eqn:HE.
pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS P PLAW).
unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_FREE) with (BASE + (PSB_OFF + PSB_FREE)) by lia.
(* `mv a0, s2`; stop at `jal fuzz_free` *)
paj_run_tok_x_inv RUN HS HJ SHOK HMN PSB_Bspan; [cbn [ss_mem]; apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m1 |} _ => remember m1 as md1 eqn:Emd1 end.
assert (Hsbm : same_but_materialized md md1) by (rewrite Emd1; apply same_but_materialized_wvb_any).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msn) =>
  assert (Emem : ms_mem msn = mem)
    by (apply functional_extensionality; intros x; apply HF; intros (rg & Hin & _); cbn [ss_mem In] in Hin;
        exact Hin) end.
(* P at the call-time memory (the twin's HMN), at the cut's memory *)
rewrite Emem in HMN.
pose proof (ajx_ar HJ) as HARc1.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
assert (Ha0 : getr (ms_regs ms) 10 = w64 out) by (rewrite R10; unfold w64; rewrite <- E50; symmetry; apply Z_to_bv_bv_unsigned).
assert (HspT : spZ (ms_regs ms) = PS_WSP D + (-144 - pi_e D)).
{ unfold spZ at 1. rewrite R2, Esp2. rewrite unsigned_lit_small by lia. unfold PS_WSP. lia. }
assert (Hs0 : s0Z (ms_regs ms) = pi_q D) by (unfold s0Z; rewrite R8; exact E40).
assert (Hgp1 : getr (ms_regs ms) 3 = getr (pi_regs D) 3) by (rewrite R3; exact E3).
assert (Htp1 : getr (ms_regs ms) 4 = getr (pi_regs D) 4) by (rewrite R4; exact E4).
assert (Hraw : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (PSB_OFF + PSB_RET0))) by (rewrite R1; f_equal; vm_compute; reflexivity).
assert (HROD1 : arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) (ms_mem ms))) by (rewrite Emem; exact HROD).
assert (H641 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite HspT, Ehi; unfold PS_WSP; lia).
(* the call's ra, the return site PSB_RET0, is below the ceiling: DERIVED (vm_compute on the closed slot value) below
   CEIL_MIN, YM05's least ceiling *)
assert (Hrac : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ assert (Hlt : BASE + (PSB_OFF + PSB_RET0) < CEIL_MIN) by (vm_compute; reflexivity).
  pose proof YM05.alloc_ceiling_value as (Hcl & _).
  unfold raZ. rewrite Hraw, unsigned_lit_small by lia. lia. }
assert (HLED1 : LEDGER ly S Hp W (ms_mem ms) ((out, Z.of_nat Q + 1) :: pi_Lam D)
  (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
  (pi_most D) (pi_own D))
  by (rewrite Emem; exact HLED).
(* ---- the callee's chain from s0 = q and its trace: the call view is the entry's off the caller word ---- *)
assert (Hview : forall a, spZ (pi_regs D) <= a < 2 ^ 64 -> ~ (pi_q D <= a < pi_q D + 8) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H (pi_W D)) (pi_mem D) a).
{ intros a Ha Hqa. rewrite Emem. pose proof HK as (_ & _ & _ & _ & _ & K1 & _). apply K1; [lia | lia |].
  intros Hf. apply inFP_cons in Hf as [Hf|Hf]; [lia | exact (inFP_nil a Hf)]. }
assert (Hg1 : spZ (pi_regs D) + 16 <= prh_s0 F_parse_string (pi_q D)) by (rewrite psb_s0_q; exact Hgap).
assert (Hs0q : prh_s0 F_parse_string (pi_q D) <= pi_q D) by (rewrite psb_s0_q; lia).
assert (Hs064 : prh_s0 F_parse_string (pi_q D) <= 2 ^ 64) by (rewrite psb_s0_q; lia).
destruct (ps_chain_call_offq (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D
  (aview segs (w_H W) (ms_mem ms)) HPRE Hg1 Hs0q ltac:(lia) Hview) as (ch1 & Hch1).
pose proof (ps_cur_call_offq (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D
  (aview segs (w_H W) (ms_mem ms)) HPRE Hg1 Hs064 Hs0q Hview) as (Hcur & Hlow).
rewrite psb_s0_q in Hch1, Hcur, Hlow.
assert (Hch2 : achain ly (aview segs (w_H W) (ms_mem ms)) (PS_WSP D + (-144 - pi_e D)) (s0Z (ms_regs ms)) ch1).
{ apply (achain_ly_top (pi_ly D) ly _ _ _ _ Etop). rewrite Hs0.
  replace (PS_WSP D + (-144 - pi_e D)) with (spZ (pi_regs D) - pi_frame F_parse_string) by (unfold PS_WSP; lia).
  exact Hch1. }
(* THE CALL TRACE (the batch kit: prh_univ_closure's clauses 2 / 4a give FIXED traces, 4b a wild one in the universe; the
   text's prh_cw_ok puts the cursor trace in CW unless its word is a pj_parse code word): it is FIXED (the literal site
   with an empty chain, or the one-record chain at a code word) or a cursor trace IN CW *)
assert (HTRS : In (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) (u_fix (as_universe B)) \/
  (In (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) CW /\
   inU (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1))).
{ assert (Hf0 : frame0_ok ly (ms_regs ms) = true)
    by (unfold frame0_ok; apply Z.ltb_lt; rewrite HspT, Etop; unfold PS_WSP; lia).
  assert (Hrv : raZ (ms_regs ms) = BASE + (PSB_OFF + PSB_RET0))
    by (unfold raZ; rewrite Hraw; apply unsigned_lit_small; lia).
  assert (HRS : In (BASE + (PSB_OFF + PSB_RET0)) (pi_ret_sites F_parse_string RT_fuzz_free))
    by (vm_compute; left; reflexivity).
  assert (Hsite : In (BASE + (PSB_OFF + PSB_RET0)) (prh_free_sites F_parse_string))
    by (exact (in_or_app _ _ _ (or_intror HRS))).
  destruct (psb_chain_one ly _ _ _ ch1 Hch2 ltac:(rewrite Hs0; lia) ltac:(rewrite Hs0; exact Hlow))
    as [-> | (w & nfp & -> & Hw)];
    unfold call_trace; rewrite Hf0, Hrv.
  - left. exact (prh_univ_closure_lit (PI := PSB_PrhImg) B CTX
      F_parse_string RT_fuzz_free _ HCLOS HRS).
  - rewrite Hs0 in Hw.
    destruct (Hcur _ w Hsite Hw) as [Hcw | Hcr].
    + right. split; [exact Hcw|].
      exact (prh_univ_closure_wild (PI := PSB_PrhImg) B CTX
        F_parse_string _ w HCLOS (or_introl eq_refl) Hsite).
    + left. exact (prh_univ_closure_cur (PI := PSB_PrhImg) B CTX
        F_parse_string _ w HCLOS (or_introl eq_refl) Hsite Hcr). }
(* the wild room at the call's state: the entry's (the text's premise, ps_pre's eighth conjunct), kept by the cut's
   journal at budget [] (YCbqGwild.ajournal_xw_room) *)
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & HWR0 & _).
assert (HWR : YCbqGwild.wild_room (as_universe B) CW 0 (st_depot S))
  by exact (YCbqGwild.ajournal_xw_room (SK := SK) segs B PST ARx _ _ _ _ _ (pi_Hp D) _ _ _ _ _ _ _ _ _ _ _ [] CW 0
              HJ HWR0 (le_n 0)).
(* THE ADMISSION of the free text (the batch kit PRH_FnAlloc 4d8aeba047e5 :336): a fixed trace by admits_ct_fix; a CW
   trace by the wild room, with the depot's NoDup from AR_laws_x FIELD 25 alx_depot_nodup (a Theorem Labs lane's
   a working branch b4ca247aad5d, YCbqG.v 219748197d6b; the former named premise DEPOT is GONE) *)
assert (Hadm : admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) S).
{ destruct HTRS as [Hfix | (Hcw & HinU)].
  - exact (admits_ct_fix _ _ _ _ _ _ Hfix).
  - exact (YCbqGwild.wild_room_admits (as_universe B) CW 0 S _ (alx_depot_nodup segs B ARx LAWS ly S Hp W mem md HARc)
      HWR HinU (or_introl Hcw)). }
(* ---- THE CALL: the engine's rule over R at wle' segs RZ_cf (YCbqGwild.aj_call_xb_spR), the cut's journal, at wle,
   lifted once here ---- *)
apply ps_finP_hand. unfold SRr'.
eapply (SRrG_bind segs (wle' segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xb_spR (SK := SK) segs B PST ARx LAWS (@pa_segs_low _ _ PSB_PAImg)
    (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf) W _ _ ms
    (PS_WSTK D) (PS_WSP D)
    [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp _ k [] STK_fuzz_free
    (if out =? 0 then [] else ablocks_fp [(out - cf_head, Z.of_nat Q + 1 + cf_head)]) (-144 - pi_e D)
    (Z_to_bv 64 (BASE + (PSB_OFF + PSB_RET0))) ch1 _ _ HS eq_refl
    (ajournal_xwR_mono (SK := SK) segs B PST ARx (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
       (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)).
  - exact HspT.
  - lia.
  - lia.
  - exact HSTKff0.
  - unfold PS_WSTK. lia.
  - rewrite Hgp1. exact Hgp0.
  - rewrite Htp1. exact Htp0.
  - exact Hraw.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PSB_PAImg)); [exact (proj1 Hko) | exact (proj2 Hko)].
  - rewrite unsigned_lit_small by lia. lia.
  - exact Hch2.
  - intros HPRE1. cbn [ss_pc setpc].
    exact (HFREE (pi_most D) (pi_own D)
      ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 out (Z.of_nat Q + 1) ((out, Z.of_nat Q + 1) :: pi_Lam D)
      (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
      (conj HPRE1 (conj HROD1 (conj H641 (conj Hrac HFRM)))) (fun _ => HRL) (fun _ => Hcnt24)
      (* the hull budget for no event: the text's less the malloc's use (PS_Gen.ps_hull_free) *)
      (fun _ => ps_hull_free (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx CTX CW D Q S HPRE HRP)
      Hadm Ha0
      (or_intror (or_introl eq_refl)) HLED1).
  - intros a Ha. rewrite Eout0 in Ha. right; left.
    apply inFP_ablocks_fp_inv in Ha as (p & n & [Epn | []] & Ha). injection Epn as <- <-.
    exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb|]. split; [exact Hnew | exact Ha]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HB1 & HJ2 & HJc & HP2 & HQ2 & HKMN).
(* P across the call: the text's memnorm keep (fQmn) from the call-time memory, by srr_inv_call *)
rewrite Emem in HKMN.
pose proof (PCALL mem mem2 HKMN HMN) as HMN2.
(* fuzz_free's post read BY NAME through the kit's projection layer (PRH_FnAlloc.v tffP_R_of and the fields of tffP_R,
   the arm records tffP_R1 / tffP_R2); regs2 and md2 are the arguments of the post its body does not mention *)
apply tffP_R_of with (regs' := regs2) (md' := md2) in HQ2.
pose proof (tffP_room HQ2) as HRL2. pose proof (tffP_hull HQ2) as HHU2. pose proof (tffP_pos_free HQ2) as HPF.
destruct (tffP_arm HQ2) as [HA1 | HA2]; [pose proof (tffP1_null (tffP_R1_of HA1)); lia|].
destruct (tffP_R2_of HA2) as (l1 & l2 & HR2).
pose proof (tffP2_hp HR2) as EHp2. destruct (tffP2_ablocks HR2) as (b1 & b2 & Eab1 & Eab2).
pose proof (tffP2_lam HR2) as ELam. pose proof (tffP2_ledger HR2) as HLED2. clear HQ2 HA2 HR2.
pose proof (HRL2 (proj1 (Z.eqb_neq out 0) Eout0)) as HRL2'.
(* the position after the call (POST-IMPLICATION): the cut's malloc transfer (ps_alloc's ps_rpos_mal,
   E = [HMal m]) followed by fuzz_free's own (E = [HFr m]) is the bad-escape arm's [HMal m; HFr m], m = Q + 1 + cf_head;
   the free uses no hull (its post's hull_used S S2 []), so the malloc's use is the use since the entry *)
assert (HRPpost : ps_rpos D [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)] S2).
{ split.
  { pose proof (PresetHullBudget.hull_used_app (pi_S D) S S2 _ [] (proj1 HRP) HHU2) as HU.
    rewrite app_nil_r in HU. exact HU. }
  intros sm x0 os i H0 hist Hpos Hrun.
  change [PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head); PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)]
    with ([PresetReqAt.HMal (Z.of_nat Q + 1 + cf_head)] ++ [PresetReqAt.HFr (Z.of_nat Q + 1 + cf_head)]) in Hrun.
  apply PRH_Base.prh_run_at_app_iff in Hrun as [Hr1 Hr2].
  destruct (proj2 HRP sm x0 os i H0 hist Hpos Hr1) as (hist1 & Hpos1).
  destruct (HPF (proj1 (Z.eqb_neq out 0) Eout0) sm x0 os _ H0 hist1 Hpos1 Hr2) as (hist2 & Hpos2).
  exists hist2. cbn [length] in Hpos2 |- *. replace (i + 2)%nat with (i + 1 + 1)%nat by lia. exact Hpos2. }
rewrite Eout0 in HJc.
(* ---- back at 1256: the block freed, the entry's blocks, heads and ledger ---- *)
assert (Eab2e : ablocks B ly2 S2 = ablocks B (pi_ly D) (pi_S D)).
{ rewrite Eab2. apply (psb_rm_last _ b1 b2 (out - cf_head, Z.of_nat Q + 1 + cf_head)); [|exact Hnew].
  rewrite <- Eab1. exact Hab. }
assert (EHp2e : Hp2 = pi_Hp D).
{ rewrite EHp2, HHp. cbn [remove]. destruct (Z.eq_dec (out - cf_head) (out - cf_head)) as [_|Hc]; [|contradiction].
  apply notin_remove. exact Hnotin. }
clear EHp2. subst Hp2.
assert (EL12 : l1 ++ l2 = pi_Lam D).
{ destruct l1 as [|y l1'].
  - apply (f_equal (@tl _)) in ELam. cbn [tl app] in ELam |- *. symmetry. exact ELam.
  - exfalso. apply (f_equal (@tl _)) in ELam. cbn [tl app] in ELam.
    apply (HoutL out (Z.of_nat Q + 1)); [|reflexivity]. rewrite ELam. apply in_or_app. right. left. reflexivity. }
rewrite EL12 in HLED2.
pose proof HLED2 as (_ & _ & Hfa2 & Hperm2).
pose proof HLED as (_ & _ & Hfa1 & _).
assert (HL1 : forall b m, In (b, m) (pi_Lam D) -> In (b - cf_head, m + cf_head) (ablocks B ly S)).
{ intros b m Hbm. destruct (proj1 (Forall_forall _ _) Hfa1 (b, m) (or_intror Hbm)) as (_ & H2 & _). exact H2. }
assert (HL2 : forall b m, In (b, m) (pi_Lam D) ->
  0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S2) /\ In (b - cf_head) (pi_Hp D)).
{ intros b m Hbm. destruct (proj1 (Forall_forall _ _) Hfa2 (b, m) Hbm) as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [exact H2 | exact H3]. }
assert (HHp2 : forall h, In h (pi_Hp D) -> exists kk, 0 <= kk /\ In (h, kk) (ablocks B ly2 S2)).
{ intros h Hh.
  assert (Hh2 : In h (map (fun ak => fst ak - cf_head) (pi_Lam D))) by (eapply Permutation_in; [exact Hperm2 | exact Hh]).
  apply in_map_iff in Hh2 as ([a kk] & Ea & Hak). cbn [fst] in Ea.
  destruct (HL2 a kk Hak) as (Hk0 & Hab2 & _). exists (kk + cf_head). split; [lia|]. rewrite <- Ea. exact Hab2. }
assert (HNB : forall p n, In (p, n) (ablocks B ly S) -> ~ In p Hp -> In (p, n) (ablocks B ly2 S2) /\ ~ In p (pi_Hp D)).
{ intros p n Hpn Hnh. rewrite Eab2e. split.
  - rewrite Hab in Hpn. apply in_app_or in Hpn as [Hpn | [Epn | []]]; [exact Hpn|].
    exfalso. apply Hnh. injection Epn as Ep _. rewrite HHp. left. exact Ep.
  - intros Hp'. apply Hnh. rewrite HHp. right. exact Hp'. }
(* the text across the call (PSB_Src.v) *)
assert (HHOMEc : prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (Z.of_nat (length (pi_tb D))))
  by (rewrite Hlentb; exact HHOME).
assert (HSRCc : src_rd W (ms_mem ms) (pi_text D) (pi_tb D)) by (rewrite Emem; exact HSRC).
destruct (psb_src_after_call_wR B ARx SK LAWS ZSA IMGV (wle' segs YGcfRehidePost.RZ_cf) STK_fuzz_free _ _ ly S Hp W
  (ms_mem ms) _ ly2 S2 (pi_Hp D) W2 mem2 md2 k1 WS1 (pi_Lam D) (pi_text D) (pi_tb D) HJc HSRCc HHOMEc HFPtext HSNK HNB
  HL1 HL2 HHp2) as [HSRC2 HHOME2].
rewrite Hlentb in HHOME2.
(* the callee's journal keeps the caller's stack above its own window: the saved slots and the cursor struct *)
pose proof (ajxR_hi HJc) as KF1.
assert (HSV2 : ps_saved D W2 mem2).
{ apply (psb_saved_keep D W mem W2 mem2); [|exact HSV].
  intros x Hx. unfold PS_Gen.PS_SP in Hx. rewrite HFR in Hx.
  apply (mbyte_of_aview segs). rewrite <- Emem. apply KF1; unfold PS_WSP; lia. }
(* the kept relation from the entry, through the call, at wle' (the cut's, at wle, lifted; the callee's at wle') *)
assert (HKpost : cj_keptR (SK := SK) segs B PST (wle' segs YGcfRehidePost.RZ_cf) STK_parse_string (spZ (pi_regs D))
    [(pi_q D, pi_q D + 8)] [] (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly2 S2 W2 mem2 md2).
{ assert (HKc : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
      (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W (ms_mem ms) md1)
    by (rewrite Emem; exact (psb_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK Hsbm)).
  pose proof (psb_kept_of_journal_wR (wle' segs YGcfRehidePost.RZ_cf) _ _ _ ly S Hp W (ms_mem ms) md1 ly2 S2 (pi_Hp D)
    W2 mem2 md2 k1 WS1 [(pi_q D, pi_q D + 8)] HJc) as HKcal.
  eapply (cj_kept_transR (SK := SK) segs B PST ARx LAWS (wle' segs YGcfRehidePost.RZ_cf)
      (wle'_trans segs YGcfRehidePost.RZ_cf)) with (FP1 := []) (Hpc := pi_Hp D) (Hp2 := Hp);
    [eapply ps_keptR_mono with (R1 := @wle segs); [exact (wle_wle' segs YGcfRehidePost.RZ_cf) | exact HKc]
    | exact HKcal | exact HAR0 | exact HARc1 | unfold PS_WSP; lia | unfold PS_WSP; lia | |].
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros a Ha. right; left. apply inFP_ablocks_fp_inv in Ha as (p & n & [Epn | []] & Ha). injection Epn as <- <-.
    exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hinb|]. split; [exact Hnew | exact Ha]. }
assert (HPJ2 : pj_in_okR segs (rdW W2 mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D)).
{ assert (Kq : forall x, pi_q D <= x < pi_q D + 24 -> mbyte segs (rdW W2 mem2) x = mbyte segs (rdW W mem) x).
  { intros x Hx. apply (mbyte_of_aview segs). rewrite <- Emem. apply KF1; unfold PS_WSP; lia. }
  pose proof (ajxR_pres HJ2) as Jpres2.
  split; [eapply (psb_val_mem_keep _ _ _ 8 _); [|exact HV0]; intros x Hx; apply Kq; lia|].
  split; [eapply (psb_val_mem_keep _ _ _ 8 _); [|exact HV8]; intros x Hx; apply Kq; lia|].
  split; [eapply (psb_val_mem_keep _ _ _ 4 _); [|exact HV16]; intros x Hx; apply Kq; lia|].
  split; [intros x Hx; apply (apresent_writable segs); apply Jpres2; unfold PS_WSP, PS_WSTK; lia|].
  split; [exact Hq8|]. split; [exact Htext0|]. split; [exact Htl|]. split; [exact Hptext|].
  split; [exact Hlentb|]. split; [exact (proj1 HSRC2)|]. split; [exact Hqtext | exact Hd32]. }
assert (HBB : blocks_bytes S2 <= blocks_bytes (pi_S D) + PRH_Charge.prh_held (PRH_Charge.prhPs_gtrace (ps_x D))).
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B (pi_ly D) (pi_S D)), Eab2e.
  unfold PRH_Charge.prh_held, PRH_Charge.prhPs_gtrace, PjGrammar.jr_string. rewrite HSCAN, HDEC.
  cbn [PjGrammar.jbind PjGrammar.jalloc PjGrammar.take PjGrammar.jret PjGrammar.jfree PjGrammar.jrefuse
       fst snd app PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]. lia. }
assert (P2 : getr regs2 2%bv = getr (ms_regs ms) 2%bv).
{ pose proof (HP2 2 ltac:(unfold acallee_saved; lia)) as H.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (P3 : getr regs2 3%bv = getr (ms_regs ms) 3%bv).
{ pose proof (HP2 3 ltac:(unfold acallee_saved; lia)) as H.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
assert (P4 : getr regs2 4%bv = getr (ms_regs ms) 4%bv).
{ pose proof (HP2 4 ltac:(unfold acallee_saved; lia)) as H.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in H by (apply bv_eq; reflexivity). exact H. }
(* THE BUDGET at the NULL return (the text's post is at wbudget CW 0): the free's budget WS1 holds only its own trace
   (wbudget [ct] 0); a FIXED trace adds no wild trace, so the journal goes back to budget [] (ajx_budgetR,
   ajournal_xw_fix1R); a CW trace is within CW (wfresh_incl) *)
pose proof (YCbqGwild.wfresh_zero_incl _ _ (proj1 (Nat.le_0_r _) HB1)) as Hinc1.
assert (HBW : exists WS, YCbqGwild.wbudget CW 0 WS /\
  ajournal_xwR (SK := SK) segs B PST ARx (wle' segs YGcfRehidePost.RZ_cf) (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S2 (pi_Hp D) W2 mem2 md2 (k + k1) WS).
{ destruct HTRS as [Hfix | (Hcw & _)].
  - exists []. split; [apply ps_wb_nil|].
    refine (ajournal_xw_fix1R (WS := []) (tr := call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1) Hfix _).
    exact (ajx_budgetR ([] ++ [call_trace ly (pc_free_ra0 (as_code B)) (ms_regs ms) ch1]) HJ2
             (wild_incl_mono _ _ _ _ Hinc1 (ajxR_wild HJ2))).
  - exists WS1. split; [|exact HJ2].
    unfold YCbqGwild.wbudget. rewrite (YCbqGwild.wfresh_incl CW WS1); [lia|].
    intros t Ht. destruct (Hinc1 t Ht) as [<- | []]. exact Hcw. }
destruct HBW as (WSr & HBWr & HJW).
(* ---- the NULL return's cut at wle' (the bad-escape arm), then the ret0 stretch over wle' ---- *)
assert (HAT0 : ps_at_ret0PR P (wle' segs YGcfRehidePost.RZ_cf) CW D ly2 S2 (pi_Hp D) W2 regs2 mem2 md2).
{ split; [exists (k + k1), WSr; split; [exact HBWr|]; split; [exact HJW|]; split; [exact HKpost|];
          split; [exact HSV2|]; split; [exact HSRC2|]; split; [exact HHOME2 | exact HMN2]|].
  split; [split; [rewrite P3; exact Hgp1 | rewrite P4; exact Htp1]|].
  split; [rewrite P2, R2, Esp2; unfold w64, PS_Gen.PS_SP; rewrite HFR; f_equal; lia|].
  split; [exact HRL2'|]. split; [exact HBB|].
  unfold ps_Qres. rewrite HSCAN. right; right; left.
  split; [exact Hcnt|]. split; [reflexivity|]. split; [exact HDEC|]. split; [reflexivity|].
  split; [exact Eab2e|]. split; [exact HLED2|]. split; [exact HPJ2|].
  (* THE EXACT ADVANCE, the malloc's event and the free's (the bad-escape arm's E) *)
  exact HRPpost. }
pose proof (HR0 D ly2 S2 (pi_Hp D) W2 regs2 mem2 md2 HPRE HAT0) as HG0.
unfold cfg_at, psb_pc, w64 in HG0.
replace (BASE + PSB_OFF + PSB_RET0) with (BASE + (PSB_OFF + PSB_RET0)) in HG0 by lia.
exact HG0.
Qed.
(* its stable statement, the P := (fun _ => True) instance (srr_inv_laws_True, srr_inv_call_True), with the NULL
   return after the free over wle' segs RZ_cf *)
Theorem psb_free_holds : forall CTX CW, psb_seg_ret0R B ARx SK CTX CW (wle' segs YGcfRehidePost.RZ_cf) ->
  psb_seg_free B ARx SK CTX CW.
Proof.
intros CTX CW HR0. apply (psb_seg_free_of_True B ARx SK CTX CW).
apply psb_free_holdsP; [exact srr_inv_laws_True | exact srr_inv_call_True |].
exact (proj2 (psb_seg_ret0R_of_True B ARx SK CTX CW (wle' segs YGcfRehidePost.RZ_cf)) HR0).
Qed.
End free.

End pst.
