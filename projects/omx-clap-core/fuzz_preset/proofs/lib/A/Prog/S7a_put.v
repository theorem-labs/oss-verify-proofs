(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* fuzz_preset image A' (the #102 asan pin 1be0f53d), slice S7a: the program walk of put (A' 0x87094, 129 instructions)
   over the ONE image-A program listing (lib/A/Listing_prog.v, the A' listing v3), generic in the image facts (Context
   PAImg) and in the allocator relation ARx (LAWS : AR_laws_x), concluding the kit's text tput_specX (put_holds). THIS
   VERSION is on the kit's CUT 7cdbb61b5fa0 (merged forward into the batch prep on the batch kit's tip e45217a4c7ba, whose texts it was
   re-fitted to; the cut's PRH_FnWriter / PRH_FnAlloc are the batch kit's bytes): every file but the lane's is the cut's
   (CfParamsPreset b60d0f63c926). The texts it meets: PRH_FnWriter's tput_specX (the run event as an entry premise,
   the consumer window prh_cons_from, the live room per event prh_live_evs, the per-arm position post with f' = 1's
   history existential, the post prhWriter_ret_ok under prh_granted: DEAD-PUT); PRH_FnAlloc's tfuzz_realloc_specX
   (the position as a post-implication of the call's own events, THE OUTCOME at a consumer allocation: res <> 0, the
   live premise guarded by cnt <> fail); PRH_Base's ledger with the #102 cells most / own. Relocated from the old-pin
   donor c2f1ac7094cb by alreloc c4338d099cfb8025 (re-run byte-identical on
   0474699fc83547e0).
   rule 24: proves function put. No kit/ARx proof of put exists (WalkS7a's reuse search, the internal file r24v2-REPORT.md, checker
   WalkS7a.S7aR24Check2 CONFIRM); the structure is walk-S10's S10TxPut.v (tx_put), a Theorem Labs lane's put.v a reading
   aid only.
   THE GENERIC-P FORM (S7a_indent.v on the lane, a Theorem Labs lane 12:18Z): every segment is stated `forall P, srr_inv_laws
   SEGS P -> ...` (and `srr_inv_call SEGS P ->` where it crosses a call) with P on its start and end memory;
   put_holds instantiates P once (memnorm).
   THE CHAIN AT THE realloc CALL is built from tput_specX's case premises (case 1: the one record from o; case 2:
   o = spZ + 8, put's own saved ra at o - 16 below the ceiling by fpre's raZ bound). fuzz_realloc's two live counts at
   put's entry state S come from the entry's iface_room_pos by PresetRoomCounts.counts_of_room_pos_rl; its live
   premise from prh_live_evs at the grow's one event (put_live_at0); a fake frame's class bound from the P'' engine's
   AR_laws_x field 19 (alx_frames_cid). The NULL arm is the allocation set to fail only: with put's event and consumer
   window, the realloc text's outcome clause gives res <> 0 at every other call (put_realloc_cases). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YG0dcf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetLiveBounds PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit PRW_CallerJ PRW_HShadow S7a_WriterRet.
(* the hull payment at preset's CfParams (hull_budget_of_room_pos); its closure has plain lib/Prog/*_c.v files *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia never sees a division here: each x / 8 is named and bounded first (set ... ; clearbody) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* no implicit sink: lib/A has no ASan sink instance, and the plain one (YI5b) would resolve silently *)
#[global] Remove Hints YI5b.src0_sink_head.

(* ---- put's place in the generated listing ---- *)
Definition PUT_SLOT : nat := A_prog_slot AS_put.
Definition PUT_K : Z := 4 * Z.of_nat PUT_SLOT.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
(* the re-hideable zone: a walk that crosses fuzz_realloc proves SRr' SEGS RZ, its journal after the call at wle' *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.

Definition put_Bx : sv := SOff 32 0.
Definition put_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the struct pj_out at o = a0 (atom 10): buf, len, cap at 0 / 8 / 16 (atoms 33 / 34 / 35), failed at 24 (a literal:
   the walk splits on failed = 0 / failed = 1 before it starts), all 32 bytes writable (the caller's window) *)
Definition put_struct (fl : Z) : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 32 0 32
    [ YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
      YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SLit fl)) ].
Definition put_regions (fl : Z) : smem :=
  [ stack_region (pi_frame F_put); got_regionP; bcell_regionP 32; put_struct fl ].
Definition put_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition put_ss (fl : Z) : sstate := mkSS PUT_K sr_atoms (put_regions fl) None put_facts.
(* the ONE shadow entry: the struct's 32 bytes; it decides every ASan check on the struct statically *)
Definition put_SH : list shent := [ mkSHE 10 0 32 ].
(* a proposition lia does not look into: a large proof context keeps its case splits (disjunctions) behind it, and
   each use unfolds it *)
Definition put_hide (P : Prop) : Prop := P.
Ltac put_hide_all := repeat match goal with H : _ \/ _ |- _ => let T := type of H in change (put_hide T) in H end.
Definition put_extra (buf len cap : Z) : list word :=
  [ Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap ].
Definition put_E (regs : bvmap 5 word) (buf len cap : Z) : env := Eimg (Ereg regs (put_extra buf len cap)).

(* ---- program points: slot deltas from put's entry (measured on the listing; the A' 0x... are reading aids) ---- *)
Definition PK (j : Z) : Z := PUT_K + 4 * j.
(* slot 42 the need test `bgeu` (A' 0x8713c); 44 `bnez cap` (A' 0x87144); 46 the doubling loop head (A' 0x8714c);
   49 after the loop (A' 0x87158); 55 fuzz_realloc's return site (A' 0x87170); 68 the copy block after its two field
   checks (A' 0x871a4, the SEAT of the shared tail); 74 __asan_memcpy's return site (A' 0x871bc); 83 the NUL store
   (A' 0x871e0); 98 the return (A' 0x8721c) *)
(* ---- the SEAT at slot 68 (A' 0x871a4 `ld a0, 0(s0)`), shared by the no-grow arm and the grow arm: a fresh symbolic
   state over the concrete registers there (every register its own atom: s0 = o is atom 8, s1 = n atom 9, s2 = s
   atom 18, s7 = the shadow base atom 23, sp atom 2 = the entry sp - 112), put's frame READ-ONLY with the thirteen
   saved registers of the entry as atoms 35 .. 47 (ra, s0, s1, s2 .. s11), and the struct at o with buf, len, cap as
   atoms 32 / 33 / 34 and failed = 0, writable (the caller's window) ---- *)
Definition put_saved (regs : bvmap 5 word) : list word :=
  [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22;
    getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27 ].
Definition put_seat_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 112 0 0
    [ YP09.mkChunk 8 (CVal 8 (SOff 47 0)); YP09.mkChunk 16 (CVal 8 (SOff 46 0));
      YP09.mkChunk 24 (CVal 8 (SOff 45 0)); YP09.mkChunk 32 (CVal 8 (SOff 44 0));
      YP09.mkChunk 40 (CVal 8 (SOff 43 0)); YP09.mkChunk 48 (CVal 8 (SOff 42 0));
      YP09.mkChunk 56 (CVal 8 (SOff 41 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
      YP09.mkChunk 72 (CVal 8 (SOff 39 0)); YP09.mkChunk 80 (CVal 8 (SOff 38 0));
      YP09.mkChunk 88 (CVal 8 (SOff 37 0)); YP09.mkChunk 96 (CVal 8 (SOff 36 0));
      YP09.mkChunk 104 (CVal 8 (SOff 35 0)) ].
Definition put_seat_struct : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 32 0 32
    [ YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
      YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SLit 0)) ].
Definition put_seat_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
            (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition put_ssk (k : Z) : sstate := mkSS k sr_atoms [put_seat_frame; put_seat_struct] None put_seat_facts.
Definition put_Bx7 : sv := SOff 23 0.
Definition put_Es (regs1 regs : bvmap 5 word) (bufx len capx : Z) : env :=
  Eimg (Ereg regs1 ([Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs)).

(* the return pc of put's `jal fuzz_realloc` (slot 55) is a listing slot, below the ceiling: fpre's raZ bound at the
   call (PRW_StepKit.pa_slot_lt_ceil_b, the S7b walk), CLOSED so its vm_compute never runs inside a big proof (the S3 walk's
   measured trap) *)
Lemma put_ret_slot_ceil : BASE + PK 55 < YM05.alloc_ceiling.
Proof.
(* the slot offset as a literal by vm_compute (a lazy conversion of PK 55 would evaluate the listing's slot search) *)
idtac "PRB-C0".
let v := eval vm_compute in (PK 55) in
 (replace (PK 55) with v by (vm_compute; reflexivity));
idtac "PRB-C1";
 (exact (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) v ltac:(lia) ltac:(vm_compute; reflexivity))).
Qed.

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib B.
Hypothesis Hent : SIGMA AS_put = BASE + PUT_K.
(* image fact, discharged at PI_prog_A (A_prog_obj_img): the GOT word (A_OBJ 0) and the shadow cell (A_OBJ 12) lie
   in the image's segments (PRW_write_value.v's Hobj, the same text) *)
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Variable CTX0 : list (list Z).
Hypothesis HREAL : tfuzz_realloc_specX (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK.
(* the runtime row of __asan_memcpy, with its memnorm keep (YGcallMxmn.v aintrin_realizes_xm; the row owner pays it) *)
Hypothesis AMC : YGcallMxmn.aintrin_realizes_xm SEGS B ARx OCpy (SIGMA AS___asan_memcpy).
Hypothesis HIMGSH : ARx_img_shadow_vis SEGS ARx.
Hypothesis HFRSH : ARx_frame_hull_vis SEGS ARx.
(* image fact (discharged at PI_prog_A by S7a_put_wit.s7p_pst_A, vm_compute over prh_pst: the SEVEN statics are image
   bytes; the in_img half of S10TxPut.v's pal_pst_ok / YC1fPx.v's PST_ok) *)
Hypothesis HPST : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img SEGS a.
(* The kit's named fact (PRH_Base.v prh_head_wide; the preset instance discharges it): the head is at least 8 bytes *)
Hypothesis HW : prh_head_wide.
(* IMAGE FACT (discharged at PI_prog_A: the SEVEN statics of prh_pst are writable, outside every read-only segment
   and outside the relro range; S7a_indent.v's HPSTRO, the same text): no read-only image byte is a program static *)
Hypothesis HPSTRO : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (@prh_pst prh_img_A).
(* IMAGE FACT (discharged at PI_prog_A: asyms_ok's aso_zshadow at the image's B): the image's zero-shadow ranges are
   8-aligned, so AR's zero-shadow law covers each of their bytes (kept_at's in_zs case after fuzz_realloc) *)
Hypothesis HZSA : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
(* IMAGE FACT (discharged at PI_prog_A by conversion, S7a_put_wit.s7p_pab_A): the instance's image bounds, which
   kept_img states the source over (PRH_Base.v @ef7c8ca98529), lie inside YImgTop's IMG_LO / IMG_TOP, the bounds of
   HIMGSH *)
Hypothesis HPAB : IMG_LO <= @pa_lo _ _ PA /\ @pa_hi _ _ PA <= IMG_TOP.
(* INSTANCE FACT (discharged at CfParams_preset by reflexivity, S7a_put_inst.v): the instance's hull caps are at least
   preset's, the caps PresetHullPay.hull_budget_of_room_pos pays under *)
Hypothesis HCAP : @YGcfNames.cf_kmax CfParamsPreset.CfParams_preset <= YGcfNames.cf_kmax /\
  @YGcfNames.cf_T_max CfParamsPreset.CfParams_preset <= YGcfNames.cf_T_max.

Let RUN := paj_run_x (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS.
Let RUNTO := paj_run_to_x (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let BRR := paj_branchR (PI := PA) (wle' SEGS RZ).

(* a journal at wle is one at wle' SEGS RZ (ajournal_xbR_mono with wle_wle') *)
Lemma put_jlift : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) STK sp0 FP ly S Hp W mem md own
    ly' S' Hp' W' mem' md' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (ajournal_xbR_mono (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (@wle SEGS) (wle' SEGS RZ) (wle_wle' SEGS RZ)
  STK sp0 FP ly S W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.

(* a walk at wle whose post is an SRr' goal at its end state is an SRr' walk (SRr'_bind over SRr_SRr'): a walk runs at
   wle up to its crossing call, and continues there at wle' SEGS RZ *)
Lemma put_SRr'_of_SRr : forall W c (Q : world SEGS -> config -> Prop),
  SRr SEGS W c (fun W' c' => SRr' SEGS RZ W' c' Q) -> SRr' SEGS RZ W c Q.
Proof.
intros W c Q H. apply (SRr'_bind SEGS RZ W c _ Q (SRr_SRr' SEGS RZ W c _ H)). intros W' c' _ H'. exact H'.
Qed.

(* THE HULL PAYMENT at put's fuzz_realloc call: the run's position at the call's state, in a run of at most 4 calls,
   leaves preset's top budget (PresetHullPay.hull_budget_of_room_pos); a request below cf_malloc_max is at most one
   call's worth (one secondary, of mapped size at most cf_nob by cf_sizes_ok); HCAP carries preset's caps to cp *)
Lemma put_hull_pay : forall sm x (os : list (option nat * option nat * option nat)) i H0 hist (S : astate) (p k r : Z),
  (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S -> 0 <= r < cf_malloc_max ->
  PresetHullBudget.hull_budget S (if p =? 0 then [PresetReqAt.HMal r] else [PresetReqAt.HRe k r]).
Proof.
intros sm x os i H0 hist S p k r Hl HP Hr.
set (Eg := if p =? 0 then [PresetReqAt.HMal r] else [PresetReqAt.HRe k r]).
assert (HN : (PresetSecTotal.nsec Eg <= 1)%nat /\ PresetSecTotal.tsec Eg <= cf_nob).
{ pose proof (cf_sizes_ok r Hr) as Hs. pose proof cf_nob_lo as Hlo.
  unfold Eg; destruct (p =? 0);
    rewrite ?PresetHullBudget.hull_nsec_re, ?PresetHullBudget.hull_tsec_re, PresetHullBudget.hull_nsec_mal,
      PresetHullBudget.hull_tsec_mal; destruct (YG00.from_primary r); lia. }
destruct HN as (HN & HT).
assert (HN1 : Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL) by (rewrite PresetSecTotal.NCALL_value; lia).
assert (HT1 : PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL)
  by (rewrite PresetSecTotal.TCALL_value; pose proof cf_nob_ok; lia).
destruct (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S Eg Hl HP HN1 HT1) as (B1 & B2).
destruct HCAP as (C1 & C2). unfold PresetHullBudget.hull_budget. split; lia.
Qed.

(* the #102 ledger's two cells g_most / g_own_ran_out (prh_ledger's `most own`): put and its fuzz_realloc write
   neither, so they are fixed through put's walk; Section mo closes over them before put_holds, which takes them from
   tput_specX's quantifier *)
Section mo.
Variable rmost rown : Z.

(* a byte range of the real stack has zero shadow in every ARx state (LAWS' alx_zshadow_byte) *)
Lemma put_stack_ra : forall ly S Hp W mem md a n,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.

(* ---- memory transfer of the writer state (S7a_indent.v ind_out_kept, with the struct's four fields read at the new
   memory instead of kept): a stretch that keeps every byte below alloc_ceiling keeps the buffer, its bytes and its
   shadow; the fields are the new state's ---- *)
Lemma put_out_kept : forall (W : world SEGS) mem mem' Lam o buf (st st' : WriterApp.wst),
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (WriterApp.w_cap st <> 0 -> 0 <= buf /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling) ->
  WriterApp.w_text st' = WriterApp.w_text st -> WriterApp.w_cap st' = WriterApp.w_cap st ->
  (WriterApp.w_failed st' = 0 \/ WriterApp.w_failed st' = 1) ->
  (WriterApp.w_failed st' = 0 -> WriterApp.w_failed st = 0) ->
  val_mem SEGS (mrestrict (w_H W) mem') o 8 buf ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 8) 8 (Z.of_nat (length (WriterApp.w_text st'))) ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 16) 8 (WriterApp.w_cap st') ->
  val_mem SEGS (mrestrict (w_H W) mem') (o + 24) 4 (WriterApp.w_failed st') ->
  prhWriter_out (PA := PA) W mem Lam o buf st -> prhWriter_out (PA := PA) W mem' Lam o buf st'.
Proof.
intros W mem mem' Lam o buf st st' Hlow Hbuf Etx Ecap Hf01' Hf0 V0' V8' V16' V24'
  (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VM : forall a n v, (forall k, (k < n)%nat -> aview SEGS (w_H W) mem' (a + Z.of_nat k) = aview SEGS (w_H W) mem (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hk Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros k Hk'. rewrite <- (Z2Nat.id k) by lia. apply Hk. lia. }
unfold prhWriter_out. rewrite Etx, Ecap in *.
split; [exact Ho8|]. split; [exact Hbr|]. split; [exact Hcr|].
split; [exact V0'|]. split; [exact V8'|]. split; [exact V16'|]. split; [exact V24'|].
split; [exact Hf01'|]. split; [exact Hbok|].
destruct Harm as [Hz | (Hgrid & Hin & Hlen & (rest & Hrl & Hba) & Hsh)]; [left; exact Hz|].
assert (Hcap0 : WriterApp.w_cap st <> 0).
{ destruct Hgrid as (j & Hj & Hc). intros Hz. rewrite Hz in Hc.
  assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
destruct (Hbuf Hcap0) as (Hb0 & Hbc).
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [exact Hlen|].
split.
{ exists rest. split; [exact Hrl|]. intros j Hj. destruct (Hba j Hj) as (Hv & Hr). split; [|exact Hr].
  eapply VM; [intros kk Hkk; apply Hlow; cbn [length] in Hj; lia | exact Hv]. }
intros Hnf. destruct (Hsh (Hf0 Hnf)) as (Hra & Hhv). split.
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

(* a 16-aligned address strictly below a 16-aligned ceiling leaves 8 bytes below it (S7a_indent.v ind_al16_room) *)
Lemma put_al16_room : forall p c, p mod 16 = 0 -> c mod 16 = 0 -> p < c -> p + 8 <= c.
Proof.
intros p c Hp Hc Hlt.
pose proof (Z.div_mod p 16 ltac:(lia)) as Ep. pose proof (Z.div_mod c 16 ltac:(lia)) as Ec.
rewrite Hp in Ep. rewrite Hc in Ec.
set (qp := p / 16) in *. set (qc := c / 16) in *. clearbody qp qc. lia.
Qed.

(* the ledger over a stretch that keeps every byte below alloc_ceiling (S7a_indent.v ind_ledger_kept) *)
Lemma put_ledger_kept0 : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran,
  ARx ly S Hp W mem md ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran rmost rown.
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
  { apply put_al16_room; [exact Hp16 | | lia].
    pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(lia)) as Ec. rewrite HCV2 in Ec.
    rewrite Ec. set (q := YM05.alloc_ceiling / 4096). clearbody q.
    replace (4096 * q + 0) with ((256 * q) * 16) by lia. apply Z_mod_mult. }
  eapply VM; [intros kk Hkk; lia | exact Hv].
Qed.

(* the writer's buffer, when there is one, lies below alloc_ceiling (its block is a live allocator block) *)
Lemma put_buf_low : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran o buf (st : WriterApp.wst),
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  WriterApp.w_cap st <> 0 ->
  cf_head <= buf - 4096 /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling /\ buf mod 16 = 0 /\
  In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran o buf st HAR HLED HOUT Hc.
destruct HLED as (_ & _ & Hbl & _).
destruct HOUT as (_ & _ & Hcr & _ & _ & _ & _ & _ & _ & [(Hz & _) | (_ & Hin & _)]); [contradiction|].
pose proof (proj1 (Forall_forall _ _) Hbl _ Hin) as (Hk0 & Hinb & _ & Ha16 & _). cbn [fst snd] in *.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hinb) as (Hp16 & Hp4 & Hpc & _).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
rewrite Hreq in Hpc. split; [lia|]. split; [lia|]. split; [exact Ha16 | exact Hinb].
Qed.

(* ---- the entry state of the walk ---- *)
Lemma put_entry : forall ly S Hp W regs mem md ch o d buf len cap fl,
  afn_pre_x SEGS B ARx STK_put ly S Hp W regs mem md ch ->
  getr regs 10 = w64 o -> fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d -> o mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) o 8 buf -> 0 <= buf < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 8) 8 len -> 0 <= len < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 16) 8 cap -> 0 <= cap < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (o + 24) 4 fl -> 0 <= fl < 2 ^ 32 ->
  st_ok_pi SEGS VAL (put_E regs buf len cap) (put_ss fl)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + PUT_K)) mem (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx put_SH (put_E regs buf len cap) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch o d buf len cap fl HAP H10 HWIN Hol Hoh Ho8 Vb Rb Vl Rl Vc Rc Vf Rf.
pose proof HAP as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : 112 <= STK_put) by (vm_compute; discriminate).
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_val_range (A_OBJ 0)) as RG. pose proof (pa_val_range (A_OBJ 12)) as RC.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_segs_low (VAL (A_OBJ 0) + 7) (proj1 (Hobj 7 ltac:(lia)))) as LG.
pose proof (pa_segs_low (VAL (A_OBJ 12) + 7) (proj2 (Hobj 7 ltac:(lia)))) as LC.
rewrite restrict_mkst_fx.
set (E := put_E regs buf len cap).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len cap)) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EG : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold put_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EC : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold put_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Ho64 : 0 <= o < 2 ^ 64) by lia.
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
split.
- unfold put_ss. apply pa_entry_st_ok_full.
  + unfold E, put_E. apply (regs_ok_agree 32 (Ereg regs (put_extra buf len cap))).
    * split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + unfold put_regions, stack_region, got_regionP, bcell_regionP, put_struct. rewrite HKf.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EC, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC). split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 put_Bx SHADOW_OFF);
        [cbn [sv_denot put_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat o E10 Ho64). split; [lia|]. split; [lia|].
      split; [intros a Ha; apply (apresent_writable SEGS); apply Hdpres; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ o 0 8 (SOff 33 0) buf);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; apply unsigned_lit_small in Rb; reflexivity
         | zside | zside | rewrite Z.add_0_r; exact Vb].
      -- apply (chunk_ok_val SEGS E _ o 8 8 (SOff 34 0) len);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vl].
      -- apply (chunk_ok_val SEGS E _ o 16 8 (SOff 35 0) cap);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vc].
      -- apply (chunk_ok_val SEGS E _ o 24 4 (SLit fl) fl);
         [cbn [sv_denot]; reflexivity | zside | zside | exact Vf].
  + apply pairwise_disjoint_of_extents.
    unfold put_regions, stack_region, got_regionP, bcell_regionP, put_struct, extent_of_region. rewrite HKf.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat o E10 Ho64).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EG RG), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EC RC).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowMemEnd in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [put_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E10, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, put_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E put_Bx 10 o 32 o 0 32).
  + apply (put_stack_ra ly S Hp W mem md o 32 HAR); lia.
  + unfold U, put_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- the seat (put_ssk k) from the concrete facts at slot 68 ---- *)
Lemma put_seat : forall k (W : world SEGS) (regs regs1 : bvmap 5 word) mem1 bufx len capx,
  spZ regs1 mod 16 = 0 -> 2 ^ 46 <= spZ regs1 -> spZ regs1 + 112 <= bv_unsigned (getr regs1 8) ->
  (forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs1 + 104 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))) ->
  bv_unsigned (getr regs1 8) mod 8 = 0 -> bv_unsigned (getr regs1 8) + 32 <= 2 ^ 47 ->
  (forall a, bv_unsigned (getr regs1 8) <= a < bv_unsigned (getr regs1 8) + 32 -> apresent (w_H W) mem1 a) ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8)) 8 bufx -> 0 <= bufx < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 8) 8 len -> 0 <= len < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 16) 8 capx -> 0 <= capx < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem1) (bv_unsigned (getr regs1 8) + 24) 4 0 ->
  getr regs1 23 = Z_to_bv 64 SHADOW_OFF ->
  st_ok_pi SEGS VAL (put_Es regs1 regs bufx len capx) (put_ssk k)
    (restrict (w_H W) (YK11.mkst regs1 (Z_to_bv 64 (BASE + k)) mem1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx7 [] (put_Es regs1 regs bufx len capx) (mrestrict (w_H W) mem1).
Proof.
intros k W regs regs1 mem1 bufx len capx Hal Hsp Hso Hsv Ho8 Ho47 Hopres Vb Rb Vl Rl Vc Rc Vf H23.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (o := bv_unsigned (getr regs1 8)) in *.
set (xs := [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs).
set (E := put_Es regs1 regs bufx len capx).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 xs) kk)
  by (intros kk Hk; subst E; unfold put_Es; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs1 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (E8 : ew E 8 = getr regs1 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 8 8%bv eq_refl)).
assert (Uo : bv_unsigned (ew E 8) = o) by (rewrite E8; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact H23).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 xs j)).
assert (Ho64 : 0 <= o < 2 ^ 64) by (subst o; apply u64_range).
assert (VB8 : base_val E (Some 8%nat) = o) by (cbn [base_val]; exact Uo).
assert (VB2 : base_val E (Some 2%nat) = spZ regs1) by (cbn [base_val]; exact Usp).
assert (CH : forall j, (j < 13)%nat -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem1) (spZ regs1)
   (YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ (spZ regs1) (104 - 8 * Z.of_nat j) 8 (SOff (35 + j) 0)
    (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
  - cbn [sv_denot]. rewrite Z.add_0_r. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
    rewrite EX by lia. subst xs. rewrite app_nth2 by (cbn [length]; lia).
    replace (3 + j - length [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx])%nat with j by (cbn [length]; lia).
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - exact (u64_range (nth j (put_saved regs) (Z_to_bv 64 0))).
  - cbn. lia.
  - replace (spZ regs1 + (104 - 8 * Z.of_nat j)) with (spZ regs1 + 104 - 8 * Z.of_nat j) by lia. exact (Hsv j Hj). }
assert (DEN : forall (j : nat) z, (j < 3)%nat -> nth j xs (Z_to_bv 64 0) = Z_to_bv 64 z -> sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 z).
{ intros j z Hj Hz. cbn [sv_denot]. rewrite EX by lia. rewrite Hz, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
- unfold put_ssk. apply pa_entry_st_ok_full.
  + subst E. unfold put_Es. apply (regs_ok_agree 32 (Ereg regs1 xs)).
    * split; [intros kk Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    * vm_compute. reflexivity.
    * apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * unfold region_ok, put_seat_frame. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      all: first [ exact (CH 12%nat ltac:(lia)) | exact (CH 11%nat ltac:(lia)) | exact (CH 10%nat ltac:(lia))
                 | exact (CH 9%nat ltac:(lia)) | exact (CH 8%nat ltac:(lia)) | exact (CH 7%nat ltac:(lia))
                 | exact (CH 6%nat ltac:(lia)) | exact (CH 5%nat ltac:(lia)) | exact (CH 4%nat ltac:(lia))
                 | exact (CH 3%nat ltac:(lia)) | exact (CH 2%nat ltac:(lia)) | exact (CH 1%nat ltac:(lia))
                 | exact (CH 0%nat ltac:(lia)) ].
    * unfold region_ok, put_seat_struct. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB8. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply (apresent_writable SEGS); apply Hopres; lia|].
      repeat (apply Forall_cons); try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ o 0 8 (SOff 32 0) bufx);
         [apply (DEN 0%nat); [lia | reflexivity] | zside | zside | rewrite Z.add_0_r; exact Vb].
      -- apply (chunk_ok_val SEGS E _ o 8 8 (SOff 33 0) len);
         [apply (DEN 1%nat); [lia | reflexivity] | zside | zside | exact Vl].
      -- apply (chunk_ok_val SEGS E _ o 16 8 (SOff 34 0) capx);
         [apply (DEN 2%nat); [lia | reflexivity] | zside | zside | exact Vc].
      -- apply (chunk_ok_val SEGS E _ o 24 4 (SLit 0) 0); [cbn [sv_denot]; reflexivity | zside | zside | exact Vf].
  + apply pairwise_disjoint_of_extents.
    unfold put_seat_frame, put_seat_struct, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB8, VB2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [put_seat_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uo, E23, !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF in *. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* the struct's shadow entry at any ARx state: the struct lies on the real stack, whose shadow is zero *)
Lemma put_shok : forall (E' : env) ly S Hp (W : world SEGS) m md o,
  ARx ly S Hp W m md -> ew E' 32 = Z_to_bv 64 SHADOW_OFF -> ew E' 10 = Z_to_bv 64 o ->
  ly_stk_lo ly <= o -> o + 32 <= ly_stk_hi ly -> YM05.alloc_ceiling <= o -> o + 32 <= 2 ^ 47 ->
  sh_ok SEGS put_Bx put_SH E' (mrestrict (w_H W) m).
Proof.
intros E' ly S Hp W m md o HAR E32 E10 Hlo Hhi Ho0 Ho47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold sh_ok, put_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m E' put_Bx 10 o 32 o 0 32).
- apply (put_stack_ra ly S Hp W m md o 32 HAR); lia.
- unfold U, put_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
- lia.
- lia.
- intros a Ha. unfold SHADOW_OFF in *. lia.
Qed.

(* the write permission of a run's regions: the frame and the struct in the caller window (both inside
   [sp0 - STK, sp0), the window journal's own range), the GOT word and the shadow cell read-only (S10TxPut.v tp_awr) *)
Ltac put_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with |- awr_ok ?Ex (YP09.mkRegion (Some ?m) _ _ _ _ _ :: _) _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (bv_unsigned (ew Ex m) - sp0')) end;
  [reflexivity | lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].

(* the region list of a symbolic state: the i-th region's region_ok at the state's memory *)
Ltac put_region HS i r H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?msr =>
    assert (H : region_ok segs E (ms_mem msr) r)
      by (exact (st_ok_region_nth segs E (abs_ss val ss) msr i r HS ltac:(vm_compute; reflexivity)));
    cbn [ms_mem restrict] in H
  end.
(* the same, with the region read off the state *)
Ltac put_region_auto HS i H :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem (abs_ss val ss)) in
    let r := eval cbn in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    put_region HS i r H
  end.

(* the shadow byte of an address below the stack band is itself below it, and so is a shadow hull there
   (FuzzStrdup.v sd_shadow_low / sd_hull_low) *)
Lemma put_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma put_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
unfold SHADOW_OFF in *. lia.
Qed.
(* a byte of value 0 *)
Lemma put_aview_val1 : forall (H : word -> bool) m a, val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a Hv. unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
vm_compute. reflexivity.
Qed.

(* ---- THE SHARED TAIL, from the seat at slot 68 to the return: the copy (__asan_memcpy (bufx + len, s, n) at
   slot 73), len += n into the struct, the NUL store at bufx + len + n (its shadow check from the destination's
   range_addressable, the token branch of a partial granule), the epilogue and the return. Its post gives the
   bytes: the copy, the NUL, the struct's fields, everything else below alloc_ceiling kept. GENERIC-P FORM (S7a_indent.v,
   a Theorem Labs lane 12:18Z): P on the start and the end memory; it crosses the runs by its laws and __asan_memcpy by the
   row's keep (aj_intrin_at_xm) and srr_inv_call ---- *)
Lemma put_tail : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W regs mem md d o s n bufx len capx (FP : list (Z * Z))
    lyc Sc Hpc W1 (regs1 : bvmap 5 word) mem1 md1 k1
    (Qf : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) (STK_put + d) (spZ regs + d) FP ly S Hp W
    mem md [] lyc Sc Hpc W1 mem1 md1 k1 -> P mem1 ->
  YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> 0 <= d -> d mod 16 = 0 -> spZ regs <= o -> o + 32 <= spZ regs + d -> o mod 8 = 0 ->
  spZ regs1 = spZ regs - 112 -> getr regs1 8 = Z_to_bv 64 o -> getr regs1 9 = Z_to_bv 64 n ->
  getr regs1 18 = Z_to_bv 64 s -> getr regs1 23 = Z_to_bv 64 SHADOW_OFF ->
  getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  (forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))) ->
  val_mem SEGS (mrestrict (w_H W1) mem1) o 8 bufx -> val_mem SEGS (mrestrict (w_H W1) mem1) (o + 8) 8 len ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (o + 16) 8 capx -> val_mem SEGS (mrestrict (w_H W1) mem1) (o + 24) 4 0 ->
  0 <= capx < 2 ^ 64 -> 0 <= len ->
  (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  (forall a, o <= a < o + 32 -> inFP FP a) ->
  0 <= n < 2 ^ 32 -> 4096 <= bufx -> bufx + len + n + 1 <= YM05.alloc_ceiling ->
  amem_range (bufx + len) (n + 1) ->
  (forall a, bufx + len <= a <= bufx + len + n ->
     awr_byte (STK_put + d) (spZ regs + d) FP (ablocks B ly S) (ablocks B lyc Sc) lyc [] a) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF (bufx + len) (n + 1) ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) mem1) (bufx + len) n) ->
  4096 <= s -> s + n <= YM05.alloc_ceiling -> amem_range s n ->
  (forall a, s <= a < s + n -> aview SEGS (w_H W1) mem1 a <> None) ->
  (bufx + len + n <= s \/ s + n <= bufx + len) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF s n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W1) mem1) s n) ->
  (forall regs' mem' md' k',
     ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) (STK_put + d) (spZ regs + d) FP ly S Hp W
       mem md [] lyc Sc Hpc W1 mem' md' k' -> P mem' ->
     (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (bufx + len <= a <= bufx + len + n) ->
        aview SEGS (w_H W1) mem' a = aview SEGS (w_H W1) mem1 a) ->
     (forall i, 0 <= i < n -> aview SEGS (w_H W1) mem' (bufx + len + i) = aview SEGS (w_H W1) mem1 (s + i)) ->
     aview SEGS (w_H W1) mem' (bufx + len + n) = Some 0 ->
     val_mem SEGS (mrestrict (w_H W1) mem') o 8 bufx ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 8) 8 (len + n) ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 16) 8 capx ->
     val_mem SEGS (mrestrict (w_H W1) mem') (o + 24) 4 0 ->
     Qf lyc Sc Hpc W1 regs' mem' md') ->
  SRr' SEGS RZ W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 68)) mem1 (YK11.seg_rom SEGS)) md1)
    (fpostWR B ARx SK (wle' SEGS RZ) STK_put d FP regs ly S Hp W mem md Qf).
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
pose (RUNTOI := paj_run_to_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
intros ly S Hp W regs mem md d o s n bufx len capx FP lyc Sc Hpc W1 regs1 mem1 md1 k1 Qf
  HJ HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8 Hsp1 R8 R9 R18 R23 R3 R4 Hsv Vb Vl Vc Vf Rc Rl HWK HFPo
  Hn Hb4096 Hbc Hamr Hawr Hra_d Hhull_d Hs4096 Hsc Hamrs Hsvis Hdisj Hra_s Hhull_s HQ.
pose proof (ajxR_ar HJ) as HAR1. pose proof (ajxR_ly HJ) as Hly1. pose proof (ajxR_k HJ) as Hk1.
pose proof (ajxR_pres HJ) as Hpres1. pose proof (ajxR_stk HJ) as Hstat1.
pose proof Hstat1 as (Hal1 & Hstk01 & Hceil1 & Hslo1 & Hshi1 & H471 & Hbot1 & Htop1 & Htop21).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HKs : STK_put = 16592) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Ho64 : bv_unsigned (getr regs1 8) = o) by (rewrite R8; apply unsigned_lit_small; lia).
destruct (put_seat (PK 68) W1 regs regs1 mem1 bufx len capx) as (HS & SHOK).
{ rewrite Hsp1, Zminus_mod, Hal16. reflexivity. }
{ rewrite Hsp1. lia. }
{ rewrite Hsp1, Ho64. lia. }
{ intros j Hj. rewrite Hsp1. replace (spZ regs - 112 + 104 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
  exact (Hsv j Hj). }
{ rewrite Ho64. exact Ho8. }
{ rewrite Ho64. lia. }
{ intros a Ha. rewrite Ho64 in Ha. apply Hpres1. lia. }
{ rewrite Ho64. exact Vb. }
{ lia. }
{ rewrite Ho64. exact Vl. }
{ lia. }
{ rewrite Ho64. exact Vc. }
{ exact Rc. }
{ rewrite Ho64. exact Vf. }
{ exact R23. }
set (xs := [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx] ++ put_saved regs) in *.
set (E := put_Es regs1 regs bufx len capx) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs1 xs) kk)
  by (intros kk Hk; subst E; unfold put_Es; apply Eimg_low; exact Hk).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 112) by (rewrite (EG 2%nat 2%bv) by (lia || reflexivity); exact Hsp1).
assert (Uo : bv_unsigned (ew E 8) = o) by (rewrite (EG 8%nat 8%bv) by (lia || reflexivity); exact Ho64).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 xs j)).
(* ---- run 1: slots 68 .. 73, buf + len, s, n into a0 / a1 / a2, the __asan_memcpy call ---- *)
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (E32 : ew E 32 = Z_to_bv 64 bufx) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 capx) by exact (EX 2%nat ltac:(lia)).
(* run 1 writes nothing but its write windows: the struct *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha Hn'. apply aview_eq_of. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  unfold put_ssk in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi put_seat_frame put_seat_struct base_val] in Hra';
    rewrite ?Usp, ?Uo in Hra'; lia. }
clear HF HG HFr.
(* ---- the copy: __asan_memcpy (bufx + len, s, n) through its text ---- *)
eapply (SRr'_bind SEGS RZ).
{ apply (SRr_SRr' SEGS RZ).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xmR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA)
    (wle' SEGS RZ) OCpy
    (SIGMA AS___asan_memcpy) AMC W1 rT mT (STK_put + d) (spZ regs + d) FP ly S Hp W mem md [] lyc Sc Hpc dT k1
    (bufx + len) s n (- (112 + d)) _ HJ) end.
  - rewrite Q10, E32, E33, alu_add_small by (unfold M64; lia). reflexivity.
  - rewrite Q11, (EG 18%nat 18%bv) by (lia || reflexivity). rewrite R18. reflexivity.
  - rewrite Q12, (EG 9%nat 9%bv) by (lia || reflexivity). rewrite R9. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ at 1. rewrite Q2. change (bv_unsigned (ew E 2) = spZ regs + d + - (112 + d)). lia.
  - replace (- (112 + d)) with ((- 7 - d / 16) * 16) by (pose proof (Z.div_mod d 16 ltac:(lia)); lia).
    apply Z_mod_mult.
  - lia.
  - rewrite Hes. lia.
  - rewrite Q3, (EG 3%nat 3%bv) by (lia || reflexivity). rewrite R3. exact Hgp.
  - rewrite Q4, (EG 4%nat 4%bv) by (lia || reflexivity). rewrite R4. exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split; [apply Hawr; lia | rewrite Hes; lia].
  - unfold amem_range in *. lia.
  - eapply (range_addressable_agree (aview SEGS (w_H W1) mem1)).
    { intros x Hx. pose proof (put_shadow_low x ltac:(lia)). apply KA; lia. }
    apply (range_addressable_sub _ _ (bufx + len) (n + 1)); [exact Hra_d | lia | lia].
  - intros Hn0 s0 Hs0. pose proof (put_hull_low (bufx + len) n s0 ltac:(lia) Hn0 ltac:(lia) Hs0).
    rewrite KA by lia. exact (Hhull_d Hn0 s0 Hs0).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [rewrite KA by lia; exact (Hsvis a Ha)|].
      unfold spZ at 1 2. rewrite Q2. change (bv_unsigned (ew E 2)) with (bv_unsigned (ew E 2)). rewrite Usp, Hes. lia. }
    split; [exact Hdisj|]. split; [exact Hamrs|]. split.
    + eapply (range_addressable_agree (aview SEGS (w_H W1) mem1)); [|exact Hra_s].
      intros x Hx. pose proof (put_shadow_low x ltac:(lia)). apply KA; lia.
    + intros Hn0 s0 Hs0. pose proof (put_hull_low s n s0 ltac:(lia) Hn0 ltac:(lia) Hs0).
      rewrite KA by lia. exact (Hhull_s Hn0 s0 Hs0). }
cbv beta. intros W5 c5 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hcopy & Hfr2 & Hpres2 & Hmn2).
(* P crosses the copy by the row's keep *)
pose proof (PCALL _ _ Hmn2 HPM) as HPM2. clear HPM Hmn2. rename HPM2 into HPM.
cbv beta iota in Hcopy.
pose proof (ajxR_pres HJ2) as Hpres2J.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|constructor; [|apply Forall_nil]]; split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | lia | rewrite Hes; lia].
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Uo in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | lia | rewrite Hes; lia].
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Uo in Ha.
    apply (apresent_writable SEGS). apply Hpres2J. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 48 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HSX.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall kk, (kk < 48)%nat -> ew E2 kk = ew E kk) by (intros kk Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs - 112) by (rewrite OLD2 by lia; exact Usp).
assert (Uo2 : bv_unsigned (ew E2 8) = o) by (rewrite OLD2 by lia; exact Uo).
assert (SHOK2 : sh_ok SEGS put_Bx7 [] E2 (mrestrict (w_H W1) mem2)) by (unfold sh_ok; apply Forall_nil).
clear HS SHOK HJ HEI. rename HSX into HS. rename SHOK2 into SHOK. rename HJ2 into HJ. rename HEI2 into HEI.
(* ---- run 2: slots 74 .. 78, len + n into the struct, a0 = bufx + len + n ---- *)
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 79).
all: try solve [put_awr].
rename HFr into HFr2. clear HF HG.
(* run 2 writes nothing but its write windows: the struct *)
assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha Hn'. apply aview_eq_of. rewrite (HFr2 (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra';
    rewrite ?Usp2, ?Uo2 in Hra'; lia. }
pmkst HS.
prreg HS (10%bv : bv 5) R10.
set (X := bufx + len + n) in *.
assert (HX10 : getr (ms_regs ms0) 10 = Z_to_bv 64 X).
{ rewrite R10, (OLD2 9%nat), (OLD2 32%nat), (OLD2 33%nat) by lia. rewrite (EG 9%nat 9%bv) by (lia || reflexivity).
  rewrite R9, E32, E33. rewrite alu_add_small by (unfold M64; lia). rewrite alu_add_small by (unfold M64; lia).
  subst X. f_equal. lia. }
(* the NUL store's address bufx + len + n is a sum of three atoms: give it an atom of its own (a zero-instruction
   stretch that clobbers only a0), so the engine decides its shadow check and reaches its region *)
let v := eval vm_compute in (PK 79) in
jafter_stretch_pi HS 64%nat (ms_regs ms0) (mrestrict (w_H W1) (ms_mem ms0)) ([10%bv] : list (bv 5)) v HSY.
specialize (HSY (fun r _ => eq_refl)).
lazymatch type of HSY with ?T -> _ => assert (HKY : T) end.
{ apply Forall_forall. intros r _. split; [intros a _; reflexivity | intros a _ Hw; exact Hw]. }
specialize (HSY HKY). clear HKY. rewrite <- restrict_mkst_fx in HSY.
remember (havoc E2 64 (map (getr (ms_regs ms0)) [10%bv])) as E3 eqn:HE3 in HSY.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall kk, (kk < 64)%nat -> ew E3 kk = ew E2 kk) by (intros kk Hk; rewrite HE3; apply ew_havoc_old; exact Hk).
assert (E3X : ew E3 64 = Z_to_bv 64 X) by (rewrite HE3, <- HX10; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs - 112) by (rewrite OLD3 by lia; exact Usp2).
assert (Uo3 : bv_unsigned (ew E3 8) = o) by (rewrite OLD3 by lia; exact Uo2).
assert (UX3 : bv_unsigned (ew E3 64) = X) by (rewrite E3X; apply unsigned_lit_small; lia).
assert (HXP : apresent (w_H W1) (ms_mem ms0) X /\ ~ aowned B lyc Sc X).
{ eapply (awr_byte_present_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS).
  all: first [exact HJ | exact (@pa_segs_low _ _ PA) | apply Hawr; lia]. }
(* the NUL byte is application memory, low or high (amem_range): its region's window must miss the shadow span
   (the engine's cells_safe_b), so the atom's range is the one of the two bands it lies in *)
assert (HXr : X + 1 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= X).
{ unfold amem_range in Hamr. subst X. unfold SHADOW_OFF. rewrite C3, C5 in Hamr. lia. }
destruct HXr as [HXr | HXr].
1: pose proof (st_ok_pi_add_fact E3 _ _ 64%nat (mkAF 0 2147450879 0) HSY) as HSF.
2: pose proof (st_ok_pi_add_fact E3 _ _ 64%nat (mkAF 17594333495296 140737479966720 0) HSY) as HSF.
all: lazymatch type of HSF with ?T -> _ => assert (HAF : T)
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite UX3, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF in *; lia) end.
all: specialize (HSF HAF); clear HAF.
all: pose proof (st_ok_pi_add_region E3 _ _ (YP09.mkRegion (Some 64%nat) 0 1 0 1 []) HSF ltac:(vm_compute; reflexivity)) as HSR.
all: lazymatch type of HSR with ?A -> ?B -> _ =>
  assert (HA : A) by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite UX3; split; [lia|]; split; [lia|]; split; [|constructor];
    intros oo Hoo; apply (apresent_writable SEGS); replace (X + oo) with X by lia; exact (proj1 HXP));
  assert (HB : B) by (lazymatch goal with |- all_disjoint _ _ (ss_mem ?s) => let rs := eval vm_compute in (ss_mem s) in change (ss_mem s) with rs end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite UX3, Usp3, Uo3; lia);
  specialize (HSR HA HB); clear HA HB end.
all: assert (SHOK3 : sh_ok SEGS put_Bx7 [] E3 (mrestrict (w_H W1) (ms_mem ms0))) by (unfold sh_ok; apply Forall_nil).
all: clear HS HSY HSF SHOK HEI; rename HSR into HS; rename SHOK3 into SHOK; rename HEI3 into HEI.
(* ---- run 3: slots 79 .. 98, the shadow check of the NUL byte, sb zero, the epilogue, the return ---- *)
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_gen E3 _ _ _ _ _ _ _ _ _ 64%nat X); [reflexivity | exact UX3 | | put_awr];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; subst X; lia ].
(* the NUL byte's shadow check: the destination's range_addressable at the seat, kept by run 1 (writes the struct
   only), the copy (writes the destination and its ESTACK window) and run 2 (the struct only); slot 79's offset is the
   literal the symbolic run prints, COMPUTED from the listing (never typed: it moves with a re-pin) *)
all: try solve [ let v79 := eval vm_compute in (PK 79) in
  change (rd_of SEGS (mrestrict (w_H W1) (ms_mem (YK11.mkst (ms_regs ms0) (Z_to_bv 64 (BASE + v79))
    (ms_mem ms0) (YK11.seg_rom SEGS))))) with (aview SEGS (w_H W1) (ms_mem ms0)); unfold put_Bx7;
  rewrite (U_atom E3 23%nat SHADOW_OFF) by (first [ unfold SHADOW_OFF; lia
    | rewrite OLD3, OLD2 by lia; rewrite (EG 23%nat 23%bv) by (lia || reflexivity); exact R23 ]);
  rewrite (U_atom E3 64%nat X E3X) by (subst X; lia);
  eapply (range_addressable_agree (aview SEGS (w_H W1) mem1));
  [ intros x Hx; pose proof (put_shadow_low x ltac:(subst X; lia)) as Hsl;
    unfold shadow_of_addr, SHADOW_OFF in Hsl |- *;
    unfold amem_range in Hamr; rewrite C3, C5 in Hamr;
    set (q := x / 8) in *; assert (0 <= q) by (unfold q; apply Z.div_pos; lia);
    assert (8 * q <= x) by (unfold q; apply Z.mul_div_le; lia); clearbody q;
    rewrite (KB2 (2147450880 + q)) by lia;
    rewrite (Hfr2 (2147450880 + q)); [rewrite KA by lia; reflexivity | lia | subst X; lia | rewrite Hes; lia]
  | apply (range_addressable_sub _ _ (bufx + len) (n + 1)); [exact Hra_d | subst X; lia | subst X; lia] ] ].
(* ---- the return at slot 98 and the post ---- *)
(* run 3 writes nothing but its write windows: the NUL byte and the struct *)
all: assert (KC3 : forall a, 0 <= a < 2 ^ 64 -> a <> X -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) (ms_mem ms0) a)
  by (intros a Ha HaX Hn'; apply aview_eq_of; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
      rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
      match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra';
      rewrite ?UX3, ?Usp3, ?Uo3 in Hra'; lia).
all: assert (KLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (bufx + len <= a <= X) ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha Hn'; subst X; rewrite KC3 by lia; rewrite KB2 by lia;
      rewrite (Hfr2 a) by (rewrite ?Hes; lia); apply KA; lia).
all: assert (KWIN : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) mem1 a)
  by (intros a Ha Hn'; subst X; rewrite KC3 by lia; rewrite KB2 by lia;
      rewrite (Hfr2 a) by (rewrite ?Hes; lia); apply KA; lia).
all: try rewrite wvb_collapse in HJ.
all: apply (SRr_SRr' SEGS RZ).
all: apply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat1.
all: lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ => set (EF := Ef) in HS end.
all: assert (EFo : forall kk, (kk < 48)%nat -> ew EF kk = ew E kk)
  by (intros kk Hk; subst EF; rewrite !ew_ewset_other by lia; rewrite OLD3, OLD2 by lia; reflexivity).
all: assert (SAV : forall j, (j < 13)%nat -> ew EF (35 + j) = nth j (put_saved regs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EFo by lia; replace (35 + j)%nat with (32 + (3 + j))%nat by lia;
      rewrite EX by lia; subst xs; rewrite app_nth2 by (cbn [length]; lia);
      replace (3 + j - length [Z_to_bv 64 bufx; Z_to_bv 64 len; Z_to_bv 64 capx])%nat with j by (cbn [length]; lia);
      reflexivity).
all: assert (GR : forall rr : bv 5, getr (ms_regs ms1) rr = sv_denot EF (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) EF _ ms1 rr HS)).
all: assert (D0 : forall (kx : nat) (wx : word), ew EF kx = wx -> sv_denot EF (SOff kx 0) = wx)
  by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
all: assert (HP : aregs_preserved regs (ms_regs ms1)) by (intros r Hr; unfold acallee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  rewrite GR;
  repeat destruct Hr' as [-> | Hr']; try (subst r);
  match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
  first
    [ (cbn [sv_denot]; rewrite EFo, Usp by lia; rewrite Z.sub_add; apply Z_to_bv_bv_unsigned)
    | (apply D0; rewrite EFo by lia; rewrite (EG 3%nat 3%bv) by (lia || reflexivity); exact R3)
    | (apply D0; rewrite EFo by lia; rewrite (EG 4%nat 4%bv) by (lia || reflexivity); exact R4)
    | (apply D0; first [ exact (SAV 1%nat ltac:(lia)) | exact (SAV 2%nat ltac:(lia)) | exact (SAV 3%nat ltac:(lia))
        | exact (SAV 4%nat ltac:(lia)) | exact (SAV 5%nat ltac:(lia)) | exact (SAV 6%nat ltac:(lia))
        | exact (SAV 7%nat ltac:(lia)) | exact (SAV 8%nat ltac:(lia)) | exact (SAV 9%nat ltac:(lia))
        | exact (SAV 10%nat ltac:(lia)) | exact (SAV 11%nat ltac:(lia)) | exact (SAV 12%nat ltac:(lia)) ]) ]).
all: assert (Hra1 : getr (ms_regs ms1) 1 = getr regs 1)
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      apply D0; exact (SAV 0%nat ltac:(lia))).
all: assert (UoF : bv_unsigned (ew EF 8) = o) by (rewrite EFo by lia; exact Uo).
all: assert (UXF : bv_unsigned (ew EF 64) = X) by (subst EF; rewrite !ew_ewset_other by lia; exact UX3).
(* the struct's fields and the NUL byte at the end, from the final state's regions *)
all: put_region HS 2%nat (YP09.mkRegion (Some 8%nat) 0 32 0 32
  [ YP09.mkChunk 8 (CVal 8 (SAlu ALU_ADD (SOff 9 0) (SOff 33 0))); YP09.mkChunk 0 (CVal 8 (SOff 32 0));
    YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SLit 0)) ]) HRS.
all: put_region HS 0%nat (YP09.mkRegion (Some 64%nat) 0 1 0 1 [ YP09.mkChunk 0 (CVal 1 (SLit 0)) ]) HRX.
all: assert (W0' : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) o 8 bufx)
  by (pose proof (field_of_region SEGS EF _ 8 o _ 0 32 0 32 0 8%N (SOff 32 0) bufx HRS UoF ltac:(cbn; tauto)
        ltac:(apply D0; rewrite EFo by lia; exact E32) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv;
      rewrite Z.add_0_r in Hv; exact Hv).
all: assert (W8' : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (o + 8) 8 (len + n))
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 8 8%N (SAlu ALU_ADD (SOff 9 0) (SOff 33 0)) (len + n) HRS UoF
        ltac:(cbn; tauto)
        ltac:(cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; rewrite (EFo 9%nat), (EFo 33%nat) by lia;
              rewrite (EG 9%nat 9%bv) by (lia || reflexivity); rewrite R9, E33;
              rewrite alu_add_small by (unfold M64; lia); f_equal; lia)
        ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (W16' : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (o + 16) 8 capx)
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 16 8%N (SOff 34 0) capx HRS UoF ltac:(cbn; tauto)
        ltac:(apply D0; rewrite EFo by lia; exact E34) ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (W24' : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms1)) (o + 24) 4 0)
  by (exact (field_of_region SEGS EF _ 8 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS UoF ltac:(cbn; tauto)
        eq_refl ltac:(cbn; lia) ltac:(cbn; lia))).
all: assert (WX : aview SEGS (w_H W1) (ms_mem ms1) X = Some 0)
  by (apply put_aview_val1;
      pose proof (field_of_region SEGS EF _ 64 X _ 0 1 0 1 0 1%N (SLit 0) 0 HRX UXF ltac:(cbn; tauto)
        eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv;
      rewrite Z.add_0_r in Hv; exact Hv).
all: unfold fpostWR.
all: lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dd = _ /\ _ =>
  exists lyc, Sc, Hpc, r, m, dd, k1 end.
all: split; [rewrite Hra1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
all: split; [exact (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA)
  (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ)|].
all: split; [intros a Ha Hnf; rewrite KWIN; [exact (HWK a Ha Hnf) | lia | intros Ho; apply Hnf; apply HFPo; exact Ho]|].
all: split; [exact HP|].
all: apply (HQ _ _ _ k1).
all: [> exact (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA)
  (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) | exact HPM | exact KLOW
  | intros i Hi; rewrite KC3 by (subst X; lia); rewrite KB2 by lia; rewrite (Hcopy i Hi); apply KA; lia
  | exact WX | exact W0' | exact W8' | exact W16' | exact W24'
  | exact (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA)
  (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) | exact HPM | exact KLOW
  | intros i Hi; rewrite KC3 by (subst X; lia); rewrite KB2 by lia; rewrite (Hcopy i Hi); apply KA; lia
  | exact WX | exact W0' | exact W8' | exact W16' | exact W24' ].
Qed.

(* ---- the byte windows of the writer, read through the walk's view (S10TxPut.v tp_garr8_aview / tp_garr8_move) ---- *)
(* the bytes of a byte window are bytes *)
Lemma put_bytes_ok_of : forall (W : world SEGS) m p l, bytes_at (PA := PA) W m p l -> WriterSpec.bytes_ok l.
Proof. intros W m p l H. exact (garr8_bytes_ok SEGS (mrestrict (w_H W) m) p l H). Qed.

(* a byte of a byte window, read through the view *)
Lemma put_garr8_aview : forall (W : world SEGS) m p l j, bytes_at (PA := PA) W m p l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold bytes_at in H. unfold aview.
rewrite (garr8_mbyte SEGS (mrestrict (w_H W) m) p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.

(* a byte window from its bytes, read through the view *)
Lemma put_garr8_of_aview : forall (W : world SEGS) m p l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m (p + Z.of_nat j) = Some (nth j l 0)) ->
  WriterSpec.bytes_ok l -> bytes_at (PA := PA) W m p l.
Proof.
intros W m p l HA Hok. unfold bytes_at, garr8. intros j Hj.
assert (Hr : 0 <= nth j l 0 < 256) by exact (proj1 (Forall_forall _ _) Hok _ (nth_In l 0 Hj)).
split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (HA j Hj). unfold aview in HA.
destruct (mbyte SEGS (mrestrict (w_H W) m) (p + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in HA;
  [|discriminate HA].
injection HA as Hb. f_equal.
rewrite (YI04.le_byte_small (nth j l 0) 1 0) by (try (change (2 ^ (8 * Z.of_nat 1)) with 256); lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r, <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the writer state after a put that copied bs at buf' + len and stored the NUL (the shared tail's facts); the byte at
   buf' + len before the put (r0) is any byte: the copy or the NUL overwrites it *)
Lemma put_out_put : forall (W1 : world SEGS) mem1 mem' Lam' o buf' cap' (text bs : list Z) r0 (rest : list Z) s
    cnt' fail' calls',
  o mod 8 = 0 -> 4096 <= buf' -> buf' + cap' <= YM05.alloc_ceiling ->
  (buf' + cap' <= kLowShadowBeg \/ kHighMemBeg <= buf') ->
  (exists j, 0 <= j <= 51 /\ cap' = 4096 * 2 ^ j) -> In (buf', cap') Lam' ->
  Z.of_nat (length (text ++ r0 :: rest)) = cap' ->
  bytes_at (PA := PA) W1 mem1 buf' (text ++ r0 :: rest) ->
  range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF buf' cap' ->
  shadow_hull_vis (aview SEGS (w_H W1) mem1) buf' cap' ->
  WriterSpec.bytes_ok text ->
  bytes_at (PA := PA) W1 mem1 s bs ->
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= cap' ->
  (forall a, 0 <= a < YM05.alloc_ceiling ->
     ~ (buf' + Z.of_nat (length text) <= a <= buf' + Z.of_nat (length text) + Z.of_nat (length bs)) ->
     aview SEGS (w_H W1) mem' a = aview SEGS (w_H W1) mem1 a) ->
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     aview SEGS (w_H W1) mem' (buf' + Z.of_nat (length text) + i) = aview SEGS (w_H W1) mem1 (s + i)) ->
  aview SEGS (w_H W1) mem' (buf' + Z.of_nat (length text) + Z.of_nat (length bs)) = Some 0 ->
  val_mem SEGS (mrestrict (w_H W1) mem') o 8 buf' ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 8) 8 (Z.of_nat (length text) + Z.of_nat (length bs)) ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 16) 8 cap' ->
  val_mem SEGS (mrestrict (w_H W1) mem') (o + 24) 4 0 ->
  prhWriter_out (PA := PA) W1 mem' Lam' o buf' (WriterApp.mkW 0 (text ++ bs) cap' cnt' fail' calls').
Proof.
intros W1 mem1 mem' Lam' o buf' cap' text bs r0 rest s cnt' fail' calls' Ho8 Hb4096 Hbc Hband Hgrid Hin Hlen Hba
  Hra Hhv Htok Hbs Hroom Hkeep Hcopy Hnul V0 V8 V16 V24.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlen' : Z.of_nat (length text) + 1 + Z.of_nat (length rest) = cap')
  by (rewrite <- Hlen, length_app; cbn [length]; lia).
(* a byte of skipn is a later byte of the list *)
assert (NS : forall (l : list Z) m i, nth i (skipn m l) 0 = nth (m + i) l 0).
{ intros l. induction l as [|x l IH]; intros [|m] i; cbn; try reflexivity; try (destruct i; reflexivity). apply IH. }
(* the quotient by 8, bounded (lia never sees the division) *)
assert (D8 : forall z, 0 <= z -> 0 <= z / 8 /\ 8 * (z / 8) <= z < 8 * (z / 8) + 8).
{ intros z Hz. pose proof (Z.div_mod z 8 ltac:(lia)) as E. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as M.
  pose proof (Z.div_pos z 8 Hz ltac:(lia)) as P.
  set (qq := z / 8) in *. set (rr := z mod 8) in *. clearbody qq rr. lia. }
unfold prhWriter_out. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap].
split; [exact Ho8|]. split; [lia|]. split; [lia|].
split; [exact V0|]. split; [rewrite length_app, Nat2Z.inj_add; exact V8|].
split; [exact V16|]. split; [exact V24|]. split; [left; reflexivity|].
split; [unfold WriterSpec.bytes_ok; apply Forall_app; split; [exact Htok | exact (put_bytes_ok_of W1 mem1 s bs Hbs)]|].
right. split; [exact Hgrid|]. split; [exact Hin|]. split; [rewrite length_app; lia|].
split.
- exists (skipn (length bs) rest). split.
  + rewrite !length_app. cbn [length]. rewrite length_skipn. lia.
  + apply put_garr8_of_aview.
    * intros j Hj. rewrite !length_app in Hj. cbn [length] in Hj. rewrite length_skipn in Hj.
      destruct (Nat.lt_ge_cases j (length text)) as [J1 | J1].
      { (* the old text: kept *)
        rewrite Hkeep by lia.
        rewrite (put_garr8_aview W1 mem1 buf' (text ++ r0 :: rest) j Hba) by (rewrite length_app; cbn [length]; lia).
        rewrite (app_nth1 text (r0 :: rest) 0 J1), <- app_assoc.
        rewrite (app_nth1 text (bs ++ 0 :: skipn (length bs) rest) 0 J1). reflexivity. }
      destruct (Nat.lt_ge_cases j (length text + length bs)) as [J2 | J2].
      { (* the copy *)
        replace (buf' + Z.of_nat j) with (buf' + Z.of_nat (length text) + Z.of_nat (j - length text)) by lia.
        rewrite (Hcopy (Z.of_nat (j - length text))) by lia.
        rewrite (put_garr8_aview W1 mem1 s bs (j - length text) Hbs) by lia.
        rewrite (app_nth1 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := j)) by (rewrite length_app; lia).
        rewrite (app_nth2 text bs 0 J1). reflexivity. }
      destruct (Nat.eq_dec j (length text + length bs)) as [J3 | J3].
      { (* the NUL *)
        subst j. rewrite Nat2Z.inj_add, Z.add_assoc, Hnul.
        rewrite (app_nth2 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := length text + length bs))
          by (rewrite length_app; lia).
        rewrite length_app, Nat.sub_diag. reflexivity. }
      { (* the old tail: kept *)
        rewrite Hkeep by lia.
        rewrite (put_garr8_aview W1 mem1 buf' (text ++ r0 :: rest) j Hba) by (rewrite length_app; cbn [length]; lia).
        rewrite (app_nth2 text (r0 :: rest) 0 J1).
        rewrite (app_nth2 (text ++ bs) (0 :: skipn (length bs) rest) 0 (n := j)) by (rewrite length_app; lia).
        rewrite length_app.
        replace (j - length text)%nat with (S (j - length text - 1)) by lia.
        replace (j - (length text + length bs))%nat with (S (j - (length text + length bs) - 1)) by lia.
        cbn [nth]. rewrite NS. f_equal. f_equal. lia. }
    * pose proof (put_bytes_ok_of W1 mem1 buf' _ Hba) as Hob.
      pose proof (put_bytes_ok_of W1 mem1 s bs Hbs) as Hobs.
      unfold WriterSpec.bytes_ok in *.
      apply Forall_app in Hob as [_ Hob]. apply Forall_cons_iff in Hob as [_ Hob].
      rewrite <- (firstn_skipn (length bs) rest) in Hob. apply Forall_app in Hob as [_ Hob].
      apply Forall_app. split; [apply Forall_app; split; [exact Htok | exact Hobs]|].
      constructor; [cbv beta; lia | exact Hob].
- (* the shadow of the buffer lies outside the changed bytes: above a low buffer, below a high one *)
  intros _. split.
  + eapply range_addressable_agree; [|exact Hra]. intros x Hx.
    destruct (D8 x ltac:(lia)) as (Qa & Qb & Qc).
    apply Hkeep; unfold shadow_of_addr, SHADOW_OFF; set (q := x / 8) in *; clearbody q;
      unfold kLowShadowBeg, kHighMemBeg in Hband; destruct Hband; lia.
  + intros s0 Hs0. rewrite Hkeep; [exact (Hhv s0 Hs0) | |];
      unfold shadow_addr, SHADOW_OFF in Hs0;
      destruct (D8 buf' ltac:(lia)) as (Q1a & Q1b & Q1c); set (q1 := buf' / 8) in *; clearbody q1;
      destruct (D8 (buf' + cap' - 1) ltac:(lia)) as (Q2a & Q2b & Q2c);
      set (q2 := (buf' + cap' - 1) / 8) in *; clearbody q2;
      destruct (D8 (2147450880 + q1) ltac:(lia)) as (R1a & R1b & R1c);
      set (r1 := (2147450880 + q1) / 8) in *; clearbody r1;
      destruct (D8 (2147450880 + q2) ltac:(lia)) as (R2a & R2b & R2c);
      set (r2 := (2147450880 + q2) / 8) in *; clearbody r2;
      unfold kLowShadowBeg, kHighMemBeg in Hband; destruct Hband; lia.
Qed.

(* the ledger over a stretch that changes only the user bytes [b, b + k) of one ledger block (and nothing else below
   alloc_ceiling): the statics are image bytes (HPST), no block byte is (YCbqG blk_img_x), and every other ledger head
   is in another block (alx_blocks: the blocks are pairwise disjoint); the head of b itself is below b (HW) *)
Lemma put_ledger_copy : forall ly S Hp (W : world SEGS) mem mem' md Lam peak cnt fail ran b k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown -> In (b, k) Lam ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (b <= a < b + k) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran rmost rown.
Proof.
intros ly S Hp W mem mem' md Lam peak cnt fail ran b k HAR (Hg & Hnd & Hbl & Hperm) Hbk Hkeep.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof HW as HW8. unfold prh_head_wide in HW8.
destruct (proj1 (Forall_forall _ _) Hbl _ Hbk) as (Hk0 & Hinb & _ & _ & _). cbn [fst snd] in Hk0, Hinb.
assert (Hrqb : req_size (k + cf_head) = k + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); cbv iota; lia).
(* the changed bytes are block bytes, so no image byte *)
assert (NIMG : forall a, b <= a < b + k -> ~ in_img SEGS a).
{ intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (k + cf_head) a HAR Hinb).
  rewrite Hrqb. lia. }
assert (VM : forall a (n : nat) v, (forall kk, (kk < n)%nat ->
    0 <= a + Z.of_nat kk < YM05.alloc_ceiling /\ ~ (b <= a + Z.of_nat kk < b + k)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v).
{ intros a n v Hr Hv. eapply (val_mem_kept SEGS (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros kk Hkk. rewrite <- (Z2Nat.id kk) by lia.
  destruct (Hr (Z.to_nat kk) ltac:(lia)) as (Hr1 & Hr2). apply Hkeep; [exact Hr1 | exact Hr2]. }
(* a static's bytes are image bytes below alloc_ceiling *)
assert (ST : forall a (n : nat), (forall kk, (kk < n)%nat -> Exists (in_zr (a + Z.of_nat kk)) (@prh_pst prh_img_A)) ->
  forall kk, (kk < n)%nat -> 0 <= a + Z.of_nat kk < YM05.alloc_ceiling /\ ~ (b <= a + Z.of_nat kk < b + k)).
{ intros a n Hx kk Hkk. pose proof (HPST _ (Hx kk Hkk)) as Hi. pose proof (pa_segs_low _ Hi) as Hl.
  split; [lia|]. intros Hr. exact (NIMG _ Hr Hi). }
destruct Hg as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & Gr).
split; [|split; [exact Hnd | split; [|exact Hperm]]].
- split; [|split; [|split; [|split; [|split; [|split; [split; [|exact G6b]|split; [split; [|exact G7b]|exact Gr]]]]]]].
  all: eapply VM; [apply ST; intros kk Hkk; unfold prh_pst;
    repeat (first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]) |].
  all: first [exact G1 | exact G2 | exact G3 | exact G4 | exact G5 | exact G6 | exact G7].
- eapply Forall_impl; [|exact Hbl]. intros [a k'] (Hk0' & Hin' & HinHp & Ha16 & Hv). cbn [fst snd] in *.
  split; [exact Hk0'|]. split; [exact Hin'|]. split; [exact HinHp|]. split; [exact Ha16|].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin') as (Hp16 & Hp4 & Hpc & _).
  assert (Hrq : req_size (k' + cf_head) = k' + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); cbv iota; lia).
  rewrite Hrq in Hpc.
  eapply VM; [|exact Hv]. intros kk Hkk. split; [lia|].
  destruct (Z.eq_dec a b) as [-> | Hne]; [lia|].
  (* another block: disjoint from b's *)
  assert (Hne2 : (a - cf_head, k' + cf_head) <> (b - cf_head, k + cf_head)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin' Hinb Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, Hrqb in Hd. lia.
Qed.

(* a doubling step of the capacity: `slli a1, a1, 1` on a small value (YI08.v alu64_sll1, for this file) *)
Lemma put_sll1 : forall c, 0 <= c < 2 ^ 62 -> alu64 ALU_SLL (Z_to_bv 64 c) (Z_to_bv 64 1) = Z_to_bv 64 (2 * c).
Proof.
intros c Hc. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small c), (Z.mod_small 1) by lia. change (Z.land 1 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
Qed.

(* ---- THE DOUBLING LOOP (slots 46 .. 48, `mv s6, a1; slli a1, a1, 1; bltu s6, a2`) from a fresh register-only seat:
   no region, no shadow entry (the loop touches no memory); by induction on WriterSpec.dbl's fuel ---- *)
Definition put_ssr (k : Z) : sstate := mkSS k sr_atoms [] None (mkFacts [] [] []).

Lemma put_seat_r : forall k (W1 : world SEGS) (regs1 : bvmap 5 word) mem1,
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (put_ssr k)
    (restrict (w_H W1) (YK11.mkst regs1 (Z_to_bv 64 (BASE + k)) mem1 (YK11.seg_rom SEGS))) /\
  sh_ok SEGS put_Bx [] (Eimg (Ereg regs1 [])) (mrestrict (w_H W1) mem1).
Proof.
intros k W1 regs1 mem1. split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold put_ssr. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

Lemma put_loop_body : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (fuel : nat) (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 c need
    STK sp0 (FP : list (Z * Z)) ly S Hp W mem md lyc Sc Hpc k1 (Q : world SEGS -> config -> Prop),
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem1 md1 k1 ->
  P mem1 ->
  getr regs1 11 = Z_to_bv 64 c -> getr regs1 12 = Z_to_bv 64 need ->
  0 < c <= 2 ^ 29 -> 0 <= need <= 2 ^ 28 -> need <= c * 2 ^ Z.of_nat fuel ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem3 md3 k1 ->
     P mem3 ->
     (forall x, mrestrict (w_H W1) mem3 x = mrestrict (w_H W1) mem1 x) ->
     getr regs3 22 = Z_to_bv 64 (WriterSpec.dbl fuel c need) ->
     getr regs3 11 = Z_to_bv 64 (2 * WriterSpec.dbl fuel c need) ->
     (forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr regs3 r = getr regs1 r) ->
     SRr SEGS W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + PK 49)) mem3 (YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 46)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
induction fuel as [|f IH]; intros W1 regs1 mem1 md1 c need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q
  HJ HPM R11 R12 Hcr Hneed Hfuel HK.
all: destruct (put_seat_r (PK 46) W1 regs1 mem1) as (HS & SHOK).
all: set (E := Eimg (Ereg regs1 [])) in *.
all: assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
all: assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
all: assert (U11 : U E (SOff 11 0) = c) by (apply U_atom; [rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact R11 | lia]).
all: assert (U12 : U E (SOff 12 0) = need)
  by (apply U_atom; [rewrite (EG 12%nat 12%bv) by (lia || reflexivity); exact R12 | lia]).
all: paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [put_awr].
all: psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken BC_LTU _ _ = _ |- _ => rewrite branch_ltu_U, U11, U12 in Hb end.
(* fuel 0 and c < need contradicts need <= c * 2 ^ 0 *)
1: (exfalso; apply Z.ltb_lt in Hc; cbn [Z.of_nat] in Hfuel; rewrite Z.pow_0_r, Z.mul_1_r in Hfuel; lia).
all: [> apply Z.ltb_ge in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 49)
     | apply Z.ltb_lt in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 46)
     | apply Z.ltb_ge in Hc; paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 49) ].
all: try solve [put_awr].
all: pmkst HS.
all: assert (GR : forall rr : bv 5, getr (ms_regs ms0) rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms0 rr HS)).
all: assert (Hreg : regs_ok E sr_atoms regs1) by (subst E; apply regs_ok_Eimg_Ereg).
all: assert (OTH : forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr (ms_regs ms0) r = getr regs1 r)
  by (intros r H11 H22; rewrite GR, (Hreg r); f_equal; unfold sr_get; destruct (bv_eqb r 0); [reflexivity|];
      match goal with |- nth _ ?L _ = nth _ ?L2 _ =>
        let L' := eval vm_compute in L in change L with L';
        let L2' := eval vm_compute in L2 in change L2 with L2' end;
      assert (Hi : (ridx r < 32)%nat) by (unfold ridx; pose proof (u5_range r); lia);
      assert (Hi11 : ridx r <> 11%nat)
        by (intros Hq; apply H11; apply bv_eq; change (bv_unsigned (11%bv : bv 5)) with 11; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      assert (Hi22 : ridx r <> 22%nat)
        by (intros Hq; apply H22; apply bv_eq; change (bv_unsigned (22%bv : bv 5)) with 22; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      generalize (ridx r) Hi Hi11 Hi22; intros i Hi' Hi11' Hi22';
      do 32 (destruct i as [|i]; [first [reflexivity | lia] |]); lia).
all: assert (MEM : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x)
  by (intros x; rewrite (HFr0 x), (HFr x); [reflexivity | |]; intros (r & Hr & _); vm_compute in Hr; destruct Hr).
all: assert (S22 : getr (ms_regs ms0) 22 = Z_to_bv 64 c)
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
      reflexivity).
all: assert (S11 : getr (ms_regs ms0) 11 = Z_to_bv 64 (2 * c))
  by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
      cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
      apply put_sll1; lia).
(* fuel 0, need <= c: the exit *)
1: { apply (HK (ms_regs ms0) (ms_mem ms0) _ HJ HPM MEM); [cbn [WriterSpec.dbl]; exact S22 | cbn [WriterSpec.dbl]; exact S11 | exact OTH]. }
(* fuel S f, c < need: one more doubling, the induction hypothesis at 2 c *)
1: { assert (R12' : getr (ms_regs ms0) 12 = Z_to_bv 64 need)
       by (rewrite OTH; [exact R12 | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq
                                   | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq]).
     apply (IH W1 (ms_regs ms0) (ms_mem ms0) _ (2 * c) need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM S11 R12'
       ltac:(lia) Hneed).
     { replace (2 * c * 2 ^ Z.of_nat f) with (c * 2 ^ Z.of_nat (Datatypes.S f)) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
       exact Hfuel. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - rewrite H22. cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_gt need c) Hc). reflexivity.
     - rewrite H11. cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_gt need c) Hc). reflexivity.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11 Hr22). }
(* fuel S f, need <= c: the exit *)
1: { apply (HK (ms_regs ms0) (ms_mem ms0) _ HJ HPM MEM).
     - cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_le need c) Hc). exact S22.
     - cbn [WriterSpec.dbl]. rewrite (proj2 (Z.leb_le need c) Hc). exact S11.
     - exact OTH. }
Qed.

(* a shadow hull of a window covers the hull of a sub-window (S10TxPut.v tp_hull_sub) *)
Lemma put_hull_sub : forall (rd : reader) p m d k, shadow_hull_vis rd p m -> p <= d -> d + k <= p + m -> 0 < k ->
  shadow_hull_vis rd d k.
Proof.
intros rd p m d k Hh Hpd Hdn Hn s0 Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + k - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* a byte window survives a change that keeps its bytes *)
Lemma put_bytes_keep : forall (W : world SEGS) m m' p l, bytes_at (PA := PA) W m p l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m' (p + Z.of_nat j) = aview SEGS (w_H W) m (p + Z.of_nat j)) ->
  bytes_at (PA := PA) W m' p l.
Proof.
intros W m m' p l H Hk. apply put_garr8_of_aview; [|exact (put_bytes_ok_of W m p l H)].
intros j Hj. rewrite (Hk j Hj). exact (put_garr8_aview W m p l j H Hj).
Qed.

(* newcap's base: 4096 when there is no buffer yet *)
Lemma put_newcap0 : forall need, WriterSpec.newcap 0 need = WriterSpec.dbl 64 4096 need.
Proof. intros need. unfold WriterSpec.newcap. rewrite Z.eqb_refl. reflexivity. Qed.

(* ---- the grow block's head (slot 44 `bnez a1`, the cap = 0 arm `lui a1, 1`) and the doubling loop: from cap and
   need, s6 = newcap cap need and a1 = 2 s6 at slot 49; memory and every other register kept ---- *)
Lemma put_loop : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 cap need
    STK sp0 (FP : list (Z * Z)) ly S Hp W mem md lyc Sc Hpc k1 (Q : world SEGS -> config -> Prop),
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem1 md1 k1 ->
  P mem1 ->
  getr regs1 11 = Z_to_bv 64 cap -> getr regs1 12 = Z_to_bv 64 need ->
  0 <= cap < need -> need <= 2 ^ 28 ->
  (forall (regs3 : bvmap 5 word) mem3 md3,
     ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md [] lyc Sc Hpc W1 mem3 md3 k1 ->
     P mem3 ->
     (forall x, mrestrict (w_H W1) mem3 x = mrestrict (w_H W1) mem1 x) ->
     getr regs3 22 = Z_to_bv 64 (WriterSpec.newcap cap need) ->
     getr regs3 11 = Z_to_bv 64 (2 * WriterSpec.newcap cap need) ->
     (forall r : bv 5, r <> 11%bv -> r <> 22%bv -> getr regs3 r = getr regs1 r) ->
     SRr SEGS W1 (mkCfg (YK11.mkst regs3 (Z_to_bv 64 (BASE + PK 49)) mem3 (YK11.seg_rom SEGS)) md3) Q) ->
  SRr SEGS W1 (mkCfg (YK11.mkst regs1 (Z_to_bv 64 (BASE + PK 44)) mem1 (YK11.seg_rom SEGS)) md1) Q.
Proof.
intros P PLAW.
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
intros W1 regs1 mem1 md1 cap need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM R11 R12 Hcap Hneed HK.
destruct (put_seat_r (PK 44) W1 regs1 mem1) as (HS & SHOK).
set (E := Eimg (Ereg regs1 [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hk Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ kk r Hr)).
assert (U11 : U E (SOff 11 0) = cap) by (apply U_atom; [rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact R11 | lia]).
psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rewrite branch_ne_U, U11, (U_lit E 0 ltac:(lia)) in Hb end.
all: [> destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [discriminate Hc|];
        paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 46)
     | destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [|discriminate Hc];
        paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 46) ].
all: try solve [put_awr].
all: pmkst HS.
all: assert (GR : forall rr : bv 5, getr (ms_regs ms) rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W1) E _ ms rr HS)).
all: assert (Hreg : regs_ok E sr_atoms regs1) by (subst E; apply regs_ok_Eimg_Ereg).
all: assert (OTH : forall r : bv 5, r <> 11%bv -> getr (ms_regs ms) r = getr regs1 r)
  by (intros r H11; rewrite GR, (Hreg r);
      match goal with |- sv_denot _ (sr_get ?L _) = sv_denot _ (sr_get ?L2 _) =>
        let L' := eval vm_compute in L in let L2' := eval vm_compute in L2 in change L with L'; change L2 with L2' end;
      first [ (lazymatch goal with |- ?a = ?a => reflexivity end)
            | (f_equal; unfold sr_get; destruct (bv_eqb r 0); [reflexivity|];
      match goal with |- nth _ ?L _ = nth _ ?L2 _ =>
        let L' := eval vm_compute in L in change L with L';
        let L2' := eval vm_compute in L2 in change L2 with L2' end;
      assert (Hi : (ridx r < 32)%nat) by (unfold ridx; pose proof (u5_range r); lia);
      assert (Hi11 : ridx r <> 11%nat)
        by (intros Hq; apply H11; apply bv_eq; change (bv_unsigned (11%bv : bv 5)) with 11; unfold ridx in Hq;
            pose proof (u5_range r); lia);
      generalize (ridx r) Hi Hi11; intros i Hi' Hi11';
      do 32 (destruct i as [|i]; [first [reflexivity | lia] |]); lia) ]).
all: assert (MEM : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x)
  by (intros x; rewrite (HFr x); [reflexivity|]; intros (r & Hr & _); vm_compute in Hr; destruct Hr).
all: assert (R12' : getr (ms_regs ms) 12 = Z_to_bv 64 need)
  by (rewrite OTH; [exact R12 | intros Hq; apply (f_equal (@bv_unsigned 5)) in Hq; vm_compute in Hq; discriminate Hq]).
(* cap <> 0: the loop from cap *)
1: { assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 cap)
       by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
           cbn [sv_denot]; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r, unsigned_lit_small by lia;
           reflexivity).
     apply (put_loop_body P PLAW 64 W1 (ms_regs ms) (ms_mem ms) _ cap need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ HPM
       R11' R12' ltac:(lia) ltac:(lia)).
     { change (2 ^ Z.of_nat 64) with 18446744073709551616. lia. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - unfold WriterSpec.newcap. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). exact H22.
     - unfold WriterSpec.newcap. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). exact H11.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11). }
(* cap = 0: `lui a1, 1`, the loop from 4096 (U11 names cap too: clear it, or subst would put U E (SOff 11 0) for cap) *)
1: { clear U11. subst cap.
     assert (R11' : getr (ms_regs ms) 11 = Z_to_bv 64 4096)
       by (rewrite GR; match goal with |- sv_denot ?EE ?e = _ => let v := eval vm_compute in e in change e with v end;
           reflexivity).
     apply (put_loop_body P PLAW 64 W1 (ms_regs ms) (ms_mem ms) _ 4096 need STK sp0 FP ly S Hp W mem md lyc Sc Hpc k1 Q HJ
       HPM R11' R12' ltac:(lia) ltac:(lia)).
     { change (2 ^ Z.of_nat 64) with 18446744073709551616. lia. }
     intros regs3 mem3 md3 HJ3 HPM3 HM3 H22 H11 HO3. apply (HK regs3 mem3 md3 HJ3 HPM3).
     - intros x. rewrite HM3. exact (MEM x).
     - rewrite put_newcap0. exact H22.
     - rewrite put_newcap0. exact H11.
     - intros r Hr11 Hr22. rewrite (HO3 r Hr11 Hr22). exact (OTH r Hr11). }
Qed.

(* ---- the grown capacity is on the 4096 * 2 ^ j grid and covers the need ---- *)
Lemma put_dbl_grid : forall f j need, 0 <= j -> need <= 4096 * 2 ^ (j + Z.of_nat f) ->
  exists j', j <= j' /\ WriterSpec.dbl f (4096 * 2 ^ j) need = 4096 * 2 ^ j' /\ need <= 4096 * 2 ^ j'.
Proof.
induction f as [|f IH]; intros j need Hj Hn.
- exists j. cbn [WriterSpec.dbl Z.of_nat] in *. rewrite Z.add_0_r in Hn. split; [lia|]. split; [reflexivity | exact Hn].
- cbn [WriterSpec.dbl]. destruct (Z.leb_spec need (4096 * 2 ^ j)) as [Hle | Hgt].
  + exists j. split; [lia|]. split; [reflexivity | exact Hle].
  + replace (2 * (4096 * 2 ^ j)) with (4096 * 2 ^ (j + 1)) by (rewrite Z.pow_add_r by lia; ring).
    destruct (IH (j + 1) need ltac:(lia)) as (j' & Hj' & E & Hn').
    { replace (j + 1 + Z.of_nat f) with (j + Z.of_nat (Datatypes.S f)) by (rewrite Nat2Z.inj_succ; lia). exact Hn. }
    exists j'. split; [lia|]. split; [exact E | exact Hn'].
Qed.

Lemma put_newcap_grid : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= 2 ^ 28 ->
  (exists j, 0 <= j <= 51 /\ WriterSpec.newcap c need = 4096 * 2 ^ j) /\ need <= WriterSpec.newcap c need /\
  WriterSpec.newcap c need <= 2 ^ 28 /\ c <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn.
pose proof (WriterSpecFacts.newcap_le28 c need Hc Hn) as H28.
assert (G : exists j, 0 <= j /\ c <= 4096 * 2 ^ j /\ WriterSpec.newcap c need = WriterSpec.dbl 64 (4096 * 2 ^ j) need).
{ destruct Hc as [-> | (j & Hj & ->)].
  - exists 0. split; [lia|]. split; [lia|]. unfold WriterSpec.newcap. rewrite Z.eqb_refl. reflexivity.
  - exists j. split; [lia|]. split; [lia|]. unfold WriterSpec.newcap.
    assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
    rewrite (proj2 (Z.eqb_neq _ 0)) by lia. reflexivity. }
destruct G as (j & Hj & Hcj & EG).
assert (Hb : need <= 4096 * 2 ^ (j + Z.of_nat 64)).
{ assert (1 <= 2 ^ j) by (apply Z.pow_le_mono_r with (a := 2) (b := 0) in Hj; lia).
  rewrite Z.pow_add_r by lia. change (2 ^ Z.of_nat 64) with 18446744073709551616. nia. }
destruct (put_dbl_grid 64 j need Hj Hb) as (j' & Hj' & E & Hn'). rewrite <- EG in E.
assert (Hj51 : j' <= 51).
{ destruct (Z_le_gt_dec j' 51) as [H | H]; [exact H|]. exfalso.
  assert (2 ^ 52 <= 2 ^ j') by (apply Z.pow_le_mono_r; lia). lia. }
split; [exists j'; split; [lia | exact E]|]. split; [rewrite E; exact Hn'|]. split; [exact H28|].
rewrite E. assert (2 ^ j <= 2 ^ j') by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* read-only image bytes survive a journal (S7a_indent.v ind_arodata_kept, the same proof) *)
Lemma put_arodata_kept : forall STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k,
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_A) ARx STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros STK sp0 FP ly S Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k HJ Hsk HRO a Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HRO a Hro Hown Herr) | | exact Hown | exact Herr | exact (HPSTRO a Hro) | exact (fp_spares_closed FP a Hsk)].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)].
Qed.

(* ---- fuzz_realloc's post: the text tfuzz_realloc_specX's anonymous post, by its named projection tfrP_Q
   (lib/A/PRH_FnAlloc.v), at the #102 cells rmost / rown: the hull use of the call's all-granted event, the position as
   the post-implication of the call's own events (none on a NULL, HMal / HRe on a block), THE OUTCOME at a consumer
   allocation, the refused arm's world-free evidence, the ledger ---- *)
Definition put_realloc_Q (p k n : Z) (old : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z) ly S (Hp : list Z)
  (W : world SEGS) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran rmost rown.

(* ---- THE ONE CALL OF fuzz_realloc: the text tfuzz_realloc_specX (HREAL) through the engine's call rule at the
   re-hiding relation, aj_call_x_spR at wle' SEGS RZ (the realloc of a live block can hide shadow again). Its premises
   are the callee text's, at the CALL's state (the chain ch1, the room, the two live counts, the hull budget of the
   call's event, the universe, the ledger, the old block, the request, fpre's raZ bound and rounding mode), so a change
   of the text threads through here only. The post is the text's fpostmR: put_realloc_Q and the memnorm keep (fQmn),
   both journals at wle' SEGS RZ. ---- *)
Lemma put_realloc_call : forall
    W E ss ms STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k (o' : Z) raw ch1
    p kk nn (old : list Z) Lam peak cnt fail ran,
  st_ok SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA AS_fuzz_realloc ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) STK sp0 FP ly S Hp W0 mem md [] lyc Sc Hpc W
    (ms_mem ms) mdc k ->
  spZ (ms_regs ms) = sp0 + o' -> o' mod 16 = 0 -> o' <= 0 -> STK_fuzz_realloc - o' <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) (ms_mem ms)) (sp0 + o') (s0Z (ms_regs ms)) ch1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms)) ->
  spZ (ms_regs ms) + 64 <= ly_stk_hi lyc -> raZ (ms_regs ms) < YM05.alloc_ceiling -> YK0o.frm_zero (@YK11.fp_csr fx) ->
  room_live_cf Sc -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt Sc <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 Sc <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget Sc
    (if p =? 0 then [PresetReqAt.HMal (nn + cf_head)] else [PresetReqAt.HRe (kk + cf_head) (nn + cf_head)]) ->
  In [cf_pc_realloc_ra0] (u_fix (as_universe B)) ->
  In (prh_trace cf_pc_realloc_ra0 pi_ret_realloc []) (u_fix (as_universe B)) ->
  getr (ms_regs ms) 10 = w64 p -> getr (ms_regs ms) 11 = w64 nn -> 0 <= nn -> nn + cf_head < cf_malloc_max ->
  prh_ledger B lyc Sc Hpc W (ms_mem ms) Lam peak cnt fail ran rmost rown ->
  (p = 0 /\ kk = 0 /\ old = [] \/ In (p, kk) Lam /\ bytes_at W (ms_mem ms) p old /\ Z.of_nat (length old) = kk) ->
  (cnt <> fail -> blocks_bytes Sc + (nn + cf_head) <= LIVE_MAX) ->
  fp_sub_x B STK sp0 FP (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) ly S [] lyc Sc ->
  SRr' SEGS RZ W (mkCfg ms mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
      c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) STK sp0 FP ly S Hp W0 mem md []
        ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
      ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) STK_fuzz_realloc (sp0 + o')
        (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) lyc Sc Hpc W (ms_mem ms) mdc []
        ly2 S2 Hp2 W2 mem2 md2 k1 /\
      aregs_preserved (ms_regs ms) regs2 /\
      fQmn (ms_mem ms) (put_realloc_Q p kk nn old Lam peak cnt fail ran lyc Sc Hpc W)
        ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W E ss ms STK sp0 FP ly S Hp W0 mem md lyc Sc Hpc mdc k o' raw ch1 p kk nn old
  Lam peak cnt fail ran
  HS Hrv HPC HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hch HRO HTOP HRAZ HFRM HROOM HMU HSEC H24 HHULL HU1 HU2 H10 H11
  Hn0 Hnmax HLED HOLD HLIVE HF.
assert (HK2 : 0 <= STK_fuzz_realloc) by (vm_compute; discriminate).
apply (aj_call_x_spR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low _ _ PA) (wle' SEGS RZ)
  (wle'_refl SEGS RZ) (wle'_trans SEGS RZ) W E ss ms STK sp0 FP ly S Hp W0
  mem md [] lyc Sc Hpc mdc k STK_fuzz_realloc (if p =? 0 then [] else ablocks_fp [(p - cf_head, kk + cf_head)]) o' raw ch1
  (fQmn (ms_mem ms) (put_realloc_Q p kk nn old Lam peak cnt fail ran lyc Sc Hpc W))
  HS Hrv HJ Hsp Hal Hneg HK2 Hbud Hgp Htp Hra Hraw Hra4 Hch);
  [|exact HF].
intros HAPc. rewrite HPC.
exact (HREAL lyc Sc Hpc W (ms_regs ms) (ms_mem ms) mdc ch1 p kk nn old Lam peak cnt fail ran rmost rown
  (conj HAPc (conj HRO (conj HTOP (conj HRAZ HFRM)))) HROOM HMU HSEC H24 HHULL HU1 HU2 H10 H11 Hn0 Hnmax HLED HOLD
  HLIVE).
Qed.

(* ---- fuzz_realloc's post, sorted by the returned a0: NULL, which with the call's event and consumer window given
   (cnt <> fail) is only the allocation set to fail (the text's outcome clause excludes a refusal: DEAD-PUT), with
   blocks as the entry's, the old buffer's bytes kept, the ledger as the text states it, the position at rp_i with
   SOME history; or a new block res (in the allocator's range; the position advances by one when the run's event at
   rp_i is this call's) ---- *)
Lemma put_realloc_cases : forall (rp_sm : list Z -> Z * Z) (rp_x : list Z)
    (rp_os : list (option nat * option nat * option nat)) (rp_H0 : list Z) (rp_i : nat) (rp_hist : list YG00.chunk)
    buf cap nc (old : list Z) Lam peak cnt fail ran ly S Hp (W : world SEGS)
    ly2 S2 Hp2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (buf = 0 /\ cap = 0 /\ old = [] \/ buf <> 0 /\ cap <> 0) -> 0 <= cap < nc ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* the call's own event and its consumer window, when it is not the allocation set to fail (put's entry premises
     HEV and HCONS give both) *)
  (cnt <> fail -> PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i
     [if cap =? 0 then PresetReqAt.HMal (nc + cf_head) else PresetReqAt.HRe (cap + cf_head) (nc + cf_head)] /\
   PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 1) ->
  put_realloc_Q buf cap nc old Lam peak cnt fail ran ly S Hp W ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  room_live_cf S2 /\
  ((bv_unsigned (getr regs2 10) = 0 /\ Permutation Hp2 Hp /\ ablocks B ly2 S2 = ablocks B ly S /\
    (buf <> 0 -> bytes_at W2 mem2 buf old) /\
    (cnt = fail /\ prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ ran rmost rown) /\
    exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S2)
   \/
   (exists res, bv_unsigned (getr regs2 10) = res /\ cnt <> fail /\
    4096 + cf_head <= res /\ res mod 16 = 0 /\ res + nc <= YM05.alloc_ceiling /\
    exists l1 l2 b1 b2,
      ((cap = 0 /\ l1 = [] /\ l2 = Lam /\ b1 = [] /\ b2 = ablocks B ly S) \/
       (cap <> 0 /\ Lam = l1 ++ (buf, cap) :: l2 /\ ablocks B ly S = b1 ++ (buf - cf_head, cap + cf_head) :: b2)) /\
      Permutation (ablocks B ly2 S2) ((res - cf_head, nc + cf_head) :: b1 ++ b2) /\
      (exists rest, bytes_at W2 mem2 res (firstn (Z.to_nat (Z.min cap nc)) old ++ rest) /\
         Z.of_nat (length rest) = nc - Z.min cap nc) /\
      range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF res nc /\
      (0 < nc -> shadow_hull_vis (aview SEGS (w_H W2) mem2) res nc) /\
      ~ In res (map fst (l1 ++ l2)) /\
      prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, nc) :: l1 ++ l2) (Z.max peak (Ledger.lsum (l1 ++ l2) + nc))
        ((cnt + 1) mod 2 ^ 64) fail ran rmost rown /\
      (nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i =
         Some (if cap =? 0 then PresetReqAt.HMal (nc + cf_head) else PresetReqAt.HRe (cap + cf_head) (nc + cf_head)) ->
       exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S2))).
Proof.
intros rp_sm rp_x rp_os rp_H0 rp_i rp_hist buf cap nc old Lam peak cnt fail ran ly S Hp W ly2 S2 Hp2 W2 regs2 mem2 md2
  HAR2 Hbc Hnc HPOS HCF (res & Hres & HR2 & _ & HP0 & HPM & HPR & HOM & HOR & HARMS).
(* THE OUTCOME: with the call's event and consumer window (cnt <> fail), fuzz_realloc did not return NULL *)
assert (HNR : cnt <> fail -> res <> 0).
{ intros Hcf. destruct (HCF Hcf) as (Hrun & Hcons).
  destruct Hbc as [(Hb0 & Hc0 & _) | (Hb0 & Hc0)].
  - rewrite (proj2 (Z.eqb_eq _ _) Hc0) in Hrun.
    exact (proj1 (HOM Hb0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS Hrun Hcons Hcf)).
  - rewrite (proj2 (Z.eqb_neq _ _) Hc0) in Hrun.
    exact (proj1 (HOR Hb0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS Hrun Hcons Hcf)). }
(* the position after a NULL (no event) and after a block (the call's one event at rp_i) *)
assert (HPN : res = 0 -> exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 hist' S2).
{ intros Hr0. destruct (HP0 Hr0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS eq_refl) as (h & Hh).
  exists h. rewrite Nat.add_0_r in Hh. exact Hh. }
assert (HPG : forall e, (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z)
    (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [e] ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [e])%nat H0 hist' S2) -> res <> 0 ->
  nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some e ->
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os (Datatypes.S rp_i) rp_H0 hist' S2).
{ intros e Hq Hr HE. destruct (Hq Hr rp_sm rp_x rp_os rp_i rp_H0 rp_hist HPOS (proj2 (prh_run_at_one _ _ _ _ _) HE))
    as (h & Hh).
  exists h. cbn [length] in Hh. rewrite Nat.add_1_r in Hh. exact Hh. }
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U0 : res = 0 -> bv_unsigned (getr regs2 10) = 0) by (intros ->; rewrite Hres; vm_compute; reflexivity).
assert (UB : forall b n', In (b, n') (ablocks B ly2 S2) -> b = res - cf_head -> n' = nc + cf_head ->
  bv_unsigned (getr regs2 10) = res /\ res + nc <= YM05.alloc_ceiling).
{ intros b n' Hin -> ->. destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin) as (_ & H4 & Hc & _).
  assert (Hreq : req_size (nc + cf_head) = nc + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0); cbv iota; lia).
  rewrite Hreq in Hc. split; [|lia]. rewrite Hres. apply unsigned_lit_small. lia. }
split; [exact HR2|].
destruct HARMS as [(Hp0 & HAP) | [(Hp0 & Hcf & Hr0 & EHp & Ebl & Hba & HL) |
  [(Hp0 & Hcf & Hr0 & PHp & Ebl & Hba & _ & _ & HL) |
   (Hp0 & Hcf & Hr4 & Hr16 & l1 & l2 & EL & Hnin & EHp & (b1 & b2 & Eb & _ & Pb) & (rest & Hlr & Hbr) & Hra & Hhv & HL)]]].
- destruct Hbc as [(Hb0 & Hc0 & Ho0) | (Hb0 & _)]; [|contradiction].
  unfold prh_alloc_post in HAP.
  destruct HAP as [(Hcf & Hr0 & EHp & Ebl & HL) | [(Hcf & Hr0 & EHp & Ebl & _ & _ & HL) |
    (Hcf & Hr4 & Hr16 & Hnin & EHp & Ebl & Hra & Hhv & (l & Hll & Hbl) & HL)]].
  + left. split; [exact (U0 Hr0)|]. split; [rewrite EHp; apply Permutation_refl|]. split; [exact Ebl|].
    split; [intros H; contradiction | split; [split; [exact Hcf | exact HL] | exact (HPN Hr0)]].
  + exfalso. exact (HNR Hcf Hr0).
  + right. destruct (UB (res - cf_head) (nc + cf_head)) as (Ur & Hrc); [rewrite Ebl; apply in_or_app; right; left; reflexivity | reflexivity | reflexivity |].
    exists res. split; [exact Ur|]. split; [exact Hcf|]. split; [lia|]. split; [exact Hr16|]. split; [exact Hrc|].
    exists [], Lam, [], (ablocks B ly S). split; [left; repeat split; assumption|].
    split; [rewrite Ebl; cbn [app]; apply Permutation_sym, Permutation_cons_append|].
    split; [exists l; rewrite Ho0, Hc0, firstn_nil; cbn [app]; split; [exact Hbl | lia]|].
    split; [exact Hra|]. split; [exact Hhv|]. split; [exact Hnin|]. split; [exact HL|].
    intros HE. rewrite Hc0 in HE. exact (HPG _ (fun Hr => HPM Hr Hp0) ltac:(lia) HE).
- left. split; [exact (U0 Hr0)|]. split; [rewrite EHp; apply Permutation_refl|]. split; [exact Ebl|].
  split; [intros _; exact Hba | split; [split; [exact Hcf | exact HL] | exact (HPN Hr0)]].
- exfalso. exact (HNR Hcf Hr0).
- right. destruct (UB (res - cf_head) (nc + cf_head)) as (Ur & Hrc);
    [apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity | reflexivity | reflexivity |].
  exists res. split; [exact Ur|]. split; [exact Hcf|]. split; [lia|]. split; [exact Hr16|]. split; [exact Hrc|].
  destruct Hbc as [(Hb0 & _) | (_ & Hc0)]; [contradiction|].
  exists l1, l2, b1, b2. split; [right; split; [exact Hc0|]; split; [exact EL | exact Eb]|].
  split; [exact Pb|]. split; [exists rest; split; [exact Hbr | exact Hlr]|].
  split; [exact Hra|]. split; [exact Hhv|]. split; [exact Hnin|]. split; [exact HL|].
  intros HE. rewrite (proj2 (Z.eqb_neq _ _) Hc0) in HE. exact (HPG _ (fun Hr => HPR Hr Hp0) ltac:(lia) HE).
Qed.

(* the model of a put that grows and whose fuzz_realloc returns NULL (outcome false): failed, text and cap kept *)
Lemma put_null_model : forall (st : WriterApp.wst) bs,
  WriterApp.w_failed st = 0 -> WriterApp.w_cap st < prhWriter_need st bs ->
  prhWriter_putN [false] st [bs] =
    WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64)
      (if WriterApp.w_cnt st =? WriterApp.w_fail st then 2 ^ 64 - 1 else WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]) /\
  prhWriter_k [false] st [bs] = 1%nat.
Proof.
intros st bs Hf Hc.
assert (Hg : prhWriter_grows st bs = true)
  by (unfold prhWriter_grows; rewrite Hf; cbn [Z.eqb andb]; apply Z.ltb_lt; exact Hc).
assert (E : prhWriter_putN [false] st [bs] =
    WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64)
      (if WriterApp.w_cnt st =? WriterApp.w_fail st then 2 ^ 64 - 1 else WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)])).
{ cbn [prhWriter_putN]. rewrite Hg. cbn [hd tl prhWriter_putN]. unfold prhWriter_put1. rewrite Hg.
  destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); reflexivity. }
split; [exact E|]. unfold prhWriter_k. rewrite E. cbn [WriterApp.w_calls]. rewrite length_app. cbn [length]. lia.
Qed.

(* ---- the memcpy source after fuzz_realloc (FuzzStrdup.v's sd_src_kept / sd_src_shadow / sd_src_disj, over ARx with
   LAWS and put's homes) ---- *)
(* fuzz_grant GrantRo.v ro_hull's arithmetic (FuzzStrdup.v sd_hull_img, the same proof) *)
Lemma put_hull_img : forall a n s0, 0 < n -> IMG_LO + 64 <= a -> a + n + 64 <= IMG_TOP ->
  shadow_addr a / 8 * 8 <= s0 < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s0 = shadow_addr (8 * (s0 - SHADOW_OFF)) /\ IMG_LO <= 8 * (s0 - SHADOW_OFF) < IMG_TOP.
Proof.
intros a n s0 Hn Hlo Hhi Hs. unfold IMG_LO, IMG_TOP in *. unfold shadow_addr in *.
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
unfold SHADOW_OFF in *.
split; [rewrite Z.mul_comm, Z.div_mul by lia; lia | lia].
Qed.
Lemma put_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a registered zero-shadow global's bytes are addressable in every ARx state (zero-shadow law, HZSA) *)
Lemma put_zs_ra : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 q m,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> In (q, m) (as_zero_shadow B) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF q m.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 q m HAR Hin.
pose proof (proj1 (Forall_forall _ _) HZSA (q, m) Hin) as (Hq & Hm). cbn [fst snd] in Hq, Hm.
pose proof (alx_zshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (q, m) HAR
  ltac:(unfold zero_shadow_ranges; right; exact Hin)) as Hz.
cbn [fst snd] in Hz.
exact (zero_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF q m Hq Hm Hz).
Qed.

Lemma put_src_after : forall ly S Hp (W : world SEGS) mem md memc mdc ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1 sp1
    Lam peak cnt fail ran buf cap s (bs : list Z) n res nc l1 l2 peak2 cnt2 fail2 ran2,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran rmost rown ->
  src_rd (PA := PA) W mem s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B ly S Lam buf cap s n ->
  (forall cid pos, In (cid, pos) (frames S) -> 0 <= cid) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
  ajournal_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) STK_fuzz_realloc sp1
    (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (cap = 0 /\ buf = 0 /\ l1 = [] /\ l2 = Lam \/ cap <> 0 /\ Lam = l1 ++ (buf, cap) :: l2) ->
  In (res - cf_head, nc + cf_head) (ablocks B ly2 S2) -> ~ In (res - cf_head, nc + cf_head) (ablocks B ly S) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, nc) :: l1 ++ l2) peak2 cnt2 fail2 ran2 rmost rown ->
  0 < nc ->
  bytes_at (PA := PA) W2 mem2 s bs /\
  (forall a, s <= a < s + n -> aview SEGS (w_H W2) mem2 a <> None) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W2) mem2) s n) /\
  (res + nc <= s \/ s + n <= res \/ n = 0).
Proof.
intros ly S Hp W mem md memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 sp1 Lam peak cnt fail ran buf cap s bs n res nc l1 l2
  peak2 cnt2 fail2 ran2 HAR HLED HSRC Hn HHOME HFSZ KLOWc HJin Harm HinN HnotN HL2 Hnc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch0.
pose proof HSRC as (Sba & S4096 & Sceil & Samr & Sra & Shull). rewrite Hn in Sceil, Samr, Sra, Shull.
pose proof (ajxR_ar HJin) as HAR2. pose proof (ajxR_ly HJin) as Hly2. pose proof (ajxR_frs HJin) as Hfr2.
pose proof (ajxR_hi HJin) as G1. pose proof (ajxR_blk HJin) as G2. pose proof (ajxR_img HJin) as G3.
pose proof (ajxR_frm HJin) as G4.
destruct (alx_layout SEGS B ARx LAWS ly S Hp W mem md ly2 HAR Hly2) as (_ & Efa & _).
pose proof HLED as (_ & Hnd & Hbl & _).
assert (Hreqn : req_size (nc + cf_head) = nc + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0); cbv iota; lia).
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
{ destruct bs as [|b0 bs']; [|cbn in Hn; lia]. cbn in Hn. subst n.
  split; [apply put_garr8_of_aview; [intros j Hj; cbn in Hj; lia | exact (put_bytes_ok_of W mem s [] Sba)]|].
  split; [intros a Ha; lia|]. split; [intros x Hx; lia|]. split; [intros H; lia|]. right; right; reflexivity. }
assert (Hnp : 0 < n) by lia.
(* the old buffer's block, when there is one, and the call's footprint *)
assert (HOLDB : buf <> 0 -> cap <> 0 /\ In (buf, cap) Lam /\ In (buf - cf_head, cap + cf_head) (ablocks B ly S) /\
  4096 <= buf - cf_head /\ req_size (cap + cf_head) = cap + cf_head).
{ intros Hb0. destruct Harm as [(_ & Hb0' & _) | (Hc0 & ELam)]; [contradiction|].
  assert (HinO : In (buf, cap) Lam) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Hbl (buf, cap) HinO) as (Hk0 & HabO & _). cbn [fst snd] in Hk0, HabO.
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HabO) as (_ & H4 & _).
  split; [exact Hc0|]. split; [exact HinO|]. split; [exact HabO|]. split; [exact H4|].
  unfold req_size; destruct (Z.eqb_spec (cap + cf_head) 0); cbv iota; lia. }
assert (HSK : ~ YI16.sink_open_fp (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)])).
{ destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [intros (r & [] & _)|].
  destruct (HOLDB Hb0) as (_ & _ & _ & H4 & _). apply sink_closed_pos. constructor; [cbn; lia | constructor]. }
destruct HHOME as (Hk & Hdisj).
assert (CASES : (forall a, s <= a < s + n -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF s n /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) s n /\ (res + nc <= s \/ s + n <= res)).
{ destruct Hk as [[(b & m & HinL & Hbs & Hbm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] |
    (cid & pos & Hfin & Hfs & Hfe)].
  - (* a live harness block other than the buffer *)
    pose proof (proj1 (Forall_forall _ _) Hbl (b, m) HinL) as (Hm0 & Hab & Hhp & Hb16 & _). cbn [fst snd] in *.
    assert (Hreq : req_size (m + cf_head) = m + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); cbv iota; lia).
    assert (HinL2 : In (b, m) (l1 ++ l2)).
    { destruct Harm as [(Hc0 & Hb0 & -> & ->) | (Hc0 & ELam)]; [exact HinL|].
      rewrite ELam in HinL. apply in_app_or in HinL as [H | [E | H]];
        [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
      inversion E; subst. destruct Hdisj as [Hz | [H1 | H1]]; lia. }
    pose proof HL2 as (_ & _ & Hbl2 & _).
    pose proof (proj1 (Forall_forall _ _) Hbl2 (b, m) (or_intror HinL2)) as (_ & Hab2 & Hhp2 & _). cbn [fst snd] in *.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & Hb4 & Hbc & _). rewrite Hreq in Hbc.
    assert (NFP : forall a, b - cf_head <= a < b + m ->
      ~ inFP (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) a).
    { intros a Ha (r & Hr & Hra).
      destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [destruct Hr|].
      destruct (HOLDB Hb0) as (Hc0 & HinO & HabO & _ & HreqO).
      cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra. rewrite HreqO in Hra.
      assert (Hne : (b - cf_head, m + cf_head) <> (buf - cf_head, cap + cf_head)).
      { intros E. inversion E as [[E1 E2]]. assert (Ebb : b = buf) by lia. subst b.
        destruct Harm as [(Hc0' & _) | (_ & ELam)]; [contradiction|].
        rewrite ELam, map_app in Hnd. cbn [map] in Hnd. apply NoDup_ListNoDup in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
        rewrite <- map_app. apply in_map_iff. exists (buf, m). split; [reflexivity | exact HinL2]. }
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab HabO Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, HreqO in Hd. lia. }
    split.
    { intros a Ha. replace a with (b - cf_head + (a - (b - cf_head))) by lia.
      rewrite (G2 (b - cf_head) (m + cf_head) (a - (b - cf_head)) Hab Hab2 ltac:(rewrite Hreq; lia)
        ltac:(apply NFP; lia)).
      apply KLOWc. lia. }
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (b - cf_head) (m + cf_head) HAR2 Hab2 Hhp2)
      as (Hbsh & Hhv).
    rewrite Hreq in Hbsh, Hhv. replace (b - cf_head + cf_head) with b in Hbsh, Hhv by lia.
    replace (m + cf_head - cf_head) with m in Hbsh, Hhv by lia.
    split; [exact (block_shadow_range (aview SEGS (w_H W2) mem2) SHADOW_OFF b m s n Hbsh Hbs Hbm)|].
    split; [exact (put_hull_sub _ b m s n (Hhv ltac:(lia)) Hbs Hbm Hnp)|].
    assert (Hne2 : (b - cf_head, m + cf_head) <> (res - cf_head, nc + cf_head))
      by (intros E; rewrite E in Hab; exact (HnotN Hab)).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hab2 HinN Hne2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hreqn in Hd. lia.
  - (* a registered zero-shadow read-only global *)
    split.
    { intros a Ha. destruct (Hro a Ha) as (Hr & Hown & Herr).
      rewrite (G3 a (put_ro_img a Hr) Hown Herr (HPSTRO a Hr) (fp_spares_closed _ a HSK)).
      apply KLOWc. pose proof (@pa_segs_low _ _ PA a (put_ro_img a Hr)). lia. }
    split.
    { destruct Hzs as (q & mq & Hinq & Hq1 & Hq2).
      apply (range_addressable_sub _ _ q mq s n); [exact (put_zs_ra ly2 S2 Hp2 W2 mem2 md2 q mq HAR2 Hinq) | lia | lia]. }
    split.
    { intros s0 Hs0. destruct (put_hull_img s n s0 Hnp ltac:(destruct HPAB; lia) ltac:(destruct HPAB; lia) Hs0)
        as (E & Hr). rewrite E.
      exact (HIMGSH ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr). }
    destruct (Z_le_gt_dec (res + nc) s) as [h | h]; [left; exact h|].
    destruct (Z_le_gt_dec (s + n) res) as [h' | h']; [right; exact h'|].
    exfalso. set (x := Z.max s res).
    assert (Hxs : s <= x < s + n) by (unfold x; lia).
    assert (Hxr : res - cf_head <= x < res - cf_head + req_size (nc + cf_head)) by (rewrite Hreqn; unfold x; lia).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 HinN Hxr (put_ro_img x (proj1 (Hro x Hxs)))).
  - (* an image string with its exact shadow (route (a)) *)
    split.
    { intros a Ha. destruct (Hro a Ha) as (Hr & Hown & Herr & _).
      rewrite (G3 a (put_ro_img a Hr) Hown Herr (HPSTRO a Hr) (fp_spares_closed _ a HSK)).
      apply KLOWc. pose proof (@pa_segs_low _ _ PA a (put_ro_img a Hr)). lia. }
    split.
    { intros x Hx. destruct (Hro x Hx) as (_ & _ & _ & [Hzs | (v & Hcell & Hv)]).
      - destruct Hzs as (q & mq & Hinq & Hq1 & Hq2). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
        exact (put_zs_ra ly2 S2 Hp2 W2 mem2 md2 q mq HAR2 Hinq x ltac:(lia)).
      - exists v. split; [|unfold saddr_ok; lia].
        pose proof (alx_const_cells SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 HAR2) as HC.
        pose proof (proj1 (Forall_forall _ _) HC _ (Hcell ly2)) as Hh.
        unfold cell_holds, z1, c1 in Hh. cbn [c_at c_val c_w aeval] in Hh.
        specialize (Hh 0%nat ltac:(lia)). rewrite Z.add_0_r in Hh.
        unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). rewrite Hh. f_equal.
        unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
        pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
        rewrite (Z.mod_small v (2 ^ 8)) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
    split.
    { intros s0 Hs0. destruct (put_hull_img s n s0 Hnp ltac:(destruct HPAB; lia) ltac:(destruct HPAB; lia) Hs0)
        as (E & Hr). rewrite E.
      exact (HIMGSH ly2 S2 Hp2 W2 mem2 md2 _ HAR2 Hr). }
    destruct (Z_le_gt_dec (res + nc) s) as [h | h]; [left; exact h|].
    destruct (Z_le_gt_dec (s + n) res) as [h' | h']; [right; exact h'|].
    exfalso. set (x := Z.max s res).
    assert (Hxs : s <= x < s + n) by (unfold x; lia).
    assert (Hxr : res - cf_head <= x < res - cf_head + req_size (nc + cf_head)) by (rewrite Hreqn; unfold x; lia).
    exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ x HAR2 HinN Hxr (put_ro_img x (proj1 (Hro x Hxs)))).
  - (* a live fake frame of the entry *)
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hf4 & Hfc & Hfapp).
    destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hf32 & _).
    pose proof (HFSZ cid pos Hfin) as Hcid.
    assert (Hfb : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (H2c : 1 <= 2 ^ cid) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    assert (Hfs8 : 8 <= fs_frame_bytes cid) by lia.
    assert (Hfm8 : fs_frame_bytes cid mod 8 = 0)
      by (rewrite Hfb; replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring; apply Z_mod_mult).
    set (fa := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *.
    assert (NFPf : forall a, fa <= a < fa + fb \/ (kLowShadowBeg <= a < kHighMemBeg) ->
      ~ inFP (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, cap + cf_head)]) a).
    { intros a Ha (r & Hr & Hra).
      destruct (Z.eqb_spec buf 0) as [Hb0 | Hb0]; [destruct Hr|].
      destruct (HOLDB Hb0) as (Hc0 & HinO & HabO & _ & HreqO).
      cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hra. rewrite HreqO in Hra.
      destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR HabO) as (_ & _ & _ & HappO & _).
      rewrite HreqO in HappO.
      pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR HabO Hfin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqO in Hd. fold fa fb in Hd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
    split.
    { intros a Ha.
      rewrite (G4 cid pos a Hfin ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold fa fb; lia)
        ltac:(apply NFPf; left; lia)).
      apply KLOWc. lia. }
    split.
    { intros x Hx. destruct (Sra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok]. rewrite <- Hv.
      set (qx := x / 8). set (qa := fa / 8). set (qf := fb / 8).
      assert (Hf8 : fa mod 8 = 0).
      { pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Hf32, Z.add_0_r in D. rewrite D.
        replace (32 * (fa / 32)) with ((4 * (fa / 32)) * 8) by ring. apply Z_mod_mult. }
      assert (Eqa : fa = 8 * qa) by (unfold qa; pose proof (Z.div_mod fa 8 ltac:(lia)); lia).
      assert (Eqf : fb = 8 * qf) by (unfold qf; pose proof (Z.div_mod fb 8 ltac:(lia)); lia).
      assert (Hqx : 8 * qx <= x < 8 * qx + 8)
        by (unfold qx; pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
      assert (Esh : shadow_of_addr SHADOW_OFF x = SHADOW_OFF + qx) by reflexivity.
      clearbody qx qa qf.
      rewrite Esh.
      rewrite (G4 cid pos (SHADOW_OFF + qx) Hfin).
      - apply KLOWc. unfold SHADOW_OFF. lia.
      - right. unfold in_zr, shadow_addr. cbn [fst snd]. fold fa fb. rewrite Eqa, Eqf.
        rewrite (Z.mul_comm 8 qa), (Z.mul_comm 8 qf), !Z.div_mul by lia. lia.
      - apply NFPf. right. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF. lia. }
    split.
    { assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hfin).
      pose proof (HFRSH ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 HinF2) as Hh. rewrite Efa in Hh. fold fa fb in Hh.
      exact (put_hull_sub _ fa fb s n Hh Hfs Hfe Hnp). }
    assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hfin).
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 HinN HinF2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqn, Efa in Hd. fold fa fb in Hd. lia. }
destruct CASES as (KEEPS & RA & HULL & DISJ).
assert (BYTES : bytes_at (PA := PA) W2 mem2 s bs).
{ apply put_garr8_of_aview; [|exact (put_bytes_ok_of W mem s bs Sba)].
  intros j Hj. rewrite KEEPS by lia. exact (put_garr8_aview W mem s bs j Sba Hj). }
split; [exact BYTES|].
split; [intros a Ha; rewrite KEEPS by exact Ha; replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia;
  rewrite (put_garr8_aview W mem s bs (Z.to_nat (a - s)) Sba ltac:(lia)); discriminate|].
split; [exact RA|]. split; [intros _; exact HULL|]. destruct DISJ as [D | D]; [left; exact D | right; left; exact D].
Qed.

(* a block's application range gives the ASan range of a window inside it, and its band (no unfolding in a large
   context: lia would split every in_app there) *)
Lemma put_app_amem : forall p m q k, in_app p m -> p <= q -> 0 <= k -> q + k <= p + m -> amem_range q k.
Proof.
intros p m q k (H1 & H2) Hq Hk Hqk. pose proof (@ASAN_CEIL_range rc) as (HC & _).
unfold amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
Lemma put_app_band : forall b c h, in_app (b - h) (c + h) -> 0 <= h -> b + c <= kLowShadowBeg \/ kHighMemBeg <= b.
Proof. intros b c h (H1 & [H2 | (H2 & H3)]) Hh; [left; lia | right; lia]. Qed.

(* ---- the grown buffer's block is new: a symmetric pairwise relation survives a permutation, and the block list
   after fuzz_realloc holds the new block once ---- *)
Lemma put_pairwise_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros X R Hsym l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' HP1 IH1 HP2 IH2]; cbn; intros H.
- exact I.
- destruct H as (Hf & Hp). split; [|exact (IH Hp)].
  apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) Hf). exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as (Hf1 & Hf2 & Hp). apply Forall_cons_iff in Hf1 as (Hyx & Hf1).
  split; [constructor; [apply Hsym; exact Hyx | exact Hf2] | split; [exact Hf1 | exact Hp]].
- exact (IH2 (IH1 H)).
Qed.

Lemma put_newblk : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 (bl0 b1 b2 : list (Z * Z)) x old,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 < snd x ->
  Permutation (ablocks B ly2 S2) (x :: b1 ++ b2) ->
  (bl0 = b2 /\ b1 = [] \/ bl0 = b1 ++ old :: b2 /\ old <> x) ->
  ~ In x bl0.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 bl0 b1 b2 x old HAR Hx Pb Hbl Hin.
assert (Hinx : In x (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity).
destruct x as [p n]. cbn [snd] in Hx.
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p n HAR Hinx) as (_ & _ & _ & _ & _ & Hpw).
pose proof (put_pairwise_perm zdisjoint (fun a b H => ltac:(unfold zdisjoint in *; lia)) _ _
  (Permutation_map (fun b : Z * Z => (fst b, req_size (snd b))) Pb) Hpw) as Hpw'.
cbn [map pairwise] in Hpw'. destruct Hpw' as (Hf & _).
assert (Hnot : ~ In (p, n) (b1 ++ b2)).
{ intros H. pose proof (proj1 (Forall_forall _ _) Hf (p, req_size n)
    (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (p, n) H)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); cbv iota; lia). lia. }
destruct Hbl as [(-> & ->) | (-> & Hne)]; [exact (Hnot Hin)|].
apply in_app_or in Hin as [H | [E | H]];
  [apply Hnot; apply in_or_app; left; exact H | exact (Hne E) | apply Hnot; apply in_or_app; right; exact H].
Qed.

(* the model of a put that grows and whose fuzz_realloc returns a block (outcome true, not the one set to fail) *)
Lemma put_grow_model : forall (st : WriterApp.wst) bs,
  WriterApp.w_failed st = 0 -> WriterApp.w_cap st < prhWriter_need st bs ->
  WriterApp.w_cnt st <> WriterApp.w_fail st ->
  prhWriter_putN [true] st [bs] =
    WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs))
      ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]) /\
  prhWriter_k [true] st [bs] = 1%nat.
Proof.
intros st bs Hf Hc Hcf.
assert (Hg : prhWriter_grows st bs = true)
  by (unfold prhWriter_grows; rewrite Hf; cbn [Z.eqb andb]; apply Z.ltb_lt; exact Hc).
assert (E : prhWriter_putN [true] st [bs] =
    WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs))
      ((WriterApp.w_cnt st + 1) mod 2 ^ 64) (WriterApp.w_fail st)
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)])).
{ cbn [prhWriter_putN]. rewrite Hg. cbn [hd tl prhWriter_putN]. unfold prhWriter_put1. rewrite Hg.
  rewrite (proj2 (Z.eqb_neq _ _) Hcf). reflexivity. }
split; [exact E|]. unfold prhWriter_k. rewrite E. cbn [WriterApp.w_calls]. rewrite length_app. cbn [length]. lia.
Qed.

(* the run events of one put that grows and is not the allocation set to fail: its one event (the batch kit's prhWriter_evs) *)
Lemma put_evs1 : forall (st : WriterApp.wst) bs,
  prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
  prhWriter_evs [] st [bs] = [prhWriter_ev st bs].
Proof.
intros st bs Hg Hcf. cbn [prhWriter_evs]. rewrite Hg, (proj2 (Z.eqb_neq _ _) Hcf).
cbn [hd tl negb orb app prhWriter_evs]. reflexivity.
Qed.

(* the live bytes before a run's first event are the allocator's live request bytes (PRH_Base.prh_live_at at j = 0;
   rs_live (room_of_cf S) is map snd (blocks S) by definition, CfRoomLivePreset.rs_live_blocks) *)
Lemma put_live_at0 : forall (S : astate) (E : list PresetReqAt.hev), prh_live_at S E 0%nat = blocks_bytes S.
Proof.
intros S E. unfold prh_live_at, PresetReqAt.hlive_from. rewrite List.firstn_O. cbn [List.fold_left].
change (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) with (map snd (blocks S)).
unfold blocks_bytes, blocks. rewrite map_map. cbn [snd].
induction (st_chunks S) as [|k l IH]; [reflexivity|].
cbn [List.filter List.fold_right]. destruct (is_alloc k); cbn [List.map List.fold_right]; rewrite IH; reflexivity.
Qed.

Section rp.
(* the position interface the text carries (the batch kit's e45217a4c7ba, PRH_FnWriter.v tput_specX; the leaf
   lib/Spec/PresetRoomPos.v): fixed through put's walk, only the index and the history advance *)
Variable rp_sm : list Z -> Z * Z.
Variable rp_x : list Z.
Variable rp_os : list (option nat * option nat * option nat).
Variable rp_H0 : list Z.

(* the post of the text tput_specX, by its named projection tputP_Q (lib/A/PRH_FnWriter.v), at the section's
   position interface and the #102 cells rmost / rown: the position per arm, keyed on the failed field at o + 24
   (f' = 0 granted, f' = 1 the chosen failure, with SOME history), and prhWriter_ret_ok under outcomes with no refusal *)
Definition put_post (rp_i : nat) (rp_hist : list YG00.chunk) ly S Lam peak ran o buf (st : WriterApp.wst) (bs : list Z) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tputP_Q B rp_sm rp_x rp_os rp_i rp_H0 rp_hist rmost rown ly S o buf st bs Lam peak ran.
(* with the segment's memory invariant P on the end memory (the generic-P form) *)
Definition put_postP (P : (word -> option byte) -> Prop) (rp_i : nat) (rp_hist : list YG00.chunk) ly S Lam peak ran o
  buf (st : WriterApp.wst) (bs : list Z) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    put_post rp_i rp_hist ly S Lam peak ran o buf st bs ly' S' Hp' W' regs' mem' md' /\ P mem'.

(* the failed field holds one value: a stored 1 is not a 0 (one byte decides) *)
Lemma put_val_mem_1 : forall (m : word -> option byte) a f, val_mem SEGS m a 4 f -> val_mem SEGS m a 4 1 -> f <> 0.
Proof.
intros m a f Hf H1 ->.
pose proof (Hf 0%nat ltac:(lia)) as B0. pose proof (H1 0%nat ltac:(lia)) as B1.
rewrite B0 in B1. injection B1 as B1. revert B1.
(* a closed goal: two literal bytes *)
vm_compute. intro B1. discriminate B1.
Qed.

(* ---- ARM 1: failed = 1 - the run from the entry to the return at slot 98: nothing written but the frame, so the
   model run of [bs] is empty (prhW_putN_failed), the ledger and the blocks are the entry's. No call: the walk runs at
   wle (SRr_SRr') and its journal lifts to wle' SEGS RZ (put_jlift) ---- *)
Lemma put_arm1 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W regs mem md ch o d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran
    (rp_i : nat) rp_hist,
  fpre B ARx STK_put ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  getr regs 10 = w64 o -> fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  WriterApp.w_failed st = 1 -> P mem ->
  SRr' SEGS RZ W (cfg_at SEGS (SIGMA AS_put) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ) STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (put_postP P rp_i rp_hist ly S Lam peak ran o buf st bs)).
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
intros ly S Hp W regs mem md ch o d buf st bs Lam peak ran rp_i rp_hist HPRE HROOM HPOS H10 HWIN Hol Hoh HOUT HLED Hf1
  HPM.
apply (SRr_SRr' SEGS RZ).
pose proof HPRE as (HAP & HRO & HSTKTOP & HRAZ & HFRM).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : STK_put = 16592) by (vm_compute; reflexivity).
pose proof HOUT as (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
set (len := Z.of_nat (length (WriterApp.w_text st))) in *.
assert (Hlen : 0 <= len < 2 ^ 64).
{ destruct Harm as [(Hc & _ & Ht) | (_ & _ & Hl & _)]; subst len; [rewrite Ht; cbn; lia | lia]. }
rewrite Hf1 in V24.
destruct (put_entry ly S Hp W regs mem md ch o d buf len (WriterApp.w_cap st) 1 HAP H10 HWIN Hol Hoh Ho8
  V0 Hbr V8 Hlen V16 Hcr V24 ltac:(lia)) as (HS & SHOK).
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (ajournal_x_init_W SK SEGS B (@prh_pst prh_img_A) ARx STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := put_E regs buf len (WriterApp.w_cap st)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len (WriterApp.w_cap st))) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Uo : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (WriterApp.w_cap st)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
unfold cfg_at. rewrite Hent.
change (w64 (BASE + PUT_K)) with (Z_to_bv 64 (BASE + PUT_K)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
(* the return at slot 98: every callee-saved register and ra are back at their entry atoms *)
try rewrite wvb_collapse in HJ.
apply (RET W E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat1.
assert (HAG : env_agree 32 (Ereg regs (put_extra buf len (WriterApp.w_cap st))) E).
{ split; [intros k Hk; apply EL; unfold A_TEXT; lia | reflexivity]. }
assert (HP : aregs_preserved regs (ms_regs ms)).
{ pose proof HS as HS'. unfold st_ok_pi in HS'.
  eapply (aregs_preserved_of_st_ok SEGS); [exact HS' | exact HAG | vm_compute; reflexivity]. }
assert (Hra1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W) E _ ms 1%bv HS).
  match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
(* only the frame [sp - 112, sp) and the struct [o, o + 32) are write windows of the run *)
assert (NOW : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout Hos. apply aview_eq_of. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  unfold put_ss, put_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP put_struct base_val] in Hra';
    rewrite ?HKf, ?Usp, ?Uo in Hra'; lia. }
(* the struct's four fields at the end, from the final state's struct region *)
put_region HS 3%nat (put_struct 1) HRS.
assert (VF : forall od (w : N) e v, In (YP09.mkChunk od (CVal w e)) (YP09.r_chunks (put_struct 1)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (o + od) (N.to_nat w) v).
{ intros od w e v Hin He Hv Hw. exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 od w e v HRS Uo Hin He Hv Hw). }
assert (DEN : forall (k : nat) z, ew E k = Z_to_bv 64 z -> sv_denot E (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk. cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (VF 0 8%N (SOff 33 0) buf ltac:(cbn; tauto) (DEN _ _ E33) ltac:(cbn; lia) ltac:(cbn; lia)) as W0.
pose proof (VF 8 8%N (SOff 34 0) len ltac:(cbn; tauto) (DEN _ _ E34) ltac:(cbn; lia) ltac:(cbn; lia)) as W8.
pose proof (VF 16 8%N (SOff 35 0) (WriterApp.w_cap st) ltac:(cbn; tauto) (DEN _ _ E35) ltac:(cbn; lia) ltac:(cbn; lia)) as W16.
pose proof (VF 24 4%N (SLit 1) 1 ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as W24.
rewrite Z.add_0_r in W0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in W0, W8, W16, W24.
exists ly, S, Hp, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat1 md), 0.
split.
{ rewrite wvb_collapse, Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ pose proof (ajournal_x_materialize (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS (@pa_segs_low rc A_prog_listing PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) as HJ1.
  rewrite wvb_collapse in HJ1. exact (put_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1). }
split.
{ intros a Ha Hn. apply NOW; [lia | lia |]. intros Ho. apply Hn. exists (o, o + 32). split; [left; reflexivity | cbn; lia]. }
split; [exact HP|].
unfold put_postP. split; [|exact HPM].
unfold put_post. split; [exact HROOM|].
split; [intros _; exact HPOS|].
split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; apply andb_prop in Hg; destruct Hg as (Hg & _);
  apply Z.eqb_eq in Hg; lia|].
assert (Hf1' : WriterApp.w_failed st <> 0) by lia.
apply prhWriter_ret_open. exists [], ran, buf, Lam, peak.
rewrite (prhW_putN_failed [bs] [] st Hf1'), (prhW_k_failed [] st [bs] Hf1').
split; [split; [intros i Hi; lia|]; split; [left; reflexivity | intros i Hi; lia]|].
split.
{ apply (put_out_kept W mem (ms_mem ms) Lam o buf st st); try reflexivity.
  - intros a Ha. apply NOW; lia.
  - intros Hc. destruct (put_buf_low ly S Hp W mem md Lam peak _ _ ran o buf st HAR HLED HOUT Hc) as (Hb1 & Hb2 & _).
    pose proof (@cf_head_nonneg cp). lia.
  - right. exact Hf1.
  - intros H0. lia.
  - exact W0.
  - exact W8.
  - exact W16.
  - rewrite Hf1. exact W24.
  - exact HOUT. }
split.
{ apply (put_ledger_kept0 ly S Hp W mem (ms_mem ms) md); [exact HAR | intros a Ha; apply NOW; lia | exact HLED]. }
split; [left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity | apply Permutation_refl]|].
intros i Hi; lia.
Qed.

(* ---- the record from o at the realloc call: eight readable bytes are a word, a present byte is readable, a word is
   nonnegative, a word survives a change that keeps its bytes, and one record whose next fp is below the ceiling is a
   whole chain (bad_next fires: nfp < ceiling <= o) ---- *)
Lemma put_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
assert (G : forall k, 0 <= k < 8 -> exists b, rd (a + k) = Some b)
  by (intros k Hk; destruct (rd (a + k)) as [b|] eqn:E; [exists b; reflexivity | exfalso; exact (H k Hk E)]).
destruct (G 0 ltac:(lia)) as (b0 & E0). rewrite Z.add_0_r in E0.
destruct (G 1 ltac:(lia)) as (b1 & E1). destruct (G 2 ltac:(lia)) as (b2 & E2).
destruct (G 3 ltac:(lia)) as (b3 & E3). destruct (G 4 ltac:(lia)) as (b4 & E4).
destruct (G 5 ltac:(lia)) as (b5 & E5). destruct (G 6 ltac:(lia)) as (b6 & E6).
destruct (G 7 ltac:(lia)) as (b7 & E7).
rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.
Lemma put_apresent_aview : forall (H : word -> bool) m a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma put_rdword_nonneg : forall (H : word -> bool) m a v, rdword (aview SEGS H m) a = Some v -> 0 <= v.
Proof.
intros H m a v Hv. unfold rdword, aview in Hv.
repeat match type of Hv with
  | context [option_map ?f (mbyte ?s ?mm ?x)] =>
      let b := fresh "b" in destruct (mbyte s mm x) as [b|]; cbn [option_map] in Hv;
      [pose proof (u8_range b) | discriminate Hv]
  end.
injection Hv as <-.
lia.
Qed.
(* a word's eight bytes give the word (YCem.v rdword_of_val_mem's proof, for this file: YCem's Require closure, YCeh.v,
   does not build on the engine s1b 459129c18903, YCeh.v:63) *)
Lemma put_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma put_rdword_ext : forall (rd rd' : reader) a, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma put_chain_one : forall ly (rd : reader) sp o ra nfp,
  YM05.alloc_ceiling <= o -> o mod 8 = 0 -> sp + 16 <= o -> o < ly_top ly - 16 ->
  rdword rd (o - 8) = Some ra -> 0 <= ra -> rdword rd (o - 16) = Some nfp -> nfp < YM05.alloc_ceiling ->
  exists ch, achain ly rd sp o ch.
Proof.
intros ly rd sp o ra nfp Hc Ho8 Hsp Htop Hra Hra0 Hnfp Hnc.
destruct (Z_lt_le_dec ra 4096) as [Hlt | Hge].
- exists []. right. split; [lia|]. split; [lia|]. split; [exact Ho8|]. split; [|constructor].
  cbn [fpchain]. exists ra. split; [exact Hra | lia].
- exists [(o, ra, nfp)]. right. split; [lia|]. split; [lia|]. split; [exact Ho8|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Ho8|]. split; [exact Hra|]. split; [exact Hnfp|].
    split; [exact Hge|]. unfold bad_next. rewrite (proj2 (Z.leb_le nfp o)) by lia. reflexivity.
  + constructor; [cbn; lia | constructor].
Qed.

(* the region list of a symbolic state at a call stop (st_ok, not st_ok_pi): the i-th region's region_ok *)
Ltac put_region_auto_st HS i H :=
  lazymatch type of HS with st_ok ?segs ?E ?ss ?msr =>
    let rs := eval vm_compute in (ss_mem ss) in
    let r := eval cbn in (nth i rs (YP09.mkRegion None 0 0 0 0 [])) in
    assert (H : region_ok segs E (ms_mem msr) r)
      by (exact (st_ok_region_nth segs E ss msr i r HS ltac:(vm_compute; reflexivity)));
    cbn [ms_mem restrict] in H
  end.

(* ---- ARM 0: failed = 0 - the entry run to the need test (slot 42); FAST (cap >= need) to the seat at slot 68 and the
   shared tail; GROW (cap < need) through the doubling loop and fuzz_realloc. The walk runs at wle up to the realloc
   call (or the seat of the FAST arm) under the post `SRr' SEGS RZ .. Q` (put_SRr'_of_SRr), and from there at
   wle' SEGS RZ (the call can hide shadow again): the entry journal lifts by put_jlift ---- *)
Lemma put_arm0 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W regs mem md ch o s n d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran
    (rp_i : nat) rp_hist,
  fpre B ARx STK_put ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* the run has at most 4 calls (tput_specX): the hull payment at the realloc call (put_hull_pay) *)
  (length rp_os <= 4)%nat ->
  (* the call's consumer window (tput_specX, the batch kit): its allocation is a consumer event of the run *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran rmost rown ->
  src_rd (PA := PA) W mem s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s n ->
  (* put's run event (tput_specX), the text's entry premise *)
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  WriterApp.w_failed st = 0 ->
  P mem ->
  SRr' SEGS RZ W (cfg_at SEGS (SIGMA AS_put) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ) STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (put_postP P rp_i rp_hist ly S Lam peak ran o buf st bs)).
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW).
(* the runners after the call, at wle' SEGS RZ *)
pose (RUNIR := paj_run_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
pose (RUNTOIR := paj_run_to_x_invR (SK := SK) (PL := PL_prog_A) (PI := PA) B (@prh_pst prh_img_A) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
intros ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran rp_i rp_hist HPRE HROOM HPOS HOS HCONS HUNIV H10 H11 H12
  HCASE HREC HWIN Hol Hoh HOUT HLED HSRC Hn HHOME HEV HWMAX HMAX HLIVE Hf0 HPM.
apply put_SRr'_of_SRr.
change (put_hide (spZ regs + 16 <= o \/ o = spZ regs + 8)) in HCASE.
pose proof HPRE as (HAP & HRO & HSTKTOP & HRAZ & HFRM).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : STK_put = 16592) by (vm_compute; reflexivity).
pose proof HOUT as (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
set (len := Z.of_nat (length (WriterApp.w_text st))) in *.
assert (Hlen : 0 <= len < 2 ^ 64).
{ destruct Harm as [(Hc & _ & Ht) | (_ & _ & Hl & _)]; subst len; [rewrite Ht; cbn; lia | lia]. }
rewrite Hf0 in V24.
destruct (put_entry ly S Hp W regs mem md ch o d buf len (WriterApp.w_cap st) 0 HAP H10 HWIN Hol Hoh Ho8
  V0 Hbr V8 Hlen V16 Hcr V24 ltac:(lia)) as (HS & SHOK).
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (ajournal_x_init_W SK SEGS B (@prh_pst prh_img_A) ARx STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := put_E regs buf len (WriterApp.w_cap st)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len (WriterApp.w_cap st))) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r)
  by (intros kk r Hk Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ kk r Hr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EG 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (Uo : bv_unsigned (ew E 10) = o)
  by (rewrite (EG 10%nat 10%bv) by (lia || reflexivity); rewrite H10; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (WriterApp.w_cap st)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
pose proof (eq_refl : len = Z.of_nat (length (WriterApp.w_text st))) as Hlen_def.
assert (Hn0 : 0 <= n) by lia.
unfold prhWriter_WMAX in HWMAX.
assert (U12 : bv_unsigned (ew E 12) = n)
  by (rewrite (EG 12%nat 12%bv) by (lia || reflexivity); rewrite H12; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = len) by (rewrite E34; apply unsigned_lit_small; lia).
(* the entry facts of the source, and of the buffer when there is one *)
pose proof HSRC as (Sba & S4096 & Sceil & Samr & Sra & Shull).
rewrite Hn in Sceil, Samr, Sra, Shull.
destruct HHOME as (Hkept & Hdisj0).
unfold cfg_at. rewrite Hent.
change (w64 (BASE + PUT_K)) with (Z_to_bv 64 (BASE + PUT_K)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
all: rewrite branch_geu_U, (U_atom E 35 (WriterApp.w_cap st) E35 Hcr), U_add_off_atom in Hc
  by (unfold M64; rewrite ?U12, ?U34; lia).
all: rewrite U12, U34 in Hc.
(* ---- FAST: len + n + 1 <= cap, no call ---- *)
1: { apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hcap0 : WriterApp.w_cap st <> 0) by lia.
  destruct (put_buf_low ly S Hp W mem md Lam peak _ _ ran o buf st HAR HLED HOUT Hcap0) as (Hb1 & Hb2 & Hb16 & Hinb).
  destruct Harm as [(Hz & _) | (Hgrid & HinL & Hlt & (rest & Hrl & Hba) & Hsh)]; [contradiction|].
  destruct (Hsh Hf0) as (Bra & Bhull).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hinb) as (_ & _ & _ & Happ & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
  rewrite Hreq in Happ.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 68).
  all: try solve [put_awr].
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => set (R1 := ms_regs X) in *; set (M1 := ms_mem X) in * end.
  (* the run writes the frame only: every byte outside the frame and the struct is the entry's *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
    aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hout Hos. apply aview_eq_of.
    rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |];
    rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
    match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp, ?Uo in Hra'; lia | ]);
    destruct Hr. }
  assert (KLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KEEP; lia).
  try rewrite wvb_collapse in HJ.
  (* the registers at slot 68 *)
  assert (GR : forall rr : bv 5, getr R1 rr = sv_denot E (sr_get (ss_regs _) rr))
    by (intros rr; exact (st_ok_pi_restrict_reg (w_H W) E _ _ rr HS)).
  assert (D0 : forall (kx : nat) (wx : word), ew E kx = wx -> sv_denot E (SOff kx 0) = wx)
    by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (R8 : getr R1 8 = Z_to_bv 64 o)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; rewrite (EG 10%nat 10%bv) by (lia || reflexivity); exact H10).
  assert (R9 : getr R1 9 = Z_to_bv 64 n)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; rewrite (EG 12%nat 12%bv) by (lia || reflexivity); exact H12).
  assert (R18 : getr R1 18 = Z_to_bv 64 s)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact H11).
  assert (R23 : getr R1 23 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; exact E32).
  assert (R3 : getr R1 3 = getr regs 3)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; apply EG; [lia | reflexivity]).
  assert (R4 : getr R1 4 = getr regs 4)
    by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        apply D0; apply EG; [lia | reflexivity]).
  assert (Hsp1 : spZ R1 = spZ regs - 112)
    by (unfold spZ at 1; rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
          let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
        cbn [sv_denot]; rewrite Usp; apply unsigned_lit_small; lia).
  (* the frame: the thirteen saved registers *)
  put_region_auto HS 0%nat HRF.
  assert (Hsv : forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) M1) (spZ regs - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
  { intros j Hj.
    lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      assert (FR : forall (k : nat) (r : bv 5) od, (k < 32)%nat -> Z.of_nat k = bv_unsigned r ->
        In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
        val_mem SEGS (mrestrict (w_H W) M1) (spZ regs + od) 8 (bv_unsigned (getr regs r)))
      by (intros k r od Hk Hr Hin;
          eapply (field_of_region SEGS E _ 2 (spZ regs) cs _ _ _ _ od 8%N (SOff k 0) (bv_unsigned (getr regs r)) HRF Usp Hin);
          [ apply D0; rewrite (EG k r Hk Hr); symmetry; apply Z_to_bv_bv_unsigned
          | pose proof (u64_range (getr regs r)); cbn; lia | cbn; lia ])
    end.
    replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
    do 13 (destruct j as [|j];
      [ cbn [nth put_saved];
        match goal with |- val_mem _ _ (spZ regs + ?od) _ (bv_unsigned (getr regs ?r)) =>
          let od' := eval vm_compute in od in let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
          change od with od'; apply (FR k r od'); [lia | reflexivity | cbn; tauto] end
      | ]).
    lia. }
  (* the struct: buf, len, cap, failed = 0 *)
  put_region_auto HS 3%nat HRS.
  assert (W0 : val_mem SEGS (mrestrict (w_H W) M1) o 8 buf).
  { pose proof (field_of_region SEGS E _ 10 o _ 0 32 0 32 0 8%N (SOff 33 0) buf HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E33) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (W8 : val_mem SEGS (mrestrict (w_H W) M1) (o + 8) 8 len)
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E34) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W16 : val_mem SEGS (mrestrict (w_H W) M1) (o + 16) 8 (WriterApp.w_cap st))
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 16 8%N (SOff 35 0) (WriterApp.w_cap st) HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E35) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W24 : val_mem SEGS (mrestrict (w_H W) M1) (o + 24) 4 0)
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS Uo ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  (* the caller window outside the struct, and the struct in the footprint *)
  assert (HWK : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
    aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hnf. apply KEEP; [lia | lia |]. intros Ho. apply Hnf. exists (o, o + 32).
    split; [left; reflexivity | cbn; lia]. }
  assert (HFPo : forall a, o <= a < o + 32 -> inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a)
    by (intros a Ha; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
  (* the destination [buf + len, buf + len + n]: in the buffer block, addressable *)
  assert (Hamr_d : amem_range (buf + len) (n + 1)).
  { apply (put_app_amem (buf - cf_head) (WriterApp.w_cap st + cf_head)); [exact Happ | lia | lia | lia]. }
  assert (Hawr_d : forall a, buf + len <= a <= buf + len + n ->
    awr_byte (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) (ablocks B ly S) (ablocks B ly S)
      ly [] a).
  { intros a Ha. right; left. split.
    - exists (buf - cf_head, buf - cf_head + req_size (WriterApp.w_cap st + cf_head)). split; [|cbn; rewrite Hreq; lia].
      right. unfold prhWriter_fp. rewrite (proj2 (Z.eqb_neq _ _) Hcap0). unfold ablocks_fp. cbn. left; reflexivity.
    - exists (buf - cf_head), (WriterApp.w_cap st + cf_head). split; [exact Hinb | rewrite Hreq; lia]. }
  assert (Hra_d : range_addressable (aview SEGS (w_H W) M1) SHADOW_OFF (buf + len) (n + 1)).
  { eapply (range_addressable_agree (aview SEGS (w_H W) mem)).
    { intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity. }
    apply (range_addressable_sub _ _ buf (WriterApp.w_cap st)); [exact Bra | lia | lia]. }
  assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) M1) (buf + len) n).
  { intros Hn1 s0 Hs0. pose proof (put_hull_low (buf + len) n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
    rewrite KLOW by lia. exact (put_hull_sub _ buf (WriterApp.w_cap st) (buf + len) n Bhull ltac:(lia) ltac:(lia) Hn1 s0 Hs0). }
  (* the source [s, s + n): read-only, addressable, apart from the destination *)
  assert (Hsc : s + n <= YM05.alloc_ceiling) by lia.
  assert (Hsvis : forall a, s <= a < s + n -> aview SEGS (w_H W) M1 a <> None).
  { intros a Ha. rewrite KLOW by lia. replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia.
    rewrite (put_garr8_aview W mem s bs (Z.to_nat (a - s)) Sba ltac:(lia)). discriminate. }
  assert (Hdisj : buf + len + n <= s \/ s + n <= buf + len) by lia.
  assert (Hra_s : range_addressable (aview SEGS (w_H W) M1) SHADOW_OFF s n).
  { eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Sra].
    intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity. }
  assert (Hhull_s : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) M1) s n).
  { intros Hn1 s0 Hs0. pose proof (put_hull_low s n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
    rewrite KLOW by lia. exact (Shull Hn1 s0 Hs0). }
  (* the seat: the shared tail runs at wle' SEGS RZ, from the entry journal lifted *)
  apply SRr_ret. cbv beta.
  apply (put_tail P PLAW PCALL ly S Hp W regs mem md d o s n buf len (WriterApp.w_cap st)
    (prhWriter_cfp o buf (WriterApp.w_cap st))
    ly S Hp W R1 M1 _ _ _ (put_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8
    Hsp1 R8 R9 R18 R23 R3 R4 Hsv W0 W8 W16 W24 Hcr
    ltac:(lia) HWK HFPo ltac:(lia) ltac:(lia) ltac:(lia) Hamr_d Hawr_d Hra_d Hhull_d S4096 Hsc Samr Hsvis Hdisj Hra_s
    Hhull_s).
  (* the post: the capacity is unchanged, the text grows by bs, the ledger is the entry's over the new bytes *)
  intros regs' mem' md' k' HJ' HPM' Hkeep' Hcopy' Hnul' V0' V8' V16' V24'.
  unfold put_postP. split; [|exact HPM'].
  unfold put_post. split; [exact HROOM|].
  split; [intros _; exact HPOS|].
  split; [intros Hg; exfalso; unfold prhWriter_grows, prhWriter_need in Hg; apply andb_prop in Hg;
    destruct Hg as (_ & Hg); apply Z.ltb_lt in Hg; rewrite <- Hlen_def, Hn in Hg; lia|].
  assert (EPUT : prhWriter_putN [] st [bs] = WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterApp.w_cap st)
     (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
  { cbn [prhWriter_putN]. unfold prhWriter_grows, prhWriter_need. rewrite Hf0.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [Z.eqb andb]. cbn [prhWriter_putN].
    unfold WriterApp.put1. rewrite Hf0. cbn [Z.eqb negb]. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (EK : prhWriter_k [] st [bs] = 0%nat) by (unfold prhWriter_k; rewrite EPUT; cbn [WriterApp.w_calls]; lia).
  exists []. split; [|rewrite EK; intros i Hi; lia].
  unfold prhWriter_ret_ok. exists ran, buf, Lam, peak. cbv zeta. rewrite EPUT.
  rewrite EK. cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
  split; [split; [intros i Hi; lia|]; split; [left; reflexivity | intros i Hi; lia]|].
  split.
  { apply (put_out_put W M1 mem' Lam o buf (WriterApp.w_cap st) (WriterApp.w_text st) bs 0 rest s); try assumption.
    - lia.
    - exact (put_app_band buf (WriterApp.w_cap st) cf_head Happ Hch0).
    - apply (put_bytes_keep W mem M1 buf _ Hba). intros j Hj. apply KLOW. lia.
    - eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Bra].
      intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity.
    - intros s0 Hs0. pose proof (put_hull_low buf (WriterApp.w_cap st) s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs0).
      rewrite KLOW by lia. exact (Bhull s0 Hs0).
    - apply (put_bytes_keep W mem M1 s bs Sba). intros j Hj. apply KLOW. lia.
    - lia.
    - rewrite <- Hlen_def, Hn. exact Hkeep'.
    - rewrite <- Hlen_def, Hn. exact Hcopy'.
    - rewrite <- Hlen_def, Hn. exact Hnul'.
    - rewrite <- Hlen_def, Hn. exact V8'. }
  split.
  { apply (put_ledger_copy ly S Hp W mem mem' md Lam peak _ _ ran buf (WriterApp.w_cap st) HAR HLED HinL).
    intros a Ha Hab. rewrite Hkeep' by lia. apply KLOW. exact Ha. }
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | apply Permutation_refl]. }
(* ---- GROW: cap < len + n + 1: the spill at slot 43, the doubling loop, fuzz_realloc ---- *)
apply negb_false_iff, Z.ltb_lt in Hc.
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 44).
all: try solve [put_awr].
pmkst HS.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => set (R1 := ms_regs X) in *; set (M1 := ms_mem X) in * end.
try rewrite wvb_collapse in HJ.
assert (GR : forall rr : bv 5, getr R1 rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W) E _ _ rr HS)).
assert (R11 : getr R1 11 = Z_to_bv 64 (WriterApp.w_cap st)).
{ rewrite GR. match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
    let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end.
  cbn [sv_denot]. rewrite E35, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (R12 : getr R1 12 = Z_to_bv 64 (n + 1 + len)).
{ rewrite GR. match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
    let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end.
  apply bv_eq. rewrite unsigned_lit_small by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)))) with (U E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0))).
  rewrite U_add_off_atom by (unfold M64; rewrite ?U12, ?U34; lia). rewrite U12, U34. lia. }
apply (put_loop P PLAW W R1 M1 _ (WriterApp.w_cap st) (n + 1 + len) _ _ _ ly S Hp W mem md ly S Hp _ _ HJ HPM R11 R12
  ltac:(lia) ltac:(lia)).
intros regs3 mem3 md3 HJ3 HPM3 HM3 L22 L11 HO3.
(* the loop changed a1 and s6 only: the symbolic state at slot 49, a1 and s6 fresh atoms 64 / 65 *)
let v := eval vm_compute in (PK 49) in
jafter_stretch_pi HS 64%nat regs3 (mrestrict (w_H W) mem3) ([11%bv; 22%bv] : list (bv 5)) v HSY.
lazymatch type of HSY with ?T -> _ => assert (HRY : T) end.
{ intros r Hr. apply HO3; intros ->; vm_compute in Hr; discriminate Hr. }
specialize (HSY HRY). clear HRY.
lazymatch type of HSY with ?T -> _ => assert (HKY : T) end.
{ apply Forall_forall. intros r _. split.
  - intros a _. unfold mbyte. cbn [ms_mem restrict]. rewrite HM3. reflexivity.
  - intros a _ Hw. unfold writable_at in *. cbn [ms_mem restrict] in Hw. unfold wview in *. rewrite HM3. exact Hw. }
specialize (HSY HKY). clear HKY. rewrite <- restrict_mkst_fx in HSY.
remember (havoc E 64 (map (getr regs3) [11%bv; 22%bv])) as E2 eqn:HE2 in HSY.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall kk, (kk < 64)%nat -> ew E2 kk = ew E kk) by (intros kk Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
assert (E264 : ew E2 64 = getr regs3 11) by (rewrite HE2; reflexivity).
assert (E265 : ew E2 65 = getr regs3 22) by (rewrite HE2; reflexivity).
pose proof HJ3 as (HAR3 & _).
assert (SHOK2 : sh_ok SEGS put_Bx put_SH E2 (mrestrict (w_H W) mem3)).
{ apply (put_shok E2 ly S Hp W mem3 md3 o HAR3); [rewrite OLD2 by lia; exact E32 | | lia | lia | lia | lia].
  rewrite OLD2 by lia. rewrite (EG 10%nat 10%bv) by (lia || reflexivity). exact H10. }
clear HS SHOK HJ HEI HPM. rename HSY into HS. rename SHOK2 into SHOK. rename HJ3 into HJ. rename HEI2 into HEI.
rename HPM3 into HPM.
clear GR R11 R12. subst R1 M1.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (Uo2 : bv_unsigned (ew E2 10) = o) by (rewrite OLD2 by lia; exact Uo).
(* ---- slots 49 .. 54: the load check of o, buf into a0, newcap into a1, the call of fuzz_realloc ---- *)
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [put_awr].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?X) => rename X into MSC end.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
(* the call's memory is the entry's but for the frame and the struct (the loop wrote nothing) *)
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W) (ms_mem MSC) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout Hos. apply aview_eq_of.
  rewrite (HFr1 (Z_to_bv 64 a)), HM3, (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | | |];
  rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp, ?Uo, ?Usp2, ?Uo2 in Hra'; lia | ]);
  destruct Hr. }
assert (KLOWC : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem MSC) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KEEPC; lia).
assert (HPCsp : spZ (ms_regs MSC) = spZ regs + d + - (112 + d))
  by (unfold spZ at 1; rewrite Q2, Usp2, unsigned_lit_small by lia; lia).
(* fuzz_realloc's two live counts at the entry state S (the call's Sc), from the entry's position *)
destruct (PresetRoomCounts.counts_of_room_pos_rl rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HPOS) as (HSEC & H24).
assert (Hs0c : s0Z (ms_regs MSC) = o) by (unfold s0Z; rewrite Q8, OLD2 by lia; exact Uo).
(* the record from o at the call: case 1 by tput_specX's record premise (both words lie at or above sp, outside put's
   frame and the struct), case 2 (o = sp + 8) by the caller window's presence at sp and put's own saved ra at sp - 8,
   below the ceiling by fpre's raZ bound *)
assert (HREC1 : exists ra nfp, rdword (aview SEGS (w_H W) (ms_mem MSC)) (o - 8) = Some ra /\
  rdword (aview SEGS (w_H W) (ms_mem MSC)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ unfold put_hide in HCASE. destruct HCASE as [Hc1 | Hc2].
  - destruct (HREC Hc1) as (ra & Hra8 & nfp & Hnfp & Hnc). exists ra, nfp.
    rewrite (put_rdword_ext (aview SEGS (w_H W) mem) _ (o - 8)) by (intros k Hk; apply KEEPC; lia).
    rewrite (put_rdword_ext (aview SEGS (w_H W) mem) _ (o - 16)) by (intros k Hk; apply KEEPC; lia).
    split; [exact Hra8|]. split; [exact Hnfp | exact Hnc].
  - destruct (put_rdword_some (aview SEGS (w_H W) (ms_mem MSC)) (o - 8)) as (ra & Hra8).
    { intros k Hk. rewrite KEEPC by lia. apply put_apresent_aview. apply Hdpres. lia. }
    put_region_auto_st HS 0%nat HRF.
    assert (DR : sv_denot E2 (SOff 1 0) = Z_to_bv 64 (raZ regs)).
    { cbn [sv_denot]. rewrite OLD2 by lia. rewrite (EG 1%nat 1%bv) by (lia || reflexivity).
      unfold raZ. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
    assert (Hr64 : 0 <= raZ regs < 2 ^ (8 * Z.of_N 8))
      by (unfold raZ; pose proof (u64_range (getr regs 1)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
    pose proof (field_of_region SEGS E2 _ 2 (spZ regs) _ (-112) 0 (-112) 0 (-8) 8%N (SOff 1 0) (raZ regs) HRF Usp2
      ltac:(cbn; tauto) DR Hr64 ltac:(cbn; lia)) as Hv.
    exists ra, (raZ regs). split; [exact Hra8|]. split; [|exact HRAZ].
    replace (o - 16) with (spZ regs + -8) by lia.
    exact (put_rdword_of_val_mem (w_H W) (ms_mem MSC) _ _ Hv (u64_range (getr regs 1))). }
destruct HREC1 as (ra & nfp & Hra8 & Hnfp & Hnc).
assert (HCO1 : YM05.alloc_ceiling <= o) by lia.
assert (HCO2 : spZ regs - 112 + 16 <= o) by lia.
assert (HCO3 : o < ly_top ly - 16) by lia.
destruct (put_chain_one ly (aview SEGS (w_H W) (ms_mem MSC)) (spZ regs - 112) o ra nfp HCO1 Ho8 HCO2 HCO3 Hra8
  (put_rdword_nonneg _ _ _ _ Hra8) Hnfp Hnc) as (ch1 & Hch1).
destruct (prh_univ_closure_realloc B CTX0 HUNIV) as (HU1 & HU2); [vm_compute; discriminate|].
assert (HMU : prh_malloc_univ B) by (apply (prh_univ_closure_malloc B CTX0 HUNIV); vm_compute; discriminate).
assert (Hcgrid : WriterApp.w_cap st = 0 \/ exists j, 0 <= j <= 51 /\ WriterApp.w_cap st = 4096 * 2 ^ j)
  by (destruct Harm as [(Hz & _) | (Hg & _)]; [left; exact Hz | right; exact Hg]).
destruct (put_newcap_grid (WriterApp.w_cap st) (n + 1 + len) Hcgrid ltac:(lia)) as (Hgrid' & Hneed' & H28' & Hge').
set (nc := WriterSpec.newcap (WriterApp.w_cap st) (n + 1 + len)) in *.
(* the grow's event (one, unless the call is the allocation set to fail) and its request nc + cf_head *)
assert (HgrowT : prhWriter_grows st bs = true).
{ unfold prhWriter_grows, prhWriter_need. rewrite Hf0. cbn [Z.eqb andb]. apply Z.ltb_lt.
  rewrite <- Hlen_def, Hn. lia. }
assert (EncN : WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs) = nc)
  by (unfold prhWriter_need, nc; rewrite <- Hlen_def, Hn; f_equal; lia).
assert (EEV : prhWriter_ev st bs =
  if WriterApp.w_cap st =? 0 then PresetReqAt.HMal (nc + cf_head)
  else PresetReqAt.HRe (WriterApp.w_cap st + cf_head) (nc + cf_head)).
{ unfold prhWriter_ev. rewrite EncN. reflexivity. }
(* the live room at the grow's event (prh_live_evs at j = 0: the entry's live bytes plus the request) *)
assert (HLIVE' : WriterApp.w_cnt st <> WriterApp.w_fail st -> blocks_bytes S + (nc + cf_head) <= LIVE_MAX).
{ intros Hcf. rewrite (put_evs1 st bs HgrowT Hcf) in HLIVE.
  pose proof (HLIVE 0%nat (prhWriter_ev st bs) eq_refl) as HL0.
  rewrite put_live_at0, EEV in HL0. destruct (WriterApp.w_cap st =? 0); cbn [prh_ev_req] in HL0; exact HL0. }
(* the call's event and consumer window for put_realloc_cases (put's entry premises HEV and HCONS) *)
assert (HCF : WriterApp.w_cnt st <> WriterApp.w_fail st ->
  PRH_Base.prh_run_at rp_sm rp_x rp_os rp_i
    [if WriterApp.w_cap st =? 0 then PresetReqAt.HMal (nc + cf_head)
     else PresetReqAt.HRe (WriterApp.w_cap st + cf_head) (nc + cf_head)] /\
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 1).
{ intros Hcf. split.
  - apply prh_run_at_one. rewrite <- EEV. exact (HEV HgrowT Hcf).
  - rewrite (put_evs1 st bs HgrowT Hcf) in HCONS. exact HCONS. }
assert (Hal' : - (112 + d) mod 16 = 0).
{ replace (- (112 + d)) with ((- 7 - d / 16) * 16) by (pose proof (Z.div_mod d 16 ltac:(lia)); lia). apply Z_mod_mult. }
assert (Hbud : STK_fuzz_realloc - - (112 + d) <= STK_put + d).
{ assert (STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate). lia. }
assert (Hgp' : getr (ms_regs MSC) 3 = w64 (as_gp B))
  by (rewrite Q3, OLD2 by lia; rewrite (EG 3%nat 3%bv) by (lia || reflexivity); exact Hgp).
assert (Htp' : getr (ms_regs MSC) 4 = w64 (as_tp B))
  by (rewrite Q4, OLD2 by lia; rewrite (EG 4%nat 4%bv) by (lia || reflexivity); exact Htp).
assert (Hraw : YK0s.ret_ok (getr (ms_regs MSC) 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (Hra4' : 4096 <= bv_unsigned (getr (ms_regs MSC) 1))
  by (pose proof (@pa_B_ok _ _ PA) as HB; rewrite Q1, unsigned_lit_small by lia; lia).
assert (Hch' : achain ly (aview SEGS (w_H W) (ms_mem MSC)) (spZ regs + d + - (112 + d)) (s0Z (ms_regs MSC)) ch1)
  by (replace (spZ regs + d + - (112 + d)) with (spZ regs - 112) by lia; rewrite Hs0c; exact Hch1).
(* the return pc of the jal is a listing slot, below the ceiling (the closed lemma put_ret_slot_ceil) *)
idtac "PRB-A0".
assert (HRAZc : raZ (ms_regs MSC) < YM05.alloc_ceiling).
{ pose proof (@pa_B_ok _ _ PA) as HB. unfold raZ.  (rewrite Q1, unsigned_lit_small by lia).
  idtac "PRB-A0a".
  match goal with |- _ + ?k < _ => assert (HK55 : PK 55 = k) by ( (vm_compute; reflexivity)) end.
  idtac "PRB-A0b".
  rewrite <- HK55.  (exact put_ret_slot_ceil). }
idtac "PRB-A1".
assert (HTOP' : spZ (ms_regs MSC) + 64 <= ly_stk_hi ly) by (rewrite HPCsp; lia).
assert (H10' : getr (ms_regs MSC) 10 = w64 buf) by (rewrite Q10, OLD2 by lia; exact E33).
assert (H11' : getr (ms_regs MSC) 11 = w64 nc) by (rewrite Q11, E265; exact L22).
assert (Hnmax : nc + cf_head < cf_malloc_max) by (unfold prhWriter_WMAX in HMAX; lia).
pose proof (put_ledger_kept0 ly S Hp W mem (ms_mem MSC) md Lam peak _ _ ran HAR KLOWC HLED) as HLED'.
(* the old block: none (cap = 0, buf = 0) or the buffer with its cap bytes *)
assert (HOX : exists OLD : list Z,
  (buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] /\ WriterApp.w_text st = []) \/
  (buf <> 0 /\ WriterApp.w_cap st <> 0 /\ (exists j, 0 <= j <= 51 /\ WriterApp.w_cap st = 4096 * 2 ^ j) /\
   In (buf, WriterApp.w_cap st) Lam /\ len < WriterApp.w_cap st /\
   (exists rest, OLD = WriterApp.w_text st ++ 0 :: rest) /\ Z.of_nat (length OLD) = WriterApp.w_cap st /\
   bytes_at W (ms_mem MSC) buf OLD /\
   cf_head <= buf - 4096 /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling /\ buf mod 16 = 0 /\
   In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S))).
{ destruct Harm as [(Hz & Hb0 & Ht0) | (Hg & HinL & Hlt & (rest & Hrl & Hba) & Hsh)].
  - exists []. left. split; [exact Hb0|]. split; [exact Hz|]. split; [reflexivity | exact Ht0].
  - assert (Hcap0 : WriterApp.w_cap st <> 0)
      by (destruct Hg as (j & Hj & ->); assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia); lia).
    destruct (put_buf_low ly S Hp W mem md Lam peak _ _ ran o buf st HAR HLED HOUT Hcap0) as (Hb1 & Hb2 & Hb16 & Hinb).
    pose proof (@cf_head_nonneg cp).
    exists (WriterApp.w_text st ++ 0 :: rest). right. split; [lia|]. split; [exact Hcap0|]. split; [exact Hg|].
    split; [exact HinL|]. split; [lia|]. split; [exists rest; reflexivity|]. split; [exact Hrl|].
    split; [apply (put_bytes_keep W mem (ms_mem MSC) buf _ Hba); intros j Hj; apply KLOWC; lia|].
    split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb16 | exact Hinb]. }
destruct HOX as (OLD & HOX).
assert (HOLD : buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] \/
  In (buf, WriterApp.w_cap st) Lam /\ bytes_at W (ms_mem MSC) buf OLD /\ Z.of_nat (length OLD) = WriterApp.w_cap st)
  by (destruct HOX as [(Hb0 & Hz & Ho0 & _) | (_ & _ & _ & HinL & _ & _ & Hrl & Hba & _)];
      [left; split; [exact Hb0 | split; [exact Hz | exact Ho0]] | right; split; [exact HinL | split; [exact Hba | exact Hrl]]]).
assert (HFP1 : fp_sub_x B (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st))
  (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, WriterApp.w_cap st + cf_head)]) ly S [] ly S).
{ intros a Ha. destruct HOX as [(Hb0 & _) | (Hb0 & Hcap0 & _)].
  - rewrite Hb0 in Ha. destruct Ha as (r & [] & _).
  - left. rewrite (proj2 (Z.eqb_neq _ _) Hb0) in Ha. destruct Ha as (r & Hr & Hra'). exists r. split; [|exact Hra'].
    right. unfold prhWriter_fp. rewrite (proj2 (Z.eqb_neq _ _) Hcap0). exact Hr. }
assert (HRO' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem MSC))).
{ apply (put_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HRO].
  pose proof (@cf_head_nonneg cp).
  apply sink_closed_cons; [cbn; lia|]. unfold prhWriter_fp.
  destruct HOX as [(_ & Hz & _) | (_ & Hcap0 & _ & _ & _ & _ & _ & _ & Hb1 & _)].
  - rewrite Hz. cbn. intros (r & [] & _).
  - rewrite (proj2 (Z.eqb_neq _ _) Hcap0). apply sink_closed_pos. constructor; [cbn; lia | constructor]. }
assert (Hbc : buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] \/ buf <> 0 /\ WriterApp.w_cap st <> 0)
  by (destruct HOX as [(Hb0 & Hz & Ho0 & _) | (Hb0 & Hcap0 & _)]; [left; auto | right; auto]).
(* THE HULL PAYMENT: the call's state is the entry state S (put makes no allocator call before it), where the run's
   position is HPOS (put_hull_pay) *)
assert (HHULL : PresetHullBudget.hull_budget S
  (if buf =? 0 then [PresetReqAt.HMal (nc + cf_head)]
   else [PresetReqAt.HRe (WriterApp.w_cap st + cf_head) (nc + cf_head)]))
  by (apply (put_hull_pay rp_sm rp_x rp_os rp_i rp_H0 rp_hist S buf (WriterApp.w_cap st + cf_head) (nc + cf_head) HOS
        HPOS); pose proof (@cf_head_nonneg cp); lia).
(* ---- THE CALL: from here the walk is at wle' SEGS RZ ---- *)
all: apply SRr_ret; cbv beta.
all: eapply (SRr'_bind SEGS RZ); [ apply (put_realloc_call W E2 _ MSC (STK_put + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st))
    ly S Hp W mem md ly S Hp _ _ (- (112 + d)) (getr (ms_regs MSC) 1) ch1 buf (WriterApp.w_cap st) nc OLD Lam peak
    (WriterApp.w_cnt st) (WriterApp.w_fail st) ran HS eq_refl eq_refl (put_jlift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
    HPCsp Hal' ltac:(lia) Hbud Hgp' Htp' eq_refl Hraw Hra4'
    Hch' HRO' HTOP' HRAZc HFRM HROOM HMU HSEC H24 HHULL HU1 HU2 H10' H11' ltac:(lia) Hnmax HLED' HOLD HLIVE' HFP1) | ].
all: cbv beta; intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJin & HP2 & (HQ2 & HMN2)).
(* P crosses the call by the text's memnorm keep (fpostm's fQmn conjunct) *)
all: pose proof (PCALL _ _ HMN2 HPM) as HPM2; clear HPM HMN2; rename HPM2 into HPM.
all: idtac "PRB-A2".
(* ---- back at slot 55: the frame and the struct kept (both above the callee's window), the caller-saved registers
   fresh atoms from 66 (the stretch used 64 / 65) ---- *)
all: rewrite Q1.
all: try rewrite wvb_collapse in HJ2.
all: pose proof (ajxR_ar HJ2) as HAR2. all: pose proof (ajxR_ly HJ2) as Hly2.
all: pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
all: jafter_call_keep_pi HS 66%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3]%nat HSX.
all: lazymatch type of HSX with ?T -> _ => assert (HRKX : T) by
  (constructor; [|constructor; [|apply Forall_nil]]; cbn [ms_mem restrict];
   [ eapply (region_kept_stack_sub_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) E2 STK_fuzz_realloc _ _
       ly S Hp W (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 2%nat (-112) 0 (-112) 0 _ (spZ regs) (STK_put + d)
       (spZ regs + d) _ ly S Hp W mem md [] _ HJin HJ2 Usp2); lia
   | eapply (region_kept_stack_sub_xR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx (wle' SEGS RZ) E2 STK_fuzz_realloc _ _
       ly S Hp W (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 10%nat 0 32 0 32 _ o (STK_put + d) (spZ regs + d) _
       ly S Hp W mem md [] _ HJin HJ2 Uo2); lia ]) end.
all: specialize (HSX HRKX); clear HRKX; rewrite <- restrict_mkst_fx in HSX.
all: remember (havoc E2 66 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HSX.
all: assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLD3 : forall kk, (kk < 66)%nat -> ew E3 kk = ew E2 kk) by (intros kk Hk; rewrite HE3; apply ew_havoc_old; exact Hk).
all: assert (SHOK3 : sh_ok SEGS put_Bx put_SH E3 (mrestrict (w_H W2) mem2))
  by (apply (put_shok E3 ly2 S2 Hp2 W2 mem2 md2 o HAR2);
      [ rewrite OLD3, OLD2 by lia; exact E32
      | rewrite OLD3, OLD2 by lia; rewrite (EG 10%nat 10%bv) by (lia || reflexivity); exact H10
      | lia | lia | lia | lia ]).
all: assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
all: assert (Uo3 : bv_unsigned (ew E3 10) = o) by (rewrite OLD3 by lia; exact Uo2).
all: clear HS SHOK HJ HEI. all: rename HSX into HS. all: rename SHOK3 into SHOK. all: rename HJ2 into HJ.
all: rename HEI3 into HEI.
all: destruct (put_realloc_cases rp_sm rp_x rp_os rp_H0 rp_i rp_hist buf (WriterApp.w_cap st) nc OLD Lam peak _ _ ran ly S Hp W
  ly2 S2 Hp2 W2 regs2 mem2 md2 HAR2 Hbc ltac:(lia) HPOS HCF HQ2) as (HROOM2 & [HNULL | HSUCC]).
all: psrr_branch_tok RUN BRR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc0 end.
all: assert (E370 : ew E3 70 = getr regs2 10) by (rewrite HE3; reflexivity).
all: rewrite branch_eq_U, U_SOff, (U_lit E3 0 ltac:(lia)), E370, Z.add_0_r, zcanon_id in Hc0
  by (unfold M64; apply u64_range).
all: try solve [ destruct HNULL as (U0 & _); rewrite U0 in Hc0; discriminate Hc0
              | destruct HSUCC as (res & Ur & _ & Hr4 & _); rewrite Ur in Hc0; apply Z.eqb_eq in Hc0;
                pose proof (@cf_head_nonneg cp); lia ].
(* ---- NULL: slots 99 .. 103 (the store check of o + 24, failed = 1), the epilogue, the return ---- *)
1: { idtac "PRB-A3". destruct HNULL as (U0 & PHp & Ebl & Hbkeep & HLcase & HPN).
  paj_run_tok_x_inv RUNIR HS HJ SHOK HPM put_Bspan.
  all: try solve [put_awr].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => rename X into MSN end.
  try rewrite wvb_collapse in HJ.
  apply (SRr_SRr' SEGS RZ).
  apply (RET W2 E3 _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros matR.
  assert (HAG : env_agree 32 (Ereg regs (put_extra buf len (WriterApp.w_cap st))) E3).
  { split; [intros kk Hk; rewrite OLD3, OLD2 by lia; apply EL; unfold A_TEXT; lia | rewrite HE3, HE2; reflexivity]. }
  assert (HP : aregs_preserved regs (ms_regs MSN)).
  { pose proof HS as HS'. unfold st_ok_pi in HS'.
    eapply (aregs_preserved_of_st_ok SEGS); [exact HS' | exact HAG | vm_compute; reflexivity]. }
  assert (Hra1 : getr (ms_regs MSN) 1 = getr regs 1).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) E3 _ MSN 1%bv HS).
    match goal with |- sv_denot E3 ?e = _ => let v := eval vm_compute in e in change e with v end.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite OLD3, OLD2 by lia.
    rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
  (* the run after the call writes the frame and struct windows only *)
  assert (KEEPN : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
    aview SEGS (w_H W2) (ms_mem MSN) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hout Hos. apply aview_eq_of.
    match goal with HF' : frame_of E3 _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem MSN)) |- _ =>
      rewrite (HF' (Z_to_bv 64 a)); [reflexivity|] end.
    rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
    match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp3, ?Uo3 in Hra'; lia | ]).
    destruct Hr. }
  pose proof (ajxR_hi HJin) as GIN.
  (* the struct's fields at the end *)
  put_region_auto HS 1%nat HRS.
  assert (D0 : forall (kx : nat) (wx : word), ew E3 kx = wx -> sv_denot E3 (SOff kx 0) = wx)
    by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (W0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) o 8 buf).
  { pose proof (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 0 8%N (SOff 33 0) buf HRS Uo3 ltac:(cbn; tauto)
      ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E33) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
    rewrite Z.add_0_r in Hv. exact Hv. }
  assert (W8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 8) 8 len)
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo3 ltac:(cbn; tauto)
      ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E34) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W16 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 16) 8 (WriterApp.w_cap st))
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 16 8%N (SOff 35 0) (WriterApp.w_cap st) HRS Uo3
      ltac:(cbn; tauto) ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E35) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W24 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 24) 4 1)
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 24 4%N (SLit 1) 1 HRS Uo3 ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (KLOWN : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem MSN) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; apply KEEPN; lia).
  (* the post: failed, text and capacity kept, the ledger counts the call *)
  exists ly2, S2, Hp2, (ms_regs MSN), (ms_mem MSN). eexists. exists (0 + k1).
  split.
  { rewrite ?wvb_collapse, Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split.
  { pose proof (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_A) ARx LAWS
      (@pa_segs_low rc A_prog_listing PA) (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matR HJ) as HJ1.
    rewrite ?wvb_collapse in HJ1. exact HJ1. }
  split.
  { intros a Ha Hnf.
    assert (Hos : ~ (o <= a < o + 32)) by (intros Ho; apply Hnf; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
    rewrite KEEPN by lia. rewrite GIN by lia. apply KEEPC; lia. }
  split; [exact HP|].
  unfold put_postP. split; [|exact HPM].
  unfold put_post. split; [exact HROOM2|].
  (* the position: grows (cap < need), fuzz_realloc returned NULL (only the allocation set to fail: the realloc
     text's outcome clause excludes a refusal), the stored failed is 1: the index kept with SOME history (the batch kit's
     tput_specX f' = 1 arm, existential, as the realloc text's res = 0 arm gives it) *)
  assert (Hneedlt : WriterApp.w_cap st < prhWriter_need st bs)
    by (unfold prhWriter_need; rewrite <- Hlen_def, Hn; lia).
  split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; rewrite (proj2 (Z.eqb_eq _ _) Hf0) in Hg;
    cbn [andb] in Hg; apply Z.ltb_ge in Hg; lia|].
  split; [intros _ f' Hf'; split; [intros Ef'; exfalso; exact (put_val_mem_1 _ _ _ Hf' W24 Ef') |
    intros _; exact HPN]|].
  destruct (put_null_model st bs Hf0) as (EPUT & EK).
  { unfold prhWriter_need. rewrite <- Hlen_def, Hn. lia. }
  assert (HOUTN : forall fl', prhWriter_out (PA := PA) W2 (ms_mem MSN) Lam o buf
    (WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64) fl'
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]))).
  { intros fl'. unfold prhWriter_out. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap].
    split; [exact Ho8|]. split; [exact Hbr|]. split; [exact Hcr|]. split; [exact W0|]. split; [exact W8|].
    split; [exact W16|]. split; [exact W24|]. split; [right; reflexivity|]. split; [exact Hbok|].
    destruct HOX as [(Hb0 & Hz & Ho0 & Ht0) | (Hb0 & Hcap0 & Hg & HinL & Hlt & (rest & Erest) & Hrl & Hba & _ & Hb2 & _)].
    - left. split; [exact Hz|]. split; [exact Hb0 | exact Ht0].
    - right. split; [exact Hg|]. split; [exact HinL|]. split; [lia|]. split.
      + exists rest. rewrite <- Erest. split; [exact Hrl|].
        apply (put_bytes_keep W2 mem2 (ms_mem MSN) buf OLD (Hbkeep Hb0)). intros j Hj. apply KEEPN; lia.
      + intros Hf; discriminate Hf. }
  destruct HLcase as (Hcf & HL2).
  exists [false]. split.
  2: { rewrite EK. intros i Hi _. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact Hcf. }
  unfold prhWriter_ret_ok. exists ran, buf, Lam, peak. cbv zeta. rewrite EPUT, EK.
  rewrite (proj2 (Z.eqb_eq _ _) Hcf). cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
  split.
  { split; [intros i Hi Hci; assert (i = 0%nat) by lia; subst i; reflexivity|].
    split; [left; reflexivity|].
    intros i Hi Hr _. assert (i = 0%nat) by lia. subst i. exfalso.
    unfold prh_refused in Hr. cbn [nth negb andb Z.of_nat] in Hr.
    rewrite Z.add_0_r, (proj2 (Z.eqb_eq _ _) Hcf) in Hr. cbn [negb] in Hr. discriminate Hr. }
  split; [exact (HOUTN _)|].
  split.
  { change SIZE_MAXZ with (2 ^ 64 - 1) in HL2.
    exact (put_ledger_kept0 ly2 S2 Hp2 W2 mem2 (ms_mem MSN) md2 Lam peak _ _ ran HAR2 KLOWN HL2). }
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite Ebl. apply Permutation_refl. }
idtac "PRB-A4".
(* ---- SUCCESS: slots 56 .. 67 (the store checks of o and o + 16, buf := res, cap := newcap, a0 := o + 8 from the
   spill, the FAST checks), the seat at slot 68 and the shared tail ---- *)
idtac "PRB-A5".
destruct HSUCC as (res & Ures & Hcf & Hr4 & Hr16 & Hrc & l1 & l2 & b1 & b2 & Harm2 & Pb & (rest' & HbrN & Hlr) &
  Hra2 & Hhv2 & Hnin & HL2 & HPS).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hnc0 : 0 < nc) by lia.
put_hide_all.
assert (HinN : In (res - cf_head, nc + cf_head) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity).
paj_run_to_tok_x_inv RUNTOIR HS HJ SHOK HPM put_Bspan (PK 68).
all: try solve [put_awr].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => rename X into M68S end.
try rewrite wvb_collapse in HJ.
pmkst HS.
assert (KEEP68 : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hout Hos. apply aview_eq_of.
  match goal with HF' : frame_of E3 _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem M68S)) |- _ =>
    rewrite (HF' (Z_to_bv 64 a)); [reflexivity|] end.
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp3, ?Uo3 in Hra'; lia | ]).
  destruct Hr. }
assert (KLOW68 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply KEEP68; lia).
pose proof (ajxR_hi HJin) as GIN.
(* the registers at slot 68 *)
assert (EG3 : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E3 kk = getr regs r)
  by (intros kk r Hk Hr; rewrite OLD3, OLD2 by lia; apply EG; [exact Hk | exact Hr]).
assert (GR : forall rr : bv 5, getr (ms_regs M68S) rr = sv_denot E3 (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W2) E3 _ _ rr HS)).
assert (D0 : forall (kx : nat) (wx : word), ew E3 kx = wx -> sv_denot E3 (SOff kx 0) = wx)
  by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (R8 : getr (ms_regs M68S) 8 = Z_to_bv 64 o)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; rewrite (EG3 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (R9 : getr (ms_regs M68S) 9 = Z_to_bv 64 n)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; rewrite (EG3 12%nat 12%bv) by (lia || reflexivity); exact H12).
assert (R18 : getr (ms_regs M68S) 18 = Z_to_bv 64 s)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; rewrite (EG3 11%nat 11%bv) by (lia || reflexivity); exact H11).
assert (R23 : getr (ms_regs M68S) 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; rewrite OLD3, OLD2 by lia; exact E32).
assert (R3 : getr (ms_regs M68S) 3 = getr regs 3)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; apply EG3; [lia | reflexivity]).
assert (R4 : getr (ms_regs M68S) 4 = getr regs 4)
  by (rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      apply D0; apply EG3; [lia | reflexivity]).
assert (Hsp1 : spZ (ms_regs M68S) = spZ regs - 112)
  by (unfold spZ at 1; rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
        let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end;
      cbn [sv_denot]; rewrite Usp3; apply unsigned_lit_small; lia).
(* the frame: the thirteen saved registers *)
put_region_auto HS 0%nat HRF.
assert (Hsv : forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (spZ regs - 8 - 8 * Z.of_nat j) 8
   (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
{ intros j Hj.
  lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
    assert (FR : forall (k : nat) (r : bv 5) od, (k < 32)%nat -> Z.of_nat k = bv_unsigned r ->
      In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
      val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (spZ regs + od) 8 (bv_unsigned (getr regs r)))
    by (intros k r od Hk Hr Hin;
        eapply (field_of_region SEGS E3 _ 2 (spZ regs) cs _ _ _ _ od 8%N (SOff k 0) (bv_unsigned (getr regs r)) HRF Usp3 Hin);
        [ apply D0; rewrite (EG3 k r Hk Hr); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (u64_range (getr regs r)); cbn; lia | cbn; lia ])
  end.
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  do 13 (destruct j as [|j];
    [ cbn [nth put_saved];
      match goal with |- val_mem _ _ (spZ regs + ?od) _ (bv_unsigned (getr regs ?r)) =>
        let od' := eval vm_compute in od in let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
        change od with od'; apply (FR k r od'); [lia | reflexivity | cbn; tauto] end
    | ]).
  lia. }
(* the struct: res, len, newcap, failed = 0 *)
assert (E370' : ew E3 70 = Z_to_bv 64 res) by (rewrite E370, <- Ures; symmetry; apply Z_to_bv_bv_unsigned).
assert (E365 : ew E3 65 = Z_to_bv 64 nc) by (rewrite OLD3 by lia; rewrite E265; exact L22).
put_region_auto HS 1%nat HRS.
assert (W0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) o 8 res).
{ pose proof (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 0 8%N (SOff 70 0) res HRS Uo3 ltac:(cbn; tauto)
    (D0 _ _ E370') ltac:(cbn; lia) ltac:(cbn; lia)) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (W8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 8) 8 len)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo3 ltac:(cbn; tauto)
    ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E34) ltac:(cbn; lia) ltac:(cbn; lia)).
assert (Hnc64 : 0 <= nc < 2 ^ (8 * Z.of_N 8)) by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
assert (W16 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 16) 8 nc)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 16 8%N (SOff 65 0) nc HRS Uo3 ltac:(cbn; tauto)
    (D0 _ _ E365) Hnc64 ltac:(cbn; lia)).
assert (W24 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 24) 4 0)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS Uo3 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
(* the caller window outside the struct, and the struct in the footprint *)
assert (HWK : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
  aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnf.
  assert (Hos : ~ (o <= a < o + 32)) by (intros Ho; apply Hnf; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
  rewrite KEEP68 by lia. rewrite GIN by lia. apply KEEPC; lia. }
assert (HFPo : forall a, o <= a < o + 32 -> inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a)
  by (intros a Ha; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
(* the new block: not an entry block; its range and shadow *)
assert (Harm' : WriterApp.w_cap st = 0 /\ buf = 0 /\ l1 = [] /\ l2 = Lam \/
  WriterApp.w_cap st <> 0 /\ Lam = l1 ++ (buf, WriterApp.w_cap st) :: l2).
{ unfold put_hide in Harm2, HOX.
  destruct Harm2 as [(Hzz & Ea1 & Ea2 & _ & _) | (Hzz & ELm & _)]; [left | right; split; [exact Hzz | exact ELm]].
  split; [exact Hzz|]. split; [|split; [exact Ea1 | exact Ea2]].
  destruct HOX as [(Hbz & _) | (_ & Hcz & _)]; [exact Hbz | contradiction]. }
assert (HnotN : ~ In (res - cf_head, nc + cf_head) (ablocks B ly S)).
{ unfold put_hide in Harm2.
  assert (Hsnd : 0 < snd (res - cf_head, nc + cf_head)) by (change (snd (res - cf_head, nc + cf_head)) with (nc + cf_head); lia).
  apply (put_newblk ly2 S2 Hp2 W2 mem2 md2 (ablocks B ly S) b1 b2 (res - cf_head, nc + cf_head)
    (buf - cf_head, WriterApp.w_cap st + cf_head) HAR2 Hsnd Pb).
  destruct Harm2 as [(Hzz & Ea1 & Ea2 & Ea3 & Ea4) | (Hzz & ELm & Eb)]; [left; split; [exact (eq_sym Ea4) | exact Ea3] |].
  right. split; [exact Eb|]. intros Eq'. inversion Eq'. lia. }
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 HinN) as (_ & _ & _ & HappN & _).
assert (Hreqn : req_size (nc + cf_head) = nc + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0); cbv iota; lia).
rewrite Hreqn in HappN.
(* the source after the call *)
(* a fake frame's class is 0 .. 10: the P'' engine's AR_laws_x field 19 (alx_frames_cid, a Theorem Labs lane) *)
assert (HCID : forall cid pos, In (cid, pos) (frames S) -> 0 <= cid)
  by (intros cid pos Hin; destruct (alx_frames_cid SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin); lia).
destruct (put_src_after ly S Hp W mem md (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 _ Lam peak _ _ ran buf (WriterApp.w_cap st)
  s bs n res nc l1 l2 _ _ _ _ HAR HLED HSRC Hn (conj Hkept Hdisj0) HCID KLOWC HJin Harm' HinN HnotN HL2 Hnc0)
  as (SBa2 & Svis2 & Sra2 & Shull2 & Sdisj2).
put_hide_all.
(* the destination [res + len, res + len + n]: in the new block, addressable *)
assert (Hamr_d : amem_range (res + len) (n + 1)).
{ apply (put_app_amem (res - cf_head) (nc + cf_head)); [exact HappN | lia | lia | lia]. }
assert (Hawr_d : forall a, res + len <= a <= res + len + n ->
  awr_byte (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) (ablocks B ly S) (ablocks B ly2 S2)
    ly2 [] a).
{ intros a Ha. right; right; left. exists (res - cf_head), (nc + cf_head).
  split; [exact HinN|]. split; [exact HnotN | rewrite Hreqn; lia]. }
assert (Hra_d : range_addressable (aview SEGS (w_H W2) (ms_mem M68S)) SHADOW_OFF (res + len) (n + 1)).
{ eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)).
  { intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW68 by lia. reflexivity. }
  apply (range_addressable_sub _ _ res nc); [exact Hra2 | lia | lia]. }
assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem M68S)) (res + len) n).
{ intros Hn1 s0 Hs0. pose proof (put_hull_low (res + len) n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
  rewrite KLOW68 by lia. exact (put_hull_sub _ res nc (res + len) n (Hhv2 Hnc0) ltac:(lia) ltac:(lia) Hn1 s0 Hs0). }
(* the source at slot 68 *)
assert (Hsc : s + n <= YM05.alloc_ceiling) by lia.
assert (Hsvis : forall a, s <= a < s + n -> aview SEGS (w_H W2) (ms_mem M68S) a <> None)
  by (intros a Ha; rewrite KLOW68 by lia; exact (Svis2 a Ha)).
assert (Hdisj : res + len + n <= s \/ s + n <= res + len) by (unfold put_hide in Sdisj2; lia).
put_hide_all.
assert (Hra_s : range_addressable (aview SEGS (w_H W2) (ms_mem M68S)) SHADOW_OFF s n).
{ eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)); [|exact Sra2].
  intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW68 by lia. reflexivity. }
assert (Hhull_s : 0 < n -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem M68S)) s n).
{ intros Hn1 s0 Hs0. pose proof (put_hull_low s n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
  rewrite KLOW68 by lia. exact (Shull2 Hn1 s0 Hs0). }
idtac "PRB-A6".
apply (put_tail P PLAW PCALL ly S Hp W regs mem md d o s n res len nc (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly2 S2 Hp2 W2 (ms_regs M68S) (ms_mem M68S) _ _ _ HJ HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8 Hsp1 R8 R9 R18 R23 R3 R4
  Hsv W0 W8 W16 W24 ltac:(lia) ltac:(lia) HWK HFPo ltac:(lia) ltac:(lia) ltac:(lia) Hamr_d Hawr_d Hra_d Hhull_d S4096 Hsc
  Samr Hsvis Hdisj Hra_s Hhull_s).
(* the post: the buffer grew to the new block, the text by bs; the ledger is fuzz_realloc's over the new bytes *)
intros regs' mem' md' k' HJ' HPM' Hkeep' Hcopy' Hnul' V0' V8' V16' V24'.
unfold put_postP. split; [|exact HPM'].
unfold put_post. split; [exact HROOM2|].
assert (Hneedlt : WriterApp.w_cap st < prhWriter_need st bs) by (unfold prhWriter_need; rewrite <- Hlen_def, Hn; lia).
destruct (put_grow_model st bs Hf0 Hneedlt Hcf) as (EPUT & EK).
assert (Enc : WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs) = nc)
  by (unfold prhWriter_need, nc; rewrite <- Hlen_def, Hn; f_equal; lia).
(* the position: grows, fuzz_realloc granted, the stored failed is 0: one event (the text's entry premise, HEV, is
   this call's), the position advanced by one *)
split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; rewrite (proj2 (Z.eqb_eq _ _) Hf0) in Hg;
  cbn [andb] in Hg; apply Z.ltb_ge in Hg; lia|].
split.
{ intros Hg f' Hf'. split.
  - intros _. apply HPS. pose proof (HEV Hg Hcf) as HE. unfold prhWriter_ev in HE. rewrite Enc in HE. exact HE.
  - (* f' = 1 against the stored failed = 0 (V24'): one byte decides (the #102 text keys this arm on f' = 1, the fix of
       the f' <> 0 defect a Theorem Labs lane found on kit-oldpin b501d43ce5af) *)
    intros Ef'. subst f'. exfalso. exact (put_val_mem_1 _ _ _ V24' Hf' eq_refl). }
(* no refusal: the one call granted (DEAD-PUT's prh_granted) *)
assert (G1 : prh_granted [true] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [true] st [bs])).
{ rewrite EK. intros i Hi Hb. assert (i = 0%nat) by lia. subst i. cbn [nth] in Hb. discriminate Hb. }
exists [true]. split; [|exact G1].
unfold prhWriter_ret_ok. exists ran, res, ((res, nc) :: l1 ++ l2), (Z.max peak (Ledger.lsum (l1 ++ l2) + nc)).
cbv zeta. rewrite EPUT, EK, Enc. cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
split.
{ split; [intros i Hi Hci; assert (i = 0%nat) by lia; subst i; cbn in Hci; lia|].
  split; [left; reflexivity|].
  intros i Hi Hr _. assert (i = 0%nat) by lia. subst i. exfalso.
  unfold prh_refused in Hr. cbn [nth negb andb] in Hr. discriminate Hr. }
assert (HNB : exists r0 rest'', Z.of_nat (length (WriterApp.w_text st ++ r0 :: rest'')) = nc /\
  bytes_at (PA := PA) W2 mem2 res (WriterApp.w_text st ++ r0 :: rest'')).
{ unfold put_hide in HOX.
  destruct HOX as [(Hbz & Hzz & Hoz & Htz) | (Hbz & Hcapz & Hgz & HinLz & Hltz & (restz & Erz) & Hrlz & Hbaz & _)].
  - rewrite Hoz, firstn_nil in HbrN. cbn [app] in HbrN. rewrite Hzz in Hlr.
    destruct rest' as [|r0 rest'']; [cbn [length] in Hlr; lia|].
    exists r0, rest''. rewrite Htz. cbn [app]. split; [cbn [length] in Hlr |- *; lia | exact HbrN].
  - rewrite Z.min_l in HbrN, Hlr by lia.
    rewrite firstn_all2 in HbrN by lia. subst OLD. rewrite <- app_assoc in HbrN. cbn [app] in HbrN.
    exists 0, (restz ++ rest'). split; [|exact HbrN].
    rewrite length_app in Hrlz |- *. cbn [length] in Hrlz |- *. rewrite length_app. lia. }
destruct HNB as (r0 & rest'' & Hlen'' & Hba'').
assert (Hba68 : bytes_at (PA := PA) W2 (ms_mem M68S) res (WriterApp.w_text st ++ r0 :: rest''))
  by (apply (put_bytes_keep W2 mem2 (ms_mem M68S) res _ Hba''); intros j Hj; apply KLOW68; lia).
split.
{ apply (put_out_put W2 (ms_mem M68S) mem' ((res, nc) :: l1 ++ l2) o res nc (WriterApp.w_text st) bs r0 rest'' s);
    try assumption.
  - lia.
  - exact (put_app_band res nc cf_head HappN Hch0).
  - left; reflexivity.
  - eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)); [|exact Hra2].
    intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW68 by lia. reflexivity.
  - intros s0 Hs0. pose proof (put_hull_low res nc s0 ltac:(lia) Hnc0 ltac:(lia) Hs0).
    rewrite KLOW68 by lia. exact (Hhv2 Hnc0 s0 Hs0).
  - apply (put_bytes_keep W2 mem2 (ms_mem M68S) s bs SBa2). intros j Hj. apply KLOW68. lia.
  - lia.
  - rewrite <- Hlen_def, Hn. exact Hkeep'.
  - rewrite <- Hlen_def, Hn. exact Hcopy'.
  - rewrite <- Hlen_def, Hn. exact Hnul'.
  - rewrite <- Hlen_def, Hn. exact V8'. }
split.
{ apply (put_ledger_copy ly2 S2 Hp2 W2 mem2 mem' md2 ((res, nc) :: l1 ++ l2) _ _ _ ran res nc HAR2 HL2 (or_introl eq_refl)).
  intros a Ha Hab. rewrite Hkeep' by lia. apply KLOW68. exact Ha. }
right. right. split; [lia|].
exists l1, l2, b1, b2. split; [exact Harm2|]. split; [reflexivity|]. split; [|exact Pb].
(* the refusal peak of a run with no refusal is 0, and the granted peak is not negative (the entry ledger) *)
rewrite (prhW_rpeak_granted [true] Lam st [bs] G1).
pose proof HLED as HB0. apply prh_ledger_bounds in HB0. lia.
Qed.

End rp.
End mo.

(* ---- THE COMPOSITION: the text tput_specX (lib/A/PRH_FnWriter.v: SRr' SEGS RZ, fpostWmR at
   wle' SEGS RZ, the entry premise `length rp_os <= 4`) from put_arm0 (failed = 0) and put_arm1 (failed = 1), the
   struct's failed field being 0 or 1 (prhWriter_out). The memory invariant of the segments is instantiated ONCE here:
   P := `memnorm mem -> memnorm m` for put's entry memory mem (YSRrMemnorm.srr_inv_laws_imp over
   srr_inv_laws_memnorm_k, srr_inv_call_imp), so the post is fpostWmR's (S7a_indent's indent_holds, the same step).
   Rule-24 CONFIRM for put: 22:53Z (the lead's record). ---- *)
Theorem put_holds : tput_specX (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran.
intros HPRE HROOM HPOS HOS HCONS HUNIV H10 H11 H12 HCASE HREC HWIN Hol Hoh HOUT HLED HSRC Hn HHOME HEV HWMAX HMAX
  HLIVE.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & Hf01 & _).
unfold fpostWmR, fQmn.
destruct Hf01 as [Hf0 | Hf1].
- eapply put_arm0 with (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
  all: first
    [ exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))
    | exact (srr_inv_call_imp SEGS mem)
    | exact (fun H => H)
    | eassumption ].
- eapply put_arm1 with (P := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
  all: first
    [ exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))
    | exact (fun H => H)
    | eassumption ].
Qed.

End h.
End W.
