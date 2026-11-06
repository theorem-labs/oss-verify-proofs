(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_string_seg_ep.v, with its module paths and module names changed; 1144 of its 1229 lines of code are new or changed and 275 lines of the source are left out. *)
(* fuzz_preset image A, slice S6: a Theorem Labs lane's program walk of pj_string (46 instructions) over the ONE image-A program
   listing (lib/A/Listing_prog.v v4, a Theorem Labs lane), generic in the image facts (Context PAImg A_prog_listing) and in the
   allocator relation ARx (LAWS : AR_laws_x .. cf_head), concluding the text tpj_string_specX from the memset row and
   fuzz_strdup's text, in SRr form.
   THE WALK: pj_string_holds_P (Section p, generic memory invariant Pm with srr_inv_laws and srr_inv_call: the walk
   crosses the memset row and fuzz_strdup, whose keeps are the memnorm one), the m-form text pj_string_holds as its
   instance at Pm := YAkMemnorm.memnorm SEGS (tpj_string_specX_of_P). Stretches: slots 0-12 (the frame, s0 = v,
   s1 = s, s2 = the shadow base) to `jal __asan_memset` (v, 0, 56) by a Theorem Labs lane's aj_intrin_at_xm_fr over the row
   AIM; a fresh seat at +0x34 (ss_ps2), the type store and `bnez s1`; both arms (s = 0: the literal PS_LIT) reach
   `jal fuzz_strdup`, where ps_tail takes over: the call (YCbqGcallW.v aj_call_xW), v's node at the return state by
   its place (a harness block, another block, a caller's fake frame), a fresh seat at +0x60 (ss_ps3), the str store
   and the epilogue (YC80xf_inv.v paj_run_xf_inv: v may be in a caller's fake frame), the ret (paj_ret_at), the post.
   Texts: the kit's cut 7cdbb61b5fa0 (lib/A/PRH_FnPj.v 5aca5cbe2cfb, PRH_FnAlloc.v 4d8aeba047e5, PRH_Base.v
   ef7c8ca98529, PRH_Reader.v 4266e709561a). History: re-fitted 2026-10-29 from the old-pin kit preset-tree-at-2026-10-29T13-54-32Z.tsv (sha256 14e543909afe; internal record) onto the
   #102 kit, then onto the batch and the cut: the ledger's most / own threaded, fpre's frm_zero passed to fuzz_strdup, fuzz_strdup's
   post-implication position arms applied at pj_string's own run, kept_img's per-instance pa_hi bound in pal_lit).
   Engine on the cut: YGcallMxmn.v 3c08bbab8292, YC80x.v 14f84f225e8f, YC1fPx.v 7814b594066f, YSRrMemnorm.v
   5ffa8525936b, YCbqGcallW.v fb6aa11676a2, YC80xf_inv.v 082f0c430210; PRW_StepKit.v 0df3991c13f4; listing
   Listing_prog.v 7ed1529926bd, PAImg_prog.v 505a51ff7d08 (first proved with a Theorem Labs lane's set s1b 459129c18903 over listing
   v4).
   Image-free pieces: lib/A/Prog/PjStringCommon.v (one copy with image B: pjs_bytes, pjs_hdr, pjs_node_str, pjs_fd0,
   the pjs1_ and pjs2_ lemmas), S6PjCommon.v. A's own: ps_vplace, ps_vheads, ps_cstr_kept, pjs0_lit_ok_A (A's twin of image B's
   pjs0_lit_ok, over the image fact pal_lit and the kit fact pal_lit_sh).
   SECTION HYPOTHESES (the theorem's premises): the image facts Hent / Hobj / PAB / pal_pst_img / pal_lit (discharged at
   PI_prog_A: the entry slot, the GOT / shadow cell bytes, IMG_LO, S1ImgA.v pst_in_img_A, and pal_lit by
   S6PalLitRefute.v pal_lit_A, vm_compute at the instance); the kit fact pal_lit_sh (the kit's shadow facts, as image
   B's pjs_g_lit_of_kit); the memset row AIM (a Theorem Labs lane's aintrin_realizes_xm); and fuzz_strdup's text STRDUP :
   tfuzz_strdup_specX (a Theorem Labs lane, post-implication position arms).
   pal_lit RESTATED 2026-10-29 (owner 16:50Z): the literal step asks only for the ONE byte it reads (arodata_okP's
   form); the old 8-byte not-owned-static claim is refuted at the instance (S6PalLitRefute.v pal_lit_unsat_A).
   Rule 24: no donor (proof-index pj_string 2026-10-29: released hits are the plain / UBSan images only; the B
   lane cold/h-rw-man-5-b-pjstring is image B's walk; its image-free lemmas are shared through PjStringCommon.v).
   Numerals: 32 (LENGTH: pj_string's frame), 56 / 16 / 24 / 8 / 4 (LENGTH: the node, str field, words), 4 (WORD: the
   tag of PjTree.JStr), 52 / 96 (DERIVED: return slots, listing offsets from AF_ps), 2 ^ 44 / 2 ^ 46 / 2 ^ 47
   (DERIVED: shadow and stack bounds); atom indices (DERIVED: the engine's numbering). No address literal: addresses
   are pa_sigma / pa_val of PAImg_prog.v. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the texts with the keep of a memory invariant P (generic over the listing and the image) ======== *)
Section xp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* The kit's tpj_string_specX (PRH_FnPj.v 5aca5cbe2cfb at the kit's cut; first written against an earlier batch commit
   62dc819e58ff, and at the cut the live bound holds only under cnt <> fail: the run's strtod model keyed to ReaderRes.jr_strtod, DW dropped, the consumer-allocation entry premise
   prh_cons_from, the dead refusal arm (cnt <> fail -> a <> 0) of DEAD-PJSTRING) with fpostWm .. Q =
   fpostW .. (fQmn mem Q) generalised to fpostW .. (fun .. => Q .. /\ (P mem -> P mem')): equal to the text by
   conversion at P := YAkMemnorm.memnorm segs (tpj_string_specX_of_P below) *)
Definition tpj_string_specXP (P : (word -> option byte) -> Prop) (CTX0 : list (list Z)) : Prop :=
  forall (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch d v s (cs : list Z) Lam peak cnt fail ran most own,
  fpre B ARx STK_pj_string ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 -> room_live_cf S ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist S ->
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod rp_x rp_os rp_i (length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail)) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 s ->
  fwin ly W regs mem d -> prhPj_slot B STK_pj_string d ly S Lam W regs mem v -> v < YM05.alloc_ceiling ->
  prh_head_wide ->
  (s = 0 /\ cs = [] \/
   s <> 0 /\ cstr_ok W mem s cs /\ kept_at B Lam s (Z.of_nat (length cs) + 1) /\
   (s + Z.of_nat (length cs) + 1 <= v \/ v + 56 <= s)) ->
  Z.of_nat (length cs) + 1 + cf_head < cf_malloc_max ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (cnt <> fail -> blocks_bytes S + LIVE_pj_string (Z.of_nat (length cs)) <= LIVE_MAX) ->
  prh_run_at ReaderRes.jr_strtod rp_x rp_os rp_i (prhPj_string_evs (Z.of_nat (length cs)) cnt fail) ->
  SRr segs W (cfg_at segs (pa_sigma AS_pj_string) regs mem md)
    (fpostW B ARx SK STK_pj_string d [(v, v + 56)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S' /\
       exists a, prh_alloc_post B (Z.of_nat (length cs) + 1) ly S Hp W Lam peak cnt fail ran most own a ly' S' Hp' W' mem' /\
       (cnt <> fail -> a <> 0) /\
       (a <> 0 \/ cnt = fail ->
          exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod rp_x rp_os
            (rp_i + length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail))%nat rp_H0 hist' S') /\
       (a <> 0 -> getr regs' 10 = w64 0 /\
          pj_nodeR segs (rdW W' mem') (prh_lin ((a, Z.of_nat (length cs) + 1) :: Lam)) v (PjTree.JStr cs)
            [(a, Z.of_nat (length cs) + 1)]) /\
       (a = 0 -> getr regs' 10 = w64 (-1) /\ pj_rwR segs (rdW W' mem') v /\
          bytes_at W' mem' v ([4; 0; 0; 0] ++ repeat 0 52) /\
          pj_fdR segs (rdW W' mem') (prh_lin Lam) 0 v [])) /\
       (P mem -> P mem'))).
Lemma tpj_string_specX_of_P : forall CTX0, tpj_string_specXP (YAkMemnorm.memnorm segs) CTX0 ->
  tpj_string_specX B ARx SK CTX0.
Proof. intros CTX0 H. exact H. Qed.
End xp.

(* ======== image A's numbers ======== *)
(* pj_string's offset in the listing (DERIVED: its slot times 4, PAImg_prog A_entry_pj_string) *)
Definition AF_ps : Z := 4 * Z.of_nat (A_prog_slot AS_pj_string).
(* the PAddHi of the literal .str.1 ("", s = NULL's replacement) at slot 21 of pj_string (A 0x86bac) *)
Definition ps_addhi_off (k : nat) : Z :=
  match nth (A_prog_slot AS_pj_string + k) A_prog_listing (PW 0) with PAddHi _ _ _ _ off => off | _ => 0 end.
Definition ps_addhi_atom (k : nat) : nat :=
  match nth (A_prog_slot AS_pj_string + k) A_prog_listing (PW 0) with PAddHi _ _ _ a _ => a | _ => 0%nat end.
(* the shadow base atom (an extra env slot, 32) and the span the token engine checks it against *)
Definition PS_Bx : sv := SOff 32 0.
Definition PS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* ---- the entry seat: the own frame of 32 bytes below the entry sp (atom 2), the GOT word of the shadow base and the
   shadow-base cell ---- *)
Definition ps_regions : smem := [stack_region 32; got_regionP; bcell_regionP 32].
Definition ps_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ps : sstate := mkSS AF_ps sr_atoms ps_regions None ps_facts.
(* ---- the seat after __asan_memset, at its return slot (AF_ps + 52): sp is atom 2 (the entry sp - 32), s0 = v (atom 8),
   s1 = s (atom 9), s2 = the shadow base (atom 18); the frame holds the entry ra, s0, s1, s2 (atoms 32 .. 35); v's node
   with the write window of the type word [0, 4) ---- *)
Definition PS_Bx2 : sv := SOff 18 0.
Definition ps_frame2 : YP09.region := YP09.mkRegion (Some 2%nat) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
   YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition ps_vreg2 : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 0 4 [].
Definition ps_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_ps2 : sstate := mkSS (AF_ps + 52) sr_atoms [ps_frame2; ps_vreg2] None ps_facts2.
(* ---- the seat at fuzz_strdup's return slot (AF_ps + 96): the frame as at +0x34 (read-only), v's node with the write
   window of the str word [16, 24) (`sd a0, 0(s0)` after `addi s0, s0, 16`) ---- *)
Definition ps_vreg3 : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 16 24 [].
Definition ss_ps3 : sstate := mkSS (AF_ps + 96) sr_atoms [ps_frame2; ps_vreg3] None ps_facts2.
(* v's 56 bytes as a shadow entry of the token engine (their shadow is checked once, from the seat) *)
Definition PS_SH2 : list shent := [mkSHE 8 0 56].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
(* the literal "" pj_string passes when s = NULL *)
Definition PS_LIT : Z := VAL (ps_addhi_atom 21) + ps_addhi_off 21.

Definition ps_E (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Definition ps_E2 (regs : bvmap 5 word) (ra s0 s1 s2 : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) [ra; s0; s1; s2])).
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis TL : PALib B.
(* image facts, discharged at PI_prog_A: the entry (DERIVED: slot * 4, PAImg_prog A_entry_pj_string), the GOT word of
   the shadow base and the shadow cell lie in the image's segments, the image start *)
Hypothesis Hent : SIGMA AS_pj_string = BASE + AF_ps.
Hypothesis Hobj : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i) /\ in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
(* the callees: the memset row with its memnorm keep (a Theorem Labs lane's YGcallMxmn.v aintrin_realizes_xm) and the text of
   fuzz_strdup (PRH_FnAlloc.v, m-form) *)
Hypothesis AIM : aintrin_realizes_xm SEGS B ARx OSet (SIGMA AS___asan_memset).
(* fuzz_strdup's text (the kit, PRH_FnAlloc.v 4d8aeba047e5 on the kit's cut 7cdbb61b5fa0: post-implication position
   arms and the outcome conjunct under the run hypothesis; the hull budget for its one event at entry, which ps_tail
   pays from pj_string's run position, and the hull use in its post) *)
Hypothesis STRDUP : tfuzz_strdup_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK.
(* image facts, discharged at PI_prog_A: alloc.c's statics are image bytes (lib/A/Prog/S1ImgA.v pst_in_img_A) *)
Hypothesis pal_pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
(* image fact, discharged at PI_prog_A (witness lib/A/Prog/S6PalLitRefute.v pal_lit_A): pj_string's "" literal PS_LIT
   (.str.1, A 0x21420, ps_lit_A): 64 bytes inside the image, 8-aligned; THE ONE BYTE THE STEP READS (PS_LIT) is
   read-only, zero in the ROM, neither runtime-owned nor errno (arodata_okP's form, so the fpre gives its value); the
   other 7 bytes of its granule are image bytes (cstr_ok's tail-granule visibility, through mbyte's ROM fallback), with
   NO claim about who owns them; the granule's shadow is the const cell 1.
   RESTATED 2026-10-29 (owner 16:50Z): the old text asked `~ Exists (in_zr a) (as_owned_static B)` for all 8 bytes
   PS_LIT .. PS_LIT + 7, FALSE at the instance (S6PalLitRefute.v pal_lit_unsat_A: (0x21421, 31), ASan's redzone after
   the 1-byte global, is owned-static).
   THE pa_hi BOUND (2026-10-29, #102 kit): kept_img is PER-INSTANCE (pa_lo + 64 <= p /\
   p + n + 64 <= pa_hi of this Section's PA). The low bound follows from IMG_LO's by PAB; no premise relates pa_hi to
   IMG_TOP, so the high bound is stated over pa_hi. The IMG_LO / IMG_TOP bounds stay: the kit fact pal_lit_sh
   (unchanged) and cstr_ok's bounds are stated over them. At PI_prog_A pa_hi is IMG_TOP. *)
Hypothesis pal_lit :
  IMG_LO + 64 <= PS_LIT /\ PS_LIT + 8 + 64 <= IMG_TOP /\ PS_LIT + 8 + 64 <= @pa_hi _ _ PA /\ PS_LIT mod 8 = 0 /\
  in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) PS_LIT /\ seg_rom SEGS (Z_to_bv 64 PS_LIT) = Some (Z_to_bv 8 0) /\
  ~ Exists (in_zr PS_LIT) (as_owned_static B) /\ ~ (as_errno B <= PS_LIT < as_errno B + 4) /\
  (forall a, PS_LIT < a < PS_LIT + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None) /\
  (forall ly, In (z1 (ANum (shadow_addr PS_LIT)) 1) (as_const B ly)).
(* kit fact, a STATE claim on every allocator state (not a layout claim): the image's shadow map is visible; the kit's
   shadow facts give it, as image B's pjs_g_lit_of_kit (lib/B/Prog/pj_string_top.v:101). Split off the old pal_lit
   unchanged. *)
Hypothesis pal_lit_sh :
  forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
    aview SEGS (w_H W) mem (shadow_addr a) <> None.
Local Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

Lemma ps_frames : STK_pj_string (PI := prh_img_A) = 32 + STK_fuzz_strdup (PI := prh_img_A) /\
  STK_fuzz_strdup (PI := prh_img_A) = 16448.
Proof. split; vm_compute; reflexivity. Qed.

Lemma ps_entry : forall ly S Hp W (regs : bvmap 5 word) mem md ch,
  afn_pre_x SEGS B ARx (STK_pj_string (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  st_ok_pi SEGS VAL (ps_E regs) ss_ps (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_ps)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PS_Bx [] (ps_E regs) (mrestrict (w_H W) mem).
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
destruct ps_frames as [FS FS2].
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := ps_E regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold ps_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold ps_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold ps_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
rewrite restrict_mkst_fx. unfold ss_ps. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ps_regions, stack_region, got_regionP, bcell_regionP.
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
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 PS_Bx SHADOW_OFF);
    [cbn [sv_denot PS_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold ps_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0 R0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12 R12).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hceil C1 C2 C3 C4 C5 HgotR HcellR HgotR7 HcellR7 HgcD FS FS2 Hes.
  unfold kLowMemEnd. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ps_facts f_atoms atoms_ok].
  split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
    revert Hslo Hshi H47 Hceil C1 FS FS2 Hes Hstk0 Hal16; clear; intros; repeat split; lia|].
  split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* where v's 56 bytes lie (prhPj_slot's place without its caller-window case, v < alloc_ceiling <= the entry sp): each
   byte in a live allocator block or in a frame of the entry's frames, and off the image *)
Lemma ps_vplace : forall ly S Hp W regs mem md d Lam peak cnt fail ran most own v,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhPj_slot (cp := CP) (PA := PA) B (STK_pj_string (PI := prh_img_A)) d ly S Lam W regs mem v ->
  v < YM05.alloc_ceiling -> YM05.alloc_ceiling <= spZ regs ->
  forall a, v <= a < v + 56 ->
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos)))) /\ ~ in_img SEGS a.
Proof.
intros ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSL Hv Hsp a Ha.
destruct HSL as (H4096 & HAT & _).
assert (HP : (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos)))).
{ destruct HAT as [(a0 & k0 & Hin & Ha0 & Hk0) | [(b & m & Hin & _ & Hb & Hm) | [(cid & pos & Hin & Hf & Hfm) | (Hs & _)]]].
  - left. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin) as (Hk & Hab & _).
    exists (a0 - @cf_head CP), (k0 + @cf_head CP). split; [exact Hab|].
    change (@cf_head CP) with 16 in *. pose proof (req_size_pos (k0 + 16) ltac:(lia)). lia.
  - left. exists b, m. split; [exact Hin|]. pose proof (req_size_pos m ltac:(lia)). lia.
  - right. exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - exfalso. lia. }
split; [exact HP|].
destruct HP as [(b & n & Hin & Hr) | (cid & pos & Hin & Hr)].
- exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b n a HAR Hin Hr).
- unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HAR Hin Hr).
Qed.
(* a byte off the image whose view is defined is writable *)
Lemma ps_wr_of_view : forall H (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS H m a <> None -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a Ha Hn Hv. unfold aview, mbyte in Hv. rewrite (seg_rom_none SEGS a Ha Hn) in Hv.
unfold writable_at, wview. destruct (mrestrict H m (Z_to_bv 64 a)) as [b|]; [discriminate | cbn in Hv; congruence].
Qed.

(* v's node bytes after the memset and the type store: the type word 4, every other byte 0 *)
Lemma ps_garr8_node : forall H (m : word -> option byte) v,
  val_mem SEGS (mrestrict H m) v 4 4 -> (forall i, 4 <= i < 56 -> aview SEGS H m (v + i) = Some 0) ->
  garr8 SEGS (mrestrict H m) v (pjs_bytes 0).
Proof.
intros H m v HT HZ j Hj. rewrite pjs_bytes_len in Hj.
split; [|exact (proj1 (Forall_forall _ _) (pjs_bytes_range 0) _ (nth_In _ _ ltac:(rewrite pjs_bytes_len; exact Hj)))].
rewrite pjs_bytes_nth by exact Hj.
intros k Hk. assert (k = 0%nat) by lia. subst k.
replace (v + Z.of_nat j + Z.of_nat 0) with (v + Z.of_nat j) by lia.
destruct (Nat.ltb_spec j 4) as [Hj4 | Hj4].
- rewrite (HT j Hj4). do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
- assert (E0 : (if (j =? 0)%nat then 4 else if ((16 <=? j) && (j <? 24))%nat then le_byte 0 8 (j - 16) else 0) = 0).
  { destruct (Nat.eqb_spec j 0); [lia|]. destruct ((16 <=? j) && (j <? 24))%nat; [apply pjs_le_byte_0 | reflexivity]. }
  rewrite E0.
  assert (Hz : aview SEGS H m (v + Z.of_nat j) = Some 0) by (apply HZ; lia).
  destruct (aview_byte SEGS H m _ 0 Hz) as (b & Hb & Hv & _).
  rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite <- Hv. vm_compute. reflexivity.
Qed.

(* the bytes of a byte array off the image are writable *)
Lemma ps_wr_of_garr8 : forall H (m : word -> option byte) p l, garr8 SEGS (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> 0 <= a < 2 ^ 64 /\ ~ in_img SEGS a) ->
  forall a, p <= a < p + Z.of_nat (length l) -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m p l Hg Hn a Ha. destruct (Hn a Ha) as [Har Hni].
apply ps_wr_of_view; [exact Har | exact Hni |].
destruct (Hg (Z.to_nat (a - p)) ltac:(lia)) as [Hv _]. specialize (Hv 0%nat ltac:(lia)).
replace (p + Z.of_nat (Z.to_nat (a - p)) + Z.of_nat 0) with a in Hv by lia.
unfold aview. rewrite Hv. cbn. discriminate.
Qed.

(* a string (cstr_ok) survives a change that keeps every view below alloc_ceiling outside [lo, hi), an application
   range the string's bytes and granule miss *)
Lemma ps_cstr_kept : forall (Wa Wb : world SEGS) m m' p l lo hi, cstr_ok (PA := PA) Wa m p l ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (lo <= a < hi) -> aview SEGS (w_H Wb) m' a = aview SEGS (w_H Wa) m a) ->
  (p + Z.of_nat (length l) + 1 <= lo \/ hi <= p) -> lo mod 8 = 0 -> amem_range lo (hi - lo) -> lo < hi ->
  cstr_ok (PA := PA) Wb m' p l.
Proof.
intros Wa Wb m m' p l lo hi HC HA Hd Hlo Hamr Hlh. destruct HC as ((Hg & Hnz) & H4096 & Hceil & H32 & Hamr8 & HRA & HH & Hv).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range in Hamr. unfold YGcfStr.amem_range8 in Hamr8.
split; [split; [|exact Hnz]|].
- apply (gs_garr8_move Wa Wb m m' p p (l ++ [0]) Hg). intros j Hj. rewrite length_app in Hj. cbn in Hj.
  apply HA; lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Hamr8|]. split; [|split].
  + eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)).
    apply HA; [lia|]. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  + intros s0 Hs. pose proof (pjs2_hull_bounds p (Z.of_nat (length l) + 1) s0 ltac:(lia) ltac:(lia)
      ltac:(unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia) Hs) as Hb.
    rewrite HA; [apply HH; exact Hs | unfold kHighShadowEnd in *; lia |].
    unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. lia.
  + intros a Ha.
    (* the NUL's aligned word lies below alloc_ceiling: the string ends below it (cstr_ok's ceiling bound, which the batch kit
       states without the old `+ 8`) and alloc_ceiling is page-aligned (YM05.alloc_ceiling_value) *)
    assert (Hqa : 0 <= a < YM05.alloc_ceiling).
    { pose proof YM05.alloc_ceiling_value as [_ Hc4096].
      set (e := p + Z.of_nat (length l)) in *.
      pose proof (Z.div_mod e 8 ltac:(lia)) as Ee. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Re.
      pose proof (Z.div_mod YM05.alloc_ceiling 4096 ltac:(lia)) as Ec. rewrite Hc4096 in Ec.
      clear - Ha Hceil H4096 Ee Re Ec. lia. }
    rewrite HA; [apply Hv; exact Ha | exact Hqa |]. lia.
Qed.

(* the head words of the harness blocks miss v's 56 bytes: a head word is the first 8 bytes of its block, and v's place
   is a harness block's user range (16 bytes above that block's head), another block or a fake frame *)
Lemma ps_vheads : forall ly S Hp W regs mem md d Lam peak cnt fail ran most own v,
  ARx ly S Hp W mem md ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhPj_slot (cp := CP) (PA := PA) B (STK_pj_string (PI := prh_img_A)) d ly S Lam W regs mem v ->
  v < YM05.alloc_ceiling -> YM05.alloc_ceiling <= spZ regs ->
  forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ (v <= a - @cf_head CP + i < v + 56).
Proof.
intros ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSL Hv Hsp a k i Hin Hi Hx.
destruct HSL as (H4096 & HAT & _).
change (@cf_head CP) with 16 in *.
destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk & Hab & _).
change (@cf_head CP) with 16 in *.
assert (R : 1 <= req_size (k + 16) /\ k + 16 <= req_size (k + 16)) by (apply req_size_pos; lia).
destruct HAT as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & Hnl & Hb & Hm) | [(cid & pos & Hin2 & Hf & Hfm) | (Hs & _)]]].
- destruct (Z.eq_dec a a0) as [-> | Hne]; [lia|].
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin0) as (Hk0' & Hab0 & _).
  change (@cf_head CP) with 16 in *.
  assert (R0 : 1 <= req_size (k0 + 16) /\ k0 + 16 <= req_size (k0 + 16)) by (apply req_size_pos; lia).
  assert (Hne' : (a - 16, k + 16) <> (a0 - 16, k0 + 16)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab0 Hne') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- assert (Hne' : (a - 16, k + 16) <> (b, m)).
  { intros E. injection E as E1 E2. apply Hnl. change (@cf_head CP) with 16. rewrite <- E1, <- E2.
    replace (a - 16 + 16) with a by lia. replace (k + 16 - 16) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin1 Hne') as Hd.
  pose proof (req_size_pos m) as Rm. assert (Hm0 : 0 <= m) by lia. specialize (Rm Hm0).
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* the "" literal at the call: an image string under route (a), A's twin of image B's pjs0_lit_ok
   (lib/B/Prog/pj_string_seg_ent.v:245-292), over the image fact pal_lit (the one byte read) and the kit fact
   pal_lit_sh *)
Lemma pjs0_lit_ok_A : forall ly S Hp W m md Lam, ARx ly S Hp W m md ->
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) m) ->
  cstr_ok (PA := PA) W m PS_LIT [] /\ kept_at (PA := PA) B Lam PS_LIT 1.
Proof.
intros ly S Hp W m md Lam HAR HROD.
destruct pal_lit as (GLO & GTOP & GHI & G8 & Hro & Hrom & Hno & Her & GTL & GL2).
pose proof pal_lit_sh as GL3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CI : IMG_LO = 65536) by (vm_compute; reflexivity).
assert (CT : IMG_TOP = 6291456) by (vm_compute; reflexivity).
(* the byte read: arodata_okP (the fpre) gives its ROM value *)
assert (L0 : aview SEGS (w_H W) m PS_LIT = Some 0) by (rewrite (HROD PS_LIT Hro Hno Her), Hrom; reflexivity).
(* the rest of the granule: image bytes, visible through mbyte's ROM fallback, whoever owns them *)
assert (LTL : forall a, PS_LIT < a < PS_LIT + 8 -> aview SEGS (w_H W) m a <> None).
{ intros a Ha. unfold aview, mbyte. destruct (mrestrict (w_H W) m (Z_to_bv 64 a)); [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) eqn:Er; [discriminate|]. exfalso. exact (GTL a Ha Er). }
assert (LSH : aview SEGS (w_H W) m (shadow_addr PS_LIT) = Some 1).
{ pose proof (alx_const_cells SEGS B ARx LAWS ly S Hp W m md HAR) as HC.
  rewrite Forall_forall in HC. pose proof (HC _ (GL2 ly)) as Hz.
  unfold cell_holds in Hz. cbn [z1 c1 c_at c_val c_w aeval] in Hz.
  specialize (Hz 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hz. rewrite Z.add_0_r in Hz. rewrite Hz.
  reflexivity. }
split.
- unfold cstr_ok, cstr. cbn [length app Z.of_nat].
  split; [split; [|constructor]|].
  { intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
    split; [|cbn [nth]; lia]. intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
    destruct (aview_byte SEGS (w_H W) m (PS_LIT + Z.of_nat 0 + Z.of_nat 0) 0) as (b & Hb & Hv & _).
    { rewrite !Z.add_0_r. exact L0. }
    rewrite Hb. f_equal. apply bv_eq. rewrite <- Hv. vm_compute. reflexivity. }
  split; [rewrite CI in GLO; lia|].
  split; [rewrite CT in GTOP; unfold YM05.alloc_ceiling in *; lia|].
  split; [lia|].
  split; [unfold YGcfStr.amem_range8; left; rewrite CT in GTOP; unfold kLowMemEnd in *; lia|].
  split.
  { intros x Hx. assert (Ex : x = PS_LIT) by lia. subst x. exists 1. split.
    - unfold shadow_of_addr. exact LSH.
    - right. lia. }
  split.
  { intros s Hs. unfold shadow_addr in Hs. unfold SHADOW_OFF in Hs.
    assert (Es : shadow_addr ((s - SHADOW_OFF) * 8) = s).
    { unfold shadow_addr. rewrite Z.div_mul by lia. lia. }
    rewrite <- Es. apply (GL3 ly S Hp W m md _ HAR). rewrite CI, CT in *. unfold SHADOW_OFF in *. lia. }
  intros a Ha. apply LTL. lia.
- right; right. unfold kept_img. split; [rewrite PAB; clear - GLO; lia|]. split; [clear - GHI; lia|].
  intros a Ha. assert (Ea : a = PS_LIT) by lia. subst a.
  split; [exact Hro|]. split; [exact Hno|]. split; [exact Her|].
  right. exists 1. split; [exact GL2 | right; lia].
Qed.

Section p.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
(* the segment crosses the memset and fuzz_strdup calls, whose keeps are the memnorm one *)
Hypothesis PCALL : srr_inv_call SEGS Pm.
Variable CTX0 : list (list Z).

#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
(* ======== the call of fuzz_strdup and the tail: both arms of `bnez s1` reach the call with a0 = sa ======== *)
Lemma ps_tail : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own
  regs2 mem2 sa regsc memc mdc k,
  fpre (PA := PA) B ARx (STK_pj_string (PI := prh_img_A)) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  (* the run has at most 4 calls: fuzz_strdup's hull budget is paid from the position *)
  (length rp_os <= 4)%nat ->
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail)) ->
  fwin (PA := PA) ly W regs mem d ->
  prhPj_slot (cp := CP) (PA := PA) B (STK_pj_string (PI := prh_img_A)) d ly S Lam W regs mem v ->
  v < YM05.alloc_ceiling ->
  (s = 0 /\ cs = [] \/ s <> 0 /\ cstr_ok (PA := PA) W mem s cs /\ kept_at (PA := PA) B Lam s (Z.of_nat (length cs) + 1) /\
     (s + Z.of_nat (length cs) + 1 <= v \/ v + 56 <= s)) ->
  Z.of_nat (length cs) + 1 + @cf_head CP < cf_malloc_max ->
  prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (cnt <> fail -> blocks_bytes S + LIVE_pj_string (Z.of_nat (length cs)) <= LIVE_MAX) ->
  prh_run_at rp_sm rp_x rp_os rp_i (prhPj_string_evs (Z.of_nat (length cs)) cnt fail) ->
  (* after the memset: v's 56 bytes 0, the frame's four words, every other byte as at the entry *)
  (forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem2 (v + i) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (spZ regs - 32 - ESTACK <= a < spZ regs) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -8) 8 (bv_unsigned (getr regs 1%bv)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -16) 8 (bv_unsigned (getr regs 8%bv)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -24) 8 (bv_unsigned (getr regs 9%bv)) ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -32) 8 (bv_unsigned (getr regs 18%bv)) ->
  spZ regs2 = spZ regs - 32 -> getr regs2 8%bv = w64 v -> getr regs2 18%bv = Z_to_bv 64 SHADOW_OFF ->
  getr regs2 3%bv = w64 (as_gp B) -> getr regs2 4%bv = w64 (as_tp B) ->
  (forall r : bv 5, In r [19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr regs2 r = getr regs r) ->
  (* the call state *)
  AJ (STK_pj_string (PI := prh_img_A) + d) (spZ regs + d) [(v, v + 56)] ly S Hp W mem md [] ly S Hp W memc mdc k ->
  (Pm mem -> Pm memc) ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_ps + 96)) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr regsc r = getr regs2 r) ->
  getr regsc 10 = w64 sa ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) ->
  val_mem SEGS (mrestrict (w_H W) memc) v 4 4 ->
  (s = 0 /\ sa = PS_LIT \/ s <> 0 /\ sa = s) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_fuzz_strdup)) memc (seg_rom SEGS)) mdc)
    (fpostW (PA := PA) B ARx SK (STK_pj_string (PI := prh_img_A)) d [(v, v + 56)] regs
       ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S' /\
       exists a, prh_alloc_post (PA := PA) B (Z.of_nat (length cs) + 1) ly S Hp W Lam
         peak cnt fail ran most own a ly' S' Hp' W' mem' /\
       (cnt <> fail -> a <> 0) /\
       (a <> 0 \/ cnt = fail ->
          exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
            (rp_i + length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail))%nat rp_H0 hist' S') /\
       (a <> 0 -> getr regs' 10 = w64 0 /\
          pj_nodeR SEGS (mrestrict (w_H W') mem') (prh_lin ((a, Z.of_nat (length cs) + 1) :: Lam)) v (PjTree.JStr cs)
            [(a, Z.of_nat (length cs) + 1)]) /\
       (a = 0 -> getr regs' 10 = w64 (-1) /\ pj_rwR SEGS (mrestrict (w_H W') mem') v /\
          bytes_at (PA := PA) W' mem' v ([4; 0; 0; 0] ++ repeat 0 52) /\
          pj_fdR SEGS (mrestrict (w_H W') mem') (prh_lin Lam) 0 v [])) /\
       (Pm mem -> Pm mem'))).
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own
  regs2 mem2 sa regsc memc mdc k
  [HPRE [HROD [HTOP [HRAZ HFRM]]]] HUNIV HROOM HRP HLEN HCONS HFWIN HSLOT HCEIL HSTR HMAX HLED HLIVE HEV
  Hset KM2 VRA VS0 VS1 VS2 Sp2 G8 G18 G3 G4 G19 HJc HPc R1c KKc R10c KC VT HSA.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct ps_frames as [FS FS2]. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof (ps_vplace ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSLOT HCEIL ltac:(lia)) as VPL.
pose proof (ps_vheads ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSLOT HCEIL ltac:(lia)) as VHD.
pose proof HSLOT as (H4096 & HAT & HRW & HAMR & HWIN & HRA & HHU).
assert (Hv47 : 4096 <= v /\ v + 56 <= YM05.alloc_ceiling).
{ split; [exact H4096|]. destruct (VPL (v + 55) ltac:(lia)) as [[(b & n & Hin & Hr) | (cid & pos & Hin & Hr)] _].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & Hc & _). lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia. }
assert (HRW8 : v mod 8 = 0) by (destruct HRW as [H8 _]; exact H8).
lazymatch eval vm_compute in (AF_ps + 96) with ?n => assert (EAF2 : AF_ps + 96 = n) by (vm_compute; reflexivity) end.
(* ---- the call state's memory: as at the entry off v's 56 bytes and pj_string's frame; v's node bytes ---- *)
assert (KMc : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (spZ regs - 32 - ESTACK <= a < spZ regs) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a)
  by (intros a Ha Hv Hw; rewrite KC by lia; apply KM2; assumption).
assert (Zc : forall i, 4 <= i < 56 -> aview SEGS (w_H W) memc (v + i) = Some 0)
  by (intros i Hi; rewrite KC by lia; apply Hset; lia).
pose proof (ps_garr8_node (w_H W) memc v VT Zc) as VBc.
assert (HVWc : forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W) memc) a).
{ intros a Ha. apply (ps_wr_of_garr8 (w_H W) memc v (pjs_bytes 0) VBc); [|rewrite pjs_bytes_len; exact Ha].
  intros x Hx. rewrite pjs_bytes_len in Hx. split; [unfold YM05.alloc_ceiling in *; lia | exact (proj2 (VPL x ltac:(lia)))]. }
assert (KLc : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (v <= a < v + 56) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a).
{ intros a Ha Hv. apply KMc; [unfold YM05.alloc_ceiling in *; lia | exact Hv | rewrite FS, FS2 in Hslo; lia]. }
assert (HRODc : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) memc)).
{ intros a Hro Hos Her. pose proof (gs_ro_img a Hro) as Hai. pose proof (Hsegs a Hai) as Hal.
  rewrite KLc; [exact (HROD a Hro Hos Her) | unfold kLowMemEnd in Hal; lia | intros Hv; exact (proj2 (VPL a Hv) Hai)]. }
assert (HLEDc : prh_ledger (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W memc Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W memc Lam peak cnt fail ran most own HLED).
  - intros a Ha. pose proof (pal_pst_img a Ha) as Hai. pose proof (Hsegs a Hai) as Hal.
    apply KLc; [unfold kLowMemEnd in Hal; lia | intros Hv; exact (proj2 (VPL a Hv) Hai)].
  - intros a k0 i Hin Hi. change (@cf_head CP) with 16 in *.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k0 _ _ HLED Hin) as (Hk0 & Hab & _).
    change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
    pose proof (req_size_pos (k0 + 16) ltac:(lia)) as Rq.
    apply KLc; [lia|]. pose proof (VHD a k0 i Hin Hi) as Hn. change (@cf_head CP) with 16 in Hn. exact Hn.
  - intros a k0 _ H. exact H.
  - apply Permutation_refl. }
(* the string fuzz_strdup duplicates *)
assert (HSTRc : cstr_ok (PA := PA) W memc sa cs /\ kept_at (PA := PA) B Lam sa (Z.of_nat (length cs) + 1)).
{ destruct HSA as [(Hs0 & ->) | (Hs0 & ->)].
  - destruct HSTR as [(_ & ->) | (Hn & _)]; [|contradiction].
    pose proof (ajx_ar HJc) as HARc.
    exact (pjs0_lit_ok_A ly S Hp W memc mdc Lam HARc HRODc).
  - destruct HSTR as [(Hz & _) | (_ & HC & HK & Hdj)]; [contradiction|].
    split; [|exact HK].
    apply (ps_cstr_kept W W mem memc s cs v (v + 56) HC); [exact KLc | | exact HRW8 | | lia].
    + destruct Hdj as [Hd | Hd]; [left; lia | right; lia].
    + replace (v + 56 - v) with 56 by lia. exact HAMR. }
destruct HSTRc as (HCSTRc & HKATc).
(* the call's registers *)
assert (HSPC : spZ regsc = spZ regs - 32) by (unfold spZ at 1; rewrite (KKc 2%bv) by (cbn; tauto); exact Sp2).
assert (HGPc : getr regsc 3 = w64 (as_gp B)) by (rewrite (KKc 3%bv) by (cbn; tauto); exact G3).
assert (HTPc : getr regsc 4 = w64 (as_tp B)) by (rewrite (KKc 4%bv) by (cbn; tauto); exact G4).
assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
{ unfold s0Z. rewrite (KKc 8%bv) by (cbn; tauto). rewrite G8. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof (pa_base_lo (PL := PL_prog_A) (PI := PA)) as HBLO. rewrite PAB in HBLO. unfold IMG_LO in HBLO.
pose proof (@pa_B_ok _ _ PA) as HB.
assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + (AF_ps + 96))))
  by (apply (ret_ok_codeptr_v (PI := PA)); [rewrite EAF2; lia | rewrite EAF2; reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (AF_ps + 96)))) by (rewrite EAF2; rewrite unsigned_lit_small by lia; lia).
assert (HRAZc : raZ regsc < YM05.alloc_ceiling).
{ unfold raZ. rewrite R1c. pose proof (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_ps + 96)) as HSL.
  rewrite unsigned_lit_small by (rewrite EAF2; lia). apply HSL; [rewrite EAF2; lia | vm_compute; reflexivity]. }
destruct (PresetRoomCounts.counts_of_room_pos_rl rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HRP) as [HSEC HC24].
(* fuzz_strdup's hull budget for its one event HMal (len + 1 + cf_head), paid from pj_string's run position: the run
   has at most 4 calls, so the meters at any position leave one call's worth (PresetHullPay.hull_budget_of_room_pos,
   the count route of PresetDrvHullA.drv_cf_hull_ok_at_call_A), and one event of a request below cf_malloc_max is
   at most one call's worth (PresetHullPay.hull_nt_one_mal) *)
assert (HHB : PresetHullBudget.hull_budget S [PresetReqAt.HMal (Z.of_nat (length cs) + 1 + @cf_head CP)]).
{ assert (Hr : 0 <= Z.of_nat (length cs) + 1 + @cf_head CP <= 2 ^ 30).
  { change (@cf_malloc_max CP) with 402653184 in HMAX. change (@cf_head CP) with 16 in HMAX |- *.
    change (2 ^ 30) with 1073741824. lia. }
  destruct (PresetHullPay.hull_nt_one_mal _ Hr) as [HN HT].
  exact (PresetHullPay.hull_budget_of_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S _ HLEN HRP HN HT). }
(* ======== the call: fuzz_strdup's text (with the room-position advance) at the callee window 0, footprint [] ======== *)
eapply SRr_bind.
{ eapply (aj_call_xW (SK := SK) SEGS B PST ARx LAWS Hsegs W regsc memc (SIGMA AS_fuzz_strdup)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_fuzz_strdup (PI := prh_img_A)) 0 [] (-32 - d) (Z_to_bv 64 (BASE + (AF_ps + 96))) [] _
    HJc).
  - rewrite HSPC. lia.
  - lia.
  - lia.
  - rewrite FS2. lia.
  - rewrite FS. lia.
  - lia.
  - reflexivity.
  - lia.
  - exact HGPc.
  - exact HTPc.
  - exact R1c.
  - exact HRAW.
  - exact HRA4.
  - exact (achain_low _ _ _ _ HS0LOW).
  - intros HPRE1 HWIN1. eapply SRr_mono.
    + apply (STRDUP ly S Hp W regsc memc mdc [] sa cs Lam peak cnt fail ran most own).
      * split; [exact HPRE1|]. split; [exact HRODc|]. split; [rewrite HSPC; lia|]. split; [exact HRAZc | exact HFRM].
      * exact HROOM.
      * apply (prh_univ_closure_malloc B CTX0 HUNIV). vm_compute. discriminate.
      * exact HSEC.
      * exact HC24.
      * exact HHB.
      * exact R10c.
      * exact HCSTRc.
      * exact HKATc.
      * exact HMAX.
      * exact HLEDc.
      * intros Hcf. pose proof (HLIVE Hcf) as HLIVE1. unfold LIVE_pj_string in HLIVE1. lia.
    + cbv beta. intros W' c' _ H. apply fpostW_x_of_apost. exact H.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ2 & HJc2 & _ & HP3 & HK).
(* fuzz_strdup's post BY NAME (the batch kit adds its outcome conjunct HOUT): every conjunct is named, and each name is
   checked against its own text below, so a further conjunct cannot be swallowed by the last name *)
destruct HK as ((res & H10' & HROOM2 & HHUSE & HRP0 & HRP1 & HOUT & HPOST & HBY) & HMN).
lazymatch type of HHUSE with PresetHullBudget.hull_used S S2 [PresetReqAt.HMal _] => idtac end.
lazymatch type of HRP0 with res = 0 -> forall (_ : list Z -> Z * Z) _ _ _ _ _, _ -> PRH_Base.prh_run_at _ _ _ _ [] -> _ =>
  idtac end.
lazymatch type of HRP1 with res <> 0 -> forall (_ : list Z -> Z * Z) _ _ _ _ _, _ ->
  PRH_Base.prh_run_at _ _ _ _ [PresetReqAt.HMal _] -> _ => idtac end.
lazymatch type of HOUT with forall (_ : list Z -> Z * Z) _ _ _ _ _, _ -> PRH_Base.prh_run_at _ _ _ _ _ ->
  PRH_Base.prh_cons_from _ _ _ _ _ -> cnt <> fail -> res <> 0 /\ _ => idtac end.
lazymatch type of HPOST with prh_alloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ res _ _ _ _ _ => idtac end.
lazymatch type of HBY with res <> 0 -> bytes_at _ _ res _ => idtac end.
assert (HPM3 : Pm mem -> Pm mem3) by (intros h; exact (PCALL _ _ HMN (HPc h))). clear HMN.
pose proof (ajx_ar HJc2) as HAR2. pose proof (ajx_ly HJc2) as Hly2. pose proof (ajx_frs HJc2) as Hfrs2.
pose proof (ajx_hi HJc2) as F1. pose proof (ajx_blk HJc2) as F2. pose proof (ajx_img HJc2) as F3.
pose proof (ajx_frm HJc2) as F4.
destruct (pjs1_blocks (cp := CP) B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md3 HPOST HAR2) as (HBK & HNEW).
change (@cf_head CP) with 16 in *.
assert (Efa : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
(* what the callee keeps at and above pj_string's frame *)
assert (KST : forall a, spZ regs - 32 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply F1; [unfold YM05.alloc_ceiling in *; rewrite FS, FS2 in Hslo; lia|]. lia. }
(* v's shadow at the call state *)
assert (HVRAc : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 56).
{ eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)).
  apply KMc; [lia | unfold amem_range, shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia |
    unfold YM05.alloc_ceiling in *; rewrite FS, FS2 in Hslo; lia]. }
(* v's facts at the return state, by its place; the new block apart from v (its user bytes) and from the str word
   (its head word) *)
assert (HV2 : garr8 SEGS (mrestrict (w_H W2) mem3) v (pjs_bytes 0) /\
  (forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W2) mem3) a) /\
  range_addressable (aview SEGS (w_H W2) mem3) SHADOW_OFF v 56 /\
  (res <> 0 -> (forall x, res <= x < res + Z.of_nat (length cs) + 1 -> ~ (v <= x < v + 56)) /\
     (forall x, res - 16 <= x < res - 16 + 8 -> ~ (v + 16 <= x < v + 24)))).
{ destruct HSLOT as (_ & HAT' & _).
  destruct HAT' as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & Hnl & Hb & Hm) | [(cid & pos & Hin2 & Hf & Hfm) | (Hs & _)]]].
  - (* a harness block's user bytes *)
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own HLED Hin0) as (Hk0p & Hab & Hhp & H16 & _).
    change (@cf_head CP) with 16 in *.
    assert (Rq : 1 <= req_size (k0 + 16) /\ k0 + 16 <= req_size (k0 + 16)) by (apply req_size_pos; lia).
    destruct (pjs1_hblock_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a0 k0 HPOST Hin0) as (Hab2 & Hhp2).
    change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hab2) as (Ha16 & _ & _ & _ & Hown2 & _).
    destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hab2 Hhp2) as [Hbs _].
    change (@cf_head CP) with 16 in *.
    split.
    { apply (pjs1_garr8_keep W W2 memc mem3 v _ VBc). rewrite pjs_bytes_len. intros x Hx.
      replace x with (a0 - 16 + (x - (a0 - 16))) by lia.
      apply (F2 _ _ _ Hab Hab2); [lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hown2 a ltac:(lia)))|].
    split; [exact (block_shadow_range _ SHADOW_OFF (a0 - 16 + 16) (req_size (k0 + 16) - 16) v 56
                    Hbs ltac:(lia) ltac:(lia))|].
    intros Hr0. destruct (HNEW Hr0) as (Hnew & Hdj). pose proof (Hdj _ Hab) as Hd.
    change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hnew) as (Hn16 & _).
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + 16) /\
      Z.of_nat (length cs) + 1 + 16 <= req_size (Z.of_nat (length cs) + 1 + 16)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia.
  - (* another live allocator block *)
    assert (Rm : 1 <= req_size m /\ m <= req_size m) by (apply req_size_pos; lia).
    pose proof (HBK _ Hin1) as Hin1'.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hin1') as (Hb16 & _ & _ & _ & Hown2 & _).
    assert (NOH : forall h, In h Hp2 -> ~ (b <= h < b + req_size m)).
    { intros h Hh Hr. destruct (pjs1_heads B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST h Hh) as [Hh0' | (Hr0 & ->)];
        change (@cf_head CP) with 16 in *.
      - pose proof HLED as (_ & _ & _ & HPm).
        apply (Permutation_in _ HPm) in Hh0'. apply in_map_iff in Hh0' as ([a1 k1'] & Eh & Hin). cbn [fst] in Eh. subst h.
        destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a1 k1' most own HLED Hin) as (Hk1 & Hab1 & _).
        change (@cf_head CP) with 16 in *.
        assert (Rq1 : 1 <= req_size (k1' + 16) /\ k1' + 16 <= req_size (k1' + 16)) by (apply req_size_pos; lia).
        assert (Hne : (b, m) <> (a1 - 16, k1' + 16)).
        { intros E. injection E as E1 E2. apply Hnl. change (@cf_head CP) with 16. rewrite E1, E2.
          replace (a1 - 16 + 16) with a1 by lia. replace (k1' + 16 - 16) with k1' by lia. exact Hin. }
        pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin1 Hab1 Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      - destruct (HNEW Hr0) as (_ & Hdj). pose proof (Hdj _ Hin1) as Hd.
        assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + 16)) by (apply req_size_pos; lia).
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 b m HAR2 Hin1' NOH) as [Hbs _].
    split.
    { apply (pjs1_garr8_keep W W2 memc mem3 v _ VBc). rewrite pjs_bytes_len. intros x Hx.
      replace x with (b + (x - b)) by lia.
      apply (F2 _ _ _ Hin1 Hin1'); [lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hown2 a ltac:(lia)))|].
    split; [exact (block_shadow_range _ SHADOW_OFF b (req_size m) v 56 Hbs ltac:(lia) ltac:(lia))|].
    intros Hr0. destruct (HNEW Hr0) as (Hnew & Hdj). pose proof (Hdj _ Hin1) as Hd. change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hnew) as (Hn16 & _).
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + 16) /\
      Z.of_nat (length cs) + 1 + 16 <= req_size (Z.of_nat (length cs) + 1 + 16)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia.
  - (* a caller's fake frame *)
    assert (Hin2' : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hin2).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 cid pos HAR2 Hin2') as (_ & _ & Hfown & _).
    rewrite Efa in Hfown.
    destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin2) as (Hf0 & Hfc & _).
    destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin2) as (Hf32 & _).
    assert (Hfs8 : fs_frame_bytes cid mod 8 = 0) by (apply pjs1_fsb8; lia).
    split.
    { apply (pjs1_garr8_keep W W2 memc mem3 v _ VBc). rewrite pjs_bytes_len. intros x Hx.
      apply (F4 cid pos x Hin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros (r & [] & _)]. }
    split; [intros a Ha; apply (apresent_writable SEGS); exact (proj1 (Hfown a ltac:(lia)))|].
    split.
    { eapply range_addressable_agree; [|exact HVRAc]. intros x Hx.
      apply (F4 cid pos); [exact Hin2 | right | intros (r & [] & _)].
      unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
      set (f := frame_addr ly cid pos) in *. set (fb := fs_frame_bytes cid) in *. lia. }
    intros Hr0. destruct (HNEW Hr0) as (Hnew & _). change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hnew) as (Hn16 & _).
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ cid pos HAR2 Hnew Hin2') as Hd.
    rewrite Efa in Hd.
    assert (Rn : 1 <= req_size (Z.of_nat (length cs) + 1 + 16) /\
      Z.of_nat (length cs) + 1 + 16 <= req_size (Z.of_nat (length cs) + 1 + 16)) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    split; intros x Hx Hx'; lia.
  - lia. }
destruct HV2 as (HVB2 & HVW2 & HVRA2 & HAP2).
(* res: 0, or a new block's user address below alloc_ceiling *)
assert (HRB : res = 0 \/ 4096 <= res - 16 /\ res + Z.of_nat (length cs) + 1 <= YM05.alloc_ceiling).
{ destruct HPOST as [(_ & -> & _) | [(_ & -> & _) | (_ & H4 & _ & _ & _ & Eab & _)]]; [left; reflexivity | left; reflexivity|].
  right. assert (Hin : In (res - 16, Z.of_nat (length cs) + 1 + 16) (ablocks B ly2 S2)).
  { change (@cf_head CP) with 16 in Eab. rewrite Eab. apply in_or_app. right. left. reflexivity. }
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 _ _ HAR2 Hin) as (_ & Hb4 & Hc & _).
  assert (Rq : 1 <= req_size (Z.of_nat (length cs) + 1 + 16) /\
    Z.of_nat (length cs) + 1 + 16 <= req_size (Z.of_nat (length cs) + 1 + 16)) by (apply req_size_pos; lia).
  lia. }
assert (Hres64 : 0 <= res < 2 ^ 64) by (destruct HRB as [-> | (Hr1 & Hr2)]; unfold YM05.alloc_ceiling in *; lia).
(* ---- the registers fuzz_strdup keeps, and the frame's words at the return state ---- *)
assert (P3 : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs3 r = getr regs2 r).
{ intros r Hr. rewrite <- (KKc r Hr). repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ =>
       let z := eval vm_compute in (bv_unsigned rr) in
       pose proof (HP3 z ltac:(unfold acallee_saved; lia)) as H;
       replace (Z_to_bv 5 z) with rr in H by (apply bv_eq; reflexivity); exact H end |]). destruct Hr. }
assert (Sp3 : spZ regs3 = spZ regs - 32) by (unfold spZ at 1; rewrite (P3 2%bv) by (cbn; tauto); exact Sp2).
assert (G83 : getr regs3 8%bv = w64 v) by (rewrite (P3 8%bv) by (cbn; tauto); exact G8).
assert (G183 : getr regs3 18%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite (P3 18%bv) by (cbn; tauto); exact G18).
assert (KF3 : forall x, spZ regs - 32 <= x < spZ regs -> aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W) mem2 x).
{ intros x Hx. rewrite KST by lia. apply KC; lia. }
set (rae := bv_unsigned (getr regs 1%bv)). set (s0e := bv_unsigned (getr regs 8%bv)).
set (s1e := bv_unsigned (getr regs 9%bv)). set (s2e := bv_unsigned (getr regs 18%bv)).
assert (VRA3 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs + -8) 8 rae)
  by (apply (val_mem_kept SEGS (w_H W) (w_H W2) mem2 mem3 _ 8 _); [intros kk Hkk; apply KF3; cbn in Hkk; lia | exact VRA]).
assert (VS03 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs + -16) 8 s0e)
  by (apply (val_mem_kept SEGS (w_H W) (w_H W2) mem2 mem3 _ 8 _); [intros kk Hkk; apply KF3; cbn in Hkk; lia | exact VS0]).
assert (VS13 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs + -24) 8 s1e)
  by (apply (val_mem_kept SEGS (w_H W) (w_H W2) mem2 mem3 _ 8 _); [intros kk Hkk; apply KF3; cbn in Hkk; lia | exact VS1]).
assert (VS23 : val_mem SEGS (mrestrict (w_H W2) mem3) (spZ regs + -32) 8 s2e)
  by (apply (val_mem_kept SEGS (w_H W) (w_H W2) mem2 mem3 _ 8 _); [intros kk Hkk; apply KF3; cbn in Hkk; lia | exact VS2]).
(* ---- the seat at fuzz_strdup's return slot (AF_ps + 96) ---- *)
set (EN := ps_E2 regs3 rae s0e s1e s2e).
assert (EL3 : forall n, (n < A_TEXT)%nat -> ew EN n = ew (Ereg regs3 (map (Z_to_bv 64) [rae; s0e; s1e; s2e])) n)
  by (intros n Hn; subst EN; unfold ps_E2; apply Eimg_low; exact Hn).
assert (QF2 : ew EN 2 = getr regs3 2%bv) by (rewrite EL3 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 2 2%bv eq_refl)).
assert (QF8 : ew EN 8 = getr regs3 8%bv) by (rewrite EL3 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 8 8%bv eq_refl)).
assert (QF10 : ew EN 10 = getr regs3 10%bv) by (rewrite EL3 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 10 10%bv eq_refl)).
assert (QF18 : ew EN 18 = getr regs3 18%bv) by (rewrite EL3 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs3 _ 18 18%bv eq_refl)).
assert (QFX : forall j0, (j0 < 4)%nat -> ew EN (32 + j0) = Z_to_bv 64 (nth j0 [rae; s0e; s1e; s2e] 0)).
{ intros j0 Hj0. rewrite EL3 by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  do 4 (destruct j0 as [|j0]; [reflexivity|]). lia. }
assert (Usp3 : bv_unsigned (ew EN 2) = spZ regs - 32) by (rewrite QF2; exact Sp3).
assert (Uv3 : bv_unsigned (ew EN 8) = v) by (rewrite QF8, G83; unfold w64; apply unsigned_lit_small; lia).
assert (E10' : ew EN 10 = Z_to_bv 64 res) by (rewrite QF10, H10'; reflexivity).
assert (HEI3 : img_env VAL A_LIM EN) by (subst EN; unfold ps_E2; apply Eimg_env).
assert (HS3 : st_ok_pi SEGS VAL EN ss_ps3
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + (AF_ps + 96))) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ps3. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ps_frame2, ps_vreg3. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp3. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 0 8 (SOff 35 0) s2e);
          [cbn [sv_denot]; change (ew EN 35) with (ew EN (32 + 3)); rewrite (QFX 3%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 0) with (spZ regs + -32) by lia. exact VS23.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 8 8 (SOff 34 0) s1e);
          [cbn [sv_denot]; change (ew EN 34) with (ew EN (32 + 2)); rewrite (QFX 2%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia. exact VS13.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 16 8 (SOff 33 0) s0e);
          [cbn [sv_denot]; change (ew EN 33) with (ew EN (32 + 1)); rewrite (QFX 1%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia. exact VS03.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 24 8 (SOff 32 0) rae);
          [cbn [sv_denot]; change (ew EN 32) with (ew EN (32 + 0)); rewrite (QFX 0%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia. exact VRA3.
    + rewrite Uv3. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply HVW2. lia.
  - apply pairwise_disjoint_of_extents. unfold ps_frame2, ps_vreg3, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp3, Uv3.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold YM05.alloc_ceiling in *; rewrite ?FS, ?FS2 in Hslo; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ps_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp3, Uv3, QF18, G183, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold YM05.alloc_ceiling in *; rewrite ?FS, ?FS2 in Hslo; lia. }
assert (SHOK3 : sh_ok SEGS PS_Bx2 PS_SH2 EN (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, PS_SH2. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U EN PS_Bx2 = SHADOW_OFF).
  { unfold PS_Bx2. apply (U_atom EN 18 SHADOW_OFF); [rewrite QF18, G183; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (UV : U EN (SOff 8 0) = v) by (apply (U_atom EN 8 v); [rewrite QF8, G83; reflexivity | lia]).
  rewrite UB, UV. split.
  - replace (v + 0) with v by lia. replace (56 - 0) with 56 by lia. exact HVRA2.
  - intros a Ha. unfold amem_range in HAMR. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
assert (HAE3 : env_agree 32 (Ereg regs3 (map (Z_to_bv 64) [rae; s0e; s1e; s2e])) EN)
  by (split; [intros n Hn; subst EN; unfold ps_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clearbody EN.
pose (RUNF := @paj_run_xf_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
(* ---- slots 24-38: s0 += 16, the shadow check of the str word, a1 = (a0 != 0) - 1, v->str = a0, the frame back,
   sp += 32; the run stops at the ret ---- *)
paj_run_tok_x_inv RUNF HS3 HJ2 SHOK3 HPM3 PS_Bspan.
{ intros a (r & Hin & Hr). cbn [ss_ps3 ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [ps_frame2 ps_vreg3 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp3 in Hr; lia | rewrite Uv3 in Hr].
  assert (HFP : inFP [(v, v + 56)] a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct HSLOT as (_ & HAT' & _).
  destruct HAT' as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & _ & Hb & Hm) | [(cid & pos & Hin2 & Hf & Hfm) | (Hs & _)]]].
  - destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own HLED Hin0) as (Hk0' & Hab & _).
    change (@cf_head CP) with 16 in *.
    assert (Rq : 1 <= req_size (k0 + 16) /\ k0 + 16 <= req_size (k0 + 16)) by (apply req_size_pos; lia).
    left. right; left. split; [exact HFP|]. exists (a0 - 16), (k0 + 16).
    split; [exact (HBK _ Hab)|]. lia.
  - pose proof (req_size_pos m ltac:(lia)) as [_ Rm].
    left. right; left. split; [exact HFP|]. exists b, m.
    split; [exact (HBK _ Hin1)|]. lia.
  - right. split; [exact HFP|]. exists cid, pos. split; [exact Hin2|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. lia.
  - lia. }
(* ---- after the run: only the str word v + 16 .. v + 24 written ---- *)
clear HF.
assert (KW : forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) ->
  mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem3 x).
{ intros x Hx. apply HFr. intros (r & Hin & Hr). cbn [ss_ps3 ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [ps_frame2 ps_vreg3 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp3 in Hr; lia | rewrite Uv3 in Hr; lia]. }
clear HFr.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (KW (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn. }
prreg HS3 (1%bv : bv 5) R1. prreg HS3 (2%bv : bv 5) R2. prreg HS3 (8%bv : bv 5) R8. prreg HS3 (9%bv : bv 5) R9.
prreg HS3 (18%bv : bv 5) R18.
assert (R10 : getr (ms_regs ms) 10 = sv_denot EN PJS2_A0)
  by (rewrite (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS3); reflexivity).
rewrite (pjs2_a0 EN res E10' Hres64) in R10.
assert (KR : forall r, In r [3%bv; 4%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) EN _ _ regs3 _
    [3%bv; 4%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS3 HAE3
    ltac:(vm_compute; reflexivity) r Hr) as K3.
  cbn [ms_regs restrict] in K3. rewrite K3.
  rewrite (P3 r) by (cbn in Hr |- *; tauto).
  destruct Hr as [<- | [<- | Hr]]; [rewrite G3; exact (eq_sym Hgp) | rewrite G4; exact (eq_sym Htp) | exact (G19 r Hr)]. }
(* the str word res at v + 16 *)
assert (VSTR : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms)) (v + 16) 8 res).
{ lazymatch type of HS3 with st_ok_pi _ _ _ ?ssq _ =>
    pose proof (st_ok_region_nth SEGS EN (abs_ss VAL ssq) _ 1%nat
      (YP09.mkRegion (Some 8%nat) 0 56 16 24 [YP09.mkChunk 16 (CVal 8 (SOff 10 0))]) HS3 eq_refl) as RGV end.
  pose proof (field_of_region SEGS EN _ 8%nat v _ 0 56 16 24 16 8%N (SOff 10 0) res RGV Uv3 (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite E10', Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hres64) ltac:(cbn; lia)) as VT3.
  cbn [ms_mem restrict N.to_nat Pos.to_nat] in VT3. exact VT3. }
pose proof (pjs2_bytes_final W2 mem3 (ms_mem ms) v res HVB2 KV VSTR ltac:(lia) ltac:(lia)) as VB3.
assert (HVW3 : forall a, v <= a < v + 56 -> writable_at SEGS (mrestrict (w_H W2) (ms_mem ms)) a)
  by (intros a Ha; exact (writable_at_grows SEGS _ _ a HG (HVW2 a Ha))).
(* ---- the ret, to the entry's ra ---- *)
eapply (RET W2 _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fpostW.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?rr _ ?mm _) ?dd = _ /\ _ =>
  exists ly2, S2, Hp2, rr, mm, dd, (k + k1) end.
split.
{ rewrite R1. change (ew EN 32) with (ew EN (32 + 0)). rewrite (QFX 0%nat) by lia. cbn [nth].
  unfold rae. rewrite Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS Hsegs); exact HJ2|].
split.
{ intros a Ha _. rewrite KV by (unfold YM05.alloc_ceiling in *; rewrite ?FS, ?FS2 in Hslo; lia).
  rewrite KST by lia. apply KMc; [lia | unfold YM05.alloc_ceiling in *; rewrite ?FS, ?FS2 in Hslo; lia | lia]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, Usp3. replace (spZ regs - 32 + 32) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). apply KR. cbn. tauto.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R8. change (ew EN 33) with (ew EN (32 + 1)). rewrite (QFX 1%nat) by lia. cbn [nth].
    unfold s0e. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R9. change (ew EN 34) with (ew EN (32 + 2)). rewrite (QFX 2%nat) by lia. cbn [nth].
    unfold s1e. apply Z_to_bv_bv_unsigned.
  - assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Hr' as [-> | Hr'].
    + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R18. change (ew EN 35) with (ew EN (32 + 3)). rewrite (QFX 3%nat) by lia. cbn [nth].
      unfold s2e. apply Z_to_bv_bv_unsigned.
    + apply KR. cbn [In].
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
        repeat (first [left; apply bv_eq; reflexivity | right]). }
(* ---- the post, and the keep of Pm ---- *)
split; [|exact HPM3].
split; [exact HROOM2|].
exists res.
assert (HSLOT8 : v mod 8 = 0) by exact HRW8.
(* THE EXACT ADVANCE: the strdup's event when it took one; none when the harness chose this allocation to fail.
   fuzz_strdup's text is post-implication: its arms are applied at pj_string's own run (the rp_ binders),
   the entry position HRP (the call state keeps S) and the entry run premise HEV *)
assert (HADV : res <> 0 \/ cnt = fail ->
  exists hist', PresetRoomPos.iface_room_pos rp_sm rp_x rp_os
    (rp_i + length (prhPj_string_evs (Z.of_nat (length cs)) cnt fail))%nat rp_H0 hist' S2).
{ intros Hcase. unfold prhPj_string_evs in HEV |- *.
  destruct (Z.eqb_spec cnt fail) as [Ecf | Ncf].
  - assert (Hr : res = 0)
      by (destruct HPOST as [(_ & Hr & _) | [(Hn & _) | (Hn & _)]]; [exact Hr | contradiction | contradiction]).
    exact (HRP0 Hr rp_sm rp_x rp_os rp_i rp_H0 rp_hist HRP HEV).
  - destruct Hcase as [Hr | E]; [|contradiction].
    exact (HRP1 Hr rp_sm rp_x rp_os rp_i rp_H0 rp_hist HRP HEV). }
(* DEAD-PJSTRING: with no chosen failure (cnt <> fail) the run's event at rp_i is the strdup's HMal and its window
   is a consumer allocation (HCONS), so fuzz_strdup's outcome conjunct HOUT gives the grant *)
assert (HDEAD : cnt <> fail -> res <> 0).
{ intros Ncf. unfold prhPj_string_evs in HEV, HCONS.
  destruct (Z.eqb_spec cnt fail) as [Ecf | _]; [contradiction|].
  exact (proj1 (HOUT rp_sm rp_x rp_os rp_i rp_H0 rp_hist HRP HEV HCONS Ncf)). }
split.
{ apply (pjs2_post_keep (cp := CP) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem3 _ HPOST).
  - intros Hr0 a. subst res. apply (pjs2_full W2 mem3 _ v KW HVB2 VB3).
  - intros Hr0. destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|].
    unfold YM05.alloc_ceiling in *. lia.
  - intros Hr0 a Ha. change (@cf_head CP) with 16 in *. apply KV.
    + destruct Ha as [Ha | [(x & k2 & i & Hin & Hi & ->) | [Ha | Ha]]].
      * pose proof (Hsegs a (pal_pst_img a Ha)). unfold kLowMemEnd in *. lia.
      * destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|].
        destruct Hin as [E1 | Hin]; [injection E1 as <- <-; unfold YM05.alloc_ceiling in *; lia|].
        destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran x k2 most own HLED Hin) as (Hk1 & Hab & _).
        change (@cf_head CP) with 16 in *.
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
        assert (Rq1 : 1 <= req_size (k2 + 16) /\ k2 + 16 <= req_size (k2 + 16)) by (apply req_size_pos; lia).
        unfold YM05.alloc_ceiling in *. lia.
      * destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction|]. unfold YM05.alloc_ceiling in *. lia.
      * unfold kLowMemEnd, kHighShadowEnd in *. lia.
    + destruct (HAP2 Hr0) as (HAPU & HAPH).
      destruct Ha as [Ha | [(x & k2 & i & Hin & Hi & ->) | [Ha | Ha]]].
      * intros Hx. exact (proj2 (VPL a ltac:(lia)) (pal_pst_img a Ha)).
      * destruct Hin as [E1 | Hin]; [injection E1 as <- <-; apply HAPH; lia|].
        intros Hx. pose proof (VHD x k2 i Hin Hi) as Hn. change (@cf_head CP) with 16 in Hn. lia.
      * intros Hx. exact (HAPU a ltac:(lia) ltac:(lia)).
      * unfold amem_range in HAMR. unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. lia. }
split; [exact HDEAD|].
split; [exact HADV|].
split.
- intros Hr0. split.
  + rewrite R10. replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr0). reflexivity.
  + destruct (HAP2 Hr0) as (HAPU & _).
    pose proof (HBY Hr0) as HBY0.
    destruct HCSTRc as ((Hg & Hnz) & _ & _ & H32 & _).
    apply pjs_node_str.
    * apply pjs_hdr; [exact Hres64 | exact VB3 | split; [exact HSLOT8 | exact HVW3]].
    * split; [left; reflexivity|]. split; [lia|]. split; [exact H32|]. split.
      -- apply Forall_forall. intros c Hc.
         destruct (In_nth _ _ 0 Hc) as (jj & Hjj & <-).
         destruct (Hg jj ltac:(rewrite length_app; cbn [length]; lia)) as [_ Hr].
         rewrite app_nth1 in Hr by exact Hjj.
         pose proof (proj1 (Forall_forall _ _) Hnz (nth jj cs 0) (nth_In _ _ Hjj)) as Hnz0. cbn beta in Hnz0. lia.
      -- unfold bytes_at in HBY0. apply (garr8R_frame SEGS (mrestrict (w_H W2) mem3) (mrestrict (w_H W2) (ms_mem ms)) res _ HBY0).
         intros x Hx. apply (mbyte_of_aview SEGS). rewrite length_app in Hx. cbn [length] in Hx.
         apply KV; [destruct HRB as [Hr | (Hr1 & Hr2)]; [contradiction | unfold YM05.alloc_ceiling in *; lia]|].
         intros Hx'. exact (HAPU x ltac:(lia) ltac:(lia)).
    * intros x Hx. exact (HAPU x ltac:(lia)).
- intros Hr0. subst res. split.
  + rewrite R10. reflexivity.
  + rewrite pjs_bytes_0 in VB3. split; [split; [exact HSLOT8 | exact HVW3]|].
    split; [exact VB3|].
    apply pjs_fd0. apply pjs_hdr; [lia | rewrite pjs_bytes_0; exact VB3 | split; [exact HSLOT8 | exact HVW3]].
Qed.

(* the write permission of a stretch from the seat ss_ps2: the one window is v's [0, 4) *)
Ltac ps_awr2 v Usp2 Uv2 VPL :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia;
     first [rewrite Usp2 in Hr; lia | rewrite Uv2 in Hr;
       let b := fresh "b" in let n := fresh "n" in let cid := fresh "cid" in let pos := fresh "pos" in
       let Hin' := fresh "Hin" in let Hb := fresh "Hb" in
       destruct (VPL a ltac:(lia)) as [[(b & n & Hin' & Hb) | (cid & pos & Hin' & Hb)] _];
       [ left; right; left; split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|];
         exists b, n; split; [exact Hin' | lia]
       | right; split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|];
         exists cid, pos; split; [exact Hin' | exact Hb] ] ] |]);
  try destruct Hin.

Theorem pj_string_holds_P : tpj_string_specXP (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK Pm CTX0.
Proof.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own
  [HPRE [HROD [HTOP [HRAZ HFRM]]]] HUNIV HROOM HRP HLEN HCONS H10 H11 HFWIN HSLOT HCEIL HHW HSTR HMAX HLED HLIVE HEV.
pose proof (@pa_wx _ _ PA) as Hwx. pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct ps_frames as [FS FS2]. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
destruct (ps_entry ly S Hp W regs mem md ch HPRE) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx (STK_pj_string (PI := prh_img_A)) d [(v, v + 56)]
  ly S Hp W regs mem md ch HPRE HFWIN) as HJ.
assert (HPM : Pm mem -> Pm mem) by (intros h; exact h).
remember (ps_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ps_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; unfold ps_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose (RUN := @paj_run_x_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (RUNF := @paj_run_xf_inv fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm mem -> Pm m)
  (srr_inv_laws_imp SEGS Pm mem PLAW)).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := PL_prog_A) (PI := PA)).
unfold cfg_at. rewrite Hent. change (w64 (BASE + AF_ps)) with (Z_to_bv 64 (BASE + AF_ps)).
(* ---- slots 0-12: the frame, s1 = s, s2 = the shadow base, s0 = v, a2 = 56, a1 = 0, jal __asan_memset ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PS_Bspan; [gs_awr regs Usp|].
(* ---- the memset call state: the frame's four words written, every other byte as at entry ---- *)
gs_keep HFr Usp (spZ regs - 32) (spZ regs) KO1. clear HF HG.
pose proof HFr as HFr1. clear HFr.
pose proof (ps_vplace ly S Hp W regs mem md d Lam peak cnt fail ran most own v HAR HLED HSLOT HCEIL ltac:(lia)) as VPL.
pose proof HSLOT as (H4096 & _ & HRW & HAMR & HWIN & HRA & HHU).
assert (Hv47 : 4096 <= v /\ v + 56 <= YM05.alloc_ceiling).
{ split; [exact H4096|]. destruct (VPL (v + 55) ltac:(lia)) as [[(b & n & Hin & Hr) | (cid & pos & Hin & Hr)] _].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b n HAR Hin) as (_ & _ & Hc & _). lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (AG : forall m, (m < 33)%nat -> ew E m = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) m)
  by (intros m Hm; apply EL; unfold A_TEXT; lia).
assert (Hd16' : (-32 - d) mod 16 = 0) by lia.
pmkst HS.
(* ---- __asan_memset (v, 0, 56) at A 0x86b88 ---- *)
eapply SRr_bind.
{ eapply (aj_intrin_at_xm_fr (SK := SK) SEGS B PST ARx LAWS Hsegs OSet (SIGMA AS___asan_memset) AIM W _ _ (STK_pj_string (PI := prh_img_A) + d) (spZ regs + d) [(v, v + 56)] ly S Hp W mem md [] ly S Hp _ _
    v 0 56 (-32 - d) _ HJ).
  - rewrite Ra0, (AG 10%nat) by lia. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - unfold YM05.alloc_ceiling in *. lia.
  - unfold spZ at 1. rewrite Rsp, Usp. rewrite unsigned_lit_small by lia. lia.
  - exact Hd16'.
  - lia.
  - rewrite FS, FS2. unfold ESTACK. lia.
  - rewrite Rgp, (AG 3%nat) by lia. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact Hgp.
  - rewrite Rtp, (AG 4%nat) by lia. rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact Htp.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | vm_compute; reflexivity].
  - intros a Ha. split.
    + destruct (VPL a Ha) as [[(b & n & Hin & Hr) | (cid & pos & Hin & Hr)] _].
      * left. right. left. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists b, n. split; [exact Hin | lia].
      * right. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists cid, pos. split; [exact Hin | exact Hr].
    + rewrite FS, FS2 in Hslo. unfold ESTACK. lia.
  - exact HAMR.
  - eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)). apply KO1; lia.
  - intros _ s0 Hs. pose proof (gs_hull_low v 56 s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs). rewrite KO1 by lia. apply HHU. exact Hs.
  - exact I. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Hset & Hfr & Hpres2 & HK2).
assert (HPM2 : Pm mem -> Pm mem2) by (intros h; exact (PCALL _ _ HK2 (HPM h))). clear HPM HK2.
(* ---- the seat at the memset's return slot (AF_ps + 52) ---- *)
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (spZ regs - 32 - ESTACK <= a < spZ regs) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hv Hw. rewrite Hfr by (try exact Ha; try exact Hv; lia). apply KO1; lia. }
set (rae := bv_unsigned (getr regs 1%bv)). set (s0e := bv_unsigned (getr regs 8%bv)).
set (s1e := bv_unsigned (getr regs 9%bv)). set (s2e := bv_unsigned (getr regs 18%bv)).
assert (VSL : forall od e val, In (YP09.mkChunk od (CVal 8 e))
    [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  -32 <= od <= -8 -> sv_denot E e = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + od) 8 val).
{ intros od e val Hin Hod He Hv.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (st_ok_region_nth SEGS E ss _ 0 (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0
      [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
       YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS eq_refl) as RG0 end.
  pose proof (slot_of_region SEGS E _ (spZ regs) _ _ _ _ _ od e val RG0 Usp Hin He Hv) as V0.
  cbn [ms_mem restrict] in V0.
  apply (val_mem_kept SEGS (w_H W) (w_H W) (ms_mem ms) mem2 (spZ regs + od) 8 val); [|exact V0].
  intros kk Hkk. apply Hfr; [lia | lia | lia]. }
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r).
{ intros n r Hn Hr. cbn [sv_denot]. rewrite (AG n) by lia. rewrite (ew_Ereg_nat regs _ n r) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VS2 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -32) 8 s2e).
{ apply (VSL (-32) (SOff 18 0) s2e); [cbn; tauto | lia | rewrite (EV 18%nat 18%bv) by (lia || reflexivity); symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range]. }
assert (VS1 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -24) 8 s1e).
{ apply (VSL (-24) (SOff 9 0) s1e); [cbn; tauto | lia | rewrite (EV 9%nat 9%bv) by (lia || reflexivity); symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range]. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -16) 8 s0e).
{ apply (VSL (-16) (SOff 8 0) s0e); [cbn; tauto | lia | rewrite (EV 8%nat 8%bv) by (lia || reflexivity); symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range]. }
assert (VRA : val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs + -8) 8 rae).
{ apply (VSL (-8) (SOff 1 0) rae); [cbn; tauto | lia | rewrite (EV 1%nat 1%bv) by (lia || reflexivity); symmetry; apply Z_to_bv_bv_unsigned | apply bv_unsigned_in_range]. }
clear VSL.
(* the registers __asan_memset keeps *)
assert (P2 : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. repeat (destruct Hr as [<- | Hr];
    [lazymatch goal with |- getr _ ?rr = _ =>
       let z := eval vm_compute in (bv_unsigned rr) in
       pose proof (HP2 z ltac:(unfold acallee_saved; lia)) as H;
       replace (Z_to_bv 5 z) with rr in H by (apply bv_eq; reflexivity); exact H end |]). destruct Hr. }
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2.
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
  by (rewrite HE; split; [intros n Hn; unfold ps_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF]
  [19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAE0 ltac:(vm_compute; reflexivity)) as K19.
cbn [ms_regs restrict] in K19.
assert (G19 : forall r : bv 5, In r [19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
  getr regs2 r = getr regs r) by (intros r Hr; rewrite P2 by (cbn in Hr |- *; tauto); exact (K19 r Hr)).
assert (G3 : getr regs2 3%bv = w64 (as_gp B)).
{ rewrite P2 by (cbn; tauto). rewrite Rgp, (AG 3%nat) by lia. rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl). exact Hgp. }
assert (G4 : getr regs2 4%bv = w64 (as_tp B)).
{ rewrite P2 by (cbn; tauto). rewrite Rtp, (AG 4%nat) by lia. rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl). exact Htp. }
assert (Sp2 : spZ regs2 = spZ regs - 32).
{ unfold spZ at 1. rewrite P2 by (cbn; tauto). rewrite Rsp, Usp. rewrite unsigned_lit_small by lia. lia. }
assert (G8 : getr regs2 8%bv = w64 v).
{ rewrite P2 by (cbn; tauto). rewrite Rs0, (AG 10%nat) by lia. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10. }
assert (G9 : getr regs2 9%bv = w64 s).
{ rewrite P2 by (cbn; tauto). rewrite Rs1, (AG 11%nat) by lia. rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl). exact H11. }
assert (G18 : getr regs2 18%bv = Z_to_bv 64 SHADOW_OFF).
{ rewrite P2 by (cbn; tauto). rewrite Rs2, (AG 32%nat) by lia. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
lazymatch eval vm_compute in (AF_ps + 52) with ?n => assert (EAF : AF_ps + 52 = n) by (vm_compute; reflexivity) end.
rewrite <- EAF.
set (EN := ps_E2 regs2 rae s0e s1e s2e).
assert (EL2 : forall n, (n < A_TEXT)%nat -> ew EN n = ew (Ereg regs2 (map (Z_to_bv 64) [rae; s0e; s1e; s2e])) n)
  by (intros n Hn; subst EN; unfold ps_E2; apply Eimg_low; exact Hn).
assert (F2 : ew EN 2 = getr regs2 2%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 2 2%bv eq_refl)).
assert (F8 : ew EN 8 = getr regs2 8%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 8 8%bv eq_refl)).
assert (F18 : ew EN 18 = getr regs2 18%bv) by (rewrite EL2 by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 18 18%bv eq_refl)).
assert (FX : forall j0, (j0 < 4)%nat -> ew EN (32 + j0) = Z_to_bv 64 (nth j0 [rae; s0e; s1e; s2e] 0)).
{ intros j0 Hj0. rewrite EL2 by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  do 4 (destruct j0 as [|j0]; [reflexivity|]). lia. }
assert (Usp2 : bv_unsigned (ew EN 2) = spZ regs - 32) by (rewrite F2; exact Sp2).
assert (Uv2 : bv_unsigned (ew EN 8) = v) by (rewrite F8, G8; unfold w64; apply unsigned_lit_small; lia).
assert (HEI2 : img_env VAL A_LIM EN) by (subst EN; unfold ps_E2; apply Eimg_env).
assert (HRW8 : v mod 8 = 0) by (destruct HRW as [H8 _]; exact H8).
assert (HS2 : st_ok_pi SEGS VAL EN ss_ps2
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (AF_ps + 52))) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ps2. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold ps_frame2, ps_vreg2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp2. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 0 8 (SOff 35 0) s2e);
          [cbn [sv_denot]; change (ew EN 35) with (ew EN (32 + 3)); rewrite (FX 3%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 0) with (spZ regs + -32) by lia. exact VS2.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 8 8 (SOff 34 0) s1e);
          [cbn [sv_denot]; change (ew EN 34) with (ew EN (32 + 2)); rewrite (FX 2%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 8) with (spZ regs + -24) by lia. exact VS1.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 16 8 (SOff 33 0) s0e);
          [cbn [sv_denot]; change (ew EN 33) with (ew EN (32 + 1)); rewrite (FX 1%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 16) with (spZ regs + -16) by lia. exact VS0.
      * apply (chunk_ok_val SEGS EN _ (spZ regs - 32) 24 8 (SOff 32 0) rae);
          [cbn [sv_denot]; change (ew EN 32) with (ew EN (32 + 0)); rewrite (FX 0%nat) by lia; cbn [nth]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | apply bv_unsigned_in_range | lia |].
        replace (spZ regs - 32 + 24) with (spZ regs + -8) by lia. exact VRA.
    + rewrite Uv2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply ps_wr_of_view; [unfold YM05.alloc_ceiling in *; lia | exact (proj2 (VPL (v + a) ltac:(lia))) |].
      rewrite Hset by lia. discriminate.
  - apply pairwise_disjoint_of_extents. unfold ps_frame2, ps_vreg2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp2, Uv2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [ps_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp2, Uv2, F18, G18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK2 : sh_ok SEGS PS_Bx2 PS_SH2 EN (mrestrict (w_H W) mem2)).
{ unfold sh_ok, PS_SH2. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U EN PS_Bx2 = SHADOW_OFF).
  { unfold PS_Bx2. apply (U_atom EN 18 SHADOW_OFF); [rewrite F18, G18; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (UV : U EN (SOff 8 0) = v) by (apply (U_atom EN 8 v); [rewrite F8, G8; reflexivity | lia]).
  rewrite UB, UV. split.
  - replace (v + 0) with v by lia. replace (56 - 0) with 56 by lia.
    eapply range_addressable_agree; [|exact HRA]. intros x Hx. pose proof (gs_shadow_low x ltac:(lia)).
    pose proof asan_consts as (CC1 & _). unfold YM05.alloc_ceiling in *.
    apply KM2; [lia | unfold amem_range, shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia | lia].
  - intros a Ha. unfold amem_range in HAMR. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
clear HS SHOK HEI.
(* ---- slots 13-19: the shadow byte of v, the type word 4, bnez s1 ---- *)
paj_run_tok_x_inv RUNF HS2 HJ2 SHOK2 HPM2 PS_Bspan.
{ intros a (r & Hin & Hr). cbn [ss_ps2 ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [ps_frame2 ps_vreg2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp2 in Hr; lia | rewrite Uv2 in Hr].
  destruct (VPL a ltac:(lia)) as [[(b & n & Hin & Hb) | (cid & pos & Hin & Hf)] _].
  - left. right. left. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
    exists b, n. split; [exact Hin | lia].
  - right. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
    exists cid, pos. split; [exact Hin | exact Hf]. }
(* ---- the branch state (AF_ps + 76, `bnez s1`): the type word stored, nothing else written ---- *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
{ apply (gs_keep_out _ _ W mem2 (ms_mem ms0) v (v + 4) HFr).
  intros a (r & Hin & Hr). cbn [ss_ps2 ss_mem In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [ps_frame2 ps_vreg2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Usp2 in Hr; lia | rewrite Uv2 in Hr; lia]. }
clear HF HFr HG.
assert (HAEN : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [rae; s0e; s1e; s2e])) EN)
  by (split; [intros n Hn; subst EN; unfold ps_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
lazymatch eval vm_compute in (AF_ps + 96) with ?n => assert (EAF2 : AF_ps + 96 = n) by (vm_compute; reflexivity) end.
(* ---- the call of fuzz_strdup, from the state at its entry (both arms of the branch come here) ---- *)
match goal with |- SRr _ _ _ ?Q => assert (CUT : forall sa regsc memc mdc k,
  AJ (STK_pj_string (PI := prh_img_A) + d) (spZ regs + d) [(v, v + 56)] ly S Hp W mem md [] ly S Hp W memc mdc k ->
  (Pm mem -> Pm memc) ->
  getr regsc 1 = Z_to_bv 64 (BASE + (AF_ps + 96)) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr regsc r = getr regs2 r) ->
  getr regsc 9 = w64 sa -> getr regsc 10 = w64 sa ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem2 a) ->
  val_mem SEGS (mrestrict (w_H W) memc) v 4 4 ->
  (s = 0 /\ sa = PS_LIT \/ s <> 0 /\ sa = s) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA AS_fuzz_strdup)) memc (seg_rom SEGS)) mdc) Q) end.
{ intros sa regsc memc mdc k HJc HPc R1c KKc _ R10c KC VT HSA.
  exact (ps_tail ReaderRes.jr_strtod rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch d v s cs Lam peak cnt fail
    ran most own regs2 mem2 sa regsc memc mdc k (conj HPRE (conj HROD (conj HTOP (conj HRAZ HFRM)))) HUNIV HROOM HRP
    HLEN HCONS HFWIN HSLOT HCEIL HSTR HMAX HLED HLIVE HEV (fun i Hi => Hset i Hi) KM2 VRA VS0 VS1 VS2 Sp2 G8 G18 G3 G4 G19
    HJc HPc R1c KKc R10c KC VT HSA). }
assert (Hsr : 0 <= s < 2 ^ 64).
{ destruct HSTR as [(-> & _) | (_ & (_ & Hs4 & Hsc & _) & _)]; [lia | unfold YM05.alloc_ceiling in *; lia]. }
assert (U9 : U EN (SOff 9 0) = s) by (apply (U_atom EN 9 s); [rewrite (EL2 9%nat) by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact G9 | exact Hsr]).
(* the call state's facts, from the stretch that reaches the call: the memory off v's type word as after the memset,
   the type word itself, the registers the stretch keeps *)
(* ---- slot 19: bnez s1 ---- *)
psrr_branch_tok RUNF BR HS2 SHOK2 PS_Bspan.
- (* taken: s <> 0; a0 = s1 = s, jal fuzz_strdup (slots 22-23) *)
  rewrite branch_ne_U, U_SLit, U9 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok_x_inv RUNF HS2 HJ2 SHOK2 HPM2 PS_Bspan; [ps_awr2 v Usp2 Uv2 VPL|].
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hn. rewrite <- (KB a Ha Hn). apply (gs_keep_out _ _ W (ms_mem ms0) (ms_mem ms1) v (v + 4) HFr); [|exact Ha | exact Hn].
    intros b (r & Hin & Hr). vm_compute in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      first [rewrite Usp2 in Hr; lia | rewrite Uv2 in Hr; lia] |]). destruct Hin. }
  lazymatch type of HS2 with st_ok _ _ ?ssc _ =>
    pose proof (st_ok_region_nth SEGS EN ssc _ 1%nat
      (YP09.mkRegion (Some 8%nat) 0 56 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 4))]) HS2 eq_refl) as RGV end.
  pose proof (field_of_region SEGS EN _ 8%nat v _ 0 56 0 4 0 4%N (SLit 4) 4 RGV Uv2 (or_introl eq_refl)
    ltac:(rewrite denot_lit_U; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VT.
  rewrite Z.add_0_r in VT. cbn [ms_mem restrict N.to_nat Pos.to_nat] in VT.
  pose proof (regs_kept_of_st_ok SEGS EN _ _ regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS2 HAEN
    ltac:(vm_compute; reflexivity)) as KK.
  cbn [ms_regs restrict] in KK.
  prreg HS2 (1%bv : bv 5) R1c. prreg HS2 (9%bv : bv 5) R9c. prreg HS2 (10%bv : bv 5) R10c.
  pmkst HS2.
  apply (CUT s _ _ _ _ HJ2 HPM2).
  + rewrite R1c, EAF2. reflexivity.
  + exact KK.
  + rewrite R9c, (EL2 9%nat) by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). exact G9.
  + rewrite R10c, (EL2 9%nat) by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). exact G9.
  + exact KC.
  + exact VT.
  + right. split; [exact Hc | reflexivity].
- (* not taken: s = 0; s1 = a0 = the literal "" (slots 20-23) *)
  rewrite branch_ne_U, U_SLit, U9 in Hc. rewrite (zcanon_id 0) in Hc by (unfold M64; lia).
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok_x_inv RUNF HS2 HJ2 SHOK2 HPM2 PS_Bspan; [ps_awr2 v Usp2 Uv2 VPL|].
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hn. rewrite <- (KB a Ha Hn). apply (gs_keep_out _ _ W (ms_mem ms0) (ms_mem ms1) v (v + 4) HFr); [|exact Ha | exact Hn].
    intros b (r & Hin & Hr). vm_compute in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; first [rewrite Usp2 in Hr; lia | rewrite Uv2 in Hr; lia] |]). destruct Hin. }
  lazymatch type of HS2 with st_ok _ ?E' ?ssc _ =>
    pose proof (st_ok_region_nth SEGS E' ssc _ 1%nat
      (YP09.mkRegion (Some 8%nat) 0 56 0 4 [YP09.mkChunk 0 (CVal 4 (SLit 4))]) HS2 eq_refl) as RGV;
    assert (HAE2 : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [rae; s0e; s1e; s2e])) E')
      by (eapply env_agree_trans; [exact HAEN | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]);
    assert (Uv2' : bv_unsigned (ew E' 8) = v) by (rewrite ?ew_ewset_other by lia; exact Uv2) end.
  pose proof (field_of_region SEGS _ _ 8%nat v _ 0 56 0 4 0 4%N (SLit 4) 4 RGV Uv2' (or_introl eq_refl)
    ltac:(rewrite denot_lit_U; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VT.
  rewrite Z.add_0_r in VT. cbn [ms_mem restrict N.to_nat Pos.to_nat] in VT.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 _
    [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS2 HAE2
    ltac:(vm_compute; reflexivity)) as KK.
  cbn [ms_regs restrict] in KK.
  prreg HS2 (1%bv : bv 5) R1c. prreg HS2 (9%bv : bv 5) R9c. prreg HS2 (10%bv : bv 5) R10c.
  match type of R9c with ?t => idtac "R9C" t end.
  pmkst HS2.
  apply (CUT PS_LIT _ _ _ _ HJ2 HPM2).
  + rewrite R1c, EAF2. reflexivity.
  + exact KK.
  + rewrite R9c. assert (E243 : ew EN 243 = Z_to_bv 64 (VAL 243)) by (unfold EN, ps_E2; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
    rewrite E243, unsigned_lit_small by (pose proof (pa_val_range 243); lia). unfold PS_LIT, w64. reflexivity.
  + rewrite R10c. assert (E243 : ew EN 243 = Z_to_bv 64 (VAL 243)) by (unfold EN, ps_E2; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
    rewrite E243, unsigned_lit_small by (pose proof (pa_val_range 243); lia). unfold PS_LIT, w64. reflexivity.
  + exact KC.
  + exact VT.
  + left. split; [lia | reflexivity].
Qed.
End p.

(* The m-form text: the walk at the invariant YAkMemnorm.memnorm *)
Theorem pj_string_holds : forall CTX0, tpj_string_specX (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK CTX0.
Proof.
intros CTX0. apply (tpj_string_specX_of_P (cp := CP) (PI := prh_img_A) (PA := PA) B ARx SK).
exact (pj_string_holds_P (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) (fun m m' H => H) CTX0).
Qed.
End f.
End d.

Print Assumptions pj_string_holds_P.
Print Assumptions pj_string_holds.
Set Printing All.
Check pj_string_holds.
Unset Printing All.
