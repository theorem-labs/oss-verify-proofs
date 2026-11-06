(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the CALLER-WINDOW call kit over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp after S, program statics PST), generic: no image
   class, no address, no ledger. Credit: WalkS4, lib/A/Prog/PRW_CallerJ.v at 85a188622c5 (statements and proofs taken
   from there; changes below). Donors there: cj_kept from cgif_file_fuzzer lib/YC20.v:311-325 tlzw_kept and
   lib/YC8n.v:272-287 tlzw_kept_of_journal (origin/release/pau-projects-recipes), generalised to ajournal_x's keep
   clauses; aj_call_xW from YCbqGcall.v aj_call_x (cgif YCbq.v:1845-1883 aj_call, origin/ossv/recipes).
   What a walk of a function in the caller-window form needs:
   - fwin_x / fpostW_x / fpostWF_x: lib/A/PRH_Base.v's fwin / fpostW / fpostWF (K0) restated with the image segs and
     the statics PST as parameters, same bodies: PRH_Base.fpostW B ARx SK STK d FP .. is
     fpostW_x (SK := SK) pa_segs B prh_pst ARx STK d FP .. by unfolding (this file does not Require lib/A).
   - START: ajournal_x_init_W, the widened journal (STK + e) (sp + e) at the entry state.
   - CALL of a caller-window callee: aj_call_xW / aj_call_xWF (callee state in mkst form), aj_call_xW_sp /
     aj_call_xWF_sp (the entry form of YCbqGcall.v's aj_call_x_sp: st_ok, ss_resv, the machine state ms).
     The footprint side condition is YCbqG.v's own fp_sub_x (h-hpreset-7 9052c7a7d74 :688-691), whose fourth
     disjunct `sp0 - STK <= a < sp0` is the caller's window: WalkS4's fp_sub_xW is that predicate, so this file
     no longer states one and ajournal_x_sub_W (the name WalkS4's callers use) is YCbqG's ajournal_x_sub.
   - vrd_call_W: h-verbs-3's lib/A/VrdArm.v call rule (6d4cddbdff5), premise shape kept, as a corollary of
     aj_call_xW_sp at e1 := - o.
   - aj_call_xWF_d: WalkH6's caller-window float call rule (h-walk-identity's S8aCallW.v aj_call_xWF), verbatim: no
     fwin_x for the callee and no window-kept clause on either side.
   - END: cj_kept (the keep clauses of ajournal_x relative to the entry, the walker's window and its written cells OR
     exempted) across stretches (cj_kept_exec) and calls (cj_kept_of_journal), chained (cj_kept_trans), closed by
     fpostW_x_of_kept / fpostWF_x_of_kept; fpostW_x_of_apost: apost_base_x is fpostW_x at e = 0.
   Numerals: 16, 4096, 8, 4 and 2 ^ 64 are LENGTH; 0 is LENGTH (the empty window e = 0) or DERIVED (event count);
   register numbers 1, 3, 4 (ra, gp, tp) are WORD. No address literal; no image constant. *)
(* Modified by Theorem Labs, 2026-10: the kit over a world relation R (suffix R). A free or realloc of a live block can
   hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a relation wider than wle with its journal at that
   relation (YCbqG.v ajournal_xR). cj_keptR is cj_kept with the world conjunct R W W2 (a copy of the body; the guard
   cj_kept_R_wle shows by reflexivity that cj_kept is cj_keptR at wle). The R forms of cj_kept_refl / cj_kept_exec /
   ajournal_x_init_W take R and its reflexivity, of cj_kept_trans / ajournal_x_sub_W R and its transitivity, of
   cj_kept_of_journal / fpostW_x_of_apost / fpostW_x_of_kept / fpostWF_x_of_kept R alone; the call rules
   aj_call_xWR / aj_call_xW_spR / aj_call_xWFR / aj_call_xWF_spR / vrd_call_WR / aj_call_xWF_dR take R and both laws
   first, then the plain rule's binders, with the journals, the callee's post (fpostW_xR / fpostWF_xR) and the
   conclusion at R. Each plain lemma is its R form at wle (wle_refl / wle_trans); its statement is unchanged.
   fpostW_x_R_lift: a plain fpostW_x (journal at wle) is fpostW_xR at every R that contains wle. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YCbqGcallW.v, with its module names changed; 482 of its 526 lines of code are new or changed and 767 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v, with its module names changed; 1639 of its 1698 lines of code are new or changed and 467 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string, image A, ASan): THE \u SUB-STRETCH ps_seg_u of S4_PsDecKit.v - from the
   decode loop head PS_DEC when the text at the read cursor is a backslash and a u, through the dispatch (408..443),
   the four-hex-digit loop at PS_HEX (452..551), the tail at 880 (the cp = 0 refusal, the surrogate split by the stack
   words sp + 24 / sp + 16, the lone-low refusal, the high-surrogate path with `jal hex4` at 988 and its out slot
   sp + 36 in parse_string's OWN frame), `jal put_utf8` at 1044, the constant reload at 1048..1096, `add s3, s3, a0`
   at 1100 and the latch at 856..872. Every exit is the back edge to PS_DEC (ps_dec_afterP) or the free cut at 1276
   (ps_seg_freeP).
   THE GENERIC INVARIANT P (a Theorem Labs lane 12:18Z / 12:22Z): ps_u_segP : ps_seg_uP P for every P with srr_inv_laws segs P
   (PLAW: every engine run goes through its YSRrMemnorm twin at P) and srr_inv_call segs P (PCALL: the stretch crosses
   the two kit calls). At each call, P at the post memory is PCALL applied to the callee's memnorm keep and to P at the
   call memory. THE KEEP COMES FROM THE TEXT: the kit's posts of hex4 and put_utf8 are m-form (fpostWm / fpostm, PRH_Base.v
   fQmn: the body Q0 and `memnorm mem -> memnorm mem'`), so the stretch takes no keep argument. P stays a Section
   Variable: no stretch unfolds an instance of it. The stable ps_u_seg : ps_seg_u is the P := (fun _ => True)
   corollary. (Statement change, exempt: MNHEX / MNPUTU left both statements when the callee TEXTS became m-form; the
   consumer told is WalkS4's S4_PsTop.)
   THE RETURN ADDRESS (the kit fpre's 4th conjunct `raZ regs < YM05.alloc_ceiling`): each call's ra is its jal's return
   pc, the listing slot BASE + PS_OFF + 992 (hex4: `PCall AS_hex4` at slot 6610 on A', PS_OFF + 988) / BASE + PS_OFF +
   1048 (put_utf8: `PCall AS_put_utf8` at slot 6624, PS_OFF + 1044; PS_OFF = 4 x 6363, PAImg_prog 505a51ff7d08
   A_entry_parse_string; on the old A listing the slots were 6312 / 6326 / 6065),
   below the ceiling by PRW_StepKit.pa_slot_lt_ceil_b on a closed goal.
   FILE SET: as the kit's cut 7cdbb61b5fa0 carries it (PRH_Base blob ef7c8ca98529, PRH_FnReader f1ae32e3b2cd, PRH_FnAlloc
   4d8aeba047e5, PRW_StepKit 0df3991c13f4, listing Listing_prog.v 7ed1529926bd, PAImg_prog.v 505a51ff7d08, YSRrMemnorm.v
   5ffa8525936b), this row's S4_PsBase.v and S4_PsDecKit.v; earlier the kit of record at base
   dd6bf533e31 (old-pin acceptance kit 4f18c75d4900, engine s1b 459129c18903).
   THE CALLS. hex4 (988) is a CALLER-WINDOW callee: aj_call_xW at e1 = 48, its out slot sp + 36 inside that window.
   put_utf8 (1044) is an fpost callee: fpostW_x_of_apost then aj_call_xW at e1 = 0, its footprint the 1..4 bytes it
   writes at the write cursor, inside the block fuzz_malloc made. NEITHER calls the allocator: no live-count premise,
   and both posts give S' = S, which is what carries room_live_cf and the room position.
   Numerals: 408 / 452 / 880 / 988 / 992 / 1036 / 1044 / 1048 / 1100 / 856 / 1276 / 328 (DERIVED byte offsets inside
   parse_string), 26444 / 26500 (DERIVED, A': PS_OFF + 992 / PS_OFF + 1048, the two return pcs' listing offsets),
   8 / 16 / 24 / 32 / 36 / 40 / 48 / 144 (DERIVED frame offsets and LENGTHs), 2 ^ 40 / 2 ^ 47 / 2 ^ 64 (DERIVED
   bounds), and the WORD constants of the JSON grammar (34 92 117 32 ... 55296 56320 57344 1024 65536 1114111). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
(* the memnorm keep's runner side and srr_inv_call (YSRrMemnorm.v 5ffa8525936b) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_HShadow S4_PsBase S4_PsDecModel S4_PsSrc S4_PsDecKit S4_PsDecWalk S4_PsUKit.
(* the return pc's ceiling bound (pa_slot_lt_ceil_b), cited qualified. Its Require closure loads lib/Reusable/YF0v.v,
   whose global `Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false)` (YF0v.v:16) turns off lia's
   div / mod reasoning; this file sets it back to the Stdlib default, locally (MEASURED: without it lia fails on the
   `mod` side goals of atoms_f_base, build-20261029T140033Z). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
(* the generic invariant (a Theorem Labs lane 12:18Z / 12:22Z): its laws for the engine runs, its call law for the two calls *)
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Hypothesis PCALL : srr_inv_call segs P.
Hypothesis HW : prh_head_wide.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.
(* the two callee texts of this stretch (the kit, PRH_FnReader.v blob f1ae32e3b2cd :267 / :290), m-form posts *)
Hypothesis HHEX4 : thex4_specX B ARx SK.
Hypothesis HPUTU : tput_utf8_specX B ARx SK.
(* the free cut of the stretch (S4_PsDecKit.v), the walk's other exit *)
Hypothesis HFREE : ps_seg_freeP B ARx SK P CTX CW.

(* ---- THE TWO CALLEES' POST BODIES Q0 (the texts' `fun ly' S' Hp' W' regs' mem' md' => ..`, copied verbatim from
   PRH_FnReader.v blob 0af3032ed375 (preset-tree-at-2026-10-29T17-47-10Z.tsv (sha256 9d6fcfaf6b8e; internal record), Batch-2 ledger: most own), hex4 / put_utf8), named for S4_PsTop.
   Each text's post is
   fQmn mem Q0: Q0 and the memnorm keep, which the stretch turns into P at the post memory by PCALL. ---- *)
Definition KC_hex4 (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (o : Z) (bs : list Z) (Lam : list (Z * Z)) (peak : Z) (cnt fail ran most own : Z)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
  match PjGrammar.hex4 bs with
  | Some h => getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') o 4%nat h
  | None =>
      getr regs' 10 = w64 (-1) /\
      (forall a, o <= a < o + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
  end.
Definition KC_putu (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (o cpv : Z) (Lam : list (Z * Z)) (peak : Z) (cnt fail ran most own : Z)
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  (room_live_cf S -> room_live_cf S') /\
  getr regs' 10 = w64 (Z.of_nat (length (PjGrammar.utf8 cpv))) /\ bytes_at W' mem' o (PjGrammar.utf8 cpv) /\
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.

(* ---- what every cut of the sub-stretch carries: the contract's cut at SOME register file (the registers of the cut
   are re-stated at each leaf, so the memory part travels alone) ---- *)
Definition u_mem (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) : Prop :=
  exists regs0, ps_at_decP B ARx SK P D ly S Hp W regs0 mem md out w r Q.

(* ---- the cut before `jal put_utf8` (offset 1036): a0 = w and a1 = cp are about to be set, s6 = r' the cursor the
   latch takes, and the model step from r to r' emits the encoding of cp ---- *)
Definition u_at_pu (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) (cpv r' : Z) : Prop :=
  u_mem D ly S Hp W mem md out w r Q /\
  0 < cpv <= 1114111 /\
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit (PjGrammar.utf8 cpv) (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r')) /\
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (q + Z.to_nat (r' - r))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r')) /\
  r + 6 <= r' /\ r' <= pi_text D + pi_len D /\
  ps_sh_regs D regs /\ ps_gptp D regs /\ getr regs 26 = w64 34 /\ getr regs 27 = w64 10 /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\
  getr regs 21 = w64 cpv /\ getr regs 22 = w64 r'.

Lemma ps_u_pu : forall D ly S Hp W regs mem md out w r Q cpv r',
  ps_pre B ARx CTX CW D -> ps_dec_afterP B ARx SK P CW D r ->
  u_at_pu D ly S Hp W regs mem md out w r Q cpv r' ->
  SRr segs W (u_cfg 1036 regs mem md) (ps_finP B ARx SK P CW D).
Proof.
  intros D ly S Hp W regs mem md out w r Q cpv r' HPRE HAFTER HAT.
  destruct HAT as ((regs0 & HDEC) & Hcp & Hstep & Hscan & Hrr & Hrend & HSH & HGT & K26 & K27
    & R2 & R18 & R19 & R20 & R8 & R9 & R21 & R22).
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs0 mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0. pose proof (ps_head8 HW) as Hh8.
  pose proof ps_stk144 as Hs144.
  pose proof HPRE as (HF & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & _ & _ & HWIN & Hq1 & Hq2 & _).
  pose proof HF as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & Hsp64).
  pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & _ & _ & HCST & HIN & HROD & HSC
    & _ & _ & _ & _ & _ & _ & _ & HREL).
  pose proof HAL as (Hcnt & Hout4 & Hout16 & EHp & Eab & HLED & HVIS & HRL & HRPOS & Hbb).
  destruct HREL as (done & Hbd & Hdl & HS0 & HN0 & Hr0 & Hwo & Hww & Hsync).
  pose proof (ajx_ly HJ) as Hly. pose proof (ajx_pres HJ) as Jpres. pose proof (ajx_stk HJ) as Jstk.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  (* the step's cursor move keeps the scan in step, so r' is inside the text *)
  destruct (psd_scan_sync _ _ _ _ Hscan Hsync) as [Hsync' Hle].
  assert (Hr'lt : r' < pi_text D + pi_len D)
    by (rewrite <- Hlen; apply (ps_scan_some_len (pi_tb D) (pi_text D) r' _ ltac:(lia) Hsync')).
  assert (Hlen4 : (1 <= length (PjGrammar.utf8 cpv) <= 4)%nat) by (apply psd_utf8_len; lia).
  (* ---- the symbolic state at the cut ---- *)
  set (E := EX regs []).
  assert (HEI : img_env VAL A_LIM E) by apply EX_env.
  assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (unfold E; rewrite (EX_reg regs [] 2 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = Z_to_bv 64 (pi_q D)) by (unfold E; rewrite (EX_reg regs [] 8 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (unfold E; rewrite (EX_reg regs [] 9 9%bv eq_refl); exact R9).
  assert (E19 : ew E 19 = Z_to_bv 64 w) by (unfold E; rewrite (EX_reg regs [] 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 r) by (unfold E; rewrite (EX_reg regs [] 20 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 cpv) by (unfold E; rewrite (EX_reg regs [] 21 21%bv eq_refl); exact R21).
  assert (E18 : ew E 18 = Z_to_bv 64 out) by (unfold E; rewrite (EX_reg regs [] 18 18%bv eq_refl); exact R18).
  assert (E22 : ew E 22 = Z_to_bv 64 r') by (unfold E; rewrite (EX_reg regs [] 22 22%bv eq_refl); exact R22).
  assert (E23 : ew E 23 = Z_to_bv 64 (SHADOW_OFF + pi_q D / 8))
    by (unfold E; rewrite (EX_reg regs [] 23 23%bv eq_refl); exact (proj1 (proj2 HSH))).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E; rewrite (EX_reg regs [] 24 24%bv eq_refl); exact (proj1 HSH)).
  assert (HS : st_ok_pi segs VAL E ss_pu
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + 1036))) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. apply build_st_ok.
    - apply EX_regs_ok.
    - apply (pins_pu_ok E regs (pi_q D)); [exact E9 | exact E24 | lia | exact (proj2 (proj2 HSH)) | exact K26 | exact K27].
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - apply facts_ok_atoms. apply (atoms_f_base E (PS_SP D) (pi_q D) r w); try assumption; lia. }
  assert (SHOK : sh_ok segs dBx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  pose proof HMN as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  unfold u_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
  + apply awr_ro. vm_compute. reflexivity.
  + (* ---- at put_utf8's entry ---- *)
    pose proof (frame_ro E (ss_mem ss_pu) _ _ ltac:(vm_compute; reflexivity) HFr) as HMeq.
    assert (HAVeq : forall a, aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
      by (intros a; apply aview_eq_of; apply HMeq).
    assert (HDECm : ps_at_decP B ARx SK P D ly S Hp W regs0 (ms_mem ms)
      (with_vm_backing (m_vm_lazy md) mat md) out w r Q).
    { apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs0 mem md out w r Q
        (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) k HPRE HDEC HJ HPM
        (same_but_materialized_wvb_any md mat)); [intros x _; apply HMeq | exact HG]. }
    assert (HB4096 : 4096 <= BASE) by (unfold Z.le; vm_compute; discriminate).
    assert (HBtop : BASE + 2 ^ 40 < 2 ^ 64) by (unfold Z.lt; vm_compute; reflexivity).
    assert (HSTKv : 160 <= STK_parse_string) by (unfold Z.le; vm_compute; discriminate).
    assert (HPUv : STK_put_utf8 = 16) by (vm_compute; reflexivity).
    prreg HS (2%bv : bv 5) C2. prreg HS (1%bv : bv 5) C1. prreg HS (3%bv : bv 5) C3.
    prreg HS (4%bv : bv 5) C4. prreg HS (8%bv : bv 5) C8. prreg HS (10%bv : bv 5) C10.
    prreg HS (11%bv : bv 5) C11.
    rewrite E2 in C2. rewrite E19 in C10. rewrite E21 in C11. rewrite E8 in C8.
    (* the block the new bytes land in *)
    assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
      by (rewrite Eab; apply in_or_app; right; left; reflexivity).
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & Hpres & _).
    rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ, Hpres by lia.
    assert (Hwlen : w + Z.of_nat (length (PjGrammar.utf8 cpv)) <= out + Z.of_nat Q + 1) by lia.
    destruct (chain_now B ARx SK P LAWS HW CTX CW D ly S Hp W regs0 mem md out w r Q HPRE HDEC) as (ch & HCH).
    eapply SRr_bind.
    { eapply (YCbqGcallW.aj_call_xW_sp (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PS_PAImg)) with
        (STK1 := STK_put_utf8) (e1 := 0)
        (FP1 := [(w, w + Z.of_nat (length (PjGrammar.utf8 cpv)))]) (o := PS_SP D - PS_WSP D) (ms := ms) (E := E)
        (ch1 := ch).
      - exact HS.
      - vm_compute. reflexivity.
      - exact HJ.
      - unfold spZ. rewrite C2. rewrite unsigned_lit_small by lia. lia.
      - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & He16 & _ & _).
        replace (spZ (pi_regs D) - 144 - (spZ (pi_regs D) + pi_e D)) with (- (144 + pi_e D)) by lia.
        rewrite Z.mod_opp_l_z; [reflexivity | lia |]. rewrite <- Zplus_mod_idemp_r, He16. reflexivity.
      - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & _ & _ & _). lia.
      - rewrite HPUv. lia.
      - unfold PS_WSP, PS_WSTK, PS_SP. rewrite ps_frame144, HPUv. lia.
      - lia.
      - reflexivity.
      - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & _ & _ & _). lia.
      - rewrite C3. unfold E. rewrite (EX_reg regs [] 3 3%bv eq_refl). rewrite (proj1 HGT). exact Hgp0.
      - rewrite C4. unfold E. rewrite (EX_reg regs [] 4 4%bv eq_refl). rewrite (proj2 HGT). exact Htp0.
      - exact C1.
      - apply (ret_ok_codeptr_v 26500); [lia | reflexivity].
      - rewrite unsigned_lit_small by lia. lia.
      - (* the frame chain from q at the call view *)
        unfold s0Z. rewrite C8. rewrite unsigned_lit_small by lia.
        replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) by lia.
        exact (achain_rd ly _ _ _ _ ch HAVeq HCH).
      - (* put_utf8's text *)
        intros HPRE1 _.
        eapply SRr_mono.
        { refine (HPUTU ly S Hp W (ms_regs ms) (ms_mem ms) _ _ w cpv
            ((out, Z.of_nat Q + 1) :: pi_Lam D)
            (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D)
            _ C10 C11 ltac:(lia) _ _ _).
          - (* fpre *)
            split; [exact HPRE1|]. split.
            + intros a Hro Hno Her. rewrite (HAVeq a). exact (HROD a Hro Hno Her).
            + split.
              * unfold spZ. rewrite C2. rewrite unsigned_lit_small by lia. rewrite Eshi. lia.
              * split.
                -- (* the return pc: the slot after `jal put_utf8` (1044), PS_OFF + 1048 *)
                   unfold raZ. rewrite C1. rewrite unsigned_lit_small by lia.
                   apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := PS_PAListing) (PI := PS_PAImg) 26500);
                     [lia | vm_compute; reflexivity].
                -- (* FRM0-ENTRY: the section's rounding mode, from the entry's fpre *)
                   exact (ps_frm0 _ _ _ _ _ HPRE).
          - (* the destination lies in the harness block the ledger holds *)
            exists out, (Z.of_nat Q + 1). split; [left; reflexivity|]. split; [lia | lia].
          - (* wdest_ok *)
            split; [lia|]. split; [lia|]. split.
            + unfold amem_range. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
              * left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
              * right. unfold kHighMemEnd in *. lia.
            + split.
              * intros a Ha. split; [|split].
                -- apply (writable_at_grows segs _ _ a HG). apply (apresent_writable segs).
                   exact (proj1 (Hpres a ltac:(lia))).
                -- exact (proj2 (Hpres a ltac:(lia))).
                -- unfold spZ. rewrite C2. rewrite unsigned_lit_small by lia. rewrite HPUv. lia.
              * split.
                -- eapply range_addressable_agree; [intros x Hx; apply HAVeq|].
                   apply (range_addressable_sub _ SHADOW_OFF out (Z.of_nat Q + 1)); [exact (proj1 HVIS) | lia | lia].
                -- intros _. apply (hull_keep (aview segs (w_H W) mem)); [|intros s Hs; apply HAVeq].
                   apply (psrc_hull_sub _ out (Z.of_nat Q + 1)); [apply (proj2 HVIS); lia | lia | lia | lia].
          - (* the ledger at the call memory *)
            apply (ledger_keep B ly S Hp W mem (ms_mem ms) _ _ _ _ _ _ _ HLED);
              [intros a _; apply HAVeq | intros a kk i _ _; apply HAVeq]. }
        cbv beta. intros W3 c3 _ HP3. exact (YCbqGcallW.fpostW_x_of_apost segs B prh_pst ARx _ _ _ _ _ _ _ _ _ _ _ _ HP3).
      - (* the callee's footprint: the bytes it writes are in the block made since the entry *)
        intros a (rg & [<-|[]] & Hrg). cbn [fst snd] in Hrg. right; left.
        exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|].
        split; [apply (ps_newblk B ARx LAWS ly S (pi_ly D) (pi_S D) Hp W mem md
                         (out - cf_head, Z.of_nat Q + 1 + cf_head) HAR); [cbn [snd]; lia | exact Eab]|].
        rewrite ps_req by lia. lia. }
    cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HXc & HPres2 & HQc).
    (* the text's m-form post: the body Q0 and the memnorm keep, which PCALL turns into P at the post memory *)
    destruct HQc as (HQc & HMNc).
    destruct HQc as (HRL2 & Ra0 & HBY & EHp2 & ES2 & EAB2 & HLED2). subst S2. subst Hp2.
    assert (HMN2 : P mem2) by exact (PCALL (ms_mem ms) mem2 HMNc HPM).
    clear HPM. pose proof HMN2 as HPM.
    replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) in HJc, HXc by lia.
    (* ---- the cut at the post state, same ghost registers ---- *)
    assert (HDEC2 : ps_at_decP B ARx SK P D ly2 S Hp W2 regs0 mem2 md2 out w r Q).
    { apply (dec_call B ARx SK P LAWS HW ZSA IMGV CTX CW D ly S Hp W regs0 (ms_mem ms)
        (with_vm_backing (m_vm_lazy md) mat md) out w r Q
        STK_put_utf8 0 [(w, w + Z.of_nat (length (PjGrammar.utf8 cpv)))] ly2 W2 mem2 md2 k1 (k + k1)
        HPRE HDECm HJ2 HJc HXc);
      [ lia | rewrite HPUv; lia | rewrite HPUv; lia
      | intros a (rg & [<-|[]] & Hrg); cbn [fst snd] in Hrg; right; lia
      | exact EAB2 | exact HLED2 | exact HMN2 ]. }
    (* ---- the reload block and the latch (1048..1104, 856..872) ---- *)
    assert (P2 : getr regs2 2%bv = getr (ms_regs ms) 2%bv)
      by (apply (pres_reg _ _ 2); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P8 : getr regs2 8%bv = getr (ms_regs ms) 8%bv)
      by (apply (pres_reg _ _ 8); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P9 : getr regs2 9%bv = getr (ms_regs ms) 9%bv)
      by (apply (pres_reg _ _ 9); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P18 : getr regs2 18%bv = getr (ms_regs ms) 18%bv)
      by (apply (pres_reg _ _ 18); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P19 : getr regs2 19%bv = getr (ms_regs ms) 19%bv)
      by (apply (pres_reg _ _ 19); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P20 : getr regs2 20%bv = getr (ms_regs ms) 20%bv)
      by (apply (pres_reg _ _ 20); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P22 : getr regs2 22%bv = getr (ms_regs ms) 22%bv)
      by (apply (pres_reg _ _ 22); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P24 : getr regs2 24%bv = getr (ms_regs ms) 24%bv)
      by (apply (pres_reg _ _ 24); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P25 : getr regs2 25%bv = getr (ms_regs ms) 25%bv)
      by (apply (pres_reg _ _ 25); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P26 : getr regs2 26%bv = getr (ms_regs ms) 26%bv)
      by (apply (pres_reg _ _ 26); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P27 : getr regs2 27%bv = getr (ms_regs ms) 27%bv)
      by (apply (pres_reg _ _ 27); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P3 : getr regs2 3%bv = getr (ms_regs ms) 3%bv)
      by (apply (pres_reg _ _ 3); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P4 : getr regs2 4%bv = getr (ms_regs ms) 4%bv)
      by (apply (pres_reg _ _ 4); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    assert (P23 : getr regs2 23%bv = getr (ms_regs ms) 23%bv)
      by (apply (pres_reg _ _ 23); [exact HPres2 | unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
    prreg HS (18%bv : bv 5) C18. prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20.
    prreg HS (22%bv : bv 5) C22. prreg HS (9%bv : bv 5) C9. prreg HS (23%bv : bv 5) C23.
    prreg HS (24%bv : bv 5) C24. prreg HS (25%bv : bv 5) C25.
    prreg HS (26%bv : bv 5) C26. prreg HS (27%bv : bv 5) C27.
    pose proof (sv_shx E 9 (pi_q D + 8) E9 ltac:(lia) E24) as HSHX. unfold shx in HSHX. prreg_norm HSHX.
    rewrite HSHX in C25.
    rewrite E18 in C18. rewrite E19 in C19. rewrite E20 in C20. rewrite E22 in C22. rewrite E9 in C9.
    rewrite E23 in C23. rewrite E24 in C24.
    (* ---- the state at the reload block (1048) ---- *)
    set (EA := EX regs2 [w64 (pi_text D + pi_len D)]).
    assert (HEIA : img_env VAL A_LIM EA) by apply EX_env.
    assert (A2 : ew EA 2 = Z_to_bv 64 (PS_SP D))
      by (unfold EA; rewrite (EX_reg regs2 _ 2 2%bv eq_refl), P2; exact C2).
    assert (A8 : ew EA 8 = Z_to_bv 64 (pi_q D))
      by (unfold EA; rewrite (EX_reg regs2 _ 8 8%bv eq_refl), P8; exact C8).
    assert (A9 : ew EA 9 = Z_to_bv 64 (pi_q D + 8))
      by (unfold EA; rewrite (EX_reg regs2 _ 9 9%bv eq_refl), P9; exact C9).
    assert (A10 : ew EA 10 = Z_to_bv 64 (Z.of_nat (length (PjGrammar.utf8 cpv))))
      by (unfold EA; rewrite (EX_reg regs2 _ 10 10%bv eq_refl); exact Ra0).
    assert (A18 : ew EA 18 = Z_to_bv 64 out)
      by (unfold EA; rewrite (EX_reg regs2 _ 18 18%bv eq_refl), P18; exact C18).
    assert (A19 : ew EA 19 = Z_to_bv 64 w)
      by (unfold EA; rewrite (EX_reg regs2 _ 19 19%bv eq_refl), P19; exact C19).
    assert (A20 : ew EA 20 = Z_to_bv 64 r)
      by (unfold EA; rewrite (EX_reg regs2 _ 20 20%bv eq_refl), P20; exact C20).
    assert (A22 : ew EA 22 = Z_to_bv 64 r')
      by (unfold EA; rewrite (EX_reg regs2 _ 22 22%bv eq_refl), P22; exact C22).
    assert (A23 : ew EA 23 = Z_to_bv 64 (SHADOW_OFF + pi_q D / 8))
      by (unfold EA; rewrite (EX_reg regs2 _ 23 23%bv eq_refl), P23; exact C23).
    assert (A24 : ew EA 24 = Z_to_bv 64 SHADOW_OFF)
      by (unfold EA; rewrite (EX_reg regs2 _ 24 24%bv eq_refl), P24; exact C24).
    assert (A25 : ew EA 25 = Z_to_bv 64 (SHADOW_OFF + (pi_q D + 8) / 8))
      by (unfold EA; rewrite (EX_reg regs2 _ 25 25%bv eq_refl), P25; exact C25).
    assert (A26 : ew EA 26 = Z_to_bv 64 34)
      by (unfold EA; rewrite (EX_reg regs2 _ 26 26%bv eq_refl), P26; exact C26).
    assert (A27 : ew EA 27 = Z_to_bv 64 10)
      by (unfold EA; rewrite (EX_reg regs2 _ 27 27%bv eq_refl), P27; exact C27).
    assert (A32 : ew EA 32 = Z_to_bv 64 (pi_text D + pi_len D))
      by (unfold EA; exact (EX_extra regs2 _ 0 ltac:(unfold A_TEXT; lia))).
    pose proof HDEC2 as (_ & _ & _ & _ & _ & HIN2 & _).
    pose proof HIN2 as (V2p & V2e & V2d & _ & _ & _ & _ & _ & _ & _ & _ & _).
    assert (HSA : st_ok_pi segs VAL EA ss_ap
      (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + (PSO + 1048))) mem2 (seg_rom segs)))).
    { rewrite restrict_mkst_fx. apply build_st_ok.
      - apply EX_regs_ok.
      - apply Forall_cons; [cbn [fst snd]|apply Forall_nil].
        rewrite P25, C25. symmetry. apply (sv_shx EA 9 (pi_q D + 8)); [exact A9 | lia | exact A24].
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil].
        unfold region_ok, rg_end.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite A9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs EA (rdW W2 mem2) (pi_q D + 8) 0 8 (SOff 32 0) (pi_text D + pi_len D));
          [ apply bv_eq; rewrite denot_SOff, A32, Z.add_0_r, !unsigned_lit_small by lia;
            apply zcanon_id; unfold M64; lia
          | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V2e ].
      - cbn [pairwise_disjoint all_disjoint ss_mem ss_ap]. split; exact I.
      - apply facts_ok_atoms. apply atoms_ok_app.
        + apply (atoms_f_base EA (PS_SP D) (pi_q D) r w); try assumption; lia.
        + cbn [atoms_ok]. split; [|split; [|split; [|exact I]]].
          * apply (afact_rng EA 22 r'); [exact A22 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
          * apply (afact_rng EA 10 (Z.of_nat (length (PjGrammar.utf8 cpv))));
              [exact A10 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
          * apply (afact_rng EA 32 (pi_text D + pi_len D));
              [exact A32 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
    assert (SHOKA : sh_ok segs dBx [] EA (mrestrict (w_H W2) mem2)) by apply Forall_nil.
    pose proof HDEC2 as ((k2 & HJ2c & _) & _).
    pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
    pose (BR := paj_branch (PI := PS_PAImg)).
    pose proof (ajx_ar HJ2) as HAR2. cbv beta in HAR2.
    pose proof (ajx_ly HJ2) as Hly2.
    pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
    assert (HSTKval : STK_parse_string = 16560) by (vm_compute; reflexivity).
    assert (Hqlo : ly_stk_lo ly2 <= pi_q D /\ pi_q D + 24 <= ly_stk_hi ly2).
    { rewrite Eslo2, Eshi2. pose proof Hslo as Hs. rewrite HSTKval in Hs.
      destruct HWIN as (_ & _ & Hetop & _). lia. }
    paj_run_tok_x_inv RUN HSA HJ2 SHOKA HPM dBspan.
    * (* the latch's shadow check of the cursor's end word: the machine stack reads shadow 0 *)
      cbn [ms_mem mkst].
      apply (ob_stack (w_H W2) mem2 EA dBx (SOff 9 0) (pi_q D + 8) 8).
      -- intros a Ha. apply (alx_zshadow_byte segs B ARx LAWS ly2 S Hp W2 mem2 md2 a HAR2). lia.
      -- unfold dBx. rewrite U_SOff, A24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
         apply zcanon_id. unfold SHADOW_OFF, M64. lia.
      -- rewrite U_SOff, A9, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
    * apply awr_ro. vm_compute. reflexivity.
    * (* the branch `bltu s6, a1` at 872 *)
      lazymatch goal with HX : frame_of EA (ss_mem ss_ap) (mrestrict (w_H W2) mem2) _ |- _ =>
        pose proof (frame_ro EA (ss_mem ss_ap) _ _ ltac:(vm_compute; reflexivity) HX) as HMeqA end.
      lazymatch goal with HX : mem_grows (mrestrict (w_H W2) mem2) _ |- _ => pose proof HX as HGA end.
      psrr_branch_tok RUN BR HSA SHOKA dBspan.
      -- (* r' < end: the back edge to PS_DEC *)
         paj_run_to_tok_x_inv RUNTO HSA HJ2 SHOKA HPM dBspan (PSO + 328).
         ++ apply awr_ro. vm_compute. reflexivity.
         ++ (* ---- the leaf at PS_DEC: the cut at r' > r, then the induction hypothesis ---- *)
            lazymatch goal with HX : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms0)) (mrestrict (w_H W2) (ms_mem ?m1)) |- _ =>
              pose proof (fun Hro => frame_ro _ _ _ _ Hro HX) as HMeqB end.
            specialize (HMeqB ltac:(vm_compute; reflexivity)).
            lazymatch goal with HX : mem_grows (mrestrict (w_H W2) (ms_mem ms0)) _ |- _ => pose proof HX as HGB end.
            assert (HMeq2 : forall x, rdW W2 (ms_mem ms1) x = rdW W2 mem2 x) by (intros x; rewrite HMeqB; apply HMeqA).
            assert (HG2 : mem_grows (rdW W2 mem2) (rdW W2 (ms_mem ms1))) by exact (mem_grows_trans _ _ _ HGA HGB).
            lazymatch goal with |- SRr _ _ {| cfg_ms := ms1; cfg_model := ?MD |} _ =>
              rewrite (u_reseat (w_H W2) _ _ ms1 MD PS_DEC HSA ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
              assert (HDEC4 : ps_at_decP B ARx SK P D ly2 S Hp W2 regs0 (ms_mem ms1) MD out w r Q)
                by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly2 S Hp W2 regs0 mem2 md2 out w r Q
                      (ms_mem ms1) MD _ HPRE HDEC2 HJ2 HPM (same_but_materialized_wvb_any md2 _));
                    [intros x _; apply HMeq2 | exact HG2])
            end.
            pose proof (bytes_at_keep W2 mem2 (ms_mem ms1) w (PjGrammar.utf8 cpv) HMeq2 HBY) as HBY1.
            (* the registers at the leaf *)
            prreg HSA (1%bv : bv 5) L1. prreg HSA (2%bv : bv 5) L2. prreg HSA (3%bv : bv 5) L3.
            prreg HSA (4%bv : bv 5) L4. prreg HSA (5%bv : bv 5) L5. prreg HSA (6%bv : bv 5) L6.
            prreg HSA (7%bv : bv 5) L7. prreg HSA (8%bv : bv 5) L8. prreg HSA (9%bv : bv 5) L9.
            prreg HSA (11%bv : bv 5) L11. prreg HSA (14%bv : bv 5) L14. prreg HSA (15%bv : bv 5) L15.
            prreg HSA (16%bv : bv 5) L16. prreg HSA (17%bv : bv 5) L17. prreg HSA (18%bv : bv 5) L18.
            prreg HSA (20%bv : bv 5) L20. prreg HSA (21%bv : bv 5) L21. prreg HSA (23%bv : bv 5) L23.
            prreg HSA (24%bv : bv 5) L24. prreg HSA (26%bv : bv 5) L26. prreg HSA (27%bv : bv 5) L27.
            prreg HSA (28%bv : bv 5) L28. prreg HSA (29%bv : bv 5) L29. prreg HSA (30%bv : bv 5) L30.
            prreg HSA (31%bv : bv 5) L31.
            pose proof (st_ok_pi_restrict_reg _ _ _ _ 19%bv HSA) as L19.
            pose proof (st_ok_pi_restrict_reg _ _ _ _ 25%bv HSA) as L25.
            change (sr_get _ 19%bv) with (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) in L19.
            change (sr_get _ 25%bv) with (shx 9) in L25.
            rewrite (sv_add _ 10 19 (Z.of_nat (length (PjGrammar.utf8 cpv))) w) in L19
              by (try (rewrite ew_ewset_other by lia); first [exact A10 | exact A19 | lia]).
            rewrite (sv_shx _ 9 (pi_q D + 8)) in L25
              by (try (rewrite ew_ewset_other by lia); first [exact A9 | exact A24 | lia]).
            rewrite A2 in L2. rewrite A8 in L8. rewrite A9 in L9. rewrite A32 in L11. rewrite A18 in L18.
            rewrite A22 in L20. rewrite A23 in L23. rewrite A24 in L24. rewrite A26 in L26. rewrite A27 in L27.
            unfold EA in L3, L4. rewrite (EX_reg regs2 _ 3 3%bv eq_refl), P3, C3 in L3.
            rewrite (EX_reg regs2 _ 4 4%bv eq_refl), P4, C4 in L4.
            unfold E in L3, L4. rewrite (EX_reg regs [] 3 3%bv eq_refl) in L3. rewrite (EX_reg regs [] 4 4%bv eq_refl) in L4.
            apply ps_finP_hand.
            apply (HAFTER ly2 S Hp W2 (ms_regs ms1) (ms_mem ms1) _ out (w + Z.of_nat (length (PjGrammar.utf8 cpv))) r' Q);
              [|lia].
            apply (dec_closeN B ARx SK P CTX CW D ly2 S Hp W2 regs0 (ms_mem ms1) _ out w r Q (ms_regs ms1) r'
                     (PjGrammar.utf8 cpv) HPRE HDEC4 Hstep Hscan ltac:(lia) ltac:(lia) HBY1).
            ** split; [exact L24|]. split; [exact L23|]. exact L25.
            ** split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)].
            ** split; [exact L26|]. split; [exact L14|]. split; [exact L16|]. split; [exact L15|].
               split; [exact L17|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|].
               split; [exact L28|]. split; [exact L29|]. split; [exact L30|]. split; [exact L31|].
               split; [exact L27|]. split; [exact L21 | exact L1].
            ** exact L2.
            ** exact L18.
            ** rewrite L19. f_equal. lia.
            ** exact L20.
            ** exact L11.
            ** exact L8.
            ** exact L9.
      -- (* r' >= end: refuted, r' is inside the text *)
         exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc.
         rewrite !U_SOff, ?ew_ewset_other in Hc by lia.
         rewrite A22, A32, !Z.add_0_r, !unsigned_lit_small in Hc by lia.
         rewrite (zcanon_id r') in Hc by (unfold M64; lia).
         rewrite (zcanon_id (pi_text D + pi_len D)) in Hc by (unfold M64; lia). lia.
Qed.


(* ---- the free exit of a run (offset 1276): the contract's free cut, then the Section hypothesis ---- *)
Lemma u_free_run : forall D ly S Hp W regs0 mem md out w r Q mem' md' k' regs',
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs0 mem md out w r Q ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  ps_gptp D regs' -> getr regs' 2 = w64 (PS_SP D) -> getr regs' 18 = w64 out -> getr regs' 8 = w64 (pi_q D) ->
  SRr segs W (cfg_at segs (ps_pc PS_FREECUT) regs' mem' md') (ps_finP B ARx SK P CW D).
Proof.
  intros D ly S Hp W regs0 mem md out w r Q mem' md' k' regs' HPRE HDEC HJ' HMN' Hsame HM HG HN HGT R2 R18 R8.
  apply ps_finP_hand. apply (HFREE D ly S Hp W regs' mem' md' out Q HPRE).
  exact (free_close B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs0 mem md out w r Q regs' mem' md' k'
           HPRE HDEC HN HJ' HMN' Hsame HM HG HGT R2 R18 R8).
Qed.
Ltac u_free_leaf W HS HJ HPM HPRE HDEC HN :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
    rewrite (u_reseat (w_H W) _ _ msN MD PS_FREECUT HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
    eapply (u_free_run _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msN) MD _ (ms_regs msN) HPRE HDEC HJ HPM);
    [ apply same_but_materialized_wvb_any
    | let x := fresh "x" in intros x _; revert x; u_memeq
    | u_grows
    | exact HN | | | | ]
  end.

(* ---- the cut after `jal hex4` (offset 992): hex4 read the four digits after the second \u into sp + 36 ---- *)
Definition u_at_ah (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) (cpv : Z) : Prop :=
  u_mem D ly S Hp W mem md out w r Q /\
  tb_at D r = 92 /\ tb_at D (r + 1) = 117 /\ r + 12 <= pi_text D + pi_len D /\
  PjGrammar.hex4 (hexs D r) = Some cpv /\ 55296 <= cpv < 56320 /\
  tb_at D (r + 6) = 92 /\ tb_at D (r + 7) = 117 /\
  match PjGrammar.hex4 (lows D r) with
  | Some lo => getr regs 10 = w64 0 /\ val_mem segs (rdW W mem) (PS_SP D + 36) 4 lo
  | None => getr regs 10 = w64 (-1)
  end /\
  ps_sh_regs D regs /\ ps_gptp D regs /\ getr regs 26 = w64 34 /\ getr regs 27 = w64 10 /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 21 = w64 cpv.

Lemma ps_u_ah : forall D ly S Hp W regs mem md out w r Q cpv,
  ps_pre B ARx CTX CW D -> ps_dec_afterP B ARx SK P CW D r ->
  u_at_ah D ly S Hp W regs mem md out w r Q cpv ->
  SRr segs W (u_cfg 992 regs mem md) (ps_finP B ARx SK P CW D).
Proof.
  intros D ly S Hp W regs mem md out w r Q cpv HPRE HAFTER HAT.
  destruct HAT as ((regs0 & HDEC) & Hb0 & Hb1 & Hr12 & Hhex & Hhi & Hb6 & Hb7 & HLO & HSH & HGT & K26 & K27
    & R2 & R18 & R19 & R20 & R8 & R9 & R21).
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs0 mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0.
  pose proof HDEC as ((k & HJ & _ & _ & _ & _ & HMN) & _ & _ & _ & HCST & _).
  destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V24 & V16 & V8).
  (* the model: the twelve bytes from r *)
  pose proof (rest_u12 D r ltac:(lia) ltac:(rewrite Hlen; lia)) as HR12.
  rewrite Hb0, Hb1, Hb6, Hb7 in HR12.
  assert (Hlow : PjGrammar.low [92; 117; tb_at D (r + 8); tb_at D (r + 9); tb_at D (r + 10); tb_at D (r + 11)] =
    match PjGrammar.hex4 (lows D r) with
    | Some lo => if (56320 <=? lo) && (lo <=? 57343) then Some lo else None
    | None => None
    end) by (rewrite psd_low_hex; reflexivity).
  assert (HNlow : PjGrammar.low [92; 117; tb_at D (r + 8); tb_at D (r + 9); tb_at D (r + 10); tb_at D (r + 11)] = None ->
    PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
  { intros HL. rewrite HR12. exact (psd_dec_hi_nolow _ _ _ _ _ _ _ _ _ _ _ cpv Hhex Hhi HL). }
  pose proof HMN as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (BR := paj_branch (PI := PS_PAImg)).
  unfold u_cfg.
  destruct (PjGrammar.hex4 (lows D r)) as [lo|] eqn:Elo.
  - (* ---- hex4 read four digits: lo at sp + 36 ---- *)
    destruct HLO as [R10 Vlo].
    pose proof (hex4_range (lows D r) lo eq_refl Elo) as Hlo.
    set (E := EX regs [w64 lo]).
    assert (HEI : img_env VAL A_LIM E) by apply EX_env.
    assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (unfold E; rewrite (EX_reg regs _ 2 2%bv eq_refl); exact R2).
    assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (unfold E; rewrite (EX_reg regs _ 9 9%bv eq_refl); exact R9).
    assert (E19 : ew E 19 = Z_to_bv 64 w) by (unfold E; rewrite (EX_reg regs _ 19 19%bv eq_refl); exact R19).
    assert (E20 : ew E 20 = Z_to_bv 64 r) by (unfold E; rewrite (EX_reg regs _ 20 20%bv eq_refl); exact R20).
    assert (E21 : ew E 21 = Z_to_bv 64 cpv) by (unfold E; rewrite (EX_reg regs _ 21 21%bv eq_refl); exact R21).
    assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF)
      by (unfold E; rewrite (EX_reg regs _ 24 24%bv eq_refl); exact (proj1 HSH)).
    assert (E32 : ew E 32 = Z_to_bv 64 lo) by (unfold E; exact (EX_extra regs _ 0 ltac:(unfold A_TEXT; lia))).
    assert (HS : st_ok_pi segs VAL E ss_ah
      (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + 992))) mem (seg_rom segs)))).
    { rewrite restrict_mkst_fx. apply build_st_ok.
      - apply EX_regs_ok.
      - apply Forall_app. split.
        + apply (pins_pu_ok E regs (pi_q D)); [exact E9 | exact E24 | lia | exact (proj2 (proj2 HSH)) | exact K26 | exact K27].
        + apply Forall_cons; [cbn [fst snd]; exact R10 | apply Forall_nil].
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        + unfold region_ok, rg_lo.
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
          rewrite E2, unsigned_lit_small by lia.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val segs E (rdW W mem) (PS_SP D) 36 4 (SOff 32 0) lo); [| cbn; lia | cbn; lia | exact Vlo].
          apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
        + apply (rok_k E _ (PS_SP D) E2); [lia | lia | exact V8 | exact V16 | exact V24].
      - apply pairwise_disjoint_of_extents. unfold extent_of_region, rg_lo, rg_k.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, !unsigned_lit_small by lia.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
      - apply facts_ok_atoms. apply atoms_ok_app.
        + apply (atoms_f_base E (PS_SP D) (pi_q D) r w); try assumption; lia.
        + cbn [atoms_ok]. split; [|split; [|exact I]].
          * apply (afact_rng E 21 cpv); [exact E21 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
          * apply (afact_rng E 32 lo); [exact E32 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
    assert (SHOK : sh_ok segs dBx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
    + apply awr_ro. vm_compute. reflexivity.
    + psrr_branch_tok RUN BR HS SHOK dBspan.
      * (* lo is not a low surrogate: the free path *)
        rewrite branch_ltu_U, !U_SOff, U_SLit, ?ew_ewset_other, E32, unsigned_lit_small in Hc by lia.
        apply Z.ltb_lt in Hc. unfold zcanon, M64 in Hc.
        pose proof (Z.div_mod (lo + -57344) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (lo + -57344) (2 ^ 64) ltac:(lia)).
        change (18446744073709550592 mod 2 ^ 64) with 18446744073709550592 in Hc.
        assert (Hnl : ~ (56320 <= lo <= 57343)) by lia.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
        -- apply awr_ro. vm_compute. reflexivity.
        -- assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
           { apply HNlow. rewrite Hlow. destruct (Z.leb_spec 56320 lo); destruct (Z.leb_spec lo 57343); cbn [andb];
               [lia | reflexivity | reflexivity | reflexivity]. }
           u_free_leaf W HS HJ HPM HPRE HDEC HN.
           ++ prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4. unfold E in L3, L4.
              rewrite (EX_reg regs _ 3 3%bv eq_refl) in L3. rewrite (EX_reg regs _ 4 4%bv eq_refl) in L4.
              split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)].
           ++ prreg HS (2%bv : bv 5) L2. rewrite L2. exact E2.
           ++ prreg HS (18%bv : bv 5) L18. rewrite L18. unfold E. rewrite (EX_reg regs _ 18 18%bv eq_refl). exact R18.
           ++ prreg HS (8%bv : bv 5) L8. rewrite L8. unfold E. rewrite (EX_reg regs _ 8 8%bv eq_refl). exact R8.
      * (* lo is a low surrogate: the pair, then put_utf8 *)
        rewrite branch_ltu_U, !U_SOff, U_SLit, ?ew_ewset_other, E32, unsigned_lit_small in Hc by lia.
        apply Z.ltb_ge in Hc. unfold zcanon, M64 in Hc.
        pose proof (Z.div_mod (lo + -57344) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (lo + -57344) (2 ^ 64) ltac:(lia)).
        change (18446744073709550592 mod 2 ^ 64) with 18446744073709550592 in Hc.
        assert (Hl : 56320 <= lo <= 57343) by lia.
        assert (HL : PjGrammar.low [92; 117; tb_at D (r + 8); tb_at D (r + 9); tb_at D (r + 10); tb_at D (r + 11)] = Some lo).
        { rewrite Hlow. destruct (Z.leb_spec 56320 lo); destruct (Z.leb_spec lo 57343); cbn [andb]; [reflexivity | lia | lia | lia]. }
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + 1036).
        -- apply awr_ro. vm_compute. reflexivity.
        -- lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
             rewrite (u_reseat (w_H W) _ _ msN MD 1036 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
             rewrite u_cfg_pc;
             assert (HDEC1 : ps_at_decP B ARx SK P D ly S Hp W regs0 (ms_mem msN) MD out w r Q)
               by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs0 mem md out w r Q
                     (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                   [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
           end.
           pose proof (psd_pair_range cpv lo Hhi Hl) as Hpr.
           apply (ps_u_pu D ly S Hp W _ _ _ out w r Q (PjGrammar.pair_cp cpv lo) (r + 12) HPRE HAFTER).
           prreg HS (2%bv : bv 5) L2. prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4.
           prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9. prreg HS (18%bv : bv 5) L18.
           prreg HS (19%bv : bv 5) L19. prreg HS (20%bv : bv 5) L20. prreg HS (22%bv : bv 5) L22.
           prreg HS (23%bv : bv 5) L23. prreg HS (24%bv : bv 5) L24. prreg HS (26%bv : bv 5) L26.
           prreg HS (27%bv : bv 5) L27.
           pose proof (st_ok_pi_restrict_reg _ _ _ _ 21%bv HS) as L21.
           pose proof (st_ok_pi_restrict_reg _ _ _ _ 25%bv HS) as L25.
           change (sr_get _ 21%bv) with
             (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 21 0) (SLit 10)) (SLit (-56613888))) (SOff 32 0)) in L21.
           change (sr_get _ 25%bv) with (shx 9) in L25.
           rewrite (sv_pair _ cpv lo) in L21 by (try (rewrite ew_ewset_other by lia); first [exact E21 | exact E32 | lia]).
           rewrite (sv_shx _ 9 (pi_q D + 8)) in L25 by (try (rewrite ew_ewset_other by lia); first [exact E9 | exact E24 | lia]).
           unfold E in L3, L4, L8, L18, L23.
           rewrite (EX_reg regs _ 3 3%bv eq_refl) in L3. rewrite (EX_reg regs _ 4 4%bv eq_refl) in L4.
           rewrite (EX_reg regs _ 8 8%bv eq_refl) in L8. rewrite (EX_reg regs _ 18 18%bv eq_refl) in L18.
           rewrite (EX_reg regs _ 23 23%bv eq_refl) in L23.
           rewrite E20, unsigned_lit_small in L22 by lia.
           split; [exists regs0; exact HDEC1|].
           split; [lia|].
           split; [rewrite HR12; exact (psd_dec_pair _ _ _ _ _ _ _ _ _ _ _ cpv lo Hhex Hhi HL)|].
           split.
           { rewrite HR12. replace (r + 12 - r) with 12 by lia.
             exact (psd_scan_pair _ _ _ _ _ _ _ _ _ _ _ cpv lo Hhex HL). }
           split; [lia|]. split; [lia|].
           split; [split; [rewrite L24; exact E24 | split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]]|].
           split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
           split; [rewrite L26; reflexivity|]. split; [rewrite L27; reflexivity|].
           split; [rewrite L2; exact E2|]. split; [rewrite L18; exact R18|]. split; [rewrite L19; exact E19|].
           split; [rewrite L20; exact E20|]. split; [rewrite L8; exact R8|]. split; [rewrite L9; exact E9|].
           split; [exact L21 | exact L22].
  - (* ---- hex4 refused the digits: a0 = -1, the free path ---- *)
    set (E := EX regs []).
    assert (HEI : img_env VAL A_LIM E) by apply EX_env.
    assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (unfold E; rewrite (EX_reg regs _ 9 9%bv eq_refl); exact R9).
    assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (unfold E; rewrite (EX_reg regs _ 2 2%bv eq_refl); exact R2).
    assert (E19 : ew E 19 = Z_to_bv 64 w) by (unfold E; rewrite (EX_reg regs _ 19 19%bv eq_refl); exact R19).
    assert (E20 : ew E 20 = Z_to_bv 64 r) by (unfold E; rewrite (EX_reg regs _ 20 20%bv eq_refl); exact R20).
    assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF)
      by (unfold E; rewrite (EX_reg regs _ 24 24%bv eq_refl); exact (proj1 HSH)).
    assert (HS : st_ok_pi segs VAL E ss_ahn
      (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + 992))) mem (seg_rom segs)))).
    { rewrite restrict_mkst_fx. apply build_st_ok.
      - apply EX_regs_ok.
      - apply Forall_app. split.
        + apply (pins_pu_ok E regs (pi_q D)); [exact E9 | exact E24 | lia | exact (proj2 (proj2 HSH)) | exact K26 | exact K27].
        + apply Forall_cons; [cbn [fst snd]; exact HLO | apply Forall_nil].
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - exact I.
      - apply facts_ok_atoms. apply (atoms_f_base E (PS_SP D) (pi_q D) r w); try assumption; lia. }
    assert (SHOK : sh_ok segs dBx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
    assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None) by (apply HNlow; rewrite Hlow; reflexivity).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
    + apply awr_ro. vm_compute. reflexivity.
    + u_free_leaf W HS HJ HPM HPRE HDEC HN.
      * prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4. unfold E in L3, L4.
        rewrite (EX_reg regs _ 3 3%bv eq_refl) in L3. rewrite (EX_reg regs _ 4 4%bv eq_refl) in L4.
        split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)].
      * prreg HS (2%bv : bv 5) L2. rewrite L2. exact E2.
      * prreg HS (18%bv : bv 5) L18. rewrite L18. unfold E. rewrite (EX_reg regs _ 18 18%bv eq_refl). exact R18.
      * prreg HS (8%bv : bv 5) L8. rewrite L8. unfold E. rewrite (EX_reg regs _ 8 8%bv eq_refl). exact R8.
Qed.


(* the four registers a free leaf states, read off the leaf's state through the cut environment's register atoms *)
Ltac u_fregs1 HS RG HGT R2 R18 R8 :=
  lazymatch goal with
  | |- ps_gptp _ _ =>
      let L3 := fresh "L3" in let L4 := fresh "L4" in
      prreg HS (3%bv : bv 5) L3; prreg HS (4%bv : bv 5) L4;
      rewrite ?ew_ewset_other in L3 by lia; rewrite ?ew_ewset_other in L4 by lia;
      rewrite (RG 3%nat 3%bv eq_refl) in L3; rewrite (RG 4%nat 4%bv eq_refl) in L4;
      split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]
  | _ =>
      first
      [ let L := fresh "L" in prreg HS (2%bv : bv 5) L; rewrite ?ew_ewset_other in L by lia;
        rewrite (RG 2%nat 2%bv eq_refl) in L; exact (eq_trans L R2)
      | let L := fresh "L" in prreg HS (18%bv : bv 5) L; rewrite ?ew_ewset_other in L by lia;
        rewrite (RG 18%nat 18%bv eq_refl) in L; exact (eq_trans L R18)
      | let L := fresh "L" in prreg HS (8%bv : bv 5) L; rewrite ?ew_ewset_other in L by lia;
        rewrite (RG 8%nat 8%bv eq_refl) in L; exact (eq_trans L R8) ]
  end.
Ltac ewr := rewrite ?ew_ewset_other by lia.
Ltac ewrh H := rewrite ?ew_ewset_other in H by lia.

(* ---- the tail cut (offset 880): s5 holds the four digits' value ---- *)
Definition u_at_tail (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) (cpv : Z) : Prop :=
  u_mem D ly S Hp W mem md out w r Q /\
  tb_at D r = 92 /\ tb_at D (r + 1) = 117 /\ r + 6 <= pi_text D + pi_len D /\
  PjGrammar.hex4 (hexs D r) = Some cpv /\
  ps_sh_regs D regs /\ ps_gptp D regs /\ u_keep_regs regs /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 11 = w64 (pi_text D + pi_len D) /\
  getr regs 21 = w64 cpv.

Lemma ps_u_tail : forall D ly S Hp W regs mem md out w r Q cpv,
  ps_pre B ARx CTX CW D -> ps_dec_afterP B ARx SK P CW D r ->
  u_at_tail D ly S Hp W regs mem md out w r Q cpv ->
  SRr segs W (u_cfg 880 regs mem md) (ps_finP B ARx SK P CW D).
Proof.
  intros D ly S Hp W regs mem md out w r Q cpv HPRE HAFTER HAT.
  destruct HAT as ((regs0 & HDEC) & Hb0 & Hb1 & Hr6 & Hhex & HSH & HGT & HKR
    & R2 & R18 & R19 & R20 & R8 & R9 & R11 & R21).
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs0 mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0. pose proof (ps_head8 HW) as Hh8.
  pose proof ps_stk144 as Hs144.
  pose proof HPRE as (HF & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & _ & _ & HWIN & Hq1 & Hq2 & _).
  pose proof HF as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & Hsp64).
  pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & _ & _ & HCST & HIN & HROD & HSC & _).
  pose proof HAL as (Hcnt & Hout4 & Hout16 & EHp & Eab & HLED & HVIS & HRL & HRPOS & Hbb).
  destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V24 & V16 & V8).
  pose proof HSRC as (Hgb & _ & _ & _ & Hrat & _).
  pose proof (ajx_ly HJ) as Hly.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof (hex4_range (hexs D r) cpv eq_refl Hhex) as Hcp.
  assert (Htb : forall x, 0 <= tb_at D x < 256).
  { intros x. unfold tb_at. destruct (Nat.lt_ge_cases (Z.to_nat (x - pi_text D)) (length (pi_tb D))) as [Hl|Hl];
      [exact (garr8_bytes _ _ _ Hgb _ Hl) | rewrite nth_overflow by exact Hl; lia]. }
  pose proof (rest_u6 D r ltac:(lia) ltac:(rewrite Hlen; lia)) as HR6. rewrite Hb0, Hb1 in HR6.
  set (E := EK regs (pi_tb D) (pi_text D) r).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, EK; apply Eimg_env).
  assert (RG : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr regs x)
    by (intros n x Hn; unfold E; apply EK_reg; exact Hn).
  assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (rewrite (RG 2%nat 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = Z_to_bv 64 (pi_q D)) by (rewrite (RG 8%nat 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (rewrite (RG 9%nat 9%bv eq_refl); exact R9).
  assert (E11 : ew E 11 = Z_to_bv 64 (pi_text D + pi_len D)) by (rewrite (RG 11%nat 11%bv eq_refl); exact R11).
  assert (E19 : ew E 19 = Z_to_bv 64 w) by (rewrite (RG 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 r) by (rewrite (RG 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 cpv) by (rewrite (RG 21%nat 21%bv eq_refl); exact R21).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (RG 24%nat 24%bv eq_refl); exact (proj1 HSH)).
  assert (E38 : ew E 38 = Z_to_bv 64 (tb_at D (r + 6))) by (unfold E; exact (EK_byte regs _ _ r 6 ltac:(lia))).
  assert (E39 : ew E 39 = Z_to_bv 64 (tb_at D (r + 7))) by (unfold E; exact (EK_byte regs _ _ r 7 ltac:(lia))).
  assert (HS : st_ok_pi segs VAL E ss_tail
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + 880))) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. apply build_st_ok.
    - unfold E. apply regs_ok_EK.
    - apply (pins_keep_ok E regs (pi_q D)); [exact E9 | exact E24 | lia | exact (proj2 (proj2 HSH)) | exact HKR].
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. apply (rok_k E _ (PS_SP D) E2); [lia | lia | exact V8 | exact V16 | exact V24].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - apply facts_ok_atoms. apply atoms_ok_app; [|apply atoms_ok_app].
      + apply (atoms_f_base E (PS_SP D) (pi_q D) r w); try assumption; lia.
      + unfold E. apply atoms_ok_bytes. exact (garr8_bytes _ _ _ Hgb).
      + cbn [atoms_ok]. split; [|exact I].
        apply (afact_rng E 21 cpv); [exact E21 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok segs dBx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  pose proof HMN as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (BR := paj_branch (PI := PS_PAImg)).
  unfold u_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
  - apply awr_ro. vm_compute. reflexivity.
  - psrr_branch_tok RUN BR HS SHOK dBspan.
    + (* cp = 0: \u0000 is refused *)
      rewrite branch_eq_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E21, unsigned_lit_small, Z.add_0_r in Hc by lia.
      rewrite (zcanon_id cpv) in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. subst cpv.
      assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None)
        by (rewrite HR6; exact (psd_dec_u_zero _ _ _ _ _ Hhex)).
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
      * apply awr_ro. vm_compute. reflexivity.
      * u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
    + rewrite branch_eq_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E21, unsigned_lit_small, Z.add_0_r in Hc by lia.
      rewrite (zcanon_id cpv) in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
      rename Hc into Hc0.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
      * apply awr_ro. vm_compute. reflexivity.
      * psrr_branch_tok RUN BR HS SHOK dBspan.
        -- (* a high surrogate *)
           rewrite branch_eq_U, (U_mask _ cpv), U_SLit in Hc by (ewr; first [exact E21 | lia]).
           change (zcanon 55296) with 55296 in Hc. apply Z.eqb_eq in Hc. apply psd_mask_hi in Hc; [|lia].
           rename Hc into Hhi.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
           ++ apply awr_ro. vm_compute. reflexivity.
           ++ psrr_branch_tok RUN BR HS SHOK dBspan.
              ** (* fewer than six bytes after the digits: refused *)
                 rewrite branch_lt_Sg, (Sg_room _ (-6) (pi_text D + pi_len D) r), S_SLit in Hc
                   by (ewr; first [exact E11 | exact E20 | lia]).
                 change (bv_swrap 64 6) with 6 in Hc. apply Z.ltb_lt in Hc.
                 assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
                 { rewrite HR6. apply (psd_dec_hi_short _ _ _ _ _ cpv Hhex Hhi).
                   rewrite psd_rest_len by lia. lia. }
                 paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
              ** (* room for the second escape: the bytes at r + 6, r + 7 join the state *)
                 rewrite branch_lt_Sg, (Sg_room _ (-6) (pi_text D + pi_len D) r), S_SLit in Hc
                   by (ewr; first [exact E11 | exact E20 | lia]).
                 change (bv_swrap 64 6) with 6 in Hc. apply Z.ltb_ge in Hc.
                 rename Hc into Hroom.
                 pose proof (rest_u12 D r ltac:(lia) ltac:(rewrite Hlen; lia)) as HR12. rewrite Hb0, Hb1 in HR12.
                 lazymatch goal with HX : st_ok_pi _ _ ?E1 ?ss1 (restrict _ ?ms1) |- _ =>
                   assert (HMc : forall y : word, mrestrict (w_H W) (ms_mem ms1) y = mrestrict (w_H W) mem y) by u_memeq;
                   pose proof (bytes_at_keep W mem (ms_mem ms1) _ _ HMc Hgb) as Hgb1;
                   destruct (garr8_at _ _ _ (r + 6) Hgb1 ltac:(lia)) as [V6 _];
                   destruct (garr8_at _ _ _ (r + 7) Hgb1 ltac:(lia)) as [V7 _];
                   pose proof (add_t67 E1 ss1 _ r (tb_at D (r + 6)) (tb_at D (r + 7)) (PS_SP D) HX
                     ltac:(vm_compute; reflexivity)
                     ltac:(ewr; exact E20) ltac:(ewr; exact E38) ltac:(ewr; exact E39) ltac:(ewr; exact E2)
                     ltac:(lia) ltac:(lia) (Htb _) (Htb _) ltac:(lia) ltac:(lia) ltac:(lia) V6 V7) as HS7;
                   clear HX; rename HS7 into HS
                 end.
                 paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
                 --- cbn [ms_mem mkst].
                     apply (ob_txt (w_H W) mem _ _ _ _ (pi_text D) (Z.of_nat (length (pi_tb D))) (r + 6) 1);
                       [u_memeq | exact Hrat | | | lia | lia].
                     +++ unfold dBx. rewrite U_SOff. ewr. rewrite E24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
                         apply zcanon_id. unfold SHADOW_OFF, M64. lia.
                     +++ rewrite U_SOff. ewr. rewrite E20, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- psrr_branch_tok RUN BR HS SHOK dBspan.
                     +++ (* no backslash at r + 6: refused *)
                         rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E38, unsigned_lit_small, Z.add_0_r in Hc
                           by (pose proof (Htb (r + 6)); lia).
                         rewrite (zcanon_id (tb_at D (r + 6))) in Hc by (pose proof (Htb (r + 6)); unfold M64; lia).
                         change (zcanon 92) with 92 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
                         assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
                         { rewrite HR12. apply (psd_dec_hi_nolow _ _ _ _ _ _ _ _ _ _ _ cpv Hhex Hhi).
                           apply psd_low_nobs. exact Hc. }
                         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                         *** apply awr_ro. vm_compute. reflexivity.
                         *** u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
                     +++ rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E38, unsigned_lit_small, Z.add_0_r in Hc
                           by (pose proof (Htb (r + 6)); lia).
                         rewrite (zcanon_id (tb_at D (r + 6))) in Hc by (pose proof (Htb (r + 6)); unfold M64; lia).
                         change (zcanon 92) with 92 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb6.
                         paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
                         *** cbn [ms_mem mkst].
                             apply (ob_txt (w_H W) mem _ _ _ _ (pi_text D) (Z.of_nat (length (pi_tb D))) (r + 7) 1);
                               [u_memeq | exact Hrat | | | lia | lia].
                             ---- unfold dBx. rewrite U_SOff. ewr.
                                  rewrite E24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
                                  apply zcanon_id. unfold SHADOW_OFF, M64. lia.
                             ---- rewrite U_SOff. ewr. rewrite E20, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
                         *** apply awr_ro. vm_compute. reflexivity.
                         *** psrr_branch_tok RUN BR HS SHOK dBspan.
                             ---- (* no u at r + 7: refused *)
                                  rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                                  rewrite E39, unsigned_lit_small, Z.add_0_r in Hc by (pose proof (Htb (r + 7)); lia).
                                  rewrite (zcanon_id (tb_at D (r + 7))) in Hc by (pose proof (Htb (r + 7)); unfold M64; lia).
                                  change (zcanon 117) with 117 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
                                  assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
                                  { rewrite HR12, Hb6. apply (psd_dec_hi_nolow _ _ _ _ _ _ _ _ _ _ _ cpv Hhex Hhi).
                                    apply psd_low_nou. exact Hc. }
                                  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                                  ++++ apply awr_ro. vm_compute. reflexivity.
                                  ++++ u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
                             ---- rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                                  rewrite E39, unsigned_lit_small, Z.add_0_r in Hc by (pose proof (Htb (r + 7)); lia).
                                  rewrite (zcanon_id (tb_at D (r + 7))) in Hc by (pose proof (Htb (r + 7)); unfold M64; lia).
                                  change (zcanon 117) with 117 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb7.
                                  paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
                                  ++++ apply awr_ro. vm_compute. reflexivity.
                                  ++++ (* ---- `jal hex4` at 988: out = sp + 36, parse_string's OWN frame (the caller
                                          window e1 = 48); hex4 reads the four digits at r + 8 ---- *)
                                       assert (HB4096 : 4096 <= BASE) by (unfold Z.le; vm_compute; discriminate).
                                       assert (HBtop : BASE + 2 ^ 40 < 2 ^ 64) by (unfold Z.lt; vm_compute; reflexivity).
                                       assert (HSTKv : 160 <= STK_parse_string) by (unfold Z.le; vm_compute; discriminate).
                                       assert (HHXv : STK_hex4 = 16) by (vm_compute; reflexivity).
                                       assert (HSTKval : STK_parse_string = 16560) by (vm_compute; reflexivity).
                                       lazymatch goal with |- SRr _ _ {| cfg_ms := ?msC; cfg_model := ?MD |} _ =>
                                         assert (HMx : forall y : word, mrestrict (w_H W) (ms_mem msC) y = mrestrict (w_H W) mem y)
                                           by u_memeq;
                                         assert (HAVx : forall a, aview segs (w_H W) (ms_mem msC) a = aview segs (w_H W) mem a)
                                           by (intros a; apply aview_eq_of; apply HMx);
                                         assert (HDECx : ps_at_decP B ARx SK P D ly S Hp W regs0 (ms_mem msC) MD out w r Q)
                                           by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs0 mem md out w r Q
                                                 (ms_mem msC) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                                               [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                                       end.
                                       pose proof (ajx_ar HJ) as HARc. cbv beta in HARc.
                                       destruct (chain_now B ARx SK P LAWS HW CTX CW D ly S Hp W regs0 mem md out w r Q HPRE HDEC)
                                         as (ch & HCH).
                                       prreg HS (1%bv : bv 5) C1. prreg HS (2%bv : bv 5) C2. prreg HS (3%bv : bv 5) C3.
                                       prreg HS (4%bv : bv 5) C4. prreg HS (8%bv : bv 5) C8. prreg HS (9%bv : bv 5) C9.
                                       prreg HS (10%bv : bv 5) C10. prreg HS (11%bv : bv 5) C11.
                                       prreg HS (18%bv : bv 5) C18. prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20.
                                       prreg HS (21%bv : bv 5) C21. prreg HS (23%bv : bv 5) C23. prreg HS (24%bv : bv 5) C24.
                                       prreg HS (26%bv : bv 5) C26. prreg HS (27%bv : bv 5) C27.
                                       pose proof (st_ok_restrict_reg _ _ _ _ _ 25%bv HS) as C25.
                                       change (sr_get _ 25%bv) with (shx 9) in C25.
                                       rewrite (sv_shx _ 9 (pi_q D + 8)) in C25 by (ewr; first [exact E9 | exact E24 | lia]).
                                       rewrite ?ew_ewset_other in C2, C3, C4, C8, C9, C18, C19, C20, C21, C23, C24 by lia.
                                       rewrite ?ew_ewset_other in C10, C11 by lia.
                                       rewrite E2 in C2. rewrite E8 in C8. rewrite E9 in C9. rewrite E19 in C19.
                                       rewrite E20 in C20, C10. rewrite E21 in C21. rewrite E24 in C24. rewrite E2 in C11.
                                       rewrite unsigned_lit_small in C10 by lia. rewrite unsigned_lit_small in C11 by lia.
                                       rewrite (RG 3%nat 3%bv eq_refl) in C3. rewrite (RG 4%nat 4%bv eq_refl) in C4.
                                       rewrite (RG 18%nat 18%bv eq_refl) in C18. rewrite (RG 23%nat 23%bv eq_refl) in C23.
                                       eapply SRr_bind.
                                       { eapply (YCbqGcallW.aj_call_xW_sp (SK := SK) segs B prh_pst ARx LAWS
                                           (@pa_segs_low _ _ PS_PAImg)) with
                                           (STK1 := STK_hex4) (e1 := 48)
                                           (FP1 := [(PS_SP D + 36, PS_SP D + 36 + 4)]) (o := PS_SP D - PS_WSP D) (ch1 := ch).
                                         - exact HS.
                                         - vm_compute. reflexivity.
                                         - exact HJ.
                                         - unfold spZ. rewrite C2, unsigned_lit_small by lia. lia.
                                         - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & He16 & _ & _).
                                           replace (spZ (pi_regs D) - 144 - (spZ (pi_regs D) + pi_e D)) with (- (144 + pi_e D)) by lia.
                                           rewrite Z.mod_opp_l_z; [reflexivity | lia |].
                                           rewrite <- Zplus_mod_idemp_r, He16. reflexivity.
                                         - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & _ & _ & _). lia.
                                         - rewrite HHXv. lia.
                                         - unfold PS_WSP, PS_WSTK, PS_SP. rewrite ps_frame144, HHXv, HSTKval.
                                           destruct HWIN as (He0 & _ & _ & _). lia.
                                         - lia.
                                         - reflexivity.
                                         - unfold PS_WSP, PS_SP. rewrite ps_frame144. destruct HWIN as (He0 & _ & _ & _). lia.
                                         - rewrite C3, (proj1 HGT). exact Hgp0.
                                         - rewrite C4, (proj2 HGT). exact Htp0.
                                         - exact C1.
                                         - apply (ret_ok_codeptr_v 26444); [lia | reflexivity].
                                         - rewrite unsigned_lit_small by lia. lia.
                                         - unfold s0Z. rewrite C8, unsigned_lit_small by lia.
                                           replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) by lia.
                                           exact (achain_rd ly _ _ _ _ ch HAVx HCH).
                                         - (* hex4's text *)
                                           intros HPRE1 HWIN1.
                                           refine (HHEX4 ly S Hp W _ _ _ ch 48 (r + 8) (PS_SP D + 36) (lows D r)
                                             ((out, Z.of_nat Q + 1) :: pi_Lam D)
                                             (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1)))
                                             (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) _ C10 C11 eq_refl _ HWIN1
                                             ltac:(unfold spZ; rewrite C2, unsigned_lit_small by lia; lia)
                                             ltac:(unfold spZ; rewrite C2, unsigned_lit_small by lia; lia) _ _ _).
                                           + (* fpre *)
                                             split; [exact HPRE1|]. split.
                                             * intros a Hro Hno Her. rewrite (HAVx a). exact (HROD a Hro Hno Her).
                                             * split.
                                               -- unfold spZ. rewrite C2, unsigned_lit_small by lia. rewrite Eshi. lia.
                                               -- split.
                                                  ++ (* the return pc: the slot after `jal hex4` (988), PS_OFF + 992 *)
                                                     unfold raZ. rewrite C1, unsigned_lit_small by lia.
                                                     apply (PRW_StepKit.pa_slot_lt_ceil_b (PL := PS_PAListing) (PI := PS_PAImg) 26444);
                                                       [lia | vm_compute; reflexivity].
                                                  ++ (* FRM0-ENTRY: the section's rounding mode, from the entry's fpre *)
                                                     exact (ps_frm0 _ _ _ _ _ HPRE).
                                           + (* the four digits at r + 8 are a source window *)
                                             apply (src_rd4 W _ D (r + 8) (lows D r));
                                               [ apply (src_rd_keep W mem); [exact HMx | exact HSRC]
                                               | lia | rewrite Hlen; lia | reflexivity | ].
                                             intros j Hj.
                                             destruct j as [|[|[|[|j]]]]; cbn [nth lows]; try (exfalso; lia);
                                               f_equal; lia.
                                           + (* sp + 36 is 4-aligned *)
                                             pose proof Hsp16. lia.
                                           + (* the slot's shadow: the machine stack reads zero *)
                                             apply (ra_stack (aview segs (w_H W) _) (PS_SP D + 36) 4).
                                             intros a Ha.
                                             apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W _ _ a HARc).
                                             pose proof Hslo as Hs. rewrite HSTKval in Hs. rewrite Eslo, Eshi. lia.
                                           + (* the ledger at the call memory *)
                                             apply (ledger_keep B ly S Hp W mem _ _ _ _ _ _ _ _ HLED);
                                               [intros a _; apply HAVx | intros a kk i _ _; apply HAVx].
                                         - (* hex4's footprint: its out slot of parse_string's own frame *)
                                           intros a (rg & [<-|[]] & Hrg). cbn [fst snd] in Hrg. right; right; right.
                                           unfold PS_WSTK, PS_WSP. unfold PS_SP in Hrg. rewrite ps_frame144 in Hrg.
                                           rewrite HSTKval. destruct HWIN as (He0 & _ & _ & _). lia. }
                                       cbv beta.
                                       intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HXc & HPres2 & HQc).
                                       (* the text's m-form post: the body Q0 and the memnorm keep, by PCALL into P *)
                                       destruct HQc as (HQc & HMNc).
                                       destruct HQc as (HRL2 & EHp2 & ES2 & EAB2 & HLED2 & HHX). subst S2. subst Hp2.
                                       assert (HMN2 : P mem2) by exact (PCALL _ mem2 HMNc HPM).
                                       replace (PS_WSP D + (PS_SP D - PS_WSP D)) with (PS_SP D) in HJc, HXc by lia.
                                       assert (HDEC2 : ps_at_decP B ARx SK P D ly2 S Hp W2 regs0 mem2 md2 out w r Q).
                                       { lazymatch type of HDECx with ps_at_decP _ _ _ _ _ _ _ _ _ _ ?memC ?mdC _ _ _ _ =>
                                           apply (dec_call B ARx SK P LAWS HW ZSA IMGV CTX CW D ly S Hp W regs0 memC mdC
                                             out w r Q STK_hex4 48 [(PS_SP D + 36, PS_SP D + 36 + 4)] ly2 W2 mem2 md2 _ _
                                             HPRE HDECx HJ2 HJc HXc) end;
                                         [ lia | rewrite HHXv; lia | rewrite HHXv, HSTKval; lia
                                         | intros a (rg & [<-|[]] & Hrg); cbn [fst snd] in Hrg; left; lia
                                         | exact EAB2 | exact HLED2 | exact HMN2 ]. }
                                       pose proof (pres_reg _ _ 2 2%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P2.
                                       pose proof (pres_reg _ _ 3 3%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P3.
                                       pose proof (pres_reg _ _ 4 4%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P4.
                                       pose proof (pres_reg _ _ 8 8%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P8.
                                       pose proof (pres_reg _ _ 9 9%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P9.
                                       pose proof (pres_reg _ _ 18 18%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P18.
                                       pose proof (pres_reg _ _ 19 19%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P19.
                                       pose proof (pres_reg _ _ 20 20%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P20.
                                       pose proof (pres_reg _ _ 21 21%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P21.
                                       pose proof (pres_reg _ _ 23 23%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P23.
                                       pose proof (pres_reg _ _ 24 24%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P24.
                                       pose proof (pres_reg _ _ 25 25%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P25.
                                       pose proof (pres_reg _ _ 26 26%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P26.
                                       pose proof (pres_reg _ _ 27 27%bv HPres2 ltac:(unfold acallee_saved; lia)
                                         ltac:(apply bv_eq; vm_compute; reflexivity)) as P27.
                                       change (SRr segs W2 (u_cfg 992 regs2 mem2 md2) (ps_finP B ARx SK P CW D)).
                                       apply (ps_u_ah D ly2 S Hp W2 regs2 mem2 md2 out w r Q cpv HPRE HAFTER).
                                       split; [exists regs0; exact HDEC2|].
                                       split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|].
                                       split; [exact Hhex|]. split; [exact Hhi|]. split; [exact Hb6|]. split; [exact Hb7|].
                                       split; [destruct (PjGrammar.hex4 (lows D r)); [exact HHX | exact (proj1 HHX)]|].
                                       split; [split; [rewrite P24, C24; reflexivity
                                                      | split; [rewrite P23, C23; exact (proj1 (proj2 HSH))
                                                               | rewrite P25, C25; reflexivity]]|].
                                       split; [split; [rewrite P3, C3; exact (proj1 HGT) | rewrite P4, C4; exact (proj2 HGT)]|].
                                       split; [rewrite P26; exact C26|].
                                       split; [rewrite P27; exact C27|].
                                       split; [rewrite P2, C2; reflexivity|].
                                       split; [rewrite P18, C18; exact R18|].
                                       split; [rewrite P19, C19; reflexivity|].
                                       split; [rewrite P20, C20; reflexivity|].
                                       split; [rewrite P8, C8; reflexivity|].
                                       split; [rewrite P9, C9; reflexivity | rewrite P21, C21; reflexivity].
        -- (* not a high surrogate *)
           rewrite branch_eq_U, (U_mask _ cpv), U_SLit in Hc by (ewr; first [exact E21 | lia]).
           change (zcanon 55296) with 55296 in Hc. apply Z.eqb_neq in Hc.
           assert (Hnhi : ~ (55296 <= cpv < 56320)) by (intros Hx; apply Hc; apply psd_mask_hi; [lia | exact Hx]).
           clear Hc.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
           ++ apply awr_ro. vm_compute. reflexivity.
           ++ psrr_branch_tok RUN BR HS SHOK dBspan.
              ** (* a lone low surrogate: refused *)
                 rewrite branch_eq_U, (U_mask _ cpv), U_SLit in Hc by (ewr; first [exact E21 | lia]).
                 change (zcanon 56320) with 56320 in Hc. apply Z.eqb_eq in Hc. apply psd_mask_lo in Hc; [|lia].
                 assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None)
                   by (rewrite HR6; exact (psd_dec_u_lone_low _ _ _ _ _ cpv Hhex Hc)).
                 paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
              ** (* a code point of the basic plane: put_utf8 *)
                 rewrite branch_eq_U, (U_mask _ cpv), U_SLit in Hc by (ewr; first [exact E21 | lia]).
                 change (zcanon 56320) with 56320 in Hc. apply Z.eqb_neq in Hc.
                 assert (Hnlo : ~ (56320 <= cpv < 57344)) by (intros Hx; apply Hc; apply psd_mask_lo; [lia | exact Hx]).
                 paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + 1036).
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                       rewrite (u_reseat (w_H W) _ _ msN MD 1036 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
                       rewrite u_cfg_pc;
                       assert (HDEC1 : ps_at_decP B ARx SK P D ly S Hp W regs0 (ms_mem msN) MD out w r Q)
                         by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs0 mem md out w r Q
                               (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                             [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                     end.
                     apply (ps_u_pu D ly S Hp W _ _ _ out w r Q cpv (r + 6) HPRE HAFTER).
                     prreg HS (2%bv : bv 5) L2. prreg HS (3%bv : bv 5) L3. prreg HS (4%bv : bv 5) L4.
                     prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9. prreg HS (18%bv : bv 5) L18.
                     prreg HS (19%bv : bv 5) L19. prreg HS (20%bv : bv 5) L20. prreg HS (21%bv : bv 5) L21.
                     prreg HS (22%bv : bv 5) L22. prreg HS (23%bv : bv 5) L23. prreg HS (24%bv : bv 5) L24.
                     prreg HS (26%bv : bv 5) L26. prreg HS (27%bv : bv 5) L27.
                     pose proof (st_ok_pi_restrict_reg _ _ _ _ 25%bv HS) as L25.
                     change (sr_get _ 25%bv) with (shx 9) in L25.
                     rewrite (sv_shx _ 9 (pi_q D + 8)) in L25 by (ewr; first [exact E9 | exact E24 | lia]).
                     rewrite (RG 3%nat 3%bv eq_refl) in L3. rewrite (RG 4%nat 4%bv eq_refl) in L4.
                     rewrite (RG 23%nat 23%bv eq_refl) in L23.
                     rewrite E20, unsigned_lit_small in L22 by lia.
                     split; [exists regs0; exact HDEC1|].
                     split; [lia|].
                     split; [rewrite HR6; exact (psd_dec_u_bmp _ _ _ _ _ cpv Hhex Hc0 ltac:(lia))|].
                     split; [rewrite HR6; replace (r + 6 - r) with 6 by lia; exact (psd_scan_u _ _ _ _ _ cpv Hhex)|].
                     split; [lia|]. split; [lia|].
                     split; [split; [rewrite L24; exact E24 | split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]]|].
                     split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                     split; [rewrite L26; reflexivity|]. split; [rewrite L27; reflexivity|].
                     split; [rewrite L2; exact E2|]. split; [rewrite L18, (RG 18%nat 18%bv eq_refl); exact R18|].
                     split; [rewrite L19; exact E19|]. split; [rewrite L20; exact E20|].
                     split; [rewrite L8; exact E8|]. split; [rewrite L9; exact E9|].
                     split; [rewrite L21; exact E21 | exact L22].
Qed.


(* ---- the four-hex-digit loop at PS_HEX (452..551): i digits read, s5 their value ---- *)
Definition u_at_hex (D : ps_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (out w r : Z) (Q : nat) (i : nat) (acc : Z) : Prop :=
  u_mem D ly S Hp W mem md out w r Q /\
  tb_at D r = 92 /\ tb_at D (r + 1) = 117 /\ r + 6 <= pi_text D + pi_len D /\
  (i <= 3)%nat /\ psd_acc (firstn i (hexs D r)) = Some acc /\ 0 <= acc < 16 ^ Z.of_nat i /\
  ps_sh_regs D regs /\ ps_gptp D regs /\ u_keep_regs regs /\
  getr regs 2 = w64 (PS_SP D) /\ getr regs 18 = w64 out /\ getr regs 19 = w64 w /\ getr regs 20 = w64 r /\
  getr regs 8 = w64 (pi_q D) /\ getr regs 9 = w64 (pi_q D + 8) /\ getr regs 11 = w64 (pi_text D + pi_len D) /\
  getr regs 21 = w64 acc /\ getr regs 12 = w64 (4 - Z.of_nat i) /\
  getr regs 10 = w64 (r + 2 + Z.of_nat i) /\ getr regs 22 = w64 (r + 2 + Z.of_nat i).

(* the registers the loop's two leaves state, read off the leaf's state *)
Ltac u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc c :=
  let L1 := fresh "L1" in let L2 := fresh "L2" in let L3 := fresh "L3" in let L4 := fresh "L4" in
  let L5 := fresh "L5" in let L6 := fresh "L6" in let L7 := fresh "L7" in let L8 := fresh "L8" in
  let L9 := fresh "L9" in let L10 := fresh "L10" in let L11 := fresh "L11" in let L12 := fresh "L12" in
  let L16 := fresh "L16" in let L17 := fresh "L17" in let L18 := fresh "L18" in let L19 := fresh "L19" in
  let L20 := fresh "L20" in let L21 := fresh "L21" in let L22 := fresh "L22" in let L23 := fresh "L23" in
  let L24 := fresh "L24" in let L25 := fresh "L25" in let L26 := fresh "L26" in let L27 := fresh "L27" in
  let L28 := fresh "L28" in let L29 := fresh "L29" in let L30 := fresh "L30" in let L31 := fresh "L31" in
  prreg HS (1%bv : bv 5) L1; prreg HS (2%bv : bv 5) L2; prreg HS (3%bv : bv 5) L3; prreg HS (4%bv : bv 5) L4;
  prreg HS (5%bv : bv 5) L5; prreg HS (6%bv : bv 5) L6; prreg HS (7%bv : bv 5) L7; prreg HS (8%bv : bv 5) L8;
  prreg HS (9%bv : bv 5) L9; prreg HS (10%bv : bv 5) L10; prreg HS (11%bv : bv 5) L11;
  prreg HS (12%bv : bv 5) L12; prreg HS (16%bv : bv 5) L16; prreg HS (17%bv : bv 5) L17;
  prreg HS (18%bv : bv 5) L18; prreg HS (19%bv : bv 5) L19; prreg HS (20%bv : bv 5) L20;
  prreg HS (22%bv : bv 5) L22; prreg HS (23%bv : bv 5) L23; prreg HS (24%bv : bv 5) L24;
  prreg HS (26%bv : bv 5) L26; prreg HS (27%bv : bv 5) L27; prreg HS (28%bv : bv 5) L28;
  prreg HS (29%bv : bv 5) L29; prreg HS (30%bv : bv 5) L30; prreg HS (31%bv : bv 5) L31;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 21%bv HS) as L21;
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 25%bv HS) as L25;
  change (sr_get _ 21%bv) with (SAlu ALU_OR (SOff 32 c) (SAlu ALU_SLL (SOff 21 0) (SLit 4))) in L21;
  change (sr_get _ 25%bv) with (shx 9) in L25;
  rewrite (sv_hexacc _ c (tb_at D (r + 2 + Z.of_nat i)) acc) in L21
    by (ewr; first [exact E32 | exact E21 | pose proof (Htb (r + 2 + Z.of_nat i)); lia]);
  rewrite (sv_shx _ 9 (pi_q D + 8)) in L25 by (ewr; first [exact E9 | exact E24 | lia]);
  rewrite ?ew_ewset_other in L2, L3, L4, L8, L9, L10, L11, L12, L18, L19, L20, L22, L23, L24 by lia;
  rewrite E2 in L2; rewrite E8 in L8; rewrite E9 in L9; rewrite E11 in L11; rewrite E12 in L12;
  rewrite E19 in L19; rewrite E20 in L20; rewrite E22 in L10, L22; rewrite E24 in L24;
  rewrite (RG 3%nat 3%bv eq_refl) in L3; rewrite (RG 4%nat 4%bv eq_refl) in L4;
  rewrite (RG 18%nat 18%bv eq_refl) in L18; rewrite (RG 23%nat 23%bv eq_refl) in L23;
  rewrite !unsigned_lit_small in L10, L12, L22 by lia.

Lemma ps_u_hex : forall n D ly St Hp W regs mem md out w r Q i acc,
  (4 - i <= n)%nat -> ps_pre B ARx CTX CW D -> ps_dec_afterP B ARx SK P CW D r ->
  u_at_hex D ly St Hp W regs mem md out w r Q i acc ->
  SRr segs W (u_cfg PS_HEX regs mem md) (ps_finP B ARx SK P CW D).
Proof.
  induction n as [|n IH]; intros D ly St Hp W regs mem md out w r Q i acc Hn HPRE HAFTER HAT.
  { exfalso. destruct HAT as (_ & _ & _ & _ & Hi & _). lia. }
  destruct HAT as ((regs0 & HDEC) & Hb0 & Hb1 & Hr6 & Hi & Hacc & Haccr & HSH & HGT & HKR
    & R2 & R18 & R19 & R20 & R8 & R9 & R11 & R21 & R12 & R10 & R22).
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly St Hp W regs0 mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0. pose proof (ps_head8 HW) as Hh8.
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & _ & _ & HCST & HIN & HROD & HSC & _).
  pose proof HSRC as (Hgb & _ & _ & _ & Hrat & _).
  assert (Htb : forall x, 0 <= tb_at D x < 256).
  { intros x. unfold tb_at. destruct (Nat.lt_ge_cases (Z.to_nat (x - pi_text D)) (length (pi_tb D))) as [Hl|Hl];
      [exact (garr8_bytes _ _ _ Hgb _ Hl) | rewrite nth_overflow by exact Hl; lia]. }
  assert (Hacc4 : 0 <= acc < 4096) by (pose proof (Z.pow_le_mono_r 16 (Z.of_nat i) 3 ltac:(lia) ltac:(lia)); cbn in *; lia).
  destruct (garr8_at _ (pi_text D) (pi_tb D) (r + 2 + Z.of_nat i) Hgb ltac:(rewrite Hlen; lia)) as [Vb _].
  set (E := EX regs [w64 (tb_at D (r + 2 + Z.of_nat i))]).
  assert (HEI : img_env VAL A_LIM E) by apply EX_env.
  assert (RG : forall n0 (x : bv 5), Z.of_nat n0 = bv_unsigned x -> ew E n0 = getr regs x)
    by (intros n0 x Hx; unfold E; apply EX_reg; exact Hx).
  assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (rewrite (RG 2%nat 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = Z_to_bv 64 (pi_q D)) by (rewrite (RG 8%nat 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (rewrite (RG 9%nat 9%bv eq_refl); exact R9).
  assert (E11 : ew E 11 = Z_to_bv 64 (pi_text D + pi_len D)) by (rewrite (RG 11%nat 11%bv eq_refl); exact R11).
  assert (E12 : ew E 12 = Z_to_bv 64 (4 - Z.of_nat i)) by (rewrite (RG 12%nat 12%bv eq_refl); exact R12).
  assert (E19 : ew E 19 = Z_to_bv 64 w) by (rewrite (RG 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 r) by (rewrite (RG 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 acc) by (rewrite (RG 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (r + 2 + Z.of_nat i)) by (rewrite (RG 22%nat 22%bv eq_refl); exact R22).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (RG 24%nat 24%bv eq_refl); exact (proj1 HSH)).
  assert (E32 : ew E 32 = Z_to_bv 64 (tb_at D (r + 2 + Z.of_nat i)))
    by (unfold E; exact (EX_extra regs _ 0 ltac:(unfold A_TEXT; lia))).
  assert (HS : st_ok_pi segs VAL E ss_hex
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + PS_HEX))) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. apply build_st_ok.
    - apply EX_regs_ok.
    - apply Forall_app. split.
      + apply (pins_keep_ok E regs (pi_q D)); [exact E9 | exact E24 | lia | exact (proj2 (proj2 HSH)) | exact HKR].
      + apply Forall_cons; [cbn [fst snd]; rewrite R10, sv_atom0; symmetry; exact E22 | apply Forall_nil].
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, rg_h.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E (rdW W mem) (r + 2 + Z.of_nat i) 0 1 (SOff 32 0) (tb_at D (r + 2 + Z.of_nat i)));
        [ apply bv_eq; rewrite denot_SOff, E32, Z.add_0_r, !unsigned_lit_small
            by (pose proof (Htb (r + 2 + Z.of_nat i)); lia);
          apply zcanon_id; unfold M64; pose proof (Htb (r + 2 + Z.of_nat i)); lia
        | cbn; pose proof (Htb (r + 2 + Z.of_nat i)); lia | cbn; lia
        | rewrite Z.add_0_r; exact Vb ].
    - cbn [pairwise_disjoint all_disjoint]. split; exact I.
    - apply facts_ok_atoms. apply atoms_ok_app.
      + apply (atoms_f_base E (PS_SP D) (pi_q D) r w); try assumption; lia.
      + cbn [atoms_ok]. split; [|split; [|split; [|split; [|exact I]]]].
        * apply (afact_rng E 22 (r + 2 + Z.of_nat i));
            [exact E22 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
        * apply (afact_rng E 12 (4 - Z.of_nat i));
            [exact E12 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
        * apply (afact_rng E 21 acc); [exact E21 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
        * apply (afact_byte E 32 (tb_at D (r + 2 + Z.of_nat i))); [exact E32 | exact (Htb _)]. }
  assert (SHOK : sh_ok segs dBx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  pose proof HMN as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (BR := paj_branch (PI := PS_PAImg)).
  unfold u_cfg.
  (* the digit's class: decimal, lower, upper, or none *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
  - cbn [ms_mem mkst].
    apply (ob_txt (w_H W) mem _ _ _ _ (pi_text D) (Z.of_nat (length (pi_tb D))) (r + 2 + Z.of_nat i) 1);
      [u_memeq | exact Hrat | | | lia | rewrite Hlen; lia].
    + unfold dBx. rewrite U_SOff. ewr. rewrite E24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    + rewrite U_SOff. ewr. rewrite E22, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
  - apply awr_ro. vm_compute. reflexivity.
  - psrr_branch_tok RUN BR HS SHOK dBspan.
    + (* not a decimal digit *)
      rewrite branch_geu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
        by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
      change (zcanon 10) with 10 in Hc.
      rewrite (zc_lt (tb_at D (r + 2 + Z.of_nat i)) (-48) 10) in Hc
        by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
      apply negb_true_iff, andb_false_iff in Hc.
      assert (Hnd : ~ (0 <= tb_at D (r + 2 + Z.of_nat i) - 48 < 10)).
      { intros Hx. destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia. }
      clear Hc.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
      * apply awr_ro. vm_compute. reflexivity.
      * psrr_branch_tok RUN BR HS SHOK dBspan.
        -- (* not a lowercase digit *)
           rewrite branch_geu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
             by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
           change (zcanon 6) with 6 in Hc.
           rewrite (zc_lt (tb_at D (r + 2 + Z.of_nat i)) (-97) 6) in Hc
             by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
           apply negb_true_iff, andb_false_iff in Hc.
           assert (Hnl : ~ (0 <= tb_at D (r + 2 + Z.of_nat i) - 97 < 6)).
           { intros Hx. destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia. }
           clear Hc.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
           ++ apply awr_ro. vm_compute. reflexivity.
           ++ psrr_branch_tok RUN BR HS SHOK dBspan.
              ** (* not an uppercase digit either: the escape is refused *)
                 rewrite branch_ltu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
                   by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
                 change (zcanon 5) with 5 in Hc.
                 rewrite (zc_lt_l (tb_at D (r + 2 + Z.of_nat i)) (-65) 5) in Hc
                   by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
                 apply negb_true_iff, andb_false_iff in Hc.
                 assert (Hnu : ~ (0 <= tb_at D (r + 2 + Z.of_nat i) - 65 <= 5)).
                 { intros Hx. destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.leb_gt in Hc]; lia. }
                 assert (Hhv : PjGrammar.hexval (tb_at D (r + 2 + Z.of_nat i)) = None)
                   by (apply psd_hexval_none; [exact (Htb _) | exact Hnd | exact Hnl | exact Hnu]).
                 assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
                 { assert (Hh4 : PjGrammar.hex4 (hexs D r) = None).
                   { unfold hexs. rewrite <- psd_acc_hex4.
                     change [tb_at D (r + 2); tb_at D (r + 3); tb_at D (r + 4); tb_at D (r + 5)] with (hexs D r).
                     replace (hexs D r) with (firstn (S i) (hexs D r) ++ skipn (S i) (hexs D r))
                       by (apply firstn_skipn).
                     apply psu_acc_none_app.
                     rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                     rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                   rewrite (rest_u6 D r ltac:(lia) ltac:(rewrite Hlen; lia)), Hb0, Hb1.
                   exact (psd_dec_u_nohex _ _ _ _ _ Hh4). }
                 paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- u_free_leaf W HS HJ HPM HPRE HDEC HN; u_fregs1 HS RG HGT R2 R18 R8.
              ** (* an uppercase digit: b - 55 *)
                 rewrite branch_ltu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
                   by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
                 change (zcanon 5) with 5 in Hc.
                 rewrite (zc_lt_l (tb_at D (r + 2 + Z.of_nat i)) (-65) 5) in Hc
                   by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
                 apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
                 apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
                 assert (Hhv : PjGrammar.hexval (tb_at D (r + 2 + Z.of_nat i)) =
                   Some (tb_at D (r + 2 + Z.of_nat i) + (-55)))
                   by (replace (tb_at D (r + 2 + Z.of_nat i) + (-55)) with (tb_at D (r + 2 + Z.of_nat i) - 55) by lia;
                       apply psd_hexval_up; [exact (Htb _) | exact Hnd | exact Hnl | lia]).
                 paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
                 --- apply awr_ro. vm_compute. reflexivity.
                 --- psrr_branch_tok RUN BR HS SHOK dBspan.
                     +++ (* another digit: the back edge to PS_HEX *)
                         rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                         rewrite E12, unsigned_lit_small in Hc by lia.
                         rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
                         change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
                         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_HEX).
                         *** apply awr_ro. vm_compute. reflexivity.
                         *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                               rewrite (u_reseat (w_H W) _ _ msN MD PS_HEX HS ltac:(vm_compute; reflexivity)
                                         ltac:(vm_compute; reflexivity));
                               rewrite u_cfg_pc;
                               assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                                 by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                                       (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                                     [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                             end.
                             apply (IH D ly St Hp W _ _ _ out w r Q (S i)
                                      (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-55)))); [lia | exact HPRE | exact HAFTER|].
                             u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-55).
                             split; [exists regs0; exact HDEC1|].
                             split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|]. split; [lia|].
                             split.
                             { rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                               rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                             split.
                             { pose proof (Htb (r + 2 + Z.of_nat i)).
                               assert (Hp16 : 16 ^ Z.of_nat (S i) = 16 * 16 ^ Z.of_nat i)
                                 by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
                               lia. }
                             split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                             split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                             split; [repeat split; assumption|].
                             split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                             split; [exact L8|]. split; [exact L9|]. split; [exact L11|]. split; [exact L21|].
                             split; [rewrite L12; f_equal; lia|].
                             split; [rewrite L10; f_equal; lia | rewrite L22; f_equal; lia].
                     +++ (* the fourth digit is read: the tail at 880 *)
                         rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                         rewrite E12, unsigned_lit_small in Hc by lia.
                         rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
                         change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
                         assert (Hi3 : i = 3%nat) by lia.
                         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + 880).
                         *** apply awr_ro. vm_compute. reflexivity.
                         *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                               rewrite (u_reseat (w_H W) _ _ msN MD 880 HS ltac:(vm_compute; reflexivity)
                                         ltac:(vm_compute; reflexivity));
                               rewrite u_cfg_pc;
                               assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                                 by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                                       (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                                     [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                             end.
                             apply (ps_u_tail D ly St Hp W _ _ _ out w r Q
                                      (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-55))) HPRE HAFTER).
                             u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-55).
                             split; [exists regs0; exact HDEC1|].
                             split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|].
                             split.
                             { unfold hexs. rewrite <- psd_acc_hex4.
                               change [tb_at D (r + 2); tb_at D (r + 3); tb_at D (r + 4); tb_at D (r + 5)] with (hexs D r).
                               rewrite <- (firstn_all (hexs D r)).
                               replace (length (hexs D r)) with (S i) by (subst i; reflexivity).
                               rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                               rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                             split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                             split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                             split; [repeat split; assumption|].
                             split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                             split; [exact L8|]. split; [exact L9|]. split; [exact L11 | exact L21].
        -- (* a lowercase digit: b - 87 *)
           rewrite branch_geu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
             by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
           change (zcanon 6) with 6 in Hc.
           rewrite (zc_lt (tb_at D (r + 2 + Z.of_nat i)) (-97) 6) in Hc
             by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
           apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
           apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
           assert (Hhv : PjGrammar.hexval (tb_at D (r + 2 + Z.of_nat i)) =
             Some (tb_at D (r + 2 + Z.of_nat i) + (-87)))
             by (replace (tb_at D (r + 2 + Z.of_nat i) + (-87)) with (tb_at D (r + 2 + Z.of_nat i) - 87) by lia;
                 apply psd_hexval_low; [exact (Htb _) | exact Hnd | lia]).
                 paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
           --- apply awr_ro. vm_compute. reflexivity.
           --- psrr_branch_tok RUN BR HS SHOK dBspan.
               +++ (* another digit: the back edge to PS_HEX *)
                   rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                   rewrite E12, unsigned_lit_small in Hc by lia.
                   rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
                   change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
                   paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_HEX).
                   *** apply awr_ro. vm_compute. reflexivity.
                   *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                         rewrite (u_reseat (w_H W) _ _ msN MD PS_HEX HS ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity));
                         rewrite u_cfg_pc;
                         assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                           by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                                 (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                               [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                       end.
                       apply (IH D ly St Hp W _ _ _ out w r Q (S i)
                                (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-87)))); [lia | exact HPRE | exact HAFTER|].
                       u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-87).
                       split; [exists regs0; exact HDEC1|].
                       split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|]. split; [lia|].
                       split.
                       { rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                         rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                       split.
                       { pose proof (Htb (r + 2 + Z.of_nat i)).
                         assert (Hp16 : 16 ^ Z.of_nat (S i) = 16 * 16 ^ Z.of_nat i)
                           by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
                         lia. }
                       split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                       split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                       split; [repeat split; assumption|].
                       split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                       split; [exact L8|]. split; [exact L9|]. split; [exact L11|]. split; [exact L21|].
                       split; [rewrite L12; f_equal; lia|].
                       split; [rewrite L10; f_equal; lia | rewrite L22; f_equal; lia].
               +++ (* the fourth digit is read: the tail at 880 *)
                   rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                   rewrite E12, unsigned_lit_small in Hc by lia.
                   rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
                   change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
                   assert (Hi3 : i = 3%nat) by lia.
                   paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + 880).
                   *** apply awr_ro. vm_compute. reflexivity.
                   *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                         rewrite (u_reseat (w_H W) _ _ msN MD 880 HS ltac:(vm_compute; reflexivity)
                                   ltac:(vm_compute; reflexivity));
                         rewrite u_cfg_pc;
                         assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                           by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                                 (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                               [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                       end.
                       apply (ps_u_tail D ly St Hp W _ _ _ out w r Q
                                (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-87))) HPRE HAFTER).
                       u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-87).
                       split; [exists regs0; exact HDEC1|].
                       split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|].
                       split.
                       { unfold hexs. rewrite <- psd_acc_hex4.
                         change [tb_at D (r + 2); tb_at D (r + 3); tb_at D (r + 4); tb_at D (r + 5)] with (hexs D r).
                         rewrite <- (firstn_all (hexs D r)).
                         replace (length (hexs D r)) with (S i) by (subst i; reflexivity).
                         rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                         rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                       split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                       split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                       split; [repeat split; assumption|].
                       split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                       split; [exact L8|]. split; [exact L9|]. split; [exact L11 | exact L21].
    + (* a decimal digit: b - 48 *)
      rewrite branch_geu_U, U_SOff, U_SLit in Hc. ewrh Hc. rewrite E32, unsigned_lit_small in Hc
        by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
      change (zcanon 10) with 10 in Hc.
      rewrite (zc_lt (tb_at D (r + 2 + Z.of_nat i)) (-48) 10) in Hc
        by (pose proof (Htb (r + 2 + Z.of_nat i)); lia).
      apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [Hc1 Hc2].
      apply Z.leb_le in Hc1. apply Z.ltb_lt in Hc2.
      assert (Hhv : PjGrammar.hexval (tb_at D (r + 2 + Z.of_nat i)) =
        Some (tb_at D (r + 2 + Z.of_nat i) + (-48)))
        by (replace (tb_at D (r + 2 + Z.of_nat i) + (-48)) with (tb_at D (r + 2 + Z.of_nat i) - 48) by lia;
            apply psd_hexval_dec; [exact (Htb _) | lia]).
                 paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
      --- apply awr_ro. vm_compute. reflexivity.
      --- psrr_branch_tok RUN BR HS SHOK dBspan.
          +++ (* another digit: the back edge to PS_HEX *)
              rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
              rewrite E12, unsigned_lit_small in Hc by lia.
              rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
              change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
              paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_HEX).
              *** apply awr_ro. vm_compute. reflexivity.
              *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                    rewrite (u_reseat (w_H W) _ _ msN MD PS_HEX HS ltac:(vm_compute; reflexivity)
                              ltac:(vm_compute; reflexivity));
                    rewrite u_cfg_pc;
                    assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                      by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                            (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                          [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                  end.
                  apply (IH D ly St Hp W _ _ _ out w r Q (S i)
                           (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-48)))); [lia | exact HPRE | exact HAFTER|].
                  u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-48).
                  split; [exists regs0; exact HDEC1|].
                  split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|]. split; [lia|].
                  split.
                  { rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                    rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                  split.
                  { pose proof (Htb (r + 2 + Z.of_nat i)).
                    assert (Hp16 : 16 ^ Z.of_nat (S i) = 16 * 16 ^ Z.of_nat i)
                      by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
                    lia. }
                  split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                  split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                  split; [repeat split; assumption|].
                  split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                  split; [exact L8|]. split; [exact L9|]. split; [exact L11|]. split; [exact L21|].
                  split; [rewrite L12; f_equal; lia|].
                  split; [rewrite L10; f_equal; lia | rewrite L22; f_equal; lia].
          +++ (* the fourth digit is read: the tail at 880 *)
              rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
              rewrite E12, unsigned_lit_small in Hc by lia.
              rewrite (zcanon_id (4 - Z.of_nat i + -1)) in Hc by (unfold M64; lia).
              change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
              assert (Hi3 : i = 3%nat) by lia.
              paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + 880).
              *** apply awr_ro. vm_compute. reflexivity.
              *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                    rewrite (u_reseat (w_H W) _ _ msN MD 880 HS ltac:(vm_compute; reflexivity)
                              ltac:(vm_compute; reflexivity));
                    rewrite u_cfg_pc;
                    assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs0 (ms_mem msN) MD out w r Q)
                      by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs0 mem md out w r Q
                            (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                          [let x := fresh "x" in intros x _; revert x; u_memeq | u_grows])
                  end.
                  apply (ps_u_tail D ly St Hp W _ _ _ out w r Q
                           (16 * acc + (tb_at D (r + 2 + Z.of_nat i) + (-48))) HPRE HAFTER).
                  u_hex_regs_t HS RG Htb E2 E8 E9 E11 E12 E19 E20 E21 E22 E24 E32 D r i acc (-48).
                  split; [exists regs0; exact HDEC1|].
                  split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|].
                  split.
                  { unfold hexs. rewrite <- psd_acc_hex4.
                    change [tb_at D (r + 2); tb_at D (r + 3); tb_at D (r + 4); tb_at D (r + 5)] with (hexs D r).
                    rewrite <- (firstn_all (hexs D r)).
                    replace (length (hexs D r)) with (S i) by (subst i; reflexivity).
                    rewrite (psu_firstn_S (hexs D r) i 0) by (cbn [hexs length]; lia).
                    rewrite psd_acc_snoc, Hacc, (hexs_nth D r i ltac:(lia)), Hhv. reflexivity. }
                  split; [split; [exact L24|]; split; [rewrite L23; exact (proj1 (proj2 HSH)) | exact L25]|].
                  split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                  split; [repeat split; assumption|].
                  split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|]. split; [exact L20|].
                  split; [exact L8|]. split; [exact L9|]. split; [exact L11 | exact L21].
Qed.


(* the memory a chain of runs with the one writable byte w leaves *)
Ltac u_memeq_w E19 :=
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  repeat match goal with
  | |- mrestrict ?H ?m1 x = mrestrict ?H ?m1 x => reflexivity
  | HF : frame_of ?EE ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- mrestrict ?H ?m1 x = _ =>
      rewrite (frame_w EE rs _ _ _ ltac:(vm_compute; reflexivity)
                 ltac:(rewrite ?ew_ewset_other by lia; rewrite E19; apply unsigned_lit_small; lia) HF x Hx)
  end.

(* ---- THE SUB-STRETCH: from PS_DEC (328) when the text at r is a backslash then a u, over the invariant P ---- *)
Theorem ps_u_segP : ps_seg_uP B ARx SK P CTX CW.
Proof.
  intros D ly St Hp W regs mem md out w r Q HPRE HDEC Hb0 Hb1 HAFTER.
  (* the runs and the two calls are at wle, into S4_PsBase's hand-off form ps_finP; the free cut and the back edge
     may cross the bad escape's fuzz_free (ps_finP_hand at u_free_run and at the back edge) *)
  apply ps_finP_SRr'.
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly St Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0. pose proof (ps_head8 HW) as Hh8.
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & HSH & HGT & HCST & HIN & HROD & HSC
    & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  pose proof HSRC as (Hgb & _ & _ & _ & Hrat & _).
  destruct HREL as (done & Hbd & Hdl & HS0 & HN0 & Hr0 & Hwo & Hww & Hsync).
  pose proof (dec_w_ns B ARx SK P LAWS HW CTX CW D ly St Hp W regs mem md out w r Q HPRE HDEC) as Hns.
  pose proof (dec_tmp_w B ARx SK P LAWS HW CTX CW D ly St Hp W regs mem md out w r Q HPRE HDEC) as Htmp.
  assert (Htb : forall x, 0 <= tb_at D x < 256).
  { intros x. unfold tb_at. destruct (Nat.lt_ge_cases (Z.to_nat (x - pi_text D)) (length (pi_tb D))) as [Hl|Hl];
      [exact (garr8_bytes _ _ _ Hgb _ Hl) | rewrite nth_overflow by exact Hl; lia]. }
  change (nth (Z.to_nat (r - pi_text D)) (pi_tb D) 0) with (tb_at D r) in Hb0.
  change (nth (Z.to_nat (r + 1 - pi_text D)) (pi_tb D) 0) with (tb_at D (r + 1)) in Hb1.
  (* a lone backslash does not scan, so the text has a byte at r + 1 *)
  assert (Hr1 : r + 1 < pi_text D + pi_len D).
  { destruct (Z_lt_le_dec (r + 1) (pi_text D + pi_len D)) as [Hx|Hx]; [exact Hx|]. exfalso.
    assert (Hnil : rest_atR (pi_tb D) (pi_text D) (r + 1) = [])
      by (unfold rest_atR; apply skipn_all2; lia).
    rewrite (rest_tb1 D r ltac:(rewrite Hlen; lia)), Hb0, Hnil in Hsync. cbn [PjGrammar.scan] in Hsync.
    discriminate. }
  set (E := EK regs (pi_tb D) (pi_text D) r).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, EK; apply Eimg_env).
  assert (RG : forall n0 (x : bv 5), Z.of_nat n0 = bv_unsigned x -> ew E n0 = getr regs x)
    by (intros n0 x Hx; unfold E; apply EK_reg; exact Hx).
  assert (E2 : ew E 2 = Z_to_bv 64 (PS_SP D)) by (rewrite (RG 2%nat 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = Z_to_bv 64 (pi_q D)) by (rewrite (RG 8%nat 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = Z_to_bv 64 (pi_q D + 8)) by (rewrite (RG 9%nat 9%bv eq_refl); exact R9).
  assert (E11 : ew E 11 = Z_to_bv 64 (pi_text D + pi_len D)) by (rewrite (RG 11%nat 11%bv eq_refl); exact R11).
  assert (E18 : ew E 18 = Z_to_bv 64 out) by (rewrite (RG 18%nat 18%bv eq_refl); exact R18).
  assert (E19 : ew E 19 = Z_to_bv 64 w) by (rewrite (RG 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 r) by (rewrite (RG 20%nat 20%bv eq_refl); exact R20).
  assert (E23 : ew E 23 = Z_to_bv 64 (SHADOW_OFF + pi_q D / 8))
    by (rewrite (RG 23%nat 23%bv eq_refl); exact (proj1 (proj2 HSH))).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (RG 24%nat 24%bv eq_refl); exact (proj1 HSH)).
  assert (E32 : ew E 32 = Z_to_bv 64 (tb_at D r))
    by (unfold E, tb_at; rewrite (EK_byte regs _ _ r 0 ltac:(lia)); do 3 f_equal; lia).
  assert (E33 : ew E 33 = Z_to_bv 64 (tb_at D (r + 1))) by (unfold E; exact (EK_byte regs _ _ r 1 ltac:(lia))).
  destruct (dec_entry B ARx SK P LAWS HW CTX CW D ly St Hp W regs mem md out w r Q HPRE HDEC) as [HSe SHOK].
  assert (HS : st_ok_pi segs VAL E (add_atom (add_atom ss_dec 33 (mkAF 117 117 0)) 32 (mkAF 92 92 0))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSO + PS_DEC))) mem (seg_rom segs)))).
  { apply st_ok_pi_add_fact; [apply st_ok_pi_add_fact; [exact HSe|]|].
    - apply (afact_rng E 33 117); [rewrite E33, Hb1; reflexivity | lia | lia
                                  | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
    - apply (afact_rng E 32 92); [rewrite E32, Hb0; reflexivity | lia | lia
                                 | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  pose proof HMN as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PS_PAListing PS_PAImg B prh_pst ARx _ LAWS P PLAW).
  pose (BR := paj_branch (PI := PS_PAImg)).
  rewrite u_cfg_pc. unfold u_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
  - cbn [ms_mem mkst].
    apply (ob_range segs (w_H W) mem E dBx (SOff 20 0) (pi_text D) (Z.of_nat (length (pi_tb D))) r 1);
      [exact Hrat | | | lia | rewrite Hlen; lia].
    + unfold dBx. rewrite U_SOff, E24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    + rewrite U_SOff, E20, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
  - apply (awr_w E _ _ _ _ _ _ _ _ w);
      [vm_compute; reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Htmp].
  - psrr_branch_tok RUN BR HS SHOK dBspan.
    + (* the byte at r is not a backslash: refuted *)
      exfalso. rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
      rewrite E32, Hb0, Z.add_0_r, unsigned_lit_small in Hc by lia.
      rewrite (zcanon_id 92) in Hc by (unfold M64; lia). change (zcanon 92) with 92 in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. lia.
    + clear Hc.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
      * apply (awr_w _ _ _ _ _ _ _ _ _ w);
          [vm_compute; reflexivity | ewr; rewrite E19; apply unsigned_lit_small; lia | exact Htmp].
      * psrr_branch_tok RUN BR HS SHOK dBspan.
        -- (* r + 1 would be past the text: refuted *)
           exfalso. rewrite branch_geu_U, !U_SOff in Hc. ewrh Hc.
           rewrite E20, E11, !unsigned_lit_small in Hc by lia.
           rewrite (zcanon_id (r + 1)) in Hc by (unfold M64; lia).
           rewrite (zcanon_id (pi_text D + pi_len D + 0)) in Hc by (unfold M64; lia).
           apply negb_true_iff, Z.ltb_ge in Hc. lia.
        -- clear Hc.
           assert (Hwne : r + 1 <> w) by (destruct (Hap (r + 1) ltac:(rewrite <- Hlen in Hr1; lia)); lia).
           lazymatch goal with HX : st_ok_pi _ _ ?E1 ?ss1 (restrict _ ?ms1) |- _ =>
             assert (HM1 : forall y : word, bv_unsigned y <> w ->
               mrestrict (w_H W) (ms_mem ms1) y = mrestrict (w_H W) mem y) by (u_memeq_w E19);
             pose proof (txt_cur W mem (ms_mem ms1) w (pi_text D) (pi_tb D) (r + 1) HM1 Hgb
                           ltac:(rewrite Hlen; lia) Hwne ltac:(lia)) as V1;
             pose proof (add_t1 E1 ss1 _ r (tb_at D (r + 1)) (PS_SP D) (pi_q D) w HX
               ltac:(vm_compute; reflexivity) ltac:(ewr; exact E20) ltac:(ewr; exact E33) ltac:(ewr; exact E2)
               ltac:(ewr; exact E9) ltac:(ewr; exact E19) ltac:(lia) ltac:(lia) (Htb _) ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V1) as HS1;
             clear HX; rename HS1 into HS
           end.
           paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
           ++ cbn [ms_mem mkst].
              apply (ob_range_w (w_H W) mem _ _ dBx (SOff 20 1) (pi_text D) (Z.of_nat (length (pi_tb D)))
                       (r + 1) 1 w); [exact HM1 | exact Hns | lia | rewrite Hlen; lia | exact Hrat | | | lia
                                     | rewrite Hlen; lia].
              ** unfold dBx. rewrite U_SOff. ewr.
                 rewrite E24, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
                 apply zcanon_id. unfold SHADOW_OFF, M64. lia.
              ** rewrite U_SOff. ewr. rewrite E20, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
           ++ apply (awr_w _ _ _ _ _ _ _ _ _ w);
                [vm_compute; reflexivity | ewr; rewrite E19; apply unsigned_lit_small; lia | exact Htmp].
           ++ psrr_branch_tok RUN BR HS SHOK dBspan.
              ** (* the byte at r + 1 is not a u: refuted *)
                 exfalso. rewrite branch_ne_U, U_SOff, U_SLit in Hc. ewrh Hc.
                 rewrite E33, Hb1, Z.add_0_r, unsigned_lit_small in Hc by lia.
                 rewrite (zcanon_id 117) in Hc by (unfold M64; lia). change (zcanon 117) with 117 in Hc.
                 apply negb_true_iff, Z.eqb_neq in Hc. lia.
              ** clear Hc.
                 paj_run_tok_x_inv RUN HS HJ SHOK HPM dBspan.
                 --- apply (awr_w _ _ _ _ _ _ _ _ _ w);
                       [vm_compute; reflexivity | ewr; rewrite E19; apply unsigned_lit_small; lia | exact Htmp].
                 --- psrr_branch_tok RUN BR HS SHOK dBspan.
                     +++ (* fewer than four bytes after the u: refused *)
                         rewrite branch_lt_Sg, (Sg_room _ (-2) (pi_text D + pi_len D) r), S_SLit in Hc
                           by (ewr; first [exact E11 | exact E20 | lia]).
                         change (bv_swrap 64 4) with 4 in Hc. apply Z.ltb_lt in Hc.
                         assert (HN : PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None).
                         { rewrite (rest_tb1 D r ltac:(rewrite Hlen; lia)), Hb0,
                             (rest_tb1 D (r + 1) ltac:(rewrite Hlen; lia)), Hb1.
                           replace (r + 1 + 1) with (r + 2) by lia.
                           apply psd_dec_u_short. rewrite psd_rest_len by lia. lia. }
                         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_FREECUT).
                         *** apply (awr_w _ _ _ _ _ _ _ _ _ w);
                               [vm_compute; reflexivity | ewr; rewrite E19; apply unsigned_lit_small; lia
                               | exact Htmp].
                         *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                               rewrite (u_reseat (w_H W) _ _ msN MD PS_FREECUT HS ltac:(vm_compute; reflexivity)
                                          ltac:(vm_compute; reflexivity));
                               eapply (u_free_run D ly St Hp W regs mem md out w r Q (ms_mem msN) MD _ (ms_regs msN)
                                         HPRE HDEC HJ HPM)
                             end;
                             [ apply same_but_materialized_wvb_any | u_memeq_w E19 | u_grows | exact HN | | | | ];
                             u_fregs1 HS RG HGT R2 R18 R8.
                     +++ (* four bytes are there: the hex loop *)
                         rewrite branch_lt_Sg, (Sg_room _ (-2) (pi_text D + pi_len D) r), S_SLit in Hc
                           by (ewr; first [exact E11 | exact E20 | lia]).
                         change (bv_swrap 64 4) with 4 in Hc. apply Z.ltb_ge in Hc.
                         paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM dBspan (PSO + PS_HEX).
                         *** apply (awr_w _ _ _ _ _ _ _ _ _ w);
                               [vm_compute; reflexivity | ewr; rewrite E19; apply unsigned_lit_small; lia
                               | exact Htmp].
                         *** lazymatch goal with |- SRr _ _ {| cfg_ms := ?msN; cfg_model := ?MD |} _ =>
                               rewrite (u_reseat (w_H W) _ _ msN MD PS_HEX HS ltac:(vm_compute; reflexivity)
                                          ltac:(vm_compute; reflexivity));
                               rewrite u_cfg_pc;
                               assert (HDEC1 : ps_at_decP B ARx SK P D ly St Hp W regs (ms_mem msN) MD out w r Q)
                                 by (apply (dec_run B ARx SK P LAWS HW PST_ok CTX CW D ly St Hp W regs mem md out w r Q
                                       (ms_mem msN) MD _ HPRE HDEC HJ HPM (same_but_materialized_wvb_any md _));
                                     [u_memeq_w E19 | u_grows])
                             end.
                         apply (ps_u_hex 4 D ly St Hp W _ _ _ out w r Q 0%nat 0 ltac:(lia) HPRE HAFTER).
                         prreg HS (1%bv : bv 5) L1. prreg HS (2%bv : bv 5) L2. prreg HS (3%bv : bv 5) L3.
                         prreg HS (4%bv : bv 5) L4. prreg HS (5%bv : bv 5) L5. prreg HS (6%bv : bv 5) L6.
                         prreg HS (7%bv : bv 5) L7. prreg HS (8%bv : bv 5) L8. prreg HS (9%bv : bv 5) L9.
                         prreg HS (10%bv : bv 5) L10. prreg HS (11%bv : bv 5) L11. prreg HS (12%bv : bv 5) L12.
                         prreg HS (16%bv : bv 5) L16. prreg HS (17%bv : bv 5) L17. prreg HS (18%bv : bv 5) L18.
                         prreg HS (19%bv : bv 5) L19. prreg HS (20%bv : bv 5) L20. prreg HS (21%bv : bv 5) L21.
                         prreg HS (22%bv : bv 5) L22. prreg HS (23%bv : bv 5) L23. prreg HS (24%bv : bv 5) L24.
                         prreg HS (26%bv : bv 5) L26. prreg HS (27%bv : bv 5) L27. prreg HS (28%bv : bv 5) L28.
                         prreg HS (29%bv : bv 5) L29. prreg HS (30%bv : bv 5) L30. prreg HS (31%bv : bv 5) L31.
                         pose proof (st_ok_pi_restrict_reg _ _ _ _ 25%bv HS) as L25.
                         change (sr_get _ 25%bv) with (shx 9) in L25.
                         rewrite (sv_shx _ 9 (pi_q D + 8)) in L25 by (ewr; first [exact E9 | exact E24 | lia]).
                         rewrite ?ew_ewset_other in L2, L3, L4, L8, L9, L10, L11, L18, L19, L20, L22, L23, L24 by lia.
                         rewrite E2 in L2. rewrite E8 in L8. rewrite E9 in L9. rewrite E11 in L11.
                         rewrite E19 in L19. rewrite E20 in L20, L10, L22. rewrite E23 in L23. rewrite E24 in L24.
                         rewrite (RG 3%nat 3%bv eq_refl) in L3. rewrite (RG 4%nat 4%bv eq_refl) in L4.
                         rewrite (RG 18%nat 18%bv eq_refl) in L18.
                         rewrite !unsigned_lit_small in L10, L22 by lia.
                         split; [exists regs; exact HDEC1|].
                         split; [exact Hb0|]. split; [exact Hb1|]. split; [lia|]. split; [lia|].
                         split; [reflexivity|]. split; [cbn; lia|].
                         split; [split; [exact L24|]; split; [exact L23 | exact L25]|].
                         split; [split; [rewrite L3; exact (proj1 HGT) | rewrite L4; exact (proj2 HGT)]|].
                         split; [repeat split; assumption|].
                         split; [exact L2|]. split; [rewrite L18; exact R18|]. split; [exact L19|].
                         split; [exact L20|]. split; [exact L8|]. split; [exact L9|]. split; [exact L11|].
                         split; [exact L21|]. split; [exact L12|].
                         split; [rewrite L10; f_equal; lia | rewrite L22; f_equal; lia].
Qed.

End w.

(* ---- the stable statement as the P := (fun _ => True) instance (ps_seg_u_of_True /
   ps_seg_free_of_True of S4_PsDecKit.v, srr_inv_laws_True / srr_inv_call_True of S4_PsBase.v). Its arguments are
   Section w's in the same order, the free cut in its stable form. ---- *)
Section wT. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable CTX : list (list Z).
Variable CW : list (list Z).
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.
Hypothesis HHEX4 : thex4_specX B ARx SK.
Hypothesis HPUTU : tput_utf8_specX B ARx SK.
Hypothesis HFREE : ps_seg_free B ARx SK CTX CW.
Theorem ps_u_seg : ps_seg_u B ARx SK CTX CW.
Proof.
apply (proj1 (ps_seg_u_of_True B ARx SK CTX CW)).
exact (ps_u_segP B ARx SK CTX CW LAWS _ srr_inv_laws_True srr_inv_call_True HW PST_ok ZSA IMGV HHEX4 HPUTU
  (proj2 (ps_seg_free_of_True B ARx SK CTX CW) HFREE)).
Qed.
End wT.
