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
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsFree.v; 622 of its 679 lines of code are new or changed and 469 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string's decode stretch): the KIT of the \u SUB-STRETCH (S4_PsU.v, the
   sub-stretch ps_seg_u of S4_PsDecKit.v). Two layers, nothing about the engine's runs:
   - PURE: the hex loop's accumulator against PjGrammar.hex4 (the code's `or (slliw acc 4) digit`), and the list
     facts the four-digit peel needs;
   - MEMORY: ps_at_decP carried across a STRETCH that writes at most the out byte (dec_run, over the kit's dec_keep),
     across a CALL whose footprint is the hex4 slot of parse_string's own frame or the bytes put_utf8 writes at the
     write cursor (dec_call), and the cursor move of a step that emits SEVERAL bytes (dec_closeN, the multi-byte twin
     of the kit's dec_close1); the frame chain from q at the CURRENT view (chain_now), which every call needs.
   THE GENERIC INVARIANT P (a Theorem Labs lane 12:18Z / 12:22Z): the cut is ps_at_decP P, whose carry ps_carryP has P mem
   last. P is a Section Variable, never instantiated here. dec_run takes the run's own P at the new memory (its HPM,
   YSRrMemnorm's runner twin at P) and hands it to the kit's dec_keep; dec_call takes P at the post memory (S4_PsU.v
   derives it by srr_inv_call from the callee text's m-form keep); dec_closeN carries it unchanged.
   FILE SET: as the kit's cut 7cdbb61b5fa0 carries it (PRH_Base blob ef7c8ca98529, PRH_FnReader f1ae32e3b2cd, listing
   Listing_prog.v 7ed1529926bd, PAImg_prog.v 505a51ff7d08), this row's S4_PsBase.v and S4_PsDecKit.v (the ledger
   through its named helpers ps_led_blocks / ps_led_heads); earlier the kit of record at base
   dd6bf533e31 (old-pin acceptance kit 4f18c75d4900, engine s1b 459129c18903).
   Numerals: 4 / 16 (WORD: a hex digit's bits and its radix), 8 / 24 / 32 / 36 / 40 / 136 (DERIVED: frame offsets
   inside parse_string, 144 its frame LENGTH), 2 ^ 47 / 2 ^ 64 (DERIVED: the address band and the word range),
   255 / 256 (WORD: a byte), 55296 / 56320 / -56613888 (WORD: the surrogate constants the prologue stores); no
   ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_HShadow S4_PsBase S4_PsDecModel S4_PsSrc S4_PsDecKit.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- PURE: lists and the hex accumulator ---- *)
Lemma psu_firstn_S : forall (l : list Z) (i : nat) (d : Z),
  (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  intros l. induction l as [|a l IH]; intros i d Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. cbn [length] in Hi. lia.
Qed.
(* the loop's digit step: acc' = (acc << 4) | v with v < 16 is 16 * acc + v *)
Lemma psu_lor_shl : forall a v, 0 <= a -> 0 <= v < 16 -> Z.lor v (Z.shiftl a 4) = 16 * a + v.
Proof.
  intros a v Ha Hv.
  assert (Hd : Z.land v (Z.shiftl a 4) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 4) as [Hl|Hl].
    - rewrite (Z.shiftl_spec a 4 n) by lia.
      replace (Z.testbit a (n - 4)) with false by (symmetry; apply Z.testbit_neg_r; lia).
      apply andb_false_r.
    - replace (Z.testbit v n) with false; [apply andb_false_l|].
      symmetry. replace v with (v mod 2 ^ 4) by (apply Z.mod_small; lia).
      apply Z.mod_pow2_bits_high. lia. }
  rewrite <- Z.lxor_lor by exact Hd. rewrite <- Z.add_nocarry_lxor by exact Hd.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. lia.
Qed.
Lemma psu_acc_none_app : forall l bs, psd_acc bs = None -> psd_acc (bs ++ l) = None.
Proof.
  intros l. induction l as [|b l IH] using rev_ind; intros bs H.
  - rewrite app_nil_r. exact H.
  - rewrite app_assoc, psd_acc_snoc, (IH bs H). reflexivity.
Qed.


(* ---- THE SUB-STRETCH'S SYMBOLIC STATES (the engine's data; every numeral a DERIVED offset inside parse_string or
   a WORD the code holds) and the builders that make them from concrete facts ---- *)
(* the one text byte the hex loop reads, at the scan cursor s6 (atom 22) *)
Definition rg_h : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
(* hex4's out slot, sp + 36 in parse_string's own frame, 4 bytes *)
Definition rg_lo : YP09.region := YP09.mkRegion (Some 2%nat) 36 40 0 0 [YP09.mkChunk 36 (CVal 4 (SOff 32 0))].
(* the cursor's end word at q + 8, re-read by the latch (its value is the extra atom 32, not a1: a1 is clobbered) *)
Definition rg_end : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition f_hex : list (nat * afact) :=
  f_base ++ [(22%nat, mkAF 0 (2 ^ 47 - 64) 0); (12%nat, mkAF 1 4 0); (21%nat, mkAF 0 4095 0); (32%nat, mkAF 0 255 0)].
Definition ss_hex : sstate :=
  mkSS (PSO + PS_HEX) (pins (pins_keep ++ [(10%bv, SOff 22 0)]) sr_atoms) [rg_h] None (mkFacts f_hex [] []).
Definition ss_tail : sstate :=
  mkSS (PSO + 880) (pins pins_keep sr_atoms) [rg_k] None
    (mkFacts (f_base ++ f_bytes ++ [(21%nat, mkAF 0 65535 0)]) [] []).
(* the constants a cut after a call keeps: the callee-saved s9 s10 s11 (the caller-saved ones are reloaded at
   1048..1096) *)
Definition pins_pu : list (bv 5 * sv) := [(25%bv, shx 9); (26%bv, SLit 34); (27%bv, SLit 10)].
Definition ss_ah : sstate :=
  mkSS (PSO + 992) (pins (pins_pu ++ [(10%bv, SLit 0)]) sr_atoms) [rg_lo; rg_k] None
    (mkFacts (f_base ++ [(21%nat, mkAF 55296 56319 0); (32%nat, mkAF 0 65535 0)]) [] []).
Definition ss_ahn : sstate :=
  mkSS (PSO + 992) (pins (pins_pu ++ [(10%bv, SLit (-1))]) sr_atoms) [] None (mkFacts f_base [] []).
Definition ss_pu : sstate := mkSS (PSO + 1036) (pins pins_pu sr_atoms) [] None (mkFacts f_base [] []).
Definition ss_ap : sstate :=
  mkSS (PSO + 1048) (pins [(25%bv, shx 9)] sr_atoms) [rg_end] None
    (mkFacts (f_base ++ [(22%nat, mkAF 0 (2 ^ 47 - 64) 0); (10%nat, mkAF 1 4 0); (32%nat, mkAF 0 (2 ^ 47 - 64) 0)]) [] []).
(* the constant registers the whole \u sub-stretch keeps (ps_dec_consts' register part less a4 / a5 / s5, which the
   hex loop and put_utf8 clobber and the block at 1048..1096 reloads) *)
Definition u_keep_regs (regs : bvmap 5 word) : Prop :=
  getr regs 26 = w64 34 /\ getr regs 16 = w64 92 /\ getr regs 17 = w64 91 /\ getr regs 5 = w64 47 /\
  getr regs 6 = w64 98 /\ getr regs 7 = w64 8 /\ getr regs 28 = w64 113 /\ getr regs 29 = w64 102 /\
  getr regs 30 = w64 12 /\ getr regs 31 = w64 110 /\ getr regs 27 = w64 10 /\ getr regs 1 = w64 116.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).

(* the environment of a cut: the registers are the atoms 0..31, the extra values the atoms 32.. *)
Definition EX (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma EX_reg : forall regs extra n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (EX regs extra) n = getr regs x.
Proof.
  intros regs extra n x Hn. unfold EX. rewrite Eimg_low by (pose proof (u5_range x); unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn.
Qed.
Lemma EX_extra : forall regs extra j, (32 + j < A_TEXT)%nat ->
  ew (EX regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. unfold EX. rewrite Eimg_low by lia. apply ew_Ereg_extra. Qed.
Lemma EX_env : forall regs extra, img_env VAL A_LIM (EX regs extra).
Proof. intros. unfold EX. apply Eimg_env. Qed.
Lemma EX_regs_ok : forall regs extra, regs_ok (EX regs extra) sr_atoms regs.
Proof. intros. unfold EX. apply regs_ok_Eimg_Ereg. Qed.
Lemma facts_ok_atoms : forall E l, atoms_ok E l -> facts_ok E (mkFacts l [] []).
Proof. intros E l H. split; [exact H | split; exact I]. Qed.
(* the five base atom facts of every cut of the stretch *)
Lemma atoms_f_base : forall E sp q r w,
  ew E 2 = Z_to_bv 64 sp -> ew E 9 = Z_to_bv 64 (q + 8) -> ew E 20 = Z_to_bv 64 r -> ew E 19 = Z_to_bv 64 w ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 2 ^ 46 <= q + 8 <= 2 ^ 47 - 16 -> (q + 8) mod 8 = 0 ->
  0 <= r <= 2 ^ 47 - 64 -> 4096 <= w <= 2 ^ 47 - 64 -> atoms_ok E f_base.
Proof.
  intros E sp q r w E2 E9 E20 E19 E24 Hsp Hsp16 Hq Hq8 Hr Hw.
  cbn [f_base atoms_ok]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  - apply (afact_rng E 2 sp); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  - apply (afact_rng E 9 (q + 8)); [exact E9 | lia | lia | change (2 ^ 3) with 8; exact Hq8 | lia].
  - apply (afact_rng E 20 r); [exact E20 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  - apply (afact_rng E 19 w); [exact E19 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  - apply (afact_rng E 24 SHADOW_OFF); [exact E24 | lia | unfold SHADOW_OFF; lia
      | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
Qed.
(* the pinned constant registers of a cut *)
Lemma pins_keep_ok : forall E regs q,
  ew E 9 = Z_to_bv 64 (q + 8) -> ew E 24 = Z_to_bv 64 SHADOW_OFF -> 0 <= q + 8 < 2 ^ 47 ->
  getr regs 25 = w64 (SHADOW_OFF + (q + 8) / 8) -> u_keep_regs regs ->
  Forall (fun p => getr regs (fst p) = sv_denot E (snd p)) pins_keep.
Proof.
  intros E regs q E9 E24 Hq R25 (K26 & K16 & K17 & K5 & K6 & K7 & K28 & K29 & K30 & K31 & K27 & K1).
  unfold pins_keep.
  apply Forall_cons; [cbn [fst snd]; rewrite R25; symmetry; apply sv_shx; [exact E9 | lia | exact E24]|].
  repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
Qed.
Lemma pins_pu_ok : forall E regs q,
  ew E 9 = Z_to_bv 64 (q + 8) -> ew E 24 = Z_to_bv 64 SHADOW_OFF -> 0 <= q + 8 < 2 ^ 47 ->
  getr regs 25 = w64 (SHADOW_OFF + (q + 8) / 8) -> getr regs 26 = w64 34 -> getr regs 27 = w64 10 ->
  Forall (fun p => getr regs (fst p) = sv_denot E (snd p)) pins_pu.
Proof.
  intros E regs q E9 E24 Hq R25 K26 K27. unfold pins_pu.
  apply Forall_cons; [cbn [fst snd]; rewrite R25; symmetry; apply sv_shx; [exact E9 | lia | exact E24]|].
  repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
Qed.
(* a state with no writable window: the run writes nothing and may write anything the walk's window admits *)
Definition ro_mem (rs : smem) : bool := forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs.
Lemma awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  ro_mem rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs STK sp0 FP bl0 blc ly own Hok a (rg & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hok rg Hin) as Hb. cbv beta in Hb. apply Z.leb_le in Hb. lia.
Qed.
Lemma frame_ro : forall E rs (m m' : word -> option byte),
  ro_mem rs = true -> frame_of E rs m m' -> forall x : word, m' x = m x.
Proof.
  intros E rs m m' Hok Hfr x. apply Hfr. intros (rg & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) Hok rg Hin) as Hb. cbv beta in Hb. apply Z.leb_le in Hb. lia.
Qed.
(* a shadow range over bytes whose shadow byte reads 0 (the machine stack, by alx_zshadow_byte) *)
Lemma ra_stack : forall (rd : reader) p m,
  (forall a, p <= a < p + m -> rd (SHADOW_OFF + a / 8) = Some 0) -> range_addressable rd SHADOW_OFF p m.
Proof.
  intros rd p m Hz a Ha. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply Hz. exact Ha.
Qed.
(* a chain under a pointwise-equal view *)
Lemma achain_rd : forall ly (rd rd' : reader) sp v ch,
  (forall a, rd' a = rd a) -> achain ly rd sp v ch -> achain ly rd' sp v ch.
Proof.
  intros ly rd rd' sp v ch Hrd [(H1 & H2)|(H1 & H2 & H3 & H4 & H5)]; [left; split; assumption|].
  right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  eapply fpchain_ext; [|lia|exact H4]. intros a _ _. apply rdword_ext. intros k Hk. apply Hrd.
Qed.
(* the sum of two atoms, as the reload block's `add s3, s3, a0` leaves it *)
Lemma sv_add : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = w64 (x + y).
Proof.
  intros E a b x y Ha Hb Hx Hy Hxy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, Ha, Hb, !Z.add_0_r, !unsigned_lit_small by lia.
  rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id y) by (unfold M64; lia).
  unfold w64. f_equal. apply zcanon_id. unfold M64. lia.
Qed.
(* a callee-saved register across a call *)
Lemma pres_reg : forall (regs regs' : bvmap 5 word) n (x : bv 5),
  aregs_preserved regs regs' -> acallee_saved n -> x = Z_to_bv 5 n -> getr regs' x = getr regs x.
Proof. intros regs regs' n x H Hc ->. exact (H n Hc). Qed.
(* the walk's configuration at a DERIVED offset inside parse_string, in the engine's form *)
Definition u_cfg (off : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : config :=
  mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + (PSO + off))) mem (seg_rom segs)) md.
Lemma u_cfg_pc : forall off regs mem md, cfg_at segs (ps_pc off) regs mem md = u_cfg off regs mem md.
Proof.
  intros off regs mem md. unfold cfg_at, ps_pc, u_cfg, w64, PSO.
  replace (BASE + PS_OFF + off) with (BASE + (PS_OFF + off)) by lia. reflexivity.
Qed.
(* bytes under a pointwise-equal memory *)
Lemma bytes_at_keep : forall (W : world segs) m m' p l,
  (forall x, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) -> bytes_at W m p l -> bytes_at W m' p l.
Proof.
  intros W m m' p l Hm H j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
  intros k Hk. pose proof (V k Hk) as Vk. unfold mbyte in *. rewrite Hm. exact Vk.
Qed.
(* a source window under a pointwise-equal memory *)
Lemma src_rd_keep : forall (W : world segs) m m' p l,
  (forall x : word, mrestrict (w_H W) m' x = mrestrict (w_H W) m x) -> src_rd W m p l -> src_rd W m' p l.
Proof.
  intros W m m' p l Hm (Hb & H4 & Hc & Ham & Hra & Hhu).
  split; [exact (bytes_at_keep W m m' p l Hm Hb)|].
  split; [exact H4|]. split; [exact Hc|]. split; [exact Ham|]. split.
  - eapply range_addressable_agree; [intros x _; apply aview_eq_of; apply Hm | exact Hra].
  - intros Hn. apply (hull_keep (aview segs (w_H W) m)); [exact (Hhu Hn) | intros sx _; apply aview_eq_of; apply Hm].
Qed.
(* the text byte at r + 1, added mid-run once the dispatch's room test passed (ss_dec's four regions) *)
Lemma add_t1 : forall E ss ms r b1 sp q w,
  st_ok_pi segs VAL E ss ms -> ss_mem ss = [rg_k; rg_in; rg_t 0; rg_o] ->
  ew E 20 = Z_to_bv 64 r -> ew E 33 = Z_to_bv 64 b1 -> ew E 2 = Z_to_bv 64 sp ->
  ew E 9 = Z_to_bv 64 (q + 8) -> ew E 19 = Z_to_bv 64 w ->
  0 <= r -> r + 2 <= 2 ^ 64 -> 0 <= b1 < 256 -> 0 <= sp -> sp + 32 <= 2 ^ 64 ->
  0 <= q + 8 -> q + 16 <= 2 ^ 64 -> 0 <= w -> w + 1 <= 2 ^ 64 ->
  (r + 2 <= sp + 8 \/ sp + 32 <= r + 1) -> (r + 2 <= q + 8 \/ q + 16 <= r + 1) ->
  (r + 2 <= w \/ w + 1 <= r + 1) -> val_mem segs (ms_mem ms) (r + 1) 1 b1 ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (rg_t 1 :: [rg_k; rg_in; rg_t 0; rg_o])
                        (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r b1 sp q w HS Hm E20 E33 E2 E9 E19 Hr Hr2 Hb1 Hsp Hsp32 Hq Hq16 Hw Hw1 Dk Di Do V1.
  pose proof (st_ok_pi_add_region E ss ms (rg_t 1) HS ltac:(vm_compute; reflexivity)) as H1.
  rewrite Hm in H1. apply H1.
  - apply (rok_t E _ r 1 b1 E20 ltac:(exact E33)); [lia | cbn [Z.of_nat]; lia | exact Hb1 | cbn [Z.of_nat]; exact V1].
  - cbn [all_disjoint]. split; [|split; [|split; [|split; [|exact I]]]];
      unfold extent_disjoint, rg_t, rg_k, rg_in, rg_o;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?E20, ?E2, ?E9, ?E19, !unsigned_lit_small by lia; cbn [Z.of_nat]; lia.
Qed.
(* THE RESEAT at a cut: a run's machine state at a DERIVED offset is the cut's configuration *)
Lemma u_reseat : forall H E ss ms md off,
  st_ok_pi segs VAL E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = PSO + off ->
  mkCfg ms md = cfg_at segs (ps_pc off) (ms_regs ms) (ms_mem ms) md.
Proof.
  intros H E ss ms md off HS Hrv Hpc. rewrite u_cfg_pc. unfold u_cfg. rewrite <- Hpc.
  rewrite <- (st_ok_pi_restrict_mkst H E ss ms HS Hrv). reflexivity.
Qed.
Lemma frame_ro2 : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> ro_mem rs = true -> forall x : word, m' x = m x.
Proof. intros E rs m m' H Hok. exact (frame_ro E rs m m' Hok H). Qed.
Lemma grows_refl : forall m : word -> option byte, mem_grows m m.
Proof. intros m x Hx. exact Hx. Qed.
(* an atom at an offset, as prreg leaves it *)
Lemma sv_off : forall E n c x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (x + c).
Proof.
  intros E n c x H Hx Hxc. apply bv_eq. rewrite denot_SOff, H, unsigned_lit_small by lia.
  unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the hex loop's digit step: (b + c) | (acc << 4) *)
Lemma sv_hexacc : forall E c b acc, ew E 32 = Z_to_bv 64 b -> ew E 21 = Z_to_bv 64 acc ->
  0 <= b < 256 -> 0 <= acc < 4096 -> 0 <= b + c < 16 ->
  sv_denot E (SAlu ALU_OR (SOff 32 c) (SAlu ALU_SLL (SOff 21 0) (SLit 4))) = w64 (16 * acc + (b + c)).
Proof.
  intros E c b acc H32 H21 Hb Ha Hbc. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu, U_SLit, !U_SOff, H32, H21, !unsigned_lit_small by lia. cbn [zalu_raw].
  rewrite Z.add_0_r. rewrite (zcanon_id (b + c)) by (unfold M64; lia). rewrite (zcanon_id acc) by (unfold M64; lia).
  change (Z.land (zcanon 4) 63) with 4.
  rewrite (zcanon_id (Z.shiftl acc 4)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
  rewrite psu_lor_shl by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the pair's code point: ((hi << 10) + (-56613888)) + lo *)
Lemma sv_pair : forall E hi lo, ew E 21 = Z_to_bv 64 hi -> ew E 32 = Z_to_bv 64 lo ->
  55296 <= hi < 56320 -> 56320 <= lo <= 57343 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 21 0) (SLit 10)) (SLit (-56613888))) (SOff 32 0)) =
  w64 (PjGrammar.pair_cp hi lo).
Proof.
  intros E hi lo H21 H32 Hh Hl. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu, !U_SLit, !U_SOff, H21, H32, !unsigned_lit_small by lia. cbn [zalu_raw].
  rewrite !Z.add_0_r. rewrite (zcanon_id hi) by (unfold M64; lia). rewrite (zcanon_id lo) by (unfold M64; lia).
  change (Z.land (zcanon 10) 63) with 10. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 10) with 1024.
  rewrite (zcanon_id (hi * 1024)) by (unfold M64; lia).
  pose proof (psd_pair_range hi lo Hh Hl) as Hr. rewrite psd_pair_cp in Hr |- *.
  unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
  rewrite <- Z.add_assoc, (Z.add_comm ((-56613888) mod 2 ^ 64) lo), Z.add_assoc, Zplus_mod_idemp_r.
  apply Z.mod_small. lia.
Qed.
(* the signed room test: (en + c) - r as the code computes it *)
Lemma Sg_room : forall E c en r, ew E 11 = Z_to_bv 64 en -> ew E 20 = Z_to_bv 64 r ->
  0 <= en < 2 ^ 62 -> 0 <= r < 2 ^ 62 -> 0 <= en + c -> - 2 ^ 62 < c <= 0 ->
  Sg E (SAlu ALU_ADD (SOff 11 c) (SMd M_MUL (SOff 20 0) (SLit (-1)))) = en + c - r.
Proof.
  intros E c en r H11 H20 Hen Hr Hc Hc2. rewrite S_SAlu. cbn [zalu_raw].
  rewrite U_SOff, U_SMd, U_SOff, U_SLit, H11, H20, !unsigned_lit_small by lia. cbn [zmd_raw].
  rewrite Z.add_0_r. rewrite (zcanon_id r) by (unfold M64; lia). rewrite (zcanon_id (en + c)) by (unfold M64; lia).
  change (zcanon (-1)) with (2 ^ 64 - 1).
  replace (r * (2 ^ 64 - 1)) with ((- r) + r * 2 ^ 64) by ring.
  unfold zcanon, M64. rewrite Z_mod_plus_full.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ 64 `div` 2) with (2 ^ 63).
  pose proof (Z.div_mod (- r) (2 ^ 64) ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (- r) (2 ^ 64) ltac:(lia)) as Hb.
  match goal with |- ?X mod 2 ^ 64 - 2 ^ 63 = _ =>
    assert (EX : X = (en + c - r + 2 ^ 63) + (- ((- r) / 2 ^ 64)) * 2 ^ 64) by lia; rewrite EX end.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
Lemma branch_lt_Sg : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
Lemma branch_ge_Sg : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.
(* an unsigned test of a byte offset: (b + c) mod 2 ^ 64 < k exactly when 0 <= b + c < k *)
Lemma zc_lt : forall b c k, 0 <= b < 2 ^ 62 -> - 2 ^ 62 < c <= 0 -> 0 <= k < 2 ^ 62 ->
  (zcanon (b + c) <? k) = ((0 <=? b + c) && (b + c <? k)).
Proof.
  intros b c k Hb Hc Hk. unfold zcanon, M64.
  destruct (Z_le_gt_dec 0 (b + c)) as [H|H].
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec 0 (b + c)); [|lia]. reflexivity.
  - replace ((b + c) mod 2 ^ 64) with (b + c + 2 ^ 64).
    + destruct (Z.leb_spec 0 (b + c)); [lia|]. cbn [andb]. apply Z.ltb_ge. lia.
    + symmetry. rewrite <- (Z_mod_plus_full (b + c) 1). apply Z.mod_small. lia.
Qed.
Lemma zc_lt_l : forall b c k, 0 <= b < 2 ^ 62 -> - 2 ^ 62 < c <= 0 -> 0 <= k < 2 ^ 62 ->
  (k <? zcanon (b + c)) = negb ((0 <=? b + c) && (b + c <=? k)).
Proof.
  intros b c k Hb Hc Hk. unfold zcanon, M64.
  destruct (Z_le_gt_dec 0 (b + c)) as [H|H].
  - rewrite Z.mod_small by lia. destruct (Z.leb_spec 0 (b + c)); [|lia]. cbn [andb].
    destruct (Z.ltb_spec k (b + c)); destruct (Z.leb_spec (b + c) k); try reflexivity; lia.
  - replace ((b + c) mod 2 ^ 64) with (b + c + 2 ^ 64).
    + destruct (Z.leb_spec 0 (b + c)); [lia|]. cbn [andb negb]. apply Z.ltb_lt. lia.
    + symmetry. rewrite <- (Z_mod_plus_full (b + c) 1). apply Z.mod_small. lia.
Qed.
(* the high-bits mask the tail tests: s5 & -1024 *)
Lemma U_mask : forall E cp, ew E 21 = Z_to_bv 64 cp -> 0 <= cp < 65536 ->
  U E (SAlu ALU_AND (SOff 21 0) (SLit (-1024))) = Z.land cp (-1024).
Proof.
  intros E cp H Hc. rewrite U_SAlu, U_SOff, U_SLit, H, unsigned_lit_small by lia. cbn [zalu_raw].
  rewrite Z.add_0_r, (zcanon_id cp) by (unfold M64; lia).
  change (zcanon (-1024)) with (Z.land (Z.ones 64) (-1024)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite (Z.mod_small cp) by lia.
  rewrite psd_land_m1024 by lia. apply zcanon_id. unfold M64.
  pose proof (Z.mod_pos_bound cp 1024 ltac:(lia)). lia.
Qed.
(* a shadow obligation of a text byte at the current memory of a read-only run *)
Lemma ob_txt : forall H mem mc E Bx x a n p m,
  (forall y : word, mrestrict H mc y = mrestrict H mem y) ->
  range_addressable (aview segs H mem) SHADOW_OFF a n ->
  U E Bx = SHADOW_OFF -> U E x = p -> a <= p -> p + m <= a + n ->
  range_addressable (rd_of segs (mrestrict H mc)) (U E Bx) (U E x) m.
Proof.
  intros H mem mc E Bx x a n p m Hm Hra HB Hx Ha Hpm. rewrite HB, Hx. rewrite <- (aview_rd_of segs).
  apply (range_addressable_sub _ SHADOW_OFF a n p m); [|exact Ha|exact Hpm].
  eapply range_addressable_agree; [|exact Hra]. intros y _. apply aview_eq_of. apply Hm.
Qed.
(* the two text bytes after the low surrogate's backslash (r + 6, r + 7), added mid-run once the room test passed *)
Lemma add_t67 : forall E ss ms r b6 b7 sp,
  st_ok_pi segs VAL E ss ms -> ss_mem ss = [rg_k] ->
  ew E 20 = Z_to_bv 64 r -> ew E 38 = Z_to_bv 64 b6 -> ew E 39 = Z_to_bv 64 b7 -> ew E 2 = Z_to_bv 64 sp ->
  0 <= r -> r + 8 <= 2 ^ 64 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= sp -> sp + 32 <= 2 ^ 64 ->
  (r + 8 <= sp + 8 \/ sp + 32 <= r + 6) ->
  val_mem segs (ms_mem ms) (r + 6) 1 b6 -> val_mem segs (ms_mem ms) (r + 7) 1 b7 ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) [rg_t 7; rg_t 6; rg_k] (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms r b6 b7 sp HS Hm E20 E38 E39 E2 Hr Hr8 Hb6 Hb7 Hsp Hsp32 Hd V6 V7.
  assert (H6 : st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (rg_t 6 :: ss_mem ss) (ss_resv ss) (ss_facts ss)) ms).
  { apply st_ok_pi_add_region; [exact HS | vm_compute; reflexivity | |].
    - apply (rok_t E _ r 6 b6 E20 E38); [lia | lia | exact Hb6 | exact V6].
    - rewrite Hm. cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, rg_t, rg_k.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E20, E2, !unsigned_lit_small by lia. lia. }
  rewrite Hm in H6.
  pose proof (st_ok_pi_add_region E _ ms (rg_t 7) H6 ltac:(vm_compute; reflexivity)) as H7.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H7. apply H7.
  - apply (rok_t E _ r 7 b7 E20 E39); [lia | lia | exact Hb7 | exact V7].
  - cbn [all_disjoint]. split; [|split; [|exact I]]; unfold extent_disjoint, rg_t, rg_k;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?E20, ?E2, !unsigned_lit_small by lia; lia.
Qed.
End b.

(* the memory a chain of read-only runs leaves, and its growth, from their frames *)
Ltac u_memeq := let x := fresh "x" in intros x;
  repeat match goal with
  | |- mrestrict ?H ?m1 x = mrestrict ?H ?m1 x => reflexivity
  | HF : frame_of _ _ (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- mrestrict ?H ?m1 x = _ =>
      rewrite (frame_ro2 _ _ _ _ HF ltac:(vm_compute; reflexivity) x)
  end.
Ltac u_grows :=
  repeat match goal with
  | |- mem_grows ?m ?m => apply grows_refl
  | HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- mem_grows ?a (mrestrict ?H ?m1) =>
      refine (mem_grows_trans _ _ _ _ HG)
  end.

(* ---- the stretch's memory layer ---- *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- the text at the read cursor: the byte at x, the four digits after \u, the four after the second \u ---- *)
Definition tb_at (D : ps_in) (x : Z) : Z := nth (Z.to_nat (x - pi_text D)) (pi_tb D) 0.
Definition hexs (D : ps_in) (r : Z) : list Z := [tb_at D (r + 2); tb_at D (r + 3); tb_at D (r + 4); tb_at D (r + 5)].
Definition lows (D : ps_in) (r : Z) : list Z := [tb_at D (r + 8); tb_at D (r + 9); tb_at D (r + 10); tb_at D (r + 11)].
Lemma hexs_nth : forall D r i, (i < 4)%nat -> nth i (hexs D r) 0 = tb_at D (r + 2 + Z.of_nat i).
Proof. intros D r i Hi. destruct i as [|[|[|[|i]]]]; cbn [hexs nth]; try (exfalso; lia); f_equal; lia. Qed.
Lemma lows_nth : forall D r i, (i < 4)%nat -> nth i (lows D r) 0 = tb_at D (r + 8 + Z.of_nat i).
Proof. intros D r i Hi. destruct i as [|[|[|[|i]]]]; cbn [lows nth]; try (exfalso; lia); f_equal; lia. Qed.
Lemma tb_at_in : forall D x, tb_at D x <> 0 -> pi_text D <= x -> x < pi_text D + Z.of_nat (length (pi_tb D)).
Proof.
  intros D x H Hx. unfold tb_at in H. destruct (Nat.lt_ge_cases (Z.to_nat (x - pi_text D)) (length (pi_tb D))) as [Hl|Hl]; [lia|].
  rewrite nth_overflow in H by exact Hl. lia.
Qed.
Lemma rest_tb1 : forall D x, pi_text D <= x < pi_text D + Z.of_nat (length (pi_tb D)) ->
  rest_atR (pi_tb D) (pi_text D) x = tb_at D x :: rest_atR (pi_tb D) (pi_text D) (x + 1).
Proof. intros D x Hx. apply rest_at_cons; [exact Hx | reflexivity]. Qed.
Lemma rest_u6 : forall D r, pi_text D <= r -> r + 6 <= pi_text D + Z.of_nat (length (pi_tb D)) ->
  rest_atR (pi_tb D) (pi_text D) r = tb_at D r :: tb_at D (r + 1) :: tb_at D (r + 2) :: tb_at D (r + 3) ::
    tb_at D (r + 4) :: tb_at D (r + 5) :: rest_atR (pi_tb D) (pi_text D) (r + 6).
Proof.
  intros D r H0 H6.
  rewrite (rest_tb1 D r) by lia. rewrite (rest_tb1 D (r + 1)) by lia. replace (r + 1 + 1) with (r + 2) by lia.
  rewrite (rest_tb1 D (r + 2)) by lia. replace (r + 2 + 1) with (r + 3) by lia.
  rewrite (rest_tb1 D (r + 3)) by lia. replace (r + 3 + 1) with (r + 4) by lia.
  rewrite (rest_tb1 D (r + 4)) by lia. replace (r + 4 + 1) with (r + 5) by lia.
  rewrite (rest_tb1 D (r + 5)) by lia. replace (r + 5 + 1) with (r + 6) by lia. reflexivity.
Qed.
Lemma rest_u12 : forall D r, pi_text D <= r -> r + 12 <= pi_text D + Z.of_nat (length (pi_tb D)) ->
  rest_atR (pi_tb D) (pi_text D) r = tb_at D r :: tb_at D (r + 1) :: tb_at D (r + 2) :: tb_at D (r + 3) ::
    tb_at D (r + 4) :: tb_at D (r + 5) :: tb_at D (r + 6) :: tb_at D (r + 7) :: tb_at D (r + 8) :: tb_at D (r + 9) ::
    tb_at D (r + 10) :: tb_at D (r + 11) :: rest_atR (pi_tb D) (pi_text D) (r + 12).
Proof.
  intros D r H0 H12. rewrite (rest_u6 D r) by lia. rewrite (rest_u6 D (r + 6)) by lia.
  replace (r + 6 + 1) with (r + 7) by lia. replace (r + 6 + 2) with (r + 8) by lia.
  replace (r + 6 + 3) with (r + 9) by lia. replace (r + 6 + 4) with (r + 10) by lia.
  replace (r + 6 + 5) with (r + 11) by lia. replace (r + 6 + 6) with (r + 12) by lia. reflexivity.
Qed.
Lemma rest_end : forall D, rest_atR (pi_tb D) (pi_text D) (pi_text D + Z.of_nat (length (pi_tb D))) = [].
Proof. intros D. unfold rest_atR. apply skipn_all2. lia. Qed.
Lemma rest_len : forall D x, pi_text D <= x ->
  Z.of_nat (length (rest_atR (pi_tb D) (pi_text D) x)) = Z.max 0 (pi_text D + Z.of_nat (length (pi_tb D)) - x).
Proof. intros D x Hx. rewrite psd_rest_len by exact Hx. lia. Qed.
(* the hex accumulator's range *)
Lemma hex4_range : forall l v, length l = 4%nat -> PjGrammar.hex4 l = Some v -> 0 <= v < 65536.
Proof.
  intros [|h0 [|h1 [|h2 [|h3 [|? ?]]]]] v Hl H; try discriminate.
  rewrite <- psd_acc_hex4 in H. pose proof (psd_acc_range _ _ H) as Hr. cbn [length Z.of_nat] in Hr.
  change (16 ^ Z.of_nat 4) with 65536 in Hr. lia.
Qed.

(* a four-byte window of the text is a source window of its own *)
Lemma src_rd4 : forall (W : world segs) mem D x l,
  src_rd W mem (pi_text D) (pi_tb D) -> pi_text D <= x -> x + 4 <= pi_text D + Z.of_nat (length (pi_tb D)) ->
  length l = 4%nat -> (forall j, (j < 4)%nat -> nth j l 0 = tb_at D (x + Z.of_nat j)) -> src_rd W mem x l.
Proof.
  intros W mem D x l (Hb & H4096 & Hc & Ham & Hra & Hhu) Hx Hx4 Hl Hn.
  unfold src_rd. rewrite Hl.
  split; [|split; [lia|split; [lia|split; [|split]]]].
  - intros j Hj. rewrite Hl in Hj. rewrite (Hn j Hj).
    destruct (garr8_at _ (pi_text D) (pi_tb D) (x + Z.of_nat j) Hb ltac:(lia)) as [V R]. split; [exact V | exact R].
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ SHADOW_OFF (pi_text D) (Z.of_nat (length (pi_tb D)))); [exact Hra | lia | lia].
  - intros _. apply (psrc_hull_sub _ (pi_text D) (Z.of_nat (length (pi_tb D)))); [apply Hhu; lia | lia | lia | lia].
Qed.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the invariant every cut carries (S4_PsBase.v Section gp), the kit's: no law is needed here *)
Variable P : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* IMAGE FACTS the text-across-a-call lemma takes (S4_PsSrc.v's Section hypotheses, same names): the image's
   zero-shadow ranges are granule-aligned (asyms_ok's aso_zshadow), and its shadow bytes are present *)
Hypothesis ZSA : forall q m, In (q, m) (as_zero_shadow B) -> q mod 8 = 0 /\ m mod 8 = 0.
Hypothesis IMGV : ARx_img_shadow_vis segs ARx.

(* a chain is a fact about the layout's top only: layout_le moves it *)
Lemma achain_ly : forall ly ly' (rd : reader) sp v ch,
  ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch E H. unfold achain in *. rewrite E. exact H. Qed.

(* THE FRAME CHAIN FROM q AT THE CURRENT VIEW: the walk has written only its own frame and the new block, and the
   caller's cursor word at q still holds p (pj_in_okR at both states), so the entry chain is the current chain. *)
Lemma chain_now : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  exists ch, achain ly (aview segs (w_H W) mem) (PS_SP D) (pi_q D) ch.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof HPRE as (HF & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & _).
  pose proof HF as ((HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _) & _ & _).
  pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof HDEC as ((k & HJ & HK & _ & _ & _ & _) & _ & _ & _ & _ & HIN & _).
  pose proof HJ as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
  pose proof asan_consts as (C1 & _).
  assert (Hag : forall a, spZ (pi_regs D) <= a < ly_top (pi_ly D) ->
    aview segs (w_H W) mem a = aview segs (w_H (pi_W D)) (pi_mem D) a).
  { intros a Ha.
    destruct (Z_le_dec (pi_q D) a) as [Hqa|Hqa].
    - destruct (Z_lt_le_dec a (pi_q D + 8)) as [Hqb|Hqb].
      + replace a with (pi_q D + Z.of_nat (Z.to_nat (a - pi_q D))) by lia. unfold aview. f_equal.
        rewrite (proj1 HIN (Z.to_nat (a - pi_q D)) ltac:(lia)).
        rewrite (proj1 HIN0 (Z.to_nat (a - pi_q D)) ltac:(lia)). reflexivity.
      + apply K1; [lia | lia|]. intros (rg & [<-|[]] & Hrg). cbn [fst snd] in Hrg. lia.
    - apply K1; [lia | lia|]. intros (rg & [<-|[]] & Hrg). cbn [fst snd] in Hrg. lia. }
  destruct (ps_chain_call D (aview segs (w_H W) mem)
    (ps_chain0_of_pre B ARx CTX CW D HPRE) (ps_qgap_of_pre B ARx CTX CW D HPRE) ltac:(lia) Hag) as (ch & HA).
  exists ch. apply (achain_ly (pi_ly D) ly); [exact Etop|].
  unfold PS_SP, PS_FRAME. exact HA.
Qed.

(* ---- a STRETCH that writes at most the out byte w: ps_at_decP at the new memory, same registers ---- *)
Lemma dec_run : forall CTX CW D ly S Hp W regs mem md out w r Q mem' md' k',
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly S Hp W mem' md' k' -> P mem' ->
  same_but_materialized md md' ->
  (forall x : word, bv_unsigned x <> w -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  ps_at_decP B ARx SK P D ly S Hp W regs mem' md' out w r Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG.
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  destruct (dec_keep B ARx SK P LAWS HW PST_ok CTX CW D ly S Hp W regs mem md out w r Q mem' md' k' HPRE HDEC HJ' HMN' Hsame HM HG)
    as (HC & HAL & V24 & V16 & V8 & HIN & HROD & HA).
  pose proof HDEC as (_ & _ & HSH & HGT & HCST & _ & _ & HSC & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr' & Hwo & Hww & Hsync).
  split; [exact HC|]. split; [exact HAL|]. split; [exact HSH|]. split; [exact HGT|].
  split.
  { destruct HCST as (C26 & C14 & C16 & C15 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C27 & C21 & C1 & _).
    split; [exact C26|]. split; [exact C14|]. split; [exact C16|]. split; [exact C15|]. split; [exact C17|].
    split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact C28|]. split; [exact C29|].
    split; [exact C30|]. split; [exact C31|]. split; [exact C27|]. split; [exact C21|]. split; [exact C1|].
    split; [exact V24|]. split; [exact V16 | exact V8]. }
  split; [exact HIN|]. split; [exact HROD|]. split; [exact HSC|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R11|]. split; [exact R8|]. split; [exact R9|].
  exists done.
  split; [|split; [exact Hdl|split; [exact HS|split; [exact HN|split; [exact Hr'|split; [exact Hwo|split; [exact Hww|exact Hsync]]]]]]].
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0.
  intros j Hj. destruct (Hbd j Hj) as [V Rg]. split; [|exact Rg].
  apply (val_mem_keep W W mem mem'); [|exact V]. intros i Hi. cbn in Hi. apply HA; lia.
Qed.

(* ---- a step that emits SEVERAL bytes at w (put_utf8's 1..4): the multi-byte twin of the kit's dec_close1, at an
   UNCHANGED memory (the bytes are already there) ---- *)
Lemma dec_closeN : forall CTX CW D ly S Hp W regs mem md out w r Q regs' r' bs,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit bs (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r')) ->
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (q + Z.to_nat (r' - r))%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r')) ->
  r < r' -> Z.of_nat (length bs) <= r' - r -> bytes_at W mem w bs ->
  ps_sh_regs D regs' -> ps_gptp D regs' -> dc_regs regs' ->
  getr regs' 2 = w64 (PS_SP D) -> getr regs' 18 = w64 out ->
  getr regs' 19 = w64 (w + Z.of_nat (length bs)) -> getr regs' 20 = w64 r' ->
  getr regs' 11 = w64 (pi_text D + pi_len D) -> getr regs' 8 = w64 (pi_q D) -> getr regs' 9 = w64 (pi_q D + 8) ->
  ps_at_decP B ARx SK P D ly S Hp W regs' mem md out (w + Z.of_nat (length bs)) r' Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs' r' bs HPRE HDEC Hstep Hscan Hrr Hblen Hbs
    HSH HGT HDC R2 R18 R19 R20 R11 R8 R9.
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & _ & _ & HCST & HIN & HROD & HSC & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr' & Hwo & Hww & Hsync).
  destruct (psd_scan_sync _ _ _ _ Hscan Hsync) as [Hsync' Hle].
  split; [exists k; split; [exact HJ|split; [exact HK|split; [exact HSV|split; [exact HSRC|split; [exact HHOME | exact HMN]]]]]|].
  split; [exact HAL|]. split; [exact HSH|]. split; [exact HGT|].
  split.
  { destruct HDC as (D26 & D14 & D16 & D15 & D17 & D5 & D6 & D7 & D28 & D29 & D30 & D31 & D27 & D21 & D1).
    destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V24 & V16 & V8).
    split; [exact D26|]. split; [exact D14|]. split; [exact D16|]. split; [exact D15|]. split; [exact D17|].
    split; [exact D5|]. split; [exact D6|]. split; [exact D7|]. split; [exact D28|]. split; [exact D29|].
    split; [exact D30|]. split; [exact D31|]. split; [exact D27|]. split; [exact D21|]. split; [exact D1|].
    split; [exact V24|]. split; [exact V16 | exact V8]. }
  split; [exact HIN|]. split; [exact HROD|]. split; [exact HSC|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R11|]. split; [exact R8|]. split; [exact R9|].
  exists (done ++ bs). split.
  - intros j Hj. rewrite length_app in Hj.
    destruct (Nat.lt_ge_cases j (length done)) as [Hjl|Hjl].
    + rewrite app_nth1 by exact Hjl. exact (Hbd j Hjl).
    + rewrite app_nth2 by exact Hjl.
      destruct (Hbs (j - length done)%nat ltac:(lia)) as [V Rg]. split; [|exact Rg].
      replace (out + Z.of_nat j) with (w + Z.of_nat (j - length done)) by lia. exact V.
  - split; [rewrite length_app; lia|].
    split; [exact (proj1 (psd_rel_step _ _ _ _ _ (conj HS HN) Hstep))|].
    split; [exact (proj2 (psd_rel_step _ _ _ _ _ (conj HS HN) Hstep))|].
    split; [lia|]. split; [lia|]. split; [lia|].
    rewrite Hsync'. f_equal. lia.
Qed.

(* ---- a CALL of a NON-ALLOCATING callee (hex4 at offset 988, put_utf8 at 1044): ps_at_decP at the post state, with
   the SAME register file (the cut's register clauses speak of regs alone, so the walk re-states them at the leaf
   with dec_closeN / free_close). The callee's footprint FP1 is parse_string's own hex4 slot (sp + 36, inside the
   caller window e1) or the bytes put_utf8 writes at the write cursor w (inside the block fuzz_malloc made). The
   callee leaves the allocator state alone (S' = S in the cut's texts, since the kit walkkit 0afb3f76c28), which is what
   carries room_live_cf and ps_rpos across; its ablocks and hidden heads are the call state's. ---- *)
Lemma dec_call : forall CTX CW D ly S Hp W regs mem md out w r Q STK1 e1 FP1 ly2 W2 mem2 md2 k2 k3,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  ajournal_x (SK := SK) segs B prh_pst ARx (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)]
    (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) [] ly2 S Hp W2 mem2 md2 k3 ->
  ajournal_x (SK := SK) segs B prh_pst ARx (STK1 + e1) (PS_SP D + e1) FP1
    ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k2 ->
  (forall a, PS_SP D <= a < PS_SP D + e1 -> ~ inFP FP1 a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  0 <= e1 <= 144 -> 0 <= STK1 -> 144 + STK1 <= STK_parse_string ->
  (forall a, inFP FP1 a -> (PS_SP D + 32 <= a < PS_SP D + 40) \/ (w <= a < out + Z.of_nat Q + 1)) ->
  ablocks B ly2 S = ablocks B ly S ->
  prh_ledger B ly2 S Hp W2 mem2 ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D) (pi_most D) (pi_own D) ->
  P mem2 ->
  ps_at_decP B ARx SK P D ly2 S Hp W2 regs mem2 md2 out w r Q.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q STK1 e1 FP1 ly2 W2 mem2 md2 k2 k3
    HPRE HDEC HJ2 HJc HX He1 HSTK1 HSTK HFP1 EAB HLED2 HMN2.
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof asan_consts as (CC1 & _). pose proof cf_head_nonneg as Hh0. pose proof (ps_head8 HW) as Hh8.
  pose proof ps_stk144 as Hs144.
  pose proof HPRE as (HF & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & _ & _ & HWIN & Hq1 & Hq2 & _).
  pose proof HF as ((HAR0 & _ & _ & _ & _ & Hstk0 & _ & _ & _) & _ & _).
  pose proof HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN) & HAL & HSH & HGT & HCST & HIN & HROD & HSC
    & R2 & R18 & R19 & R20 & R11 & R8 & R9 & HREL).
  pose proof HAL as (Hcnt & Hout4 & Hout16 & EHp & Eab & HLED & HVIS & HRL & HRPOS & Hbb).
  pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jpres & _).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  assert (Hin_o2 : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly2 S)) by (rewrite EAB; exact Hin_o).
  assert (Hhd : In (out - cf_head) Hp) by (rewrite EHp; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & Hpres & _).
  rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ by lia.
  (* the footprint misses parse_string's saved registers, its three constants, the caller's cursor and the done bytes *)
  assert (HnFP : forall a, PS_SP D <= a -> ~ (PS_SP D + 32 <= a < PS_SP D + 40) -> ~ inFP FP1 a).
  { intros a Ha Hne Hf. destruct (HFP1 a Hf) as [Hs|Hb]; [exact (Hne Hs) | lia]. }
  assert (HnFPo : forall a, out - cf_head <= a < w -> ~ inFP FP1 a).
  { intros a Ha Hf. destruct (HFP1 a Hf) as [Hs|Hb]; lia. }
  assert (Hst : forall a, PS_SP D <= a < 2 ^ 64 -> ~ inFP FP1 a ->
    aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha Hf. destruct (Z_lt_le_dec a (PS_SP D + e1)) as [Hl|Hl]; [apply HX; [lia | exact Hf]|].
    apply F1; lia. }
  assert (Hst40 : forall a, PS_SP D + 40 <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply Hst; [lia | apply HnFP; lia]).
  assert (Hst8 : forall a, PS_SP D + 8 <= a < PS_SP D + 32 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply Hst; [lia | apply HnFP; lia]).
  assert (Hblk : forall a, out - cf_head <= a < out + Z.of_nat Q + 1 -> ~ inFP FP1 a ->
    aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha Hf. replace a with (out - cf_head + (a - (out - cf_head))) by lia.
    apply (F2 (out - cf_head) (Z.of_nat Q + 1 + cf_head)); [exact Hin_o | exact Hin_o2 | rewrite ps_req by lia; lia|].
    replace (out - cf_head + (a - (out - cf_head))) with a by lia. exact Hf. }
  assert (Hnosink : ~ YI16.sink_open_fp FP1).
  { intros Hs. assert (Hf : inFP FP1 0) by (destruct Hs as (rg & Hrg & Hb); exists rg; split; assumption).
    destruct (HFP1 0 Hf) as [Hs0|Hb0]; lia. }
  (* the text across the call *)
  assert (HFPtxt : forall a, inFP FP1 a -> ~ (pi_text D <= a < pi_text D + Z.of_nat (length (pi_tb D)))).
  { intros a Hf Ht. rewrite Hlen in Ht. destruct (HFP1 a Hf) as [Hs|Hb]; [lia|]. destruct (Hap a Ht); lia. }
  assert (HL1 : forall b m, In (b, m) (pi_Lam D) -> In (b - cf_head, m + cf_head) (ablocks B ly S)).
  { intros b m Hin. pose proof HLED as HFa; apply ps_led_blocks in HFa.
    pose proof (proj1 (Forall_forall _ _) HFa (b, m) (or_intror Hin)) as Hb. cbn [fst snd] in Hb.
    exact (proj1 (proj2 Hb)). }
  assert (HL2 : forall b m, In (b, m) (pi_Lam D) ->
    0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B ly2 S) /\ In (b - cf_head) Hp).
  { intros b m Hin. pose proof HLED2 as HFa; apply ps_led_blocks in HFa.
    pose proof (proj1 (Forall_forall _ _) HFa (b, m) (or_intror Hin)) as Hb. cbn [fst snd] in Hb.
    split; [exact (proj1 Hb)|]. split; [exact (proj1 (proj2 Hb)) | exact (proj1 (proj2 (proj2 Hb)))]. }
  assert (HHp : forall h, In h Hp -> exists kk, 0 <= kk /\ In (h, kk) (ablocks B ly2 S)).
  { intros h Hh. pose proof HLED2 as HFa; apply ps_led_blocks in HFa. pose proof HLED2 as HPerm; apply ps_led_heads in HPerm.
    assert (Hm : In h (map (fun ak => fst ak - cf_head) ((out, Z.of_nat Q + 1) :: pi_Lam D)))
      by (apply (Permutation_in _ HPerm); exact Hh).
    apply in_map_iff in Hm as ([b m] & Eh & Hin).
    pose proof (proj1 (Forall_forall _ _) HFa (b, m) Hin) as Hb. cbn [fst snd] in Eh, Hb.
    exists (m + cf_head). split; [pose proof (proj1 Hb); lia|]. rewrite <- Eh. exact (proj1 (proj2 Hb)). }
  assert (Hnew : ~ In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B (pi_ly D) (pi_S D))).
  { apply (ps_newblk B ARx LAWS ly S (pi_ly D) (pi_S D) Hp W mem md
      (out - cf_head, Z.of_nat Q + 1 + cf_head) HAR); [cbn [snd]; lia | exact Eab]. }
  rewrite <- Hlen in HHOME.
  destruct (ps_src_after_call B ARx SK LAWS ZSA IMGV (STK1 + e1) (PS_SP D + e1) FP1
      ly S Hp W mem md ly2 S Hp W2 mem2 md2 k2 (pi_Lam D) (pi_text D) (pi_tb D)
      HJc HSRC HHOME HFPtxt Hnosink
      ltac:(intros p n Hin Hnh; split; [rewrite EAB; exact Hin | exact Hnh])
      HL1 HL2 HHp) as [HSRC2 HHOME2].
  rewrite Hlen in HHOME, HHOME2.
  (* ---- the cut's clauses at the post state ---- *)
  split.
  { exists k3. split; [exact HJ2|]. split.
    - apply (cj_kept_trans SK segs B prh_pst ARx cf_head LAWS STK_parse_string (spZ (pi_regs D))
        (STK1 + e1) (PS_SP D + e1) [(pi_q D, pi_q D + 8)] [] FP1 []
        (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) ly S Hp W mem md ly2 S W2 mem2 md2);
      [ exact HK
      | exact (cj_kept_of_journal SK segs B prh_pst ARx (STK1 + e1) (PS_SP D + e1) FP1 ly S Hp W mem md
                 ly2 S Hp W2 mem2 md2 k2 [(pi_q D, pi_q D + 8)] HJc)
      | exact HAR0 | exact HAR | lia | lia
      | intros a Ha; exfalso; exact (inFP_nil a Ha)
      | intros a Ha; destruct (HFP1 a Ha) as [Hs|Hb];
        [ right; right; lia
        | right; left; exists (out - cf_head), (Z.of_nat Q + 1 + cf_head);
          split; [exact Hin_o|];
          split; [ exact Hnew
                 | rewrite ps_req by lia; lia ] ] ].
    - split; [|split; [exact HSRC2 | split; [exact HHOME2 | exact HMN2]]].
      unfold ps_saved in *. destruct HSV as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split;
        (eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst40; cbn in Hi; lia | eassumption]). }
  split.
  { split; [exact Hcnt|]. split; [exact Hout4|]. split; [exact Hout16|]. split; [exact EHp|].
    split; [rewrite EAB; exact Eab|]. split; [exact HLED2|].
    split; [|split; [exact HRL | split; [exact HRPOS | exact Hbb]]].
    destruct (HSHADOW B ARx LAWS ly2 S Hp W2 mem2 md2 (out - cf_head) (Z.of_nat Q + 1 + cf_head)
                HAR2 Hin_o2 Hhd) as [Hbs2 Hhu2].
    rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hbs2, Hhu2 by lia.
    replace (out - cf_head + cf_head) with out in Hbs2, Hhu2 by lia.
    replace (Z.of_nat Q + 1 + cf_head - cf_head) with (Z.of_nat Q + 1) in Hbs2, Hhu2 by lia.
    split; [eapply block_shadow_range; [exact Hbs2 | lia | lia] | intros _; apply Hhu2; lia]. }
  split; [exact HSH|]. split; [exact HGT|].
  split.
  { destruct HCST as (C26 & C14 & C16 & C15 & C17 & C5 & C6 & C7 & C28 & C29 & C30 & C31 & C27 & C21 & C1 & V24 & V16 & V8).
    split; [exact C26|]. split; [exact C14|]. split; [exact C16|]. split; [exact C15|]. split; [exact C17|].
    split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact C28|]. split; [exact C29|].
    split; [exact C30|]. split; [exact C31|]. split; [exact C27|]. split; [exact C21|]. split; [exact C1|].
    split; [eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst8; cbn in Hi; lia | exact V24]|].
    split; [eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst8; cbn in Hi; lia | exact V16]
           |eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst8; cbn in Hi; lia | exact V8]]. }
  split.
  { destruct HIN as (Vp & Ve & Vd & Hrw & Hq8' & Ht0' & Ht62 & Htp' & Hlentb & Hg & Hqt & Hd).
    split; [eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst40; cbn in Hi; lia | exact Vp]|].
    split; [eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst40; cbn in Hi; lia | exact Ve]|].
    split; [eapply (val_mem_keep W W2 mem mem2); [intros i Hi; apply Hst40; cbn in Hi; lia | exact Vd]|].
    split; [intros x Hx; apply (apresent_writable segs); apply Jpres; unfold PS_WSP, PS_WSTK; lia|].
    do 5 (split; [assumption|]). split; [exact (proj1 HSRC2)|]. split; assumption. }
  split.
  { intros a Hro Hno Her.
    rewrite (F3 a (psrc_ro_img a Hro) Hno Her (fun Hx => prh_pst_not_ro a Hx Hro) (fp_spares_closed FP1 a Hnosink)).
    exact (HROD a Hro Hno Her). }
  split; [exact HSC|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R11|]. split; [exact R8|]. split; [exact R9|].
  destruct HREL as (done & Hbd & Hdl & HS & HN & Hr' & Hwo & Hww & Hsync).
  exists done.
  split; [|split; [exact Hdl|split; [exact HS|split; [exact HN|split; [exact Hr'|split; [exact Hwo|split; [exact Hww|exact Hsync]]]]]]].
  intros j Hj. destruct (Hbd j Hj) as [V Rg]. split; [|exact Rg].
  apply (val_mem_keep W W2 mem mem2); [|exact V]. intros i Hi. cbn in Hi.
  apply Hblk; [lia | apply HnFPo; lia].
Qed.

End u.
