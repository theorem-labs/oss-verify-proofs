(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 1110 of its 1140 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PSB_Tail.v, with its module paths and module names changed; 2151 of its 2263 lines of code are new or changed and 1028 lines of the source are left out. *)
(* fuzz_preset lib/B, parse_string on image B (asan-ubsan): the DECODE LOOP BODY stretch of the walk, proved against
   the cut layer lib/A/Prog/PS_Gen.v + lib/B/Prog/PSB_Base.v: psb_dec_step_holds (psb_dec_lt m -> psb_dec_lt (S m)),
   ending in ps_postR (wle' segs RZ_cf) CW D (SRr' segs RZ_cf: the turn may reach the bad escape's fuzz_free).
   rule 24: proves no function (kind: segment lemma). The function is parse_string B (lane BParseString); its reuse
   search is the record file r24-index.txt (sha256 e7c12b08eeb1; internal record) (checker CONFIRM; donor none;
   templates T1 the released plain / UBSan walks, T2 the OLD image-B walk, T3 WalkS4's image-A cut layer).
   GENERIC-P FORM (the internal file GP-BRIEF.md, a Theorem Labs lane 12:18Z / 12:22Z): base 3d53a181c75 (a working branch;
   PS_Gen ba0681112ea5, PSB_Base 73bed5b3d393, YSRrMemnorm a1c1ece77b14, YAkMemnorm 96c72061b4d4). Reason: an SRr post is
   OPAQUE once Qed, so an end-state invariant must be in the segment's statement. psb_dec_step_holdsP is over an
   abstract P with srr_inv_laws segs P only (the stretch makes no kit call, so no srr_inv_call / srr_inv_mn); every
   run is the invariant twin (paj_run_x_inv / paj_run_to_x_inv at P, PLAW); P mem is ps_carryP's last conjunct at
   each exit, from the run's end keep. The old psb_dec_step_holds is kept, statement byte-identical (it did NOT move),
   as the corollary at P := fun _ => True. Ported from the concrete memnorm port a working branch
   preset-tree-at-2026-10-29T12-18-41Z.tsv (sha256 01b6eb28a24f; internal record) (ps_mn D -> P, ps_mn_laws D -> PLAW).
   Proved first on base 8860ed3a414 (the kit walkkit 0afb3f76c28; blobs re-derived by git rev-parse at that sha:
   PRH_FnReader ba3a5407e12b, PS_Gen 8fe447f77d55, PSB_Base fd79fd54d991, YCbqG 83da015952be, A Listing_prog v4
   cbba047f885a, B Listing_prog f843fdf7fe2f). Section hypotheses taken: LAWS, PST_ok, HW (prh_head_wide, WalkS4's
   form; the harness heads below the out block); no callee text (the stretch makes no call); TL not needed.
   THE CODE (the neutral listing parse_string.fuzz_preset.asan-ubsan.s (sha256 549ddc2d23bf; internal record); every offset below is a
   DERIVED byte offset from parse_string's B entry, never an address):
     324  DEC    srli a1, s4, 3; add a1, a1, s7; lb a2, 0(a1); bnez a2 -> 1080 (partial granule, back to 340)
     340         lbu a2, 0(s4); beq a2, s9 -> 1324 (PSB_RETOK: the closing quote)
     348         lb a1, 0(a1); bnez a1 -> 1092 (partial granule, back to 356)
     356         lbu a1, 0(s4); bltu a1, a4 -> 1248 (PSB_FREE: a control byte; decode refuses)
     364         addi s5, s4, 1; bne a1, s11 -> 508 (a plain byte)
     372         beq s4, s10 -> 1372 (UBSan, not taken); bgeu s5, a0 -> 1248; beq s5, s10 -> 1372 (UBSan)
     384         srli a1, s5, 3; ..; lb a1, 0(a1); bnez a1 -> 1116; lbu a1, 0(s5); addi s5, s4, 2
     408         the escape compare tree (bge a5, a1 / bge a7, a1 / beq a1, t0 / beq a1, 116 / bne a1, 117 -> 1248)
     436  U      the \u escape (PSB_U)
     508         the plain byte: beq s4, s10 / beq s3, s10 (UBSan), the store shadow check, addi a0, s3, 1
     536         sb a1, 0(s3)
     540  JOIN   mv s3, a0; lbu a0, 0(s8); bnez a0 -> 1408; ld a0, 0(s1); mv s4, s5; bltu s5, a0 -> 324 (else 1248)
     568..864   the eight escape arms (34 92 47 98 102 110 114 116), each with its own store, all rejoining 536 / 540
   Every UBSan check of the stretch (`beq s4, s10`, `beq s5, s10`, `beq s3, s10`, at the `unimp` of offset 1372) is
   DECIDED NOT TAKEN by the engine from the atom ranges of s3 / s4 / s5 (the cursor and the out pointer are far below
   2 ^ 64 - 1); every ASan shadow check is not taken because the shadow byte of the text (src_rd), of q + 8
   (range_addressable q 24) and of the out byte (ps_alloc's prhReader_vis) is 0.
   Numerals: the offsets above (DERIVED: byte offsets inside parse_string); register numbers 2 5 8 9 10 14 15 16 17 18
   19 20 21 22 23 24 25 26 27 (WORD); the decode constants 34 92 32 101 91 113 114 116 117 47 98 102 110 and the
   stored bytes 8 9 10 12 13 (WORD: characters, the listing's li immediates); -1 (WORD: s10); atom indices 0 .. 33 and
   512 (DERIVED: the symbolic engine's numbering, A_LIM the first token atom); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 63 /
   2 ^ 64 (DERIVED: the shadow span, the stack band, machine words); 4096 / 255 / 256 / 8 / 16 / 24 / 144 (LENGTH).
   PSB_OFF + 324 / 384 / 436 / 540 / 1248 / 1324 (DERIVED: the form pmkst leaves after `BASE +`; psb_pc_fold below
   COMPUTES each by vm_compute and replaces it by psb_pc PSB_*, so no slot-derived numeral is typed: the #102
   relocation moved PSB_OFF from 26172 to 27184, and the old typed 26496 .. 27496 were stale); 540 / 384 (DERIVED:
   PSB_JOIN / PSB_ESC, offsets inside parse_string). 32 / 33 / 512 / 513 (DERIVED: atom indices).
   No ADDRESS literal: every address is a psb_pc / PSB_* of PSB_Base.v or a pa_val / pa_sigma of lib/B/PAImg_prog.v. *)
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
(* the memnorm keep: the cut's YSRrMemnorm.v 5ffa8525936b (its runner twins moved to YC1fPx.v); override-free *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PS_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PSB_Base.
(* NOT REQUIRED HERE: lib/Spec/PsDecStep.v and lib/Prog/ps_seg_*.v state the same one-step decode facts, but they pull
   in lib/Lib, whose LiaTwx2.v REDEFINES `lia` to a hypothesis-pruning variant (`Ltac lia ::= first [..]`) that fails
   on this file's stack / ceiling goals. The five decode steps and the signed-compare bridge are restated below. *)
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the loop's measure falls by at least one byte. `lia` is the pruning variant in this unit's Import chain and does
   not split nat subtraction, so the step is spelled with Nat's own lemmas. *)
Lemma pdc_meas_step : forall Q a b m : nat, (a < Q)%nat -> (1 <= b)%nat -> (Q - a < Nat.succ m)%nat ->
  (Q - a - b < m)%nat.
Proof.
  intros Q a b m H1 H2 H3.
  assert (Hd : (1 <= Q - a)%nat) by (apply Nat.le_add_le_sub_l; rewrite Nat.add_1_r; exact H1).
  assert (Hdm : (Q - a <= m)%nat) by (apply Nat.lt_succ_r; exact H3).
  destruct (Nat.le_gt_cases b (Q - a)) as [Hle|Hgt].
  - apply (Nat.lt_le_trans _ (Q - a)); [|exact Hdm].
    apply Nat.sub_lt; [exact Hle | exact (Nat.lt_le_trans 0 1 b Nat.lt_0_1 H2)].
  - rewrite (proj2 (Nat.sub_0_le (Q - a) b)) by (apply Nat.lt_le_incl; exact Hgt).
    exact (Nat.lt_le_trans 0 1 m Nat.lt_0_1 (Nat.le_trans 1 (Q - a) m Hd Hdm)).
Qed.

(* ---- the model layer: one decode / scan step of the loop (PjGrammar over PRH_Reader's rest_atR) ---- *)
Lemma pdc_rest_cons : forall tb text x c, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c ->
  rest_atR tb text x = c :: rest_atR tb text (x + 1).
Proof.
  intros tb text x c Hx Hc. unfold rest_atR.
  assert (Hs : forall (l : list Z) k c0, nth_error l k = Some c0 -> skipn k l = c0 :: skipn (S k) l).
  { intros l. induction l as [|h t IH]; intros [|k] c0 H; cbn in *; try discriminate;
      [injection H as -> ; reflexivity | exact (IH k c0 H)]. }
  rewrite (Hs _ _ c Hc). replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia. reflexivity.
Qed.
Lemma pdc_rest_nth : forall tb text x, text <= x < text + Z.of_nat (length tb) ->
  nth_error tb (Z.to_nat (x - text)) = Some (nth (Z.to_nat (x - text)) tb 0).
Proof.
  intros tb text x Hx. apply nth_error_nth'. lia.
Qed.
Lemma pdc_scan_plain : forall b x, b <> 34 -> b <> 92 -> PjGrammar.scan (b :: x) = option_map S (PjGrammar.scan x).
Proof.
  intros b x H34 H92. cbn [PjGrammar.scan].
  rewrite (proj2 (Z.eqb_neq b 34) H34), (proj2 (Z.eqb_neq b 92) H92). reflexivity.
Qed.
Lemma pdc_scan_esc : forall e x, PjGrammar.scan (92 :: e :: x) = option_map (fun q => S (S q)) (PjGrammar.scan x).
Proof. intros e x. reflexivity. Qed.

(* one decode step, as the loop's four exits take it (PjGrammar.decode's own cases) *)
Lemma pdc_dec_quote : forall x, PjGrammar.decode (34 :: x) = Some ([], x).
Proof. intros x. reflexivity. Qed.
Lemma pdc_dec_ctl : forall b x, b <> 34 -> b < 32 -> PjGrammar.decode (b :: x) = None.
Proof.
  intros b x H34 H32. cbn [PjGrammar.decode].
  rewrite (proj2 (Z.eqb_neq b 34) H34), (proj2 (Z.ltb_lt b 32) H32). reflexivity.
Qed.
Lemma pdc_dec_plain : forall b x, b <> 34 -> 32 <= b -> b <> 92 ->
  PjGrammar.decode (b :: x) = PjGrammar.emit [b] (PjGrammar.decode x).
Proof.
  intros b x H34 H32 H92. cbn [PjGrammar.decode].
  rewrite (proj2 (Z.eqb_neq b 34) H34), (proj2 (Z.ltb_ge b 32) H32), (proj2 (Z.eqb_neq b 92) H92).
  reflexivity.
Qed.
Lemma pdc_dec_esc : forall e c x, e <> 117 -> PjGrammar.escape e = Some c ->
  PjGrammar.decode (92 :: e :: x) = PjGrammar.emit [c] (PjGrammar.decode x).
Proof.
  intros e c x Hu He. cbn [PjGrammar.decode]. rewrite (proj2 (Z.eqb_neq e 117) Hu), He. reflexivity.
Qed.
Lemma pdc_dec_esc_bad : forall e x, e <> 117 -> PjGrammar.escape e = None ->
  PjGrammar.decode (92 :: e :: x) = None.
Proof.
  intros e x Hu He. cbn [PjGrammar.decode]. rewrite (proj2 (Z.eqb_neq e 117) Hu), He. reflexivity.
Qed.

(* ---- the branch bridges the engine leaves: the signed pair (bge / blt) and the literal compares ---- *)
Lemma pdc_lts_lit : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit.
  rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id b) by (unfold M64; lia).
  rewrite (swrap64_id a) by (unfold half64; lia). rewrite (swrap64_id b) by (unfold half64; lia).
  reflexivity.
Qed.
Lemma pdc_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
  intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, Z.add_0_r, unsigned_lit_small by exact Hv.
  reflexivity.
Qed.
Lemma pdc_br_ge : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit c)) (sv_denot E (SOff n 0)) = negb (c <? v).
Proof.
  intros E n v c Hn Hv Hc. cbn [branch_taken]. rewrite (pdc_denot_atom E n v Hn ltac:(lia)).
  change (sv_denot E (SLit c)) with (Z_to_bv 64 c). rewrite (pdc_lts_lit c v Hc Hv). reflexivity.
Qed.
Lemma pdc_br_lt : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit c)) (sv_denot E (SOff n 0)) = (c <? v).
Proof.
  intros E n v c Hn Hv Hc. cbn [branch_taken]. rewrite (pdc_denot_atom E n v Hn ltac:(lia)).
  change (sv_denot E (SLit c)) with (Z_to_bv 64 c). exact (pdc_lts_lit c v Hc Hv).
Qed.
Lemma pdc_br_eq : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v =? c).
Proof.
  intros E n v c Hn Hv Hc. rewrite branch_eq_U. unfold U.
  rewrite (pdc_denot_atom E n v Hn Hv). change (sv_denot E (SLit c)) with (Z_to_bv 64 c).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pdc_br_eq_atoms : forall E n m v u, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 u ->
  0 <= v < 2 ^ 64 -> 0 <= u < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = (v =? u).
Proof.
  intros E n m v u Hn Hm Hv Hu. rewrite branch_eq_U. unfold U.
  rewrite (pdc_denot_atom E n v Hn Hv), (pdc_denot_atom E m u Hm Hu).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pdc_br_ltu : forall E n m v u, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 u ->
  0 <= v < 2 ^ 64 -> 0 <= u < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff n 0)) (sv_denot E (SOff m 0)) = (v <? u).
Proof.
  intros E n m v u Hn Hm Hv Hu. rewrite branch_ltu_U. unfold U.
  rewrite (pdc_denot_atom E n v Hn Hv), (pdc_denot_atom E m u Hm Hu).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pdc_br_ltu_lit : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (v <? c).
Proof.
  intros E n v c Hn Hv Hc. rewrite branch_ltu_U. unfold U.
  rewrite (pdc_denot_atom E n v Hn Hv). change (sv_denot E (SLit c)) with (Z_to_bv 64 c).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma pdc_br_ne : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = negb (v =? c).
Proof.
  intros E n v c Hn Hv Hc. rewrite branch_ne_U. unfold U.
  rewrite (pdc_denot_atom E n v Hn Hv). change (sv_denot E (SLit c)) with (Z_to_bv 64 c).
  rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pdc_br_geu_off : forall E n m v u z, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 u ->
  0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 -> 0 <= u < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff n z)) (sv_denot E (SOff m 0)) = negb (v + z <? u).
Proof.
  intros E n m v u z Hn Hm Hv Hvz Hu. rewrite branch_geu_U. unfold U.
  cbn [sv_denot]. rewrite Hn, Hm, Z.add_0_r.
  rewrite (unsigned_lit_small v) by lia. rewrite (unsigned_lit_small u) by lia.
  rewrite (unsigned_lit_small (v + z)) by lia. rewrite (unsigned_lit_small u) by lia. reflexivity.
Qed.
(* a register the engine holds as an atom with a constant offset *)
Lemma pdc_off_val : forall E n v z, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (ew E n) + z) = w64 (v + z).
Proof. intros E n v z Hn Hv Hvz. rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.

(* ---- a value appears at most once in a list the allocator keeps pairwise disjoint ---- *)
Lemma pdc_pw_mid : forall {X : Type} (R : X -> X -> Prop) l1 x l2 y, pairwise R (l1 ++ x :: l2) -> In y l1 -> R y x.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros x l2 y Hpw Hin; cbn in Hpw, Hin; [destruct Hin|].
  destruct Hpw as [HF Hpw]. destruct Hin as [->|Hin].
  - apply (proj1 (Forall_forall _ _) HF x). apply in_or_app. right. left. reflexivity.
  - exact (IH x l2 y Hpw Hin).
Qed.

(* ---- THE SYMBOLIC LAYOUT at the decode loop head (atoms: 0 .. 31 the registers AT the cut, 32 the text byte at r,
   33 the text byte at r + 1; the shadow base is s7's atom 23) ----
     rg_in  = q + 8 + [0, 8)   read-only: in->end (= text + len, the cut's a0, atom 10)
     rg_t i = r + [i, i + 1)   read-only: the text byte (atom 32 + i), the second only once r + 1 < end is known
     rg_o   = w + [0, 1)       WRITABLE: the out byte the loop stores, in the block fuzz_malloc made *)
Definition pdc_Bx : sv := SOff 23 0.
Definition pdc_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pdc_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 23 0).
Definition pdc_rg_in : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 10 0))].
Definition pdc_rg_t (i : Z) (n : nat) : YP09.region :=
  YP09.mkRegion (Some 20%nat) i (i + 1) 0 0 [YP09.mkChunk i (CVal 1 (SOff n 0))].
Definition pdc_rg_o : YP09.region := YP09.mkRegion (Some 19%nat) 0 1 0 1 [].
(* the escape byte, addressed through s5 = r + 1 (atom 21), the way the engine resolves `lbu a1, 0(s5)` *)
Definition pdc_rg_t5 : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
(* the registers the prologue block pinned and the loop keeps: s8 the shadow cell of q + 8, s9 34, s10 -1, s11 92,
   a4 32, a5 101, a6 91, a7 113, t0 114 *)
Fixpoint pdc_pins (l : list (bv 5 * sv)) (s : list sv) : list sv :=
  match l with [] => s | (r, e) :: l' => pdc_pins l' (sr_set s r e) end.
Definition pdc_pin_dec : list (bv 5 * sv) :=
  [(24%bv, pdc_shx 9); (25%bv, SLit 34); (26%bv, SLit (-1)); (27%bv, SLit 92); (14%bv, SLit 32); (15%bv, SLit 101);
   (16%bv, SLit 91); (17%bv, SLit 113); (5%bv, SLit 114)].
Definition pdc_afacts : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (19%nat, mkAF 4096 (2 ^ 47 - 64) 0); (20%nat, mkAF 0 (2 ^ 47 - 64) 0);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)].
Definition pdc_SH : list shent := [mkSHE 19 0 1].
Definition pdc_regs_of (bs : bool) : smem :=
  if bs then [pdc_rg_in; pdc_rg_t 0 32; pdc_rg_t 1 33; pdc_rg_o] else [pdc_rg_in; pdc_rg_t 0 32; pdc_rg_o].
Definition pdc_ss (bs : bool) : sstate :=
  mkSS (PSB_OFF + PSB_DEC) (pdc_pins pdc_pin_dec sr_atoms) (pdc_regs_of bs) None (mkFacts pdc_afacts [] []).
(* ---- THE LOOP TAIL (JOIN, DERIVED offset 540): `mv s3, a0` with a0 = w + 1, the q + 8 shadow re-check, a0 =
   in->end, `mv s4, s5`, and the back edge `bltu s5, a0` to the decode head. Every store path of the body reaches it,
   so the rejoin is proved ONCE. Atoms: 0 .. 31 the registers at 540, 32 the end pointer (in->end). ---- *)
Definition PSB_JOIN : Z := 540.
Definition pdc_rg_in_t : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition pdc_afacts_t : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition pdc_pin_t : list (bv 5 * sv) := [(24%bv, pdc_shx 9)].
Definition pdc_ss_t : sstate :=
  mkSS (PSB_OFF + PSB_JOIN) (pdc_pins pdc_pin_t sr_atoms) [pdc_rg_in_t] None (mkFacts pdc_afacts_t [] []).
(* ---- THE ESCAPE SUBTREE (DERIVED offset 384): the shadow check of text[r + 1], the escape byte, s5 = r + 2 and
   the compare tree. Atoms as at the decode head, plus 21 for s5 = r + 1. ---- *)
Definition PSB_ESC : Z := 384.
Definition pdc_afacts_e : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (19%nat, mkAF 4096 (2 ^ 47 - 64) 0); (20%nat, mkAF 0 (2 ^ 47 - 64) 0);
   (21%nat, mkAF 0 (2 ^ 47 - 64) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0)].
Definition pdc_ss_e : sstate :=
  mkSS (PSB_OFF + PSB_ESC) (pdc_pins pdc_pin_dec sr_atoms) [pdc_rg_in; pdc_rg_t5; pdc_rg_o] None
    (mkFacts pdc_afacts_e [] []).

(* ---- the register / region / fact building blocks (WalkS4's S4_PsDecKit.v shapes, image B's atoms) ---- *)
Lemma pdc_regs_ok_pin : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e H He r'. destruct (bv_eqb r 0) eqn:Hr0.
  - unfold sr_set. rewrite Hr0. apply H.
  - destruct (decide (r' = r)) as [->|Hne].
    + rewrite sr_get_set_same by exact Hr0. exact He.
    + rewrite sr_get_set_other by exact Hne. apply H.
Qed.
Lemma pdc_regs_ok_pins : forall E l s regs,
  regs_ok E s regs -> Forall (fun p => getr regs (fst p) = sv_denot E (snd p)) l -> regs_ok E (pdc_pins l s) regs.
Proof.
  intros E l. induction l as [|[r e] l IH]; intros s regs H Hl; cbn [pdc_pins]; [exact H|].
  apply Forall_cons_iff in Hl as [He Hl]. apply IH; [|exact Hl]. apply pdc_regs_ok_pin; [exact H | exact He].
Qed.
Lemma pdc_sv_shx : forall E n a, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 47 -> ew E 23 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E (pdc_shx n) = w64 (SHADOW_OFF + a / 8).
Proof.
  intros E n a Hn Ha Hb. rewrite denot_lit_U. unfold w64. f_equal. unfold pdc_shx.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hn, Hb, !Z.add_0_r.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite (zcanon_id a) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold SHADOW_OFF, M64; lia).
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite Z.add_comm. apply zcanon_id. unfold SHADOW_OFF, M64. lia.
Qed.
(* the same, in the form prreg_norm leaves after a run *)
Lemma pdc_shx_alu : forall E n a, ew E n = w64 a -> 0 <= a < 2 ^ 47 -> ew E 23 = w64 SHADOW_OFF ->
  alu64 ALU_ADD (alu64 ALU_SRL (ew E n) (Z_to_bv 64 3)) (ew E 23) = w64 (SHADOW_OFF + a / 8).
Proof.
  intros E n a Hn Ha Hb. rewrite <- (pdc_sv_shx E n a Hn Ha Hb). unfold pdc_shx.
  cbn [sv_denot]. rewrite Hn, Hb, !Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pdc_afact_rng : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> lo <= v <= hi -> 0 <= v < 2 ^ 64 ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
  intros E n v lo hi al H Hv Hv2 Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite H, unsigned_lit_small by lia. lia.
Qed.
(* the engine extends the environment with token atoms at or above A_LIM; an old atom's value is unchanged *)
Ltac pdc_ew H := cbn [ew ewset Nat.eqb]; first [exact H | rewrite !ew_ewset_other by lia; exact H].

Lemma pdc_uval : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. lia. Qed.
(* the atom's unsigned value; the one write window (the out byte) of this stretch; the branch bridges per shape *)
Ltac pdc_uw EW := rewrite (pdc_uval _ _ _ EW ltac:(lia)).
Ltac pdc_ewr EW := cbn [ew ewset Nat.eqb]; first [rewrite EW | (rewrite !ew_ewset_other by lia; rewrite EW)].
Ltac pdc_wr1 EW :=
  intros a Hin; destruct Hin as (rr & Hin & Hrr);
  cbn [ss_mem add_cond In pdc_ss pdc_ss_e pdc_ss_t pdc_regs_of] in Hin;
  repeat (destruct Hin as [Er|Hin]; [subst rr|]); try (destruct Hin);
  cbn [pdc_rg_in pdc_rg_t pdc_rg_t5 pdc_rg_o pdc_rg_in_t YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hrr;
  lazymatch type of Hrr with
  | context [ew ?Ex 19%nat] => rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW) ltac:(lia)) in Hrr
  | _ => idtac end;
  lia.
Ltac pdc_nowr EW Hx :=
  intros Hin; destruct Hin as (rr & Hin & Hrr); apply Hx;
  cbn [ss_mem add_cond In pdc_ss pdc_ss_e pdc_ss_t pdc_regs_of] in Hin;
  repeat (destruct Hin as [Er|Hin]; [subst rr|]); try (destruct Hin);
  cbn [pdc_rg_in pdc_rg_t pdc_rg_t5 pdc_rg_o pdc_rg_in_t YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hrr;
  lazymatch type of Hrr with
  | context [ew ?Ex 19%nat] => rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW) ltac:(lia)) in Hrr
  | _ => idtac end;
  lia.
Ltac pdc_hc_eq32 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_eq Ex 32 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_ne32 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_ne Ex 32 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_ltu32 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_ltu_lit Ex 32 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_ge33 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_ge Ex 33 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_lt33 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_lt Ex 33 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_eq33 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_eq Ex 33 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.
Ltac pdc_hc_ne33 Hc c EW :=
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (pdc_br_ne Ex 33 _ c ltac:(pdc_ew EW) ltac:(lia) ltac:(lia)) in Hc end.

Section pdc. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* image B's instances (PSB_Base.v's), the ones the engine's tactics infer; every statement below names them *)
#[local] Existing Instances PSB_PrhImg PSB_PAListing PSB_PAImg.
#[local] Notation segs := (@pa_segs _ B_prog_listing PSB_PAImg).
#[local] Notation VAL := (@pa_val _ B_prog_listing PSB_PAImg).
#[local] Notation BASE := (@pa_val _ B_prog_listing PSB_PAImg A_TEXT).
#[local] Notation EB := (Eimg (L := B_prog_listing) (PI := PSB_PAImg)).
(* the pc a run leaves as `BASE + n`, n = PSB_OFF + X: n is COMPUTED here (vm_compute), never typed, because it moves
   with parse_string's listing slot (old pin 26172 + X, B' 27184 + X) *)
Ltac psb_pc_fold X :=
  let v := eval vm_compute in (PSB_OFF + X) in
  replace (BASE + v) with (psb_pc X) by (unfold psb_pc; vm_compute; reflexivity).
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
#[local] Notation PS_WSTK := (PS_WSTK (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation PS_WSP := (PS_WSP (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_x := (ps_x (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_alloc := (ps_alloc (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B).
#[local] Notation ps_pre := (ps_pre (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx).
#[local] Notation ps_gptp := (ps_gptp (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_dec_rel := (ps_dec_rel (L := B_prog_listing) (PA := PSB_PAImg)).
#[local] Notation ps_saved := (ps_saved (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg)).

(* ---- the Section hypotheses (the internal file STRETCH-BRIEF.md) ---- *)
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis PST_ok : forall a, Exists (in_zr a) prh_pst -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* The kit's ONE spelling of the head width (PRH_Base.v:233-241), discharged by a Theorem Labs lane's preset_head_wide at
   CfParams_preset (lib/A/CfParamsPreset.v:103): the harness head is at least one shadow granule wide *)
Hypothesis HW : prh_head_wide.

(* ---- THE GENERIC INVARIANT (the internal file GP-BRIEF.md; a Theorem Labs lane 12:18Z / 12:22Z): every proof below is over an ABSTRACT P with
   its run laws PLAW (srr_inv_laws, YC80x.v 14f84f225e8f); the stretch makes no call, so no srr_inv_call. The top
   (BParseString's) instantiates P once per record as PS_Gen's ps_mn D. ---- *)
Section pdcP.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
#[local] Notation ps_carry := (ps_carryP (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).
(* THE HAND-OFF FORM (PS_Gen): the leaves run at wle into ps_finP, the SRr' fact of the stretch they hand to: the
   back edge, \u and the free may cross the bad escape's fuzz_free (ps_finP_hand), the success return ends at wle
   (ps_finP_of_postP); the turn is made SRr' once, at its entry (ps_finP_SRr' in pdc_stepP) *)
#[local] Notation ps_post := (ps_finP (RL := RL) (PI := PSB_PrhImg) (L := B_prog_listing) (PA := PSB_PAImg) B ARx SK P).

(* ---- THE NUMERIC BUNDLE at the decode loop head ---- *)
Lemma pdc_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
Lemma pdc_frame : PS_FRAME = 144.
Proof. vm_compute. reflexivity. Qed.
Lemma pdc_stk144 : 144 <= STK_parse_string.
Proof. unfold Z.le. vm_compute. discriminate. Qed.
Lemma pdc_scan_len : forall tb text r k, text <= r -> PjGrammar.scan (rest_atR tb text r) = Some k ->
  r < text + Z.of_nat (length tb).
Proof.
  intros tb text r k Hr H. destruct (Z_lt_le_dec r (text + Z.of_nat (length tb))) as [Hl|Hl]; [exact Hl|].
  exfalso. unfold rest_atR in H. rewrite skipn_all2 in H by lia. discriminate.
Qed.

(* the new block is not a block of the entry state: it is appended to a list the allocator keeps pairwise disjoint *)
Lemma pdc_new_block : forall ly S Hp W mem md ly0 S0 N,
  ARx ly S Hp W mem md -> ablocks B ly S = ablocks B ly0 S0 ++ [N] -> 0 < req_size (snd N) ->
  ~ In N (ablocks B ly0 S0).
Proof.
  intros ly S Hp W mem md ly0 S0 N HAR Eab Hpos Hin.
  destruct (alx_sep segs B ARx LAWS ly S Hp W mem md HAR) as [Hpw _].
  rewrite Eab, map_app in Hpw. cbn [map] in Hpw. rewrite <- app_assoc in Hpw. cbn [app] in Hpw.
  pose proof (pdc_pw_mid zdisjoint _ _ _ (fst N, req_size (snd N)) Hpw
    (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ N Hin)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma pdc_facts : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  PS_SP D = spZ (pi_regs D) - 144 /\ YM05.alloc_ceiling <= PS_SP D /\ PS_SP D mod 16 = 0 /\
  2 ^ 46 <= spZ (pi_regs D) /\ spZ (pi_regs D) <= pi_q D /\ pi_q D + 24 <= 2 ^ 47 /\ pi_q D mod 8 = 0 /\
  0 < pi_text D /\ pi_text D <= pi_p D /\ pi_p D + 1 <= r /\ r < pi_text D + pi_len D /\
  pi_text D + pi_len D <= YM05.alloc_ceiling /\ Z.of_nat (length (pi_tb D)) = pi_len D /\
  4096 + cf_head <= out /\ out <= w /\ w <= out + Z.of_nat Q /\ out + Z.of_nat Q + 1 <= YM05.alloc_ceiling /\
  In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S) /\
  (forall a, out - cf_head <= a < out + Z.of_nat Q + 1 -> app_addr a) /\
  (forall a, out - cf_head <= a < out + Z.of_nat Q + 1 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  YM05.alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK_parse_string <= spZ (pi_regs D) /\
  spZ (pi_regs D) <= ly_stk_hi ly /\ pi_q D + 24 <= ly_stk_hi ly /\ ARx ly S Hp W mem md.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  pose proof cf_head_nonneg as Hh0. pose proof pdc_stk144 as Hstk144.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HPRE as (HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIN0 & Hpl & Hnth & HWIN & Hq1 & Hq2 & HRA0 & HSRC0 & _).
  destruct HF as ((HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
  pose proof Hstk as (Hal & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct HWIN as (He0 & He16 & Hetop & Hepres).
  destruct HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN0) & HAL & HSH & HGT & HCST & HIN & HROD & HSC & R2 & R18 & R19
    & R20 & R10 & R8 & R9 & HREL).
  pose proof (ajx_ar HJ) as HAR. cbv beta in HAR.
  destruct HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Ht62 & Htp' & Hlen & Hg & Hqt & Hd).
  destruct HSRC as (Hb & H4096 & Hsc & Hamr & Hra' & Hhu).
  destruct HREL as (done & Hbd & Hdl & HSo & HNo & Hr & Hwo & Hw & Hsync).
  pose proof (pdc_scan_len (pi_tb D) (pi_text D) r _ ltac:(lia) Hsync) as Hrlt.
  destruct HAL as (Hcnt & Hout & Hout16 & EHp & Eab & HLED & Hvis & Hroom & Hrpos & Hbb).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & Hpr & _).
  rewrite (pdc_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ, Hpr by lia.
  unfold PS_Gen.PS_SP. rewrite pdc_frame.
  assert (HSP16 : (spZ (pi_regs D) - 144) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
  assert (Hlen' : r < pi_text D + pi_len D) by lia.
  pose proof (ajx_ly HJ) as Hly.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  repeat apply conj; try assumption; try lia.
  - intros a Ha. apply (in_app_addr _ _ a Happ). lia.
  - intros a Ha. exact (Hpr a ltac:(lia)).
Qed.

(* ---- the regions of the cut, from concrete memory facts ---- *)
Lemma pdc_rok_in : forall E m a en, ew E 9 = w64 a -> ew E 10 = w64 en -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  0 <= en < 2 ^ 64 -> val_mem segs m a 8 en -> region_ok segs E m pdc_rg_in.
Proof.
  intros E m a en H9 H10 Ha Ha2 Hen V. unfold region_ok, pdc_rg_in.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E m a 0 8 (SOff 10 0) en); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V].
  exact (pdc_denot_atom E 10 en H10 ltac:(lia)).
Qed.
Lemma pdc_rok_inx : forall E m a en (n : nat), ew E 9 = w64 a -> ew E n = w64 en -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  0 <= en < 2 ^ 64 -> val_mem segs m a 8 en ->
  region_ok segs E m (YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff n 0))]).
Proof.
  intros E m a en n H9 Hn Ha Ha2 Hen V. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E m a 0 8 (SOff n 0) en); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V].
  exact (pdc_denot_atom E n en Hn ltac:(lia)).
Qed.
Lemma pdc_rok_t : forall E m r i b n, ew E 20 = w64 r -> ew E n = w64 b -> 0 <= r -> 0 <= i ->
  r + i + 1 <= 2 ^ 64 -> 0 <= b < 256 -> val_mem segs m (r + i) 1 b -> region_ok segs E m (pdc_rg_t i n).
Proof.
  intros E m r i b n H20 Hb Hr Hi Hr2 Hb0 V. unfold region_ok, pdc_rg_t.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H20, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E m r i 1 (SOff n 0) b); [| cbn; lia | cbn; lia | exact V].
  exact (pdc_denot_atom E n b Hb ltac:(lia)).
Qed.
Lemma pdc_rok_o : forall E m w, ew E 19 = w64 w -> 0 <= w -> w + 1 <= 2 ^ 64 -> writable_at segs m w ->
  region_ok segs E m pdc_rg_o.
Proof.
  intros E m w H19 Hw Hw2 Wr. unfold region_ok, pdc_rg_o.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite H19, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. replace (w + o) with w by lia. exact Wr.
Qed.

(* ---- the environment of the cut: the registers at the cut plus the two text bytes ---- *)
Definition pdc_b (D : ps_in) (r i : Z) : Z := nth (Z.to_nat (r + i - pi_text D)) (pi_tb D) 0.
Definition pdc_E (D : ps_in) (regs : bvmap 5 word) (r : Z) : env :=
  EB (Ereg regs [w64 (pdc_b D r 0); w64 (pdc_b D r 1)]).
Lemma pdc_ew_reg : forall D regs r n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (pdc_E D regs r) n = getr regs x.
Proof.
  intros D regs r n x Hn. unfold pdc_E. rewrite Eimg_low by (pose proof (u5_range x); unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn.
Qed.
Lemma pdc_ew_b : forall D regs r i, (i < 2)%nat ->
  ew (pdc_E D regs r) (32 + i) = w64 (pdc_b D r (Z.of_nat i)).
Proof.
  intros D regs r i Hi. unfold pdc_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. destruct i as [|[|i]]; cbn [nth]; try reflexivity. exfalso. lia.
Qed.
Lemma pdc_img_E : forall D regs r, img_env VAL A_LIM (pdc_E D regs r).
Proof. intros D regs r. unfold pdc_E. apply Eimg_env. Qed.
Lemma pdc_E_agree : forall D regs r, env_agree 32 (Ereg regs [w64 (pdc_b D r 0); w64 (pdc_b D r 1)]) (pdc_E D regs r).
Proof.
  intros D regs r. split; [intros n Hn; unfold pdc_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.
(* a text byte and its range, from the text's garr8 *)
Lemma pdc_byte : forall D (W : world segs) mem r i, garr8 segs (rdW W mem) (pi_text D) (pi_tb D) ->
  pi_text D <= r + i < pi_text D + Z.of_nat (length (pi_tb D)) -> 0 <= i ->
  val_mem segs (rdW W mem) (r + i) 1 (pdc_b D r i) /\ 0 <= pdc_b D r i < 256.
Proof.
  intros D W mem r i Hg Hx Hi. unfold pdc_b.
  destruct (Hg (Z.to_nat (r + i - pi_text D)) ltac:(lia)) as [V R].
  replace (pi_text D + Z.of_nat (Z.to_nat (r + i - pi_text D))) with (r + i) in V by lia. auto.
Qed.

(* ---- THE TEXT AND THE NEW BLOCK ARE APART (WalkS4's S4_PsDecKit.v ps_txt_out, image B): the text lives in a harness
   block of the entry ledger, in read-only image bytes, or in a block whose base is no hidden head, while the new
   block is a hidden head's block that the entry ledger does not list ---- *)
Lemma pdc_txt_out : forall D ly S Hp W mem md out Q a,
  ARx ly S Hp W mem md -> prhReader_home B ly S Hp (pi_Lam D) (pi_text D) (pi_len D) ->
  ps_alloc D ly S Hp W mem out Q -> LEDGER ly S Hp W mem ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D) ->
  pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a.
Proof.
  intros D ly S Hp W mem md out Q a HAR HHOME HAL HLED Ha.
  pose proof cf_head_nonneg as Hh0.
  destruct HAL as (Hcnt & Hout & Hout16 & EHp & Eab & _ & Hvis & Hroom & Hrpos & Hbb).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  assert (Ro : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head) by (apply pdc_req; lia).
  destruct (Z_lt_le_dec a (out - cf_head)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_le_dec a (out + Z.of_nat Q + 1)) as [Hr|Hr]; [|right; exact Hr]. exfalso.
  destruct HHOME as [[(b & m & Hin & Hb & Hm) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)].
  - destruct HLED as (_ & HND & HFA & _).
    pose proof (proj1 (Forall_forall _ _) HFA (b, m) (or_intror Hin)) as (Hm0 & Hab & _). cbn [fst snd] in Hm0, Hab.
    assert (Hne : (b - cf_head, m + cf_head) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
    { intros E. injection E as E1 _. cbn [map fst] in HND. inversion HND as [|x l HN HND2]; subst. apply HN.
      assert (Hi : In out (map fst (pi_Lam D)))
        by (apply in_map_iff; exists (b, m); split; [cbn [fst]; lia | exact Hin]).
      first [ apply list_elem_of_In; exact Hi | apply elem_of_list_In; exact Hi ]. }
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin_o Hne) as Hd.
    pose proof (req_size_pos (m + cf_head) (Z.add_nonneg_nonneg _ _ Hm0 Hh0)) as [_ Rm].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Ro in Hd. lia.
  - destruct (Hro a Ha) as (Hr0 & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HAR Hin_o); [rewrite Ro; lia|].
    destruct Hr0 as [(sg & Hs & _ & Hsr) | Hrr];
      [exists sg; split; [exact Hs | exact Hsr] | exact (@pa_relro_img _ _ PSB_PAImg a Hrr)].
  - destruct (Hro a Ha) as (Hr0 & _ & _ & _).
    apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ a HAR Hin_o); [rewrite Ro; lia|].
    destruct Hr0 as [(sg & Hs & _ & Hsr) | Hrr];
      [exists sg; split; [exact Hs | exact Hsr] | exact (@pa_relro_img _ _ PSB_PAImg a Hrr)].
  - assert (Hne : (b, m) <> (out - cf_head, Z.of_nat Q + 1 + cf_head)).
    { intros E. injection E as E1 _. apply Hnh. rewrite EHp, E1. left. reflexivity. }
    pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hin Hin_o Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Ro in Hd.
    pose proof (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin) as (Hm16 & _).
    assert (Rm : req_size m = m) by (apply pdc_req; lia). rewrite Rm in Hd. lia.
Qed.

(* ---- THE STATE AT THE DECODE LOOP HEAD, from the cut predicate ---- *)
Lemma pdc_entry : forall CTX CW D ly S Hp W regs mem md out w r Q bs,
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  (bs = true -> r + 1 < pi_text D + pi_len D) ->
  st_ok_pi segs VAL (pdc_E D regs r) (pdc_ss bs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (PSB_OFF + PSB_DEC))) mem (seg_rom segs))) /\
  sh_ok segs pdc_Bx pdc_SH (pdc_E D regs r) (rdW W mem).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q bs HPRE HDEC Hbs.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN0) & HAL & HSH & HGT & HCST & HIN & HROD & HSC & R2 & R18 & R19
    & R20 & R10 & R8 & R9 & HREL).
  destruct HSH as (S23 & S22 & S24).
  destruct HIN as (Vp & Ve & Vd & Hrw & _ & _ & Ht62 & _ & _ & Hg & Hqt & Hd).
  pose proof HAL as HAL'. destruct HAL as (_ & _ & _ & _ & _ & HLED & (Hvra & Hvhu) & _ & _ & _).
  assert (Hwr : writable_at segs (rdW W mem) w) by (apply apresent_writable; apply (proj1 (Hpres w ltac:(lia)))).
  (* the text window and the new block do not meet, so w is neither text byte *)
  assert (Hout_t : forall a, pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a)
    by (intros a Ha; exact (pdc_txt_out D ly S Hp W mem md out Q a HAR HHOME HAL' HLED Ha)).
  pose proof (Hout_t r ltac:(lia)) as Hwr0.
  set (E := pdc_E D regs r).
  assert (E9 : ew E 9 = w64 (pi_q D + 8)) by (subst E; rewrite (pdc_ew_reg D regs r 9 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = w64 (pi_text D + pi_len D))
    by (subst E; rewrite (pdc_ew_reg D regs r 10 10%bv eq_refl); exact R10).
  assert (E19 : ew E 19 = w64 w) by (subst E; rewrite (pdc_ew_reg D regs r 19 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = w64 r) by (subst E; rewrite (pdc_ew_reg D regs r 20 20%bv eq_refl); exact R20).
  assert (E23 : ew E 23 = w64 SHADOW_OFF) by (subst E; rewrite (pdc_ew_reg D regs r 23 23%bv eq_refl); exact S23).
  assert (E32 : ew E 32 = w64 (pdc_b D r 0)) by (subst E; exact (pdc_ew_b D regs r 0 ltac:(lia))).
  assert (E33 : ew E 33 = w64 (pdc_b D r 1))
    by (subst E; exact (pdc_ew_b D regs r 1 ltac:(lia))).
  destruct (pdc_byte D W mem r 0 Hg ltac:(lia) ltac:(lia)) as [V0 B0].
  assert (B1 : 0 <= pdc_b D r 1 < 256).
  { unfold pdc_b. destruct (Nat.lt_ge_cases (Z.to_nat (r + 1 - pi_text D)) (length (pi_tb D))) as [Hl|Hl].
    - exact (proj2 (Hg _ Hl)).
    - rewrite nth_overflow by exact Hl. lia. }
  split.
  - rewrite restrict_mkst_fx. unfold pdc_ss. apply pa_entry_st_ok_full.
    + apply pdc_regs_ok_pins; [subst E; unfold pdc_E; apply regs_ok_Eimg_Ereg|].
      unfold pdc_pin_dec. destruct HCST as (C25 & C26 & C27 & C14 & C15 & C16 & C17 & C5t & _).
      repeat (apply Forall_cons; [cbn [fst snd]|]); [..|apply Forall_nil].
      * rewrite S24. symmetry. exact (pdc_sv_shx E 9 (pi_q D + 8) E9 ltac:(lia) E23).
      * exact C25.
      * exact C26.
      * exact C27.
      * exact C14.
      * exact C15.
      * exact C16.
      * exact C17.
      * exact C5t.
    + destruct bs; vm_compute; reflexivity.
    + unfold pdc_regs_of. destruct bs.
      * specialize (Hbs eq_refl).
        destruct (pdc_byte D W mem r 1 Hg ltac:(lia) ltac:(lia)) as [V1 _].
        apply Forall_cons;
          [exact (pdc_rok_in E _ (pi_q D + 8) (pi_text D + pi_len D) E9 E10 ltac:(lia) ltac:(lia) ltac:(lia) Ve)|].
        apply Forall_cons; [exact (pdc_rok_t E _ r 0 (pdc_b D r 0) 32 E20 E32 ltac:(lia) ltac:(lia) ltac:(lia) B0 V0)|].
        apply Forall_cons; [exact (pdc_rok_t E _ r 1 (pdc_b D r 1) 33 E20 E33 ltac:(lia) ltac:(lia) ltac:(lia) B1 V1)|].
        apply Forall_cons; [exact (pdc_rok_o E _ w E19 ltac:(lia) ltac:(lia) Hwr)|]. apply Forall_nil.
      * apply Forall_cons;
          [exact (pdc_rok_in E _ (pi_q D + 8) (pi_text D + pi_len D) E9 E10 ltac:(lia) ltac:(lia) ltac:(lia) Ve)|].
        apply Forall_cons; [exact (pdc_rok_t E _ r 0 (pdc_b D r 0) 32 E20 E32 ltac:(lia) ltac:(lia) ltac:(lia) B0 V0)|].
        apply Forall_cons; [exact (pdc_rok_o E _ w E19 ltac:(lia) ltac:(lia) Hwr)|]. apply Forall_nil.
    + apply pairwise_disjoint_of_extents.
      unfold pdc_regs_of, pdc_rg_in, pdc_rg_t, pdc_rg_o, extent_of_region.
      destruct bs.
      * specialize (Hbs eq_refl). pose proof (Hout_t (r + 1) ltac:(lia)) as Hwr1.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
        rewrite E9, E19, E20, !unsigned_lit_small by lia.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        destruct Hqt as [Hqt|Hqt]; destruct Hwr0 as [Hwr0|Hwr0]; destruct Hwr1 as [Hwr1|Hwr1];
          repeat split; lia.
      * cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
        rewrite E9, E19, E20, !unsigned_lit_small by lia.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        destruct Hqt as [Hqt|Hqt]; destruct Hwr0 as [Hwr0|Hwr0]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [pdc_afacts f_atoms atoms_ok].
      split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
      * apply (pdc_afact_rng E 9 (pi_q D + 8)); [exact E9 | lia | lia | | lia].
        change (2 ^ 3) with 8. rewrite Z.add_mod, Hq8 by lia. reflexivity.
      * apply (pdc_afact_rng E 19 w); [exact E19 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      * apply (pdc_afact_rng E 20 r); [exact E20 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      * apply (pdc_afact_rng E 23 SHADOW_OFF);
          [exact E23 | lia | unfold SHADOW_OFF; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      * apply (pdc_afact_rng E 32 (pdc_b D r 0));
          [exact E32 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      * apply (pdc_afact_rng E 33 (pdc_b D r 1));
          [exact E33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  - unfold sh_ok, pdc_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem E pdc_Bx 19 out (Z.of_nat Q + 1) w 0 1 Hvra).
    + unfold pdc_Bx. rewrite U_SOff, E23. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
      apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    + rewrite U_SOff, E19. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
      apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + intros x Hx. pose proof (Happ x ltac:(lia)) as Hax.
      unfold app_addr, kLowShadowBeg, kHighMemBeg in Hax. unfold SHADOW_OFF. lia.
Qed.

(* ---- TRANSPORT: the stretch writes ONE byte (the out byte at w), so every fact of the cut whose bytes miss w is
   kept. The shadow band and the image are apart from w because w is an application byte of a live block. ---- *)
Lemma pdc_val_kept : forall (W : world segs) (m m2 : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W) m2 x = aview segs (w_H W) m x) ->
  val_mem segs (rdW W m) a n v -> val_mem segs (rdW W m2) a n v.
Proof.
  intros W m m2 a n v HE Hv kk Hk.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W) m m2 (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HE. lia.
Qed.
Lemma pdc_garr_kept : forall (W : world segs) (m m2 : word -> option byte) p L,
  (forall x, p <= x < p + Z.of_nat (length L) -> aview segs (w_H W) m2 x = aview segs (w_H W) m x) ->
  garr8 segs (rdW W m) p L -> garr8 segs (rdW W m2) p L.
Proof.
  intros W m m2 p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  intros kk Hk. cbn in Hk.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W) m m2 (p + Z.of_nat j + Z.of_nat kk)); [exact (Hv kk Hk)|].
  apply HE. lia.
Qed.
Lemma pdc_ra_kept : forall (W : world segs) (m m2 : word -> option byte) a n,
  (forall x, a <= x < a + n ->
     aview segs (w_H W) m2 (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF a n ->
  range_addressable (aview segs (w_H W) m2) SHADOW_OFF a n.
Proof.
  intros W m m2 a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto.
Qed.
Lemma pdc_hull_kept : forall (W : world segs) (m m2 : word -> option byte) x n,
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
     aview segs (w_H W) m2 s = aview segs (w_H W) m s) ->
  shadow_hull_vis (aview segs (w_H W) m) x n -> shadow_hull_vis (aview segs (w_H W) m2) x n.
Proof. intros W m m2 x n HE H s Hs. rewrite (HE s Hs). exact (H s Hs). Qed.
(* the shadow of an application address is in the band the walk's Bx spans *)
Lemma pdc_shadow_band : forall a, 0 <= a < 2 ^ 47 -> SHADOW_OFF <= SHADOW_OFF + a / 8 < SHADOW_OFF + 2 ^ 44.
Proof.
  intros a Ha. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma pdc_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 64 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44.
Proof.
  intros x n s Hx Hn Hxn Hs. unfold shadow_addr in Hs.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (x + n - 1) 8 ltac:(lia) ltac:(lia)).
  assert (H1 : (x + n - 1) / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia).
  assert (H2 : forall k, 0 <= k -> SHADOW_OFF <= (SHADOW_OFF + k) / 8 * 8).
  { intros k Hk. pose proof (Z.div_mod (SHADOW_OFF + k) 8 ltac:(lia)) as Hdm.
    assert (Hm : (SHADOW_OFF + k) mod 8 = k mod 8)
      by (rewrite Z.add_mod by lia; change (SHADOW_OFF mod 8) with 0; rewrite Z.add_0_l, Z.mod_mod by lia; reflexivity).
    pose proof (Z.mod_le k 8 Hk ltac:(lia)). lia. }
  pose proof (H2 (x / 8) ltac:(lia)).
  assert (Hup : (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (x + n - 1) / 8).
  { pose proof (Z.mul_div_le (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)). lia. }
  unfold SHADOW_OFF in *. lia.
Qed.

(* a byte that stays present stays writable (PRW_StepKit.v:106 writable_kept, at this walk's world) *)
Lemma pdc_writable_kept : forall (W : world segs) (m m2 : word -> option byte) a,
  (apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  writable_at segs (rdW W m) a -> writable_at segs (rdW W m2) a.
Proof.
  intros W m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
  destruct (w_H W (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  - destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  - destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* the kept relation does not look at the model's materialised pages *)
Lemma pdc_kept_md : forall STKf sp OR FPc lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 md3,
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 -> same_but_materialized md2 md3 ->
  KEPT STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md3.
Proof.
  intros STKf sp OR FPc lyc Sc W memc mdc ly2 S2 W2 mem2 md2 md3 (H1 & H2 & H3 & H4 & H5) Hs.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  exact (aos_step_same_io _ _ _ _ H4 (same_io_materialized _ _ Hs)).
Qed.

Lemma pdc_keep : forall CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2,
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  ps_carry D ly S Hp W mem2 md2 k2 [] /\
  ps_alloc D ly S Hp W mem2 out Q /\
  pj_in_okR segs (rdW W mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) /\
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B (aview segs (w_H W) mem2) /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, pi_text D <= a < pi_text D + pi_len D -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) /\
  (forall a, out <= a < w -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HW as Hhw. unfold prh_head_wide in Hhw.
  pose proof HPRE as (HF & _).
  destruct HF as ((HAR0 & _ & _ & _ & _ & _ & _ & _ & _) & _).
  destruct HDEC as ((k & HJ & HK & HSV & HSRC & HHOME & HMN0) & HAL & HSH & HGT & HCST & HIN & HROD & HSC & R2 & R18 & R19
    & R20 & R10 & R8 & R9 & HREL).
  pose proof HAL as HAL'.
  destruct HAL as (Hcnt & Hout' & Hout16 & EHp & Eab & HLED & (Hvra & Hvhu) & Hroom & Hrpos & Hbb).
  destruct HIN as (Vp & Ve & Vd & Hrw & _ & _ & Ht62 & Htp' & Hlentb & Hg & Hqt & Hd).
  destruct HSRC as (Hsb & H4096 & Hsc & Hamr & Hsra & Hshu).
  assert (Rqo : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head) by (apply pdc_req; lia).
  assert (Hwapp : app_addr w) by (apply Happ; lia).
  assert (Hwimg : ~ in_img segs w).
  { apply (blk_img_x segs B ARx LAWS ly S Hp W mem md _ _ w HAR Hin_o). rewrite Rqo. lia. }
  assert (KA : forall a, 0 <= a < 2 ^ 64 -> a <> w -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha Hne. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia. exact Hne. }
  assert (Hwceil : 4096 <= w < YM05.alloc_ceiling).
  { unfold app_addr, kLowShadowBeg, ASAN_CEIL in Hwapp. destruct Hwapp as (H4 & [Hl|[Hh1 Hh2]]); lia. }
  assert (Hwband : ~ (SHADOW_OFF <= w < SHADOW_OFF + 2 ^ 44)).
  { unfold SHADOW_OFF. unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hwapp.
    destruct Hwapp as (H4 & [Hl|[Hh1 Hh2]]); lia. }
  assert (KC : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KA; [lia | lia]. }
  assert (KSB : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
    aview segs (w_H W) mem2 s = aview segs (w_H W) mem s).
  { intros s Hs. apply KA; [unfold SHADOW_OFF in *; lia|]. intros Ew. apply Hwband. rewrite <- Ew. exact Hs. }
  assert (KIMG : forall a, in_img segs a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { intros a Hi. pose proof (@pa_segs_low _ B_prog_listing PSB_PAImg a Hi) as Hlo.
    apply KA; [unfold kLowMemEnd in *; lia|]. intros Ew. rewrite <- Ew in Hwimg. exact (Hwimg Hi). }
  assert (Hout_t : forall a, pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a)
    by (intros a Ha; exact (pdc_txt_out D ly S Hp W mem md out Q a HAR HHOME HAL' HLED Ha)).
  assert (KT : forall a, pi_text D <= a < pi_text D + pi_len D ->
    aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KA; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia|].
    intros Ew. destruct (Hout_t a Ha); lia. }
  assert (KD : forall a, out <= a < w -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KA; lia).
  assert (KPST : forall a, Exists (in_zr a) prh_pst -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KIMG; exact (proj1 (PST_ok a Ha))).
  assert (KHD : forall a kk i, In (a, kk) ((out, Z.of_nat Q + 1) :: pi_Lam D) -> 0 <= i < 8 ->
    aview segs (w_H W) mem2 (a - cf_head + i) = aview segs (w_H W) mem (a - cf_head + i)).
  { intros a kk i Hin Hi.
    pose proof HLED as (_ & _ & HFA0 & _).
    pose proof (proj1 (Forall_forall _ _) HFA0 (a, kk) Hin) as (Hk0 & Hblk & _ & Ha16 & _).
    cbn [fst snd] in Hk0, Hblk, Ha16.
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096a & Hca & Happa & _).
    assert (Rka : req_size (kk + cf_head) = kk + cf_head) by (apply pdc_req; lia).
    rewrite Rka in Hca, Happa.
    apply KA; [unfold in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd in Happa; lia|]. intros Ew.
    destruct (Z.eq_dec a out) as [Eao|Hne].
    - rewrite Eao in Ew. lia.
    - assert (Hbne : (a - cf_head, kk + cf_head) <> (out - cf_head, Z.of_nat Q + 1 + cf_head))
        by (intros Eq; injection Eq as E1 _; apply Hne; lia).
      pose proof (sep_blocks_x segs B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hblk Hin_o Hbne) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Rka, Rqo in Hdj. lia. }
  assert (HKEPT : KEPT STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] []
    (pi_ly D) (pi_S D) (pi_W D) (pi_mem D) (pi_md D) ly S W mem2 md2).
  { apply (@cj_kept_trans rc SK segs B PST ARx cf_head LAWS
      STK_parse_string (spZ (pi_regs D)) STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [] [(w, w + 1)] []
      (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) ly S Hp W mem md ly S W mem2 md2).
    - exact HK.
    - apply (@cj_kept_exec rc SK segs B PST ARx cf_head LAWS (@pa_segs_low _ B_prog_listing PSB_PAImg)
        STK_parse_string (spZ (pi_regs D)) [(pi_q D, pi_q D + 8)] [(w, w + 1)] ly S Hp W mem md mem2 md2
        (fun a => a = w)).
      + exact HAR.
      + exact Hclo.
      + lia.
      + exact Hshi.
      + intros x Hx. apply HFR. intros Ex. apply Hx. exact Ex.
      + intros a Ha. right. right. split.
        * exists (w, w + 1). split; [left; reflexivity | cbn [fst snd]; lia].
        * exists (out - cf_head), (Z.of_nat Q + 1 + cf_head). split; [exact Hin_o|]. rewrite Rqo. lia.
      + exact HMD.
    - exact HAR0.
    - exact HAR.
    - lia.
    - lia.
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - intros a (rr & Hrin & Hrr). destruct Hrin as [Er|[]]. rewrite <- Er in Hrr. cbn [fst snd] in Hrr.
      right. left. exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
      split; [exact Hin_o|].
      split; [apply (pdc_new_block ly S Hp W mem md (pi_ly D) (pi_S D) _ HAR Eab); cbn [snd]; rewrite Rqo; lia|].
      rewrite Rqo. lia. }
  assert (HSV2 : ps_saved D W mem2).
  { destruct HSV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    unfold PS_Gen.ps_saved in *. rewrite Esp in *.
    repeat apply conj;
      (apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | assumption]). }
  assert (HSRC2 : src_rd W mem2 (pi_text D) (pi_tb D)).
  { split; [|split; [exact H4096|split; [exact Hsc|split; [exact Hamr|split]]]].
    - apply (pdc_garr_kept W mem mem2); [intros x Hx; apply KT; lia | exact Hsb].
    - apply (pdc_ra_kept W mem mem2); [|exact Hsra].
      intros x Hx. apply KSB. unfold shadow_of_addr. apply pdc_shadow_band.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia.
    - intros Hpos. apply (pdc_hull_kept W mem mem2); [|exact (Hshu Hpos)].
      intros s Hs. apply KSB. apply (pdc_hull_band (pi_text D) (Z.of_nat (length (pi_tb D))) s); [lia|lia| |exact Hs].
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
  assert (HLED2 : LEDGER ly S Hp W mem2 ((out, Z.of_nat Q + 1) :: pi_Lam D)
    (Z.max (pi_peak D) (Ledger.lsum (pi_Lam D) + (Z.of_nat Q + 1))) (pi_cnt D + 1) (pi_fail D) (pi_ran D)
    (pi_most D) (pi_own D)).
  { destruct HLED as (HGL & HND & HFA & HPM). split; [|split; [exact HND | split; [|exact HPM]]].
    - destruct HGL as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Grest).
      split; [|split; [|split; [|split; [|split; [|split; [split; [|exact G6r]|split; [split; [|exact G7r]|exact Grest]]]]]]].
      + apply (pdc_val_kept W mem mem2); [|exact G1]. intros x Hx. apply KPST.
        apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G2]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G3]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G4]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G5]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
        unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G6]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
        unfold in_zr. cbn [fst snd]. lia.
      + apply (pdc_val_kept W mem mem2); [|exact G7]. intros x Hx. apply KPST.
        apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl,
          Exists_cons_hd.
        unfold in_zr. cbn [fst snd]. lia.
    - apply Forall_forall. intros [a kk] Hin.
      destruct (proj1 (Forall_forall _ _) HFA (a, kk) Hin) as (Hk0 & Hblk & HinHp & Ha16 & Vhd).
      cbn [fst snd] in Hk0, Hblk, HinHp, Ha16, Vhd |- *.
      split; [exact Hk0|]. split; [exact Hblk|]. split; [exact HinHp|]. split; [exact Ha16|].
      apply (pdc_val_kept W mem mem2); [|exact Vhd].
      intros x Hx. replace x with (a - cf_head + (x - (a - cf_head))) by lia.
      apply (KHD a kk (x - (a - cf_head)) Hin). lia. }
  assert (HVIS2 : prhReader_vis W mem2 out (Z.of_nat Q + 1)).
  { split.
    - apply (pdc_ra_kept W mem mem2); [|exact Hvra].
      intros x Hx. apply KSB. unfold shadow_of_addr. apply pdc_shadow_band. lia.
    - intros Hpos. apply (pdc_hull_kept W mem mem2); [|exact (Hvhu Hpos)].
      intros s Hs. apply KSB. apply (pdc_hull_band out (Z.of_nat Q + 1) s); [lia|lia| |exact Hs]. lia. }
  split.
  { split; [exact HJ2|]. split; [exact HKEPT|].
    split; [exact HSV2 | split; [exact HSRC2 | split; [exact HHOME | exact HMNm]]]. }
  split.
  { split; [exact Hcnt|]. split; [exact Hout'|]. split; [exact Hout16|]. split; [exact EHp|].
    split; [exact Eab|]. split; [exact HLED2|]. split; [exact HVIS2|].
    split; [exact Hroom | split; [exact Hrpos | exact Hbb]]. }
  split.
  { split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact Vp]|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact Ve]|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact Vd]|].
    split; [intros x Hx; apply (pdc_writable_kept W mem mem2 x (HGR x)); exact (Hrw x Hx)|].
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Ht62|]. split; [exact Htp'|].
    split; [exact Hlentb|].
    split; [apply (pdc_garr_kept W mem mem2); [intros x Hx; apply KT; lia | exact Hg]|].
    split; [exact Hqt | exact Hd]. }
  split.
  { intros a Hro Hown Herr. rewrite KIMG; [exact (HROD a Hro Hown Herr)|].
    destruct Hro as [(sg & Hs & _ & Hsr) | Hrr];
      [exists sg; split; [exact Hs | exact Hsr] | exact (@pa_relro_img _ _ PSB_PAImg a Hrr)]. }
  split; [exact KC | split; [exact KT | exact KD]].
Qed.

(* ---- the shadow of the caller's cursor words: the real stack reads shadow 0 at every ARx state (alx_zshadow_byte),
   so the loop tail's q + 8 re-check is not taken ---- *)
Lemma pdc_stack_ra : forall ly S Hp W mem md a n,
  ARx ly S Hp W mem md -> a mod 8 = 0 -> n mod 8 = 0 -> ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> 0 <= n ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros ly S Hp W mem md a n HAR Ha Hn Hlo Hhi Hn0.
  apply (zero_shadow_range (aview segs (w_H W) mem) SHADOW_OFF a n Ha Hn).
  intros i Hi. unfold shadow_of_addr.
  replace (SHADOW_OFF + a / 8 + i) with (SHADOW_OFF + (a + i * 8) / 8)
    by (rewrite Z.div_add by lia; lia).
  apply (alx_zshadow_byte segs B ARx LAWS ly S Hp W mem md (a + i * 8) HAR).
  pose proof (Z.mul_div_le n 8 ltac:(lia)) as Hmd. lia.
Qed.

Lemma pdc_scan_ltn : forall n l k, (length l <= n)%nat -> PjGrammar.scan l = Some k -> (k < length l)%nat.
Proof.
  induction n as [|n IH]; intros l k Hn H.
  - destruct l; cbn [PjGrammar.scan length] in H, Hn |- *; [discriminate | lia].
  - destruct l as [|b t]; cbn [PjGrammar.scan length] in H, Hn |- *; [discriminate|].
    destruct (Z.eqb_spec b 34) as [Eb|Hb34]; [injection H as <-; lia|].
    destruct (Z.eqb_spec b 92) as [Eb|Hb92].
    + destruct t as [|b2 t2]; [discriminate|].
      destruct (PjGrammar.scan t2) as [k2|] eqn:E2; cbn [option_map] in H; [|discriminate].
      injection H as <-. cbn [length] in Hn |- *.
      assert (k2 < length t2)%nat by (apply (IH t2 k2); [lia | exact E2]). lia.
    + destruct (PjGrammar.scan t) as [k2|] eqn:E2; cbn [option_map] in H; [|discriminate].
      injection H as <-. assert (k2 < length t)%nat by (apply (IH t k2); [lia | exact E2]). lia.
Qed.
Lemma pdc_scan_lt : forall l k, PjGrammar.scan l = Some k -> (k < length l)%nat.
Proof. intros l k H. exact (pdc_scan_ltn (length l) l k (Nat.le_refl _) H). Qed.
Lemma pdc_garr_snoc : forall (m : word -> option byte) p l v,
  garr8 segs m p l -> val_mem segs m (p + Z.of_nat (length l)) 1 v -> 0 <= v < 256 -> garr8 segs m p (l ++ [v]).
Proof.
  intros m p l v HG HV Hv j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length l)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl. exact (HG j Hl).
  - assert (Ej : j = length l) by lia. subst j.
    rewrite nth_middle. split; [|exact Hv]. exact HV.
Qed.

(* ---- THE REJOIN: from the loop tail at offset 540 back to the decode head, one measure lower ---- *)
Lemma pdc_join : forall CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 j,
  psb_dec_ltP B ARx SK CTX CW P m ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  ps_carry D ly S Hp W mem2 md2 k2 [] -> ps_alloc D ly S Hp W mem2 out Q ->
  pj_in_okR segs (rdW W mem2) (pi_q D) (pi_text D) (pi_len D) (pi_p D) (pi_d D) (pi_tb D) ->
  arodata_okP segs (@pa_relro_lo _ B_prog_listing PSB_PAImg) (@pa_relro_hi _ B_prog_listing PSB_PAImg) B (aview segs (w_H W) mem2) ->
  psb_sh_regs D regs2 -> ps_gptp D regs2 -> psb_dec_consts D W mem2 regs2 ->
  getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 10 = w64 (w + 1) ->
  getr regs2 21 = w64 (r + j) -> getr regs2 8 = w64 (pi_q D) -> getr regs2 9 = w64 (pi_q D + 8) ->
  ps_dec_rel D W mem2 out (w + 1) (r + j) Q ->
  (Q - Z.to_nat (r + j - (pi_p D + 1)))%nat = (Q - Z.to_nat (r - (pi_p D + 1)) - Z.to_nat j)%nat ->
  (Q - Z.to_nat (r + j - (pi_p D + 1)) < m)%nat ->
  0 < j -> w + 1 <= out + Z.of_nat Q ->
  SRr segs W (cfg_at segs (psb_pc PSB_JOIN) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 j
    HLT HPRE HDEC HC2 HAL2 HIN2 HROD2 HSH2 HGT2 HCST2 R2 R18 R10 R21 R8 R9 HREL2 Emeas Hmeas Hj Hwq.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pdc_stk144 as Hstk144.
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSCd & _).
  pose proof HC2 as (HJ2 & HK2 & HSV2 & HSRC2 & HHOME2 & HMN2).
  pose proof (ajx_ar HJ2) as HAR2. cbv beta in HAR2.
  destruct HIN2 as (Vp2 & Ve2 & Vd2 & Hrw2 & _ & _ & Ht62 & Htp2 & Hlentb & Hg2 & Hqt2 & Hd2).
  destruct HSH2 as (S23 & S22 & S24).
  pose proof HREL2 as (done & Hbd & Hdl & HSo & HNo & Hr2 & Hwo & Hww & Hsync2).
  pose proof (pdc_scan_len (pi_tb D) (pi_text D) (r + j) _ ltac:(lia) Hsync2) as Hrjlt.
  (* the symbolic state at the tail *)
  set (E := EB (Ereg regs2 [w64 (pi_text D + pi_len D)])).
  assert (Ereg9 : ew E 9 = w64 (pi_q D + 8)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl). exact R9. }
  assert (Ereg23 : ew E 23 = w64 SHADOW_OFF).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl). exact S23. }
  assert (Ereg32 : ew E 32 = w64 (pi_text D + pi_len D))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (Ereg21 : ew E 21 = w64 (r + j)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl). exact R21. }
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs2 [w64 (pi_text D + pi_len D)]) E)
    by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HS : st_ok_pi segs VAL E pdc_ss_t
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (PSB_OFF + PSB_JOIN))) mem2 (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold pdc_ss_t. apply pa_entry_st_ok_full.
    - apply pdc_regs_ok_pins; [subst E; apply regs_ok_Eimg_Ereg|].
      unfold pdc_pin_t. apply Forall_cons; [cbn [fst snd]|apply Forall_nil].
      rewrite S24. symmetry. exact (pdc_sv_shx E 9 (pi_q D + 8) Ereg9 ltac:(lia) Ereg23).
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      exact (pdc_rok_inx E _ (pi_q D + 8) (pi_text D + pi_len D) 32 Ereg9 Ereg32 ltac:(lia) ltac:(lia) ltac:(lia) Ve2).
    - apply pairwise_disjoint_of_extents. unfold pdc_rg_in_t, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]]. cbn [pdc_afacts_t f_atoms atoms_ok]. split; [|split; [|exact I]].
      + apply (pdc_afact_rng E 9 (pi_q D + 8)); [exact Ereg9 | lia | lia | | lia].
        change (2 ^ 3) with 8. rewrite Z.add_mod, Hq8 by lia. reflexivity.
      + apply (pdc_afact_rng E 23 SHADOW_OFF);
          [exact Ereg23 | lia | unfold SHADOW_OFF; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok segs pdc_Bx [] E (rdW W mem2)) by (unfold sh_ok; apply Forall_nil).
  pose proof HMN2 as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (BR := @paj_branch fx rc B_prog_listing PSB_PAImg).
  unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_JOIN) with (BASE + (PSB_OFF + PSB_JOIN)) by lia.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { (* the q + 8 granule: the real stack's shadow is 0 *)
    unfold ob_holds. cbn [ob_x ob_n].
    replace (U E pdc_Bx) with SHADOW_OFF
      by (unfold pdc_Bx; rewrite U_SOff, Ereg23; unfold w64;
          rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r;
          symmetry; apply zcanon_id; unfold SHADOW_OFF, M64; lia).
    replace (U E (SOff 9 0)) with (pi_q D + 8)
      by (rewrite U_SOff, Ereg9; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
          symmetry; apply zcanon_id; unfold M64; lia).
    exact (pdc_stack_ra ly S Hp W mem2 md2 (pi_q D + 8) 8 HAR2
      ltac:(change (2 ^ 3) with 8 in *; rewrite Z.add_mod, Hq8 by lia; reflexivity)
      ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)). }
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  (* the tail writes nothing *)
  lazymatch goal with |- _ => idtac end.
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ (* r + j >= end: not reachable, the closing quote is at or after r + j *)
    exfalso.
    lazymatch type of Hc with
    | branch_taken _ (sv_denot ?Ex _) _ = _ =>
      rewrite (pdc_br_ltu Ex 21 32 (r + j) (pi_text D + pi_len D)
        ltac:(pdc_ew Ereg21) ltac:(pdc_ew Ereg32) ltac:(lia) ltac:(lia)) in Hc
    end.
    apply Z.ltb_ge in Hc. lia. }
  (* back at the decode head with (w + 1, r + j) *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_DEC).
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (Emem : ms_mem msn = mem2)
      by (apply functional_extensionality; intros x;
          rewrite (HF0 x ltac:(intros (rr & Hin & Hrr); cbn [ss_mem add_cond In] in Hin;
                    destruct Hin as [Er | []]; rewrite <- Er in Hrr;
                    cbn [pdc_rg_in_t YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hrr; lia));
          apply HF; intros (rr & Hin & Hrr); cbn [ss_mem In] in Hin;
          destruct Hin as [Er | []]; rewrite <- Er in Hrr;
          cbn [pdc_rg_in_t YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hrr; lia) end.
  rewrite Emem in HJ2.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20. prreg HS (10%bv : bv 5) T10. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
  prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
  prreg HS (27%bv : bv 5) T27. prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15.
  prreg HS (16%bv : bv 5) T16. prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS. rewrite Emem.
  psb_pc_fold PSB_DEC.
  destruct HCST2 as (C25 & C26 & C27 & C14 & C15 & C16 & C17 & C5t & V24w & V16w & V8w).
  destruct HGT2 as (Hgp2 & Htp2').
  apply ps_finP_hand. eapply (HLT D ly S Hp W _ mem2 _ out (w + 1) (r + j) Q HPRE); [|exact Hmeas].
  split.
  { exists k2. split; [exact HJ2|].
    split; [exact (pdc_kept_md _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HK2 (same_but_materialized_wvb_any md2 _))|].
    split; [exact HSV2 | split; [exact HSRC2 | split; [exact HHOME2 | exact HMN2]]]. }
  split; [exact HAL2|].
  split; [split; [|split]|].
  - cbn [ms_regs]. rewrite T23. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl). exact S23.
  - cbn [ms_regs]. rewrite T22. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl). exact S22.
  - cbn [ms_regs]. rewrite T24. exact (pdc_shx_alu E 9 (pi_q D + 8) Ereg9 ltac:(lia) Ereg23).
  - split; [split|].
    + cbn [ms_regs]. rewrite T3. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl). exact Hgp2.
    + cbn [ms_regs]. rewrite T4. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl). exact Htp2'.
    + split.
      * split; [cbn [ms_regs]; rewrite T25; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl); exact C25|].
        split; [cbn [ms_regs]; rewrite T26; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact C26|].
        split; [cbn [ms_regs]; rewrite T27; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact C27|].
        split; [cbn [ms_regs]; rewrite T14; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 14 14%bv eq_refl); exact C14|].
        split; [cbn [ms_regs]; rewrite T15; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 15 15%bv eq_refl); exact C15|].
        split; [cbn [ms_regs]; rewrite T16; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 16 16%bv eq_refl); exact C16|].
        split; [cbn [ms_regs]; rewrite T17; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 17 17%bv eq_refl); exact C17|].
        split; [cbn [ms_regs]; rewrite T5; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 5 5%bv eq_refl); exact C5t|].
        split; [exact V24w | split; [exact V16w | exact V8w]].
      * split; [split; [exact Vp2 | split; [exact Ve2 | split; [exact Vd2 | split; [exact Hrw2 |
          split; [exact Hq8 | split; [exact Ht0 | split; [exact Ht62 | split; [exact Htp2 |
          split; [exact Hlentb | split; [exact Hg2 | split; [exact Hqt2 | exact Hd2]]]]]]]]]]]|].
        split; [exact HROD2|].
        split; [exact HSCd|].
        split; [cbn [ms_regs]; rewrite T2; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact R2|].
        split; [cbn [ms_regs]; rewrite T18; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18|].
        split; [cbn [ms_regs]; rewrite T19; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10|].
        split; [cbn [ms_regs]; rewrite T20; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact R21|].
        split; [cbn [ms_regs]; rewrite T10; exact Ereg32|].
        split; [cbn [ms_regs]; rewrite T8; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8|].
        split; [cbn [ms_regs]; rewrite T9; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
                rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9|].
        exact HREL2.
Qed.

(* ---- the decode relation after ONE emitted byte: `done` grows by the byte stored at w, the cursor by j ---- *)
Lemma pdc_rel_emit : forall D (W : world segs) mem mem2 out w r Q j v,
  ps_dec_rel D W mem out w r Q ->
  (forall a, out <= a < w -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  val_mem segs (rdW W mem2) w 1 v -> 0 <= v < 256 ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit [v] (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) (r + j))) ->
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (q + Z.to_nat j)%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + j))) ->
  0 < j -> r + j <= pi_p D + 1 + Z.of_nat Q ->
  ps_dec_rel D W mem2 out (w + 1) (r + j) Q.
Proof.
  intros D W mem mem2 out w r Q j v (done & Hbd & Hdl & HSo & HNo & Hr & Hwo & Hww & Hsync)
    Hkeep Hvw Hv Hdec Hscan Hj Hrj.
  exists (done ++ [v]). split.
  { unfold bytes_at in *. apply pdc_garr_snoc; [|rewrite Hdl; replace (out + (w - out)) with w by lia; exact Hvw|exact Hv].
    apply (pdc_garr_kept W mem mem2); [intros x Hx; apply Hkeep; lia | exact Hbd]. }
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros sx rx Hd. rewrite Hd in Hdec. cbn [PjGrammar.emit] in Hdec.
    rewrite <- app_assoc. cbn [app]. exact (HSo _ _ Hdec). }
  split.
  { intros Hd. rewrite Hd in Hdec. cbn [PjGrammar.emit] in Hdec. exact (HNo Hdec). }
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Hsync in Hscan.
  destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + j))) as [k2|] eqn:E2;
    cbn [option_map] in Hscan; [|discriminate].
  injection Hscan as Hscan. f_equal. lia.
Qed.

(* ---- THE STORE LEAF, shared by the plain byte and the eight escape arms: at the loop tail (540) the stored byte is
   at w, the cursor moved j bytes, and the measure is one lower ---- *)
Lemma pdc_store_leaf : forall CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 j v,
  psb_dec_ltP B ARx SK CTX CW P m ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  val_mem segs (rdW W mem2) w 1 v -> 0 <= v < 256 ->
  psb_sh_regs D regs2 -> ps_gptp D regs2 ->
  getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 10 = w64 (w + 1) ->
  getr regs2 21 = w64 (r + j) -> getr regs2 8 = w64 (pi_q D) -> getr regs2 9 = w64 (pi_q D + 8) ->
  getr regs2 25 = w64 34 -> getr regs2 26 = w64 (-1) -> getr regs2 27 = w64 92 ->
  getr regs2 14 = w64 32 -> getr regs2 15 = w64 101 -> getr regs2 16 = w64 91 -> getr regs2 17 = w64 113 ->
  getr regs2 5 = w64 114 ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) =
    PjGrammar.emit [v] (PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) (r + j))) ->
  PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r) =
    option_map (fun q => (q + Z.to_nat j)%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + j))) ->
  0 < j -> r + j <= pi_p D + 1 + Z.of_nat Q -> (Q - Z.to_nat (r - (pi_p D + 1)) < Nat.succ m)%nat ->
  SRr segs W (cfg_at segs (psb_pc PSB_JOIN) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 j v
    HLT HPRE HDEC HJ2 HMD HFR HGR HMNm Hvw Hv HSH2 HGT2 R2 R18 R10 R21 R8 R9 C25 C26 C27 C14 C15 C16 C17 C5t
    Hdec Hscan Hj Hrj Hmeas.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof HDEC as (_ & _ & _ & _ & HCST & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct (pdc_keep CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm)
    as (HC2 & HAL2 & HIN2 & HROD2 & KC & KT & KD).
  pose proof (pdc_rel_emit D W mem mem2 out w r Q j v HREL KD Hvw Hv Hdec Hscan Hj Hrj) as HREL2.
  destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & V24w & V16w & V8w).
  assert (HCST2 : psb_dec_consts D W mem2 regs2).
  { split; [exact C25|]. split; [exact C26|]. split; [exact C27|]. split; [exact C14|]. split; [exact C15|].
    split; [exact C16|]. split; [exact C17|]. split; [exact C5t|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V24w]|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V16w]|].
    apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V8w]. }
  pose proof HREL2 as (_ & _ & _ & _ & _ & Hr2 & Hwo2 & Hww2 & _).
  assert (Ea : Z.to_nat (r + j - (pi_p D + 1)) = (Z.to_nat (r - (pi_p D + 1)) + Z.to_nat j)%nat).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_add, !Z2Nat.id by lia. lia. }
  assert (Emeas : (Q - Z.to_nat (r + j - (pi_p D + 1)))%nat
                = (Q - Z.to_nat (r - (pi_p D + 1)) - Z.to_nat j)%nat)
    by (rewrite Ea; apply Nat.sub_add_distr).
  assert (Hjn : (1 <= Z.to_nat j)%nat).
  { apply (proj2 (Nat2Z.inj_le _ _)). rewrite Z2Nat.id by lia. cbn [Z.of_nat]. lia. }
  assert (Hlt : (Z.to_nat (r - (pi_p D + 1)) < Q)%nat).
  { apply (proj2 (Nat2Z.inj_lt _ _)). rewrite Z2Nat.id by lia. lia. }
  assert (Hm2 : (Q - Z.to_nat (r + j - (pi_p D + 1)) < m)%nat).
  { rewrite Emeas. exact (pdc_meas_step Q _ _ m Hlt Hjn Hmeas). }
  apply (pdc_join CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 j
    HLT HPRE HDEC HC2 HAL2 HIN2 HROD2 HSH2 HGT2 HCST2 R2 R18 R10 R21 R8 R9 HREL2);
    [exact Emeas | exact Hm2 | exact Hj | lia].
Qed.


(* ---- reading a byte the engine has just stored: the region's chunk at the write window ---- *)
Lemma pdc_region_nth : forall E ss (ms : machine_state) i rr,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some rr -> region_ok segs E (ms_mem ms) rr.
Proof.
  intros E ss ms i rr HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
  exact (proj1 (Forall_forall _ _) Hrs rr (nth_error_In _ _ Hi)).
Qed.
Lemma pdc_field1 : forall E m n b cs lo hi wlo whi od e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem segs m (b + od) 1 v.
Proof.
  intros E m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He Hv.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  change 1%nat with (N.to_nat 1).
  exact (val_of_chunk_ok segs E m b od 1%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
(* the two text positions as the head of the rest *)
Lemma pdc_rest_at0 : forall D r, pi_text D <= r -> r < pi_text D + Z.of_nat (length (pi_tb D)) ->
  rest_atR (pi_tb D) (pi_text D) r = pdc_b D r 0 :: rest_atR (pi_tb D) (pi_text D) (r + 1).
Proof.
  intros D r H1 H2. apply (pdc_rest_cons _ _ _ _ H1). unfold pdc_b.
  rewrite (pdc_rest_nth (pi_tb D) (pi_text D) r ltac:(lia)). all: (do 2 f_equal; lia).
Qed.
Lemma pdc_rest_at1 : forall D r, pi_text D <= r + 1 -> r + 1 < pi_text D + Z.of_nat (length (pi_tb D)) ->
  rest_atR (pi_tb D) (pi_text D) (r + 1) = pdc_b D r 1 :: rest_atR (pi_tb D) (pi_text D) (r + 2).
Proof.
  intros D r H1 H2. replace (r + 2) with (r + 1 + 1) by lia.
  apply (pdc_rest_cons _ _ _ _ H1). unfold pdc_b.
  rewrite (pdc_rest_nth (pi_tb D) (pi_text D) (r + 1) ltac:(lia)). all: (do 2 f_equal; lia).
Qed.
(* the obligations every run of this stretch leaves: the shadow of a text byte and of the cursor words *)
Lemma pdc_ra_text : forall D (W : world segs) mem mem' a n,
  src_rd W mem (pi_text D) (pi_tb D) ->
  pi_text D <= a -> a + n <= pi_text D + Z.of_nat (length (pi_tb D)) -> 0 <= n ->
  (forall x, a <= x < a + n ->
     aview segs (w_H W) mem' (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview segs (w_H W) mem') SHADOW_OFF a n.
Proof.
  intros D W mem mem' a n (_ & _ & _ & _ & Hsra & _) H1 H2 Hn HE.
  apply (pdc_ra_kept W mem mem' a n HE). intros x Hx. apply Hsra. lia.
Qed.


Lemma pdc_md_wvb : forall m1 m2, same_but_materialized m1 m2 ->
  forall X, same_but_materialized m1 (with_vm_backing (m_vm_lazy m2) X m2).
Proof.
  intros m1 m2 H X. eapply same_but_materialized_trans; [exact H | apply same_but_materialized_wvb_any].
Qed.
Lemma pdc_apresent_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HG (HE & b & Hb). split; [exact HE|].
  assert (Hne : mrestrict (w_H W) m (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite HE, Hb; discriminate).
  pose proof (HG _ Hne) as Hne'. unfold mrestrict in Hne'. rewrite HE in Hne'.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | contradiction].
Qed.
Lemma pdc_region_nth_pi : forall E ss (ms : machine_state) i rr,
  st_ok_pi segs VAL E ss ms -> nth_error (ss_mem ss) i = Some rr -> region_ok segs E (ms_mem ms) rr.
Proof.
  intros E ss ms i rr HS Hi. unfold st_ok_pi, abs_ss in HS.
  exact (pdc_region_nth E (setpc ss (BASE + ss_pc ss)) ms i rr HS Hi).
Qed.
(* the one write window of this stretch is the out byte, which lies in the block the malloc made *)
Lemma pdc_awr_w : forall D ly S Hp W mem md out w Q E (rs : smem),
  (forall a, in_wrange E rs a -> a = w) -> ps_alloc D ly S Hp W mem out Q -> ARx ly S Hp W mem md ->
  out <= w -> w <= out + Z.of_nat Q ->
  awr_ok E rs (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (ablocks B (pi_ly D) (pi_S D)) (ablocks B ly S) ly [].
Proof.
  intros D ly S Hp W mem md out w Q E rs Hw HAL HAR Hw1 Hw2 a Ha.
  pose proof cf_head_nonneg as Hh0. pose proof HW as Hhw. unfold prh_head_wide in Hhw.
  pose proof HAL as (_ & Hout & _ & _ & Eab & _).
  assert (Rqo : req_size (Z.of_nat Q + 1 + cf_head) = Z.of_nat Q + 1 + cf_head) by (apply pdc_req; lia).
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S))
    by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  rewrite (Hw a Ha). right. right. left.
  exists (out - cf_head), (Z.of_nat Q + 1 + cf_head).
  split; [exact Hin_o|].
  split; [apply (pdc_new_block ly S Hp W mem md (pi_ly D) (pi_S D) _ HAR Eab); cbn [snd]; rewrite Rqo; lia|].
  rewrite Rqo. lia.
Qed.

(* ---- THE ESCAPE SUBTREE: from offset 384 (the shadow check of text[r + 1]) through the compare tree to the eight
   stores, the \u cut and the four refusals ---- *)

(* ---- THE THREE EXITS THAT STORE NOTHING: the closing quote (RETOK), a refused byte (FREE) and the \u escape (U) ---- *)
Lemma pdc_free_leaf : forall CTX CW D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2,
  psb_seg_freeP B ARx SK CTX CW P ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  ps_gptp D regs2 -> getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 8 = w64 (pi_q D) ->
  PjGrammar.decode (rest_atR (pi_tb D) (pi_text D) r) = None ->
  SRr segs W (cfg_at segs (psb_pc PSB_FREE) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 HFREE HPRE HDEC HJ2 HMD HFR HGR HMNm
    HGT2 R2 R18 R8 Hnone.
  destruct (pdc_keep CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm)
    as (HC2 & HAL2 & HIN2 & HROD2 & KC & KT & KD).
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSCd & _ & _ & _ & _ & _ & _ & _ & HREL).
  pose proof HREL as (done & _ & _ & _ & HNo & _).
  apply ps_finP_hand. apply (HFREE D ly S Hp W regs2 mem2 md2 out Q HPRE).
  split; [exists k2; exact HC2|]. split; [exact HAL2|]. split; [exact HGT2|].
  split; [exact HIN2|]. split; [exact HROD2|]. split; [exact HSCd|].
  split; [exact (HNo Hnone)|]. split; [exact R2 | split; [exact R18 | exact R8]].
Qed.

Lemma pdc_retok_leaf : forall CTX CW D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2,
  psb_seg_retokP B ARx SK CTX CW P ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  psb_sh_regs D regs2 -> ps_gptp D regs2 ->
  getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 19 = w64 w ->
  getr regs2 20 = w64 r -> getr regs2 8 = w64 (pi_q D) -> getr regs2 9 = w64 (pi_q D + 8) ->
  r = pi_p D + 1 + Z.of_nat Q ->
  rest_atR (pi_tb D) (pi_text D) r = 34 :: rest_atR (pi_tb D) (pi_text D) (r + 1) ->
  SRr segs W (cfg_at segs (psb_pc PSB_RETOK) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 HRETOK HPRE HDEC HJ2 HMD HFR HGR HMNm
    HSH2 HGT2 R2 R18 R19 R20 R8 R9 Er Erest.
  destruct (pdc_keep CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm)
    as (HC2 & HAL2 & HIN2 & HROD2 & KC & KT & KD).
  pose proof HDEC as (_ & _ & _ & _ & _ & _ & _ & HSCd & _ & _ & _ & _ & _ & _ & _ & HREL).
  pose proof HREL as (done & Hbd & Hdl & HSo & _ & Hr & Hwo & Hww & _).
  apply ps_finP_of_postP. apply (HRETOK D ly S Hp W regs2 mem2 md2 out w r Q HPRE).
  split; [exists k2; exact HC2|]. split; [exact HAL2|]. split; [exact HSH2|]. split; [exact HGT2|].
  split; [exact HIN2|]. split; [exact HSCd|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|].
  split; [exact R8|]. split; [exact R9|]. split; [exact Er|].
  split.
  { exists done. split.
    { rewrite <- (app_nil_r done). apply HSo. rewrite Erest. exact (pdc_dec_quote _). }
    split; [|exact Hdl].
    unfold bytes_at in *. apply (pdc_garr_kept W mem mem2); [|exact Hbd].
    intros x Hx. apply KD. lia. }
  split; [exact Hwo | lia].
Qed.

Lemma pdc_u_leaf : forall CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2,
  psb_dec_ltP B ARx SK CTX CW P m -> psb_seg_uP B ARx SK CTX CW P ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  psb_sh_regs D regs2 -> ps_gptp D regs2 ->
  getr regs2 25 = w64 34 -> getr regs2 26 = w64 (-1) -> getr regs2 27 = w64 92 ->
  getr regs2 14 = w64 32 -> getr regs2 15 = w64 101 -> getr regs2 16 = w64 91 -> getr regs2 17 = w64 113 ->
  getr regs2 5 = w64 114 ->
  getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 19 = w64 w ->
  getr regs2 20 = w64 r -> getr regs2 21 = w64 (r + 2) -> getr regs2 10 = w64 (pi_text D + pi_len D) ->
  getr regs2 8 = w64 (pi_q D) -> getr regs2 9 = w64 (pi_q D + 8) ->
  nth_error (pi_tb D) (Z.to_nat (r - pi_text D)) = Some 92 ->
  nth_error (pi_tb D) (Z.to_nat (r + 1 - pi_text D)) = Some 117 ->
  (Q - Z.to_nat (r - (pi_p D + 1)) < Nat.succ m)%nat ->
  SRr segs W (cfg_at segs (psb_pc PSB_U) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 HLT HU HPRE HDEC HJ2 HMD HFR HGR HMNm
    HSH2 HGT2 C25 C26 C27 C14 C15 C16 C17 C5t R2 R18 R19 R20 R21 R10 R8 R9 Hb0 Hb1 Hmeas.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  destruct (pdc_keep CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm)
    as (HC2 & HAL2 & HIN2 & HROD2 & KC & KT & KD).
  pose proof HDEC as (_ & _ & _ & _ & HCST & _ & _ & HSCd & _ & _ & _ & _ & _ & _ & _ & HREL).
  destruct HCST as (_ & _ & _ & _ & _ & _ & _ & _ & V24w & V16w & V8w).
  assert (HCST2 : psb_dec_consts D W mem2 regs2).
  { split; [exact C25|]. split; [exact C26|]. split; [exact C27|]. split; [exact C14|]. split; [exact C15|].
    split; [exact C16|]. split; [exact C17|]. split; [exact C5t|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V24w]|].
    split; [apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V16w]|].
    apply (pdc_val_kept W mem mem2); [intros x Hx; apply KC; lia | exact V8w]. }
  assert (HREL2 : ps_dec_rel D W mem2 out w r Q).
  { pose proof HREL as (done & Hbd & Hdl & HSo & HNo & Hr & Hwo & Hww & Hsync).
    exists done. split; [|split; [exact Hdl | split; [exact HSo | split; [exact HNo |
      split; [exact Hr | split; [exact Hwo | split; [exact Hww | exact Hsync]]]]]]].
    unfold bytes_at in *. apply (pdc_garr_kept W mem mem2); [|exact Hbd].
    intros x Hx. apply KD. lia. }
  apply ps_finP_hand. apply (HU m HLT D ly S Hp W regs2 mem2 md2 out w r Q HPRE); [|apply Nat.lt_succ_r; exact Hmeas].
  split; [exists k2; exact HC2|]. split; [exact HAL2|]. split; [exact HSH2|]. split; [exact HGT2|].
  split; [exact HCST2|]. split; [exact HIN2|]. split; [exact HROD2|]. split; [exact HSCd|].
  split; [exact R2|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
  split; [exact R10|]. split; [exact R8|]. split; [exact R9|].
  split; [exact Hb0 | split; [exact Hb1 | exact HREL2]].
Qed.


(* ---- THE ESCAPE SUBTREE: from offset 384 through the compare tree ---- *)
Lemma pdc_esc : forall CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2,
  psb_dec_ltP B ARx SK CTX CW P m -> psb_seg_uP B ARx SK CTX CW P -> psb_seg_freeP B ARx SK CTX CW P ->
  ps_pre CTX CW D -> psb_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  AJ (PS_WSTK D) (PS_WSP D) [(pi_q D, pi_q D + 8)] (pi_ly D) (pi_S D) (pi_Hp D) (pi_W D) (pi_mem D) (pi_md D) []
     ly S Hp W mem2 md2 k2 ->
  same_but_materialized md md2 ->
  (forall x : word, bv_unsigned x <> w -> rdW W mem2 x = rdW W mem x) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  P mem2 ->
  psb_sh_regs D regs2 -> ps_gptp D regs2 ->
  getr regs2 25 = w64 34 -> getr regs2 26 = w64 (-1) -> getr regs2 27 = w64 92 ->
  getr regs2 14 = w64 32 -> getr regs2 15 = w64 101 -> getr regs2 16 = w64 91 -> getr regs2 17 = w64 113 ->
  getr regs2 5 = w64 114 ->
  getr regs2 2 = w64 (PS_SP D) -> getr regs2 18 = w64 out -> getr regs2 19 = w64 w ->
  getr regs2 20 = w64 r -> getr regs2 21 = w64 (r + 1) -> getr regs2 10 = w64 (pi_text D + pi_len D) ->
  getr regs2 8 = w64 (pi_q D) -> getr regs2 9 = w64 (pi_q D + 8) ->
  pdc_b D r 0 = 92 -> r + 1 < pi_text D + pi_len D ->
  (Q - Z.to_nat (r - (pi_p D + 1)) < Nat.succ m)%nat ->
  SRr segs W (cfg_at segs (psb_pc PSB_ESC) regs2 mem2 md2) (ps_post CW D).
Proof.
  intros CTX CW m D ly S Hp W regs mem md out w r Q regs2 mem2 md2 k2 HLT HU HFREE HPRE HDEC HJ2 HMD HFR HGR HMNm
    HSH2 HGT2 C25 C26 C27 C14 C15 C16 C17 C5t R2 R18 R19 R20 R21 R10 R8 R9 Hb92 Hr1 Hmeas.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HDEC as (HC & HAL & _ & _ & HCST & HIN & HROD & HSCd & _ & _ & _ & _ & _ & _ & _ & HREL).
  pose proof HC as (k & HJ & HK & HSV & HSRC & HHOME & HMN0).
  destruct HIN as (Vp & Ve & Vd & Hrw & _ & _ & Ht62 & Htp' & Hlentb & Hg & Hqt & Hd).
  pose proof HREL as (done & Hbd & Hdl & HSo & HNo & Hr & Hwo & Hww & Hsync).
  pose proof HAL as (HALc & HALout & HALo16 & EHp & Eab & HLED & HVIS & HALroom & HALrp & HALbb).
  assert (Hout_t : forall a, pi_text D <= a < pi_text D + pi_len D -> a < out - cf_head \/ out + Z.of_nat Q + 1 <= a)
    by (intros a Ha; exact (pdc_txt_out D ly S Hp W mem md out Q a HAR HHOME HAL HLED Ha)).
  destruct (pdc_keep CTX CW D ly S Hp W regs mem md out w r Q mem2 md2 k2 HPRE HDEC HJ2 HMD HFR HGR HMNm)
    as (HC2 & HAL2 & HIN2 & HROD2 & KC & KT & KD).
  pose proof HC2 as (_ & _ & _ & HSRC2 & _).
  pose proof HIN2 as (Vp2 & Ve2 & Vd2 & Hrw2 & _).
  pose proof HAL2 as (_ & _ & _ & _ & _ & _ & (HVRA2 & _) & _ & _ & _).
  pose proof (ajx_ar HJ2) as HAR2. cbv beta in HAR2.
  destruct (pdc_byte D W mem2 r 1 (proj1 HSRC2) ltac:(lia) ltac:(lia)) as [V1 B1].
  destruct (pdc_byte D W mem r 1 Hg ltac:(lia) ltac:(lia)) as [_ B1'].
  (* the text from r, and the model's two steps *)
  assert (Hrest2 : rest_atR (pi_tb D) (pi_text D) r
                 = 92 :: pdc_b D r 1 :: rest_atR (pi_tb D) (pi_text D) (r + 2)).
  { rewrite (pdc_rest_at0 D r ltac:(lia) ltac:(lia)), Hb92. f_equal.
    exact (pdc_rest_at1 D r ltac:(lia) ltac:(lia)). }
  assert (Hscan2 : PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) r)
        = option_map (fun q => (q + Z.to_nat 2)%nat) (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 2)))).
  { rewrite Hrest2, pdc_scan_esc.
    destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 2))); cbn [option_map];
      [f_equal; cbn [Z.to_nat Pos.to_nat Pos.iter_op]; lia | reflexivity]. }
  assert (Hrj2 : r + 2 <= pi_p D + 1 + Z.of_nat Q).
  { rewrite Hsync in Hscan2.
    destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 2))) as [k2'|] eqn:E2;
      cbn [option_map] in Hscan2; [|discriminate].
    injection Hscan2 as Hscan2.
    assert (Hge : (2 <= Q - Z.to_nat (r - (pi_p D + 1)))%nat)
      by (rewrite Hscan2; cbn [Z.to_nat Pos.to_nat Pos.iter_op]; lia).
    assert (Hle : (Z.to_nat (r - (pi_p D + 1)) <= Q)%nat)
      by (apply (proj2 (Nat2Z.inj_le _ _)); rewrite Z2Nat.id by lia; lia).
    assert (Hsum : (Z.to_nat (r - (pi_p D + 1)) + 2 <= Q)%nat).
    { rewrite <- (Nat.sub_add _ Q Hle). rewrite (Nat.add_comm (Z.to_nat (r - (pi_p D + 1))) 2).
      apply Nat.add_le_mono_r. exact Hge. }
    assert (HZ2 : Z.of_nat (Z.to_nat (r - (pi_p D + 1)) + 2) <= Z.of_nat Q) by (apply Nat2Z.inj_le; exact Hsum).
    rewrite Nat2Z.inj_add, Z2Nat.id in HZ2 by lia. cbn [Z.of_nat] in HZ2. lia. }
  (* the symbolic state at the escape entry *)
  set (E := EB (Ereg regs2 [w64 (pdc_b D r 0); w64 (pdc_b D r 1)])).
  assert (EW : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr regs2 x)
    by (intros n x Hn; subst E; rewrite Eimg_low by (pose proof (u5_range x); unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (EW33 : ew E 33 = w64 (pdc_b D r 1))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (EW9 : ew E 9 = w64 (pi_q D + 8)) by (rewrite (EW 9%nat 9%bv eq_refl); exact R9).
  assert (EW10 : ew E 10 = w64 (pi_text D + pi_len D)) by (rewrite (EW 10%nat 10%bv eq_refl); exact R10).
  assert (EW19 : ew E 19 = w64 w) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
  assert (EW20 : ew E 20 = w64 r) by (rewrite (EW 20%nat 20%bv eq_refl); exact R20).
  assert (EW21 : ew E 21 = w64 (r + 1)) by (rewrite (EW 21%nat 21%bv eq_refl); exact R21).
  assert (EW23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EW 23%nat 23%bv eq_refl); exact (proj1 HSH2)).
  assert (EW2 : ew E 2 = w64 (PS_SP D)) by (rewrite (EW 2%nat 2%bv eq_refl); exact R2).
  assert (EW18 : ew E 18 = w64 out) by (rewrite (EW 18%nat 18%bv eq_refl); exact R18).
  assert (EW8 : ew E 8 = w64 (pi_q D)) by (rewrite (EW 8%nat 8%bv eq_refl); exact R8).
  assert (EW22 : ew E 22 = w64 (SHADOW_OFF + pi_q D / 8))
    by (rewrite (EW 22%nat 22%bv eq_refl); exact (proj1 (proj2 HSH2))).
  assert (EW25 : ew E 25 = w64 34) by (rewrite (EW 25%nat 25%bv eq_refl); exact C25).
  assert (EW26 : ew E 26 = w64 (-1)) by (rewrite (EW 26%nat 26%bv eq_refl); exact C26).
  assert (EW27 : ew E 27 = w64 92) by (rewrite (EW 27%nat 27%bv eq_refl); exact C27).
  assert (EW14 : ew E 14 = w64 32) by (rewrite (EW 14%nat 14%bv eq_refl); exact C14).
  assert (EW15 : ew E 15 = w64 101) by (rewrite (EW 15%nat 15%bv eq_refl); exact C15).
  assert (EW16 : ew E 16 = w64 91) by (rewrite (EW 16%nat 16%bv eq_refl); exact C16).
  assert (EW17 : ew E 17 = w64 113) by (rewrite (EW 17%nat 17%bv eq_refl); exact C17).
  assert (EW5 : ew E 5 = w64 114) by (rewrite (EW 5%nat 5%bv eq_refl); exact C5t).
  assert (EW3 : ew E 3 = getr regs2 3) by (exact (EW 3%nat 3%bv eq_refl)).
  assert (EW4 : ew E 4 = getr regs2 4) by (exact (EW 4%nat 4%bv eq_refl)).
  pose proof HSRC2 as (_ & _ & _ & _ & Hsra2 & _).
  pose proof HGT2 as (Hgp2 & Htp2).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (Hwr : writable_at segs (rdW W mem2) w).
  { apply (pdc_writable_kept W mem mem2 w (HGR w)). apply apresent_writable. apply (proj1 (Hpres w ltac:(lia))). }
  assert (HS : st_ok_pi segs VAL E pdc_ss_e
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + (PSB_OFF + PSB_ESC))) mem2 (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold pdc_ss_e. apply pa_entry_st_ok_full.
    - apply pdc_regs_ok_pins; [subst E; apply regs_ok_Eimg_Ereg|].
      unfold pdc_pin_dec.
      repeat (apply Forall_cons; [cbn [fst snd]|]); [..|apply Forall_nil].
      + rewrite (proj2 (proj2 HSH2)). symmetry. exact (pdc_sv_shx E 9 (pi_q D + 8) EW9 ltac:(lia) EW23).
      + exact C25.
      + exact C26.
      + exact C27.
      + exact C14.
      + exact C15.
      + exact C16.
      + exact C17.
      + exact C5t.
    - vm_compute. reflexivity.
    - apply Forall_cons;
        [exact (pdc_rok_in E _ (pi_q D + 8) (pi_text D + pi_len D) EW9 EW10 ltac:(lia) ltac:(lia) ltac:(lia) Ve2)|].
      apply Forall_cons; [|apply Forall_cons; [exact (pdc_rok_o E _ w EW19 ltac:(lia) ltac:(lia) Hwr)|apply Forall_nil]].
      unfold region_ok, pdc_rg_t5.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EW21, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (r + 1) 0 1 (SOff 33 0) (pdc_b D r 1));
        [exact (pdc_denot_atom E 33 _ EW33 ltac:(lia)) | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V1].
    - apply pairwise_disjoint_of_extents.
      unfold pdc_rg_in, pdc_rg_t5, pdc_rg_o, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite EW9, EW19, EW21, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      pose proof (Hout_t (r + 1) ltac:(lia)) as Hwr1.
      destruct Hqt as [Hqt|Hqt]; destruct Hwr1 as [Hwr1|Hwr1]; repeat split; lia.
    - split; [|split; [exact I | exact I]]. cbn [pdc_afacts_e f_atoms atoms_ok].
      split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
      + apply (pdc_afact_rng E 9 (pi_q D + 8)); [exact EW9 | lia | lia | | lia].
        change (2 ^ 3) with 8. rewrite Z.add_mod, Hq8 by lia. reflexivity.
      + apply (pdc_afact_rng E 19 w); [exact EW19 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (pdc_afact_rng E 20 r); [exact EW20 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (pdc_afact_rng E 21 (r + 1)); [exact EW21 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (pdc_afact_rng E 23 SHADOW_OFF);
          [exact EW23 | lia | unfold SHADOW_OFF; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (pdc_afact_rng E 33 (pdc_b D r 1));
          [exact EW33 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok segs pdc_Bx pdc_SH E (rdW W mem2)).
  { unfold sh_ok, pdc_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem2 E pdc_Bx 19 out (Z.of_nat Q + 1) w 0 1 HVRA2).
    - unfold pdc_Bx. rewrite U_SOff, EW23. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
      apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    - rewrite U_SOff, EW19. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
      apply zcanon_id. unfold M64. lia.
    - lia.
    - lia.
    - intros x Hx. pose proof (Happ x ltac:(lia)) as Hax.
      unfold app_addr, kLowShadowBeg, kHighMemBeg in Hax. unfold SHADOW_OFF. lia. }
  pose proof HMNm as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (BR := @paj_branch fx rc B_prog_listing PSB_PAImg).
  unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_ESC) with (BASE + (PSB_OFF + PSB_ESC)) by lia.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { (* the shadow of text[r + 1] *)
    unfold ob_holds. cbn [ob_x ob_n].
    replace (U E pdc_Bx) with SHADOW_OFF
      by (unfold pdc_Bx; rewrite U_SOff, EW23; unfold w64;
          rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r;
          symmetry; apply zcanon_id; unfold SHADOW_OFF, M64; lia).
    replace (U E (SOff 21 0)) with (r + 1)
      by (rewrite U_SOff, EW21; unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
          symmetry; apply zcanon_id; unfold M64; lia).
    intros x Hx. apply Hsra2. lia. }
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 <= 101 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ge33 Hc 101 EW33. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hb12f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 <= 113 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ge33 Hc 113 EW33. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hb6f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 114 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq33 Hc 114 EW33. apply Z.eqb_neq in Hc. rename Hc into Hb3f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 116 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq33 Hc 116 EW33. apply Z.eqb_neq in Hc. rename Hc into Hb2f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 117 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ne33 Hc 117 EW33. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1f.
  (* the \u escape: hand the walk to psb_seg_u at m *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_U).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  pmkst HS.
  psb_pc_fold PSB_U.
  apply (pdc_u_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 HLT HU HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T19; pdc_ew EW19 | cbn [ms_regs]; rewrite T20; pdc_ew EW20
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T10; pdc_ew EW10 | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9
    | rewrite (pdc_rest_nth (pi_tb D) (pi_text D) r ltac:(lia)); f_equal; rewrite <- Hb92;
      unfold pdc_b; f_equal; lia
    | rewrite (pdc_rest_nth (pi_tb D) (pi_text D) (r + 1) ltac:(lia)); f_equal; rewrite <- Hb1f;
      unfold pdc_b; f_equal; lia
    | exact Hmeas ].
  }
  pdc_hc_ne33 Hc 117 EW33. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hb1t.
  (* a bad escape above 113: the escape is not one of the eight, so decode is None *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_FREE).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (8%bv : bv 5) T8.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_FREE.
  apply (pdc_free_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k2 HFREE HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T8; pdc_ew EW8
    | rewrite Hrest2; apply (pdc_dec_esc_bad (pdc_b D r 1));
      [lia | unfold PjGrammar.escape; repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia); reflexivity] ].
  }
  pdc_hc_eq33 Hc 116 EW33. apply Z.eqb_eq in Hc. rename Hc into Hb2t.
  (* the escape byte 116 stores 9 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 9);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 9) 9 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 9 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 9);
        [lia | rewrite Hb2t; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_eq33 Hc 114 EW33. apply Z.eqb_eq in Hc. rename Hc into Hb3t.
  (* the escape byte 114 stores 13 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 13);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 13) 13 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 13 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 13);
        [lia | rewrite Hb3t; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_ge33 Hc 113 EW33. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hb6t.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 102 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq33 Hc 102 EW33. apply Z.eqb_neq in Hc. rename Hc into Hb5f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 110 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ne33 Hc 110 EW33. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb4f.
  (* the escape byte 110 stores 10 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 10);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 10) 10 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 10 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 10);
        [lia | rewrite Hb4f; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_ne33 Hc 110 EW33. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hb4t.
  (* a bad escape in (101, 113]: the escape is not one of the eight, so decode is None *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_FREE).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (8%bv : bv 5) T8.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_FREE.
  apply (pdc_free_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k2 HFREE HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T8; pdc_ew EW8
    | rewrite Hrest2; apply (pdc_dec_esc_bad (pdc_b D r 1));
      [lia | unfold PjGrammar.escape; repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia); reflexivity] ].
  }
  pdc_hc_eq33 Hc 102 EW33. apply Z.eqb_eq in Hc. rename Hc into Hb5t.
  (* the escape byte 102 stores 12 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 12);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 12) 12 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 12 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 12);
        [lia | rewrite Hb5t; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_ge33 Hc 101 EW33. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hb12t.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* 91 < b1 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_lt33 Hc 91 EW33. apply Z.ltb_ge in Hc. rename Hc into Hb11f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 34 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq33 Hc 34 EW33. apply Z.eqb_neq in Hc. rename Hc into Hb8f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 47 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ne33 Hc 47 EW33. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb7f.
  (* the escape byte 47 stores 47 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 47);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 47) 47 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 47 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 47);
        [lia | rewrite Hb7f; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_ne33 Hc 47 EW33. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hb7t.
  (* a bad escape at or below 91: the escape is not one of the eight, so decode is None *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_FREE).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (8%bv : bv 5) T8.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_FREE.
  apply (pdc_free_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k2 HFREE HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T8; pdc_ew EW8
    | rewrite Hrest2; apply (pdc_dec_esc_bad (pdc_b D r 1));
      [lia | unfold PjGrammar.escape; repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia); reflexivity] ].
  }
  pdc_hc_eq33 Hc 34 EW33. apply Z.eqb_eq in Hc. rename Hc into Hb8t.
  (* the escape byte 34 stores 34 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 34);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 34) 34 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 34 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 34);
        [lia | rewrite Hb8t; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_lt33 Hc 91 EW33. apply Z.ltb_lt in Hc. rename Hc into Hb11t.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 92 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq33 Hc 92 EW33. apply Z.eqb_neq in Hc. rename Hc into Hb10f.
  paj_run_tok_x_inv RUN HS HJ2 SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* b1 = 98 ? *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ne33 Hc 98 EW33. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb9f.
  (* the escape byte 98 stores 8 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 8);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 8) 8 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 8 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 8);
        [lia | rewrite Hb9f; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
  }
  pdc_hc_ne33 Hc 98 EW33. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hb9t.
  (* a bad escape in (91, 101]: the escape is not one of the eight, so decode is None *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_FREE).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (8%bv : bv 5) T8.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_FREE.
  apply (pdc_free_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k2 HFREE HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T8; pdc_ew EW8
    | rewrite Hrest2; apply (pdc_dec_esc_bad (pdc_b D r 1));
      [lia | unfold PjGrammar.escape; repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia); reflexivity] ].
  }
  pdc_hc_eq33 Hc 92 EW33. apply Z.eqb_eq in Hc. rename Hc into Hb10t.
  (* the escape byte 92 stores 92 *)
  paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 92);
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SLit 92) 92 RO eq_refl ltac:(left; reflexivity)
        ltac:(reflexivity) ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k2 2 92 HLT HPRE HDEC HJ2);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 2 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest2; apply (pdc_dec_esc (pdc_b D r 1) 92);
        [lia | rewrite Hb10t; vm_compute; reflexivity]
    | exact Hscan2 | lia | exact Hrj2 | exact Hmeas ].
Qed.

(* ---- THE STRETCH at P: the decode loop body, from the head at offset 324 ---- *)
Lemma pdc_stepP : forall CTX CW,
  psb_seg_uP B ARx SK CTX CW P -> psb_seg_freeP B ARx SK CTX CW P -> psb_seg_retokP B ARx SK CTX CW P ->
  psb_dec_stepP B ARx SK CTX CW P.
Proof.
  intros CTX CW HU HFREE HRETOK m HLT D ly S Hp W regs mem md out w r Q HPRE HDEC Hmeas.
  apply ps_finP_SRr'.
  destruct (pdc_facts CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hsp46 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hpr1 & Hrlt & Htc & Hlen & Hout & Hw1 & Hw2
        & Hoc & Hin_o & Happ & Hpres & Hclo & Hslo & Hshi & Hqhi & HAR).
  pose proof cf_head_nonneg as Hh0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HDEC as (HC & HAL & HSH2 & HGT2 & HCST & HIN & HROD & HSCd & R2 & R18 & R19 & R20 & R10 & R8 & R9
    & HREL).
  pose proof HC as (k & HJ & HK & HSV & HSRC & HHOME & HMN0).
  pose proof HSRC as (Hsb & H4096 & Hsc & Hamr & Hsra & Hshu).
  pose proof HIN as (Vp & Ve & Vd & Hrw & _ & _ & Ht62 & Htp' & Hlentb & Hg & Hqt & Hd).
  pose proof HREL as (done & Hbd & Hdl & HSo & HNo & Hr & Hwo & Hww & Hsync).
  pose proof HGT2 as (Hgp2 & Htp2).
  pose proof HCST as (C25 & C26 & C27 & C14 & C15 & C16 & C17 & C5t & V24w & V16w & V8w).
  destruct (pdc_byte D W mem r 0 Hg ltac:(lia) ltac:(lia)) as [V0 B0].
  assert (Hrest1 : rest_atR (pi_tb D) (pi_text D) r
                 = pdc_b D r 0 :: rest_atR (pi_tb D) (pi_text D) (r + 1))
    by (apply (pdc_rest_at0 D r ltac:(lia) ltac:(lia))).
  (* the stretch starts with the cut's own memory and model *)
  pose proof (same_but_materialized_refl md) as HMD.
  pose proof (fun (x : word) (_ : bv_unsigned x <> w) => eq_refl : rdW W mem x = rdW W mem x) as HFR.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) => Ha) as HGR.
  destruct (pdc_entry CTX CW D ly S Hp W regs mem md out w r Q false HPRE HDEC ltac:(discriminate))
    as [HS SHOK].
  set (E := pdc_E D regs r) in *.
  assert (EW : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = getr regs x)
    by (intros n x Hn; subst E; apply pdc_ew_reg; exact Hn).
  assert (EW32 : ew E 32 = w64 (pdc_b D r 0)) by (subst E; exact (pdc_ew_b D regs r 0 ltac:(lia))).
  assert (EW9 : ew E 9 = w64 (pi_q D + 8)) by (rewrite (EW 9%nat 9%bv eq_refl); exact R9).
  assert (EW10 : ew E 10 = w64 (pi_text D + pi_len D)) by (rewrite (EW 10%nat 10%bv eq_refl); exact R10).
  assert (EW19 : ew E 19 = w64 w) by (rewrite (EW 19%nat 19%bv eq_refl); exact R19).
  assert (EW20 : ew E 20 = w64 r) by (rewrite (EW 20%nat 20%bv eq_refl); exact R20).
  assert (EW2 : ew E 2 = w64 (PS_SP D)) by (rewrite (EW 2%nat 2%bv eq_refl); exact R2).
  assert (EW18 : ew E 18 = w64 out) by (rewrite (EW 18%nat 18%bv eq_refl); exact R18).
  assert (EW8 : ew E 8 = w64 (pi_q D)) by (rewrite (EW 8%nat 8%bv eq_refl); exact R8).
  assert (EW22 : ew E 22 = w64 (SHADOW_OFF + pi_q D / 8))
    by (rewrite (EW 22%nat 22%bv eq_refl); exact (proj1 (proj2 HSH2))).
  assert (EW23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (EW 23%nat 23%bv eq_refl); exact (proj1 HSH2)).
  assert (EW3 : ew E 3 = getr regs 3) by (exact (EW 3%nat 3%bv eq_refl)).
  assert (EW4 : ew E 4 = getr regs 4) by (exact (EW 4%nat 4%bv eq_refl)).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply pdc_img_E).
  pose proof HMN0 as HPM.
  pose (RUN := @paj_run_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (RUNTO := @paj_run_to_x_inv fx rc SK _ PSB_PAListing PSB_PAImg B PST ARx _ LAWS _ PLAW).
  pose (BR := @paj_branch fx rc B_prog_listing PSB_PAImg).
  unfold cfg_at, psb_pc, w64. replace (BASE + PSB_OFF + PSB_DEC) with (BASE + (PSB_OFF + PSB_DEC)) by lia.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM pdc_Bspan.
  { (* the shadow of text[r] *)
    unfold ob_holds. cbn [ob_x ob_n].
    lazymatch goal with |- context [U ?Ex (SOff 20 0)] =>
      replace (U Ex pdc_Bx) with SHADOW_OFF
        by (unfold pdc_Bx; rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite EW23; unfold w64;
            rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r;
            symmetry; apply zcanon_id; unfold SHADOW_OFF, M64; lia);
      replace (U Ex (SOff 20 0)) with r
        by (rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite EW20; unfold w64;
            rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
            symmetry; apply zcanon_id; unfold M64; lia) end.
    apply (pdc_ra_kept W mem _ r 1); [|intros x Hx; apply Hsra; lia].
    intros x Hx. apply (aview_eq_of segs). apply HFR.
    pose proof (pdc_shadow_band x ltac:(lia)) as Hsbx.
    rewrite unsigned_lit_small by (unfold shadow_of_addr, SHADOW_OFF in *; lia).
    intros Ew. pose proof (Happ w ltac:(lia)) as Hwa. unfold shadow_of_addr in Ew.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    destruct Hwa as (H4 & [Hl|[Hh1 Hh2]]); lia. }
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* text[r] = 34 ? the closing quote *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_eq32 Hc 34 EW32. apply Z.eqb_neq in Hc. rename Hc into Hne34.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM pdc_Bspan.
  { (* the shadow of text[r] *)
    unfold ob_holds. cbn [ob_x ob_n].
    lazymatch goal with |- context [U ?Ex (SOff 20 0)] =>
      replace (U Ex pdc_Bx) with SHADOW_OFF
        by (unfold pdc_Bx; rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite EW23; unfold w64;
            rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); rewrite Z.add_0_r;
            symmetry; apply zcanon_id; unfold SHADOW_OFF, M64; lia);
      replace (U Ex (SOff 20 0)) with r
        by (rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite EW20; unfold w64;
            rewrite unsigned_lit_small by lia; rewrite Z.add_0_r;
            symmetry; apply zcanon_id; unfold M64; lia) end.
    apply (pdc_ra_kept W mem _ r 1); [|intros x Hx; apply Hsra; lia].
    intros x Hx. apply (aview_eq_of segs). apply HFR.
    pose proof (pdc_shadow_band x ltac:(lia)) as Hsbx.
    rewrite unsigned_lit_small by (unfold shadow_of_addr, SHADOW_OFF in *; lia).
    intros Ew. pose proof (Happ w ltac:(lia)) as Hwa. unfold shadow_of_addr in Ew.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    destruct Hwa as (H4 & [Hl|[Hh1 Hh2]]); lia. }
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* text[r] < 32 ? a control byte *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  1:{ pdc_hc_ltu32 Hc 32 EW32. apply Z.ltb_lt in Hc. rename Hc into Hctl.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pdc_Bspan (PSB_OFF + PSB_FREE).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (8%bv : bv 5) T8.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_FREE.
  apply (pdc_free_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k HFREE HPRE HDEC HJ);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T8; pdc_ew EW8
    | rewrite Hrest1; exact (pdc_dec_ctl (pdc_b D r 0) _ Hne34 Hctl) ].
  }
  pdc_hc_ltu32 Hc 32 EW32. apply Z.ltb_ge in Hc. rename Hc into Hge32.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM pdc_Bspan.
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* text[r] = 92 ? a backslash *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  2:{ pdc_hc_ne32 Hc 92 EW32. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hbs.
  (* the escape subtree *)
  assert (Hr1 : r + 1 < pi_text D + pi_len D).
  { destruct (Z_lt_le_dec (r + 1) (pi_text D + pi_len D)) as [Hl|Hl]; [exact Hl|exfalso].
    rewrite Hrest1, Hbs in Hsync.
    assert (Erest : rest_atR (pi_tb D) (pi_text D) (r + 1) = [])
      by (unfold rest_atR; apply skipn_all2; lia).
    rewrite Erest in Hsync. cbn [PjGrammar.scan] in Hsync. discriminate. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pdc_Bspan (PSB_OFF + PSB_ESC).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  (* r + 1 < end: the bound check before the escape byte is not taken *)
  psrr_branch_tok RUN BR HS SHOK pdc_Bspan.
  1:{ exfalso.
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      rewrite (pdc_br_geu_off Ex 20 10 r (pi_text D + pi_len D) 1 ltac:(pdc_ew EW20) ltac:(pdc_ew EW10)
        ltac:(lia) ltac:(lia) ltac:(lia)) in Hc end.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pdc_Bspan (PSB_OFF + PSB_ESC).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  pmkst HS.
  psb_pc_fold PSB_ESC.
  apply (pdc_esc CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k HLT HU HFREE HPRE HDEC HJ);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T19; pdc_ew EW19 | cbn [ms_regs]; rewrite T20; pdc_ew EW20
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 1 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T10; pdc_ew EW10 | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9
    | exact Hbs | exact Hr1 | exact Hmeas ].
  }
  pdc_hc_ne32 Hc 92 EW32. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hne92.
  (* the plain byte: store it and rejoin the head *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pdc_Bspan (PSB_OFF + PSB_JOIN).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (10%bv : bv 5) T10.
  prreg HS (21%bv : bv 5) T21. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
  prreg HS (14%bv : bv 5) T14. prreg HS (15%bv : bv 5) T15. prreg HS (16%bv : bv 5) T16.
  prreg HS (17%bv : bv 5) T17. prreg HS (5%bv : bv 5) T5. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  pose proof (pdc_region_nth_pi _ _ _ 2%nat _ HS eq_refl) as RO.
  cbn [ms_mem restrict] in RO.
  lazymatch type of RO with
  | region_ok _ ?Ex ?M _ =>
    assert (Vw : val_mem segs M w 1 (pdc_b D r 0));
    [ replace w with (bv_unsigned (ew Ex 19%nat) + 0)
        by (rewrite (pdc_uval Ex 19%nat _ ltac:(pdc_ew EW19) ltac:(lia)); lia);
      exact (pdc_field1 Ex _ 19%nat _ _ _ _ _ _ 0 (SOff 32 0) (pdc_b D r 0) RO eq_refl
        ltac:(left; reflexivity) ltac:(exact (pdc_denot_atom Ex 32%nat _ ltac:(pdc_ew EW32) ltac:(lia)))
        ltac:(lia))
    | ] end.
  pmkst HS.
  psb_pc_fold PSB_JOIN.
  apply (pdc_store_leaf CTX CW m D ly S Hp W regs mem md out w r Q _ _ _ k 1 (pdc_b D r 0)
    HLT HPRE HDEC HJ);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM | exact Vw | lia
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18
    | cbn [ms_regs]; rewrite T10; exact (pdc_off_val E 19 w 1 EW19 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T21; exact (pdc_off_val E 20 r 1 EW20 ltac:(lia) ltac:(lia))
    | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9 | cbn [ms_regs]; rewrite T25; reflexivity | cbn [ms_regs]; rewrite T26; reflexivity | cbn [ms_regs]; rewrite T27; reflexivity | cbn [ms_regs]; rewrite T14; reflexivity | cbn [ms_regs]; rewrite T15; reflexivity | cbn [ms_regs]; rewrite T16; reflexivity | cbn [ms_regs]; rewrite T17; reflexivity | cbn [ms_regs]; rewrite T5; reflexivity
    | rewrite Hrest1; exact (pdc_dec_plain (pdc_b D r 0) _ Hne34 Hge32 Hne92)
    | rewrite Hrest1, (pdc_scan_plain (pdc_b D r 0) _ Hne34 Hne92);
      destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 1))); cbn [option_map];
        [f_equal; cbn [Z.to_nat Pos.to_nat Pos.iter_op]; lia | reflexivity]
    | lia
    | (* r + 1 <= p + 1 + Q *)
      rewrite Hrest1, (pdc_scan_plain (pdc_b D r 0) _ Hne34 Hne92) in Hsync;
      destruct (PjGrammar.scan (rest_atR (pi_tb D) (pi_text D) (r + 1))) as [k1|] eqn:Ek1;
        cbn [option_map] in Hsync; [|discriminate];
      injection Hsync as Hsync;
      assert (Hle1 : (Z.to_nat (r - (pi_p D + 1)) <= Q)%nat)
        by (apply (proj2 (Nat2Z.inj_le _ _)); rewrite Z2Nat.id by lia; lia);
      assert (Hge1 : (1 <= Q - Z.to_nat (r - (pi_p D + 1)))%nat) by (rewrite <- Hsync; lia);
      assert (Hsum1 : (Z.to_nat (r - (pi_p D + 1)) + 1 <= Q)%nat)
        by (rewrite <- (Nat.sub_add _ Q Hle1); rewrite (Nat.add_comm (Z.to_nat (r - (pi_p D + 1))) 1);
            apply Nat.add_le_mono_r; exact Hge1);
      assert (HZ1 : Z.of_nat (Z.to_nat (r - (pi_p D + 1)) + 1) <= Z.of_nat Q)
        by (apply Nat2Z.inj_le; exact Hsum1);
      rewrite Nat2Z.inj_add, Z2Nat.id in HZ1 by lia; cbn [Z.of_nat] in HZ1; lia
    | exact Hmeas ].
  }
  (* the closing quote: r is at p + 1 + Q and decode finishes *)
  pdc_hc_eq32 Hc 34 EW32. apply Z.eqb_eq in Hc. rename Hc into Hq34.
  assert (Erq : r = pi_p D + 1 + Z.of_nat Q).
  { rewrite Hrest1, Hq34 in Hsync. cbn [PjGrammar.scan] in Hsync. injection Hsync as Hsync.
    assert (Hle0 : (Z.to_nat (r - (pi_p D + 1)) <= Q)%nat)
      by (apply (proj2 (Nat2Z.inj_le _ _)); rewrite Z2Nat.id by lia; lia).
    assert (Heq0 : (Q - Z.to_nat (r - (pi_p D + 1)))%nat = 0%nat) by (symmetry; exact Hsync).
    assert (HQ : Q = Z.to_nat (r - (pi_p D + 1))) by (apply Nat.le_antisymm; [lia | exact Hle0]).
    assert (HZq : Z.of_nat Q = r - (pi_p D + 1)) by (rewrite HQ, Z2Nat.id by lia; reflexivity).
    lia. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM pdc_Bspan (PSB_OFF + PSB_RETOK).
  { apply (pdc_awr_w D ly S Hp W mem md out w Q _ _); [pdc_wr1 EW19 | exact HAL | exact HAR | lia | lia]. }
  pose proof (fun (x : word) (Hx : bv_unsigned x <> w) =>
    eq_trans (HFr x ltac:(pdc_nowr EW19 Hx)) (HFR x Hx)) as HFRn.
  pose proof (fun (a : Z) (Ha : apresent (w_H W) mem a) =>
    pdc_apresent_grows W _ _ a HG (HGR a Ha)) as HGRn.
  clear HFR HFr HGR HG. rename HFRn into HFR. rename HGRn into HGR.
  prreg HS (2%bv : bv 5) T2. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  pmkst HS.
  psb_pc_fold PSB_RETOK.
  apply (pdc_retok_leaf CTX CW D ly S Hp W regs mem md out w r Q _ _ _ k HRETOK HPRE HDEC HJ);
    [ repeat (apply pdc_md_wvb); exact HMD | exact HFR | exact HGR | exact HPM
    | split; [cbn [ms_regs]; rewrite T23; pdc_ew EW23 | split; [cbn [ms_regs]; rewrite T22; pdc_ew EW22 | cbn [ms_regs]; rewrite T24; exact (pdc_shx_alu E 9 (pi_q D + 8) EW9 ltac:(lia) EW23)]] | split; [cbn [ms_regs]; rewrite T3; pdc_ewr EW3; exact Hgp2 | cbn [ms_regs]; rewrite T4; pdc_ewr EW4; exact Htp2] | cbn [ms_regs]; rewrite T2; pdc_ew EW2 | cbn [ms_regs]; rewrite T18; pdc_ew EW18 | cbn [ms_regs]; rewrite T19; pdc_ew EW19 | cbn [ms_regs]; rewrite T20; pdc_ew EW20 | cbn [ms_regs]; rewrite T8; pdc_ew EW8 | cbn [ms_regs]; rewrite T9; pdc_ew EW9
    | exact Erq
    | rewrite Hrest1, Hq34; reflexivity ].
Qed.

End pdcP.

(* ---- THE STRETCH AT A GENERIC INVARIANT P (the internal file GP-BRIEF.md): the old premises at psb_seg_*P P, the conclusion
   psb_dec_stepP P; srr_inv_laws only (no call) ---- *)
Theorem psb_dec_step_holdsP : forall CTX CW (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P ->
  psb_seg_uP B ARx SK CTX CW P -> psb_seg_freeP B ARx SK CTX CW P -> psb_seg_retokP B ARx SK CTX CW P ->
  psb_dec_stepP B ARx SK CTX CW P.
Proof. intros CTX CW P PLAW. exact (pdc_stepP P PLAW CTX CW). Qed.

(* ---- THE OLD STATEMENT, byte-identical, as the corollary at P := fun _ => True (PSB_Base's psb_*_of_True, PS_Gen's
   srr_inv_laws_True); its statement did not move ---- *)
Theorem psb_dec_step_holds : forall CTX CW,
  psb_seg_u B ARx SK CTX CW -> psb_seg_free B ARx SK CTX CW -> psb_seg_retok B ARx SK CTX CW ->
  psb_dec_step B ARx SK CTX CW.
Proof.
  intros CTX CW HU HF HR m Hlt.
  apply (proj1 (psb_dec_lt_of_True B ARx SK CTX CW (S m))).
  apply (psb_dec_step_holdsP CTX CW (fun _ => True) srr_inv_laws_True
    (proj2 (psb_seg_u_of_True B ARx SK CTX CW) HU) (proj2 (psb_seg_free_of_True B ARx SK CTX CW) HF)
    (proj2 (psb_seg_retok_of_True B ARx SK CTX CW) HR) m).
  exact (proj2 (psb_dec_lt_of_True B ARx SK CTX CW m) Hlt).
Qed.

End pdc.
