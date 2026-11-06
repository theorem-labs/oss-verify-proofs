(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its module paths, module names, addresses and numbers changed; 1014 of its 1163 lines of code are new or changed and 2537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread.v, with its module paths and module names changed; 1341 of its 1416 lines of code are new or changed and 1088 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread_top.v, with its addresses changed; 716 of its 798 lines of code are new or changed and 1334 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_check_no_overread_segf.v, with its module paths and module names changed; 1057 of its 1146 lines of code are new or changed and 709 lines of the source are left out. *)
(* check_no_overread 0x811c8 (fs.c), fs.asan: SEGMENT D of the walk, `cno_segD : cno_segD_T B`
   (FSW_check_no_overread_inv.v): from the machine INV_D1 at the first preset_base64_decode call (0x81398) to the
   machine INV_F1 at the first fuzz_free call (0x81420). Owner of this file: a Theorem Labs lane. Rule 24: this file
   proves PART of check_no_overread only (the walk's header carries the lookup).
   RANGE (MEASURED, capstone on the pinned fs.asan; every claim about a run is re-checked by the engine here):
   - 0x81398 / 0x813a8 / 0x813b8 preset_base64_decode (a, F + 0x20), (b, F + 0x40), (t, F + 0x60) (cno_call_dec, a
     Section hypothesis): the three texts are the same C string db, so b64_dec db is decided ONCE; the arms of the
     second and third call that disagree with the first are refuted by b64_dec;
   - 0x8139c-0x813a4 / 0x813ac-0x813b4: s6 := r1, a0 := b, a1 := s7; s8 := r2, a0 := t, a1 := s11;
   - 0x813bc-0x813d8 (s9 := r3): 0x813c8 `beq (r1 <> 0), (r3 = 0)` -> 0x81548 and 0x813d4 `beqz ((r2 <> 0) xor
     (r3 = 0))` -> 0x81548 are UNTAKEN (exfalso: the three results are all 0 or all non-zero); 0x813d8 `beqz s9` is
     taken on a bad text (-> 0x8141c, the frees) and untaken on success (exfalso);
   - 0x813dc-0x813e8 (success): n1 / n3 loaded from F + 0x20 / F + 0x60; 0x813e4 `bne n1, n3` -> 0x81548 UNTAKEN
     (exfalso, n1 = n3 = length out); 0x813e8 `beqz n1` has two live arms, split by the branch's own value: taken
     (out = []) into 0x81540 `ld a0, 0(s7)` (n2) and 0x81544 `beq n2, n1`, taken back to 0x8141c (its untaken arm ->
     0x81548 refuted by exfalso); untaken (out <> []) into the first bcmp;
   - 0x813f8 / 0x81414 bcmp (r1, r3, n1) / (r2, r3, n1) (cno_call_bcmp, a Section hypothesis; out <> []): 0x813fc /
     0x81418 `bnez a0` -> 0x81548 UNTAKEN by bcmp's value a0 = 0 (exfalso); 0x81400 n2 loaded, 0x81404 `bne n2, n1`
     -> 0x81548 UNTAKEN (exfalso);
   - 0x8141c a0 := r1, 0x81420 `jal fuzz_free`: the machine INV_F1 (bad text: k = 3 + 3 * 2, all results 0; success:
     k = 3 + 3, three reader blocks of dec_size db).
   Every in-function error arm is closed by exfalso at SRr_sym_branch from the machine's values, never by a halted
   leaf and never as an exit at a Report* call. The runs carry no memory region (or only read-only 8-byte regions
   for the length loads), so each run keeps the whole memory (segd_mem_eq); the bytes a call keeps come from its
   cno_ret clauses (zone, blocks) and cno_dec_strs.
   TEMPLATES (text only, never Required): the bespoke A-build lib/A/Prog/check_no_overread_mid_r2.v / mid_r3.v /
   mid_r4.v / mid_st.v on a working branch 1da71ab56d4; the length bound of a decode is the plain
   lib/Prog/SlotStepD.v dec_len (same WriterSpec.b64_dec), restated here (cno_dec_len) because that file imports the
   plain line's modules (lib/Contract, lib/Img0, Reusable YI14 ...), which this file must not load. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL07.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl FSW_check_no_overread
FSW_check_no_overread_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= pure facts ================= *)
(* a decoded text is shorter than dec_size (plain lib/Prog/SlotStepD.v six_len / dec_len, restated) *)
Lemma cno_six_len : forall six, Z.of_nat (length (WriterSpec.six_bytes six)) <= Z.of_nat (length six) / 4 * 3 + 2.
Proof.
  fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [WriterSpec.six_bytes length]; try (Z.div_mod_to_equations; lia).
  specialize (IH r). Z.div_mod_to_equations. lia.
Qed.
Lemma cno_dec_len : forall tb bs, WriterSpec.b64_dec tb = Some bs ->
  Z.of_nat (length bs) + 1 <= FSH_Fn_writer.dec_size tb.
Proof.
  intros tb bs H. unfold WriterSpec.b64_dec in H. unfold FSH_Fn_writer.dec_size.
  destruct (WriterSpec.b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && WriterSpec.six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (cno_six_len six). Z.div_mod_to_equations. lia.
Qed.
Lemma segd_split2 : forall {X : Type} (l1 l2 : list X) x y, In x l1 -> In y l2 ->
  exists u v w, l1 ++ l2 = u ++ x :: v ++ y :: w.
Proof.
  intros X l1 l2 x y H1 H2. apply in_split in H1 as (u & v & ->). apply in_split in H2 as (v' & w & ->).
  exists u, (v ++ v'), w. rewrite <- app_assoc. cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma segd_zb_prefix : forall (W : world tfibsegs) mem p (l1 l2 : list Z),
  zbytes_at tfibsegs W mem p (l1 ++ l2) -> zbytes_at tfibsegs W mem p l1.
Proof.
  intros W mem p l1 l2 H j Hj. pose proof (H j ltac:(rewrite length_app; lia)) as X.
  rewrite app_nth1 in X by lia. exact X.
Qed.


Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the call steps this segment chains (FSW_check_no_overread.v Section I); their lemmas are chained by the top file *)
Hypothesis cno_call_dec : cno_call_dec_T B.
Hypothesis cno_call_bcmp : cno_call_bcmp_T B.

(* ================= the engine's branch values ================= *)
Lemma segd_U_atom : forall E n x, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n 0) = x.
Proof. intros E n x H Hx. exact (U_atom E n x H Hx). Qed.
(* 0x813c8: beq (r1 <> 0), (r3 = 0) *)
Lemma segd_br_c1 : forall E i j x y, ew E i = w64 x -> ew E j = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff i 0))) (sv_denot E (SAlu ALU_SLTU (SOff j 0) (SLit 1)))
  = Bool.eqb (negb (x =? 0)) (y =? 0).
Proof.
  intros E i j x y Hi Hj Hx Hy. rewrite branch_eq_U, !U_SAlu, !U_SLit, (segd_U_atom E i x Hi Hx),
    (segd_U_atom E j y Hj Hy). cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Zmod_0_l, (Z.mod_small 1) by lia.
  destruct (Z.ltb_spec 0 x) as [Hx0 | Hx0]; destruct (Z.ltb_spec y 1) as [Hy1 | Hy1].
  all: first [ rewrite (proj2 (Z.eqb_neq x 0)) by lia | assert (x = 0) as -> by lia ].
  all: first [ rewrite (proj2 (Z.eqb_neq y 0)) by lia | assert (y = 0) as -> by lia ].
  all: vm_compute; reflexivity.
Qed.
(* 0x813d4: beqz ((r2 <> 0) xor (r3 = 0)) *)
Lemma segd_br_c2 : forall E i j x y, ew E i = w64 x -> ew E j = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff i 0)) (SAlu ALU_SLTU (SOff j 0) (SLit 1))))
    (sv_denot E (SLit 0))
  = Bool.eqb (negb (x =? 0)) (y =? 0).
Proof.
  intros E i j x y Hi Hj Hx Hy. rewrite branch_eq_U, !U_SAlu, !U_SLit, (segd_U_atom E i x Hi Hx),
    (segd_U_atom E j y Hj Hy). cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Zmod_0_l, (Z.mod_small 1) by lia.
  destruct (Z.ltb_spec 0 x) as [Hx0 | Hx0]; destruct (Z.ltb_spec y 1) as [Hy1 | Hy1].
  all: first [ rewrite (proj2 (Z.eqb_neq x 0)) by lia | assert (x = 0) as -> by lia ].
  all: first [ rewrite (proj2 (Z.eqb_neq y 0)) by lia | assert (y = 0) as -> by lia ].
  all: vm_compute; reflexivity.
Qed.
(* an atom against 0, an atom against an atom *)
Lemma segd_br_eq0 : forall E i x, ew E i = w64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff i 0)) (sv_denot E (SLit 0)) = (x =? 0).
Proof. intros E i x Hi Hx. rewrite branch_eq_U, U_SLit, (segd_U_atom E i x Hi Hx). reflexivity. Qed.
Lemma segd_br_ne0 : forall E i x, ew E i = w64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff i 0)) (sv_denot E (SLit 0)) = negb (x =? 0).
Proof. intros E i x Hi Hx. rewrite branch_ne_U, U_SLit, (segd_U_atom E i x Hi Hx). reflexivity. Qed.
Lemma segd_br_eq2 : forall E i j x y, ew E i = w64 x -> ew E j = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff i 0)) (sv_denot E (SOff j 0)) = (x =? y).
Proof. intros E i j x y Hi Hj Hx Hy. rewrite branch_eq_U, (segd_U_atom E i x Hi Hx), (segd_U_atom E j y Hj Hy). reflexivity. Qed.
Lemma segd_br_ne2 : forall E i j x y, ew E i = w64 x -> ew E j = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff i 0)) (sv_denot E (SOff j 0)) = negb (x =? y).
Proof. intros E i j x y Hi Hj Hx Hy. rewrite branch_ne_U, (segd_U_atom E i x Hi Hx), (segd_U_atom E j y Hj Hy). reflexivity. Qed.

(* ================= memory ================= *)
(* the runs' regions: read-only (no write window), each at an atom *)
Definition segd_ro (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) && match YP09.r_base r with Some _ => true | None => false end) rs.
(* a run whose regions have no write window keeps the whole memory *)
Lemma segd_mem_eq : forall E rs (m m' : word -> option byte), frame_of E rs m m' -> segd_ro rs = true -> m' = m.
Proof.
  intros E rs m m' HF Hw. apply functional_extensionality. intros x. apply HF. intros (r & Hr & Hx).
  pose proof (proj1 (forallb_forall _ _) Hw r Hr) as X. apply andb_prop in X as [X _]. apply Z.leb_le in X. lia.
Qed.
(* bytes a step keeps, as val_mem / range_addressable read them *)
Lemma segd_val_keep : forall (W W' : world tfibsegs) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W') m' (a + i) = aview tfibsegs (w_H W) m (a + i)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W') m') a n v.
Proof.
  intros W W' m m' a n v HK Hv k Hk. rewrite (YCbq.mbyte_of_aview tfibsegs (w_H W) (w_H W') m m'); [exact (Hv k Hk)|].
  apply HK. lia.
Qed.
Lemma segd_ra_keep : forall (W W' : world tfibsegs) m m' x n,
  (forall y, x <= y < x + n -> aview tfibsegs (w_H W') m' (shadow_of_addr SHADOW_OFF y) =
     aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF y)) ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF x n ->
  range_addressable (aview tfibsegs (w_H W') m') SHADOW_OFF x n.
Proof.
  intros W W' m m' x n HK H y Hy. destruct (H y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (HK y Hy). exact Hs.
Qed.
(* the bytes of a window inside a block live before and after a call, off the call's own writes Kp *)
Lemma segd_blk_keep : forall (W W' : world tfibsegs) m m' ly S ly' S' (Kp : Z -> Prop) p n a len,
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ Kp (p + i) -> aview tfibsegs (w_H W') m' (p + i) = aview tfibsegs (w_H W) m (p + i)) ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a -> a + len <= p + n -> n <= req_size n ->
  (forall i, 0 <= i < len -> ~ Kp (a + i)) ->
  forall i, 0 <= i < len -> aview tfibsegs (w_H W') m' (a + i) = aview tfibsegs (w_H W) m (a + i).
Proof.
  intros W W' m m' ly S ly' S' Kp p n a len HBK H1 H2 Ha Hl Hr HK i Hi.
  replace (a + i) with (p + (a + i - p)) by lia. apply (HBK p n (a + i - p) H1 H2); [lia|].
  replace (p + (a + i - p)) with (a + i) by lia. exact (HK i Hi).
Qed.

(* ================= the decoders' texts at the first call ================= *)
(* a C string at the start of a live block: its bytes and NUL in the block, no byte of it on a range of U (U's ranges
   are 16-byte heads, fs_heads); the shadow, hull and tail word by the block's AR facts at the unpoisoned reading,
   moved to the machine's memory by FSW_strkit.cstr_ok_unpoison (no shadow byte of the string is U's) *)
Lemma segd_cstr_blk : forall ly S U (W : world tfibsegs) mem md p m l,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (p, m) (ablocks B ly S) ->
  zbytes_at tfibsegs W mem p (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  Z.of_nat (length l) + 9 <= m -> Z.of_nat (length l) < 2 ^ 32 ->
  (forall r, In r U -> p + Z.of_nat (length l) + 1 <= fst r \/ fst r + snd r <= p) ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p m l H Hh Hin Hz Hnz Hm H32 HU.
pose proof H as (HAR & OK & PO).
destruct (fsw_ablock_low B ly S W (unpoison U mem) md p m HAR Hin) as (L1 & L2 & L3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (cstr_ok_unpoison B ly S U W mem md p l H).
{ intros x Hx. change (shadow_addr x) with (shadow_of_addr SHADOW_OFF x). apply fsw_head_ush_out; [lia|].
  intros r Hr. destruct (Hh r Hr) as (E16 & _). destruct (upoison_ok_In B ly S U r OK Hr) as (A8 & _).
  split; [exact E16|]. split; [exact A8|]. destruct (HU r Hr); lia. }
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hz). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (YCbq.mbyte_of_aview tfibsegs). replace a with (p + (a - p)) by lia.
  apply (cno_blk_unp B ly S U W mem md p m (a - p) H Hin). lia. }
split; [lia|]. split; [lia|]. split; [(destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 H) Hin) as (_ & _ & _ & _ & _ & _ & HmxL); unfold MALLOC_MAX in HmxL; lia)|].
split.
{ unfold amem_range. destruct (Z_lt_le_dec p SHADOW_OFF) as [Hlo | Hhi].
  - left. destruct (Z_lt_le_dec (p + req_size m) (SHADOW_OFF + 1)) as [Hq | Hq].
    + unfold SHADOW_OFF in Hq. rewrite C5. lia.
    + exfalso. apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p m HAR Hin SHADOW_OFF); [lia|].
      unfold SHADOW_OFF. lia.
  - right. assert (Hh2 : SHADOW_OFF + 2 ^ 44 <= p).
    { destruct (Z_lt_le_dec p (SHADOW_OFF + 2 ^ 44)) as [X | X]; [|exact X]. exfalso.
      apply (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p m HAR Hin p); lia. }
    unfold SHADOW_OFF in Hh2. rewrite C3, C4. lia. }
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md p m p _ HAR Hin); lia. }
split.
{ destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md p m HAR Hin) as (_ & Hhv').
  apply (shadow_hull_vis_sub _ p (req_size m) p _ Hhv'); lia. }
intros a Ha. apply (block_word_tail_vis B ly S W (unpoison U mem) md p m HAR Hin ltac:(lia)).
pose proof (word_end_mono (p + Z.of_nat (length l)) (p + m - 1) ltac:(lia)). lia.
Qed.

(* a block appended to the entry's blocks misses every range of the entry's U (each the head of an entry block,
   fs_heads at the entry; distinct blocks are disjoint, YCbq.sep_blocks_pos) *)
Lemma segd_U_new : forall cx ly S W mem md p n (l : list (Z * Z)),
  AR tfibsegs B ly S W mem md -> FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ l -> In (p, n) l ->
  forall r, In r (c_U cx) -> p + req_size n <= fst r \/ fst r + snd r <= p.
Proof.
intros cx ly S W mem md p n l HAR Hh El Hpl r Hr.
destruct (Hh r Hr) as (E16 & m & Hin & Hm16).
destruct (segd_split2 _ _ _ _ Hin Hpl) as (u & v & w & Euvw).
pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (fst r, m) (p, n) u v w HAR (eq_trans El Euvw)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite E16. lia.
Qed.

(* ================= the boundary frame ================= *)
Lemma segd_frame : forall cx k ly S U (W : world tfibsegs) regs mem md A,
  cno_mframe B cx k ly S U W regs mem md A ->
  In (1, c_fpos cx) (frames S) /\ ly_F ly = ly_F (c_ly cx) /\
  4096 <= cno_F cx /\ cno_F cx + 128 <= alloc_ceiling /\ in_app (cno_F cx) 128 /\ cno_F cx mod 32 = 0.
Proof.
intros cx k ly S U W regs mem md A Hm. pose proof Hm as (HJ & HARU & _).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : ly_F ly = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & X & _); exact X).
assert (EFa : frame_addr ly 1 (c_fpos cx) = cno_F cx) by (unfold cno_F, frame_addr; rewrite EF; reflexivity).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H1 & H2 & H3).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (Hal32 & _).
change (fs_frame_bytes 1) with 128 in H1, H2, H3, Hal32. rewrite EFa in H1, H2, H3, Hal32.
split; [exact Hin|]. split; [exact EF|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact Hal32].
Qed.

(* the boundary frame at the next call: the journal, ARU and heads there, the kept registers, and the saved words,
   the flag word and the two slots read the same (cno_ret's zone clause; the call's own writes Kp miss them) *)
Lemma segd_mframe : forall cx k ly S U (W : world tfibsegs) regs mem md A k' ly' S' U' (W' : world tfibsegs) regs'
  mem' md' (Kp : Z -> Prop),
  cno_mframe B cx k ly S U W regs mem md A ->
  cno_J B cx k' ly' S' W' (unpoison U' mem') md' -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  FSupoisonU.fs_heads B ly' S' U' ->
  (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, cno_sp0 cx - 104 <= a < cno_sp0 cx -> ~ Kp a) ->
  (forall i, 0 <= i < 8 -> ~ Kp (cno_F cx + 120 + i)) ->
  (forall i, 0 <= i < 16 -> ~ Kp (cno_sp1 cx + 16 + i)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 3 = getr regs 3 ->
  getr regs' 4 = getr regs 4 ->
  cno_mframe B cx k' ly' S' U' W' regs' mem' md' A.
Proof.
intros cx k ly S U W regs mem md A k' ly' S' U' W' regs' mem' md' Kp Hm HJ HARU Hh HZ HKs HKf HKl
  E2 E8 E9 E18 E19 E3 E4.
destruct Hm as (_ & _ & _ & R2 & R8 & R9 & R18 & R19 & R3 & R4 & Hsv & HFL & HS16 & HS24).
split; [exact HJ|]. split; [exact HARU|]. split; [exact Hh|].
split; [rewrite E2; exact R2|]. split; [rewrite E8; exact R8|]. split; [rewrite E9; exact R9|].
split; [rewrite E18; exact R18|]. split; [rewrite E19; exact R19|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split.
{ intros j Hj. apply (segd_val_keep W W' mem mem' _ 8 _); [|exact (Hsv j Hj)].
  intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. apply HZ; [unfold cno_zone; left; lia|]. apply HKs. lia. }
split.
{ apply (segd_val_keep W W' mem mem' _ 8 _); [|exact HFL].
  intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. apply HZ; [unfold cno_zone; right; right; left; lia|].
  exact (HKf i Hi). }
split.
{ apply (segd_val_keep W W' mem mem' _ 8 _); [|exact HS16].
  intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. apply HZ; [unfold cno_zone; right; left; lia|].
  exact (HKl i ltac:(lia)). }
apply (segd_val_keep W W' mem mem' _ 8 _); [|exact HS24].
intros i Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. apply HZ; [unfold cno_zone; right; left; lia|].
replace (cno_sp1 cx + 24 + i) with (cno_sp1 cx + 16 + (8 + i)) by lia. exact (HKl (8 + i) ltac:(lia)).
Qed.

(* ================= the machine boundaries inside the segment ================= *)
(* the second decode call (0x813a8; a0 = b, a1 = F + 0x40, ra = 0x813ac), after the first decode, one arm each *)
Definition INV_D2 : cno_minv := fun cx k ly S U W regs mem md => exists a b t peak',
  cno_mframe B cx k ly S U W regs mem md a /\
  getr regs 1 = w64 0x813ac /\ getr regs 10 = w64 b /\ getr regs 11 = w64 (cno_F cx + 64) /\
  getr regs 20 = w64 b /\ getr regs 21 = w64 t /\ getr regs 23 = w64 (cno_F cx + 64) /\
  getr regs 26 = w64 (cno_F cx + 32) /\ getr regs 27 = w64 (cno_F cx + 96) /\
  cstr_ok tfibsegs W mem b (c_db cx) /\ cstr_ok tfibsegs W mem t (c_db cx) /\
  (forall r, In r U -> b + cno_n cx + 1 <= fst r \/ fst r + snd r <= b) /\
  (forall r, In r U -> t + cno_n cx + 1 <= fst r \/ fst r + snd r <= t) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 64) 8 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 96) 8 0 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 64) 8 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 96) 8 /\
  c_peak cx <= peak' /\
  ((WriterSpec.b64_dec (c_db cx) = None /\ U = c_U cx /\ k = 3 + EV_preset_base64_decode /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\ getr regs 22 = w64 0 /\
    fs_glob tfibsegs W mem (c_live cx) peak' (c_cnt cx + 1) (c_fail cx))
   \/
   (exists out q1, WriterSpec.b64_dec (c_db cx) = Some out /\ U = c_U cx ++ [(q1 - HEAD, HEAD)] /\ k = 3 + 1 /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++
      [(q1 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD)] /\
    4096 + HEAD <= q1 /\ getr regs 22 = w64 q1 /\
    fs_rblock tfibsegs B ly S W mem q1 (FSH_Fn_writer.dec_size (c_db cx)) /\ zbytes_at tfibsegs W mem q1 out /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 32) 8 (Z.of_nat (length out)) /\
    fs_glob tfibsegs W mem (c_live cx + FSH_Fn_writer.dec_size (c_db cx)) peak' (c_cnt cx + 1) (c_fail cx))).

(* the third decode call (0x813b8; a0 = t, a1 = F + 0x60, ra = 0x813bc), after two decodes of the same text *)
Definition INV_D3 : cno_minv := fun cx k ly S U W regs mem md => exists a b t peak',
  cno_mframe B cx k ly S U W regs mem md a /\
  getr regs 1 = w64 0x813bc /\ getr regs 10 = w64 t /\ getr regs 11 = w64 (cno_F cx + 96) /\
  getr regs 20 = w64 b /\ getr regs 21 = w64 t /\ getr regs 23 = w64 (cno_F cx + 64) /\
  getr regs 26 = w64 (cno_F cx + 32) /\ getr regs 27 = w64 (cno_F cx + 96) /\
  cstr_ok tfibsegs W mem t (c_db cx) /\
  (forall r, In r U -> t + cno_n cx + 1 <= fst r \/ fst r + snd r <= t) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 96) 8 0 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (cno_F cx + 96) 8 /\
  c_peak cx <= peak' /\
  ((WriterSpec.b64_dec (c_db cx) = None /\ U = c_U cx /\ k = 3 + 2 * EV_preset_base64_decode /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t /\ getr regs 22 = w64 0 /\
    getr regs 24 = w64 0 /\ fs_glob tfibsegs W mem (c_live cx) peak' (c_cnt cx + 2) (c_fail cx))
   \/
   (exists out q1 q2, WriterSpec.b64_dec (c_db cx) = Some out /\
    U = c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD)] /\ k = 3 + 2 /\
    ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++
      [(q1 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD); (q2 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD)] /\
    4096 + HEAD <= q1 /\ 4096 + HEAD <= q2 /\ getr regs 22 = w64 q1 /\ getr regs 24 = w64 q2 /\
    fs_rblock tfibsegs B ly S W mem q1 (FSH_Fn_writer.dec_size (c_db cx)) /\
    fs_rblock tfibsegs B ly S W mem q2 (FSH_Fn_writer.dec_size (c_db cx)) /\
    zbytes_at tfibsegs W mem q1 out /\ zbytes_at tfibsegs W mem q2 out /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 32) 8 (Z.of_nat (length out)) /\
    val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 64) 8 (Z.of_nat (length out)) /\
    fs_glob tfibsegs W mem (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx)) peak' (c_cnt cx + 2) (c_fail cx))).

(* what the two bcmp calls share: three reader blocks holding the same non-empty out *)
Definition segd_ok3 (cx : cnocx) (k : Z) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (a b t peak' : Z) (out : list Z) (q1 q2 q3 : Z) : Prop :=
  getr regs 20 = w64 b /\ getr regs 21 = w64 t /\ getr regs 22 = w64 q1 /\ getr regs 23 = w64 (cno_F cx + 64) /\
  getr regs 24 = w64 q2 /\ getr regs 25 = w64 q3 /\ getr regs 26 = w64 (Z.of_nat (length out)) /\
  c_peak cx <= peak' /\ WriterSpec.b64_dec (c_db cx) = Some out /\ out <> [] /\
  U = c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD); (q3 - HEAD, HEAD)] /\ k = 3 + 3 /\
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++
    [(q1 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD); (q2 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD);
     (q3 - HEAD, FSH_Fn_writer.dec_size (c_db cx) + HEAD)] /\
  4096 + HEAD <= q1 /\ 4096 + HEAD <= q2 /\ 4096 + HEAD <= q3 /\
  fs_rblock tfibsegs B ly S W mem q1 (FSH_Fn_writer.dec_size (c_db cx)) /\
  fs_rblock tfibsegs B ly S W mem q2 (FSH_Fn_writer.dec_size (c_db cx)) /\
  fs_rblock tfibsegs B ly S W mem q3 (FSH_Fn_writer.dec_size (c_db cx)) /\
  zbytes_at tfibsegs W mem q1 out /\ zbytes_at tfibsegs W mem q2 out /\ zbytes_at tfibsegs W mem q3 out /\
  fs_glob tfibsegs W mem (c_live cx + 3 * FSH_Fn_writer.dec_size (c_db cx)) peak' (c_cnt cx + 3) (c_fail cx).
(* the first bcmp call (0x813f8; a0 = r1, a1 = r3, a2 = n1, ra = 0x813fc); n2 still at F + 0x40 *)
Definition INV_B1 : cno_minv := fun cx k ly S U W regs mem md => exists a b t peak' out q1 q2 q3,
  cno_mframe B cx k ly S U W regs mem md a /\ segd_ok3 cx k ly S U W regs mem a b t peak' out q1 q2 q3 /\
  getr regs 1 = w64 0x813fc /\ getr regs 10 = w64 q1 /\ getr regs 11 = w64 q3 /\
  getr regs 12 = w64 (Z.of_nat (length out)) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (cno_F cx + 64) 8 (Z.of_nat (length out)).
(* the second bcmp call (0x81414; a0 = r2, a1 = r3, a2 = n1, ra = 0x81418) *)
Definition INV_B2 : cno_minv := fun cx k ly S U W regs mem md => exists a b t peak' out q1 q2 q3,
  cno_mframe B cx k ly S U W regs mem md a /\ segd_ok3 cx k ly S U W regs mem a b t peak' out q1 q2 q3 /\
  getr regs 1 = w64 0x81418 /\ getr regs 10 = w64 q2 /\ getr regs 11 = w64 q3 /\
  getr regs 12 = w64 (Z.of_nat (length out)).

(* ================= reading a run's end ================= *)
(* a register the run left as an atom of the resume env Ereg regs' xs *)
Lemma segd_rd : forall (H : word -> bool) regs' xs ss rg pc m rom (r r' : bv 5) n v,
  st_ok tfibsegs (Ereg regs' xs) ss (restrict H (mkst rg pc m rom)) -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r' -> getr regs' r' = v -> getr rg r = v.
Proof.
intros H regs' xs ss rg pc m rom r r' n v HS Hr Hn Hv.
pose proof (cno_reg H _ ss (mkst rg pc m rom) r n HS Hr) as X. cbn [ms_regs mkst] in X.
rewrite X, (ew_Ereg_nat regs' xs n r' Hn). exact Hv.
Qed.
(* a run from a state of read-only regions (FSW_K.fsw_run_to_AJU): the memory stays, the machine at the run's end is
   the configuration at the engine's last pc *)
Lemma segd_run : forall (W : world tfibsegs) n stop E ss ss' st pc' regs pc mem rom STK sp0 FP ly S W0 mem0 md0 own
  lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) (mkst regs pc mem rom)) ->
  sym_run_toN tfibsegs cno_tbl n stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
  segd_ro (ss_mem ss) = true -> ss_resv ss' = None -> ss_pc ss' = pc' ->
  ARU tfibsegs B lyc Sc U W mem mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U mem) mdc k ->
  (forall regs' mat',
     st_ok tfibsegs E ss' (restrict (w_H W) (mkst regs' (Z_to_bv 64 pc') mem (seg_rom tfibsegs))) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison U mem)
       (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
     ARU tfibsegs B lyc Sc U W mem (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
     SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 pc') mem (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdc) mat' mdc))
       Q) ->
  SRr tfibsegs W (mkCfg (mkst regs pc mem rom) mdc) Q.
Proof.
intros W n stop E ss ss' st pc' regs pc mem rom STK sp0 FP ly S W0 mem0 md0 own lyc Sc U mdc k Q
  HS Hrun Hst Hw Hrv Hpc HARU HJ HK.
eapply (fsw_run_to_AJU B cno_tbl cno_tbl_ok W n stop E ss ss' st (mkst regs pc mem rom) STK sp0 FP ly S W0 mem0 md0
  own lyc Sc U mdc k Q HS Hrun Hst HARU HJ).
- clear - Hw. generalize (ss_mem ss) Hw. clear Hw. intros rs. induction rs as [|r rs IH]; intros Hw; [apply awr_ok_nil|].
  cbn [segd_ro forallb] in Hw. apply andb_prop in Hw as [H1 H2]. apply andb_prop in H1 as [Hwin Hbase].
  destruct (YP09.r_base r) as [kk|] eqn:Eb; [|discriminate].
  apply (awr_ok_cons_gen tfibsegs B E r rs _ _ _ _ _ _ _ _ kk (bv_unsigned (ew E kk)) Eb eq_refl);
    [intros a Ha; apply Z.leb_le in Hwin; lia | exact (IH H2)].
- intros ms' mat' HS' HJ' HARU' HF _ _.
  pose proof (segd_mem_eq E _ _ _ HF Hw) as Em. cbn [ms_mem mkst] in Em.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss' ms' HS' Hrv) as Ems. rewrite Em, Hpc in Ems.
  rewrite Em in HJ', HARU'. rewrite Ems in HS' |- *. exact (HK (ms_regs ms') mat' HS' HJ' HARU').
Qed.
(* the run tactic over segd_run: HS / HJ / HARU come back under the same names, rg / mt name the machine's registers
   and the model's backing at the run's end *)
Ltac segd_run HS HJ HARU stop rg mt :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) (mkst ?regs ?pc ?mem ?rom)) =>
    let r := eval vm_compute in (sym_run_toN segs cno_tbl FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let pc' := eval vm_compute in (ss_pc ss') in
      refine (segd_run W FUEL stop E ss ss' st pc' regs pc mem rom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS
        ltac:(vm_compute; reflexivity) I ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) HARU HJ _);
      clear HS HJ HARU; intros rg mt HS HJ HARU
    end
  end.
(* the bytes below alloc_ceiling are off bcmp's runtime stack *)
Lemma segd_bcmp_low : forall cx (W W' : world tfibsegs) m m',
  cno_base B cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cno_sp1 cx - STK_RT_BCMP <= a < cno_sp1 cx) ->
     aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a.
Proof.
intros cx W W' m m' Hb HK a Ha. pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & _).
pose proof cno_stk as FS. pose proof asan_consts as (C1 & _). unfold STK_RT_BCMP, ESTACK in HK.
apply HK; lia.
Qed.
(* a reader block kept by a step that keeps its head and the block *)
Lemma segd_rblock_keep : forall ly S ly' S' (W W' : world tfibsegs) m m' q n,
  fs_rblock tfibsegs B ly S W m q n -> In (q - HEAD, n + HEAD) (ablocks B ly' S') ->
  (forall i, 0 <= i < 8 -> aview tfibsegs (w_H W') m' (q - HEAD + i) = aview tfibsegs (w_H W) m (q - HEAD + i)) ->
  fs_rblock tfibsegs B ly' S' W' m' q n.
Proof.
intros ly S ly' S' W W' m m' q n (Hin & H16 & Hn & Hv) Hin' HK.
split; [exact Hin'|]. split; [exact H16|]. split; [exact Hn|].
exact (segd_val_keep W W' m m' (q - HEAD) 8 n HK Hv).
Qed.

(* a read-only 8-byte region at the atom n holding the atom k (the decoders' lengths, loaded at 0x813dc / 0x813e0 /
   0x81400 / 0x81540) *)
Definition segd_rg (n k : nat) : YP09.region := YP09.mkRegion (Some n) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff k 0))].
Lemma segd_rg_ok : forall E (m : word -> option byte) (n k : nat) x v,
  bv_unsigned (ew E n) = x -> ew E k = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= x -> x + 8 <= 2 ^ 64 ->
  val_mem tfibsegs m x 8 v -> region_ok tfibsegs E m (segd_rg n k).
Proof.
intros E m n k x v Hn Hk Hv Hx Hx8 Hm. unfold region_ok, segd_rg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros; lia|]. constructor; [|constructor].
apply (chunk_ok_val tfibsegs E m x 0 8 (SOff k 0) v); [rewrite fsw_SOff0; exact Hk | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Hm.
Qed.
(* the extra atoms 51 .. of the resume env *)
Lemma segd_x51 : forall cx regs' A Bp T (v1 : word) l, ew (Ereg regs' (cno_xs cx A Bp T (v1 :: l))) 51 = v1.
Proof. intros. change 51%nat with (32 + 19)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma segd_x52 : forall cx regs' A Bp T (v1 v2 : word) l, ew (Ereg regs' (cno_xs cx A Bp T (v1 :: v2 :: l))) 52 = v2.
Proof. intros. change 52%nat with (32 + 20)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma segd_x53 : forall cx regs' A Bp T (v1 v2 v3 : word) l,
  ew (Ereg regs' (cno_xs cx A Bp T (v1 :: v2 :: v3 :: l))) 53 = v3.
Proof. intros. change 53%nat with (32 + 21)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

(* ================= what a decode call keeps ================= *)
(* a frame word off the call's own writes: cno_ret's zone clause *)
Lemma segd_zone_val : forall cx (W W' : world tfibsegs) m m' (Kp : Z -> Prop) x v,
  (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  cno_F cx <= x -> x + 8 <= cno_F cx + 128 -> (forall i, 0 <= i < 8 -> ~ Kp (x + i)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) x 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') x 8 v.
Proof.
intros cx W W' m m' Kp x v HZ H1 H2 HK Hv. apply (segd_val_keep W W' m m' x 8 v); [|exact Hv].
intros i Hi. cbn in Hi. apply HZ; [unfold cno_zone; right; right; left; lia | exact (HK i Hi)].
Qed.
(* a frame local's granule: its shadow byte is in the frame's shadow, off the call's own (application) writes *)
Lemma segd_zone_ra : forall cx (W W' : world tfibsegs) m m' (Kp : Z -> Prop) x,
  (forall a, cno_zone cx a -> ~ Kp a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  4096 <= cno_F cx -> cno_F cx mod 32 = 0 -> cno_F cx <= x -> x + 8 <= cno_F cx + 128 ->
  (forall y, cno_SF cx <= y < cno_SF cx + 16 -> ~ Kp y) ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF x 8 -> range_addressable (aview tfibsegs (w_H W') m') SHADOW_OFF x 8.
Proof.
intros cx W W' m m' Kp x HZ H4 H32 H1 H2 HK Hra. apply (segd_ra_keep W W' m m' x 8); [|exact Hra].
intros y Hy. assert (Hs : cno_SF cx <= shadow_of_addr SHADOW_OFF y < cno_SF cx + 16).
{ unfold cno_SF, shadow_addr, shadow_of_addr. Z.div_mod_to_equations. lia. }
apply HZ; [unfold cno_zone; right; right; right; exact Hs | exact (HK _ Hs)].
Qed.
(* a reader block and its bytes across a decode call that keeps the block (lenp in the frame) *)
Lemma segd_keep_dec : forall cx ly S U (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' lenp q n
  (l : list Z),
  cno_base B cx -> ARU tfibsegs B ly S U W mem md -> In (1, c_fpos cx) (frames S) -> ly_F ly = ly_F (c_ly cx) ->
  cno_F cx <= lenp -> lenp + 8 <= cno_F cx + 128 ->
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ (lenp <= p + i < lenp + 8) -> aview tfibsegs (w_H W') mem' (p + i) = aview tfibsegs (w_H W) mem (p + i)) ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  fs_rblock tfibsegs B ly S W mem q n -> Z.of_nat (length l) <= n -> zbytes_at tfibsegs W mem q l ->
  fs_rblock tfibsegs B ly' S' W' mem' q n /\ zbytes_at tfibsegs W' mem' q l.
Proof.
intros cx ly S U W mem md ly' S' W' mem' lenp q n l Hb HARU Hin EF H1 H2 HBK Hsub Hq Hl Hz.
pose proof Hq as (Hqin & H16 & Hn & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (fsw_ablock_low B ly S W _ md _ _ HAR Hqin) as (L1 & L2 & L3).
assert (HK : forall i, 0 <= i < req_size (n + HEAD) -> ~ (lenp <= q - HEAD + i < lenp + 8)).
{ intros i Hi X. apply (cno_zone_blk B cx ly S U W mem md (q - HEAD) (n + HEAD) i Hb HARU Hin EF Hqin Hi).
  unfold cno_zone. right; right; left. lia. }
split.
- apply (segd_rblock_keep ly S ly' S' W W' mem mem' q n Hq (Hsub _ Hqin)).
  intros i Hi. apply (segd_blk_keep W W' mem mem' ly S ly' S' (fun a => lenp <= a < lenp + 8) (q - HEAD) (n + HEAD)
    (q - HEAD) 8 HBK Hqin (Hsub _ Hqin) ltac:(lia) ltac:(unfold HEAD; lia) L3); [|exact Hi].
  intros i' Hi'. apply HK. unfold HEAD in *. lia.
- apply (cno_zbytes_kept W W' mem mem' q l); [|exact Hz]. intros j Hj.
  replace (q + j) with (q - HEAD + (HEAD + j)) by lia.
  apply (HBK (q - HEAD) (n + HEAD) (HEAD + j) Hqin (Hsub _ Hqin)); [unfold HEAD in *; lia|].
  apply HK. unfold HEAD in *. lia.
Qed.

(* the text's block at a decode call: the text starts its block *)
Lemma segd_blk1 : forall ly S (U : list (Z * Z)) p n0, In (p, n0 + 18) (ablocks B ly S) -> 0 <= n0 ->
  (forall r, In r U -> p + n0 + 1 <= fst r \/ fst r + snd r <= p) ->
  exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + n0 + 1 <= b + m /\
    (forall r, In r U -> p + n0 + 1 <= fst r \/ fst r + snd r <= p).
Proof. intros ly S U p n0 Hin H0 HU. exists p, (n0 + 18). split; [exact Hin|]. split; [lia|]. split; [lia | exact HU]. Qed.

(* ================= the budgets of a decode call ================= *)
Lemma segd_ds_pos : forall db, 3 <= FSH_Fn_writer.dec_size db.
Proof. intros db. unfold FSH_Fn_writer.dec_size. pose proof (Z.div_pos (Z.of_nat (length db)) 4 ltac:(lia) ltac:(lia)). lia. Qed.
(* the blocks' bytes: the walk's raw blocks and at most three decoder blocks fit in LIVE_check_no_overread *)
Lemma segd_bb : forall cx ly S (l : list (Z * Z)), cno_base B cx ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ l ->
  bsum l + (FSH_Fn_writer.dec_size (c_db cx) + HEAD) <=
    3 * (cno_n cx + 18) + 3 * (FSH_Fn_writer.dec_size (c_db cx) + HEAD) ->
  blocks_bytes S + (FSH_Fn_writer.dec_size (c_db cx) + HEAD) <= LIVE_MAX.
Proof.
intros cx ly S l Hb El Hl. pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & _ & _ & _ & Hbb).
rewrite (blocks_bytes_bsum B ly S), El, cno_bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
unfold LIVE_check_no_overread, PRESET_FILE_MAX_BYTES, FSH_Fn_writer.dec_size, cno_n, HEAD, LIVE_MAX in *. lia.
Qed.

(* a callee-saved register the run did not touch, at the run's end, is the call site's *)
Ltac segd_keep HS HP :=
  lazymatch goal with |- getr ?rg ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (segd_rd _ _ _ _ rg _ _ _ r r n _ HS ltac:(vm_compute; reflexivity) eq_refl);
    rewrite (fsw_pres _ _ r HP ltac:(cno_cs)); try reflexivity
  end.

(* ================= the second bcmp (0x81414) to the first fuzz_free (0x81420) ================= *)
Lemma segd_B2 : cno_at B A_fuzz_free (INV_F1 B) -> cno_at B PC_bcmp INV_B2.
Proof.
intros HNX cx k ly S U W regs mem md Hb HI.
destruct HI as (a & b & t & peak' & out & q1 & q2 & q3 & Hm & Hok & R1 & R10 & R11 & R12).
pose proof Hok as (R20 & R21 & R22 & R23 & R24 & R25 & R26 & Hpk & Hdec & Hne & -> & -> & Hab & Q1 & Q2 & Q3 &
  B1 & B2 & B3 & Z1 & Z2 & Z3 & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof Hm as (HJ0 & HARU0 & Hh0 & _).
pose proof (ARU_AR tfibsegs B ly S _ W mem md HARU0) as HAR.
assert (Ha : 0 <= a < 2 ^ 64).
{ assert (Hi : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W _ md a _ HAR Hi) as (L1 & L2 & L3). unfold cno_n in *. lia. }
pose proof (cno_dec_len _ _ Hdec) as Hlen.
assert (Hn0 : 0 < Z.of_nat (length out)) by (destruct out; [congruence | cbn [length]; lia]).
assert (Hsite : cno_site B cx (3 + 3) ly S _ W regs mem md)
  by exact (cno_site_of_mframe B cx _ ly S _ W regs mem md a 0x81418 Hm R1 ltac:(lia) ltac:(reflexivity)).
eapply SRr_bind.
{ exact (cno_call_bcmp cx _ ly S _ W regs mem md q2 q3 (Z.of_nat (length out)) _ _ out Hb Hsite (or_intror R1)
    R10 R11 R12 eq_refl Hn0 B2 B3 ltac:(lia) ltac:(lia) Z2 Z3). }
intros W' c' _ Hret.
destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] 0 _ (fun _ => False) _ W' c' Hb Hm Hsite Ha Hret
  ltac:(intros; tauto) ltac:(intros; tauto) ltac:(intros; tauto))
  as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
destruct HPP as (-> & -> & -> & P10 & Pkeep).
assert (Era : raZ regs = 0x81418) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
rewrite Era in Ec, HS'. subst c'.
pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
assert (X10 : ew E' 10 = w64 0) by (subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10).
(* 0x81418 bnez a0 *)
segd_run HS HJ HARU A_fuzz_free rg1 mt1.
refine (SRr_sym_branch tfibsegs W E' _ _ _ _ BC_NE (SOff 10 0) (SLit 0) HS _ _).
{ intros Hc _. exfalso. rewrite (segd_br_ne0 E' 10 0 X10 ltac:(lia)) in Hc. discriminate Hc. }
intros _ HS2. clear HS. rename HS2 into HS.
(* 0x8141c a0 := r1, 0x81420 jal fuzz_free *)
segd_run HS HJ HARU A_fuzz_free rg mt.
apply (HNX cx (3 + 3 + 0) ly S (c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD); (q3 - HEAD, HEAD)]) W rg mem' _ Hb).
exists a, b, t, peak'.
split.
{ apply (segd_mframe cx _ ly S _ W regs mem md a _ ly S _ W rg mem' _ (fun _ => False) Hm HJ HARU Hh' HZ).
  all: first [ solve [intros; tauto] | solve [segd_keep HS HP] ]. }
split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x81424 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|].
split; [exact Hpk|].
right. exists out, q1, q2, q3.
split; [exact Hdec|]. split; [reflexivity|]. split; [lia|]. split; [exact Hab|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
split.
{ apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 22%bv 22 _ HS ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (fsw_pres _ _ 22%bv HP ltac:(cno_cs)). exact R22. }
split; [segd_keep HS HP; exact R22|]. split; [segd_keep HS HP; exact R24|]. split; [segd_keep HS HP; exact R25|].
assert (KB : forall q, fs_rblock tfibsegs B ly S W mem q (FSH_Fn_writer.dec_size (c_db cx)) ->
  fs_rblock tfibsegs B ly S W mem' q (FSH_Fn_writer.dec_size (c_db cx))).
{ intros q Hq. apply (segd_rblock_keep ly S ly S W W mem mem' q _ Hq (proj1 Hq)). intros i Hi.
  destruct (fsw_rblock_low B ly S W _ md mem q _ HAR Hq) as (L1 & L2).
  apply (segd_bcmp_low cx W W mem mem' Hb Pkeep). unfold HEAD in *. lia. }
split; [exact (KB q1 B1)|]. split; [exact (KB q2 B2)|]. split; [exact (KB q3 B3)|].
apply (cno_glob_ledger W W mem mem' _ _ _ _); [|exact Hg].
intros x Hx. pose proof (cno_pstat_bounds x Hx). apply (segd_bcmp_low cx W W mem mem' Hb Pkeep). lia.
Qed.

(* ================= the first bcmp (0x813f8) to the second (0x81414) ================= *)
Lemma segd_B1 : cno_at B PC_bcmp INV_B2 -> cno_at B PC_bcmp INV_B1.
Proof.
intros HNX cx k ly S U W regs mem md Hb HI.
destruct HI as (a & b & t & peak' & out & q1 & q2 & q3 & Hm & Hok & R1 & R10 & R11 & R12 & V64).
pose proof Hok as (R20 & R21 & R22 & R23 & R24 & R25 & R26 & Hpk & Hdec & Hne & -> & -> & Hab & Q1 & Q2 & Q3 &
  B1 & B2 & B3 & Z1 & Z2 & Z3 & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
destruct (segd_frame cx _ ly S _ W regs mem md a Hm) as (Hin & EF & HF4096 & HFceil & HFapp & HF32).
pose proof Hm as (HJ0 & HARU0 & Hh0 & _).
pose proof (ARU_AR tfibsegs B ly S _ W mem md HARU0) as HAR.
assert (Ha : 0 <= a < 2 ^ 64).
{ assert (Hi : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W _ md a _ HAR Hi) as (L1 & L2 & L3). unfold cno_n in *. lia. }
pose proof (cno_dec_len _ _ Hdec) as Hlen.
set (n := Z.of_nat (length out)) in *.
assert (Hn0 : 0 < n) by (subst n; destruct out; [congruence | cbn [length]; lia]).
assert (Hsite : cno_site B cx (3 + 3) ly S _ W regs mem md)
  by exact (cno_site_of_mframe B cx _ ly S _ W regs mem md a 0x813fc Hm R1 ltac:(lia) ltac:(reflexivity)).
eapply SRr_bind.
{ exact (cno_call_bcmp cx _ ly S _ W regs mem md q1 q3 n _ _ out Hb Hsite (or_introl R1)
    R10 R11 R12 eq_refl Hn0 B1 B3 ltac:(lia) ltac:(lia) Z1 Z3). }
intros W' c' _ Hret.
destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [w64 n] 0 _ (fun _ => False) _ W' c' Hb Hm Hsite Ha Hret
  ltac:(intros; tauto) ltac:(intros; tauto) ltac:(intros; tauto))
  as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
destruct HPP as (-> & -> & -> & P10 & Pkeep).
assert (Era : raZ regs = 0x813fc) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
rewrite Era in Ec, HS'. subst c'.
pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS0. clear HS'.
set (E' := Ereg regs' (cno_xs cx a b t [w64 n])) in *.
assert (X10 : ew E' 10 = w64 0) by (subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10).
assert (X23 : ew E' 23 = w64 (cno_F cx + 64))
  by (subst E'; rewrite (ew_Ereg_nat regs' _ 23 23%bv eq_refl), (fsw_pres _ _ 23%bv HP ltac:(cno_cs)); exact R23).
assert (X26 : ew E' 26 = w64 n)
  by (subst E'; rewrite (ew_Ereg_nat regs' _ 26 26%bv eq_refl), (fsw_pres _ _ 26%bv HP ltac:(cno_cs)); exact R26).
assert (X51 : ew E' 51 = w64 n) by (subst E'; apply segd_x51).
assert (Hn64 : 0 <= n < 2 ^ 64).
{ destruct (fsw_rblock_low B ly S W _ md mem q1 _ HAR B1) as (L1 & L2). unfold HEAD in *. lia. }
assert (KL : forall x, 0 <= x < alloc_ceiling -> aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x)
  by exact (segd_bcmp_low cx W W mem mem' Hb Pkeep).
(* the read-only region of n2 at s7 = F + 0x40 (atom 23) *)
pose proof (st_ok_add_region' tfibsegs E' _ _ (segd_rg 23 51) HS0 ltac:(vm_compute; reflexivity)
  (segd_rg_ok E' _ 23 51 (cno_F cx + 64) n ltac:(rewrite X23; unfold w64; apply wz; lia) X51 Hn64 ltac:(lia) ltac:(lia)
    (segd_val_keep W W mem mem' (cno_F cx + 64) 8 n ltac:(intros i Hi; apply KL; cbn in Hi; lia) V64)) I) as HS.
clear HS0.
(* 0x813fc bnez a0 *)
segd_run HS HJ HARU PC_bcmp rg1 mt1.
refine (SRr_sym_branch tfibsegs W E' _ _ _ _ BC_NE (SOff 10 0) (SLit 0) HS _ _).
{ intros Hc _. exfalso. rewrite (segd_br_ne0 E' 10 0 X10 ltac:(lia)) in Hc. discriminate Hc. }
intros _ HS2. clear HS. rename HS2 into HS.
(* 0x81400 a0 := n2, 0x81404 bne n2, n1 *)
segd_run HS HJ HARU PC_bcmp rg2 mt2.
refine (SRr_sym_branch tfibsegs W E' _ _ _ _ BC_NE (SOff 51 0) (SOff 26 0) HS _ _).
{ intros Hc _. exfalso. rewrite (segd_br_ne2 E' 51 26 n n X51 X26 Hn64 Hn64), Z.eqb_refl in Hc. discriminate Hc. }
intros _ HS2. clear HS. rename HS2 into HS.
(* 0x81408 a0 := r2, a1 := r3, a2 := n1, 0x81414 jal bcmp *)
segd_run HS HJ HARU PC_bcmp rg mt.
apply (HNX cx (3 + 3 + 0) ly S (c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD); (q3 - HEAD, HEAD)]) W rg mem' _ Hb).
exists a, b, t, peak', out, q1, q2, q3.
split.
{ apply (segd_mframe cx _ ly S _ W regs mem md a _ ly S _ W rg mem' _ (fun _ => False) Hm HJ HARU Hh' HZ).
  all: first [ solve [intros; tauto] | solve [segd_keep HS HP] ]. }
assert (KB : forall q, fs_rblock tfibsegs B ly S W mem q (FSH_Fn_writer.dec_size (c_db cx)) ->
  fs_rblock tfibsegs B ly S W mem' q (FSH_Fn_writer.dec_size (c_db cx))).
{ intros q Hq. apply (segd_rblock_keep ly S ly S W W mem mem' q _ Hq (proj1 Hq)). intros i Hi.
  destruct (fsw_rblock_low B ly S W _ md mem q _ HAR Hq) as (L1 & L2). apply KL. unfold HEAD in *. lia. }
assert (KZ : forall q, fs_rblock tfibsegs B ly S W mem q (FSH_Fn_writer.dec_size (c_db cx)) ->
  zbytes_at tfibsegs W mem q out -> zbytes_at tfibsegs W mem' q out).
{ intros q Hq Hz. apply (cno_zbytes_kept W W mem mem' q out); [|exact Hz]. intros j Hj.
  destruct (fsw_rblock_low B ly S W _ md mem q _ HAR Hq) as (L1 & L2). apply KL. fold n in Hj. unfold HEAD in *. lia. }
split.
{ split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|].
  split; [segd_keep HS HP; exact R22|]. split; [segd_keep HS HP; exact R23|].
  split; [segd_keep HS HP; exact R24|]. split; [segd_keep HS HP; exact R25|].
  split; [segd_keep HS HP; exact R26|].
  split; [exact Hpk|]. split; [exact Hdec|]. split; [exact Hne|]. split; [reflexivity|]. split; [lia|].
  split; [exact Hab|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
  split; [exact (KB q1 B1)|]. split; [exact (KB q2 B2)|]. split; [exact (KB q3 B3)|].
  split; [exact (KZ q1 B1 Z1)|]. split; [exact (KZ q2 B2 Z2)|]. split; [exact (KZ q3 B3 Z3)|].
  apply (cno_glob_ledger W W mem mem' _ _ _ _); [|exact Hg].
  intros x Hx. pose proof (cno_pstat_bounds x Hx). apply KL. lia. }
split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x81418 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split.
{ apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 24%bv 24 _ HS ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (fsw_pres _ _ 24%bv HP ltac:(cno_cs)). exact R24. }
split.
{ apply (segd_rd _ _ _ _ rg _ _ _ 11%bv 25%bv 25 _ HS ltac:(vm_compute; reflexivity) eq_refl).
  rewrite (fsw_pres _ _ 25%bv HP ltac:(cno_cs)). exact R25. }
apply (segd_rd _ _ _ _ rg _ _ _ 12%bv 26%bv 26 _ HS ltac:(vm_compute; reflexivity) eq_refl).
rewrite (fsw_pres _ _ 26%bv HP ltac:(cno_cs)). exact R26.
Qed.

(* ================= the third decode (0x813b8) to the first fuzz_free (0x81420) or the first bcmp (0x813f8) ======== *)
Lemma segd_D3 : cno_at B A_fuzz_free (INV_F1 B) -> cno_at B PC_bcmp INV_B1 -> cno_at B A_preset_base64_decode INV_D3.
Proof.
intros HF1 HB1 cx k ly S U W regs mem md Hb HI.
destruct HI as (a & b & t & peak' & Hm & R1 & R10 & R11 & R20 & R21 & R23 & R26 & R27 & Hct & HUt & V96 & A96 & Hpk
  & Harm).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & Hq & Hhd & _ & Hbb).
pose proof (segd_ds_pos (c_db cx)) as Hds.
destruct (segd_frame cx _ ly S _ W regs mem md a Hm) as (Hin & EF & HF4096 & HFceil & HFapp & HF32).
pose proof Hm as (HJ0 & HARU0 & Hh0 & _).
pose proof (ARU_AR tfibsegs B ly S _ W mem md HARU0) as HAR.
assert (Hsite : cno_site B cx k ly S U W regs mem md)
  by exact (cno_site_of_mframe B cx k ly S U W regs mem md a 0x813bc Hm R1 ltac:(lia) ltac:(reflexivity)).
set (Kp := fun x => cno_F cx + 96 <= x < cno_F cx + 96 + 8).
assert (HKs : forall x, cno_sp0 cx - 104 <= x < cno_sp0 cx -> ~ Kp x) by (intros x Hx X; unfold Kp in X; lia).
assert (HKf : forall i, 0 <= i < 8 -> ~ Kp (cno_F cx + 120 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (HKl : forall i, 0 <= i < 16 -> ~ Kp (cno_sp1 cx + 16 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (Ha : forall l, ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++ l ->
  0 <= a < 2 ^ 64 /\ In (t, cno_n cx + 18) (ablocks B ly S)).
{ intros l El.
  assert (Hia : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite El; apply in_or_app; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W _ md a _ HAR Hia) as (L1 & L2 & L3). unfold cno_n in *.
  split; [lia|]. rewrite El. apply in_or_app; right; right; right; left; reflexivity. }
assert (HF64 : 0 <= cno_F cx < 2 ^ 64) by lia.
destruct Harm as [(Hdec & -> & -> & Hab & R22 & R24 & Hg) |
  (out & q1 & q2 & Hdec & -> & -> & Hab & Q1 & Q2 & R22 & R24 & B1 & B2 & Z1 & Z2 & V32 & V64 & Hg)].
- (* ---- a bad text: r1 = r2 = 0 ---- *)
  destruct (Ha [] ltac:(rewrite app_nil_r; exact Hab)) as (Ha64 & Hti).
  eapply SRr_bind.
  { exact (cno_call_dec cx _ ly S (c_U cx) W regs mem md t (cno_F cx + 96) 0 (c_live cx) peak' (c_cnt cx + 2) (c_fail cx)
      Hb Hsite (or_intror (or_intror (conj R1 eq_refl))) R10 R11 Hct
      (segd_blk1 ly S _ t (cno_n cx) Hti ltac:(unfold cno_n; lia) HUt) A96 V96
      ltac:(lia) Hg ltac:(unfold quiet in *; lia) ltac:(lia)
      ltac:(unfold FSH_Fn_writer.dec_ev; rewrite Hdec; cbv [EV_preset_base64_decode EV_check_no_overread]; lia)
      (segd_bb cx ly S _ Hb Hab ltac:(cbn [cno_raw bsum fold_right snd]; unfold HEAD; lia))). }
  intros W' c' _ Hpost.
  destruct Hpost as [(_ & Hret) | (q & out & Hdec' & _ & _)]; [|rewrite Hdec in Hdec'; discriminate Hdec'].
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] _ _ Kp _ W' c' Hb Hm Hsite Ha64 Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pab & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x813bc) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
  assert (X10 : ew E' 10 = w64 0) by (subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10).
  assert (X22 : ew E' 22 = w64 0)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl), (fsw_pres _ _ 22%bv HP ltac:(cno_cs)); exact R22).
  assert (X24 : ew E' 24 = w64 0)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 24 24%bv eq_refl), (fsw_pres _ _ 24%bv HP ltac:(cno_cs)); exact R24).
  (* 0x813c8 beq (r1 <> 0), (r3 = 0): untaken *)
  segd_run HS HJ HARU A_fuzz_free rg1 mt1.
  assert (NT1 : branch_taken BC_EQ (sv_denot E' (SAlu ALU_SLTU (SLit 0) (SOff 22 0)))
    (sv_denot E' (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) = true -> False).
  { intros Hc. rewrite (segd_br_c1 E' 22 10 0 0 X22 X10 ltac:(lia) ltac:(lia)) in Hc. cbn in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SAlu ALU_SLTU (SLit 0) (SOff 22 0))
    (SAlu ALU_SLTU (SOff 10 0) (SLit 1)) HS (fun Hc _ => False_ind _ (NT1 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813d4 beqz ((r2 <> 0) xor (r3 = 0)): untaken *)
  segd_run HS HJ HARU A_fuzz_free rg2 mt2.
  assert (NT2 : branch_taken BC_EQ
    (sv_denot E' (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 24 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))))
    (sv_denot E' (SLit 0)) = true -> False).
  { intros Hc. rewrite (segd_br_c2 E' 24 10 0 0 X24 X10 ltac:(lia) ltac:(lia)) in Hc. cbn in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ
    (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 24 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) (SLit 0) HS
    (fun Hc _ => False_ind _ (NT2 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813d8 beqz s9 (r3 = 0): taken, to the frees *)
  segd_run HS HJ HARU A_fuzz_free rg3 mt3.
  assert (NT3 : branch_taken BC_EQ (sv_denot E' (SOff 10 0)) (sv_denot E' (SLit 0)) = false -> False).
  { intros Hc. rewrite (segd_br_eq0 E' 10 0 X10 ltac:(lia)) in Hc. cbn in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SOff 10 0) (SLit 0) HS _ (fun Hc _ => False_ind _ (NT3 Hc))).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x8141c a0 := r1, 0x81420 jal fuzz_free *)
  segd_run HS HJ HARU A_fuzz_free rg mt.
  apply (HF1 cx (3 + 2 * EV_preset_base64_decode + EV_preset_base64_decode) ly' S' (c_U cx) W' rg mem' _ Hb).
  exists a, b, t, (Z.max peak' (c_live cx + FSH_Fn_writer.dec_size (c_db cx))).
  split.
  { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
    all: segd_keep HS HP. }
  split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x81424 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|].
  split; [lia|].
  left. split; [exact Hdec|]. split; [reflexivity|]. split; [lia|]. split; [rewrite Pab; exact Hab|].
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 22%bv 22 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 22%bv HP ltac:(cno_cs)). exact R22. }
  split; [segd_keep HS HP; exact R22|]. split; [segd_keep HS HP; exact R24|].
  split; [exact (segd_rd _ _ _ _ rg _ _ _ 25%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
  replace (c_cnt cx + 3) with (c_cnt cx + 2 + 1) by lia. exact Pg.
- (* ---- success: r1 = q1, r2 = q2 ---- *)
  destruct (Ha _ Hab) as (Ha64 & Hti).
  pose proof (cno_dec_len _ _ Hdec) as Hlen.
  eapply SRr_bind.
  { exact (cno_call_dec cx _ ly S _ W regs mem md t (cno_F cx + 96) 0 (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx))
      peak' (c_cnt cx + 2) (c_fail cx)
      Hb Hsite (or_intror (or_intror (conj R1 eq_refl))) R10 R11 Hct
      (segd_blk1 ly S _ t (cno_n cx) Hti ltac:(unfold cno_n; lia) HUt) A96 V96
      ltac:(lia) Hg ltac:(unfold quiet in *; lia) ltac:(lia)
      ltac:(unfold FSH_Fn_writer.dec_ev; rewrite Hdec; cbv [EV_fuzz_malloc EV_check_no_overread]; lia)
      (segd_bb cx ly S _ Hb Hab ltac:(rewrite cno_bsum_app; cbn [cno_raw bsum fold_right snd]; unfold HEAD; lia))). }
  intros W' c' _ Hpost.
  destruct Hpost as [(Hdec' & _) | (q & out' & Hdec' & Hq0 & Hret)]; [rewrite Hdec in Hdec'; discriminate Hdec'|].
  rewrite Hdec in Hdec'. injection Hdec' as <-.
  set (n := Z.of_nat (length out)) in *.
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [w64 n; w64 n; w64 n] _ _ Kp _ W' c' Hb Hm Hsite Ha64
    Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pq & Pab & Prb & Pz & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x813bc) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS0. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [w64 n; w64 n; w64 n])) in *.
  pose proof (ARU_AR tfibsegs B ly' S' _ W' mem' md' HARU) as HAR'.
  destruct (fsw_rblock_low B ly' S' W' _ md' mem' q _ HAR' Prb) as (L1q & L2q).
  destruct (fsw_rblock_low B ly S W _ md mem q1 _ HAR B1) as (L11 & L21).
  destruct (fsw_rblock_low B ly S W _ md mem q2 _ HAR B2) as (L12 & L22).
  assert (Hn64 : 0 <= n < 2 ^ 64) by (subst n; unfold HEAD in *; lia).
  assert (X10 : ew E' 10 = w64 q) by (subst E'; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact P10).
  assert (X22 : ew E' 22 = w64 q1)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 22 22%bv eq_refl), (fsw_pres _ _ 22%bv HP ltac:(cno_cs)); exact R22).
  assert (X24 : ew E' 24 = w64 q2)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 24 24%bv eq_refl), (fsw_pres _ _ 24%bv HP ltac:(cno_cs)); exact R24).
  assert (X51 : ew E' 51 = w64 n) by (subst E'; apply segd_x51).
  assert (X52 : ew E' 52 = w64 n) by (subst E'; apply segd_x52).
  assert (X53 : ew E' 53 = w64 n) by (subst E'; apply segd_x53).
  assert (U23 : bv_unsigned (ew E' 23) = cno_F cx + 64)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 23 23%bv eq_refl), (fsw_pres _ _ 23%bv HP ltac:(cno_cs)), R23;
        unfold w64; apply wz; lia).
  assert (U26 : bv_unsigned (ew E' 26) = cno_F cx + 32)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 26 26%bv eq_refl), (fsw_pres _ _ 26%bv HP ltac:(cno_cs)), R26;
        unfold w64; apply wz; lia).
  assert (U27 : bv_unsigned (ew E' 27) = cno_F cx + 96)
    by (subst E'; rewrite (ew_Ereg_nat regs' _ 27 27%bv eq_refl), (fsw_pres _ _ 27%bv HP ltac:(cno_cs)), R27;
        unfold w64; apply wz; lia).
  assert (V32' : val_mem tfibsegs (mrestrict (w_H W') mem') (cno_F cx + 32) 8 n)
    by exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 32) n HZ ltac:(lia) ltac:(lia) ltac:(intros i Hi X; unfold Kp in X; lia) V32).
  assert (V64' : val_mem tfibsegs (mrestrict (w_H W') mem') (cno_F cx + 64) 8 n)
    by exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 64) n HZ ltac:(lia) ltac:(lia) ltac:(intros i Hi X; unfold Kp in X; lia) V64).
  (* the three lengths, read-only at s10 = F + 0x20 (atom 26), s7 = F + 0x40 (23), s11 = F + 0x60 (27) *)
  pose proof (st_ok_add_region' tfibsegs E' _ _ (segd_rg 27 53) HS0 ltac:(vm_compute; reflexivity)
    (segd_rg_ok E' _ 27 53 (cno_F cx + 96) n U27 X53 Hn64 ltac:(lia) ltac:(lia) Pv) I) as HS1.
  clear HS0.
  assert (D1 : extent_disjoint E' (segd_rg 23 52) (segd_rg 27 53))
    by (unfold extent_disjoint, segd_rg; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U23, U27; lia).
  pose proof (st_ok_add_region' tfibsegs E' _ _ (segd_rg 23 52) HS1 ltac:(vm_compute; reflexivity)
    (segd_rg_ok E' _ 23 52 (cno_F cx + 64) n U23 X52 Hn64 ltac:(lia) ltac:(lia) V64') (conj D1 I)) as HS2.
  clear HS1.
  assert (D2 : extent_disjoint E' (segd_rg 26 51) (segd_rg 23 52))
    by (unfold extent_disjoint, segd_rg; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U26, U23; lia).
  assert (D3 : extent_disjoint E' (segd_rg 26 51) (segd_rg 27 53))
    by (unfold extent_disjoint, segd_rg; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U26, U27; lia).
  pose proof (st_ok_add_region' tfibsegs E' _ _ (segd_rg 26 51) HS2 ltac:(vm_compute; reflexivity)
    (segd_rg_ok E' _ 26 51 (cno_F cx + 32) n U26 X51 Hn64 ltac:(lia) ltac:(lia) V32') (conj D2 (conj D3 I))) as HS.
  clear HS2.
  (* what the third decode kept of the first two blocks *)
  assert (Hsub : forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S'))
    by (intros x Hx; rewrite Pab; apply in_or_app; left; exact Hx).
  destruct (segd_keep_dec cx ly S _ W mem md ly' S' W' mem' (cno_F cx + 96) q1 _ out Hb HARU0 Hin EF ltac:(lia)
    ltac:(lia) HBK Hsub B1 ltac:(lia) Z1) as (B1' & Z1').
  destruct (segd_keep_dec cx ly S _ W mem md ly' S' W' mem' (cno_F cx + 96) q2 _ out Hb HARU0 Hin EF ltac:(lia)
    ltac:(lia) HBK Hsub B2 ltac:(lia) Z2) as (B2' & Z2').
  (* 0x813c8 beq (r1 <> 0), (r3 = 0): untaken *)
  segd_run HS HJ HARU A_fuzz_free rg1 mt1.
  assert (NT1 : branch_taken BC_EQ (sv_denot E' (SAlu ALU_SLTU (SLit 0) (SOff 22 0)))
    (sv_denot E' (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) = true -> False).
  { intros Hc. rewrite (segd_br_c1 E' 22 10 q1 q X22 X10 ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia)) in Hc.
    rewrite (proj2 (Z.eqb_neq q1 0)), (proj2 (Z.eqb_neq q 0)) in Hc by (unfold HEAD in *; lia).
    cbn in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SAlu ALU_SLTU (SLit 0) (SOff 22 0))
    (SAlu ALU_SLTU (SOff 10 0) (SLit 1)) HS (fun Hc _ => False_ind _ (NT1 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813d4 beqz ((r2 <> 0) xor (r3 = 0)): untaken *)
  segd_run HS HJ HARU A_fuzz_free rg2 mt2.
  assert (NT2 : branch_taken BC_EQ
    (sv_denot E' (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 24 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))))
    (sv_denot E' (SLit 0)) = true -> False).
  { intros Hc. rewrite (segd_br_c2 E' 24 10 q2 q X24 X10 ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia)) in Hc.
    rewrite (proj2 (Z.eqb_neq q2 0)), (proj2 (Z.eqb_neq q 0)) in Hc by (unfold HEAD in *; lia).
    cbn in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ
    (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 24 0)) (SAlu ALU_SLTU (SOff 10 0) (SLit 1))) (SLit 0) HS
    (fun Hc _ => False_ind _ (NT2 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813d8 beqz s9 (r3 = q <> 0): untaken *)
  segd_run HS HJ HARU A_fuzz_free rg3 mt3.
  assert (NT3 : branch_taken BC_EQ (sv_denot E' (SOff 10 0)) (sv_denot E' (SLit 0)) = true -> False).
  { intros Hc. rewrite (segd_br_eq0 E' 10 q X10 ltac:(unfold HEAD in *; lia)) in Hc. apply Z.eqb_eq in Hc.
    unfold HEAD in *. lia. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SOff 10 0) (SLit 0) HS (fun Hc _ => False_ind _ (NT3 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813dc / 0x813e0 n1, n3 loaded; 0x813e4 bne n1, n3: untaken *)
  segd_run HS HJ HARU A_fuzz_free rg4 mt4.
  assert (NT4 : branch_taken BC_NE (sv_denot E' (SOff 51 0)) (sv_denot E' (SOff 53 0)) = true -> False).
  { intros Hc. rewrite (segd_br_ne2 E' 51 53 n n X51 X53 Hn64 Hn64), Z.eqb_refl in Hc. discriminate Hc. }
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_NE (SOff 51 0) (SOff 53 0) HS (fun Hc _ => False_ind _ (NT4 Hc)) _).
  intros _ HS2. clear HS. rename HS2 into HS.
  (* 0x813e8 beqz n1: out = [] or not *)
  segd_run HS HJ HARU A_fuzz_free rg5 mt5.
  refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SOff 51 0) (SLit 0) HS _ _).
  + (* out = []: 0x81540 n2 loaded, 0x81544 beq n2, n1: taken back to the frees *)
    intros Hc HS2. clear HS. rename HS2 into HS.
    rewrite (segd_br_eq0 E' 51 n X51 Hn64) in Hc. apply Z.eqb_eq in Hc.
    segd_run HS HJ HARU A_fuzz_free rg6 mt6.
    assert (NT6 : branch_taken BC_EQ (sv_denot E' (SOff 52 0)) (sv_denot E' (SOff 51 0)) = false -> False).
    { intros Hc6. rewrite (segd_br_eq2 E' 52 51 n n X52 X51 Hn64 Hn64), Z.eqb_refl in Hc6. discriminate Hc6. }
    refine (SRr_sym_branch tfibsegs W' E' _ _ _ _ BC_EQ (SOff 52 0) (SOff 51 0) HS _ (fun Hc6 _ => False_ind _ (NT6 Hc6))).
    intros _ HS2. clear HS. rename HS2 into HS.
    (* 0x8141c a0 := r1, 0x81420 jal fuzz_free *)
    segd_run HS HJ HARU A_fuzz_free rg mt.
    apply (HF1 cx (3 + 2 + 1) ly' S' ((c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD)]) ++ [(q - HEAD, HEAD)]) W' rg mem'
      _ Hb).
    exists a, b, t, (Z.max peak' (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx))).
    split.
    { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
      all: segd_keep HS HP. }
    split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x81424 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|].
    split; [lia|].
    right. exists out, q1, q2, q.
    split; [exact Hdec|]. split; [rewrite <- app_assoc; reflexivity|]. split; [lia|].
    split; [rewrite Pab, Hab, <- !app_assoc; reflexivity|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Pq|].
    split.
    { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 22%bv 22 _ HS ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 22%bv HP ltac:(cno_cs)). exact R22. }
    split; [segd_keep HS HP; exact R22|]. split; [segd_keep HS HP; exact R24|].
    split; [exact (segd_rd _ _ _ _ rg _ _ _ 25%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
    split; [exact B1'|]. split; [exact B2'|]. split; [exact Prb|].
    replace (c_live cx + 3 * FSH_Fn_writer.dec_size (c_db cx))
      with (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx)) by lia.
    replace (c_cnt cx + 3) with (c_cnt cx + 2 + 1) by lia. exact Pg.
  + (* out <> []: 0x813ec .. 0x813f8 bcmp (r1, r3, n1) *)
    intros Hc HS2. clear HS. rename HS2 into HS.
    rewrite (segd_br_eq0 E' 51 n X51 Hn64) in Hc. apply Z.eqb_neq in Hc.
    segd_run HS HJ HARU PC_bcmp rg mt.
    apply (HB1 cx (3 + 2 + 1) ly' S' ((c_U cx ++ [(q1 - HEAD, HEAD); (q2 - HEAD, HEAD)]) ++ [(q - HEAD, HEAD)]) W' rg mem'
      _ Hb).
    exists a, b, t, (Z.max peak' (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx))),
      out, q1, q2, q.
    assert (R26' : getr rg 26 = w64 n).
    { pose proof (cno_reg _ E' _ _ 26%bv 51 HS ltac:(vm_compute; reflexivity)) as X. cbn [ms_regs mkst] in X.
      rewrite X. exact X51. }
    assert (R12' : getr rg 12 = w64 n).
    { pose proof (cno_reg _ E' _ _ 12%bv 51 HS ltac:(vm_compute; reflexivity)) as X. cbn [ms_regs mkst] in X.
      rewrite X. exact X51. }
    split.
    { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
      all: segd_keep HS HP. }
    split.
    { split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|].
      split; [segd_keep HS HP; exact R22|]. split; [segd_keep HS HP; exact R23|].
      split; [segd_keep HS HP; exact R24|].
      split; [exact (segd_rd _ _ _ _ rg _ _ _ 25%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
      split; [exact R26'|].
      split; [lia|]. split; [exact Hdec|]. split; [intros E0; subst n; rewrite E0 in Hc; cbn in Hc; lia|].
      split; [rewrite <- app_assoc; reflexivity|]. split; [lia|].
      split; [rewrite Pab, Hab, <- !app_assoc; reflexivity|].
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Pq|].
      split; [exact B1'|]. split; [exact B2'|]. split; [exact Prb|].
      split; [exact Z1'|]. split; [exact Z2'|]. split; [exact Pz|].
      replace (c_live cx + 3 * FSH_Fn_writer.dec_size (c_db cx))
        with (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx)) by lia.
      replace (c_cnt cx + 3) with (c_cnt cx + 2 + 1) by lia. exact Pg. }
    split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x813fc HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split.
    { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 22%bv 22 _ HS ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 22%bv HP ltac:(cno_cs)). exact R22. }
    split; [exact (segd_rd _ _ _ _ rg _ _ _ 11%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
    split; [exact R12'|]. exact V64'.
Qed.

(* ================= the second decode (0x813a8) to the third (0x813b8) ================= *)
Lemma segd_D2 : cno_at B A_preset_base64_decode INV_D3 -> cno_at B A_preset_base64_decode INV_D2.
Proof.
intros HNX cx k ly S U W regs mem md Hb HI.
destruct HI as (a & b & t & peak' & Hm & R1 & R10 & R11 & R20 & R21 & R23 & R26 & R27 & Hcb & Hct & HUb & HUt & V64 & V96
  & A64 & A96 & Hpk & Harm).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hmax & _ & Hq & Hhd & _ & Hbb).
pose proof (segd_ds_pos (c_db cx)) as Hds.
destruct (segd_frame cx _ ly S _ W regs mem md a Hm) as (Hin & EF & HF4096 & HFceil & HFapp & HF32).
pose proof Hm as (HJ0 & HARU0 & Hh0 & _).
pose proof (ARU_AR tfibsegs B ly S _ W mem md HARU0) as HAR.
assert (Hsite : cno_site B cx k ly S U W regs mem md)
  by exact (cno_site_of_mframe B cx k ly S U W regs mem md a 0x813ac Hm R1 ltac:(lia) ltac:(reflexivity)).
set (Kp := fun x => cno_F cx + 64 <= x < cno_F cx + 64 + 8).
assert (HKs : forall x, cno_sp0 cx - 104 <= x < cno_sp0 cx -> ~ Kp x) by (intros x Hx X; unfold Kp in X; lia).
assert (HKf : forall i, 0 <= i < 8 -> ~ Kp (cno_F cx + 120 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (HKl : forall i, 0 <= i < 16 -> ~ Kp (cno_sp1 cx + 16 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (HKsh : forall y, cno_SF cx <= y < cno_SF cx + 16 -> ~ Kp y).
{ intros y Hy X. unfold Kp in X. unfold cno_SF, shadow_addr, SHADOW_OFF in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. Z.div_mod_to_equations. lia. }
assert (Ha : forall l, ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ cno_raw cx a b t ++ l ->
  0 <= a < 2 ^ 64 /\ In (b, cno_n cx + 18) (ablocks B ly S) /\ In (t, cno_n cx + 18) (ablocks B ly S)).
{ intros l El.
  assert (Hia : In (a, cno_n cx + 18) (ablocks B ly S)) by (rewrite El; apply in_or_app; right; left; reflexivity).
  destruct (fsw_ablock_low B ly S W _ md a _ HAR Hia) as (L1 & L2 & L3). unfold cno_n in *.
  split; [lia|]. rewrite El. split; apply in_or_app; right; right; [left | right; left]; reflexivity. }
assert (V96' : forall (W' : world tfibsegs) mem',
  (forall x, cno_zone cx x -> ~ Kp x -> aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (cno_F cx + 96) 8 0 /\
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (cno_F cx + 96) 8).
{ intros W' mem' HZ. split.
  - exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 96) 0 HZ ltac:(lia) ltac:(lia)
      ltac:(intros i Hi X; unfold Kp in X; lia) V96).
  - exact (segd_zone_ra cx W W' mem mem' Kp (cno_F cx + 96) HZ HF4096 HF32 ltac:(lia) ltac:(lia) HKsh A96). }
destruct Harm as [(Hdec & -> & -> & Hab & R22 & Hg) |
  (out & q1 & Hdec & -> & -> & Hab & Q1 & R22 & B1 & Z1 & V32 & Hg)].
- (* ---- a bad text ---- *)
  destruct (Ha [] ltac:(rewrite app_nil_r; exact Hab)) as (Ha64 & Hbi & Hti).
  eapply SRr_bind.
  { exact (cno_call_dec cx _ ly S (c_U cx) W regs mem md b (cno_F cx + 64) 0 (c_live cx) peak' (c_cnt cx + 1) (c_fail cx)
      Hb Hsite (or_intror (or_introl (conj R1 eq_refl))) R10 R11 Hcb
      (segd_blk1 ly S _ b (cno_n cx) Hbi ltac:(unfold cno_n; lia) HUb) A64 V64
      ltac:(lia) Hg ltac:(unfold quiet in *; lia) ltac:(lia)
      ltac:(unfold FSH_Fn_writer.dec_ev; rewrite Hdec; cbv [EV_preset_base64_decode EV_check_no_overread]; lia)
      (segd_bb cx ly S _ Hb Hab ltac:(cbn [cno_raw bsum fold_right snd]; unfold HEAD; lia))). }
  intros W' c' _ Hpost.
  destruct Hpost as [(_ & Hret) | (q & out & Hdec' & _ & _)]; [|rewrite Hdec in Hdec'; discriminate Hdec'].
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] _ _ Kp _ W' c' Hb Hm Hsite Ha64 Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pab & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x813ac) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
  destruct (Pstr t (c_db cx) t (cno_n cx + 18) Hti (Z.le_refl t) ltac:(unfold cno_n; lia) HUt Hct) as (Hct' & HUt').
  destruct (V96' W' mem' HZ) as (V96'' & A96').
  (* 0x813ac s8 := r2, a0 := t, a1 := s11, 0x813b8 jal preset_base64_decode *)
  segd_run HS HJ HARU A_preset_base64_decode rg mt.
  apply (HNX cx (3 + EV_preset_base64_decode + EV_preset_base64_decode) ly' S' (c_U cx) W' rg mem' _ Hb).
  exists a, b, t, (Z.max peak' (c_live cx + FSH_Fn_writer.dec_size (c_db cx))).
  split.
  { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
    all: segd_keep HS HP. }
  split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x813bc HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 21%bv 21 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 21%bv HP ltac:(cno_cs)). exact R21. }
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 11%bv 27%bv 27 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 27%bv HP ltac:(cno_cs)). exact R27. }
  split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|]. split; [segd_keep HS HP; exact R23|].
  split; [segd_keep HS HP; exact R26|]. split; [segd_keep HS HP; exact R27|].
  split; [exact Hct'|]. split; [exact HUt'|]. split; [exact V96''|]. split; [exact A96'|]. split; [lia|].
  left. split; [exact Hdec|]. split; [reflexivity|]. split; [lia|]. split; [rewrite Pab; exact Hab|].
  split; [segd_keep HS HP; exact R22|].
  split; [exact (segd_rd _ _ _ _ rg _ _ _ 24%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
  replace (c_cnt cx + 2) with (c_cnt cx + 1 + 1) by lia. exact Pg.
- (* ---- success ---- *)
  destruct (Ha _ Hab) as (Ha64 & Hbi & Hti).
  pose proof (cno_dec_len _ _ Hdec) as Hlen.
  eapply SRr_bind.
  { exact (cno_call_dec cx _ ly S _ W regs mem md b (cno_F cx + 64) 0 (c_live cx + FSH_Fn_writer.dec_size (c_db cx))
      peak' (c_cnt cx + 1) (c_fail cx)
      Hb Hsite (or_intror (or_introl (conj R1 eq_refl))) R10 R11 Hcb
      (segd_blk1 ly S _ b (cno_n cx) Hbi ltac:(unfold cno_n; lia) HUb) A64 V64
      ltac:(lia) Hg ltac:(unfold quiet in *; lia) ltac:(lia)
      ltac:(unfold FSH_Fn_writer.dec_ev; rewrite Hdec; cbv [EV_fuzz_malloc EV_check_no_overread]; lia)
      (segd_bb cx ly S _ Hb Hab ltac:(rewrite cno_bsum_app; cbn [cno_raw bsum fold_right snd]; unfold HEAD; lia))). }
  intros W' c' _ Hpost.
  destruct Hpost as [(Hdec' & _) | (q & out' & Hdec' & Hq0 & Hret)]; [rewrite Hdec in Hdec'; discriminate Hdec'|].
  rewrite Hdec in Hdec'. injection Hdec' as <-.
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] _ _ Kp _ W' c' Hb Hm Hsite Ha64 Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pq & Pab & Prb & Pz & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x813ac) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
  destruct (Pstr t (c_db cx) t (cno_n cx + 18) Hti (Z.le_refl t) ltac:(unfold cno_n; lia) HUt Hct) as (Hct' & HUt').
  destruct (V96' W' mem' HZ) as (V96'' & A96').
  assert (Hsub : forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S'))
    by (intros x Hx; rewrite Pab; apply in_or_app; left; exact Hx).
  destruct (segd_keep_dec cx ly S _ W mem md ly' S' W' mem' (cno_F cx + 64) q1 _ out Hb HARU0 Hin EF ltac:(lia)
    ltac:(lia) HBK Hsub B1 ltac:(lia) Z1) as (B1' & Z1').
  assert (V32' : val_mem tfibsegs (mrestrict (w_H W') mem') (cno_F cx + 32) 8 (Z.of_nat (length out)))
    by exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 32) _ HZ ltac:(lia) ltac:(lia)
      ltac:(intros i Hi X; unfold Kp in X; lia) V32).
  segd_run HS HJ HARU A_preset_base64_decode rg mt.
  apply (HNX cx (3 + 1 + 1) ly' S' ((c_U cx ++ [(q1 - HEAD, HEAD)]) ++ [(q - HEAD, HEAD)]) W' rg mem' _ Hb).
  exists a, b, t, (Z.max peak' (c_live cx + FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx))).
  split.
  { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
    all: segd_keep HS HP. }
  split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x813bc HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 21%bv 21 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 21%bv HP ltac:(cno_cs)). exact R21. }
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 11%bv 27%bv 27 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 27%bv HP ltac:(cno_cs)). exact R27. }
  split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|]. split; [segd_keep HS HP; exact R23|].
  split; [segd_keep HS HP; exact R26|]. split; [segd_keep HS HP; exact R27|].
  split; [exact Hct'|]. split; [exact HUt'|]. split; [exact V96''|]. split; [exact A96'|]. split; [lia|].
  right. exists out, q1, q.
  split; [exact Hdec|]. split; [rewrite <- app_assoc; reflexivity|]. split; [lia|].
  split; [rewrite Pab, Hab, <- !app_assoc; reflexivity|].
  split; [exact Q1|]. split; [exact Pq|].
  split; [segd_keep HS HP; exact R22|].
  split; [exact (segd_rd _ _ _ _ rg _ _ _ 24%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
  split; [exact B1'|]. split; [exact Prb|]. split; [exact Z1'|]. split; [exact Pz|].
  split; [exact V32'|]. split; [exact Pv|].
  replace (c_live cx + 2 * FSH_Fn_writer.dec_size (c_db cx))
    with (c_live cx + FSH_Fn_writer.dec_size (c_db cx) + FSH_Fn_writer.dec_size (c_db cx)) by lia.
  replace (c_cnt cx + 2) with (c_cnt cx + 1 + 1) by lia. exact Pg.
Qed.

(* ================= the first decode (0x81398) to the second (0x813a8) ================= *)
Lemma segd_D1 : cno_at B A_preset_base64_decode INV_D2 -> cno_at B A_preset_base64_decode (INV_D1 B).
Proof.
intros HNX cx k ly S U W regs mem md Hb HI.
destruct HI as (a & b & t & -> & -> & Hm & Hab & R1 & R10 & R11 & R20 & R21 & R23 & R26 & R27 & Hza & Hzb & Hzt & V32 & V64
  & V96 & A32 & A64 & A96 & Hg).
pose proof (cno_nums B cx Hb) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cno_stk as FS.
pose proof Hb as (_ & Hhe & _ & _ & _ & _ & _ & Hnz & _ & Hmax & _ & Hq & Hhd & _ & Hbb).
pose proof (segd_ds_pos (c_db cx)) as Hds.
destruct (segd_frame cx _ ly S _ W regs mem md a Hm) as (Hin & EF & HF4096 & HFceil & HFapp & HF32).
pose proof Hm as (HJ0 & HARU0 & Hh0 & _).
pose proof (ARU_AR tfibsegs B ly S _ W mem md HARU0) as HAR.
assert (Hsite : cno_site B cx 3 ly S (c_U cx) W regs mem md)
  by exact (cno_site_of_mframe B cx 3 ly S (c_U cx) W regs mem md a 0x8139c Hm R1 ltac:(lia) ltac:(reflexivity)).
(* the three texts: each the start of a raw block, holding db then a NUL; no range of the entry's U on them *)
assert (Hraw : forall p, In (p, cno_n cx + 18) (cno_raw cx a b t) ->
  In (p, cno_n cx + 18) (ablocks B ly S) /\ 0 <= p < 2 ^ 64 /\
  (forall r, In r (c_U cx) -> p + cno_n cx + 1 <= fst r \/ fst r + snd r <= p)).
{ intros p Hp. assert (Hpi : In (p, cno_n cx + 18) (ablocks B ly S)) by (rewrite Hab; apply in_or_app; right; exact Hp).
  destruct (fsw_ablock_low B ly S W _ md p _ HAR Hpi) as (L1 & L2 & L3).
  split; [exact Hpi|]. split; [unfold cno_n in *; lia|].
  intros r Hr. destruct (segd_U_new cx ly S W _ md p _ _ HAR Hhe Hab Hp r Hr); unfold cno_n in *; lia. }
destruct (Hraw a ltac:(left; reflexivity)) as (Hai & Ha64 & HUa).
destruct (Hraw b ltac:(right; left; reflexivity)) as (Hbi & Hb64 & HUb).
destruct (Hraw t ltac:(right; right; left; reflexivity)) as (Hti & Ht64 & HUt).
assert (Hlen32 : Z.of_nat (length (c_db cx)) < 2 ^ 32) by (unfold cno_n, PRESET_FILE_MAX_BYTES in *; lia).
assert (Hca : cstr_ok tfibsegs W mem a (c_db cx)).
{ apply (segd_cstr_blk ly S (c_U cx) W mem md a (cno_n cx + 18) (c_db cx) HARU0 Hh0 Hai); [| exact Hnz | unfold cno_n; lia
    | exact Hlen32 | exact HUa].
  apply (segd_zb_prefix W mem a _ ([65 mod 256; 65] ++ repeat 0 15)).
  replace ((c_db cx ++ [0]) ++ [65 mod 256; 65] ++ repeat 0 15) with (pn_copy (c_db cx) 65)
    by (unfold pn_copy; rewrite <- app_assoc; reflexivity). exact Hza. }
assert (Hcb : cstr_ok tfibsegs W mem b (c_db cx)).
{ apply (segd_cstr_blk ly S (c_U cx) W mem md b (cno_n cx + 18) (c_db cx) HARU0 Hh0 Hbi); [| exact Hnz | unfold cno_n; lia
    | exact Hlen32 | exact HUb].
  apply (segd_zb_prefix W mem b _ ([66 mod 256; 65] ++ repeat 0 15)).
  replace ((c_db cx ++ [0]) ++ [66 mod 256; 65] ++ repeat 0 15) with (pn_copy (c_db cx) 66)
    by (unfold pn_copy; rewrite <- app_assoc; reflexivity). exact Hzb. }
assert (Hct : cstr_ok tfibsegs W mem t (c_db cx)).
{ apply (segd_cstr_blk ly S (c_U cx) W mem md t (cno_n cx + 18) (c_db cx) HARU0 Hh0 Hti); [| exact Hnz | unfold cno_n; lia
    | exact Hlen32 | exact HUt].
  apply (segd_zb_prefix W mem t _ (repeat 0 17)).
  replace ((c_db cx ++ [0]) ++ repeat 0 17) with (c_db cx ++ repeat 0 18) by (rewrite <- app_assoc; reflexivity).
  exact Hzt. }
set (Kp := fun x => cno_F cx + 32 <= x < cno_F cx + 32 + 8).
assert (HKs : forall x, cno_sp0 cx - 104 <= x < cno_sp0 cx -> ~ Kp x) by (intros x Hx X; unfold Kp in X; lia).
assert (HKf : forall i, 0 <= i < 8 -> ~ Kp (cno_F cx + 120 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (HKl : forall i, 0 <= i < 16 -> ~ Kp (cno_sp1 cx + 16 + i)) by (intros i Hi X; unfold Kp in X; lia).
assert (HKsh : forall y, cno_SF cx <= y < cno_SF cx + 16 -> ~ Kp y).
{ intros y Hy X. unfold Kp in X. unfold cno_SF, shadow_addr, SHADOW_OFF in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. Z.div_mod_to_equations. lia. }
eapply SRr_bind.
{ exact (cno_call_dec cx 3 ly S (c_U cx) W regs mem md a (cno_F cx + 32) 0 (c_live cx) (c_peak cx) (c_cnt cx) (c_fail cx)
    Hb Hsite (or_introl (conj R1 eq_refl)) R10 R11 Hca
    (segd_blk1 ly S _ a (cno_n cx) Hai ltac:(unfold cno_n; lia) HUa) A32 V32
    ltac:(lia) Hg ltac:(unfold quiet in *; lia) ltac:(lia)
    ltac:(unfold FSH_Fn_writer.dec_ev; destruct (WriterSpec.b64_dec (c_db cx));
          cbv [EV_fuzz_malloc EV_preset_base64_decode EV_check_no_overread]; lia)
    (segd_bb cx ly S _ Hb Hab ltac:(cbn [cno_raw bsum fold_right snd]; unfold HEAD; lia))). }
intros W' c' _ Hpost.
destruct Hpost as [(Hdec & Hret) | (q & out & Hdec & Hq0 & Hret)].
- (* ---- a bad text ---- *)
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] _ _ Kp _ W' c' Hb Hm Hsite Ha64 Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pab & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x8139c) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
  destruct (Pstr b (c_db cx) b (cno_n cx + 18) Hbi (Z.le_refl b) ltac:(unfold cno_n; lia) HUb Hcb) as (Hcb' & HUb').
  destruct (Pstr t (c_db cx) t (cno_n cx + 18) Hti (Z.le_refl t) ltac:(unfold cno_n; lia) HUt Hct) as (Hct' & HUt').
  (* 0x8139c s6 := r1, a0 := b, a1 := s7, 0x813a8 jal preset_base64_decode *)
  segd_run HS HJ HARU A_preset_base64_decode rg mt.
  apply (HNX cx (3 + EV_preset_base64_decode) ly' S' (c_U cx) W' rg mem' _ Hb).
  exists a, b, t, (Z.max (c_peak cx) (c_live cx + FSH_Fn_writer.dec_size (c_db cx))).
  split.
  { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
    all: segd_keep HS HP. }
  split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x813ac HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 20%bv 20 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 20%bv HP ltac:(cno_cs)). exact R20. }
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 11%bv 23%bv 23 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 23%bv HP ltac:(cno_cs)). exact R23. }
  split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|]. split; [segd_keep HS HP; exact R23|].
  split; [segd_keep HS HP; exact R26|]. split; [segd_keep HS HP; exact R27|].
  split; [exact Hcb'|]. split; [exact Hct'|]. split; [exact HUb'|]. split; [exact HUt'|].
  split; [exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 64) 0 HZ ltac:(lia) ltac:(lia)
    ltac:(intros i Hi X; unfold Kp in X; lia) V64)|].
  split; [exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 96) 0 HZ ltac:(lia) ltac:(lia)
    ltac:(intros i Hi X; unfold Kp in X; lia) V96)|].
  split; [exact (segd_zone_ra cx W W' mem mem' Kp (cno_F cx + 64) HZ HF4096 HF32 ltac:(lia) ltac:(lia) HKsh A64)|].
  split; [exact (segd_zone_ra cx W W' mem mem' Kp (cno_F cx + 96) HZ HF4096 HF32 ltac:(lia) ltac:(lia) HKsh A96)|].
  split; [lia|].
  left. split; [exact Hdec|]. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Pab; exact Hab|].
  split; [exact (segd_rd _ _ _ _ rg _ _ _ 22%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
  exact Pg.
- (* ---- success ---- *)
  destruct (cno_mframe_resume B cx _ ly S _ W regs mem md a b t [] _ _ Kp _ W' c' Hb Hm Hsite Ha64 Hret HKs HKf HKl)
    as (ly' & S' & regs' & mem' & md' & Ec & HJ & HARU & Hh' & HP & HBK & HZ & HPP & HS').
  cbv beta in HPP. destruct HPP as (P10 & Pq & Pab & Prb & Pz & Pv & Pg & Pstr).
  assert (Era : raZ regs = 0x8139c) by (unfold raZ; rewrite R1; unfold w64; apply wz; lia).
  rewrite Era in Ec, HS'. subst c'.
  pose proof (YL07.st_ok_relayout tfibsegs _ _ _ [] HS' ltac:(vm_compute; reflexivity)) as HS. clear HS'.
  set (E' := Ereg regs' (cno_xs cx a b t [])) in *.
  destruct (Pstr b (c_db cx) b (cno_n cx + 18) Hbi (Z.le_refl b) ltac:(unfold cno_n; lia) HUb Hcb) as (Hcb' & HUb').
  destruct (Pstr t (c_db cx) t (cno_n cx + 18) Hti (Z.le_refl t) ltac:(unfold cno_n; lia) HUt Hct) as (Hct' & HUt').
  segd_run HS HJ HARU A_preset_base64_decode rg mt.
  apply (HNX cx (3 + 1) ly' S' (c_U cx ++ [(q - HEAD, HEAD)]) W' rg mem' _ Hb).
  exists a, b, t, (Z.max (c_peak cx) (c_live cx + FSH_Fn_writer.dec_size (c_db cx))).
  split.
  { apply (segd_mframe cx _ ly S _ W regs mem md a _ ly' S' _ W' rg mem' _ Kp Hm HJ HARU Hh' HZ HKs HKf HKl).
    all: segd_keep HS HP. }
  split; [exact (fsw_reg_lit _ E' _ _ 1%bv 0x813ac HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 10%bv 20%bv 20 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 20%bv HP ltac:(cno_cs)). exact R20. }
  split.
  { apply (segd_rd _ _ _ _ rg _ _ _ 11%bv 23%bv 23 _ HS ltac:(vm_compute; reflexivity) eq_refl).
    rewrite (fsw_pres _ _ 23%bv HP ltac:(cno_cs)). exact R23. }
  split; [segd_keep HS HP; exact R20|]. split; [segd_keep HS HP; exact R21|]. split; [segd_keep HS HP; exact R23|].
  split; [segd_keep HS HP; exact R26|]. split; [segd_keep HS HP; exact R27|].
  split; [exact Hcb'|]. split; [exact Hct'|]. split; [exact HUb'|]. split; [exact HUt'|].
  split; [exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 64) 0 HZ ltac:(lia) ltac:(lia)
    ltac:(intros i Hi X; unfold Kp in X; lia) V64)|].
  split; [exact (segd_zone_val cx W W' mem mem' Kp (cno_F cx + 96) 0 HZ ltac:(lia) ltac:(lia)
    ltac:(intros i Hi X; unfold Kp in X; lia) V96)|].
  split; [exact (segd_zone_ra cx W W' mem mem' Kp (cno_F cx + 64) HZ HF4096 HF32 ltac:(lia) ltac:(lia) HKsh A64)|].
  split; [exact (segd_zone_ra cx W W' mem mem' Kp (cno_F cx + 96) HZ HF4096 HF32 ltac:(lia) ltac:(lia) HKsh A96)|].
  split; [lia|].
  right. exists out, q.
  split; [exact Hdec|]. split; [reflexivity|]. split; [reflexivity|].
  split; [rewrite Pab, Hab, <- !app_assoc; reflexivity|].
  split; [exact Pq|].
  split; [exact (segd_rd _ _ _ _ rg _ _ _ 22%bv 10%bv 10 _ HS ltac:(vm_compute; reflexivity) eq_refl P10)|].
  split; [exact Prb|]. split; [exact Pz|]. split; [exact Pv|]. exact Pg.
Qed.

(* ================= segment D ================= *)
Lemma cno_segD : cno_segD_T B.
Proof.
intros HF1. apply segd_D1, segd_D2, segd_D3; [exact HF1|]. apply segd_B1, segd_B2, HF1.
Qed.
End D.
