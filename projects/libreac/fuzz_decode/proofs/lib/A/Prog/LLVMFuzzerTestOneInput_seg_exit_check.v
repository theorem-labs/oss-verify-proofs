(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module names changed; 695 of its 789 lines of code are new or changed and 2595 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_check: the first piece of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput, i.e. ex_check_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v, stepped through the Pa engine
   (lib/A/Prog/{PaRun,PaShadow,PaJournal,DecodePaLib}.v) in the idiom of libreac/fuzz_boxreg's
   lib/A/Prog/ReadName.v (pb_read_name at a working branch 1d92330b7ad) and of this unit's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (a Theorem Labs lane).

   What the code does from the return of the third reac_upstream_decode (+0x86c), offsets of the audited listing
   lib/A/Prog/DecodeList.v:567-605 (offset = 4 * (line - 28)):
     +0x86c  li a2,-1                      a2 := -1
     +0x870  blez s6 -> +0x900             s6 = reac_upstream_channels' result
     +0x874..+0x890  the byte at res + 12 (shadow-checked) against 136, else -> +0x900
     +0x894..+0x8b0  the byte at res + 13 against 25, else -> +0x900
     +0x8b4..+0x8d4  a3 := res + len; the byte at a3 - 2 against 194, else -> +0x900
     +0x8d8..+0x8fc  the byte at a3 - 1: a2 := ((byte = 234) - 1) | 12, i.e. 12 or -1
     +0x900  bne a0,a2 -> +0xa4c           REFUTED: a0 = a2 on every path (the C lemma x_up_ok_* below)
     +0x904  bgez a0 -> +0x95c             taken iff the decode was accepted (a0 = 12)
     +0x908  the scan's entry  (ex_st_908), +0x95c `blez a0` not taken -> +0x960 (ex_st_960)
   Each of the four reads is preceded by the instrumented check of its shadow byte; the token executor of
   lib/Reusable/YCbn.v resolves every one of the four slow-path edges (+0xa8c, +0xae8, +0xb24, +0xb44) against a
   one-byte range_addressable obligation (traps.md item 5), which the AR block law of the copy (res, len)
   discharges, so no branch into +0xa4c..+0xb60 is ever followed.

   The stretch writes NO memory (no store between +0x86c and +0x960) and no region of the symbolic state has a
   write window, so each run's frame_of gives the raw memory back unchanged (x_mem_eq); every memory clause of
   ex_st_908 / ex_st_960 is then the clause of llvm_a_st_86c verbatim. The registers the two cut predicates read
   are the ones the stretch never writes (x_keep); only a1 .. a4 change.

   The C side (lib/A/Prog/reac_upstream_decode_c.v:14-21, reac_upstream_channels_c.v:11-17,
   reac_frame_inspect_c.v:11): up_ok is the conjunction of res <> 0, upb <> 0, 0 <= up_nch len and the four header
   bytes; 0 < upstream_result len is equivalent to 0 <= up_nch len and forces 124 <= len, which is what makes the
   four reads lie inside the copy. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep DecodePaLib YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeAddr DecodeImg check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Abbreviation segs := decodesegs0.

(* ------------------------------------------------------------------ *)
(* 1. The C side: up_ok, up_nch and upstream_result                     *)
(* ------------------------------------------------------------------ *)

(* 0 < upstream_result len and 0 <= up_nch len agree, and both force 124 <= len
   (reac_upstream_channels_c.v:11-17, reac_upstream_decode_c.v:14-16). upstream_width takes its quotient mod
   2 ^ 32, so the direction that starts from the channel count needs the copy's length bound. *)
Lemma x_nch_chan : forall len, 0 <= CUp.up_nch len -> 0 < CChan.upstream_result len /\ 124 <= len.
Proof.
intros len H. unfold CUp.up_nch in H.
destruct ((124 <=? len) && ((len - 52) mod 36 =? 0) && (((len - 52) / 36) mod 2 =? 0) &&
          ((len - 52) / 36 <=? 40)) eqn:Hok; [|lia].
rewrite !andb_true_iff in Hok. destruct Hok as (((H124 & Hm36) & Hm2) & H40).
apply Z.leb_le in H124. apply Z.leb_le in H40. apply Z.eqb_eq in Hm36. apply Z.eqb_eq in Hm2.
assert (Hw : 2 <= (len - 52) / 36 <= 40) by lia.
assert (Hsm : ((len - 52) / 36) mod 2 ^ 32 = (len - 52) / 36) by (apply Z.mod_small; lia).
split; [|lia].
unfold CChan.upstream_result, CChan.upstream_ok, CChan.upstream_width. rewrite Hsm.
replace (52 <=? len) with true by (symmetry; apply Z.leb_le; lia).
rewrite Hm36.
replace (Z.even ((len - 52) / 36)) with true
  by (symmetry; apply Z.even_spec; exists ((len - 52) / 36 / 2); lia).
replace (2 <=? (len - 52) / 36) with true by (symmetry; apply Z.leb_le; lia).
replace ((len - 52) / 36 <=? 40) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb Z.eqb]. lia.
Qed.

Lemma x_chan_nch : forall len, 0 <= len < 2 ^ 26 -> 0 < CChan.upstream_result len ->
  124 <= len /\ CUp.up_nch len = CChan.upstream_result len.
Proof.
intros len Hb Hpos.
unfold CChan.upstream_result, CChan.upstream_ok, CChan.upstream_width in Hpos |- *.
destruct ((52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even (((len - 52) / 36) mod 2 ^ 32) &&
          (2 <=? ((len - 52) / 36) mod 2 ^ 32) && (((len - 52) / 36) mod 2 ^ 32 <=? 40)) eqn:Hok; [|lia].
rewrite !andb_true_iff in Hok. destruct Hok as ((((H52 & Hm36) & Hev) & H2) & H40).
apply Z.leb_le in H52. apply Z.eqb_eq in Hm36.
assert (Hw0 : 0 <= (len - 52) / 36) by (apply Z.div_pos; lia).
assert (Hwhi : (len - 52) / 36 < 2 ^ 32) by (apply Z.div_lt_upper_bound; lia).
assert (Hsm : ((len - 52) / 36) mod 2 ^ 32 = (len - 52) / 36) by (apply Z.mod_small; lia).
rewrite Hsm in Hev, H2, H40 |- *.
apply Z.leb_le in H2. apply Z.leb_le in H40.
assert (Hm2 : ((len - 52) / 36) mod 2 = 0)
  by (destruct (Z.even_spec ((len - 52) / 36)) as [HE _]; destruct (HE Hev) as [q Hq]; lia).
split; [lia|].
unfold CUp.up_nch.
replace (124 <=? len) with true by (symmetry; apply Z.leb_le; lia).
rewrite Hm36, Hm2.
replace ((len - 52) / 36 <=? 40) with true by (symmetry; apply Z.leb_le; lia).
cbn [andb Z.eqb]. reflexivity.
Qed.

(* The four header bytes and the positivity, as up_ok states them. *)
Lemma x_up_ok_fwd : forall res upb len bs, CUp.up_ok res upb len bs = true ->
  0 < CChan.upstream_result len /\ 124 <= len /\
  CInsp.inspect_byte bs 12 = 136 /\ CInsp.inspect_byte bs 13 = 25 /\
  CInsp.inspect_byte bs (Z.to_nat (len - 2)) = 194 /\ CInsp.inspect_byte bs (Z.to_nat (len - 1)) = 234.
Proof.
intros res upb len bs H. unfold CUp.up_ok in H.
rewrite !andb_true_iff in H. destruct H as ((((((Hr & Hu) & Hn) & H12) & H13) & H2) & H1).
apply Z.leb_le in Hn. apply Z.eqb_eq in H12. apply Z.eqb_eq in H13. apply Z.eqb_eq in H2. apply Z.eqb_eq in H1.
destruct (x_nch_chan len Hn) as (Hp & Hge).
repeat split; assumption.
Qed.

Lemma x_up_ok_bwd : forall res upb len bs, 0 <= len < 2 ^ 26 -> res <> 0 -> upb <> 0 ->
  0 < CChan.upstream_result len ->
  CInsp.inspect_byte bs 12 = 136 -> CInsp.inspect_byte bs 13 = 25 ->
  CInsp.inspect_byte bs (Z.to_nat (len - 2)) = 194 -> CInsp.inspect_byte bs (Z.to_nat (len - 1)) = 234 ->
  CUp.up_ok res upb len bs = true.
Proof.
intros res upb len bs Hb Hr Hu Hp H12 H13 H2 H1. unfold CUp.up_ok.
destruct (x_chan_nch len Hb Hp) as (_ & Hn).
rewrite H12, H13, H2, H1, Hn.
replace (res =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
replace (upb =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hu).
replace (0 <=? CChan.upstream_result len) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. Small arithmetic and memory helpers                               *)
(* ------------------------------------------------------------------ *)

Lemma x_s64 : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> s64 (bv_unsigned (Z_to_bv 64 v)) = v.
Proof.
intros v Hv. rewrite unsigned_lit. unfold zcanon, M64, s64.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- replace (v mod 2 ^ 64) with (v + 2 ^ 64)
    by (rewrite <- (Z.mod_add v 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  destruct (Z.ltb_spec (v + 2 ^ 64) (2 ^ 63)); lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); lia.
Qed.

Lemma x_s64_off : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  s64 (bv_unsigned (sv_denot E (SOff n 0))) = v.
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply x_s64. exact Hv.
Qed.

Lemma x_bgez_t : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true.
Proof.
intros E n v H Hv. rewrite branch_ge, (x_s64_off E n v H ltac:(lia)).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). rewrite (x_s64 0 ltac:(lia)).
destruct (Z.ltb_spec v 0); [lia | reflexivity].
Qed.

Lemma x_bgez_f : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 0 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E n v H Hv. rewrite branch_ge, (x_s64_off E n v H ltac:(lia)).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). rewrite (x_s64 0 ltac:(lia)).
destruct (Z.ltb_spec v 0); [reflexivity | lia].
Qed.

Lemma x_blez_f : forall E n v, ew E n = Z_to_bv 64 v -> 0 < v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = false.
Proof.
intros E n v H Hv. rewrite branch_ge, (x_s64_off E n v H ltac:(lia)).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). rewrite (x_s64 0 ltac:(lia)).
destruct (Z.ltb_spec 0 v); [reflexivity | lia].
Qed.

(* The byte the listing builds at +0x8ec..+0x8fc: ((x = 234) - 1) | 12. *)
Definition x_a2sv : sv :=
  SAlu ALU_OR (SAlu ALU_ADD (SAlu ALU_SLTU (SOff 36 (-234)) (SLit 1)) (SLit (-1))) (SLit 12).

Lemma x_a2_val : forall E v, ew E 36 = Z_to_bv 64 v -> 0 <= v < 256 ->
  U E x_a2sv = (if v =? 234 then 12 else 2 ^ 64 - 1).
Proof.
intros E v H36 Hv.
set (E' := mkEnv (fun _ => Z_to_bv 64 v) (ed E)).
assert (HA : env_agree_p (fun n => Nat.eqb n 36) E E').
{ split; [|reflexivity]. intros n Hn. apply Nat.eqb_eq in Hn. subst n. cbn [ew E']. symmetry. exact H36. }
unfold U. rewrite <- (sv_denot_agree_p (fun n => Nat.eqb n 36) E E' x_a2sv HA eq_refl).
assert (Hb : forallb (fun n => Z.eqb (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 (Z.of_nat n)) (ed E)) x_a2sv))
  (if Z.of_nat n =? 234 then 12 else 2 ^ 64 - 1)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat v)). rewrite Z2Nat.id in Hb by lia.
apply Z.eqb_eq. apply Hb. apply in_seq. lia.
Qed.

(* A byte of a garr8 array, as inspect_byte names it. *)
Lemma x_nth_map : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j. destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply (map_nth (fun b : byte => bv_unsigned b)).
- rewrite !nth_overflow by (rewrite ?length_map; lia). vm_compute. reflexivity.
Qed.

(* No region of this walk has a write window, so a run gives the memory back unchanged. *)
Lemma x_mem_eq : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hr).
assert (Hw : YP09.r_whi r <= YP09.r_wlo r) by (exact (proj1 (Forall_forall _ _) Hro r Hin)).
lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic state at +0x86c                                      *)
(* ------------------------------------------------------------------ *)

(* The upper bound of alloc_ceiling (lib/Reusable/YCbq.v:467 asan_consts); the facts must be closed for
   vm_compute, so the bound is written out. *)
Definition X_CEIL_HI : Z := 0x7fffff800000.

(* Atoms beyond the 32 registers: 32 = res + len, 33 / 34 / 35 / 36 = the four header bytes. *)
Definition x_extra (cx : dctx) (res : Z) : list word :=
  [w64 (res + dec_a_len (d_n cx));
   w64 (CInsp.inspect_byte (d_body cx) 12);
   w64 (CInsp.inspect_byte (d_body cx) 13);
   w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2)));
   w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1)))].

Section ee. Context {rc : YM05.RunCeil}.
Definition x_E (regs : bvmap 5 word) (cx : dctx) (res : Z) : env :=
  @Eimg rc decode_listing PI_decode (Ereg regs (x_extra cx res)).
End ee.

Definition x_BX : sv := SOff 18 0.

Definition x_facts : facts :=
  mkFacts [(18%nat, mkAF SB SB 0); (20%nat, mkAF 4096 X_CEIL_HI 0); (26%nat, mkAF 0 (2 ^ 26 - 1) 0);
           (32%nat, mkAF 4096 X_CEIL_HI 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0)] []
          [(SAlu ALU_ADD (SOff 20 0) (SOff 26 0), SOff 32 0)].

Definition x_ss : sstate := mkSS 0x86c sr_atoms [] None x_facts.

(* The two read-only regions the four header reads use; they are seated only after `blez s6` falls through,
   which is what gives 124 <= len. *)
Definition x_rg_body : YP09.region :=
  YP09.mkRegion (Some 20%nat) 12 14 0 0
    [YP09.mkChunk 12 (CVal 1 (SOff 33 0)); YP09.mkChunk 13 (CVal 1 (SOff 34 0))].
Definition x_rg_tail : YP09.region :=
  YP09.mkRegion (Some 32%nat) (-2) 0 0 0
    [YP09.mkChunk (-2) (CVal 1 (SOff 35 0)); YP09.mkChunk (-1) (CVal 1 (SOff 36 0))].

(* The registers the stretch never writes. *)
Definition x_keep : list (bv 5) :=
  [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv.

Section ef. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).

Lemma x_ew_low : forall regs cx res n, (n < A_TEXT)%nat -> ew (x_E regs cx res) n = ew (Ereg regs (x_extra cx res)) n.
Proof. intros regs cx res n Hn. unfold x_E. apply Eimg_low. exact Hn. Qed.

Lemma x_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

Lemma x_byte_range : forall bs i, 0 <= CInsp.inspect_byte bs i < 256.
Proof.
intros bs i. unfold CInsp.inspect_byte.
pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as H.
change (bv_modulus 8) with 256 in H. lia.
Qed.

(* The atoms of the entry environment. *)
Lemma x_ew : forall (regs : bvmap 5 word) cx res,
  ew (x_E regs cx res) 32 = w64 (res + dec_a_len (d_n cx)) /\
  ew (x_E regs cx res) 33 = w64 (CInsp.inspect_byte (d_body cx) 12) /\
  ew (x_E regs cx res) 34 = w64 (CInsp.inspect_byte (d_body cx) 13) /\
  ew (x_E regs cx res) 35 = w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))) /\
  ew (x_E regs cx res) 36 = w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))).
Proof.
intros regs cx res.
assert (H : forall j, (j < 5)%nat -> ew (x_E regs cx res) (32 + j) = nth j (x_extra cx res) (Z_to_bv 64 0)).
{ intros j Hj. rewrite x_ew_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
split; [exact (H 0%nat ltac:(lia))|].
split; [exact (H 1%nat ltac:(lia))|].
split; [exact (H 2%nat ltac:(lia))|].
split; [exact (H 3%nat ltac:(lia))|].
exact (H 4%nat ltac:(lia)).
Qed.

Lemma x_ew_reg : forall (regs : bvmap 5 word) cx res n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (x_E regs cx res) n = YK11.getr regs r.
Proof.
intros regs cx res n r Hn Hlt. rewrite x_ew_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

(* The state at +0x86c: no region, the atoms of the four bytes, res, len and res + len. *)
Lemma x_entry : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (cx : dctx) (res : Z),
  YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 res ->
  YK11.getr regs 26 = w64 (dec_a_len (d_n cx)) ->
  4096 <= res -> 0 <= dec_a_len (d_n cx) < 2 ^ 26 -> res + dec_a_len (d_n cx) <= X_CEIL_HI ->
  @st_ok_pi segs decode_val fx (x_E regs cx res) x_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x86c)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem cx res R18 R20 R26 Hres Hlen Htop.
destruct (x_ew regs cx res) as (E32 & E33 & E34 & E35 & E36).
assert (E18 : ew (x_E regs cx res) 18 = w64 SHADOW_OFF)
  by (rewrite (x_ew_reg regs cx res 18 18%bv eq_refl ltac:(lia)); exact R18).
assert (E20 : ew (x_E regs cx res) 20 = w64 res)
  by (rewrite (x_ew_reg regs cx res 20 20%bv eq_refl ltac:(lia)); exact R20).
assert (E26 : ew (x_E regs cx res) 26 = w64 (dec_a_len (d_n cx)))
  by (rewrite (x_ew_reg regs cx res 26 26%bv eq_refl ltac:(lia)); exact R26).
pose proof (x_byte_range (d_body cx) 12). pose proof (x_byte_range (d_body cx) 13).
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))).
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))).
rewrite restrict_mkst_fx. unfold x_ss.
apply (@pa_entry_st_ok_full fx rc decode_listing PI_decode).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- unfold x_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E20, E26, E32, E33, E34, E35, E36.
  rewrite !x_bv_small by (unfold X_CEIL_HI, SHADOW_OFF in *; lia).
  unfold SB, SHADOW_OFF, X_CEIL_HI in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; try (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity);
    try lia.
  (* the alias res + len *)
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom _ 20 res E20 ltac:(lia)), (U_atom _ 26 (dec_a_len (d_n cx)) E26 ltac:(lia)),
    (U_atom _ 32 (res + dec_a_len (d_n cx)) E32 ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
Qed.
(* The channel count is at most 40 (reac_upstream_channels_c.v:15). *)
Lemma x_chan_hi : forall len, CChan.upstream_result len <= 40.
Proof.
intros len. unfold CChan.upstream_result, CChan.upstream_ok.
destruct ((52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even (CChan.upstream_width len) &&
          (2 <=? CChan.upstream_width len) && (CChan.upstream_width len <=? 40)) eqn:Hok; [|lia].
rewrite !andb_true_iff in Hok. destruct Hok as ((((_ & _) & _) & _) & H40).
apply Z.leb_le in H40. exact H40.
Qed.

(* U of an atom, with no bound on its value. *)
Lemma x_U_atomz : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = zcanon v.
Proof.
intros E n v H. rewrite U_SOff, H, unsigned_lit, Z.add_0_r. unfold zcanon, M64. apply Zmod_mod.
Qed.

Lemma x_bne_f : forall E a b, U E a = U E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b H. rewrite YI04.branch_ne_U, H, Z.eqb_refl. reflexivity. Qed.

Lemma x_bne_t : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = true -> U E a <> U E b.
Proof.
intros E a b H Hq. rewrite YI04.branch_ne_U, Hq, Z.eqb_refl in H. discriminate.
Qed.

Lemma x_bne_eq : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false -> U E a = U E b.
Proof.
intros E a b H. rewrite YI04.branch_ne_U in H. apply negb_false_iff, Z.eqb_eq in H. exact H.
Qed.

(* One register the stretch does not write. *)
Lemma x_kept_regs : forall (E : env) ss (H : word -> bool) ms (regs0 : bvmap 5 word) extra (r : bv 5),
  @st_ok_pi segs decode_val fx E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0) = true ->
  YK11.getr (ms_regs ms) r = YK11.getr regs0 r.
Proof.
intros E ss H ms regs0 extra r HS HAE Hr.
exact (regs_kept_of_st_ok_pi (PI := PI_decode) E ss (restrict H ms) regs0 extra [r] HS HAE
  ltac:(cbn [forallb]; rewrite Hr; reflexivity) r (or_introl eq_refl)).
Qed.

(* dec_a_core and dec_a_fr read only registers this stretch keeps. *)
Lemma x_core_regs : forall (B : asyms) cx ly S (W : world segs) regs regs2 mem md md2 k,
  dec_a_core B cx ly S W regs mem md k ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem md2 k ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 ->
  YK11.getr regs2 4 = YK11.getr regs 4 -> YK11.getr regs2 8 = YK11.getr regs 8 ->
  YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_a_core B cx ly S W regs2 mem md2 k.
Proof.
intros B cx ly S W regs regs2 mem md md2 k HC HJ H2 H3 H4 H8 H9.
destruct HC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16).
unfold dec_a_core.
split; [exact HJ|]. split; [exact A2|]. split; [rewrite H8; exact A3|]. split; [rewrite H9; exact A4|].
split; [unfold spZ in A5 |- *; rewrite H2; exact A5|]. split; [exact A6|]. split; [exact A7|].
split; [rewrite H3; exact A8|]. split; [rewrite H4; exact A9|]. split; [exact A10|].
split; [exact A11|]. split; [exact A12|]. split; [exact A13|]. split; [exact A14|].
split; [exact A15|]. exact A16.
Qed.

Lemma x_fr_regs : forall cx regs regs2, dec_a_fr cx regs ->
  YK11.getr regs2 19 = YK11.getr regs 19 -> YK11.getr regs2 21 = YK11.getr regs 21 ->
  YK11.getr regs2 27 = YK11.getr regs 27 -> dec_a_fr cx regs2.
Proof.
intros cx regs regs2 (A1 & A2 & A3) H19 H21 H27.
split; [rewrite H19; exact A1|]. split; [rewrite H21; exact A2|]. rewrite H27. exact A3.
Qed.

(* A one-byte shadow obligation of the token executor, inside the copy. *)
Lemma x_obl_at : forall (B : asyms), AR_laws segs B -> forall E (W : world segs) mem ly S md
    (p m base c len : Z) (n : nat),
  AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> 0 <= m ->
  ew E 18 = w64 SHADOW_OFF -> ew E n = w64 base ->
  0 <= base < 2 ^ 64 -> 0 <= base + c < 2 ^ 64 ->
  p <= base + c -> base + c + len <= p + m ->
  range_addressable (rd_of segs (mrestrict (w_H W) mem)) (U E x_BX) (U E (SOff n c)) len.
Proof.
intros B LAWS E W mem ly S md p m base c len n HAR Hin Hm H18 Hb Hbr Hbc Hlo Hhi.
unfold x_BX. rewrite (U_atom E 18 SHADOW_OFF H18 ltac:(unfold SHADOW_OFF; lia)).
rewrite (U_atom_off E n base c Hb ltac:(lia) ltac:(lia)).
rewrite <- (aview_rd_of segs).
pose proof (req_size_pos0 m Hm) as (Q1 & Q2).
eapply (range_addressable_of_block segs B LAWS ly S W mem md p m (base + c) len HAR Hin); lia.
Qed.

(* The channel count is at least -1 (reac_upstream_channels_c.v:17). *)
Lemma x_chan_lo : forall len, -1 <= CChan.upstream_result len.
Proof.
intros len. unfold CChan.upstream_result, CChan.upstream_ok.
destruct ((52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even (CChan.upstream_width len) &&
          (2 <=? CChan.upstream_width len) && (CChan.upstream_width len <=? 40)) eqn:Hok; [|lia].
rewrite !andb_true_iff in Hok. destruct Hok as ((((_ & _) & _) & H2) & _).
apply Z.leb_le in H2. lia.
Qed.

Lemma x_blez_pos : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = false -> 0 < v.
Proof.
intros E n v H Hv Hb. rewrite branch_ge, (x_s64_off E n v H ltac:(lia)) in Hb.
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hb. rewrite (x_s64 0 ltac:(lia)) in Hb.
apply negb_false_iff, Z.ltb_lt in Hb. exact Hb.
Qed.

(* The two read-only regions of the four header reads. *)
Lemma x_regions_ok : forall (E : env) (m : word -> option byte) (cx : dctx) (res : Z),
  ew E 20 = w64 res -> ew E 32 = w64 (res + dec_a_len (d_n cx)) ->
  ew E 33 = w64 (CInsp.inspect_byte (d_body cx) 12) ->
  ew E 34 = w64 (CInsp.inspect_byte (d_body cx) 13) ->
  ew E 35 = w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))) ->
  ew E 36 = w64 (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))) ->
  4096 <= res -> 124 <= dec_a_len (d_n cx) -> res + dec_a_len (d_n cx) <= X_CEIL_HI ->
  (forall j, 0 <= j < dec_a_len (d_n cx) ->
     val_mem segs m (res + j) 1 (CInsp.inspect_byte (d_body cx) (Z.to_nat j))) ->
  region_ok segs E m x_rg_body /\ region_ok segs E m x_rg_tail /\
  all_disjoint E x_rg_body [x_rg_tail].
Proof.
intros E m cx res E20 E32 E33 E34 E35 E36 Hres H124 Htop Hb.
pose proof (x_byte_range (d_body cx) 12). pose proof (x_byte_range (d_body cx) 13).
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))).
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))).
unfold X_CEIL_HI in Htop.
assert (U20 : bv_unsigned (ew E 20) = res) by (rewrite E20; apply x_bv_small; lia).
assert (U32 : bv_unsigned (ew E 32) = res + dec_a_len (d_n cx)) by (rewrite E32; apply x_bv_small; lia).
split.
- unfold x_rg_body, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val segs E m res 12 1 (SOff 33 0) (CInsp.inspect_byte (d_body cx) 12));
    [ cbn [sv_denot]; rewrite E33, x_bv_small by lia; rewrite Z.add_0_r; reflexivity
    | cbn; lia | cbn; lia |].
    replace 12%nat with (Z.to_nat 12) by reflexivity. apply Hb. lia.
  + apply (chunk_ok_val segs E m res 13 1 (SOff 34 0) (CInsp.inspect_byte (d_body cx) 13));
    [ cbn [sv_denot]; rewrite E34, x_bv_small by lia; rewrite Z.add_0_r; reflexivity
    | cbn; lia | cbn; lia |].
    replace 13%nat with (Z.to_nat 13) by reflexivity. apply Hb. lia.
- split.
  + unfold x_rg_tail, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E m (res + dec_a_len (d_n cx)) (-2) 1 (SOff 35 0)
        (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))));
      [ cbn [sv_denot]; rewrite E35, x_bv_small by lia; rewrite Z.add_0_r; reflexivity
      | cbn; lia | cbn; lia |].
      replace (res + dec_a_len (d_n cx) + -2) with (res + (dec_a_len (d_n cx) - 2)) by lia.
      apply Hb. lia.
    * apply (chunk_ok_val segs E m (res + dec_a_len (d_n cx)) (-1) 1 (SOff 36 0)
        (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))));
      [ cbn [sv_denot]; rewrite E36, x_bv_small by lia; rewrite Z.add_0_r; reflexivity
      | cbn; lia | cbn; lia |].
      replace (res + dec_a_len (d_n cx) + -1) with (res + (dec_a_len (d_n cx) - 1)) by lia.
      apply Hb. lia.
  + cbn [all_disjoint]. split; [|exact I].
    unfold extent_disjoint, x_rg_body, x_rg_tail.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U32. lia.
Qed.

End ef.

(* ------------------------------------------------------------------ *)
(* 4. Tactics of the walk                                               *)
(* ------------------------------------------------------------------ *)

(* Every region is read only, so the runs need no write right. *)
Ltac x_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?a ?b ?c ?d ?e ?f ?g =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' a b c d e f g) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

(* The model term after a run (traps.md item 1). *)
Ltac x_md :=
  repeat match goal with
  | |- context [with_vm_backing ?a ?b ?c] =>
      let m := fresh "mdv" in set (m := with_vm_backing a b c) in *; clearbody m
  end.

(* A run writes nothing: its memory is the memory before it. The equations chain back to the entry's mem; a goal
   or a hypothesis is brought back to it with x_memg / x_memh. *)
Ltac x_keepmem :=
  lazymatch goal with
  | HF : frame_of ?E ?rs ?m0 (ms_mem ?msb) |- _ =>
      let Hq := fresh "HM" in
      assert (Hq : ms_mem msb = m0) by
        (apply (x_mem_eq E rs m0 (ms_mem msb));
         [ let rs' := eval vm_compute in rs in change rs with rs';
           repeat apply Forall_cons; try apply Forall_nil; cbn [YP09.r_wlo YP09.r_whi]; lia
         | exact HF ])
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac x_memg :=
  cbn [ms_mem restrict];
  repeat match goal with H : ms_mem _ = _ |- _ => rewrite H end.
Ltac x_memh Hh :=
  repeat match goal with H : ms_mem _ = _ |- _ => rewrite H in Hh end.

(* AG : the environment's atoms below 512 are the entry's (ReadName's rn_env). *)
Ltac x_env HS AG :=
  let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
  lazymatch type of AG with forall n, _ -> ew ?Eo n = ew ?E0 n =>
  lazymatch Ex with
  | Eo => idtac
  | _ => let AG2 := fresh "AG" in
    assert (AG2 : forall n, (n < 512)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia];
          first [reflexivity | apply AG; exact Hnn]);
    clear AG; rename AG2 into AG
  end end;
  repeat match goal with H : img_env _ _ ?Ey |- _ => lazymatch Ey with Ex => fail | _ => clear H end end.

Ltac x_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in
  change ss3 with v in HS end.

(* ------------------------------------------------------------------ *)
(* 5. The two cut points, as lemmas (an Ltac body may name no hypothesis) *)
(* ------------------------------------------------------------------ *)

Section fin. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma x_at908 : forall (B : asyms) (MT : ameter_ops) (cx : dctx) ly S (W : world segs)
    (regs regs2 : bvmap 5 word) (mem : word -> option byte) md md2 (res upb : Z),
  dec_a_core B cx ly S W regs mem md dec_ev_86c ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem md2 dec_ev_86c ->
  (forall r, In r x_keep -> YK11.getr regs2 r = YK11.getr regs r) ->
  frm_zero (@fp_csr fx) ->
  Permutation (ablocks B ly S) (ex_blocks B cx res upb) ->
  4096 <= res -> 4096 <= upb ->
  mo_le MT (d_S cx) S (dec_spent_86c MT (d_n cx)) -> mo_ok MT S (dec_rest_86c MT) ->
  dec_a_fr cx regs ->
  YK11.getr regs 10 = w64 (-1) ->
  YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 res ->
  YK11.getr regs 23 = w64 upb ->
  YK11.getr regs 24 = w64 (ex_uolen cx) ->
  dec_a_filled W mem upb (ex_uolen cx) ->
  dec_a_fsh cx (aview segs (w_H W) mem) 0 4 ->
  ex_st_908 B MT cx W (mkCfg (@YK11.mkst fx regs2 (w64 (DEC_A_LLVMF + 0x908)) mem (YK11.seg_rom segs)) md2).
Proof.
intros B MT cx ly S W regs regs2 mem md md2 res upb HC HJ Hk Hfrm Hperm Hres Hupb Hmle Hmok Hfr
  R10 R18 R20 R23 R24 Hfill Hfsh.
assert (K2 : YK11.getr regs2 2 = YK11.getr regs 2) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K3 : YK11.getr regs2 3 = YK11.getr regs 3) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K4 : YK11.getr regs2 4 = YK11.getr regs 4) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K8 : YK11.getr regs2 8 = YK11.getr regs 8) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K9 : YK11.getr regs2 9 = YK11.getr regs 9) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K10 : YK11.getr regs2 10 = YK11.getr regs 10) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K18 : YK11.getr regs2 18 = YK11.getr regs 18) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K19 : YK11.getr regs2 19 = YK11.getr regs 19) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K20 : YK11.getr regs2 20 = YK11.getr regs 20) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K21 : YK11.getr regs2 21 = YK11.getr regs 21) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K23 : YK11.getr regs2 23 = YK11.getr regs 23) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K24 : YK11.getr regs2 24 = YK11.getr regs 24) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K27 : YK11.getr regs2 27 = YK11.getr regs 27) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
unfold ex_st_908.
exists fx, ly, S, regs2, mem, md2, res, upb.
split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (x_core_regs B cx ly S W regs regs2 mem md md2 dec_ev_86c HC HJ K2 K3 K4 K8 K9)|].
split; [exact Hperm|]. split; [exact Hres|]. split; [exact Hupb|]. split; [exact Hmle|]. split; [exact Hmok|].
split; [exact (x_fr_regs cx regs regs2 Hfr K19 K21 K27)|].
split; [rewrite K10; exact R10|].
split; [rewrite K18; exact R18|].
split; [rewrite K20; exact R20|].
split; [rewrite K23; exact R23|].
split; [rewrite K24; exact R24|].
split; [exact Hfill|]. exact Hfsh.
Qed.

Lemma x_at960 : forall (B : asyms) (MT : ameter_ops) (cx : dctx) ly S (W : world segs)
    (regs regs2 : bvmap 5 word) (mem : word -> option byte) md md2 (res upb : Z),
  dec_a_core B cx ly S W regs mem md dec_ev_86c ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx)
    (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S W mem md2 dec_ev_86c ->
  (forall r, In r x_keep -> YK11.getr regs2 r = YK11.getr regs r) ->
  frm_zero (@fp_csr fx) ->
  Permutation (ablocks B ly S) (ex_blocks B cx res upb) ->
  4096 <= res -> 4096 <= upb ->
  mo_le MT (d_S cx) S (dec_spent_86c MT (d_n cx)) -> mo_ok MT S (dec_rest_86c MT) ->
  dec_a_fr cx regs ->
  YK11.getr regs 20 = w64 res ->
  YK11.getr regs 22 = w64 (CChan.upstream_result (dec_a_len (d_n cx))) ->
  YK11.getr regs 23 = w64 upb ->
  CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) = true ->
  garr8 segs (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  garr8 segs (mrestrict (w_H W) mem) upb
    (map (fun b : byte => bv_unsigned b)
       (CDec.braid_out (d_body cx) (CUp.up_nch (dec_a_len (d_n cx))) 12)) ->
  dec_a_fsh cx (aview segs (w_H W) mem) 0 4 ->
  dec_a_slot cx (aview segs (w_H W) mem) 64 (res + 50) ->
  ex_st_960 B MT cx W (mkCfg (@YK11.mkst fx regs2 (w64 (DEC_A_LLVMF + 0x960)) mem (YK11.seg_rom segs)) md2).
Proof.
intros B MT cx ly S W regs regs2 mem md md2 res upb HC HJ Hk Hfrm Hperm Hres Hupb Hmle Hmok Hfr
  R20 R22 R23 HUP Hgarr Hbraid Hfsh Hs64.
assert (K2 : YK11.getr regs2 2 = YK11.getr regs 2) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K3 : YK11.getr regs2 3 = YK11.getr regs 3) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K4 : YK11.getr regs2 4 = YK11.getr regs 4) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K8 : YK11.getr regs2 8 = YK11.getr regs 8) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K9 : YK11.getr regs2 9 = YK11.getr regs 9) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K19 : YK11.getr regs2 19 = YK11.getr regs 19) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K20 : YK11.getr regs2 20 = YK11.getr regs 20) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K21 : YK11.getr regs2 21 = YK11.getr regs 21) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K22 : YK11.getr regs2 22 = YK11.getr regs 22) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K23 : YK11.getr regs2 23 = YK11.getr regs 23) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
assert (K27 : YK11.getr regs2 27 = YK11.getr regs 27) by (apply Hk; cbn [In x_keep]; repeat first [left; reflexivity | right]).
unfold ex_st_960.
exists fx, ly, S, regs2, mem, md2, res, upb.
split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (x_core_regs B cx ly S W regs regs2 mem md md2 dec_ev_86c HC HJ K2 K3 K4 K8 K9)|].
split; [exact Hperm|]. split; [exact Hres|]. split; [exact Hupb|]. split; [exact Hmle|]. split; [exact Hmok|].
split; [exact (x_fr_regs cx regs regs2 Hfr K19 K21 K27)|].
split; [rewrite K20; exact R20|].
split; [rewrite K22; exact R22|].
split; [rewrite K23; exact R23|].
split; [exact HUP|]. split; [exact Hgarr|]. split; [exact Hbraid|]. split; [exact Hfsh|]. exact Hs64.
Qed.

End fin.

(* ------------------------------------------------------------------ *)
(* 6. The tactics of the walk (every proof-local name is an argument)   *)
(* ------------------------------------------------------------------ *)

(* Seat the two read-only regions of the header reads, once the length is known. *)
Ltac x_seat Wq memq cxq resq AGq E20q E32q E33q E34q E35q E36q Hbyteq :=
  lazymatch goal with HSq : st_ok_pi _ _ ?Ex _ _ |- _ =>
    destruct (x_regions_ok Ex (mrestrict (w_H Wq) memq) cxq resq
      (eq_trans (AGq 20%nat ltac:(lia)) E20q) (eq_trans (AGq 32%nat ltac:(lia)) E32q)
      (eq_trans (AGq 33%nat ltac:(lia)) E33q) (eq_trans (AGq 34%nat ltac:(lia)) E34q)
      (eq_trans (AGq 35%nat ltac:(lia)) E35q) (eq_trans (AGq 36%nat ltac:(lia)) E36q)
      ltac:(lia) ltac:(lia) ltac:(lia) Hbyteq) as (HRb & HRt & HDbt) end;
  lazymatch goal with HSq : st_ok_pi _ _ ?Ex ?ssx ?msx |- _ =>
    lazymatch goal with Htq : region_ok _ _ _ x_rg_tail |- _ =>
      let H1 := fresh "HSn" in
      pose proof (st_ok_pi_add_region Ex ssx msx x_rg_tail HSq ltac:(vm_compute; reflexivity)
                   ltac:(x_memg; exact Htq) I) as H1;
      clear HSq; rename H1 into HS end end;
  lazymatch goal with HSq : st_ok_pi _ _ ?Ex ?ssx ?msx |- _ =>
    lazymatch goal with Hbq : region_ok _ _ _ x_rg_body |- _ =>
      lazymatch goal with Hdq : all_disjoint _ x_rg_body _ |- _ =>
        let H1 := fresh "HSn" in
        pose proof (st_ok_pi_add_region Ex ssx msx x_rg_body HSq ltac:(vm_compute; reflexivity)
                     ltac:(x_memg; exact Hbq) Hdq) as H1;
        clear HSq; rename H1 into HS end end end;
  lazymatch goal with HSq : st_ok_pi _ _ _ ?ss3 _ |- _ =>
    let v := eval vm_compute in ss3 in change ss3 with v in HSq end.

(* The one-byte shadow obligations of the four reads. *)
Ltac x_oblb Bq LAWSq HARq Hinq AGq E18q E20q :=
  x_memg; eapply (x_obl_at Bq LAWSq _ _ _ _ _ _ _ _ _ _ _ 20%nat HARq Hinq ltac:(lia)
    (eq_trans (AGq 18%nat ltac:(lia)) E18q) (eq_trans (AGq 20%nat ltac:(lia)) E20q)); lia.
Ltac x_oblt Bq LAWSq HARq Hinq AGq E18q E32q :=
  x_memg; eapply (x_obl_at Bq LAWSq _ _ _ _ _ _ _ _ _ _ _ 32%nat HARq Hinq ltac:(lia)
    (eq_trans (AGq 18%nat ltac:(lia)) E18q) (eq_trans (AGq 32%nat ltac:(lia)) E32q)); lia.

(* The registers the stretch keeps, at the current environment. *)
Ltac x_kept AGq HAEq rgq exq :=
  lazymatch goal with HSq : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (HAEf : env_agree 32 (Ereg rgq exq) Ex)
      by (split; [intros nn Hnn; exact (eq_trans (AGq nn ltac:(lia)) (proj1 HAEq nn Hnn))
                 | cbn [ed ewset havoc extK]; exact (proj2 HAEq)]) end;
  lazymatch goal with HSq : st_ok_pi _ _ _ _ _ |- _ =>
    lazymatch goal with HAq : env_agree 32 (Ereg rgq exq) _ |- _ =>
      pose proof (regs_kept_of_st_ok_pi (PI := PI_decode) _ _ _ rgq exq x_keep HSq HAq
        ltac:(vm_compute; reflexivity)) as Hk end end.

(* A header byte read by a `bne` that was not taken. *)
Ltac x_byte_eq nq Enq AGq :=
  lazymatch goal with Hcq : branch_taken BC_NE _ _ = false |- _ =>
    let Hq := fresh "Hq" in
    pose proof (x_bne_eq _ _ _ Hcq) as Hq;
    rewrite (x_U_atomz _ nq _ (eq_trans (AGq nq ltac:(lia)) Enq)), U_SLit in Hq;
    unfold zcanon, M64 in Hq; rewrite !Z.mod_small in Hq by lia; exact Hq end.

(* Bring every hypothesis that still names a run's memory back to the entry's memory. *)
Ltac x_memj :=
  repeat match goal with
  | HMq : ms_mem ?mx = _, Hq : context [ms_mem ?mx] |- _ =>
      lazymatch type of Hq with ms_mem _ = _ => fail | _ => rewrite HMq in Hq end
  end.

(* The two cut points reached. *)
Ltac x_fin908 AGq HAEq rgq exq resq upbq :=
  x_memj; x_kept AGq HAEq rgq exq;
  lazymatch goal with HSq : st_ok_pi _ _ _ _ _ |- _ => pmkst HSq end;
  apply SRr_ret; cbv beta; right; x_memg;
  eapply (x_at908 _ _ _ _ _ _ _ _ _ _ _ resq upbq); try eassumption.
Ltac x_fin960 AGq HAEq rgq exq resq upbq :=
  x_memj; x_kept AGq HAEq rgq exq;
  lazymatch goal with HSq : st_ok_pi _ _ _ _ _ |- _ => pmkst HSq end;
  apply SRr_ret; cbv beta; left; x_memg;
  eapply (x_at960 _ _ _ _ _ _ _ _ _ _ _ resq upbq); try eassumption.

(* +0x900 .. +0x908 of the refused case: the `bgez a0` edge, then the scan's entry. *)
Ltac x_tail908 RUNq RUNTOq BRq HSq HJq SHOKq AGq E10q finq :=
  paj_run_tok RUNq HSq HJq SHOKq Bspan; [x_awr |];
  x_md; x_keepmem; x_env HSq AGq;
  psrr_branch_tok RUNq BRq HSq SHOKq Bspan;
  [ exfalso;
    lazymatch goal with Hcq : branch_taken _ _ _ = true |- _ =>
      rewrite (x_bgez_f _ 10%nat _ (eq_trans (AGq 10%nat ltac:(lia)) E10q) ltac:(lia)) in Hcq; discriminate end
  | lazymatch goal with Hcq : branch_taken _ _ _ = false |- _ => clear Hcq end;
    paj_run_to_tok RUNTOq HSq HJq SHOKq Bspan 0x908; [x_awr |];
    x_md; x_keepmem; x_env HSq AGq;
    finq ].

(* A refused header byte: the edge to +0x900, its `bne a0,a2` refuted, then the tail. *)
Ltac x_tail900 RUNq RUNTOq BRq HSq HJq SHOKq AGq E10q finq :=
  paj_run_tok RUNq HSq HJq SHOKq Bspan; [x_awr |];
  x_md; x_keepmem; x_env HSq AGq;
  psrr_branch_tok RUNq BRq HSq SHOKq Bspan;
  [ exfalso;
    lazymatch goal with Hcq : branch_taken _ _ _ = true |- _ => apply (x_bne_t _ _ _ Hcq) end;
    rewrite (x_U_atomz _ 10%nat _ (eq_trans (AGq 10%nat ltac:(lia)) E10q)), U_SLit; vm_compute; reflexivity
  | lazymatch goal with Hcq : branch_taken _ _ _ = false |- _ => clear Hcq end;
    x_tail908 RUNq RUNTOq BRq HSq HJq SHOKq AGq E10q finq ].


(* ------------------------------------------------------------------ *)
(* 7. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section x. Context {rc : YM05.RunCeil}.
(* lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v's Section cuts, variable for variable. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem ex_check_ok :
  ex_check_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_check_stmt.
intros LAWS ML MTL cx W c HB HROM H86.
pose proof asan_consts as (CR1 & CR2 & CR3 & CR4 & CR5).
destruct H86 as (fx & ly1 & S1 & regs1 & mem1 & md1 & res & upb & mode & nch & ns & -> & Hfrm & HC & Hperm
  & Hres & Hupb & Hmle & Hmok & Hfr & R10 & R18 & R20 & R22 & R23 & R24 & R26 & Hmode & Hfsh & Hgarr
  & HupT & HupF & Hslots & Hs40 & Hs56 & Hs64 & Hs112).
pose proof HC as (HJ & Hfrs & R8 & R9 & Hsp & Hsp1r & Hsp1a & Hgp & Htp & Hsaved & HF4 & HFa & HFp & HFL
  & Hblk & Hga).
pose proof (proj1 HJ) as HAR.
(* n and the copy's length; only the first six conjuncts of the slot pre are read *)
unfold dec_a_base, dec_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & Hpn & Hlen & _).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hlen0 : 0 <= dec_a_len (d_n cx) < 2 ^ 26) by (unfold dec_a_len; lia).
assert (Hbody : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx)).
{ unfold d_body, dec_a_len, dec_a_u. rewrite length_skipn. lia. }
(* the copy is a live block *)
assert (Hin : In (res, dec_a_len (d_n cx)) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly1 S1 W mem1 md1 _ _ HAR Hin) as (_ & _ & Hceil & _).
pose proof (req_size_pos0 (dec_a_len (d_n cx)) ltac:(lia)) as (Hrq0 & Hrq1).
assert (Htop : res + dec_a_len (d_n cx) <= X_CEIL_HI) by (unfold X_CEIL_HI; unfold ASAN_CEIL in *; lia).
assert (Htop64 : 0 <= res + dec_a_len (d_n cx) < 2 ^ 64) by (unfold X_CEIL_HI in Htop; lia).
(* the bytes of the copy *)
assert (Hbyte : forall j, 0 <= j < dec_a_len (d_n cx) ->
  val_mem segs (mrestrict (w_H W) mem1) (res + j) 1 (CInsp.inspect_byte (d_body cx) (Z.to_nat j))).
{ intros j Hj.
  destruct (Hgarr (Z.to_nat j) ltac:(rewrite length_map; lia)) as (Hv & _).
  rewrite x_nth_map in Hv. rewrite Z2Nat.id in Hv by lia. exact Hv. }
pose proof (x_byte_range (d_body cx) 12) as HB12.
pose proof (x_byte_range (d_body cx) 13) as HB13.
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2))) as HB2.
pose proof (x_byte_range (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1))) as HB1.
(* the symbolic entry *)
set (E0 := x_E regs1 cx res).
assert (HS : @st_ok_pi segs decode_val fx E0 x_ss
  (restrict (w_H W) (@YK11.mkst fx regs1 (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x86c)) mem1
     (YK11.seg_rom segs))))
  by (apply (x_entry W regs1 mem1 cx res R18 R20 R26 ltac:(lia) ltac:(lia) ltac:(lia))).
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM E0) by (unfold E0, x_E; apply Eimg_env).
assert (SHOK : sh_ok segs x_BX (@nil shent) E0 (mrestrict (w_H W) mem1)) by constructor.
assert (AG : forall n, (n < 512)%nat -> ew E0 n = ew E0 n) by reflexivity.
assert (HAE : env_agree 32 (Ereg regs1 (x_extra cx res)) E0)
  by (split; [intros n Hn; apply x_ew_low; unfold A_TEXT; lia | reflexivity]).
destruct (x_ew regs1 cx res) as (E32 & E33 & E34 & E35 & E36).
assert (E10 : ew E0 10 = w64 (if CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx) then 12 else -1))
  by (unfold E0; rewrite (x_ew_reg regs1 cx res 10 10%bv eq_refl ltac:(lia)); exact R10).
assert (E22 : ew E0 22 = w64 (CChan.upstream_result (dec_a_len (d_n cx))))
  by (unfold E0; rewrite (x_ew_reg regs1 cx res 22 22%bv eq_refl ltac:(lia)); exact R22).
assert (E18 : ew E0 18 = w64 SHADOW_OFF)
  by (unfold E0; rewrite (x_ew_reg regs1 cx res 18 18%bv eq_refl ltac:(lia)); exact R18).
assert (E20 : ew E0 20 = w64 res)
  by (unfold E0; rewrite (x_ew_reg regs1 cx res 20 20%bv eq_refl ltac:(lia)); exact R20).
pose proof (paj_run (fx := fx) (SK := dec_A_sink_head) (L := decode_listing) (PI := PI_decode) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := dec_A_sink_head) (L := decode_listing) (PI := PI_decode) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (L := decode_listing) (PI := PI_decode)) as BR.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr (@pa_segs _ decode_listing PI_decode) Wx
    (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x86c)) mm rom) mdx) Q) end.
(* The decode's answer: a0 is 12 or -1. *)
case_eq (CUp.up_ok res upb (dec_a_len (d_n cx)) (d_body cx)); intros HUP.
{ (* ---- accepted: the channel count is positive and the four header bytes agree ---- *)
  destruct (x_up_ok_fwd res upb (dec_a_len (d_n cx)) (d_body cx) HUP) as (Hpos & H124 & Bb12 & Bb13 & Bb2 & Bb1).
  pose proof (x_chan_hi (dec_a_len (d_n cx))) as Hhi.
  pose proof (HupT HUP) as Hbraid.
  rewrite HUP in E10. cbv beta iota in E10.
  rewrite HUP in R10. cbv beta iota in R10.
  (* +0x86c .. +0x870: li a2,-1 and `blez s6` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite (x_blez_f _ 22%nat _ (eq_trans (AG 22%nat ltac:(lia)) E22) ltac:(lia)) in Hc. discriminate. }
  clear Hc. x_seat W mem1 cx res AG E20 E32 E33 E34 E35 E36 Hbyte.
  (* +0x874 .. +0x890: the byte at res + 12 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_oblb B LAWS HAR Hin AG E18 E20 | x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. apply (x_bne_t _ _ _ Hc).
    rewrite (x_U_atomz _ 33%nat _ (eq_trans (AG 33%nat ltac:(lia)) E33)), U_SLit, Bb12. reflexivity. }
  clear Hc.
  (* +0x894 .. +0x8b0: the byte at res + 13 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_oblb B LAWS HAR Hin AG E18 E20 | x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. apply (x_bne_t _ _ _ Hc).
    rewrite (x_U_atomz _ 34%nat _ (eq_trans (AG 34%nat ltac:(lia)) E34)), U_SLit, Bb13. reflexivity. }
  clear Hc.
  (* +0x8b4 .. +0x8d4: the byte at res + len - 2 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_oblt B LAWS HAR Hin AG E18 E32 | x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. apply (x_bne_t _ _ _ Hc).
    rewrite (x_U_atomz _ 35%nat _ (eq_trans (AG 35%nat ltac:(lia)) E35)), U_SLit, Bb2. reflexivity. }
  clear Hc.
  (* +0x8d8 .. +0x900: the byte at res + len - 1 builds a2, and `bne a0,a2` is refuted *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_oblt B LAWS HAR Hin AG E18 E32 | x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. apply (x_bne_t _ _ _ Hc). fold x_a2sv.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ex _ _ |- _ =>
      rewrite (x_U_atomz Ex 10%nat _ (eq_trans (AG 10%nat ltac:(lia)) E10)),
        (x_a2_val Ex _ (eq_trans (AG 36%nat ltac:(lia)) E36) ltac:(apply x_byte_range)) end.
    rewrite Bb1. vm_compute. reflexivity. }
  clear Hc.
  (* +0x900 .. +0x904: `bgez a0` taken (a0 = 12) *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  2: { exfalso. rewrite (x_bgez_t _ 10%nat _ (eq_trans (AG 10%nat ltac:(lia)) E10) ltac:(lia)) in Hc.
       discriminate. }
  clear Hc.
  (* +0x904 .. +0x95c: `blez a0` not taken, on to +0x960 *)
  paj_run_tok RUN HS HJ SHOK Bspan; [x_awr |].
  x_md. x_keepmem. x_env HS AG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite (x_blez_f _ 10%nat _ (eq_trans (AG 10%nat ltac:(lia)) E10) ltac:(lia)) in Hc. discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x960; [x_awr |].
  x_md. x_keepmem. x_env HS AG.
  x_fin960 AG HAE regs1 (x_extra cx res) res upb. }
(* ---- refused: a0 = -1 ---- *)
rewrite HUP in E10. cbv beta iota in E10.
rewrite HUP in R10. cbv beta iota in R10.
pose proof (HupF HUP) as Hfill.
pose proof (x_chan_hi (dec_a_len (d_n cx))) as Hhi.
pose proof (x_chan_lo (dec_a_len (d_n cx))) as Hlo.
paj_run_tok RUN HS HJ SHOK Bspan; [x_awr |].
x_md. x_keepmem. x_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* `blez s6` taken: nothing is read, on to +0x900 *)
  clear Hc.
  x_tail900 RUN RUNTO BR HS HJ SHOK AG E10 ltac:(x_fin908 AG HAE regs1 (x_extra cx res) res upb). }
(* `blez s6` not taken: the channel count is positive, the four reads are inside the copy *)
assert (Hpos : 0 < CChan.upstream_result (dec_a_len (d_n cx)))
  by (apply (x_blez_pos _ 22%nat _ (eq_trans (AG 22%nat ltac:(lia)) E22) ltac:(lia) Hc)).
destruct (x_chan_nch (dec_a_len (d_n cx)) ltac:(lia) Hpos) as (H124 & _).
clear Hc. x_seat W mem1 cx res AG E20 E32 E33 E34 E35 E36 Hbyte.
(* the byte at res + 12 *)
paj_run_tok RUN HS HJ SHOK Bspan; [x_oblb B LAWS HAR Hin AG E18 E20 | x_awr |].
x_md. x_keepmem. x_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ clear Hc. x_tail900 RUN RUNTO BR HS HJ SHOK AG E10 ltac:(x_fin908 AG HAE regs1 (x_extra cx res) res upb). }
assert (Bb12 : CInsp.inspect_byte (d_body cx) 12 = 136) by (x_byte_eq 33%nat E33 AG).
clear Hc.
(* the byte at res + 13 *)
paj_run_tok RUN HS HJ SHOK Bspan; [x_oblb B LAWS HAR Hin AG E18 E20 | x_awr |].
x_md. x_keepmem. x_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ clear Hc. x_tail900 RUN RUNTO BR HS HJ SHOK AG E10 ltac:(x_fin908 AG HAE regs1 (x_extra cx res) res upb). }
assert (Bb13 : CInsp.inspect_byte (d_body cx) 13 = 25) by (x_byte_eq 34%nat E34 AG).
clear Hc.
(* the byte at res + len - 2 *)
paj_run_tok RUN HS HJ SHOK Bspan; [x_oblt B LAWS HAR Hin AG E18 E32 | x_awr |].
x_md. x_keepmem. x_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ clear Hc. x_tail900 RUN RUNTO BR HS HJ SHOK AG E10 ltac:(x_fin908 AG HAE regs1 (x_extra cx res) res upb). }
assert (Bb2 : CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 2)) = 194)
  by (x_byte_eq 35%nat E35 AG).
clear Hc.
(* the byte at res + len - 1: it cannot be 234, else the decode would have been accepted *)
assert (Bne : CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1)) <> 234).
{ intros Hq.
  pose proof (x_up_ok_bwd res upb (dec_a_len (d_n cx)) (d_body cx) ltac:(lia) ltac:(lia) ltac:(lia) Hpos
    Bb12 Bb13 Bb2 Hq) as Hq2.
  rewrite HUP in Hq2. discriminate. }
paj_run_tok RUN HS HJ SHOK Bspan; [x_oblt B LAWS HAR Hin AG E18 E32 | x_awr |].
x_md. x_keepmem. x_env HS AG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. apply (x_bne_t _ _ _ Hc). fold x_a2sv.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ex _ _ |- _ =>
    rewrite (x_U_atomz Ex 10%nat _ (eq_trans (AG 10%nat ltac:(lia)) E10)),
      (x_a2_val Ex _ (eq_trans (AG 36%nat ltac:(lia)) E36) ltac:(apply x_byte_range)) end.
  replace (CInsp.inspect_byte (d_body cx) (Z.to_nat (dec_a_len (d_n cx) - 1)) =? 234) with false
    by (symmetry; apply Z.eqb_neq; exact Bne).
  vm_compute. reflexivity. }
clear Hc.
x_tail908 RUN RUNTO BR HS HJ SHOK AG E10 ltac:(x_fin908 AG HAE regs1 (x_extra cx res) res upb).
Qed.

End x.
